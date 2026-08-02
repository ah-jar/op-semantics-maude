#!/usr/bin/env python3
"""
Ejecuta Maude vía 'search', extrae todas las ramas de ejecución no deterministas (or, par, protect)
o deterministas, convierte los términos de prueba en árboles LaTeX y genera un PDF multipágina.
Soporta los modos --ns, --sos y --compare.
"""

import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

# --- ELEVAR LÍMITE DE RECURSIÓN PARA TRAZAS LARGAS/PROFUNDAS ---
sys.setrecursionlimit(100000)


@dataclass
class Node:
    rule: str
    statement: str
    before: str
    after: str
    children: tuple = ()
    next_stat: str = None
    semantics: str = "ns"
    is_stuck: bool = False


def check_ns_compatibility(program_text: str) -> None:
    """Verifica que el programa no contenga concurrencia o atomicidad si se va a ejecutar en NS."""
    if re.search(r"\b(par|protect)\b", program_text) or "||" in program_text:
        sys.exit(
            "\n[Error de Semántica] Los operadores 'par' (||) y 'protect' "
            "no están soportados en Semántica Natural (NS).\n"
            "Ejecute el script en modo SOS mediante el modificador '--sos'.\n"
        )


def split_arguments(text: str) -> list[str]:
    parts, start, depth = [], 0, 0
    for i, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(text[start:i].strip())
            start = i + 1
    parts.append(text[start:].strip())
    return parts


def parse_tree(term: str, semantics: str = "ns") -> Node:
    term = re.sub(r"\s+", " ", term).strip()

    # Detección de estados atascados
    match_run_stuck = re.fullmatch(r"run\(\s*\(?\s*<\s*(.*?)\s*,\s*(.*?)\s*>\s*\)?\s*\)", term)
    if match_run_stuck:
        return Node("stuck", match_run_stuck.group(1).strip(), match_run_stuck.group(2).strip(), "stuck", semantics=semantics, is_stuck=True)

    match = re.fullmatch(r"([A-Za-z0-9_-]+)\((.*)\)", term)
    if not match:
        raise ValueError(f"Término de árbol no reconocido:\n{term}")

    constructor = match.group(1)
    args = split_arguments(match.group(2))

    # Rechazo explícito de constructores concurrentes/atómicos en Semántica Natural
    if ("par" in constructor or "protect" in constructor) and semantics == "ns":
        raise ValueError("Los operadores 'par' y 'protect' no están soportados en Semántica Natural (NS).")

    # --- CIERRE TRANSITIVO (SOS) ---
    if constructor == "seqsos":
        children = tuple(parse_tree(arg, "sos") for arg in args if arg != "nilSOS")
        return Node("seq", "", "", "", children, semantics="sos")

    # --- REGLAS DE SEMÁNTICA NATURAL (NS) ---
    if constructor == "assns" and len(args) == 3:
        return Node("ass", args[0], args[1], args[2], semantics="ns")
    if constructor == "skipns" and len(args) == 3:
        return Node("skip", args[0], args[1], args[2], semantics="ns")
    if constructor == "compns" and len(args) == 5:
        return Node("comp", args[0], args[1], args[4], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns")), semantics="ns")
    if constructor == "ifttns" and len(args) == 4:
        return Node("if-tt", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "ifffns" and len(args) == 4:
        return Node("if-ff", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "whilettns" and len(args) == 5:
        return Node("while-tt", args[0], args[1], args[4], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns")), semantics="ns")
    if constructor == "whileffns" and len(args) == 3:
        return Node("while-ff", args[0], args[1], args[2], semantics="ns")
    if constructor == "repeatffns" and len(args) == 5:
        return Node("repeat-ff", args[0], args[1], args[4], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns")), semantics="ns")
    if constructor == "repeatttns" and len(args) == 4:
        return Node("repeat-tt", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "forttns" and len(args) == 6:
        return Node("for-tt", args[0], args[1], args[5], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns"), parse_tree(args[4], "ns")), semantics="ns")
    if constructor == "forffns" and len(args) == 3:
        return Node("for-ff", args[0], args[1], args[2], semantics="ns")
    if constructor == "abortns" and len(args) == 3:
        return Node("abort", args[0], args[1], args[2], semantics="ns")
    if constructor == "compabortns" and len(args) == 4:
        return Node("comp-abort", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "whileabortns" and len(args) == 4:
        return Node("while-abort", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "repeatabortns" and len(args) == 4:
        return Node("repeat-abort", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "forabortns" and len(args) == 5:
        return Node("for-abort", args[0], args[1], args[4], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns")), semantics="ns")
    if constructor == "assertttns" and len(args) == 4:
        return Node("assert-tt", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "assertffns" and len(args) == 3:
        return Node("assert-ff", args[0], args[1], args[2], semantics="ns")
    if constructor == "or1ns" and len(args) == 4:
        return Node("or1", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "or2ns" and len(args) == 4:
        return Node("or2", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")

    # --- REGLAS DE SEMÁNTICA DE PASO CORTO (SOS) ---
    if constructor == "asssos" and len(args) == 3:
        return Node("ass", args[0], args[1], args[2], semantics="sos")
    if constructor == "skipsos" and len(args) == 3:
        return Node("skip", args[0], args[1], args[2], semantics="sos")
    if constructor == "comp1sos" and len(args) == 5:
        return Node("comp^1", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "comp2sos" and len(args) == 5:
        return Node("comp^2", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "ifttsos" and len(args) == 4:
        return Node("if-tt", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "ifffsos" and len(args) == 4:
        return Node("if-ff", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "whilesos" and len(args) == 4:
        return Node("while", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "repeatsos" and len(args) == 4:
        return Node("repeat", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "forsos" and len(args) == 4:
        return Node("for", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "abortsos" and len(args) == 3:
        return Node("abort", args[0], args[1], args[2], semantics="sos")
    if constructor == "compabortsos" and len(args) == 4:
        return Node("comp-abort", args[0], args[1], args[3], (parse_tree(args[2], "sos"),), semantics="sos")
    if constructor == "assertsos" and len(args) == 4:
        return Node("assert", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "or1sos" and len(args) == 4:
        return Node("or1", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "or2sos" and len(args) == 4:
        return Node("or2", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "par1sos" and len(args) == 5:
        return Node("par^1", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "par2sos" and len(args) == 5:
        return Node("par^2", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "par3sos" and len(args) == 5:
        return Node("par^3", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "par4sos" and len(args) == 5:
        return Node("par^4", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "protectsos" and len(args) == 4:
        return Node("protect", args[0], args[1], args[3], (parse_tree(args[2], "sos"),), semantics="sos")

    raise ValueError(f"Constructor no soportado: {constructor}/{len(args)}")


def identifier_latex(name: str) -> str:
    name = name.lstrip("'").replace("_", r"\_")
    return rf"\mathit{{{name}}}"


def statement_latex(text: str) -> str:
    variables: list[str] = []

    def save_variable(match: re.Match) -> str:
        variables.append(identifier_latex(match.group(1)))
        return f"@@V{len(variables) - 1}@@"

    text = re.sub(r"\s+", " ", text.strip())
    text = re.sub(r"'([A-Za-z0-9_-]+)", save_variable, text)

    # --- TRANSFORMACIÓN DE PROTECT A < S > ---
    text = re.sub(r"\bprotect\s*\((.*?)\)", r"\\langle \1 \\rangle", text)
    text = re.sub(r"\bprotect\s+([^\(\)].*)", r"\\langle \1 \\rangle", text)

    replacements = [
        ("<=?", r"\leq"), ("=?", "="), ("&&?", r"\land"),
        ("!", r"\neg"), ("++", "+"), ("**", r"\cdot"),
        ("--", "-"), (":=", r"\mathrel{:=}"),
        ("|||", r"\mathbin{||}"), ("||", r"\mathbin{||}"),
    ]
    for old, new in replacements:
        text = text.replace(old, new)

    text = re.sub(r"\bpar\b", lambda _: r"\mathbin{||}", text)
    text = re.sub(r"\bor\b", lambda _: r"\mathbin{|}", text)
    text = re.sub(r"(?<!\|)\|(?!\|)", lambda _: r"\mathbin{|}", text)

    keywords = ("skip", "abort", "if", "then", "else", "while", "do", "repeat", "until", "for", "to", "assert", "before", "true", "false")
    for word in keywords:
        text = re.sub(rf"\b{word}\b", lambda m, w=word: rf"\mathbf{{{w}}}", text)

    for i, variable in enumerate(variables):
        text = text.replace(f"@@V{i}@@", variable)

    text = text.replace(" ", r"\;")
    return text


class Context:
    def __init__(self):
        self.sigma_keys = {}
        self.sigma_raw_texts = {}
        self.statement_map = {}
        self.statement_values = {}
        self.subtrees = []
        self.max_stat_length = 30
        self.tree_counter = 0

    def get_sigma(self, text: str) -> str:
        clean_text = re.sub(r"\s+", " ", text.strip())
        if clean_text == "stuck": return r"\mathbf{stuck}"
        if clean_text == "Bottom": return r"\bot"
        if clean_text == "empty": return r"\varnothing"

        norm_key = re.sub(r"[\s'\(\)]+", "", clean_text)
        if norm_key not in self.sigma_keys:
            sig_id = len(self.sigma_keys)
            self.sigma_keys[norm_key] = sig_id
            self.sigma_raw_texts[sig_id] = clean_text

        sig_id = self.sigma_keys[norm_key]
        return f"@@SIG_{sig_id}@@"

    def get_statement(self, text: str) -> str:
        clean_text = re.sub(r"\s+", " ", text.strip())
        length_check_text = clean_text.replace("'", "")

        if len(length_check_text) > self.max_stat_length:
            if clean_text not in self.statement_map:
                i = len(self.statement_map) + 1
                name = rf"S_{{{i}}}"
                self.statement_map[clean_text] = name
                self.statement_values[name] = statement_latex(clean_text)
            return self.statement_map[clean_text]

        return statement_latex(clean_text)

    def format_state_value(self, text: str) -> str:
        if text == "Bottom": return r"\bot"
        bindings = re.findall(r"'?([a-zA-Z0-9_-]+)\s*(?:\|->|:=)\s*(-?\d+)", text)
        if bindings:
            items = [rf"{identifier_latex(name)} \mapsto {value}" for name, value in bindings]
            return r"\{" + r",\; ".join(items) + r"\}"

        safe = text.replace("_", r"\_").replace("%", r"\%").replace("#", r"\#")
        return rf"\mathtt{{{safe}}}"


def get_transition(node: Node, ctx: Context) -> str:
    stmt = ctx.get_statement(node.statement)
    left = rf"\left\langle {stmt},\; {ctx.get_sigma(node.before)}\right\rangle"

    if node.is_stuck:
        arrow = r"\mathbin{\not\longrightarrow}" if node.semantics == "ns" else r"\mathbin{\not\Rightarrow}"
        right = r"\mathbf{stuck}"
    else:
        arrow = r"\longrightarrow" if node.semantics == "ns" else r"\Rightarrow"
        if node.semantics == "sos" and node.next_stat:
            next_stmt = ctx.get_statement(node.next_stat)
            right = rf"\left\langle {next_stmt},\; {ctx.get_sigma(node.after)}\right\rangle"
        else:
            right = ctx.get_sigma(node.after)

    return rf"{left} {arrow} {right}"


def format_axiom(node: Node, ctx: Context) -> str:
    judgement = get_transition(node, ctx)
    sem_label = "ns" if node.semantics == "ns" else "sos"
    return rf"{judgement}\;\mathrm{{[{node.rule}_{{{sem_label}}}]}}"


def format_rule(node: Node, child_derivs: list[str], ctx: Context) -> str:
    judgement = get_transition(node, ctx)
    sem_label = "ns" if node.semantics == "ns" else "sos"
    premises = r"\qquad".join(child_derivs)
    return rf"\frac{{{premises}}}{{{judgement}}}\;\mathrm{{[{node.rule}_{{{sem_label}}}]}}"


def split_tree(node: Node, ctx: Context) -> str:
    if node.rule == "seq":
        child_ids = []
        for child in node.children:
            cid = split_tree(child, ctx)
            if cid:
                child_ids.extend(cid.split(","))
        return ",".join(child_ids)

    child_derivs = []
    for child in node.children:
        if child.rule == "seq":
            cid = split_tree(child, ctx)
            if cid:
                child_derivs.append(f"@@T_{cid}@@")
        elif child.children:
            child_id = split_tree(child, ctx)
            child_derivs.append(f"@@T_{child_id}@@")
        else:
            child_axiom = format_axiom(child, ctx)
            if len(child_axiom) > 160:
                child_id = split_tree(child, ctx)
                child_derivs.append(f"@@T_{child_id}@@")
            else:
                child_derivs.append(child_axiom)

    my_id = str(ctx.tree_counter)
    ctx.tree_counter += 1

    if not node.children:
        ctx.subtrees.append((my_id, format_axiom(node, ctx)))
    else:
        ctx.subtrees.append((my_id, format_rule(node, child_derivs, ctx)))
    return my_id


def build_semantics_section(tree: Node, title: str) -> str:
    ctx = Context()
    main_steps = list(tree.children) if tree.rule == "seq" else [tree]

    for step_node in main_steps:
        split_tree(step_node, ctx)

    if not ctx.subtrees:
        return rf"\section*{{{title}}}"

    tree_display_map = {uid: str(idx + 1) for idx, (uid, _) in enumerate(ctx.subtrees)}

    def replace_tree_ref(m: re.Match) -> str:
        raw_ids = m.group(1).split(",")
        mapped = [
            rf"\mathcal{{T}}_{{{tree_display_map[i]}}}"
            for i in raw_ids
            if i in tree_display_map
        ]
        return r", \; ".join(mapped) if mapped else r"\mathcal{T}"

    derivations_tex_list = []
    for idx, (uid, tex) in enumerate(ctx.subtrees):
        if idx > 0:
            derivations_tex_list.append(r"\[ \Downarrow \]")

        final_tex = re.sub(r"@@T_([0-9,]+)@@", replace_tree_ref, tex)
        final_tex = re.sub(r"@@SIG_(\d+)@@", lambda m: f"\\sigma_{{{int(m.group(1)) + 1}}}", final_tex)
        derivations_tex_list.append(rf"\[ \mathcal{{T}}_{{{tree_display_map[uid]}}} = {final_tex} \]")

    derivations_tex = "\n\\vspace{0.1cm}\n".join(derivations_tex_list)

    stmt_rows = [rf"{name} &= \parbox[t]{{0.85\linewidth}}{{$\raggedright {value}$}} \\" for name, value in ctx.statement_values.items()]
    statements_tex = f"\n\\subsubsection*{{Sentencias Abreviadas}}\n\\begin{{align*}}\n" + "\n".join(stmt_rows) + f"\n\\end{{align*}}" if stmt_rows else ""

    state_items = [rf"\noindent $\sigma_{{{sig_id + 1}}} = {ctx.format_state_value(clean_text)}$ \par" for sig_id, clean_text in ctx.sigma_raw_texts.items()]
    states_tex = f"\n\\subsubsection*{{Estados Registrados}}\n\\begin{{multicols}}{{3}}\n" + "\n".join(state_items) + f"\n\\end{{multicols}}" if state_items else ""

    return rf"""\section*{{{title}}}

{derivations_tex}

{statements_tex}

{states_tex}
"""


def extract_search_results(output: str, semantics: str) -> list[Node]:
    pattern = r"[X_a-zA-Z0-9]+:(?:Tree|Result|SeqSOS|Config)\s*-->\s*(.*?)(?=\n\s*Solution|\n\s*No more solutions|\n\s*Bye\.|\Z)"
    solutions = re.findall(pattern, output, re.DOTALL)

    if not solutions:
        match_single = re.search(r"result\s+[^:]+:\s*(.*)", output, re.DOTALL)
        if match_single:
            term = match_single.group(1).split("\nBye.")[0].strip()
            return [parse_tree(term, semantics)]
        raise RuntimeError("No se encontraron soluciones válidas en la salida de Maude.\n" + output)

    return [parse_tree(term.strip(), semantics) for term in solutions]


def run_maude_search(program_term: str, main_file: Path, semantics: str) -> list[Node]:
    maude = shutil.which("maude")
    if not maude:
        raise RuntimeError("No se encuentra 'maude' en PATH.")

    module = "SOS-WHILE-PROOFS" if semantics == "sos" else "NS-WHILE-PROOFS"
    search_cmd = f"search in {module} : run({program_term}) =>! X:Tree .\nquit\n" if semantics == "sos" else f"search in {module} : {program_term} =>! X:Tree .\nquit\n"

    process = subprocess.run(
        [maude, "-no-banner", main_file.name],
        input=search_cmd, text=True, capture_output=True, cwd=main_file.parent
    )
    return extract_search_results(process.stdout + process.stderr, semantics)


def generate_multipage_pdf(trees: list[Node], mode_label: str) -> str:
    n_branches = len(trees)
    pages = []

    for idx, tree in enumerate(trees, start=1):
        title = f"Rama {idx} de {n_branches} ({mode_label})"
        pages.append(build_semantics_section(tree, title))

    full_body = "\n\n\\newpage\n\n".join(pages)

    return rf"""\documentclass[12pt,a4paper]{{article}}
\usepackage[margin=1.2cm, landscape]{{geometry}}
\usepackage{{amsmath}}
\usepackage{{amssymb}}
\usepackage{{multicol}}
\allowdisplaybreaks
\pagestyle{{empty}}
\begin{{document}}

\title{{\textbf{{Exploración Semántica No Determinista y Concurrente ($S_1 \mathbin{{||}} S_2$)}}}}
\date{{\vspace{{-1cm}}}}
\maketitle

{full_body}

\end{{document}}
"""


def generate_comparison_latex(trees_ns: list[Node], trees_sos: list[Node]) -> str:
    pages = []

    for idx, tree_ns in enumerate(trees_ns, start=1):
        title = f"1. Semántica Natural (NS) -- Rama {idx} de {len(trees_ns)}" if len(trees_ns) > 1 else "1. Semántica Natural (NS)"
        pages.append(build_semantics_section(tree_ns, title))

    for idx, tree_sos in enumerate(trees_sos, start=1):
        title = f"2. Semántica SOS -- Rama {idx} de {len(trees_sos)}" if len(trees_sos) > 1 else "2. Semántica SOS"
        pages.append(build_semantics_section(tree_sos, title))

    full_body = "\n\n\\newpage\n\n".join(pages)

    return rf"""\documentclass[12pt,a4paper]{{article}}
\usepackage[margin=1.2cm, landscape]{{geometry}}
\usepackage{{amsmath}}
\usepackage{{amssymb}}
\usepackage{{multicol}}
\allowdisplaybreaks
\pagestyle{{empty}}
\begin{{document}}

\begin{{center}}
  {{\bfseries\Large Comparativa de Semánticas Formales (NS vs SOS)}}
\end{{center}}
\vspace{{4pt}}

{full_body}

\end{{document}}
"""


def compile_pdf_in_temp(latex_code: str, output_pdf_path: Path) -> None:
    pdflatex = shutil.which("pdflatex")
    if not pdflatex:
        raise RuntimeError("No se encuentra 'pdflatex' en PATH.")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        tex_file = tmp_path / "derivation.tex"
        tex_file.write_text(latex_code, encoding="utf-8")

        process = subprocess.run(
            [pdflatex, "-interaction=nonstopmode", "-halt-on-error", tex_file.name],
            cwd=tmp_path, text=True, capture_output=True
        )
        if process.returncode != 0:
            raise RuntimeError("Error al compilar LaTeX:\n\n" + process.stdout)

        shutil.copy(tmp_path / "derivation.pdf", output_pdf_path)


def main() -> None:
    args = sys.argv[1:]

    mode = "ns"
    if "--compare" in args or "--both" in args:
        mode = "compare"
        if "--compare" in args: args.remove("--compare")
        if "--both" in args: args.remove("--both")
    elif "--sos" in args:
        mode = "sos"
        args.remove("--sos")
    elif "--ns" in args:
        args.remove("--ns")

    program_file = Path(args[0] if len(args) > 0 else "program.while").resolve()
    output_pdf = Path(args[1] if len(args) > 1 else "derivation.pdf").resolve()

    main_file = Path("main.maude").resolve()
    if not main_file.exists():
        main_file = (Path(__file__).parent / "main.maude").resolve()

    if not main_file.exists():
        raise FileNotFoundError("No se encontró el archivo 'main.maude' en el directorio actual ni junto al script.")

    program = program_file.read_text(encoding="utf-8").strip().rstrip(".")
    program_term = program if program.startswith("<") else f"< {program} , empty >"

    if mode == "compare":
        check_ns_compatibility(program)
        print("Modo Comparativa activado: Buscando ejecuciones en NS y SOS...")
        trees_ns = run_maude_search(program_term, main_file, "ns")
        trees_sos = run_maude_search(program_term, main_file, "sos")
        print(f"Ramas encontradas -> NS: {len(trees_ns)}, SOS: {len(trees_sos)}")
        print("Generando LaTeX comparativo y compilando...")
        latex_code = generate_comparison_latex(trees_ns, trees_sos)
    else:
        if mode == "ns":
            check_ns_compatibility(program)
        print(f"Buscando ejecuciones no deterministas en Maude ({mode.upper()})...")
        trees = run_maude_search(program_term, main_file, mode)
        print(f"Se detectaron {len(trees)} rama(s) de ejecución. Generando LaTeX multipágina...")
        latex_code = generate_multipage_pdf(trees, mode.upper())

    compile_pdf_in_temp(latex_code, output_pdf)
    print(f"¡Éxito! PDF generado correctamente: {output_pdf}")


if __name__ == "__main__":
    main()