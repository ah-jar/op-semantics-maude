#!/usr/bin/env python3
r"""
Generador automático de árboles de derivación formal para el lenguaje WHILE.
Basado estrictamente en los módulos Maude NS-WHILE-PROOFS y SOS-WHILE-PROOFS.
Compila el resultado en un documento PDF en notación Nielson.
"""

import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

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
    if re.search(r"\b(par|protect)\b", program_text) or "||" in program_text:
        sys.exit(
            "\n[Error de Semántica] Los operadores 'par' (||) y 'protect' "
            "no están soportados en Semántica Natural (NS).\n"
            "Ejecute el script en modo SOS mediante '-m sos' o '--sos'.\n"
        )


def has_nondeterminism(program_text: str) -> bool:
    pattern = r"\b(par|or)\b|\|\||\|(?!>)"
    return bool(re.search(pattern, program_text))


def split_arguments(text: str) -> list[str]:
    """Divide argumentos considerando la anidación de paréntesis y corchetes."""
    text = text.strip()
    if not text:
        return []

    while text.startswith("(") and text.endswith(")"):
        depth = 0
        matched_all = True
        for i, c in enumerate(text):
            if c in "([{<":
                depth += 1
            elif c in ")]}>":
                depth -= 1
            if depth == 0 and i < len(text) - 1:
                matched_all = False
                break
        if matched_all:
            text = text[1:-1].strip()
        else:
            break

    parts = []
    current = []
    depth = 0

    for i, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == "<":
            depth += 1
        elif char == ">":
            if i > 0 and text[i - 1] in ("-", "=", "|", "?", "<"):
                pass
            else:
                depth -= 1

        if char == "," and depth == 0:
            part = "".join(current).strip()
            if part:
                parts.append(part)
            current = []
        else:
            current.append(char)

    last_part = "".join(current).strip()
    if last_part:
        parts.append(last_part)

    return parts


def parse_config(config_str: str) -> tuple[str, str]:
    """Extrae (sentencia, estado) de una configuración < S , M >."""
    config_str = config_str.strip()
    if config_str.startswith("<") and config_str.endswith(">"):
        config_str = config_str[1:-1].strip()
    parts = split_arguments(config_str)
    if len(parts) >= 2:
        return parts[0], ", ".join(parts[1:])
    elif len(parts) == 1:
        return parts[0], "empty"
    return config_str, "empty"


def parse_tree(term: str, semantics: str = "ns") -> Node:
    term = re.sub(r"\s+", " ", term).strip()
    term = re.sub(r"\s*Bye\.\s*$", "", term).strip()

    # Detección de estado bloqueado (stuck)
    match_run_stuck = re.fullmatch(r"run\(\s*\(?\s*<\s*(.*?)\s*,\s*(.*?)\s*>\s*\)?\s*\)", term)
    if match_run_stuck:
        return Node("stuck", match_run_stuck.group(1).strip(), match_run_stuck.group(2).strip(), "stuck", semantics=semantics, is_stuck=True)

    match = re.fullmatch(r"([A-Za-z0-9_-]+)\((.*)\)", term)
    if not match:
        raise ValueError(f"Término de árbol no reconocido:\n{term}")

    constructor = match.group(1)
    args = split_arguments(match.group(2))

    # Cierre transitivo en SOS
    if constructor == "seqsos":
        children = tuple(parse_tree(arg, "sos") for arg in args if arg and arg != "nilSOS")
        return Node("seq", "", "", "", children, semantics="sos")

    # Mapeo universal para el operador node(Qid, Judg, ProofTL)
    if constructor == "node" and len(args) >= 2:
        raw_qid = args[0].strip().lstrip("'")
        
        # Mapeo de Qid a etiquetas de reglas formateadas
        rule_map_ns = {
            "assignns": "ass", "skipns": "skip", "abortns": "abort", "compns": "comp",
            "compabortns": "comp-abort", "ifttns": "if-tt", "ifffns": "if-ff",
            "whilettns": "while-tt", "whileabortns": "while-abort", "whileffns": "while-ff",
            "repeatffns": "repeat-ff", "repeatttns": "repeat-tt", "repeatabortns": "repeat-abort",
            "forttns": "for-tt", "forffns": "for-ff", "forabortns": "for-abort",
            "assertttns": "assert-tt", "assertffns": "assert-ff", "or1ns": "or1", "or2ns": "or2",
            "blockns": "block", "varns": "var", "nonens": "none",
        }
        rule_map_sos = {
            "asssos": "ass", "skipsos": "skip", "comp1sos": "comp^1", "comp2sos": "comp^2",
            "compabortsos": "comp-abort", "ifttsos": "if-tt", "ifffsos": "if-ff",
            "whilesos": "while", "repeatsos": "repeat", "forsos": "for", "abortsos": "abort",
            "assertsos": "assert", "or1sos": "or1", "or2sos": "or2", "par1sos": "par^1",
            "par2sos": "par^2", "par3sos": "par^3", "par4sos": "par^4", "protectsos": "protect",
            "beginblocksos": "begin-block", "varsos": "var", "nonesos": "none", "endblocksos": "end-block",
        }

        rule_map = rule_map_sos if semantics == "sos" else rule_map_ns
        rule_label = rule_map.get(raw_qid, raw_qid.replace("sos", "").replace("ns", "").replace("_", "-"))

        judgement = args[1]
        statement, before, next_stat, after = "", "", None, ""

        if "-->" in judgement or "==>" in judgement:
            arrow = "-->" if "-->" in judgement else "==>"
            left, right = judgement.split(arrow, 1)
            statement, before = parse_config(left.strip())

            right = right.strip()
            if arrow == "==>" and right.startswith("<") and right.endswith(">"):
                next_stat, after = parse_config(right)
            else:
                next_stat = None
                after = right
        
        # Subárboles (ProofTL) pasados en argumentos posteriores
        child_args = args[2:]
        children = tuple(parse_tree(arg, semantics) for arg in child_args if arg and arg not in ("nilProofTL", "nilSOS"))

        return Node(rule_label, statement, before, after, children=children, next_stat=next_stat, semantics=semantics)

    raise ValueError(f"Constructor de Maude no reconocido: {constructor}/{len(args)}")


def identifier_latex(name: str) -> str:
    name = name.lstrip("'").replace("_", r"\_")
    return r"\mathit{" + name + "}"


def statement_latex(text: str) -> str:
    variables: list[str] = []

    def save_variable(match: re.Match) -> str:
        variables.append(identifier_latex(match.group(1)))
        return f"@@V{len(variables) - 1}@@"

    text = re.sub(r"\s+", " ", text.strip())
    text = text.replace("emptyDecv", r"\varepsilon")
    text = re.sub(r"'([A-Za-z0-9_-]+)", save_variable, text)

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

    keywords = (
        "skip", "abort", "if", "then", "else", "while", "do", "repeat", 
        "until", "for", "to", "assert", "before", "true", "false",
        "begin", "end", "var", "restore"
    )
    for word in keywords:
        text = re.sub(rf"\b{word}\b", lambda m, w=word: rf"\mathbf{{{w}}}", text)

    for i, variable in enumerate(variables):
        text = text.replace(f"@@V{i}@@", variable)

    text = text.replace(" ", r"\;")
    return text


def parse_assignment_parts(text: str) -> tuple[str, str]:
    text = text.strip()
    if text.startswith("var "):
        text = text[4:].strip()
    if ";" in text:
        text = text.split(";")[0].strip()
    if ":=" in text:
        parts = text.split(":=", 1)
        var_part = identifier_latex(parts[0].strip())
        expr_part = statement_latex(parts[1].strip())
        return var_part, expr_part
    return identifier_latex(text), ""


def format_concrete_bindings(raw_text: str) -> str:
    clean_text = re.sub(r"\s+", " ", raw_text.strip())
    if clean_text in ("empty", "null", "", "s", "sigma"):
        return r"\varnothing"
    bindings = re.findall(r"'?([a-zA-Z0-9_-]+)\s*(?:\|->|:=)\s*(-?\d+|'[a-zA-Z0-9_-]+)", clean_text)
    if bindings:
        items = [identifier_latex(k) + r" \mapsto " + (identifier_latex(v) if v.startswith("'") else v) for k, v in bindings]
        return r"\{" + r",\; ".join(items) + r"\}"
    return ""


class Context:
    def __init__(self, initial_raw: str = "", final_raw: str = "", initial_stmt_raw: str = "", final_stmt_raw: str = ""):
        self.statement_map = {}
        self.statement_values = {}
        self.statement_tags = {}
        self.raw_to_sigma = {}
        self.legend_dict = {}
        self.legend_order = []
        self.subtrees = []
        self.max_stat_length = 35
        self.tree_counter = 0
        self.sigma_counter = 0
        self.initial_raw = initial_raw
        self.final_raw = final_raw
        self.initial_stmt_raw = re.sub(r"\s+", " ", initial_stmt_raw.strip())
        self.final_stmt_raw = re.sub(r"\s+", " ", final_stmt_raw.strip())

    def get_sigma(self, raw_text: str) -> str:
        clean = re.sub(r"\s+", " ", raw_text.strip())
        if not clean:
            clean = "empty"

        if clean not in self.raw_to_sigma:
            symbol = r"\sigma_{" + str(self.sigma_counter) + r"}"
            self.raw_to_sigma[clean] = symbol
            self.sigma_counter += 1
            self.legend_order.append(clean)

            concrete = format_concrete_bindings(clean)
            self.legend_dict[clean] = {
                "symbol": symbol,
                "formula": None,
                "concrete": concrete
            }

        return self.raw_to_sigma[clean]

    def register_substitution_legend(self, sigma_symbol: str, substitution_formula: str, raw_after: str) -> None:
        for raw_key, sym in self.raw_to_sigma.items():
            if sym == sigma_symbol:
                if raw_key in self.legend_dict:
                    self.legend_dict[raw_key]["formula"] = substitution_formula
                    concrete = format_concrete_bindings(raw_after)
                    if concrete:
                        self.legend_dict[raw_key]["concrete"] = concrete
                break

    def get_statement(self, text: str) -> str:
        clean_text = re.sub(r"\s+", " ", text.strip())
        length_check_text = clean_text.replace("'", "")

        if len(length_check_text) > self.max_stat_length:
            if clean_text not in self.statement_map:
                i = len(self.statement_map) + 1
                name = r"S_{" + str(i) + r"}"
                self.statement_map[clean_text] = name
                self.statement_values[name] = statement_latex(clean_text)

                tags = []
                if clean_text == self.initial_stmt_raw:
                    tags.append(r"\mathbf{(S_{\text{ini}})}")
                if clean_text == self.final_stmt_raw and clean_text != self.initial_stmt_raw:
                    tags.append(r"\mathbf{(S_{\text{fin}})}")
                if tags:
                    self.statement_tags[name] = " ".join(tags)

            return self.statement_map[clean_text]

        return statement_latex(clean_text)


def format_rule_label(rule: str, sem_tag: str) -> str:
    rule_clean = rule.replace("_", "-")
    if "^" in rule_clean:
        base, sup = rule_clean.split("^", 1)
        return rf"\;\mathrm{{[{base}^{{{sup}}}_{{{sem_tag}}}]}}"
    return rf"\;\mathrm{{[{rule_clean}_{{{sem_tag}}}]}}"


def get_transition(node: Node, ctx: Context) -> str:
    stmt = ctx.get_statement(node.statement)
    sigma_before = ctx.get_sigma(node.before)
    left = r"\left\langle " + stmt + r",\; " + sigma_before + r"\right\rangle"

    is_decl = node.rule in ("var", "none")

    if node.is_stuck:
        arrow_base = r"\mathbin{\not\longrightarrow}" if node.semantics == "ns" else r"\mathbin{\not\Rightarrow}"
        arrow = arrow_base + r"_D" if is_decl else arrow_base
        right = r"\mathbf{stuck}"
    else:
        arrow_base = r"\longrightarrow" if node.semantics == "ns" else r"\Rightarrow"
        arrow = arrow_base + r"_D" if is_decl else arrow_base

        if node.semantics == "sos" and node.next_stat:
            next_stmt = ctx.get_statement(node.next_stat)
            sigma_after = ctx.get_sigma(node.after)
            right = r"\left\langle " + next_stmt + r",\; " + sigma_after + r"\right\rangle"
        else:
            if node.rule == "ass":
                var_latex, expr_latex = parse_assignment_parts(node.statement)
                right = sigma_before + r"[" + var_latex + r" \mapsto \mathcal{A}\llbracket " + expr_latex + r" \rrbracket " + sigma_before + r"]"
                sigma_after = ctx.get_sigma(node.after)
                ctx.register_substitution_legend(sigma_after, right, node.after)
            elif node.rule == "var" and ":=" in node.statement:
                var_latex, expr_latex = parse_assignment_parts(node.statement)
                right = sigma_before + r"[" + var_latex + r" \mapsto \mathcal{A}\llbracket " + expr_latex + r" \rrbracket " + sigma_before + r"]"
                sigma_after = ctx.get_sigma(node.after)
                ctx.register_substitution_legend(sigma_after, right, node.after)
            elif node.rule == "block" and len(node.children) >= 2:
                body_node = node.children[1]
                sigma_k = ctx.get_sigma(body_node.after)
                dv_latex = ctx.get_statement(node.children[0].statement) if node.children else r"D_V"
                right = sigma_k + r"[\text{DV}(" + dv_latex + r") \longmapsto " + sigma_before + r"]"
                sigma_after = ctx.get_sigma(node.after)
                ctx.register_substitution_legend(sigma_after, right, node.after)
            else:
                right = ctx.get_sigma(node.after)

    return left + " " + arrow + " " + right


def format_axiom(node: Node, ctx: Context) -> str:
    judgement = get_transition(node, ctx)
    sem_label = "ns" if node.semantics == "ns" else "sos"
    return judgement + format_rule_label(node.rule, sem_label)


def format_rule(node: Node, child_derivs: list[str], ctx: Context) -> str:
    judgement = get_transition(node, ctx)
    sem_label = "ns" if node.semantics == "ns" else "sos"
    premises = r"\qquad".join(child_derivs)
    return r"\frac{" + premises + r"}{" + judgement + r"}" + format_rule_label(node.rule, sem_label)


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


def get_tree_bounds(tree: Node) -> tuple[str, str, str, str]:
    if tree.rule == "seq" and tree.children:
        init_sigma, _, init_stmt, _ = get_tree_bounds(tree.children[0])
        _, fin_sigma, _, fin_stmt = get_tree_bounds(tree.children[-1])
        return init_sigma, fin_sigma, init_stmt, fin_stmt

    fin_stmt = tree.next_stat if (tree.semantics == "sos" and tree.next_stat) else tree.statement
    return tree.before, tree.after, tree.statement, fin_stmt


def build_semantics_section(tree: Node, title: str) -> str:
    init_raw, fin_raw, init_stmt_raw, fin_stmt_raw = get_tree_bounds(tree)
    ctx = Context(
        initial_raw=init_raw,
        final_raw=fin_raw,
        initial_stmt_raw=init_stmt_raw,
        final_stmt_raw=fin_stmt_raw
    )
    main_steps = list(tree.children) if tree.rule == "seq" else [tree]

    for step_node in main_steps:
        split_tree(step_node, ctx)

    if not ctx.subtrees:
        return r"\subsection*{" + title + "}"

    tree_display_map = {uid: str(idx + 1) for idx, (uid, _) in enumerate(ctx.subtrees)}

    def replace_tree_ref(m: re.Match) -> str:
        raw_ids = m.group(1).split(",")
        mapped = [
            r"\mathcal{T}_{" + tree_display_map[i] + "}"
            for i in raw_ids
            if i in tree_display_map
        ]
        return r", \; ".join(mapped) if mapped else r"\mathcal{T}"

    horizontal_blocks = []
    current_row = []
    current_length = 0
    MAX_ROW_LENGTH = 140

    for idx, (uid, tex) in enumerate(ctx.subtrees):
        final_tex = re.sub(r"@@T_([0-9,]+)@@", replace_tree_ref, tex)
        expr = r"\mathcal{T}_{" + tree_display_map[uid] + "} = " + final_tex
        expr_len = len(expr)

        if current_row and (current_length + expr_len > MAX_ROW_LENGTH):
            horizontal_blocks.append(r"\[ " + r" \qquad\qquad ".join(current_row) + r" \]")
            current_row = [expr]
            current_length = expr_len
        else:
            current_row.append(expr)
            current_length += expr_len

    if current_row:
        horizontal_blocks.append(r"\[ " + r" \qquad\qquad ".join(current_row) + r" \]")

    derivations_tex = "\n\\vspace{-0.2cm}\n".join(horizontal_blocks)

    stmt_rows = []
    for name, value in ctx.statement_values.items():
        tag = ctx.statement_tags.get(name, "")
        if tag:
            stmt_rows.append(name + r" &= " + value + r" \quad " + tag)
        else:
            stmt_rows.append(name + r" &= " + value)

    statements_tex = ""
    if stmt_rows:
        statements_tex = (
            "\\subsubsection*{Sentencias Abreviadas}\n"
            "{\\small\\begin{align*}\n" +
            " \\\\\n".join(stmt_rows) +
            "\n\\end{align*}}\n"
        )

    legend_rows = []
    for raw_key in ctx.legend_order:
        item = ctx.legend_dict[raw_key]
        sym = item["symbol"]
        formula = item["formula"]
        concrete = item["concrete"]

        is_init = (raw_key == ctx.initial_raw or (raw_key in ("s", "sigma", "empty", "null", "") and ctx.initial_raw in ("s", "sigma", "empty", "null", "")))
        is_fin = (raw_key == ctx.final_raw)

        tag_init = r" \; \mathbf{(\sigma_{\text{ini}})}"
        tag_fin = r" \; \mathbf{(\sigma_{\text{fin}})}"

        if formula:
            entry = sym + r" \equiv " + formula
            if concrete and concrete != r"\varnothing":
                entry += r" = " + concrete
        elif concrete:
            if concrete == r"\varnothing":
                entry = sym + r" \equiv \varnothing"
            else:
                entry = sym + r" \equiv " + concrete
        else:
            entry = sym + r" \equiv \text{Estado}"

        if is_init: entry += tag_init
        if is_fin: entry += tag_fin

        legend_rows.append(entry)

    legend_tex = (
        "\\subsubsection*{Leyenda de Estados}\n"
        "{\\small\\begin{multicols}{2}\n"
        "\\begin{itemize}[leftmargin=*,itemsep=1pt,topsep=1pt]\n" +
        "\n".join([rf"\item ${r}$" for r in legend_rows]) +
        "\n\\end{itemize}\n"
        "\\end{multicols}}\n"
    )

    return (
        r"\subsection*{" + title + "}\n"
        r"{\small" + "\n" +
        derivations_tex + "\n" +
        r"}" + "\n\n" +
        statements_tex + "\n" +
        legend_tex
    )


def extract_search_results(output: str, semantics: str) -> list[Node]:
    pattern = r"[X_a-zA-Z0-9]+:(?:Tree|ProofT|Result|SeqSOS|Config)\s*-->\s*(.*?)(?=\n\s*Solution|\n\s*No more solutions|\n\s*Bye\.|\Z)"
    solutions = re.findall(pattern, output, re.DOTALL)

    if solutions:
        return [parse_tree(term.strip(), semantics) for term in solutions]

    match_single = re.search(r"result\s+[A-Za-z0-9_-]+:\s*(.*?)(?=\nMaude>|\nBye\.|\Z)", output, re.DOTALL)
    if match_single:
        term = match_single.group(1).strip()
        return [parse_tree(term, semantics)]

    raise RuntimeError("No se encontraron soluciones válidas en la salida de Maude.\n" + output)


def run_maude_execution(program_term: str, program_raw: str, main_file: Path, semantics: str) -> list[Node]:
    maude = shutil.which("maude")
    if not maude:
        raise RuntimeError("No se encuentra 'maude' en PATH.")

    module = "SOS-WHILE-PROOFS" if semantics == "sos" else "NS-WHILE-PROOFS"
    is_nondet = has_nondeterminism(program_raw)

    if is_nondet:
        print(f"[{semantics.upper()}] Detectado no determinismo (par/or). Buscando todas las ramas con 'search'...")
        target_sort = "ProofT" if semantics == "sos" else "Result"
        maude_cmd = f"search in {module} : {'run(' + program_term + ')' if semantics == 'sos' else program_term} =>! X:{target_sort} .\nquit\n"
    else:
        print(f"[{semantics.upper()}] Programa determinista. Ejecutando mediante 'rewrite' directo...")
        maude_cmd = f"rewrite in {module} : {'run(' + program_term + ')' if semantics == 'sos' else program_term} .\nquit\n"

    process = subprocess.run(
        [maude, "-no-banner", main_file.name],
        input=maude_cmd, text=True, capture_output=True, cwd=main_file.parent
    )
    return extract_search_results(process.stdout + process.stderr, semantics)


def generate_multipage_pdf(trees: list[Node], mode_label: str) -> str:
    n_branches = len(trees)
    pages = []

    for idx, tree in enumerate(trees, start=1):
        title = f"Rama {idx} de {n_branches} ({mode_label})"
        pages.append(build_semantics_section(tree, title))

    full_body = "\n\n\\hrulefill\n\n".join(pages)

    return r"""\documentclass[10pt,a4paper]{article}
\usepackage[margin=1cm, landscape]{geometry}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{multicol}
\usepackage{enumitem}

\newcommand{\llbracket}{\mathopen{[\![}}
\newcommand{\rrbracket}{\mathclose{]\!]}}

\setlength{\parindent}{0pt}
\setlength{\jot}{2pt}
\allowdisplaybreaks
\pagestyle{empty}

\begin{document}

\begin{center}
  {\bfseries\Large Derivación Semántica Formal -- Notación Nielson}
\end{center}
\vspace{-0.3cm}

""" + full_body + r"""

\end{document}
"""


def generate_comparison_latex(trees_ns: list[Node], trees_sos: list[Node]) -> str:
    pages = []

    for idx, tree_ns in enumerate(trees_ns, start=1):
        title = f"1. Semántica Natural (NS) -- Rama {idx} de {len(trees_ns)}" if len(trees_ns) > 1 else "1. Semántica Natural (NS)"
        pages.append(build_semantics_section(tree_ns, title))

    for idx, tree_sos in enumerate(trees_sos, start=1):
        title = f"2. Semántica Operacional (SOS) -- Rama {idx} de {len(trees_sos)}" if len(trees_sos) > 1 else "2. Semántica Operacional (SOS)"
        pages.append(build_semantics_section(tree_sos, title))

    full_body = "\n\n\\hrulefill\n\n".join(pages)

    return r"""\documentclass[10pt,a4paper]{article}
\usepackage[margin=1cm, landscape]{geometry}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{multicol}
\usepackage{enumitem}

\newcommand{\llbracket}{\mathopen{[\![}}
\newcommand{\rrbracket}{\mathclose{]\!]}}

\setlength{\parindent}{0pt}
\setlength{\jot}{2pt}
\allowdisplaybreaks
\pagestyle{empty}

\begin{document}

\begin{center}
  {\bfseries\Large Comparativa de Semánticas Formales (NS vs SOS)}
\end{center}
\vspace{-0.3cm}

""" + full_body + r"""

\end{document}
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
    program_input = "program.while"
    output_input = "derivation.pdf"

    clean_args = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg in ("--sos", "-sos"):
            mode = "sos"
        elif arg in ("--ns", "-ns"):
            mode = "ns"
        elif arg in ("--compare", "--both", "-compare"):
            mode = "compare"
        elif arg in ("-m", "--mode") and i + 1 < len(args):
            mode = args[i + 1].lower()
            i += 1
        elif arg in ("-o", "--output") and i + 1 < len(args):
            output_input = args[i + 1]
            i += 1
        else:
            clean_args.append(arg)
        i += 1

    if clean_args:
        program_input = clean_args[0]
        if len(clean_args) > 1 and output_input == "derivation.pdf":
            output_input = clean_args[1]

    program_file = Path(program_input).resolve()
    output_pdf = Path(output_input).resolve()

    if not program_file.exists():
        sys.exit(f"[Error] No se encontró el archivo del programa: {program_file}")

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
        trees_ns = run_maude_execution(program_term, program, main_file, "ns")
        trees_sos = run_maude_execution(program_term, program, main_file, "sos")
        print(f"Ramas encontradas -> NS: {len(trees_ns)}, SOS: {len(trees_sos)}")
        print("Generando LaTeX comparativo compacto y compilando...")
        latex_code = generate_comparison_latex(trees_ns, trees_sos)
    else:
        if mode == "ns":
            check_ns_compatibility(program)
        trees = run_maude_execution(program_term, program, main_file, mode)
        print(f"Se generó el árbol de derivación ({len(trees)} rama(s)). Compilando LaTeX compacto...")
        latex_code = generate_multipage_pdf(trees, mode.upper())

    compile_pdf_in_temp(latex_code, output_pdf)
    print(f"¡Éxito! PDF comparativo generado correctamente: {output_pdf}")


if __name__ == "__main__":
    main()