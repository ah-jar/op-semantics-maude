#!/usr/bin/env python3
r"""
Ejecuta Maude y genera árboles de derivación formal en estricta notación Nielson.
Soporta Semántica Natural (NS) y Semántica Operacional de Paso Corto (SOS),
incluyendo bloques locales (begin ... end), declaraciones (var) y restore.
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
            "Ejecute el script en modo SOS mediante el modificador '--sos'.\n"
        )


def has_nondeterminism(program_text: str) -> bool:
    pattern = r"\b(par|or)\b|\|\||\|(?!>)"
    return bool(re.search(pattern, program_text))


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

    match_run_stuck = re.fullmatch(r"run\(\s*\(?\s*<\s*(.*?)\s*,\s*(.*?)\s*>\s*\)?\s*\)", term)
    if match_run_stuck:
        return Node("stuck", match_run_stuck.group(1).strip(), match_run_stuck.group(2).strip(), "stuck", semantics=semantics, is_stuck=True)

    match = re.fullmatch(r"([A-Za-z0-9_-]+)\((.*)\)", term)
    if not match:
        raise ValueError(f"Término de árbol no reconocido:\n{term}")

    constructor = match.group(1)
    args = split_arguments(match.group(2))

    if ("par" in constructor or "protect" in constructor) and semantics == "ns":
        raise ValueError("Los operadores 'par' y 'protect' no están soportados en Semántica Natural (NS).")

    if constructor == "seqsos":
        children = tuple(parse_tree(arg, "sos") for arg in args if arg != "nilSOS")
        return Node("seq", "", "", "", children, semantics="sos")

    # --- Reglas Semántica Natural (NS) ---
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

    # Bloques y declaraciones (NS)
    if constructor == "blockns" and len(args) == 5:
        return Node("block", args[0], args[1], args[4], (parse_tree(args[2], "ns"), parse_tree(args[3], "ns")), semantics="ns")
    if constructor == "varns" and len(args) == 4:
        return Node("var", args[0], args[1], args[3], (parse_tree(args[2], "ns"),), semantics="ns")
    if constructor == "nonens" and len(args) == 3:
        return Node("none", args[0], args[1], args[2], semantics="ns")

    # --- Reglas Semántica SOS ---
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

    # Bloques y declaraciones (SOS)
    if constructor == "beginblocksos" and len(args) == 5:
        return Node("begin-block", args[0], args[1], args[4], (parse_tree(args[2], "sos"),), next_stat=args[3], semantics="sos")
    if constructor == "varsos":
        if len(args) == 4:
            if any(args[2].startswith(c) for c in ("varsos", "nonesos", "seqsos")):
                return Node("var", args[0], args[1], args[3], (parse_tree(args[2], "sos"),), semantics="sos")
            else:
                return Node("var", args[0], args[1], args[3], next_stat=args[2], semantics="sos")
    if constructor == "nonesos" and len(args) == 3:
        return Node("none", args[0], args[1], args[2], semantics="sos")
    if constructor == "endblocksos" and len(args) == 3:
        return Node("end-block", args[0], args[1], args[2], semantics="sos")

    raise ValueError(f"Constructor no soportado: {constructor}/{len(args)}")


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
    return judgement + r"\;\mathrm{[" + node.rule + r"_{" + sem_label + r"}]}"


def format_rule(node: Node, child_derivs: list[str], ctx: Context) -> str:
    judgement = get_transition(node, ctx)
    sem_label = "ns" if node.semantics == "ns" else "sos"
    premises = r"\qquad".join(child_derivs)
    return r"\frac{" + premises + r"}{" + judgement + r"}\;\mathrm{[" + node.rule + r"_{" + sem_label + r"}]}"


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
    """Obtiene (sigma_ini, sigma_fin, S_ini, S_fin) del árbol principal."""
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
    # 1. Buscar resultados provistos por comandos 'search'
    pattern = r"[X_a-zA-Z0-9]+:(?:Tree|Result|SeqSOS|Config)\s*-->\s*(.*?)(?=\n\s*Solution|\n\s*No more solutions|\n\s*Bye\.|\Z)"
    solutions = re.findall(pattern, output, re.DOTALL)

    if solutions:
        return [parse_tree(term.strip(), semantics) for term in solutions]

    # 2. Buscar resultados provistos por 'rewrite' o 'reduce' (result <Type>: ...)
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
        if semantics == "sos":
            maude_cmd = f"search in {module} : run({program_term}) =>! X:Tree .\nquit\n"
        else:
            maude_cmd = f"search in {module} : {program_term} =>! X:Tree .\nquit\n"
    else:
        print(f"[{semantics.upper()}] Programa determinista. Ejecutando mediante 'rewrite' directo...")
        if semantics == "sos":
            maude_cmd = f"rewrite in {module} : run({program_term}) .\nquit\n"
        else:
            maude_cmd = f"rewrite in {module} : {program_term} .\nquit\n"

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
  {\bfseries\Large Derivación Semántica Formal -- Notación Nielson con Estados $\sigma_k$}
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
        title = f"2. Semántica SOS -- Rama {idx} de {len(trees_sos)}" if len(trees_sos) > 1 else "2. Semántica SOS"
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
    print(f"¡Éxito! PDF compacto generado correctamente: {output_pdf}")


if __name__ == "__main__":
    main()