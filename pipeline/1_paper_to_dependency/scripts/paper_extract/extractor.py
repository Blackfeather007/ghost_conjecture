from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .auxfile import parse_aux
from .preamble import extract_render_context, find_preamble, parse_newtheorem_commands
from .sections import SectionState, update_section_state
from .types import AuxLabel, TheoremEnv
from .util import paper_id_from_root_tex, read_text, stable_id, strip_comments


_RE_BEGIN = re.compile(r"\\begin\{([^}]+)\}")
_RE_LABEL = re.compile(r"\\label\{([^}]+)\}")
_REF_COMMANDS = ("ref", "eqref", "cref", "Cref", "autoref")
_RE_ANYREF = re.compile(r"\\(" + "|".join(_REF_COMMANDS) + r")\{([^}]+)\}")


EQUATION_ENVS = {
    "equation",
    "equation*",
    "align",
    "align*",
    "alignat",
    "alignat*",
    "gather",
    "gather*",
    "multline",
    "multline*",
    "flalign",
    "flalign*",
    "eqnarray",
    "eqnarray*",
}


def _extract_dependencies(latex: str) -> Tuple[List[str], List[Dict[str, Any]]]:
    labels: List[str] = []
    refs: List[Dict[str, Any]] = []
    for m in _RE_ANYREF.finditer(latex):
        cmd = m.group(1)
        payload = m.group(2)
        for lab in [p.strip() for p in payload.split(",") if p.strip()]:
            labels.append(lab)
            refs.append({"cmd": cmd, "label": lab})
    seen = set()
    uniq = []
    for lab in labels:
        if lab in seen:
            continue
        seen.add(lab)
        uniq.append(lab)
    return uniq, refs


def _caption_for(kind: str, printed_name: Optional[str], number: Optional[str]) -> Optional[str]:
    if not number:
        return None
    if kind == "equation":
        return f"Equation ({number})"
    if printed_name:
        return f"{printed_name} {number}"
    return number


def _make_block(
    *,
    kind: str,
    env_name: Optional[str],
    printed_name: Optional[str],
    label: Optional[str],
    location_file: str,
    start_line: int,
    end_line: int,
    section_state: Dict[str, Any],
    latex_lines: List[str],
    aux_labels: Dict[str, AuxLabel],
    origin_source_tex: str,
    origin_kind: str = "paper",
    origin_id: Optional[str] = None,
    parent: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    latex = "\n".join(latex_lines).strip("\n")
    deps, refs = _extract_dependencies(latex)

    display_number: Optional[str] = None
    number_source: str = "none"
    if label and label in aux_labels and aux_labels[label].number:
        display_number = aux_labels[label].number
        number_source = "aux"

    block_id = stable_id(location_file, str(start_line), kind, label or "", env_name or "")

    block: Dict[str, Any] = {
        "id": block_id,
        "kind": kind,
        "env": env_name,
        "label": label,
        "display": {
            "printed_name": printed_name,
            "number": display_number,
            "caption": _caption_for(kind, printed_name, display_number),
            "number_source": number_source,
        },
        "location": {
            "file": location_file,
            "start_line": start_line,
            "end_line": end_line,
        },
        "origin": {
            "source_tex": origin_source_tex,
            "source_kind": origin_kind,
            "source_id": origin_id,
        },
        "structure": section_state,
        "text": {
            "latex": latex,
        },
        "dependencies": {
            "labels": deps,
            "unresolved_labels": [],
            "refs": refs,
        },
        "formalization": {
            "status": "unformalized",
            "lean_files": [],
            "lean_decls": [],
            "assignee": None,
            "notes": None,
        },
        "annotations": {},
    }
    if parent:
        block["parent"] = parent
    return block


def _synth_label(kind: str, paper_id: str, file_path: str, start_line: int) -> str:
    base = f"{paper_id}:{Path(file_path).name}:{start_line}"
    return f"auto:{kind}:{base}"


def _extract_environment_block(
    lines: List[str],
    start_line_idx: int,
    env_name: str,
) -> Tuple[List[str], int, List[str]]:
    begin_pat = re.compile(rf"\\begin\{{{re.escape(env_name)}\}}")
    end_pat = re.compile(rf"\\end\{{{re.escape(env_name)}\}}")

    depth = 0
    out_lines: List[str] = []
    labels: List[str] = []
    i = start_line_idx

    while i < len(lines):
        raw = lines[i]
        line = strip_comments(raw)
        if begin_pat.search(line):
            depth += 1
        if depth > 0:
            out_lines.append(raw)
            labels.extend(_RE_LABEL.findall(line))
        if end_pat.search(line):
            depth -= 1
            if depth == 0:
                return out_lines, i, labels
        i += 1

    return out_lines, len(lines) - 1, labels


def _pick_primary_env_label(env_lines: List[str]) -> Optional[str]:
    """Prefer the label near the start of the environment (before nested envs)."""
    m0 = _RE_LABEL.search(strip_comments(env_lines[0]))
    if m0:
        return m0.group(1).strip()
    for raw in env_lines[1:]:
        line = strip_comments(raw).strip()
        if not line:
            continue
        if _RE_BEGIN.search(line):
            break
        m = _RE_LABEL.search(line)
        if m:
            return m.group(1).strip()
    return None


def _extract_labeled_equations_in_range(
    *,
    lines: List[str],
    start_idx: int,
    end_idx: int,
    file_path: str,
    paper_id: str,
    section_state: Dict[str, Any],
    aux_labels: Dict[str, AuxLabel],
    origin_source_tex: str,
    parent_block: Optional[Dict[str, Any]],
    parent_role: Optional[str],
) -> List[Dict[str, Any]]:
    blocks: List[Dict[str, Any]] = []
    i = start_idx
    while i <= end_idx and i < len(lines):
        line = strip_comments(lines[i])
        m = _RE_BEGIN.search(line)
        if not m:
            i += 1
            continue
        env = m.group(1)
        if env not in EQUATION_ENVS:
            i += 1
            continue

        env_lines, end_line_idx, labels = _extract_environment_block(lines, i, env)
        labels = [lab.strip() for lab in labels if lab.strip()]
        if labels:
            for lab in sorted(set(labels)):
                block = _make_block(
                    kind="equation",
                    env_name=env,
                    printed_name="Equation",
                    label=lab,
                    location_file=file_path,
                    start_line=i + 1,
                    end_line=end_line_idx + 1,
                    section_state=section_state,
                    latex_lines=env_lines,
                    aux_labels=aux_labels,
                    origin_source_tex=origin_source_tex,
                    parent=(
                        {
                            "block_id": parent_block["id"],
                            "role": parent_role,
                            "label": parent_block.get("label"),
                        }
                        if parent_block and parent_role
                        else None
                    ),
                )
                blocks.append(block)
        i = end_line_idx + 1
    return blocks


def collect_declared_labels(
    *,
    lines: List[str],
    theorem_envs: Dict[str, TheoremEnv],
) -> Dict[str, Dict[str, Any]]:
    """Collect all \\label{...} and best-effort classify by nearest environment."""
    declared: Dict[str, Dict[str, Any]] = {}
    env_stack: List[str] = []

    for idx, raw in enumerate(lines):
        line = strip_comments(raw)
        m_begin = _RE_BEGIN.search(line)
        if m_begin:
            env_stack.append(m_begin.group(1))

        is_section_line = bool(re.search(r"\\(sub)*section(\*?)\{", line))

        for lab in _RE_LABEL.findall(line):
            lab = lab.strip()
            if not lab:
                continue
            top = env_stack[-1] if env_stack else None
            if is_section_line:
                kind = "section"
            elif top in theorem_envs:
                kind = top
            elif top in EQUATION_ENVS:
                kind = "equation"
            elif top == "proof":
                kind = "proof"
            else:
                kind = "other"

            declared.setdefault(lab, {"label": lab, "kind": kind, "location": {"file": None, "line": idx + 1}})

        m_end = re.search(r"\\end\{([^}]+)\}", line)
        if m_end:
            end_env = m_end.group(1)
            for j in range(len(env_stack) - 1, -1, -1):
                if env_stack[j] == end_env:
                    del env_stack[j]
                    break

    return declared


def extract(
    *,
    root_tex: Path,
    out_json: Path,
    aux: Optional[Path],
) -> Dict[str, Any]:
    text = read_text(root_tex)
    preamble = find_preamble(text)
    theorem_envs = parse_newtheorem_commands(preamble)
    render = extract_render_context(preamble)

    paper_id = paper_id_from_root_tex(root_tex)
    aux_labels = parse_aux(aux)

    lines = text.splitlines()
    state = SectionState()

    blocks: List[Dict[str, Any]] = []
    by_label: Dict[str, str] = {}

    def register(block: Dict[str, Any]) -> None:
        blocks.append(block)
        if block.get("label"):
            by_label[block["label"]] = block["id"]

    i = 0
    while i < len(lines):
        raw = lines[i]
        line = strip_comments(raw)
        update_section_state(line, state)

        m = _RE_BEGIN.search(line)
        if not m:
            i += 1
            continue
        env = m.group(1)

        if env in theorem_envs:
            theorem_start_idx = i
            env_lines, end_line_idx, labels = _extract_environment_block(lines, i, env)
            label = _pick_primary_env_label(env_lines)
            if not label and labels:
                label = sorted(set(lab.strip() for lab in labels if lab.strip()))[0]
            if not label:
                label = _synth_label(env, paper_id, str(root_tex), i + 1)

            sec_snapshot = state.snapshot()
            thm = theorem_envs[env]
            theorem_block = _make_block(
                kind=env,
                env_name=env,
                printed_name=thm.printed_name,
                label=label,
                location_file=str(root_tex),
                start_line=i + 1,
                end_line=end_line_idx + 1,
                section_state=sec_snapshot,
                latex_lines=env_lines,
                aux_labels=aux_labels,
                origin_source_tex=str(root_tex),
            )

            proof_block: Optional[Dict[str, Any]] = None
            j = end_line_idx + 1
            while j < len(lines):
                nxt = strip_comments(lines[j]).strip()
                if not nxt or nxt.startswith("%"):
                    j += 1
                    continue
                if re.search(r"\\begin\{proof\}", nxt):
                    proof_lines, proof_end_idx, _ = _extract_environment_block(lines, j, "proof")
                    proof_label = _synth_label("proof", paper_id, str(root_tex), j + 1)
                    proof_block = _make_block(
                        kind="proof",
                        env_name="proof",
                        printed_name="Proof",
                        label=proof_label,
                        location_file=str(root_tex),
                        start_line=j + 1,
                        end_line=proof_end_idx + 1,
                        section_state=sec_snapshot,
                        latex_lines=proof_lines,
                        aux_labels=aux_labels,
                        origin_source_tex=str(root_tex),
                        parent={"block_id": theorem_block["id"], "role": "proof", "label": theorem_block.get("label")},
                    )
                    i = proof_end_idx
                break

            eq_blocks = _extract_labeled_equations_in_range(
                lines=lines,
                start_idx=theorem_start_idx,
                end_idx=end_line_idx,
                file_path=str(root_tex),
                paper_id=paper_id,
                section_state=sec_snapshot,
                aux_labels=aux_labels,
                origin_source_tex=str(root_tex),
                parent_block=theorem_block,
                parent_role="statement",
            )
            for b in eq_blocks:
                register(b)

            theorem_block.setdefault("parts", {})
            theorem_block["parts"]["equations"] = [b["id"] for b in eq_blocks]

            if proof_block:
                register(proof_block)
                proof_eq_blocks = _extract_labeled_equations_in_range(
                    lines=lines,
                    start_idx=proof_block["location"]["start_line"] - 1,
                    end_idx=proof_block["location"]["end_line"] - 1,
                    file_path=str(root_tex),
                    paper_id=paper_id,
                    section_state=sec_snapshot,
                    aux_labels=aux_labels,
                    origin_source_tex=str(root_tex),
                    parent_block=theorem_block,
                    parent_role="proof",
                )
                for b in proof_eq_blocks:
                    register(b)

                theorem_block["parts"]["proof"] = {"block_id": proof_block["id"]}
                theorem_block["parts"]["equations"] = [b["id"] for b in eq_blocks + proof_eq_blocks]

                deps = set(theorem_block["dependencies"]["labels"])
                deps.update(proof_block["dependencies"]["labels"])
                theorem_block["dependencies"]["labels"] = sorted(deps)

            register(theorem_block)
            i = end_line_idx + 1
            continue

        i += 1

    existing_equation_labels = {b.get("label") for b in blocks if b.get("kind") == "equation"}
    global_eq_blocks = _extract_labeled_equations_in_range(
        lines=lines,
        start_idx=0,
        end_idx=len(lines) - 1,
        file_path=str(root_tex),
        paper_id=paper_id,
        section_state=state.snapshot(),
        aux_labels=aux_labels,
        origin_source_tex=str(root_tex),
        parent_block=None,
        parent_role=None,
    )
    for b in global_eq_blocks:
        if b.get("label") in existing_equation_labels:
            continue
        register(b)

    data: Dict[str, Any] = {
        "schema_version": "paper-extract/v2",
        "paper_id": paper_id,
        "source": {
            "root_tex": str(root_tex),
            "inputs_resolved": False,
            "aux_file": str(aux) if aux else None,
        },
        "render": render,
        "theorem_envs": {k: th.__dict__ for k, th in theorem_envs.items()},
        "declared_labels": collect_declared_labels(lines=lines, theorem_envs=theorem_envs),
        "blocks": blocks,
        "index": {
            "by_label": by_label,
            "by_kind": _index_by_kind(blocks),
        },
    }

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    return data


def _index_by_kind(blocks: Iterable[Dict[str, Any]]) -> Dict[str, List[str]]:
    out: Dict[str, List[str]] = {}
    for b in blocks:
        out.setdefault(b["kind"], []).append(b["id"])
    return out

