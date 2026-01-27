from __future__ import annotations

import re
from typing import Any, Dict, Optional, Tuple

from .types import TheoremEnv
from .util import strip_comments


_RE_DOCUMENTCLASS = re.compile(r"\\documentclass(?:\[[^\]]*\])?\{([^}]+)\}")
_RE_USEPACKAGE = re.compile(r"\\usepackage(?:\[([^\]]*)\])?\{([^}]+)\}")
_RE_NUMBERWITHIN = re.compile(r"\\numberwithin\{([^}]+)\}\{([^}]+)\}")


def find_preamble(text: str) -> str:
    """Return preamble text (up to \\begin{document})."""
    m = re.search(r"\\begin\{document\}", text)
    return text if not m else text[: m.start()]


def _parse_braced(text: str, start: int, open_ch: str, close_ch: str) -> Tuple[Optional[str], int]:
    """Parse {...} or [...] starting at start, return (content, next_index)."""
    if start >= len(text) or text[start] != open_ch:
        return None, start
    depth = 0
    i = start
    buf: list[str] = []
    while i < len(text):
        ch = text[i]
        if ch == open_ch:
            depth += 1
            if depth > 1:
                buf.append(ch)
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return "".join(buf), i + 1
            buf.append(ch)
        else:
            buf.append(ch)
        i += 1
    return None, start


def parse_newtheorem_commands(preamble: str) -> Dict[str, TheoremEnv]:
    """Discover theorem-like environments by scanning \\newtheorem statements (best-effort)."""
    theorem_envs: Dict[str, TheoremEnv] = {}

    preamble_no_comments = "\n".join(strip_comments(ln) for ln in preamble.splitlines())

    current_style: Optional[str] = None
    for line in preamble_no_comments.splitlines():
        line = line.strip()
        if not line:
            continue
        m_style = re.search(r"\\theoremstyle\{([^}]+)\}", line)
        if m_style:
            current_style = m_style.group(1).strip()

    i = 0
    while True:
        j = preamble_no_comments.find(r"\newtheorem", i)
        if j < 0:
            break
        k = j + len(r"\newtheorem")
        while k < len(preamble_no_comments) and preamble_no_comments[k].isspace():
            k += 1

        env, k2 = _parse_braced(preamble_no_comments, k, "{", "}")
        if env is None:
            i = j + 1
            continue
        k = k2

        shared_counter, k2 = _parse_braced(preamble_no_comments, k, "[", "]")
        k = k2

        while k < len(preamble_no_comments) and preamble_no_comments[k].isspace():
            k += 1
        printed, k2 = _parse_braced(preamble_no_comments, k, "{", "}")
        if printed is None:
            i = j + 1
            continue
        k = k2

        within, k2 = _parse_braced(preamble_no_comments, k, "[", "]")

        theorem_envs[env.strip()] = TheoremEnv(
            env=env.strip(),
            printed_name=printed.strip(),
            shared_counter=(shared_counter.strip() if shared_counter else None),
            within=(within.strip() if within else None),
            style=current_style,
        )
        i = k2

    return theorem_envs


def extract_render_context(preamble: str) -> Dict[str, Any]:
    """Extract a UI-friendly render context from the preamble (best-effort)."""
    preamble_lines = preamble.splitlines()
    packages: list[dict[str, Any]] = []
    macros: list[dict[str, Any]] = []
    theorem_defs: list[str] = []
    numberwithin: list[dict[str, str]] = []

    for raw in preamble_lines:
        line = strip_comments(raw).strip()
        if not line:
            continue

        if _RE_DOCUMENTCLASS.search(line):
            macros.append({"kind": "documentclass", "raw": raw})

        m_pkg = _RE_USEPACKAGE.search(line)
        if m_pkg:
            options = m_pkg.group(1)
            names = [p.strip() for p in m_pkg.group(2).split(",") if p.strip()]
            for name in names:
                packages.append({"name": name, "options": options, "raw": raw})

        if r"\newtheorem" in line:
            theorem_defs.append(raw)

        m_nw = _RE_NUMBERWITHIN.search(line)
        if m_nw:
            numberwithin.append({"counter": m_nw.group(1).strip(), "within": m_nw.group(2).strip(), "raw": raw})

        if line.startswith((r"\newcommand", r"\renewcommand", r"\DeclareMathOperator", r"\def")):
            macros.append({"kind": "macro", "raw": raw})

    return {
        "preamble_lines": preamble_lines,
        "packages": packages,
        "macros": macros,
        "newtheorem_lines": theorem_defs,
        "numberwithin": numberwithin,
    }

