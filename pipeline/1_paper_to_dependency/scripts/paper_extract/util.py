from __future__ import annotations

import hashlib
from pathlib import Path


def strip_comments(line: str) -> str:
    """Remove LaTeX comments from a line (best-effort).

    Treat an unescaped '%' as the start of a comment.
    """
    out: list[str] = []
    escaped = False
    for ch in line:
        if ch == "\\" and not escaped:
            escaped = True
            out.append(ch)
            continue
        if ch == "%" and not escaped:
            break
        escaped = False
        out.append(ch)
    return "".join(out)


def stable_id(*parts: str) -> str:
    h = hashlib.sha1()
    for p in parts:
        h.update(p.encode("utf-8"))
        h.update(b"\0")
    return "block:" + h.hexdigest()[:16]


def paper_id_from_root_tex(root_tex: Path) -> str:
    return root_tex.stem


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")

