from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Dict, Optional


@dataclass
class SectionState:
    section_no: int = 0
    subsection_no: int = 0
    subsubsection_no: int = 0
    section_title: Optional[str] = None
    subsection_title: Optional[str] = None
    subsubsection_title: Optional[str] = None

    def snapshot(self) -> Dict[str, Any]:
        def _mk(title: Optional[str], number: Optional[str]) -> Dict[str, Any]:
            return {"title": title, "number": number}

        section_number = str(self.section_no) if self.section_no else None
        subsection_number = (
            f"{self.section_no}.{self.subsection_no}" if self.section_no and self.subsection_no else None
        )
        subsubsection_number = (
            f"{self.section_no}.{self.subsection_no}.{self.subsubsection_no}"
            if self.section_no and self.subsection_no and self.subsubsection_no
            else None
        )
        return {
            "section": _mk(self.section_title, section_number),
            "subsection": _mk(self.subsection_title, subsection_number),
            "subsubsection": _mk(self.subsubsection_title, subsubsection_number),
            "breadcrumbs": [t for t in [self.section_title, self.subsection_title, self.subsubsection_title] if t],
        }


def update_section_state(line: str, state: SectionState) -> None:
    """Update section counters based on a line (best-effort)."""
    for cmd, level in (("section", "section"), ("subsection", "subsection"), ("subsubsection", "subsubsection")):
        m = re.search(rf"\\{cmd}(\*?)\{{([^}}]+)\}}", line)
        if not m:
            continue
        starred = bool(m.group(1))
        title = m.group(2).strip()

        if level == "section":
            state.section_title = title
            state.subsection_title = None
            state.subsubsection_title = None
            state.subsection_no = 0
            state.subsubsection_no = 0
            if not starred:
                state.section_no += 1
        elif level == "subsection":
            state.subsection_title = title
            state.subsubsection_title = None
            state.subsubsection_no = 0
            if not starred:
                state.subsection_no += 1
        else:
            state.subsubsection_title = title
            if not starred:
                state.subsubsection_no += 1
        return

