from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class TheoremEnv:
    env: str
    printed_name: str
    shared_counter: Optional[str] = None
    within: Optional[str] = None
    style: Optional[str] = None


@dataclass(frozen=True)
class AuxLabel:
    number: str
    page: Optional[str] = None

