from __future__ import annotations
from dataclasses import dataclass


@dataclass
class ParsedItem:
    type: str
    name: str
    namespace: list[str]
    line_hash: str

    @property
    def full_name(self) -> str:
        return self.type + ":" + ".".join(self.namespace) + "." + self.name


@dataclass
class LeanParseResult:
    items: list[ParsedItem]

    def get_item(self, full_name: str) -> ParsedItem | None:
        for item in self.items:
            if item.full_name == full_name:
                return item
        return None


def parse_lean(contents: str) -> list[ParsedItem]:
    pass
