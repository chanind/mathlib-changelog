from __future__ import annotations
from dataclasses import dataclass
from typing import Literal


ItemType = Literal["theorem", "def", "inductive", "structure"]
BlockType = Literal["section", "namespace"]


@dataclass
class ParsedItem:
    type: ItemType
    name: str
    namespace: list[str]
    line_hash: str

    @property
    def full_name(self) -> str:
        return self.type + ":" + ".".join([*self.namespace, self.name])


@dataclass
class LeanParseResult:
    items: list[ParsedItem]

    def get_item(self, full_name: str) -> ParsedItem | None:
        for item in self.items:
            if item.full_name == full_name:
                return item
        return None


@dataclass
class ParseState:
    blocks: list[tuple[BlockType, str]]
    items: list[ParsedItem]

    @property
    def namespace(self) -> list[str]:
        namespace = []
        for block in self.blocks:
            if block[0] == "namespace":
                # handle cases like "namespace Thing1.thing2"
                namespace += block[1].split(".")
        return namespace
