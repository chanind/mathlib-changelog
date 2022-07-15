from __future__ import annotations
from dataclasses import dataclass
import re
from typing import Literal, cast
import hashlib


ItemType = Literal["lemma", "theorem", "def"]
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


def parse_lean(contents: str) -> list[ParsedItem]:
    state = ParseState(blocks=[], items=[])
    lines = strip_lean_comments(contents).splitlines()
    for line in lines:
        parse_line(line, state)
    if len(state.blocks) > 0:
        raise Exception("Invalid parse state! open blocks remaining at end of parse")
    return state.items


OPTIONAL_DECORATOR_REGEX = r"(?:@\[[^\]]+\]\s?)"
ITEM_REGEX = rf"^\s*{OPTIONAL_DECORATOR_REGEX}*(def|lemma|theorem)\s+([^\s]+)"
START_BLOCK_REGEX = r"^\s*(section|namespace)\s+([^\s]+)"
END_BLOCK_REGEX = r"^\s*end\s+([^\s]+)"


def parse_line(line: str, state: ParseState) -> None:
    """
    Extract any items from the line, and track sections/namespaces.
    This will modify the state in-place.

    NOTE: this assumes there can only be a single def/theorem/lemma/section/namespace per line
    """
    item_match = re.search(ITEM_REGEX, line)
    start_block_match = re.search(START_BLOCK_REGEX, line)
    end_block_match = re.search(END_BLOCK_REGEX, line)

    if item_match:
        line_hash = hashlib.md5(line.encode()).hexdigest()
        [item_type, item_name] = item_match.groups()
        state.items.append(
            build_parsed_item(item_type, item_name, state.namespace, line_hash)
        )
    if start_block_match:
        [block_type, block_name] = start_block_match.groups()
        state.blocks.append((cast(BlockType, block_type), block_name))
    if end_block_match:
        [block_name] = end_block_match.groups()
        if block_name != state.blocks[-1][1]:
            raise Exception(f"Tried to pop unopened block {block_name}")
        state.blocks.pop()


def build_parsed_item(
    item_type: str,
    item_name: str,
    namespace: list[str],
    line_hash: str,
) -> ParsedItem:
    item_name_parts = item_name.split(".")

    if item_type not in ["lemma", "theorem", "def"]:
        raise Exception(f"Invalid item type found: {item_type}")
    safe_item_type = cast(ItemType, item_type)

    # starting with _root_ means we should throw out the namespace we're in
    if item_name_parts[0] == "_root_":
        return ParsedItem(
            type=safe_item_type,
            name=item_name_parts[-1],
            namespace=item_name_parts[1:-1],
            line_hash=line_hash,
        )
    return ParsedItem(
        type=safe_item_type,
        name=item_name_parts[-1],
        namespace=namespace + item_name_parts[0:-1],
        line_hash=line_hash,
    )


def strip_lean_comments(lean_contents: str) -> str:
    processed = re.sub(r"/-((?!-/)(.|\r|\n))*-/", "", lean_contents, re.MULTILINE)
    return re.sub(r"\-\-[^\n\r]*", "", processed, re.MULTILINE)
