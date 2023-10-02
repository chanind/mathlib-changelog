from __future__ import annotations
import logging
import re
from typing import cast
import hashlib

from crawler.parser.types import BlockType, ItemType, ParseState, ParsedItem

from .strip_lean_comments import strip_lean_comments


def parse_lean_v3(contents: str) -> list[ParsedItem]:
    state = ParseState(blocks=[], items=[])

    lines = strip_lean_comments(contents).splitlines()
    for line in lines:
        parse_line(line, state)
    if len(state.namespace) > 0:
        logging.warning(
            f"Invalid parse state! open namespace remaining at end of parse: {state.namespace}"
        )
    return state.items


OPTIONAL_DECORATOR_REGEX = r"(?:@\[[^\]]+\]\s?)"
ITEM_REGEX = rf"^\s*{OPTIONAL_DECORATOR_REGEX}*(def|lemma|theorem|abbreviation|inductive|structure)\s+([^\s]+)"
START_BLOCK_REGEX = r"^\s*(section|namespace)\s+([^\s]+)"
END_BLOCK_REGEX = r"^\s*end\s+([^\s]+)"


def remap_item_type(item_type: str) -> ItemType:
    """
    map lemma -> theorem, and abbreviation -> def
    """
    if item_type == "lemma":
        return "theorem"
    if item_type == "abbreviation":
        return "def"
    return cast(ItemType, item_type)


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
            build_parsed_item(
                remap_item_type(item_type), item_name, state.namespace, line_hash
            )
        )
    if start_block_match:
        [block_type, block_name] = start_block_match.groups()
        # weird keyword `section end` in https://github.com/leanprover-community/mathlib/blob/master/src/algebraic_geometry/pullbacks.lean#L113
        # not sure what this means, so just skip it
        if block_type == "section" and block_name == "end":
            return
        state.blocks.append((cast(BlockType, block_type), block_name))
    if end_block_match:
        [block_name] = end_block_match.groups()
        if len(state.blocks) > 0 and block_name == state.blocks[-1][1]:
            state.blocks.pop()


def build_parsed_item(
    item_type: str,
    item_name: str,
    namespace: list[str],
    line_hash: str,
) -> ParsedItem:
    item_name_parts = item_name.split(".")
    if item_type not in [
        "theorem",
        "def",
        "inductive",
        "structure",
    ]:
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
