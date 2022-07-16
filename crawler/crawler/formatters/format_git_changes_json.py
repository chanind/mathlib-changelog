from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from typing import Literal, cast
from crawler.parser.DiffParser import ParsedDiff


ChangeType = Literal["add", "del", "mod"]
ItemType = Literal["lemma", "theorem", "def", "abbreviation", "inductive", "structure"]


@dataclass
class DiffJson:
    oldPath: str | None
    newPath: str | None
    pathSha: str  # used by Github to link to files in diffs
    changes: list[tuple[ChangeType, ItemType, str, list[str]]]


def format_git_changes_json(diffs: list[ParsedDiff]) -> list[DiffJson]:
    changes: list[DiffJson] = []
    for diff in diffs:
        json_changes: list[tuple[ChangeType, ItemType, str, list[str]]] = []
        for change in diff.changes:
            json_changes.append(
                (change.change_type, change.item_type, change.name, change.namespace)
            )
        changes.append(
            DiffJson(
                oldPath=diff.old_path,
                newPath=diff.new_path,
                changes=json_changes,
                pathSha=sha256(
                    cast(str, diff.new_path or diff.old_path).encode()
                ).hexdigest(),
            )
        )
    return changes
