from dataclasses import dataclass
from typing import cast
from crawler.extract_diff_info import extract_diff_changes, extract_diff_file_info
from crawler.stable_dedupe import stable_dedupe
from git import Diff


@dataclass
class DiffJson:
    pathChange: str
    path: str
    changes: list[tuple[str, str, str]]


def get_change_type(
    changed_item: str, added_items: list[str], deleted_items: list[str]
) -> str:
    if changed_item in added_items and changed_item in deleted_items:
        return "mod"
    if changed_item in deleted_items:
        return "del"
    return "add"


def format_git_changes_json(diffs: list[Diff]) -> list[DiffJson]:
    changes: list[DiffJson] = []
    for diff in diffs:
        path_change = extract_diff_file_info(diff)
        diff_changes = extract_diff_changes(cast(bytes, diff.diff).decode("utf-8"))
        json_changes: list[tuple[str, str, str]] = []
        lemmas = diff_changes.added_lemmas + diff_changes.deleted_lemmas
        theorems = diff_changes.added_theorems + diff_changes.deleted_theorems
        defs = diff_changes.added_defs + diff_changes.deleted_defs
        for lemma in lemmas:
            change_type = get_change_type(
                lemma, diff_changes.added_lemmas, diff_changes.deleted_lemmas
            )
            json_changes.append((change_type, "lemma", lemma))
        for theorem in theorems:
            change_type = get_change_type(
                theorem, diff_changes.added_theorems, diff_changes.deleted_theorems
            )
            json_changes.append((change_type, "theorem", theorem))
        for def_str in defs:
            change_type = get_change_type(
                def_str, diff_changes.added_defs, diff_changes.deleted_defs
            )
            json_changes.append((change_type, "def", def_str))
        changes.append(
            DiffJson(
                pathChange=path_change,
                path=cast(str, diff.a_path or diff.b_path),
                changes=stable_dedupe(json_changes),
            )
        )
    return changes
