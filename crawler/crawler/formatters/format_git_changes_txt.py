from typing import cast
from crawler.extract_diff_info import extract_diff_changes, extract_diff_file_info
from crawler.stable_dedupe import stable_dedupe
from git import Diff


def get_change_prefix(
    changed_item: str, added_items: list[str], deleted_items: list[str]
) -> str:
    prefixes = []
    if changed_item in added_items:
        prefixes.append("+")
    if changed_item in deleted_items:
        prefixes.append("-")
    return "/".join(prefixes)


def format_git_changes_txt(diffs: list[Diff]) -> str:
    outputs: list[str] = []
    for diff in diffs:
        diff_output = extract_diff_file_info(diff) + "\n"
        changes = extract_diff_changes(cast(bytes, diff.diff).decode("utf-8"))
        lemmas = changes.added_lemmas + changes.deleted_lemmas
        theorems = changes.added_theorems + changes.deleted_theorems
        defs = changes.added_defs + changes.deleted_defs
        item_changes = []
        for lemma in lemmas:
            change_prefix = get_change_prefix(
                lemma, changes.added_lemmas, changes.deleted_lemmas
            )
            item_changes.append(f"{change_prefix} lemma {lemma}")
        for theorem in theorems:
            change_prefix = get_change_prefix(
                theorem, changes.added_theorems, changes.deleted_theorems
            )
            item_changes.append(f"{change_prefix} theorem {theorem}")
        for def_str in defs:
            change_prefix = get_change_prefix(
                def_str, changes.added_defs, changes.deleted_defs
            )
            item_changes.append(f"{change_prefix} def {def_str}")
        diff_output += "\n".join(stable_dedupe(item_changes)) + "\n"
        outputs.append(diff_output)
    return "".join(outputs)
