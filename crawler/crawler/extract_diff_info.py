import re
from dataclasses import dataclass
from git import Diff


@dataclass
class Changes:
    added_lemmas: list[str]
    deleted_lemmas: list[str]
    added_theorems: list[str]
    deleted_theorems: list[str]
    added_defs: list[str]
    deleted_defs: list[str]


def named_keyword_extractor_regex(keyword: str, prefix: str) -> str:
    optional_decorator_prefix = r"(?:@\[[^\]]+\]\s?)"
    return rf"\{prefix}{optional_decorator_prefix}*{keyword}\s([^\s]+)"


def extract_diff_changes(diff_str: str) -> Changes:
    added_lemmas = re.findall(
        named_keyword_extractor_regex("lemma", "+"), diff_str, re.MULTILINE
    )
    added_theorems = re.findall(
        named_keyword_extractor_regex("theorem", "+"), diff_str, re.MULTILINE
    )
    added_defs = re.findall(
        named_keyword_extractor_regex("def", "+"), diff_str, re.MULTILINE
    )
    deleted_lemmas = re.findall(
        named_keyword_extractor_regex("lemma", "-"), diff_str, re.MULTILINE
    )
    deleted_theorems = re.findall(
        named_keyword_extractor_regex("theorem", "-"), diff_str, re.MULTILINE
    )
    deleted_defs = re.findall(
        named_keyword_extractor_regex("def", "-"), diff_str, re.MULTILINE
    )

    return Changes(
        added_lemmas=added_lemmas,
        deleted_lemmas=deleted_lemmas,
        added_theorems=added_theorems,
        deleted_theorems=deleted_theorems,
        added_defs=added_defs,
        deleted_defs=deleted_defs,
    )


def extract_diff_file_info(diff: Diff) -> str:
    path = diff.a_path or diff.b_path
    if diff.renamed:
        return f"renamed {diff.rename_from} to {diff.rename_to}"
    elif diff.new_file:
        return f"created {path}"
    elif diff.deleted_file:
        return f"deleted {path}"
    return f"modified {path}"
