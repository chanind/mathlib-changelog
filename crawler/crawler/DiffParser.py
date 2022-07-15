from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from hashlib import md5
from typing import Literal
from git import Repo
from git.objects import Commit

from crawler.parse_lean import ParsedItem, parse_lean


ChangeType = Literal["add", "del", "mod"]
ItemType = Literal["lemma", "theorem", "def"]


@dataclass
class ItemChange:
    change_type: ChangeType
    item_type: ItemType
    name: str
    namespace: list[str]

    @property
    def full_name(self) -> str:
        return ".".join([*self.namespace, self.name])

    @property
    def sort_key(self) -> str:
        return f"{self.full_name}:{self.change_type}:{self.change_type}"


@dataclass
class ParsedDiff:
    old_path: str | None
    new_path: str | None
    changes: list[ItemChange]


class DiffParser:
    parse_cache: dict[str, list[ParsedItem]]
    repo: Repo

    def __init__(self, repo: Repo):
        self.repo = repo
        self.parse_cache = {}

    def parse_items(self, commit_sha: str, path: str) -> list[ParsedItem]:
        git_lookup_key = f"{commit_sha}:{path}"
        if git_lookup_key in self.parse_cache:
            return self.parse_cache[git_lookup_key]
        contents = self.repo.git.show(git_lookup_key)
        contents_hash = md5(contents.encode()).hexdigest()
        if contents_hash in self.parse_cache:
            return self.parse_cache[contents_hash]
        parse_result = parse_lean(contents)
        self.parse_cache[git_lookup_key] = parse_result
        self.parse_cache[contents_hash] = parse_result
        return parse_result

    def diff_commits(self, old_commit: Commit, new_commit: Commit) -> list[ParsedDiff]:
        parsed_diffs = []
        for diff in old_commit.diff(new_commit):
            old_path = None if diff.new_file else diff.a_path
            new_path = None if diff.deleted_file else diff.b_path
            old_items = (
                self.parse_items(old_commit.hexsha, old_path) if old_path else []
            )
            new_items = (
                self.parse_items(new_commit.hexsha, new_path) if old_path else []
            )
            old_items_index = index_parsed_items(old_items)
            new_items_index = index_parsed_items(new_items)
            changes: list[ItemChange] = []
            for old_name, old_items in old_items_index.items():
                if old_name not in new_items_index:
                    changes.append(
                        ItemChange(
                            "del",
                            old_items[0].type,
                            old_items[0].name,
                            old_items[0].namespace,
                        )
                    )
                else:
                    new_items = new_items_index[old_name]
                    old_hashes = {item.line_hash for item in old_items}
                    new_hashes = {item.line_hash for item in new_items}
                    if old_hashes != new_hashes:
                        changes.append(
                            ItemChange(
                                "mod",
                                old_items[0].type,
                                old_items[0].name,
                                old_items[0].namespace,
                            )
                        )
            for new_name, new_items in new_items_index.items():
                if new_name not in old_items_index:
                    changes.append(
                        ItemChange(
                            "add",
                            new_items[0].type,
                            new_items[0].name,
                            new_items[0].namespace,
                        )
                    )
            sorted_changes = sorted(changes, key=lambda change: change.sort_key)
            parsed_diffs.append(
                ParsedDiff(old_path=old_path, new_path=new_path, changes=sorted_changes)
            )
        return parsed_diffs


def index_parsed_items(parsed_items: list[ParsedItem]) -> dict[str, list[ParsedItem]]:
    index = defaultdict(list)
    for item in parsed_items:
        index[item.full_name].append(item)
    return index
