from collections import defaultdict
from dataclasses import asdict
import json
from os import mkdir
from shutil import rmtree
from typing import Any
from crawler.formatters.format_commit_json import format_commit_json
from git import Diff, Repo
from git.objects import Commit  # keep mypy happy...
from pathlib import Path

from crawler.formatters.format_commit_md import format_commit_md
from crawler.formatters.format_commit_txt import format_commit_txt

CUR_DIR = Path(__file__).parent.resolve()
MARKDOWN_DIR = CUR_DIR / "../../markdown"

rmtree("mathlib", ignore_errors=True)
mathlib_repo = Repo.clone_from(
    "https://github.com/leanprover-community/mathlib.git", "mathlib"
)

FULL_TXT_OUTPUT_FILE = CUR_DIR / "../../CHANGELOG.full.txt"
FULL_JSON_OUTPUT_FILE = CUR_DIR / "../../CHANGELOG.full.json"


def get_md_output_file(suffix: str) -> Path:
    return MARKDOWN_DIR / f"CHANGELOG.{suffix}.md"


commits_info_md_by_month: dict[str, list[str]] = defaultdict(list)
commits_info_txt_full: list[str] = []
commits_info_json_full: list[dict[Any, Any]] = []


def get_diffs(commit1: Commit, commit2: Commit) -> list[Diff]:
    return commit2.diff(commit1, create_patch=True)


commits = list(mathlib_repo.iter_commits())
for index, commit in enumerate(commits):
    diffs = []
    if index + 1 < len(commits):
        next_commit = commits[index + 1]
        diffs = get_diffs(commit, next_commit)
    commit_md = format_commit_md(commit, diffs)
    commit_txt = format_commit_txt(commit, diffs)
    commit_json = format_commit_json(commit, diffs)

    month_str = f"{commit.committed_datetime.year}.{commit.committed_datetime.month:02}"
    commits_info_md_by_month[month_str].append(commit_md)
    commits_info_txt_full.append(commit_txt)
    commits_info_json_full.append(asdict(commit_json))

rmtree(MARKDOWN_DIR, ignore_errors=True)
mkdir(MARKDOWN_DIR)

for year, commits_info in commits_info_md_by_month.items():
    with open(get_md_output_file(year), "w") as f:
        f.write("\n\n".join(commits_info))

with open(FULL_TXT_OUTPUT_FILE, "w") as f:
    f.write("\n\n\n".join(commits_info_txt_full))

with open(FULL_JSON_OUTPUT_FILE, "w") as f:
    f.write(
        json.dumps(
            {"commits": commits_info_json_full},
            indent=2,
            ensure_ascii=False,
        )
    )
