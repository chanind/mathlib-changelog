from dataclasses import asdict
from genericpath import exists
import json
import logging
import pickle
from tqdm import tqdm
from shutil import rmtree
from typing import Any
from crawler.parser.DiffParser import DiffParser, ParseCache
from crawler.formatters.format_commit_json import format_commit_json
from git import Repo
from pathlib import Path

from crawler.formatters.format_commit_txt import format_commit_txt

logging.basicConfig(level=logging.INFO)

CUR_DIR = Path(__file__).parent.resolve()

logging.info("Cloning mathlib repo")

rmtree("mathlib", ignore_errors=True)
mathlib_repo = Repo.clone_from(
    "https://github.com/leanprover-community/mathlib.git", "mathlib"
)

FULL_TXT_OUTPUT_FILE = CUR_DIR / "../../CHANGELOG.full.txt"
FULL_JSON_OUTPUT_FILE = CUR_DIR / "../../CHANGELOG.full.json"
PARSE_CACHE_FILE = CUR_DIR / "../parse_cache.pkl"


commits_info_txt_full: list[str] = []
commits_info_json_full: list[dict[Any, Any]] = []

parse_cache: ParseCache = {}
if exists(PARSE_CACHE_FILE):
    logging.info("Parser cache found")
    with open(PARSE_CACHE_FILE, "rb") as f:
        parse_cache = pickle.load(f)

diff_parser = DiffParser(mathlib_repo, parse_cache)

logging.info("Parsing commits")

commits = list(mathlib_repo.iter_commits())
for index, commit in enumerate(tqdm(commits)):
    diffs = []
    if index + 1 < len(commits):
        older_commit = commits[index + 1]
        diffs = diff_parser.diff_commits(older_commit, commit)
    commit_txt = format_commit_txt(commit, diffs)
    commit_json = format_commit_json(commit, diffs)
    commits_info_txt_full.append(commit_txt)
    commits_info_json_full.append(asdict(commit_json))

logging.info("writing outputs")

with open(PARSE_CACHE_FILE, "wb") as f:
    pickle.dump(diff_parser.parse_cache, f, pickle.HIGHEST_PROTOCOL)

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
