import argparse
from dataclasses import asdict
from genericpath import exists
import json
import logging
import pickle
from tqdm import tqdm
from shutil import rmtree
from typing import Any, Literal
from crawler.parser.DiffParser import DiffParser, ParseCache
from crawler.formatters.format_commit_json import format_commit_json
from git import Repo
from pathlib import Path

from crawler.formatters.format_commit_txt import format_commit_txt

logging.basicConfig(level=logging.INFO)

CUR_DIR = Path(__file__).parent.resolve()

FULL_TXT_OUTPUT_FILE_V3 = CUR_DIR / "../../CHANGELOG.v3.full.txt"
FULL_JSON_OUTPUT_FILE_V3 = CUR_DIR / "../../CHANGELOG.v3.full.json"
PARSE_CACHE_FILE_V3 = CUR_DIR / "../parse_cache.v3.pkl"

FULL_TXT_OUTPUT_FILE_V4 = CUR_DIR / "../../CHANGELOG.v4.full.txt"
FULL_JSON_OUTPUT_FILE_V4 = CUR_DIR / "../../CHANGELOG.v4.full.json"
PARSE_CACHE_FILE_V4 = CUR_DIR / "../parse_cache.v4.pkl"


def crawl(
    mathlib_repo: Repo,
    full_txt_output_file: Path,
    full_json_output_file: Path,
    parse_cache_file: Path,
    lean_version: Literal["v3", "v4"],
) -> None:
    logging.info(f"Starting crawl for {lean_version}")
    commits_info_txt_full: list[str] = []
    commits_info_json_full: list[dict[Any, Any]] = []

    parse_cache: ParseCache = {}
    if exists(parse_cache_file):
        logging.info("Parser cache found")
        with open(parse_cache_file, "rb") as f:
            parse_cache = pickle.load(f)

    diff_parser = DiffParser(
        mathlib_repo, lean_version=lean_version, parse_cache=parse_cache
    )

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

    with open(parse_cache_file, "wb") as f:
        pickle.dump(diff_parser.parse_cache, f, pickle.HIGHEST_PROTOCOL)

    with open(full_txt_output_file, "w") as f:
        f.write("\n\n\n".join(commits_info_txt_full))

    with open(full_json_output_file, "w") as f:
        f.write(
            json.dumps(
                {"commits": commits_info_json_full},
                ensure_ascii=False,
            )
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Crawl mathlib git repos to update changelog"
    )
    parser.add_argument("--skip-v3", action="store_true")
    parser.add_argument("--skip-v4", action="store_true")
    args = parser.parse_args()

    if not args.skip_v3:
        logging.info("Cloning mathlib v3 repo")
        rmtree("mathlib", ignore_errors=True)
        mathlib_repo_v3 = Repo.clone_from(
            "https://github.com/leanprover-community/mathlib.git", "mathlib"
        )
        crawl(
            mathlib_repo_v3,
            FULL_TXT_OUTPUT_FILE_V3,
            FULL_JSON_OUTPUT_FILE_V3,
            PARSE_CACHE_FILE_V3,
            "v3",
        )

    if not args.skip_v4:
        logging.info("Cloning mathlib v4 repo")
        rmtree("mathlib4", ignore_errors=True)
        mathlib_repo_v4 = Repo.clone_from(
            "https://github.com/leanprover-community/mathlib4.git", "mathlib4"
        )
        crawl(
            mathlib_repo_v4,
            FULL_TXT_OUTPUT_FILE_V4,
            FULL_JSON_OUTPUT_FILE_V4,
            PARSE_CACHE_FILE_V4,
            "v4",
        )
