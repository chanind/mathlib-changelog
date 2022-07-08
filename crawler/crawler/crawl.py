from collections import defaultdict
import re
from shutil import rmtree
from git import Repo
import pathlib

rmtree("mathlib", ignore_errors=True)
mathlib_repo = Repo.clone_from(
    "https://github.com/leanprover-community/mathlib.git", "mathlib"
)

def get_output_file(suffix: str):
    return pathlib.Path(__file__).parent.resolve() / f"../../CHANGELOG.{suffix}.md"

commits_info_full: list[str] = []
commits_info_by_year: dict[str, list[str]] = defaultdict(list)

def process_commit_msg(msg: str) -> str:
    processed_msg = msg.strip()
    processed_msg = re.sub(r'(#\d+)', r'[\1](https://github.com/leanprover-community/mathlib/pull/\1)', processed_msg)
    return processed_msg

for commit in mathlib_repo.iter_commits():
    commit_str = f"### [{commit.committed_datetime.isoformat()}](https://github.com/leanprover-community/mathlib/commit/{commit.hexsha})" + "\n"
    commit_str += process_commit_msg(commit.message)
    commits_info_full.append(commit_str)
    commits_info_by_year[commit.committed_datetime.year].append(commit_str)



with open(get_output_file('full'), "w") as f:
    f.write("\n\n".join(commits_info_full))

for year, commits_info in commits_info_by_year.items():
    with open(get_output_file(year), "w") as f:
        f.write("\n\n".join(commits_info))