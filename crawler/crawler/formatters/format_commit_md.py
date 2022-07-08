import re
from git import Commit

from .clean_commit_msg import clean_commit_msg
from .format_datetime import format_datetime

def process_commit_msg(msg: str) -> str:
    processed_msg = clean_commit_msg(msg)
    processed_msg = re.sub(r'#(\d+)', r'[#\1](https://github.com/leanprover-community/mathlib/pull/\1)', processed_msg)
    return processed_msg


def format_commit_md(commit: Commit) -> str:
    short_sha = commit.hexsha[0:7]
    commit_str = f"### [{format_datetime(commit.committed_datetime)}](https://github.com/leanprover-community/mathlib/commit/{short_sha})" + "\n"
    commit_str += process_commit_msg(commit.message)
    return commit_str

