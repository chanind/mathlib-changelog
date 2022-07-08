from git import Commit
from .clean_commit_msg import clean_commit_msg
from .format_datetime import format_datetime


def format_commit_txt(commit: Commit) -> str:
    commit_str = format_datetime(commit.committed_datetime) + " " + commit.hexsha[0:7] + "\n"
    commit_str += clean_commit_msg(commit.message)
    return commit_str

