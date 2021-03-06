from typing import cast
from crawler.parser.DiffParser import ParsedDiff
from crawler.formatters.format_git_changes_txt import format_git_changes_txt
from git.objects import Commit
from .clean_commit_msg import clean_commit_msg
from .format_datetime import format_datetime


def format_commit_txt(commit: Commit, diffs: list[ParsedDiff]) -> str:
    commit_str = (
        format_datetime(commit.committed_datetime) + " " + commit.hexsha[0:7] + "\n\n"
    )
    commit_str += clean_commit_msg(cast(str, commit.message)) + "\n\n"
    commit_str += "ESTIMATED CHANGES\n" + format_git_changes_txt(diffs)
    return commit_str
