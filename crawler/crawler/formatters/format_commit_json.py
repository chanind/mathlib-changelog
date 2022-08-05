from dataclasses import dataclass
import time
from typing import cast
from crawler.parser.DiffParser import ParsedDiff
from crawler.formatters.format_git_changes_json import DiffJson, format_git_changes_json
from git.objects import Commit
from .clean_commit_msg import clean_commit_msg


@dataclass
class CommitJson:
    timestamp: int
    sha: str
    message: str
    changes: list[DiffJson]


def format_commit_json(commit: Commit, diffs: list[ParsedDiff]) -> CommitJson:
    return CommitJson(
        timestamp=int(time.mktime(commit.committed_datetime.timetuple())),
        message=clean_commit_msg(cast(str, commit.message)),
        sha=commit.hexsha[0:8],
        changes=format_git_changes_json(diffs),
    )
