from dataclasses import dataclass
import time
from typing import cast
from crawler.formatters.format_git_changes_json import DiffJson, format_git_changes_json
from git import Diff
from git.objects import Commit
from .clean_commit_msg import clean_commit_msg


@dataclass
class CommitJson:
    timestamp: int
    sha: str
    message: str
    changes: list[DiffJson]


def format_commit_json(commit: Commit, diffs: list[Diff]) -> CommitJson:
    return CommitJson(
        timestamp=int(time.mktime(commit.committed_datetime.timetuple())),
        message=clean_commit_msg(cast(str, commit.message)),
        sha=commit.hexsha[0:7],
        changes=format_git_changes_json(diffs),
    )
