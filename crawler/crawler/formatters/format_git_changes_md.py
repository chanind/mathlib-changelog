from crawler.parser.DiffParser import ItemChange, ParsedDiff


def get_change_prefix(change: ItemChange) -> str:
    if change.change_type == "mod":
        return r"\+/\-"
    if change.change_type == "del":
        return r"\-"
    return r"\+"


def format_git_changes_md(diffs: list[ParsedDiff]) -> str:
    outputs: list[str] = []
    for diff in diffs:
        diff_output = diff.file_change_str + "\n"
        item_changes = []
        for change in diff.changes:
            change_prefix = get_change_prefix(change)
            item_changes.append(
                f"- {change_prefix} *{change.item_type}* {change.full_name}"
            )
        diff_output += "\n".join(item_changes) + "\n"
        outputs.append(diff_output)
    return "\n".join(outputs)
