import re

def clean_commit_msg(msg: str) -> str:
    cleaned_msg = re.sub(r'Co-authored-by:.*', '', msg)
    cleaned_msg = re.sub(r'\r+', '\n', cleaned_msg)
    cleaned_msg = re.sub(r'\n+', '\n', cleaned_msg)
    return cleaned_msg.strip()