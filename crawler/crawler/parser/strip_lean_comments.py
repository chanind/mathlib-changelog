import re


def strip_lean_comments(lean_contents: str) -> str:
    processed = re.sub(r"/-((?!-/)(.|\r|\n))*-/", "", lean_contents, re.MULTILINE)
    return re.sub(r"\-\-[^\n\r]*", "", processed, re.MULTILINE)
