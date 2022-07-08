# mathlib-changelog

This Repo maintains an auto-updating list of the commits to [mathlib](https://github.com/leanprover-community/mathlib) for [Lean](https://leanprover.github.io/) to have these in a searchable, indexable location.

Currently this pulls in git commit messages, and runs a regex against the diff contents to guess at the changed lemmas/defs/theorems in the commit. This is just a heuristic though, and not guaranteed to catch all changes that occurred in the commit.

The full changelog in the following formats:

- plaintext is available in [CHANGELOG.full.txt](https://raw.githubusercontent.com/chanind/mathlib-changelog/main/CHANGELOG.full.txt)
- markdown changelogs per month are available in [/markdown](https://github.com/chanind/mathlib-changelog/tree/main/markdown).
