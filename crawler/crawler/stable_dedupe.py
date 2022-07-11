from typing import TypeVar


T = TypeVar("T")


def stable_dedupe(items: list[T]) -> list[T]:
    "Dedupe while keeping the same order"
    seen_items = set()
    deduped_items = []
    for item in items:
        if item not in seen_items:
            deduped_items.append(item)
            seen_items.add(item)
    return deduped_items
