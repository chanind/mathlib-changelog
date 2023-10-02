from pathlib import Path
from crawler.parser.parse_lean_v3 import parse_lean_v3
from syrupy.assertion import SnapshotAssertion


FIXTURES_DIR = Path(__file__).resolve().parent / "../fixtures_v3"


def read_fixture(filename: str) -> str:
    with open(FIXTURES_DIR / filename, "r") as file:
        return file.read()


def test_parse_lean_ess_sup_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("ess_sup.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot


def test_parse_lean_filtered_colimits_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("filtered_colimits.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot


def test_parse_lean_algebra_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("algebra.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot


def test_parse_lean_cont_mdiff_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("cont_mdiff.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot


def test_parse_lean_to_additive_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("to_additive.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot


def test_parse_lean_fermat4_fixture(snapshot: SnapshotAssertion) -> None:
    contents = read_fixture("fermat4.lean")
    parsed_items = parse_lean_v3(contents)
    assert [item.full_name for item in parsed_items] == snapshot
