from pathlib import Path
from crawler.parse_lean import strip_lean_comments, parse_lean


FIXTURES_DIR = Path(__file__).resolve().parent / "fixtures"


def read_fixture(filename: str) -> str:
    with open(FIXTURES_DIR / filename, "r") as file:
        return file.read()


def test_strip_lean_comments_removes_single_line_comments() -> None:
    input = """
hi
ok -- this is a comment
just some more code
-- I don't know what I'm doing
more stuff
    """.strip()
    expected = """
hi
ok 
just some more code

more stuff
    """.strip()
    assert strip_lean_comments(input) == expected


def test_strip_lean_comments_removes_multi_line_comments() -> None:
    input = """
/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.single_obj
import category_theory.limits.shapes.products
import category_theory.pi.basic
import category_theory.limits.is_limit

/-!
# Category of groupoids
This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.
We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.
## Implementation notes
Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/

universes v u

namespace category_theory

/-- Category of groupoids -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def Groupoid := bundled groupoid.{v u}
    """.strip()
    expected = """
import category_theory.single_obj
import category_theory.limits.shapes.products
import category_theory.pi.basic
import category_theory.limits.is_limit



universes v u

namespace category_theory


@[nolint check_univs] 
def Groupoid := bundled groupoid.{v u}
    """.strip()
    assert strip_lean_comments(input).strip() == expected


def test_parse_lean_ess_sup_fixture() -> None:
    contents = read_fixture("ess_sup.lean")
    parsed_items = parse_lean(contents)
    assert [item.full_name for item in parsed_items] == [
        "def:ess_sup",
        "def:ess_inf",
        "lemma:ess_sup_congr_ae",
        "lemma:ess_inf_congr_ae",
        "lemma:ess_sup_eq_Inf",
        "lemma:ess_sup_measure_zero",
        "lemma:ess_inf_measure_zero",
        "lemma:ess_sup_mono_ae",
        "lemma:ess_inf_mono_ae",
        "lemma:ess_sup_const",
        "lemma:ess_sup_le_of_ae_le",
        "lemma:ess_inf_const",
        "lemma:le_ess_inf_of_ae_le",
        "lemma:ess_sup_const_bot",
        "lemma:ess_inf_const_top",
        "lemma:order_iso.ess_sup_apply",
        "lemma:order_iso.ess_inf_apply",
        "lemma:ess_sup_mono_measure",
        "lemma:ess_sup_mono_measure'",
        "lemma:ess_inf_antitone_measure",
        "lemma:ess_sup_smul_measure",
        "lemma:ess_sup_comp_le_ess_sup_map_measure",
        "lemma:measurable_embedding.ess_sup_map_measure",
        "lemma:ess_sup_map_measure_of_measurable",
        "lemma:ess_sup_map_measure",
        "lemma:ae_lt_of_ess_sup_lt",
        "lemma:ae_lt_of_lt_ess_inf",
        "lemma:ess_sup_indicator_eq_ess_sup_restrict",
        "lemma:ennreal.ae_le_ess_sup",
        "lemma:ennreal.ess_sup_eq_zero_iff",
        "lemma:ennreal.ess_sup_const_mul",
        "lemma:ennreal.ess_sup_add_le",
        "lemma:ennreal.ess_sup_liminf_le",
    ]


def test_parse_lean_filtered_colimits_fixture() -> None:
    contents = read_fixture("filtered_colimits.lean")
    parsed_items = parse_lean(contents)
    assert [item.full_name for item in parsed_items] == [
        "def:SemiRing.filtered_colimits.colimit",
        "def:SemiRing.filtered_colimits.colimit_cocone",
        "def:SemiRing.filtered_colimits.colimit_cocone_is_colimit",
        "def:CommSemiRing.filtered_colimits.colimit",
        "def:CommSemiRing.filtered_colimits.colimit_cocone",
        "def:CommSemiRing.filtered_colimits.colimit_cocone_is_colimit",
        "def:Ring.filtered_colimits.colimit",
        "def:Ring.filtered_colimits.colimit_cocone",
        "def:Ring.filtered_colimits.colimit_cocone_is_colimit",
        "def:CommRing.filtered_colimits.colimit",
        "def:CommRing.filtered_colimits.colimit_cocone",
        "def:CommRing.filtered_colimits.colimit_cocone_is_colimit",
    ]
