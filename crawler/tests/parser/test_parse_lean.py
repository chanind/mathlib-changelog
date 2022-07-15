from pathlib import Path
from crawler.parser.parse_lean import parse_lean


FIXTURES_DIR = Path(__file__).resolve().parent / "../fixtures"


def read_fixture(filename: str) -> str:
    with open(FIXTURES_DIR / filename, "r") as file:
        return file.read()


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


def test_parse_lean_algebra_fixture() -> None:
    contents = read_fixture("algebra.lean")
    parsed_items = parse_lean(contents)
    assert [item.full_name for item in parsed_items] == [
        "def:category_theory.monad.algebra.hom.id",
        "def:category_theory.monad.algebra.hom.comp",
        "lemma:category_theory.monad.algebra.comp_eq_comp",
        "lemma:category_theory.monad.algebra.id_eq_id",
        "lemma:category_theory.monad.algebra.id_f",
        "lemma:category_theory.monad.algebra.comp_f",
        "def:category_theory.monad.algebra.iso_mk",
        "def:category_theory.monad.forget",
        "def:category_theory.monad.free",
        "def:category_theory.monad.adj",
        "lemma:category_theory.monad.algebra_iso_of_iso",
        "lemma:category_theory.monad.algebra_epi_of_epi",
        "lemma:category_theory.monad.algebra_mono_of_mono",
        "lemma:category_theory.monad.left_adjoint_forget",
        "lemma:category_theory.monad.of_right_adjoint_forget",
        "def:category_theory.monad.algebra_functor_of_monad_hom",
        "def:category_theory.monad.algebra_functor_of_monad_hom_id",
        "def:category_theory.monad.algebra_functor_of_monad_hom_comp",
        "def:category_theory.monad.algebra_functor_of_monad_hom_eq",
        "def:category_theory.monad.algebra_equiv_of_iso_monads",
        "lemma:category_theory.monad.algebra_equiv_of_iso_monads_comp_forget",
        "def:category_theory.comonad.coalgebra.hom.id",
        "def:category_theory.comonad.coalgebra.hom.comp",
        "lemma:category_theory.comonad.coalgebra.comp_eq_comp",
        "lemma:category_theory.comonad.coalgebra.id_eq_id",
        "lemma:category_theory.comonad.coalgebra.id_f",
        "lemma:category_theory.comonad.coalgebra.comp_f",
        "def:category_theory.comonad.coalgebra.iso_mk",
        "def:category_theory.comonad.forget",
        "def:category_theory.comonad.cofree",
        "def:category_theory.comonad.adj",
        "lemma:category_theory.comonad.coalgebra_iso_of_iso",
        "lemma:category_theory.comonad.algebra_epi_of_epi",
        "lemma:category_theory.comonad.algebra_mono_of_mono",
        "lemma:category_theory.comonad.right_adjoint_forget",
        "lemma:category_theory.comonad.of_left_adjoint_forget",
    ]


def test_parse_lean_cont_mdiff_fixture() -> None:
    contents = read_fixture("cont_mdiff.lean")
    parse_lean(contents)  # just make sure it doesn't error


def test_parse_lean_to_additive_fixture() -> None:
    contents = read_fixture("to_additive.lean")
    parse_lean(contents)  # just make sure it doesn't error


def test_parse_lean_fermat4_fixture() -> None:
    contents = read_fixture("fermat4.lean")
    parse_lean(contents)  # just make sure it doesn't error
