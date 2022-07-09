## [2020-02-28 18:23:59+01:00](https://github.com/leanprover-community/mathlib/commit/19a9bdc)
fix(tactic/omega): reify nonconstant ints and nats ([#1748](https://github.com/leanprover-community/mathlib/pull/1748))
#### Estimated changes
Modified archive/imo1988_q6.lean

Modified docs/tactics.md

Modified scripts/nolints.txt

Modified src/tactic/omega/clause.lean

Modified src/tactic/omega/coeffs.lean

Modified src/tactic/omega/eq_elim.lean

Modified src/tactic/omega/find_ees.lean

Modified src/tactic/omega/find_scalars.lean

Modified src/tactic/omega/int/dnf.lean
- \+/\- *lemma* is_nnf_push_neg
- \+/\- *lemma* is_nnf_nnf
- \+/\- *lemma* nnf_equiv
- \+/\- *lemma* neg_free_neg_elim
- \+/\- *lemma* implies_neg_elim
- \+/\- *lemma* clauses_sat_dnf_core
- \+/\- *lemma* unsat_of_clauses_unsat
- \+/\- *lemma* is_nnf_push_neg
- \+/\- *lemma* is_nnf_nnf
- \+/\- *lemma* nnf_equiv
- \+/\- *lemma* neg_free_neg_elim
- \+/\- *lemma* implies_neg_elim
- \+/\- *lemma* clauses_sat_dnf_core
- \+/\- *lemma* unsat_of_clauses_unsat
- \+/\- *def* push_neg
- \+/\- *def* nnf
- \+/\- *def* is_nnf
- \+/\- *def* neg_free
- \+/\- *def* neg_elim
- \+/\- *def* dnf_core
- \+/\- *def* dnf
- \+/\- *def* push_neg
- \+/\- *def* nnf
- \+/\- *def* is_nnf
- \+/\- *def* neg_free
- \+/\- *def* neg_elim
- \+/\- *def* dnf_core
- \+/\- *def* dnf

Modified src/tactic/omega/int/form.lean
- \+/\- *lemma* sat_of_implies_of_sat
- \+/\- *lemma* sat_or
- \+/\- *lemma* univ_close_of_valid
- \+/\- *lemma* valid_of_unsat_not
- \+/\- *lemma* sat_of_implies_of_sat
- \+/\- *lemma* sat_or
- \+/\- *lemma* univ_close_of_valid
- \+/\- *lemma* valid_of_unsat_not
- \+/\- *def* holds
- \+/\- *def* univ_close
- \+/\- *def* fresh_index
- \+/\- *def* valid
- \+/\- *def* sat
- \+/\- *def* implies
- \+/\- *def* equiv
- \+/\- *def* unsat
- \+/\- *def* repr
- \+/\- *def* holds
- \+/\- *def* univ_close
- \+/\- *def* fresh_index
- \+/\- *def* valid
- \+/\- *def* sat
- \+/\- *def* implies
- \+/\- *def* equiv
- \+/\- *def* unsat
- \+/\- *def* repr

Modified src/tactic/omega/int/main.lean
- \+/\- *lemma* univ_close_of_unsat_clausify
- \+/\- *lemma* univ_close_of_unsat_clausify

Modified src/tactic/omega/int/preterm.lean

Modified src/tactic/omega/lin_comb.lean

Modified src/tactic/omega/main.lean

Modified src/tactic/omega/misc.lean

Modified src/tactic/omega/nat/dnf.lean
- \+/\- *lemma* exists_clause_holds
- \+/\- *lemma* exists_clause_sat
- \+/\- *lemma* unsat_of_unsat_dnf
- \+/\- *lemma* exists_clause_holds
- \+/\- *lemma* exists_clause_sat
- \+/\- *lemma* unsat_of_unsat_dnf
- \+/\- *def* dnf_core
- \+/\- *def* dnf
- \+/\- *def* dnf_core
- \+/\- *def* dnf

Modified src/tactic/omega/nat/form.lean
- \+/\- *lemma* sat_of_implies_of_sat
- \+/\- *lemma* sat_or
- \+/\- *lemma* univ_close_of_valid
- \+/\- *lemma* valid_of_unsat_not
- \+/\- *lemma* sat_of_implies_of_sat
- \+/\- *lemma* sat_or
- \+/\- *lemma* univ_close_of_valid
- \+/\- *lemma* valid_of_unsat_not
- \+/\- *def* holds
- \+/\- *def* univ_close
- \+/\- *def* neg_free
- \+/\- *def* sub_free
- \+/\- *def* fresh_index
- \+/\- *def* valid
- \+/\- *def* sat
- \+/\- *def* implies
- \+/\- *def* equiv
- \+/\- *def* unsat
- \+/\- *def* repr
- \+/\- *def* holds
- \+/\- *def* univ_close
- \+/\- *def* neg_free
- \+/\- *def* sub_free
- \+/\- *def* fresh_index
- \+/\- *def* valid
- \+/\- *def* sat
- \+/\- *def* implies
- \+/\- *def* equiv
- \+/\- *def* unsat
- \+/\- *def* repr

Modified src/tactic/omega/nat/main.lean
- \+/\- *lemma* univ_close_of_unsat_neg_elim_not
- \+/\- *lemma* univ_close_of_unsat_neg_elim_not

Modified src/tactic/omega/nat/neg_elim.lean
- \+/\- *lemma* is_nnf_push_neg
- \+/\- *lemma* is_nnf_nnf
- \+/\- *lemma* nnf_equiv
- \+/\- *lemma* implies_neg_elim_core
- \+/\- *lemma* neg_free_neg_elim
- \+/\- *lemma* implies_neg_elim
- \+/\- *lemma* is_nnf_push_neg
- \+/\- *lemma* is_nnf_nnf
- \+/\- *lemma* nnf_equiv
- \+/\- *lemma* implies_neg_elim_core
- \+/\- *lemma* neg_free_neg_elim
- \+/\- *lemma* implies_neg_elim
- \+/\- *def* push_neg
- \+/\- *def* nnf
- \+/\- *def* is_nnf
- \+/\- *def* neg_elim_core
- \+/\- *def* neg_elim
- \+/\- *def* push_neg
- \+/\- *def* nnf
- \+/\- *def* is_nnf
- \+/\- *def* neg_elim_core
- \+/\- *def* neg_elim

Modified src/tactic/omega/nat/preterm.lean

Modified src/tactic/omega/nat/sub_elim.lean
- \+/\- *lemma* sat_sub_elim
- \+/\- *lemma* unsat_of_unsat_sub_elim
- \+/\- *lemma* sat_sub_elim
- \+/\- *lemma* unsat_of_unsat_sub_elim
- \+/\- *def* sub_terms
- \+/\- *def* sub_subst
- \+/\- *def* is_diff
- \+/\- *def* sub_elim_core
- \+/\- *def* sub_fresh_index
- \+/\- *def* sub_elim
- \+/\- *def* sub_terms
- \+/\- *def* sub_subst
- \+/\- *def* is_diff
- \+/\- *def* sub_elim_core
- \+/\- *def* sub_fresh_index
- \+/\- *def* sub_elim

Modified src/tactic/omega/prove_unsats.lean

Modified src/tactic/omega/term.lean

Modified test/omega.lean



## [2020-02-28 16:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/354a4ed)
chore(ci): remove unneeded Lean version restrictions ([#2065](https://github.com/leanprover-community/mathlib/pull/2065))
* remove lean version from CI
* more version references
* fix?
* persist environment var between steps
#### Estimated changes
Modified .github/workflows/build.yml

Modified scripts/deploy_docs.sh

Modified scripts/deploy_nightly.sh



## [2020-02-28 15:33:18](https://github.com/leanprover-community/mathlib/commit/0760829)
feat(ring_theory): Fractional ideals ([#2062](https://github.com/leanprover-community/mathlib/pull/2062))
* Some WIP work on fractional ideals
* Fill in the `sorry`
* A lot of instances for fractional_ideal
* Show that an invertible fractional ideal `I` has inverse `1 : I`
* Cleanup and documentation
* Move `has_div submodule` to algebra_operations
* More cleanup and documentation
* Explain the `non_zero_divisors R` in the `quotient` section
* whitespace
Co-Authored-By: Scott Morrison <scott@tqft.net>
* `has_inv` instance for `fractional_ideal`
* `set.univ.image` -> `set.range`
* Fix: `mem_div_iff.mpr` should be `mem_div_iff.mp`
(but both reduce to reflexivity anyway)
* Add `mem_div_iff_smul_subset`
Since that is how the definition of `I / J` is traditionally done,
but it is not as convenient to work with, I didn't change the definition
but added a lemma stating the two are equivalent
* whitespace again
(it got broken because I merged changes incorrectly)
* Fix unused argument to `inv_nonzero`
#### Estimated changes
Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* mem_div_iff_forall_mul_mem
- \+ *lemma* mem_div_iff_smul_subset
- \+ *lemma* le_div_iff

Created src/ring_theory/fractional_ideal.lean
- \+ *lemma* ext
- \+ *lemma* fractional_of_subset_one
- \+ *lemma* mem_zero_iff
- \+ *lemma* val_zero
- \+ *lemma* nonzero_iff_val_nonzero
- \+ *lemma* mem_one_iff
- \+ *lemma* coe_mem_one
- \+ *lemma* le_iff
- \+ *lemma* zero_le
- \+ *lemma* bot_eq_zero
- \+ *lemma* eq_zero_iff
- \+ *lemma* fractional_sup
- \+ *lemma* fractional_inf
- \+ *lemma* sup_eq_add
- \+ *lemma* val_add
- \+ *lemma* fractional_mul
- \+ *lemma* val_mul
- \+ *lemma* mul_left_mono
- \+ *lemma* mul_right_mono
- \+ *lemma* fractional_div_of_nonzero
- \+ *lemma* div_nonzero
- \+ *lemma* inv_nonzero
- \+ *lemma* div_one
- \+ *theorem* right_inverse_eq
- \+ *def* is_fractional
- \+ *def* fractional_ideal

Modified src/ring_theory/localization.lean
- \+ *lemma* of_smul
- \+ *lemma* coe_smul
- \+ *lemma* coe_mul_eq_smul
- \+ *lemma* mul_coe_eq_smul
- \+ *lemma* lin_coe_apply
- \+ *lemma* of_id
- \+ *lemma* is_integer_coe
- \+ *lemma* is_integer_add
- \+ *lemma* is_integer_mul
- \+ *lemma* is_integer_smul
- \+ *def* lin_coe
- \+ *def* is_integer



## [2020-02-28 13:49:48](https://github.com/leanprover-community/mathlib/commit/4149099)
fix(tactic/ring): more precise pattern match for div ([#1557](https://github.com/leanprover-community/mathlib/pull/1557))
* fix(tactic/ring): more precise pattern match for div
* add test
* fix instance check for div
* chore(algebra/quadratic_discriminant): add braces in have steps
* use norm_num instead of ring to evaluate exponents
* fix norm_num uses
* fix norm_num pow bug
* bugfix
* fix proof
#### Estimated changes
Modified src/algebra/quadratic_discriminant.lean

Modified src/linear_algebra/determinant.lean

Modified src/tactic/norm_num.lean

Modified src/tactic/ring.lean

Modified test/ring.lean



## [2020-02-28 04:02:06](https://github.com/leanprover-community/mathlib/commit/0bf2064)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-28 01:50:01](https://github.com/leanprover-community/mathlib/commit/4637e5c)
refactor(analysis/calculus/times_cont_diff): massive refactor ([#2012](https://github.com/leanprover-community/mathlib/pull/2012))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* feat(*/multilinear): better multilinear
* docstrings
* snoc
* fix build
* comp_snoc and friends
* refactor(analysis/calculus/times_cont_diff): massive refactor
* fix docstring
* move notation
* fix build
* linter
* linter again
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* curryfication -> currying
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* add_one_le_of_lt

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.zero_eq'
- \+ *lemma* has_ftaylor_series_up_to_on.congr
- \+ *lemma* has_ftaylor_series_up_to_on.mono
- \+ *lemma* has_ftaylor_series_up_to_on.of_le
- \+ *lemma* has_ftaylor_series_up_to_on.continuous_on
- \+ *lemma* has_ftaylor_series_up_to_on_zero_iff
- \+ *lemma* has_ftaylor_series_up_to_on_top_iff
- \+ *lemma* has_ftaylor_series_up_to_on.has_fderiv_within_at
- \+ *lemma* has_ftaylor_series_up_to_on.differentiable_on
- \+ *lemma* times_cont_diff_on_nat
- \+/\- *lemma* times_cont_diff_on_top
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+/\- *lemma* times_cont_diff_on.congr
- \+ *lemma* times_cont_diff_on_congr
- \+/\- *lemma* times_cont_diff_on.mono
- \+/\- *lemma* times_cont_diff_on.congr_mono
- \+/\- *lemma* times_cont_diff_on.of_le
- \+/\- *lemma* times_cont_diff_on.differentiable_on
- \+/\- *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \+ *lemma* iterated_fderiv_within_zero_apply
- \+ *lemma* iterated_fderiv_within_zero_eq_comp
- \+ *lemma* iterated_fderiv_within_succ_apply_left
- \+ *lemma* iterated_fderiv_within_succ_eq_comp_left
- \+ *lemma* iterated_fderiv_within_succ_eq_comp_right
- \+ *lemma* iterated_fderiv_within_one_apply
- \+/\- *lemma* iterated_fderiv_within_congr
- \+/\- *lemma* iterated_fderiv_within_inter_open
- \+ *lemma* iterated_fderiv_within_inter'
- \+/\- *lemma* iterated_fderiv_within_inter
- \+/\- *lemma* times_cont_diff_on_zero
- \+ *lemma* times_cont_diff_on_of_continuous_on_differentiable_on
- \+ *lemma* times_cont_diff_on_of_differentiable_on
- \+ *lemma* times_cont_diff_on.continuous_on_iterated_fderiv_within
- \+ *lemma* times_cont_diff_on.differentiable_on_iterated_fderiv_within
- \+ *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on
- \+ *lemma* times_cont_diff_on.fderiv_within
- \+/\- *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* has_ftaylor_series_up_to.zero_eq'
- \+ *lemma* has_ftaylor_series_up_to_on_univ_iff
- \+ *lemma* has_ftaylor_series_up_to.has_ftaylor_series_up_to_on
- \+ *lemma* has_ftaylor_series_up_to.of_le
- \+ *lemma* has_ftaylor_series_up_to.continuous
- \+ *lemma* has_ftaylor_series_up_to_zero_iff
- \+ *lemma* has_ftaylor_series_up_to.has_fderiv_at
- \+ *lemma* has_ftaylor_series_up_to.differentiable
- \+/\- *lemma* times_cont_diff_top
- \+/\- *lemma* times_cont_diff.times_cont_diff_on
- \+/\- *lemma* times_cont_diff.of_le
- \+/\- *lemma* times_cont_diff.continuous
- \+ *lemma* times_cont_diff.differentiable
- \+ *lemma* iterated_fderiv_zero_apply
- \+ *lemma* iterated_fderiv_zero_eq_comp
- \+ *lemma* iterated_fderiv_succ_apply_left
- \+ *lemma* iterated_fderiv_succ_eq_comp_left
- \+ *lemma* iterated_fderiv_within_univ
- \+ *lemma* ftaylor_series_within_univ
- \+ *lemma* iterated_fderiv_succ_eq_comp_right
- \+ *lemma* iterated_fderiv_one_apply
- \+ *lemma* times_cont_diff_iff_continuous_differentiable
- \+ *lemma* times_cont_diff_of_differentiable_iterated_fderiv
- \+/\- *lemma* times_cont_diff.continuous_fderiv
- \+/\- *lemma* times_cont_diff.continuous_fderiv_apply
- \+ *lemma* iterated_fderiv_within_zero_fun
- \+ *lemma* times_cont_diff_zero_fun
- \+/\- *lemma* times_cont_diff_on_const
- \+ *lemma* continuous_linear_map.times_cont_diff
- \+ *lemma* has_ftaylor_series_up_to_on.continuous_linear_map_comp
- \+ *lemma* times_cont_diff_on.continuous_linear_map_comp
- \+ *lemma* times_cont_diff.continuous_linear_map_comp
- \+ *lemma* continuous_linear_equiv.comp_times_cont_diff_on_iff
- \+ *lemma* has_ftaylor_series_up_to_on.comp_continuous_linear_map
- \+ *lemma* times_cont_diff_on.comp_continuous_linear_map
- \+ *lemma* times_cont_diff.comp_continuous_linear_map
- \+ *lemma* continuous_linear_equiv.times_cont_diff_on_comp_iff
- \+ *lemma* has_ftaylor_series_up_to_on.prod
- \+/\- *lemma* times_cont_diff_on.comp
- \+/\- *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \- *lemma* iterated_fderiv_zero
- \- *lemma* iterated_fderiv_succ
- \- *lemma* iterated_fderiv_within_zero
- \- *lemma* iterated_fderiv_within_succ
- \+/\- *lemma* iterated_fderiv_within_congr
- \+/\- *lemma* iterated_fderiv_within_inter_open
- \+/\- *lemma* iterated_fderiv_within_inter
- \- *lemma* times_cont_diff_rec_zero
- \- *lemma* times_cont_diff_rec_succ
- \- *lemma* times_cont_diff_rec.of_succ
- \- *lemma* times_cont_diff_rec.continuous
- \- *lemma* times_cont_diff_rec.differentiable
- \- *lemma* times_cont_diff_on_rec_zero
- \- *lemma* times_cont_diff_on_rec_succ
- \- *lemma* times_cont_diff_on_rec.of_succ
- \- *lemma* times_cont_diff_on_rec.continuous_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on_rec.differentiable_on
- \- *lemma* times_cont_diff_on_rec_univ
- \+/\- *lemma* times_cont_diff_on_zero
- \- *lemma* times_cont_diff_on_succ
- \+/\- *lemma* times_cont_diff_on.of_le
- \- *lemma* times_cont_diff_on.of_succ
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+/\- *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \+/\- *lemma* times_cont_diff_on.differentiable_on
- \+/\- *lemma* times_cont_diff_on_top
- \- *lemma* times_cont_diff_on_fderiv_within_nat
- \- *lemma* times_cont_diff_on_fderiv_within
- \+/\- *lemma* times_cont_diff_on.congr_mono
- \+/\- *lemma* times_cont_diff_on.congr
- \- *lemma* times_cont_diff_on.congr_mono'
- \+/\- *lemma* times_cont_diff_on.mono
- \+/\- *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \- *lemma* times_cont_diff_on_univ
- \- *lemma* times_cont_diff_succ
- \+/\- *lemma* times_cont_diff.of_le
- \- *lemma* times_cont_diff.of_succ
- \+/\- *lemma* times_cont_diff.continuous
- \+/\- *lemma* times_cont_diff.continuous_fderiv
- \+/\- *lemma* times_cont_diff.continuous_fderiv_apply
- \+/\- *lemma* times_cont_diff_top
- \+/\- *lemma* times_cont_diff.times_cont_diff_on
- \+/\- *lemma* times_cont_diff_on_const
- \- *lemma* times_cont_diff_on.comp_is_bounded_linear
- \- *lemma* times_cont_diff.comp_is_bounded_linear
- \+/\- *lemma* times_cont_diff_on.comp
- \+/\- *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \+ *theorem* has_ftaylor_series_up_to_on_succ_iff_left
- \+ *theorem* has_ftaylor_series_up_to_on_succ_iff_right
- \+ *theorem* times_cont_diff_on_succ_iff_has_fderiv_within_at
- \+ *theorem* iterated_fderiv_within_succ_apply_right
- \+ *theorem* has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on
- \+ *theorem* times_cont_diff_on.ftaylor_series_within
- \+ *theorem* times_cont_diff_on_succ_iff_fderiv_within
- \+ *theorem* times_cont_diff_on_top_iff_fderiv_within
- \+ *theorem* has_ftaylor_series_up_to_succ_iff_right
- \+ *theorem* times_cont_diff_on_univ
- \+ *theorem* iterated_fderiv_succ_apply_right
- \+ *theorem* times_cont_diff_on_iff_ftaylor_series
- \+ *theorem* times_cont_diff_succ_iff_fderiv
- \+ *theorem* times_cont_diff_top_iff_fderiv
- \- *theorem* iterated_fderiv_within_univ
- \- *theorem* times_cont_diff_on_iff_times_cont_diff_on_rec
- \- *theorem* times_cont_diff_iff_times_cont_diff_rec
- \+ *def* formal_multilinear_series
- \+ *def* shift
- \+ *def* unshift
- \+ *def* ftaylor_series_within
- \+ *def* ftaylor_series
- \- *def* iterated_continuous_linear_map
- \- *def* iterated_continuous_linear_map.normed_group_rec
- \- *def* iterated_continuous_linear_map.normed_space_rec
- \- *def* iterated_fderiv
- \- *def* iterated_fderiv_within
- \- *def* times_cont_diff_rec
- \- *def* times_cont_diff_on_rec
- \- *def* times_cont_diff_on
- \- *def* times_cont_diff

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_linear_map_prod_multilinear
- \+ *lemma* is_bounded_linear_map_continuous_multilinear_map_comp_linear
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_left
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_right
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+ *lemma* is_bounded_bilinear_map_comp_multilinear
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_right

Modified src/analysis/normed_space/multilinear.lean

Modified src/geometry/manifold/basic_smooth_bundle.lean

Modified src/geometry/manifold/mfderiv.lean

Modified src/geometry/manifold/real_instances.lean

Modified src/geometry/manifold/smooth_manifold_with_corners.lean

Modified src/linear_algebra/multilinear.lean

Modified src/topology/algebra/multilinear.lean

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_of_mem_nhds_within



## [2020-02-27 22:04:31](https://github.com/leanprover-community/mathlib/commit/0e4eb09)
feat(ci): avoid push to Azure if branch has been updated ([#2048](https://github.com/leanprover-community/mathlib/pull/2048))
* avoid push to Azure if branch has been updated
* changes to git config in deploy_nightly.sh break git fetch
* I don't understand why this is different than on my own repo
* artifact upload breaks fetch, I guess?
* factor out git config
* fix env variable
* adjustments
* removed repo check
#### Estimated changes
Modified .github/workflows/build.yml

Modified scripts/deploy_nightly.sh

Modified scripts/update_nolints.sh



## [2020-02-27 17:35:47](https://github.com/leanprover-community/mathlib/commit/691456c)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-27 15:18:39](https://github.com/leanprover-community/mathlib/commit/7907f8f)
feat(tactic/tidy): include norm_cast in tidy ([#2063](https://github.com/leanprover-community/mathlib/pull/2063))
* feat(tactic/tidy): include norm_cast in tidy
* Update src/tactic/core.lean
#### Estimated changes
Modified src/tactic/auto_cases.lean

Modified src/tactic/core.lean

Modified src/tactic/hint.lean

Modified src/tactic/tidy.lean



## [2020-02-27 13:32:50](https://github.com/leanprover-community/mathlib/commit/6c2411b)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-27 11:54:47](https://github.com/leanprover-community/mathlib/commit/a46b3e5)
doc(data/finsupp): module docs and docstrings  ([#2059](https://github.com/leanprover-community/mathlib/pull/2059))
* doc(data/finsupp): module docs and docstrings
* chore(data/finsupp): squeeze_simp, cleanup, style
* reviewer comments
#### Estimated changes
Modified src/data/finsupp.lean
- \+/\- *lemma* zero_apply
- \+/\- *lemma* support_zero
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* map_domain_id
- \+/\- *lemma* one_def
- \+/\- *lemma* smul_apply'
- \+/\- *lemma* zero_apply
- \+/\- *lemma* support_zero
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* map_domain_id
- \+/\- *lemma* one_def
- \+/\- *lemma* smul_apply'
- \+ *def* comap_domain
- \+/\- *def* frange
- \+ *def* split
- \+ *def* split_comp
- \+/\- *def* frange



## [2020-02-27 01:35:32](https://github.com/leanprover-community/mathlib/commit/ef1e38e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-26 23:31:28](https://github.com/leanprover-community/mathlib/commit/f0bb2f8)
feat(ring_theory/polynomial): mv_polynomial.integral_domain ([#2021](https://github.com/leanprover-community/mathlib/pull/2021))
* feat(ring_theory/polynomial): mv_polynomial.integral_domain
* Add docstrings
* Add docstrings
* Fix import
* Fix build
* Please linter, please
* Update src/algebra/ring.lean
* Clean up code, process comments
* Update src/data/equiv/fin.lean
* Update src/data/equiv/fin.lean
* Update src/data/equiv/fin.lean
* Update src/ring_theory/polynomial.lean
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* integral_domain.to_is_integral_domain
- \+ *def* is_integral_domain.to_integral_domain

Modified src/data/equiv/algebra.lean

Modified src/data/equiv/fin.lean
- \+ *def* fin_zero_equiv'
- \+ *def* fin_succ_equiv

Modified src/data/mv_polynomial.lean
- \+ *theorem* exists_finset_rename
- \+ *theorem* exists_fin_rename

Modified src/ring_theory/adjoin.lean

Modified src/ring_theory/polynomial.lean
- \+ *lemma* is_integral_domain_fin
- \+ *lemma* is_integral_domain_fintype
- \+ *theorem* is_noetherian_ring_fin
- \- *theorem* is_noetherian_ring_polynomial
- \- *theorem* is_noetherian_ring_mv_polynomial_fin
- \- *theorem* is_noetherian_ring_mv_polynomial_of_fintype
- \+ *def* integral_domain_fintype



## [2020-02-26 10:53:53](https://github.com/leanprover-community/mathlib/commit/73b41b2)
chore(data/prod): rename `injective_prod` to `injective.prod` ([#2058](https://github.com/leanprover-community/mathlib/pull/2058))
This way we can use dot notation
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* function.injective.prod
- \- *lemma* function.injective_prod

Modified src/topology/uniform_space/uniform_embedding.lean



## [2020-02-25 22:59:53](https://github.com/leanprover-community/mathlib/commit/6a6beaa)
chore(data/list/basic): drop `append_foldl` and `append_foldr`, add `map_nil` and `prod_singleton` ([#2057](https://github.com/leanprover-community/mathlib/pull/2057))
`append_foldl` and `append_foldr` were unused duplicates of
`foldl_append` and `foldr_append`
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* map_nil
- \+ *theorem* prod_singleton
- \- *theorem* append_foldl
- \- *theorem* append_foldr



## [2020-02-25 21:09:35](https://github.com/leanprover-community/mathlib/commit/7be3e93)
chore(field_theory/minimal_polynomial): fix timeout ([#2054](https://github.com/leanprover-community/mathlib/pull/2054))
* chore(field_theory/minimal_polynomial): fix timeout
* Update src/field_theory/minimal_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean



## [2020-02-25 19:22:49](https://github.com/leanprover-community/mathlib/commit/06c5594)
chore(analyis/normed_space/banach): split proof to avoid timeout ([#2053](https://github.com/leanprover-community/mathlib/pull/2053))
* chore(analyis/normed_space/banach): split proof to avoid timeout
* delay introducing unnecessary variable
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* fix indent
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* exists_approx_preimage_norm_le
- \+/\- *theorem* exists_preimage_norm_le
- \+/\- *theorem* exists_preimage_norm_le



## [2020-02-25 16:06:50](https://github.com/leanprover-community/mathlib/commit/089d058)
feat(tactic/lint): linter for commutativity lemmas that are marked simp ([#2045](https://github.com/leanprover-community/mathlib/pull/2045))
* feat(tactic/lint): linter for commutativity lemmas that are marked simp
* chore(*): remove simp from commutativity lemmas
* doc(*): document simp_comm linter
#### Estimated changes
Modified docs/commands.md

Modified src/data/finmap.lean
- \+/\- *theorem* erase_erase
- \+/\- *theorem* erase_erase

Modified src/data/finset.lean
- \+/\- *theorem* union_comm
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm
- \+/\- *theorem* union_comm
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm

Modified src/data/hash_map.lean

Modified src/data/list/alist.lean
- \+/\- *theorem* erase_erase
- \+/\- *theorem* erase_erase

Modified src/data/list/basic.lean
- \+/\- *theorem* disjoint_comm
- \+ *theorem* disjoint_nil_right
- \+/\- *theorem* disjoint_comm

Modified src/data/multiset.lean
- \+/\- *theorem* disjoint_comm
- \+/\- *theorem* disjoint_comm

Modified src/data/nat/dist.lean
- \+/\- *theorem* dist_comm
- \+/\- *theorem* dist_comm

Modified src/linear_algebra/basis.lean

Modified src/tactic/lint.lean

Modified src/topology/algebra/infinite_sum.lean

Created test/lint_simp_comm.lean
- \+ *lemma* list.filter_congr_decidable



## [2020-02-25 14:16:23](https://github.com/leanprover-community/mathlib/commit/450dcdf)
refactor(order/bounds): use dot notation, reorder, prove more properties ([#2028](https://github.com/leanprover-community/mathlib/pull/2028))
* refactor(order/bounds): use dot notation, prove more properties
Also make parts of `complete_lattice` and
`conditionally_complete_lattice` use these lemmas.
* Comments
* Add a module docstring
* Fixes from review, +4 lemmas about images
* Fix a typo in the previous commit
* Update src/order/bounds.lean
* Update src/order/bounds.lean
#### Estimated changes
Modified src/data/set/finite.lean

Modified src/data/set/lattice.lean

Modified src/order/basic.lean

Modified src/order/bounds.lean
- \+ *lemma* upper_bounds_mono_set
- \+ *lemma* lower_bounds_mono_set
- \+ *lemma* upper_bounds_mono_mem
- \+ *lemma* lower_bounds_mono_mem
- \+/\- *lemma* upper_bounds_mono
- \+/\- *lemma* lower_bounds_mono
- \+ *lemma* bdd_above.mono
- \+ *lemma* bdd_below.mono
- \+ *lemma* is_lub.of_subset_of_superset
- \+ *lemma* is_glb.of_subset_of_superset
- \+ *lemma* is_least.is_glb
- \+ *lemma* is_greatest.is_lub
- \+ *lemma* is_lub.upper_bounds_eq
- \+ *lemma* is_glb.lower_bounds_eq
- \+ *lemma* is_least.lower_bounds_eq
- \+ *lemma* is_greatest.upper_bounds_eq
- \+ *lemma* is_lub.bdd_above
- \+ *lemma* is_glb.bdd_below
- \+ *lemma* is_greatest.bdd_above
- \+ *lemma* is_least.bdd_below
- \+ *lemma* is_least.nonempty
- \+ *lemma* is_greatest.nonempty
- \+ *lemma* upper_bounds_union
- \+ *lemma* lower_bounds_union
- \+ *lemma* union_upper_bounds_subset_upper_bounds_inter
- \+ *lemma* union_lower_bounds_subset_lower_bounds_inter
- \+ *lemma* is_least_union_iff
- \+ *lemma* is_greatest_union_iff
- \+ *lemma* bdd_above.inter_of_left
- \+ *lemma* bdd_above.inter_of_right
- \+ *lemma* bdd_below.inter_of_left
- \+ *lemma* bdd_below.inter_of_right
- \+ *lemma* bdd_above.union
- \+/\- *lemma* bdd_above_union
- \+ *lemma* bdd_below.union
- \+/\- *lemma* bdd_below_union
- \+ *lemma* is_lub.union
- \+ *lemma* is_glb.union
- \+ *lemma* is_least.union
- \+ *lemma* is_greatest.union
- \+ *lemma* is_least_Ici
- \+ *lemma* is_greatest_Iic
- \+/\- *lemma* is_lub_Iic
- \+/\- *lemma* is_glb_Ici
- \+ *lemma* upper_bounds_Iic
- \+ *lemma* lower_bounds_Ici
- \+ *lemma* bdd_above_Iic
- \+ *lemma* bdd_below_Ici
- \+ *lemma* bdd_above_Iio
- \+ *lemma* bdd_below_Ioi
- \+/\- *lemma* is_lub_Iio
- \+/\- *lemma* is_glb_Ioi
- \+ *lemma* upper_bounds_Iio
- \+ *lemma* lower_bounds_Ioi
- \+ *lemma* is_greatest_singleton
- \+ *lemma* is_least_singleton
- \+/\- *lemma* is_lub_singleton
- \+/\- *lemma* is_glb_singleton
- \+/\- *lemma* bdd_above_singleton
- \+/\- *lemma* bdd_below_singleton
- \+ *lemma* upper_bounds_singleton
- \+ *lemma* lower_bounds_singleton
- \+ *lemma* bdd_above_Icc
- \+ *lemma* bdd_above_Ico
- \+ *lemma* bdd_above_Ioc
- \+ *lemma* bdd_above_Ioo
- \+ *lemma* is_greatest_Icc
- \+/\- *lemma* is_lub_Icc
- \+ *lemma* upper_bounds_Icc
- \+ *lemma* is_least_Icc
- \+/\- *lemma* is_glb_Icc
- \+ *lemma* lower_bounds_Icc
- \+ *lemma* is_greatest_Ioc
- \+/\- *lemma* is_lub_Ioc
- \+ *lemma* upper_bounds_Ioc
- \+ *lemma* is_least_Ico
- \+/\- *lemma* is_glb_Ico
- \+ *lemma* lower_bounds_Ico
- \+/\- *lemma* is_glb_Ioo
- \+ *lemma* lower_bounds_Ioo
- \+/\- *lemma* is_glb_Ioc
- \+ *lemma* lower_bound_Ioc
- \+/\- *lemma* is_lub_Ioo
- \+ *lemma* upper_bounds_Ioo
- \+/\- *lemma* is_lub_Ico
- \+ *lemma* upper_bounds_Ico
- \+/\- *lemma* bdd_below_iff_subset_Ici
- \+/\- *lemma* bdd_above_iff_subset_Iic
- \+/\- *lemma* bdd_below_bdd_above_iff_subset_Icc
- \+ *lemma* order_top.upper_bounds_univ
- \+ *lemma* is_greatest_univ
- \+ *lemma* is_lub_univ
- \+ *lemma* order_bot.lower_bounds_univ
- \+ *lemma* is_least_univ
- \+ *lemma* is_glb_univ
- \+ *lemma* no_top_order.upper_bounds_univ
- \+ *lemma* no_bot_order.lower_bounds_univ
- \+ *lemma* upper_bounds_empty
- \+ *lemma* lower_bounds_empty
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_below_empty
- \+/\- *lemma* is_glb_empty
- \+/\- *lemma* is_lub_empty
- \+ *lemma* is_lub.nonempty
- \+ *lemma* is_glb.nonempty
- \+/\- *lemma* bdd_above_insert
- \+ *lemma* bdd_above.insert
- \+/\- *lemma* bdd_below_insert
- \+ *lemma* bdd_below.insert
- \+ *lemma* is_lub.insert
- \+ *lemma* is_glb.insert
- \+ *lemma* is_greatest.insert
- \+ *lemma* is_least.insert
- \+ *lemma* upper_bounds_insert
- \+ *lemma* lower_bounds_insert
- \+ *lemma* is_lub_pair
- \+ *lemma* is_glb_pair
- \+ *lemma* is_least_pair
- \+ *lemma* is_greatest_pair
- \+ *lemma* lower_bounds_le_upper_bounds
- \+ *lemma* is_glb_le_is_lub
- \+ *lemma* is_lub_lt_iff
- \+ *lemma* lt_is_glb_iff
- \+ *lemma* is_least.unique
- \+ *lemma* is_least.is_least_iff_eq
- \+ *lemma* is_greatest.unique
- \+ *lemma* is_greatest.is_greatest_iff_eq
- \+ *lemma* is_lub.unique
- \+ *lemma* is_glb.unique
- \+/\- *lemma* is_lub_le_iff
- \+/\- *lemma* le_is_glb_iff
- \+/\- *lemma* lt_is_lub_iff
- \+/\- *lemma* is_glb_lt_iff
- \+/\- *lemma* mem_upper_bounds_image
- \+/\- *lemma* mem_lower_bounds_image
- \+ *lemma* map_bdd_above
- \+ *lemma* map_bdd_below
- \+ *lemma* map_is_least
- \+ *lemma* map_is_greatest
- \+ *lemma* is_lub_image_le
- \+ *lemma* le_is_glb_image_le
- \+/\- *lemma* upper_bounds_mono
- \+/\- *lemma* lower_bounds_mono
- \+/\- *lemma* mem_upper_bounds_image
- \+/\- *lemma* mem_lower_bounds_image
- \+/\- *lemma* is_lub_singleton
- \+/\- *lemma* is_glb_singleton
- \+/\- *lemma* is_glb_Ici
- \+/\- *lemma* is_glb_Icc
- \+/\- *lemma* is_glb_Ico
- \+/\- *lemma* is_lub_Iic
- \+/\- *lemma* is_lub_Icc
- \+/\- *lemma* is_lub_Ioc
- \- *lemma* eq_of_is_least_of_is_least
- \- *lemma* is_least_iff_eq_of_is_least
- \- *lemma* eq_of_is_greatest_of_is_greatest
- \- *lemma* is_greatest_iff_eq_of_is_greatest
- \- *lemma* eq_of_is_lub_of_is_lub
- \- *lemma* is_lub_iff_eq_of_is_lub
- \+/\- *lemma* is_lub_le_iff
- \+/\- *lemma* le_is_glb_iff
- \- *lemma* eq_of_is_glb_of_is_glb
- \- *lemma* is_glb_iff_eq_of_is_glb
- \- *lemma* nonempty_of_is_lub
- \- *lemma* nonempty_of_is_glb
- \+/\- *lemma* is_glb_empty
- \+/\- *lemma* is_lub_empty
- \- *lemma* is_lub_union_sup
- \- *lemma* is_glb_union_inf
- \- *lemma* is_lub_insert_sup
- \- *lemma* is_lub_iff_sup_eq
- \- *lemma* is_glb_insert_inf
- \- *lemma* is_glb_iff_inf_eq
- \+/\- *lemma* lt_is_lub_iff
- \+/\- *lemma* is_glb_lt_iff
- \+/\- *lemma* is_glb_Ioi
- \+/\- *lemma* is_lub_Iio
- \+/\- *lemma* is_glb_Ioo
- \+/\- *lemma* is_glb_Ioc
- \+/\- *lemma* is_lub_Ioo
- \+/\- *lemma* is_lub_Ico
- \- *lemma* bdd_above.mk
- \- *lemma* bdd_below.mk
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_below_empty
- \+/\- *lemma* bdd_above_singleton
- \+/\- *lemma* bdd_below_singleton
- \- *lemma* bdd_above_subset
- \- *lemma* bdd_below_subset
- \- *lemma* bdd_above_inter_left
- \- *lemma* bdd_above_inter_right
- \- *lemma* bdd_below_inter_left
- \- *lemma* bdd_below_inter_right
- \- *lemma* bdd_above_of_bdd_above_of_monotone
- \- *lemma* bdd_below_of_bdd_below_of_monotone
- \+/\- *lemma* bdd_below_iff_subset_Ici
- \+/\- *lemma* bdd_above_iff_subset_Iic
- \+/\- *lemma* bdd_below_bdd_above_iff_subset_Icc
- \- *lemma* bdd_above_top
- \- *lemma* bdd_below_bot
- \+/\- *lemma* bdd_above_union
- \+/\- *lemma* bdd_above_insert
- \+/\- *lemma* bdd_below_union
- \+/\- *lemma* bdd_below_insert
- \+/\- *def* bdd_above
- \+/\- *def* bdd_below
- \+/\- *def* bdd_above
- \+/\- *def* bdd_below

Modified src/order/complete_boolean_algebra.lean

Modified src/order/complete_lattice.lean
- \+/\- *lemma* is_lub_Sup
- \+/\- *lemma* is_glb_Inf
- \+/\- *lemma* is_lub_supr
- \+/\- *lemma* is_glb_infi
- \+/\- *lemma* is_lub_Sup
- \- *lemma* is_lub_iff_Sup_eq
- \+/\- *lemma* is_glb_Inf
- \- *lemma* is_glb_iff_Inf_eq
- \+/\- *lemma* is_lub_supr
- \- *lemma* is_lub_iff_supr_eq
- \+/\- *lemma* is_glb_infi
- \- *lemma* is_glb_iff_infi_eq
- \+/\- *theorem* Inf_le_Sup
- \+ *theorem* Sup_pair
- \+ *theorem* Inf_pair
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* Inf_le_Sup
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* is_lub_cSup
- \+/\- *lemma* is_glb_cInf
- \+ *lemma* cInf_Ici
- \+ *lemma* cSup_Iic
- \- *lemma* cInf_interval
- \- *lemma* cSup_interval
- \+/\- *lemma* is_lub_cSup
- \+/\- *lemma* is_glb_cInf
- \+/\- *theorem* cSup_le_iff
- \+/\- *theorem* le_cInf_iff
- \+/\- *theorem* cInf_le_cSup
- \+/\- *theorem* cSup_union
- \+/\- *theorem* cInf_union
- \+/\- *theorem* cSup_insert
- \+/\- *theorem* cInf_insert
- \+/\- *theorem* cSup_le_iff
- \+/\- *theorem* le_cInf_iff
- \- *theorem* cSup_of_mem_of_le
- \- *theorem* cInf_of_mem_of_le
- \+/\- *theorem* cInf_le_cSup
- \+/\- *theorem* cSup_union
- \+/\- *theorem* cInf_union
- \+/\- *theorem* cSup_insert
- \+/\- *theorem* cInf_insert

Modified src/order/galois_connection.lean

Modified src/topology/algebra/ordered.lean

Modified src/topology/instances/ennreal.lean



## [2020-02-25 12:27:02](https://github.com/leanprover-community/mathlib/commit/a227e06)
Unify naming of lemmas related to the (co)lim functor ([#2040](https://github.com/leanprover-community/mathlib/pull/2040))
#### Estimated changes
Modified src/algebraic_geometry/stalks.lean

Modified src/category_theory/limits/limits.lean
- \+ *lemma* limit.map_π
- \+ *lemma* colimit.ι_map
- \- *lemma* lim.map_π
- \- *lemma* colim.ι_map

Modified src/topology/sheaves/stalks.lean



## [2020-02-25 10:39:52](https://github.com/leanprover-community/mathlib/commit/f77cb57)
chore(data/fintype): move  results depending on big_operators ([#2044](https://github.com/leanprover-community/mathlib/pull/2044))
#### Estimated changes
Modified src/algebra/big_operators.lean

Modified src/analysis/normed_space/multilinear.lean

Modified src/data/fintype.lean
- \- *lemma* card_eq_sum_ones
- \- *lemma* fintype.card_pi
- \- *lemma* fintype.card_fun
- \- *lemma* card_vector
- \- *lemma* finset.prod_attach_univ
- \- *lemma* finset.range_prod_eq_univ_prod
- \- *theorem* fin.prod_univ_succ
- \- *theorem* fin.prod_univ_zero
- \- *theorem* fin.sum_univ_succ
- \- *theorem* fin.prod_univ_cast_succ
- \- *theorem* fin.sum_univ_cast_succ
- \- *theorem* fintype.card_sigma
- \- *theorem* fintype.card_sum

Created src/data/fintype/card.lean
- \+ *lemma* card_eq_sum_ones
- \+ *lemma* fintype.card_pi
- \+ *lemma* fintype.card_fun
- \+ *lemma* card_vector
- \+ *lemma* finset.prod_attach_univ
- \+ *lemma* finset.range_prod_eq_univ_prod
- \+ *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_zero
- \+ *theorem* fin.sum_univ_succ
- \+ *theorem* fin.prod_univ_cast_succ
- \+ *theorem* fin.sum_univ_cast_succ
- \+ *theorem* fintype.card_sigma
- \+ *theorem* fintype.card_sum

Modified src/data/set/finite.lean

Modified src/group_theory/perm/sign.lean

Modified src/group_theory/sylow.lean

Modified src/linear_algebra/basis.lean

Modified src/linear_algebra/determinant.lean

Modified src/number_theory/bernoulli.lean

Modified src/set_theory/cardinal.lean



## [2020-02-25 08:51:21](https://github.com/leanprover-community/mathlib/commit/61d75bb)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-25 06:38:57](https://github.com/leanprover-community/mathlib/commit/17a33f0)
refactor(order/copy): move complete_lattice.copy to its own file ([#2050](https://github.com/leanprover-community/mathlib/pull/2050))
* refactor(order/copy): move complete_lattice.copy to its own file
* Docstrings
* Update src/order/copy.lean
#### Estimated changes
Modified src/data/setoid.lean

Created src/order/copy.lean
- \+ *def* bounded_lattice.copy
- \+ *def* distrib_lattice.copy
- \+ *def* complete_lattice.copy
- \+ *def* complete_distrib_lattice.copy
- \+ *def* conditionally_complete_lattice.copy

Modified src/order/filter/basic.lean
- \- *def* complete_lattice.copy

Modified src/topology/opens.lean



## [2020-02-24 23:51:03](https://github.com/leanprover-community/mathlib/commit/5770369)
refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric ([#2051](https://github.com/leanprover-community/mathlib/pull/2051))
* refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric; it is automatic
* Alternative constructor for isometric bijections
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry_inv_fun
- \+ *def* mk'



## [2020-02-24 22:06:59](https://github.com/leanprover-community/mathlib/commit/3ff50d9)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-24 19:58:16](https://github.com/leanprover-community/mathlib/commit/fb878e7)
feat(tactic/lint): add linter for simp lemmas whose lhs has a variable as head symbol ([#2038](https://github.com/leanprover-community/mathlib/pull/2038))
#### Estimated changes
Modified docs/commands.md

Modified src/algebra/field.lean
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div

Modified src/algebra/module.lean
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub

Modified src/data/list/basic.lean
- \+/\- *theorem* find_some
- \+/\- *theorem* find_some

Modified src/tactic/lint.lean

Created test/lint_simp_var_head.lean



## [2020-02-24 18:12:09](https://github.com/leanprover-community/mathlib/commit/cb4bdd8)
doc(category_theory): add a few docstrings ([#2046](https://github.com/leanprover-community/mathlib/pull/2046))
* doc(category_theory): add a few docstrings
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/category_theory/core.lean

Modified src/category_theory/isomorphism.lean



## [2020-02-24 17:33:16+01:00](https://github.com/leanprover-community/mathlib/commit/8030469)
Revert "Update README.md"
This reverts commit 4d3ef8368051e45e1b20e77462b958be3e427c87.
#### Estimated changes
Modified README.md



## [2020-02-24 17:31:46+01:00](https://github.com/leanprover-community/mathlib/commit/4d3ef83)
Update README.md
#### Estimated changes
Modified README.md



## [2020-02-24 15:43:04](https://github.com/leanprover-community/mathlib/commit/0fc45dc)
feat(tactic/lint): support @[nolint unused_arguments] ([#2041](https://github.com/leanprover-community/mathlib/pull/2041))
* feat(tactic/lint): support @[nolint unused_arguments]
* refactor(scripts/mk_nolint): include failing linter name in nolints.txt
* chore(scripts/nolints): update nolints.txt
* doc(category/functor): add docstrings
#### Estimated changes
Modified docs/commands.md

Modified scripts/mk_all.sh

Modified scripts/mk_nolint.lean

Modified scripts/nolints.txt

Modified src/category/functor.lean
- \+/\- *def* const
- \+/\- *def* const

Modified src/category/monad/writer.lean

Modified src/category_theory/concrete_category/bundled_hom.lean

Modified src/meta/expr.lean

Modified src/meta/rb_map.lean

Modified src/number_theory/pell.lean

Modified src/order/filter/bases.lean

Modified src/order/filter/basic.lean
- \+/\- *lemma* mem_at_top_sets
- \+/\- *lemma* mem_at_top_sets

Modified src/order/lattice.lean

Modified src/ring_theory/algebra.lean
- \+/\- *def* comap
- \+/\- *def* comap

Modified src/ring_theory/localization.lean

Modified src/set_theory/ordinal.lean
- \+/\- *def* div_def
- \+/\- *def* ord_eq_min
- \+/\- *def* div_def
- \+/\- *def* ord_eq_min

Modified src/tactic/core.lean

Modified src/tactic/interactive.lean
- \+/\- *lemma* {u}
- \+/\- *lemma* {u}

Modified src/tactic/linarith.lean

Modified src/tactic/lint.lean

Modified src/topology/algebra/ordered.lean

Modified src/topology/metric_space/basic.lean

Modified src/topology/metric_space/emetric_space.lean

Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* index
- \+/\- *def* base
- \+/\- *def* fiber
- \+/\- *def* total_space
- \+/\- *def* index
- \+/\- *def* base
- \+/\- *def* fiber
- \+/\- *def* total_space

Modified src/topology/uniform_space/cauchy.lean

Modified test/lint.lean
- \+/\- *def* bar.foo
- \+/\- *def* bar.foo



## [2020-02-24 11:42:56](https://github.com/leanprover-community/mathlib/commit/32b32ad)
docs(data/set/basic): add module docstring ([#1991](https://github.com/leanprover-community/mathlib/pull/1991))
* adding module docstring
* tidying up
* markdown fixes
* more md tidying
* remove some unnecessary {alpha : Type*}
* responding to comments
* responding to comments
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* sep_set_of
- \+/\- *lemma* exists_of_ssubset
- \+/\- *lemma* univ_eq_empty_iff
- \+/\- *lemma* empty_diff
- \+/\- *lemma* sep_set_of
- \+/\- *lemma* exists_of_ssubset
- \+/\- *lemma* univ_eq_empty_iff
- \+/\- *lemma* empty_diff
- \+/\- *theorem* mem_of_mem_of_subset
- \+/\- *theorem* set_of_subset_set_of
- \+/\- *theorem* mem_of_eq_of_mem
- \+/\- *theorem* mem_image
- \+/\- *theorem* compl_image_set_of
- \+/\- *theorem* mem_of_mem_of_subset
- \+/\- *theorem* set_of_subset_set_of
- \+/\- *theorem* mem_of_eq_of_mem
- \+/\- *theorem* mem_image
- \+/\- *theorem* compl_image_set_of



## [2020-02-23 17:01:48](https://github.com/leanprover-community/mathlib/commit/28e4bdf)
feat(topology): an `is_complete` set is a `complete_space` ([#2037](https://github.com/leanprover-community/mathlib/pull/2037))
* feat(*): misc simple lemmas
* +1 lemma
* Rename `inclusion_range` to `range_inclusion`
Co-Authored-By: Johan Commelin <johan@commelin.net>
* feat(topology): an `is_complete` set is a `complete_space`
Also simplify a proof in `topology/metric_space/closeds`.
* Use in `finite_dimension`
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean

Modified src/topology/metric_space/closeds.lean

Modified src/topology/opens.lean
- \+/\- *def* nonempty_compacts.to_closeds
- \+/\- *def* nonempty_compacts.to_closeds

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* complete_space_iff_is_complete_univ

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_embedding_subtype_val
- \+ *lemma* uniform_embedding_subtype_coe
- \+ *lemma* uniform_embedding_set_inclusion
- \+ *lemma* is_complete_of_complete_image
- \+ *lemma* complete_space_iff_is_complete_range
- \+ *lemma* complete_space_congr
- \+ *lemma* complete_space_coe_iff_is_complete
- \+ *lemma* is_complete.complete_space_coe
- \+ *lemma* is_closed.complete_space_coe



## [2020-02-23 13:57:52](https://github.com/leanprover-community/mathlib/commit/16c1d9d)
chore(*): minimise imports of data.list.basic ([#2042](https://github.com/leanprover-community/mathlib/pull/2042))
#### Estimated changes
Modified src/algebra/group_power.lean

Modified src/category/fold.lean

Modified src/data/array/lemmas.lean

Modified src/data/int/basic.lean

Modified src/data/nat/prime.lean

Modified src/data/seq/wseq.lean

Modified src/group_theory/free_group.lean

Modified src/tactic/linarith.lean

Modified src/tactic/omega/coeffs.lean

Modified test/monotonicity.lean



## [2020-02-23 12:16:38](https://github.com/leanprover-community/mathlib/commit/256bedc)
chore(test): don't use sorry in tests, to reduce noise ([#2043](https://github.com/leanprover-community/mathlib/pull/2043))
#### Estimated changes
Modified test/apply.lean

Modified test/tactics.lean



## [2020-02-22 22:26:53](https://github.com/leanprover-community/mathlib/commit/bfa2465)
refactor(topology/metric_space/lipschitz): redefine for an `emetric_space` ([#2035](https://github.com/leanprover-community/mathlib/pull/2035))
* refactor(topology/metric_space/lipschitz): redefine for an `emetric_space`
* Fix compile
* Fixes, thanks @sgouzel
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean

Modified src/analysis/normed_space/finite_dimension.lean

Modified src/analysis/normed_space/operator_norm.lean

Modified src/data/real/ennreal.lean
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* mul_lt_of_lt_div

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/metric_space/closeds.lean

Modified src/topology/metric_space/contracting.lean
- \+ *lemma* dist_le
- \+/\- *def* contracting_with
- \+/\- *def* contracting_with

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/hausdorff_distance.lean

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_with_iff_dist_le
- \+ *lemma* edist_le
- \+/\- *lemma* ediam_image_le
- \+ *lemma* edist_iterate_succ_le_geometric
- \+ *lemma* nndist_le
- \+/\- *lemma* diam_image_le
- \+/\- *lemma* dist_iterate_succ_le_geometric
- \- *lemma* nndist_map_le
- \- *lemma* edist_map_le
- \+/\- *lemma* ediam_image_le
- \+/\- *lemma* diam_image_le
- \+/\- *lemma* dist_iterate_succ_le_geometric
- \+/\- *def* lipschitz_with
- \+/\- *def* lipschitz_with



## [2020-02-22 20:47:15](https://github.com/leanprover-community/mathlib/commit/ea149c8)
feat(algebraic_geometry/prime_spectrum): prime spectrum of a ring is compact ([#1987](https://github.com/leanprover-community/mathlib/pull/1987))
* wip
* wip
* wip
* wip
* WIP
* WIP
* Reset changes that belong to other PR
* Docstrings
* Add Heine--Borel to docstring
* Cantor's intersection theorem
* Cantor for sequences
* Revert "Reset changes that belong to other PR"
This reverts commit e6026b8819570ef6a763582a25d7ae5ad508134b.
* Move submodule lemmas to other file
* Fix build
* Update prime_spectrum.lean
* Docstring
* Update prime_spectrum.lean
* Slight improvement?
* Slightly improve structure of proof
* WIP
* Cleaning up proofs
* Final fixes
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean

Modified src/linear_algebra/basic.lean
- \+ *lemma* supr_eq_span
- \+ *lemma* span_singleton_le_iff_mem
- \+ *lemma* mem_supr

Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* linear_map.map_finsupp_total
- \+ *lemma* submodule.exists_finset_of_mem_supr
- \+/\- *lemma* linear_map.map_finsupp_total
- \+/\- *theorem* mem_span_iff_total
- \+/\- *theorem* mem_span_iff_total

Modified src/order/complete_lattice.lean
- \+ *lemma* le_supr_iff



## [2020-02-22 19:10:31](https://github.com/leanprover-community/mathlib/commit/d615ee6)
feat(ci): skip Azure upload if archive already exists ([#2039](https://github.com/leanprover-community/mathlib/pull/2039))
* skip upload if archive already exists
* simplify script
* remove unused variable
* fix
#### Estimated changes
Modified .github/workflows/build.yml



## [2020-02-22 16:24:24](https://github.com/leanprover-community/mathlib/commit/1c6a317)
feat(*): misc simple lemmas ([#2036](https://github.com/leanprover-community/mathlib/pull/2036))
* feat(*): misc simple lemmas
* +1 lemma
* Rename `inclusion_range` to `range_inclusion`
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nndist_smul

Modified src/data/set/basic.lean
- \+ *lemma* range_inclusion

Modified src/order/filter/basic.lean
- \+ *lemma* comap_ne_bot_of_image_mem

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* prod.edist_eq
- \+ *theorem* is_closed_ball_top



## [2020-02-22 13:59:03](https://github.com/leanprover-community/mathlib/commit/603c7ba)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-22 12:05:43](https://github.com/leanprover-community/mathlib/commit/eabcd13)
feat(category_theory/limits): kernels ([#1988](https://github.com/leanprover-community/mathlib/pull/1988))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fixes
* feat(category_theory/limits): kernels
* finishing basic API for kernels
* update post [#1412](https://github.com/leanprover-community/mathlib/pull/1412)
* fix
* documentation
* documentation
* more docs
* replacing dumb code
* forall -> Pi
* removing all instances
* working on Reid's suggested lemmas
* experiments
* lots to do
* Show that equalizers are monomorphisms
* Show that equalizer of (f, f) is always an iso
* Show that an equalizer that is an epimorphism is an isomorphism
* Clean up
* Show that the kernel of a monomorphism is zero
* Fix
* Show that the kernel of a linear map is a kernel in the categorical sense
* Modify proof
* Compactify proof
* Various cleanup
* Some more cleanup
* Fix bibtex
* Address some issues raised during discussion of the PR
* Fix some more incorrect indentation
* Some more minor fixes
* Unify capitalization in Bibtex entries
* Replace equalizer.lift.uniq with equalizer.hom_ext
* Some more slight refactors
* Typo
#### Estimated changes
Modified docs/references.bib

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* of_apply
- \+ *def* kernel_cone
- \+ *def* kernel_is_limit

Modified src/category_theory/limits/limits.lean

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* cone_parallel_pair_left
- \+ *lemma* cone_parallel_pair_right
- \+ *lemma* cone_parallel_pair_ext
- \+ *lemma* fork.eq_of_ι_ι
- \+ *lemma* equalizer.ι.fork
- \+ *lemma* equalizer.ι.eq_app_zero
- \+/\- *lemma* equalizer.condition
- \+ *lemma* equalizer.hom_ext
- \+ *lemma* equalizer.ι_mono
- \+ *lemma* cone_parallel_pair_self_π_app_zero
- \+ *lemma* cone_parallel_pair_self_X
- \+/\- *lemma* coequalizer.condition
- \+/\- *lemma* equalizer.condition
- \+/\- *lemma* coequalizer.condition
- \+ *def* cone_parallel_pair_self
- \+ *def* is_limit_cone_parallel_pair_self
- \+ *def* limit_cone_parallel_pair_self_is_iso
- \+ *def* epi_limit_cone_parallel_pair_is_iso

Created src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel.condition
- \+ *lemma* cokernel.condition
- \+ *def* kernel.ι_zero_is_iso
- \+ *def* kernel.zero_cone
- \+ *def* kernel.is_limit_cone_zero_cone

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* has_terminal_of_unique
- \+ *def* has_initial_of_unique

Created src/category_theory/limits/shapes/zero.lean
- \+ *lemma* zero_of_comp_mono
- \+ *lemma* zero_of_comp_epi
- \+ *lemma* zero_of_to_zero
- \+ *lemma* zero_of_from_zero
- \+ *def* zero_of_zero_object
- \+ *def* zero_morphisms_of_zero_object
- \+ *def* has_initial_of_has_zero_object
- \+ *def* has_terminal_of_has_zero_object



## [2020-02-22 11:14:19+01:00](https://github.com/leanprover-community/mathlib/commit/a9ed54c)
feat(ci): upload all branch builds to Azure server ([#2032](https://github.com/leanprover-community/mathlib/pull/2032))
#### Estimated changes
Modified .github/workflows/build.yml



## [2020-02-22 09:45:22](https://github.com/leanprover-community/mathlib/commit/928496a)
feat(category_theory/limits) Binary product from pullbacks and terminal object ([#1998](https://github.com/leanprover-community/mathlib/pull/1998))
* Binary product from pullbacks and terminal object
* Update binary_products.lean
* simplifications
* pare down the proof a bit more
* changes from review
* adjust simp to rw
#### Estimated changes
Modified src/category_theory/discrete_category.lean
- \+ *lemma* of_homs_app

Modified src/category_theory/equivalence.lean

Created src/category_theory/limits/shapes/constructions/binary_products.lean
- \+ *def* has_binary_products_of_terminal_and_pullbacks



## [2020-02-22 08:15:14](https://github.com/leanprover-community/mathlib/commit/03af46c)
chore(presheafed_space): avoid deterministic timeout ([#1617](https://github.com/leanprover-community/mathlib/pull/1617))
* chore(presheafed_space): avoid deterministic timeout
* fix proofs: now works with -T16000
* fix
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean

Modified src/algebraic_geometry/stalks.lean



## [2020-02-22 00:36:59](https://github.com/leanprover-community/mathlib/commit/11797e6)
chore(topology/metric_space/emetric_space): use filter bases in 2 proofs ([#2034](https://github.com/leanprover-community/mathlib/pull/2034))
#### Estimated changes
Modified src/topology/metric_space/emetric_space.lean



## [2020-02-21 22:47:11](https://github.com/leanprover-community/mathlib/commit/ffb6d6e)
feat(tactic): add various tactics about local definitions ([#1953](https://github.com/leanprover-community/mathlib/pull/1953))
* feat(tactic): add various tactics about local definitions
* remove {α β}
* rename generalize' in monotonicity.
* updates after reviews
#### Estimated changes
Modified src/data/option/defs.lean

Modified src/tactic/core.lean

Modified src/tactic/interactive.lean

Modified src/tactic/monotonicity/interactive.lean

Modified test/tactics.lean



## [2020-02-21 21:54:18+01:00](https://github.com/leanprover-community/mathlib/commit/86c9417)
doc(topology/dense_embedding): fix list syntax in a comment ([#2033](https://github.com/leanprover-community/mathlib/pull/2033))
#### Estimated changes
Modified src/topology/dense_embedding.lean



## [2020-02-21 19:29:22](https://github.com/leanprover-community/mathlib/commit/ff36e0f)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-21 17:46:31](https://github.com/leanprover-community/mathlib/commit/472156f)
feat(tactic/lint): check that left-hand side of all simp lemmas is in simp-normal form ([#2017](https://github.com/leanprover-community/mathlib/pull/2017))
* feat(tactic/lint): check that lhs of simp lemmas are in simp nf
* fix(topology/metric_space/basic): remove @[simp] from lemmas with {x,y} on the lhs
* chore(topology/local_homeomorph): remove redundant lemmas from the simp set
* fix(topology/algebra/module): fix simp-nf lints
* chore(ring_theory/localization): mark fewer things as simp
* fix(set_theory/ordinal): put lhs into simp-normal form
* chore(algebra/big_operators): fix simp lemmas
* chore(data/set/lattice): remove redundant simp lemmas
* chore(data/set/basic): remove redundant simp lemma
* chore(data/zsqrtd/basic): make simp_nf lint happy
* fix(order/complete_lattice): remove lemmas from simp set
* chore(order/filter/filter_product): fix linting issues
* feat(data/mv_polynomial): add simp lemmas about neg
* fix(data/multiset): fix simp_nf linter issues
* chore(data/list/sigma): fix simp_nf linter issues
* fix(data/list/basic): remove redundant and unapplicable simp lemmas
* fix(measure_theory/set_integral): remove redundant simp lemma
* fix(measure_theory/l1_space): remove redundant simp lemmas
* fix(algebra/group_power): remove simp lemmas that are not in nf
* fix(algebra/field): remove redundant simp lemma
* chore(data/list/alist): remove simp lemmas
* fix(data/int/basic): simp-normal form for coercions...
* fix(data/finset): formulate simp-lemmas for simp-nf
* fix(data/int/parity): use simp-normal form
* fix(data/equiv/denumerable): remove redundant simp lemma
* fix(category_theory/**): fix simp-normal forms
* fix(set_theory/zfc): put simp lemmas in simp-normal form
* fix(tactlic/lint): ignore sub_eq_add_neg for simp_nf lint
* doc(tactic/lint): add simp_nf linter to module doc
* doc(docs/commands): add simp_nf linter
* fix(*): put lemmas in simp-normal form
#### Estimated changes
Modified docs/commands.md

Modified scripts/mk_all.sh

Modified src/algebra/big_operators.lean
- \+/\- *lemma* sum_mul_boole
- \+/\- *lemma* sum_boole_mul
- \+/\- *lemma* sum_mul_boole
- \+/\- *lemma* sum_boole_mul

Modified src/algebra/field.lean
- \- *theorem* mk0_inv

Modified src/algebra/group_power.lean
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* one_div_pow

Modified src/algebra/ring.lean
- \+ *lemma* ite_mul

Modified src/algebraic_geometry/prime_spectrum.lean
- \+/\- *lemma* zero_locus_bot
- \+ *lemma* zero_locus_singleton_zero
- \+/\- *lemma* zero_locus_bot

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.apply_zero_curry0
- \+/\- *lemma* continuous_multilinear_map.uncurry0_curry0
- \+ *lemma* continuous_multilinear_map.fin0_apply_norm
- \+/\- *lemma* continuous_multilinear_map.curry0_norm
- \+/\- *lemma* continuous_multilinear_map.uncurry0_curry0
- \+/\- *lemma* continuous_multilinear_map.curry0_norm

Modified src/category_theory/const.lean
- \- *lemma* const_comp_hom_app
- \- *lemma* const_comp_inv_app
- \+/\- *def* const_comp
- \+/\- *def* const_comp

Modified src/category_theory/equivalence.lean
- \+/\- *lemma* functor_unit_comp
- \+/\- *lemma* functor_unit_comp

Modified src/category_theory/functor.lean

Modified src/category_theory/functor_category.lean
- \+ *lemma* vcomp_app'

Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* map_hom_inv
- \+/\- *lemma* map_inv_hom
- \+/\- *lemma* map_hom_inv
- \+/\- *lemma* map_inv_hom

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.cone_morphism_π
- \+/\- *lemma* colimit.ι_cocone_morphism
- \+/\- *lemma* limit.cone_morphism_π
- \+/\- *lemma* colimit.ι_cocone_morphism

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.symmetry'
- \+/\- *lemma* prod.symmetry
- \+ *lemma* coprod.symmetry'
- \+/\- *lemma* coprod.symmetry
- \+/\- *lemma* prod.symmetry
- \+/\- *lemma* coprod.symmetry

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* cospan_map_id
- \+/\- *lemma* span_map_id
- \+/\- *lemma* cospan_map_id
- \+/\- *lemma* span_map_id

Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* naturality_1
- \+/\- *lemma* naturality_2
- \+/\- *lemma* naturality_1
- \+/\- *lemma* naturality_2

Modified src/category_theory/natural_transformation.lean
- \+/\- *lemma* vcomp_app
- \+/\- *lemma* vcomp_app

Modified src/data/equiv/denumerable.lean
- \+/\- *theorem* decode_is_some
- \+/\- *theorem* decode_is_some

Modified src/data/fin.lean

Modified src/data/finset.lean
- \+ *lemma* sup_singleton'
- \+/\- *lemma* sup_singleton
- \+ *lemma* inf_singleton'
- \+/\- *lemma* inf_singleton
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* inf_singleton
- \+/\- *theorem* insert_singleton_self_eq
- \+ *theorem* insert_singleton_self_eq'
- \+/\- *theorem* max_singleton
- \+/\- *theorem* min_singleton
- \+ *theorem* min_singleton'
- \+/\- *theorem* supr_union
- \+/\- *theorem* insert_singleton_self_eq
- \+/\- *theorem* max_singleton
- \+/\- *theorem* min_singleton
- \+/\- *theorem* supr_union

Modified src/data/int/basic.lean
- \+/\- *theorem* cast_of_nat
- \+/\- *theorem* cast_coe_nat'
- \+/\- *theorem* cast_of_nat
- \+/\- *theorem* cast_coe_nat'

Modified src/data/int/parity.lean
- \+/\- *theorem* mod_two_ne_zero
- \+ *theorem* two_dvd_ne_zero
- \+/\- *theorem* mod_two_ne_zero

Modified src/data/list/alist.lean
- \+/\- *theorem* insert_insert_of_ne
- \+/\- *theorem* insert_insert_of_ne

Modified src/data/list/basic.lean
- \+/\- *theorem* exists_mem_cons_iff
- \+/\- *theorem* concat_nil
- \+/\- *theorem* concat_cons
- \+/\- *theorem* concat_ne_nil
- \+/\- *theorem* concat_append
- \+/\- *theorem* length_concat
- \+/\- *theorem* count_concat
- \+/\- *theorem* infix_append
- \+ *theorem* infix_append'
- \+/\- *theorem* prefix_concat
- \+/\- *theorem* exists_mem_cons_iff
- \+/\- *theorem* concat_nil
- \+/\- *theorem* concat_cons
- \+/\- *theorem* concat_ne_nil
- \+/\- *theorem* concat_append
- \+/\- *theorem* length_concat
- \+/\- *theorem* count_concat
- \+/\- *theorem* infix_append
- \+/\- *theorem* prefix_concat

Modified src/data/list/sigma.lean
- \+/\- *theorem* mem_keys_kinsert
- \+/\- *theorem* lookup_kinsert
- \+/\- *theorem* lookup_kinsert_ne
- \+/\- *theorem* mem_keys_kinsert
- \+/\- *theorem* lookup_kinsert
- \+/\- *theorem* lookup_kinsert_ne

Modified src/data/multiset.lean
- \+/\- *lemma* map_singleton
- \+/\- *lemma* prod_map_one
- \+/\- *lemma* sum_map_zero
- \+/\- *lemma* map_singleton
- \+/\- *lemma* prod_map_one
- \+/\- *lemma* sum_map_zero

Modified src/data/mv_polynomial.lean
- \+ *lemma* coeff_neg
- \+ *lemma* rename_neg

Modified src/data/option/basic.lean
- \+ *lemma* lift_or_get_none_left
- \+ *lemma* lift_or_get_none_right
- \+ *lemma* lift_or_get_some_some

Modified src/data/set/basic.lean
- \+/\- *theorem* nmem_set_of_eq
- \+/\- *theorem* subset_preimage_univ
- \+/\- *theorem* nmem_set_of_eq
- \+/\- *theorem* subset_preimage_univ

Modified src/data/set/lattice.lean
- \+/\- *theorem* bInter_empty
- \+/\- *theorem* bInter_univ
- \+/\- *theorem* bUnion_empty
- \+/\- *theorem* bUnion_univ
- \+/\- *theorem* bInter_empty
- \+/\- *theorem* bInter_univ
- \+/\- *theorem* bUnion_empty
- \+/\- *theorem* bUnion_univ

Modified src/data/zsqrtd/basic.lean

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* lintegral_nnnorm_zero
- \+/\- *lemma* lintegral_nnnorm_zero

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_on_zero
- \+/\- *lemma* integral_on_zero

Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_emptyset
- \+/\- *theorem* supr_emptyset
- \+/\- *theorem* infi_univ
- \+/\- *theorem* supr_univ
- \+/\- *theorem* infi_union
- \+/\- *theorem* supr_union
- \+/\- *theorem* infi_insert
- \+/\- *theorem* supr_insert
- \+/\- *theorem* infi_singleton
- \+/\- *theorem* infi_pair
- \+/\- *theorem* supr_singleton
- \+/\- *theorem* supr_pair
- \+/\- *theorem* infi_emptyset
- \+/\- *theorem* supr_emptyset
- \+/\- *theorem* infi_univ
- \+/\- *theorem* supr_univ
- \+/\- *theorem* infi_union
- \+/\- *theorem* supr_union
- \+/\- *theorem* infi_insert
- \+/\- *theorem* supr_insert
- \+/\- *theorem* infi_singleton
- \+/\- *theorem* infi_pair
- \+/\- *theorem* supr_singleton
- \+/\- *theorem* supr_pair

Modified src/order/filter/filter_product.lean
- \+/\- *lemma* of_seq_zero
- \+/\- *lemma* of_seq_one
- \+/\- *lemma* abs_def
- \+/\- *lemma* of_seq_zero
- \+/\- *lemma* of_seq_one
- \+/\- *lemma* abs_def

Modified src/ring_theory/localization.lean
- \+/\- *lemma* to_units_coe
- \+/\- *lemma* coe_is_unit
- \+/\- *lemma* coe_is_unit'
- \+/\- *lemma* coe_mul_mk
- \+/\- *lemma* mk_mul_mk
- \+/\- *lemma* lift'_mk
- \+/\- *lemma* to_units_coe
- \+/\- *lemma* coe_is_unit
- \+/\- *lemma* coe_is_unit'
- \+/\- *lemma* coe_mul_mk
- \+/\- *lemma* mk_mul_mk
- \+/\- *lemma* lift'_mk

Modified src/ring_theory/power_series.lean

Modified src/set_theory/ordinal.lean

Modified src/set_theory/zfc.lean
- \+ *lemma* eval_mk
- \+/\- *theorem* eval_val
- \+/\- *theorem* eval_val

Modified src/tactic/core.lean

Modified src/tactic/lint.lean
- \- *lemma* +

Modified src/topology/algebra/module.lean
- \+/\- *lemma* symm_comp_self
- \+/\- *lemma* self_comp_symm
- \+ *lemma* symm_comp_self'
- \+ *lemma* self_comp_symm'
- \+/\- *lemma* symm_comp_self
- \+/\- *lemma* self_comp_symm

Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* symm_to_fun
- \+/\- *lemma* symm_inv_fun
- \+/\- *lemma* symm_source
- \+/\- *lemma* symm_target
- \+/\- *lemma* restr_open_source
- \+/\- *lemma* restr_to_fun
- \+/\- *lemma* restr_inv_fun
- \+/\- *lemma* restr_source
- \+/\- *lemma* restr_target
- \+/\- *lemma* refl_source
- \+/\- *lemma* refl_target
- \+/\- *lemma* refl_symm
- \+/\- *lemma* refl_to_fun
- \+/\- *lemma* refl_inv_fun
- \+/\- *lemma* of_set_source
- \+/\- *lemma* of_set_target
- \+/\- *lemma* of_set_to_fun
- \+/\- *lemma* of_set_inv_fun
- \+/\- *lemma* of_set_symm
- \+/\- *lemma* trans_to_fun
- \+/\- *lemma* trans_inv_fun
- \+/\- *lemma* prod_source
- \+/\- *lemma* prod_target
- \+/\- *lemma* prod_to_fun
- \+/\- *lemma* prod_inv_fun
- \+/\- *lemma* symm_to_fun
- \+/\- *lemma* symm_inv_fun
- \+/\- *lemma* symm_source
- \+/\- *lemma* symm_target
- \+/\- *lemma* restr_open_source
- \+/\- *lemma* restr_to_fun
- \+/\- *lemma* restr_inv_fun
- \+/\- *lemma* restr_source
- \+/\- *lemma* restr_target
- \+/\- *lemma* refl_source
- \+/\- *lemma* refl_target
- \+/\- *lemma* refl_symm
- \+/\- *lemma* refl_to_fun
- \+/\- *lemma* refl_inv_fun
- \+/\- *lemma* of_set_source
- \+/\- *lemma* of_set_target
- \+/\- *lemma* of_set_to_fun
- \+/\- *lemma* of_set_inv_fun
- \+/\- *lemma* of_set_symm
- \+/\- *lemma* trans_to_fun
- \+/\- *lemma* trans_inv_fun
- \+/\- *lemma* prod_source
- \+/\- *lemma* prod_target
- \+/\- *lemma* prod_to_fun
- \+/\- *lemma* prod_inv_fun

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* diam_pair
- \+/\- *lemma* diam_triple
- \+/\- *lemma* diam_pair
- \+/\- *lemma* diam_triple

Created test/lint_simp_nf.lean
- \+ *lemma* c_eq_d
- \+ *lemma* f_c
- \+ *lemma* h_c
- \+ *def* f
- \+ *def* c
- \+ *def* d
- \+ *def* h



## [2020-02-21 11:26:12](https://github.com/leanprover-community/mathlib/commit/bb7631f)
feat(algebraic_geometry/prime_spectrum): vanishing ideal ([#1972](https://github.com/leanprover-community/mathlib/pull/1972))
* wip
* wip
* Remove stuff for next PR
* Update prime_spectrum.lean
* Process comments
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+/\- *lemma* zero_locus_span
- \+ *lemma* coe_vanishing_ideal
- \+ *lemma* mem_vanishing_ideal
- \+ *lemma* subset_zero_locus_iff_le_vanishing_ideal
- \+ *lemma* gc
- \+ *lemma* gc_set
- \+ *lemma* subset_zero_locus_iff_subset_vanishing_ideal
- \+ *lemma* subset_vanishing_ideal_zero_locus
- \+ *lemma* le_vanishing_ideal_zero_locus
- \+ *lemma* subset_zero_locus_vanishing_ideal
- \+ *lemma* zero_locus_bot
- \+ *lemma* zero_locus_empty
- \+ *lemma* vanishing_ideal_univ
- \+ *lemma* zero_locus_empty_iff_eq_top
- \+ *lemma* zero_locus_sup
- \+ *lemma* zero_locus_union
- \+ *lemma* vanishing_ideal_union
- \+ *lemma* zero_locus_supr
- \+/\- *lemma* zero_locus_Union
- \+ *lemma* vanishing_ideal_Union
- \+ *lemma* zero_locus_inf
- \+/\- *lemma* union_zero_locus
- \+ *lemma* sup_vanishing_ideal_le
- \+ *lemma* is_closed_zero_locus
- \+ *lemma* zero_locus_vanishing_ideal_eq_closure
- \+/\- *lemma* zero_locus_span
- \- *lemma* union_zero_locus_ideal
- \+/\- *lemma* union_zero_locus
- \+/\- *lemma* zero_locus_Union
- \- *lemma* Inter_zero_locus
- \- *lemma* zero_locus_is_closed
- \+ *def* vanishing_ideal



## [2020-02-21 05:36:39](https://github.com/leanprover-community/mathlib/commit/b30b5e9)
feat(tactic/hint): update tactic list ([#2024](https://github.com/leanprover-community/mathlib/pull/2024))
* feat(tactic/hint): update tactic list
* Removing `fsplit` in favour of `fconstructor`.
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fix test
* silence a test
#### Estimated changes
Modified src/tactic/hint.lean

Modified src/tactic/norm_cast.lean

Modified test/hint.lean

Modified test/tidy.lean



## [2020-02-21 02:50:57](https://github.com/leanprover-community/mathlib/commit/888e75b)
refactor(*/multilinear): better right curryfication ([#1985](https://github.com/leanprover-community/mathlib/pull/1985))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* feat(*/multilinear): better multilinear
* docstrings
* snoc
* fix build
* comp_snoc and friends
* fix docstring
* typo
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_linear_map.norm_map_tail_le
- \+ *lemma* continuous_multilinear_map.norm_map_init_le
- \+ *lemma* continuous_multilinear_map.norm_map_snoc_le
- \+ *lemma* continuous_multilinear_curry_left_equiv_apply
- \+ *lemma* continuous_multilinear_curry_left_equiv_symm_apply
- \+ *lemma* continuous_multilinear_curry_right_equiv_apply
- \+ *lemma* continuous_multilinear_curry_right_equiv_symm_apply
- \+ *lemma* continuous_multilinear_map.uncurry0_apply
- \+ *lemma* continuous_multilinear_curry_fin0_apply
- \+ *lemma* continuous_multilinear_curry_fin0_symm_apply
- \+ *lemma* continuous_multilinear_curry_fin1_apply
- \+ *lemma* continuous_multilinear_curry_fin1_symm_apply
- \- *lemma* continuous_linear_map.norm_map_tail_right_le
- \- *lemma* continuous_multilinear_map.norm_map_tail_left_le
- \+ *def* continuous_multilinear_curry_fin1

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* snoc_add
- \+ *lemma* snoc_smul
- \+ *def* prod
- \+ *def* comp_linear_map
- \+ *def* comp_multilinear_map
- \+/\- *def* multilinear_map.uncurry_right
- \+/\- *def* multilinear_map.uncurry_right

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* prod_apply
- \+ *lemma* comp_continuous_multilinear_map_coe
- \+ *def* prod
- \+ *def* comp_continuous_linear_map
- \+ *def* comp_continuous_multilinear_map



## [2020-02-20 15:52:23-08:00](https://github.com/leanprover-community/mathlib/commit/eeedc6a)
fix(*): remove loopy simp lemmas ([#2026](https://github.com/leanprover-community/mathlib/pull/2026))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* conj_comp
- \+/\- *lemma* conj_comp

Modified src/order/basic.lean
- \+/\- *lemma* dual_le
- \+/\- *lemma* dual_lt
- \+/\- *lemma* dual_le
- \+/\- *lemma* dual_lt



## [2020-02-20 21:25:20](https://github.com/leanprover-community/mathlib/commit/b0eeea4)
fix(data/bool): remove simp attribute from commutativity lemmas ([#2027](https://github.com/leanprover-community/mathlib/pull/2027))
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *theorem* bor_comm
- \+/\- *theorem* bor_left_comm
- \+/\- *theorem* band_comm
- \+/\- *theorem* band_left_comm
- \+/\- *theorem* bxor_comm
- \+/\- *theorem* bxor_left_comm
- \+/\- *theorem* bor_comm
- \+/\- *theorem* bor_left_comm
- \+/\- *theorem* band_comm
- \+/\- *theorem* band_left_comm
- \+/\- *theorem* bxor_comm
- \+/\- *theorem* bxor_left_comm

Modified src/data/int/basic.lean
- \+ *lemma* bodd_coe



## [2020-02-20 16:55:22](https://github.com/leanprover-community/mathlib/commit/aefdb86)
feat(data/int/basic): format -42 as -42 instead of -(41+1) ([#2025](https://github.com/leanprover-community/mathlib/pull/2025))
#### Estimated changes
Modified src/data/int/basic.lean



## [2020-02-20 15:24:23](https://github.com/leanprover-community/mathlib/commit/d933ea5)
doc(lint): add linter missing from list of defaults ([#2023](https://github.com/leanprover-community/mathlib/pull/2023))
#### Estimated changes
Modified docs/commands.md

Modified src/tactic/lint.lean



## [2020-02-20 14:50:00+01:00](https://github.com/leanprover-community/mathlib/commit/43dd938)
chore(ci): check roadmap directory ([#2022](https://github.com/leanprover-community/mathlib/pull/2022))
* chore(ci): check roadmap directory
partially addresses [#2016](https://github.com/leanprover-community/mathlib/pull/2016)
* fix roadmap compilation
#### Estimated changes
Modified .github/workflows/build.yml

Modified roadmap/topology/paracompact.lean

Modified roadmap/topology/shrinking_lemma.lean



## [2020-02-20 11:06:30](https://github.com/leanprover-community/mathlib/commit/4e398cc)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-20 09:21:34](https://github.com/leanprover-community/mathlib/commit/68b9c16)
feat(algebra/group): add `units.lift_right` and `is_unit.lift_right` ([#2020](https://github.com/leanprover-community/mathlib/pull/2020))
* Rename type variables, add a docstring
* feat(algebra/group): add `units.lift_right` and `is_unit.lift_right`
These defs/lemmas may be useful for `monoid_localization`.
#### Estimated changes
Modified src/algebra/group/is_unit.lean
- \+ *lemma* is_unit.coe_lift_right

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* coe_map
- \+/\- *lemma* coe_map'
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+ *lemma* coe_lift_right
- \+/\- *lemma* coe_map
- \+/\- *lemma* coe_map'
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+/\- *def* map
- \+/\- *def* map'
- \+/\- *def* coe_hom
- \+ *def* lift_right
- \+/\- *def* map
- \+/\- *def* map'
- \+/\- *def* coe_hom



## [2020-02-20 02:23:59](https://github.com/leanprover-community/mathlib/commit/d42d29b)
fix(tactic/tauto): fix typos ([#2019](https://github.com/leanprover-community/mathlib/pull/2019))
* fix(tactic/tauto): fix typos
* fix same error in tactics.md
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/tauto.lean



## [2020-02-20 00:52:33](https://github.com/leanprover-community/mathlib/commit/34724f4)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-19 23:20:36](https://github.com/leanprover-community/mathlib/commit/2d6556d)
feat(analysis/mean_inequalities) : Prove AM-GM ([#1836](https://github.com/leanprover-community/mathlib/pull/1836))
* feat(analysis/mean_inequalities) : Prove AM-GM
* Update, add more inequalities
* Update src/analysis/convex/specific_functions.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/mean_inequalities.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/mean_inequalities.lean
* Small fixes, thanks @sgouezel
* Update src/analysis/mean_inequalities.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* iter_deriv_pow'
- \+ *lemma* iter_deriv_pow
- \+ *lemma* has_deriv_at_fpow
- \+ *lemma* differentiable_at_fpow
- \+ *lemma* differentiable_within_at_fpow
- \+ *lemma* differentiable_on_fpow
- \+ *lemma* deriv_fpow
- \+ *lemma* deriv_within_fpow
- \+ *lemma* iter_deriv_fpow
- \+ *theorem* has_deriv_within_at_fpow

Created src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_exp
- \+ *lemma* convex_on_pow_of_even
- \+ *lemma* convex_on_pow
- \+ *lemma* finset.prod_nonneg_of_card_nonpos_even
- \+ *lemma* int_prod_range_nonneg
- \+ *lemma* convex_on_fpow

Created src/analysis/mean_inequalities.lean
- \+ *theorem* real.am_gm_weighted
- \+ *theorem* nnreal.am_gm_weighted
- \+ *theorem* nnreal.am_gm2_weighted
- \+ *theorem* real.am_gm2_weighted
- \+ *theorem* nnreal.am_gm3_weighted
- \+ *theorem* nnreal.young_inequality
- \+ *theorem* real.young_inequality
- \+ *theorem* real.pow_am_le_am_pow
- \+ *theorem* nnreal.pow_am_le_am_pow
- \+ *theorem* real.pow_am_le_am_pow_of_even
- \+ *theorem* real.fpow_am_le_am_fpow

Modified src/data/nat/parity.lean
- \+ *theorem* even.add
- \+ *theorem* even.sub

Modified src/data/real/nnreal.lean
- \+ *theorem* coe_mk

Modified src/data/set/intervals/basic.lean
- \+ *lemma* compl_Iic
- \+ *lemma* compl_Ici
- \+ *lemma* compl_Iio
- \+ *lemma* compl_Ioi

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* is_open_Iio
- \+/\- *lemma* is_open_Ioi
- \+/\- *lemma* is_open_Ioo
- \+ *lemma* interior_Ioi
- \+ *lemma* interior_Iio
- \+ *lemma* interior_Ioo
- \+ *lemma* interior_Ici
- \+ *lemma* interior_Iic
- \+ *lemma* interior_Icc
- \+ *lemma* interior_Ico
- \+ *lemma* interior_Ioc
- \+/\- *lemma* is_open_Iio
- \+/\- *lemma* is_open_Ioi
- \+/\- *lemma* is_open_Ioo



## [2020-02-19 21:46:28](https://github.com/leanprover-community/mathlib/commit/5b77b64)
refactor(analysis/calculus/tangent_cone): split a proof into parts ([#2013](https://github.com/leanprover-community/mathlib/pull/2013))
* refactor(analysis/calculus/tangent_cone): split a proof into parts
Prove `submodule.eq_top_of_nonempty_interior` and use it in the
proof of `unique_diff_on_convex`.
* Update src/analysis/normed_space/basic.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix a docstring.
* Update src/topology/algebra/module.lean
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* is_unit_iff_ne_zero

Modified src/algebra/module.lean
- \+ *lemma* smul_mem_iff'

Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* punctured_nhds_ne_bot
- \+ *lemma* submodule.eq_top_of_nonempty_interior

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.eq_top_of_nonempty_interior'



## [2020-02-19 12:42:42](https://github.com/leanprover-community/mathlib/commit/bcdb4c3)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-19 11:05:33](https://github.com/leanprover-community/mathlib/commit/8563695)
refactor(algebra/associated): move `is_unit` def to `algebra/group` ([#2015](https://github.com/leanprover-community/mathlib/pull/2015))
* refactor(algebra/associated): move `is_unit` def to `algebra/group`
I think it makes sense to have it near `units`.
* Add a docstring to `units`, mention `is_unit` there.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* is_unit_unit
- \- *lemma* is_unit.map
- \- *lemma* is_unit.map'
- \- *theorem* is_unit_one
- \- *theorem* is_unit_of_mul_one
- \- *theorem* is_unit_iff_exists_inv
- \- *theorem* is_unit_iff_exists_inv'
- \- *theorem* units.is_unit_mul_units
- \- *theorem* is_unit_of_mul_is_unit_left
- \- *theorem* is_unit_of_mul_is_unit_right
- \- *theorem* is_unit_nat
- \- *def* is_unit

Modified src/algebra/group/default.lean

Created src/algebra/group/is_unit.lean
- \+ *lemma* is_unit_unit
- \+ *lemma* is_unit.map
- \+ *lemma* is_unit.map'
- \+ *theorem* is_unit_one
- \+ *theorem* is_unit_of_mul_one
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* units.is_unit_mul_units
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* is_unit_nat
- \+ *def* is_unit

Modified src/algebra/group/units.lean



## [2020-02-19 08:48:40](https://github.com/leanprover-community/mathlib/commit/177c06f)
chore(measure_theory/*): make a few proofs slightly shorter ([#2014](https://github.com/leanprover-community/mathlib/pull/2014))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean

Modified src/measure_theory/l1_space.lean

Modified src/measure_theory/simple_func_dense.lean



## [2020-02-18 23:13:13](https://github.com/leanprover-community/mathlib/commit/8700aa7)
feat(docs): install mathlibtools package with pip ([#2010](https://github.com/leanprover-community/mathlib/pull/2010))
#### Estimated changes
Modified docs/contribute/index.md

Modified docs/install/debian_details.md

Modified docs/install/linux.md

Modified docs/install/macos.md

Modified docs/install/windows.md



## [2020-02-18 20:06:18](https://github.com/leanprover-community/mathlib/commit/2198d2c)
feat(roadmap): add some formal roadmaps in topology ([#1914](https://github.com/leanprover-community/mathlib/pull/1914))
* feat(roadmap): add some formal roadmaps in topology
* Update roadmap/topology/paracompact.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update roadmap/todo.lean
* Update roadmap/topology/shrinking_lemma.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* add `todo` tactic as a wrapper for `exact todo`
* Update roadmap/topology/shrinking_lemma.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* copyright notices and module docs
* oops
#### Estimated changes
Created roadmap/todo.lean

Created roadmap/topology/paracompact.lean
- \+ *lemma* paracompact_space.precise_refinement
- \+ *lemma* paracompact_of_compact
- \+ *lemma* normal_of_paracompact_t2
- \+ *lemma* paracompact_of_metric

Created roadmap/topology/shrinking_lemma.lean
- \+ *lemma* shrinking_lemma



## [2020-02-18 17:07:17](https://github.com/leanprover-community/mathlib/commit/0c2dbd5)
chore(analysis/normed_space/basic): implicit args ([#2011](https://github.com/leanprover-community/mathlib/pull/2011))
Arguments to these `iff`s should be implicit.
#### Estimated changes
Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/deriv.lean

Modified src/analysis/calculus/fderiv.lean

Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/normed_space/banach.lean

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* nnnorm_eq_zero

Modified src/analysis/normed_space/multilinear.lean

Modified src/analysis/normed_space/operator_norm.lean

Modified src/analysis/specific_limits.lean

Modified src/data/padics/hensel.lean

Modified src/data/padics/padic_numbers.lean

Modified src/measure_theory/simple_func_dense.lean

Modified src/topology/metric_space/cau_seq_filter.lean



## [2020-02-18 14:56:44](https://github.com/leanprover-community/mathlib/commit/8a660ec)
feat(scripts/deploy_nightly): change pre-release to release ([#2009](https://github.com/leanprover-community/mathlib/pull/2009))
The `--pre-release` doesn't really achieve anything as far as we can tell, and complicates some scripting: see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20nightlies
#### Estimated changes
Modified scripts/deploy_nightly.sh



## [2020-02-18 12:09:47](https://github.com/leanprover-community/mathlib/commit/115e513)
chore(topology/constructions): rename `tendsto_prod_mk_nhds` ([#2008](https://github.com/leanprover-community/mathlib/pull/2008))
New name is `tendsto.prod_mk_nhds`. Also use it in a few proofs and
generalize `tendsto_smul` to a `topological_semimodule`.
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/normed_space/basic.lean
- \- *lemma* tendsto_smul
- \- *lemma* tendsto_smul_const

Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous.smul
- \+ *lemma* tendsto_smul
- \+ *lemma* filter.tendsto.smul
- \+/\- *lemma* continuous.smul

Modified src/topology/algebra/monoid.lean

Modified src/topology/constructions.lean
- \+ *lemma* filter.tendsto.prod_mk_nhds
- \- *lemma* tendsto_prod_mk_nhds

Modified src/topology/continuous_on.lean

Modified src/topology/instances/ennreal.lean



## [2020-02-18 09:33:08](https://github.com/leanprover-community/mathlib/commit/1435a19)
refactor(topology/maps): split the proof of `is_open_map_iff_nhds_le` ([#2007](https://github.com/leanprover-community/mathlib/pull/2007))
Extract a lemma `is_open_map.image_mem_nhds` from the proof, and make
the proof use this lemma.
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* image_mem_nhds
- \+/\- *lemma* is_open_map_iff_nhds_le
- \+/\- *lemma* is_open_map_iff_nhds_le
- \+/\- *def* is_open_map
- \+/\- *def* is_open_map



## [2020-02-18 02:10:56](https://github.com/leanprover-community/mathlib/commit/2d00f20)
feat(data/fin): init and snoc ([#1978](https://github.com/leanprover-community/mathlib/pull/1978))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* change append to snoc
* comp_snoc and friends
* markdown in docstrings
* fix docstring
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* succ_last
- \+ *lemma* eq_last_of_not_lt
- \+ *lemma* cast_succ_fin_succ
- \+ *lemma* comp_cons
- \+ *lemma* comp_tail
- \+ *lemma* init_snoc
- \+ *lemma* snoc_cast_succ
- \+ *lemma* snoc_last
- \+ *lemma* snoc_update
- \+ *lemma* update_snoc_last
- \+ *lemma* snoc_init_self
- \+ *lemma* init_update_last
- \+ *lemma* init_update_cast_succ
- \+ *lemma* tail_init_eq_init_tail
- \+ *lemma* cons_snoc_eq_snoc_cons
- \+ *lemma* comp_snoc
- \+ *lemma* comp_init
- \+ *def* init
- \+ *def* snoc

Modified src/data/fintype.lean
- \+ *lemma* fin.univ_cast_succ
- \+ *theorem* fin.prod_univ_cast_succ
- \+ *theorem* fin.sum_univ_cast_succ

Modified src/logic/function.lean
- \+ *lemma* comp_update



## [2020-02-18 00:40:07](https://github.com/leanprover-community/mathlib/commit/b373dae)
feat(linear_algebra/contraction): define contraction maps between a module and its dual ([#1973](https://github.com/leanprover-community/mathlib/pull/1973))
* feat(linear_algebra/contraction): define contraction maps between a module and its dual
* Implicit carrier types for smul_comm
* Add comment with license and file description
* Build on top of extant linear_map.smul_right
* Feedback from code review
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+ *lemma* smul_comm

Modified src/linear_algebra/basic.lean
- \+ *lemma* smul_rightₗ_apply
- \+ *def* smul_rightₗ

Created src/linear_algebra/contraction.lean
- \+ *lemma* contract_left_apply
- \+ *lemma* contract_right_apply
- \+ *lemma* dual_tensor_hom_apply
- \+ *def* contract_left
- \+ *def* contract_right
- \+ *def* dual_tensor_hom



## [2020-02-17 23:10:41](https://github.com/leanprover-community/mathlib/commit/4299a80)
refactor(topology/subset_properties): use finite subcovers indexed by types ([#1980](https://github.com/leanprover-community/mathlib/pull/1980))
* wip
* wip
* wip
* wip
* WIP
* WIP
* Reset changes that belong to other PR
* Docstrings
* Add Heine--Borel to docstring
* Cantor's intersection theorem
* Cantor for sequences
* Generalise Cantor intersection thm
* More fixes
#### Estimated changes
Modified src/topology/metric_space/basic.lean

Modified src/topology/subset_properties.lean
- \+/\- *lemma* compact.elim_finite_subcover
- \+ *lemma* compact.elim_finite_subfamily_closed
- \+ *lemma* compact.nonempty_Inter_of_directed_nonempty_compact_closed
- \+ *lemma* compact.nonempty_Inter_of_sequence_nonempty_compact_closed
- \+/\- *lemma* compact_of_finite_subcover
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* compact.elim_finite_subcover
- \+/\- *lemma* compact_of_finite_subcover
- \+/\- *lemma* set.finite.compact_bUnion
- \+ *theorem* compact_of_finite_subfamily_closed
- \+ *theorem* compact_iff_finite_subfamily_closed
- \+ *theorem* compact_space_of_finite_subfamily_closed



## [2020-02-17 21:45:03](https://github.com/leanprover-community/mathlib/commit/bbf5d1a)
refactor(algebra/field): partially migrate to bundled homs ([#1999](https://github.com/leanprover-community/mathlib/pull/1999))
* refactor(algebra/field): partially migrate to bundled homs
* Add a few `@[simp]` attrs
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* map_ne_zero
- \+ *lemma* map_eq_zero
- \+ *lemma* map_inv'
- \+ *lemma* map_div'
- \+ *lemma* injective
- \+ *lemma* map_inv
- \+ *lemma* map_div

Modified src/algebra/field_power.lean
- \+ *lemma* ring_hom.map_fpow
- \+ *lemma* ring_hom.map_fpow'
- \+/\- *lemma* map_fpow
- \+/\- *lemma* map_fpow'
- \+/\- *lemma* map_fpow
- \+/\- *lemma* map_fpow'

Modified src/field_theory/subfield.lean



## [2020-02-17 20:10:20](https://github.com/leanprover-community/mathlib/commit/6cdd96b)
chore(*): reduce proof size ([#2006](https://github.com/leanprover-community/mathlib/pull/2006))
#### Estimated changes
Modified src/data/dfinsupp.lean

Modified src/measure_theory/ae_eq_fun.lean



## [2020-02-17 18:37:15](https://github.com/leanprover-community/mathlib/commit/5eefae2)
chore(set_theory/ordinal): shorten proofs ([#2005](https://github.com/leanprover-community/mathlib/pull/2005))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+/\- *theorem* initial_seg.lt_or_eq_apply_left
- \+/\- *theorem* initial_seg.lt_or_eq_apply_right
- \+/\- *theorem* initial_seg.lt_or_eq_apply_left
- \+/\- *theorem* initial_seg.lt_or_eq_apply_right



## [2020-02-17 17:00:24](https://github.com/leanprover-community/mathlib/commit/5f06692)
feat(data/set/intervals): add `Ici_subset_Ici`, `Iic_subset_Iic` ([#2003](https://github.com/leanprover-community/mathlib/pull/2003))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ici_subset_Ici
- \+ *lemma* Iic_subset_Iic



## [2020-02-17 13:55:11](https://github.com/leanprover-community/mathlib/commit/f8d0931)
feat(tactic/rename_var): A teaching tactic ([#1974](https://github.com/leanprover-community/mathlib/pull/1974))
* feat(tactic/rename_var): A teaching tactic
The goal is to teach that bound variables names are irrelevant, and also
help clarify local context.
* allow rename_var to act on several locations at once
* Apply suggestions from code review
by Rob.
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/basic.lean

Created src/tactic/rename_var.lean

Created test/rename_var.lean



## [2020-02-17 12:19:30](https://github.com/leanprover-community/mathlib/commit/cd0e2f6)
add "Try this: " to squeeze_simp and suggest ([#1990](https://github.com/leanprover-community/mathlib/pull/1990))
* add "Try this" to squeeze_simp and suggest
* update docs
* fix suggest tests
* add "try this" to rcases, rintro, and tidy
* add "try this" to hint
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/hint.lean

Modified src/tactic/rcases.lean

Modified src/tactic/squeeze.lean

Modified src/tactic/suggest.lean

Modified src/tactic/tidy.lean

Modified test/suggest.lean

Modified test/tidy.lean



## [2020-02-17 10:45:46](https://github.com/leanprover-community/mathlib/commit/557b01d)
chore(analysis/calculus/tangent_cone): simplify a proof ([#2002](https://github.com/leanprover-community/mathlib/pull/2002))
Use `linear_map.span_inl_union_inr` instead of repeating its proof.
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean



## [2020-02-17 09:07:47](https://github.com/leanprover-community/mathlib/commit/b42e568)
chore(algebra/group_power): rename type vars, minor cleanup ([#1997](https://github.com/leanprover-community/mathlib/pull/1997))
The only non-BC change should be removing
is_group_hom.map_gpow` / `is_add_group_hom.map_gsmul` in favor of `monoid_hom.map_gpow`.
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive

Modified src/algebra/group_power.lean
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* with_bot.coe_smul
- \+/\- *lemma* zero_pow
- \+/\- *lemma* ring_hom.map_pow
- \+ *lemma* is_semiring_hom.map_pow
- \+/\- *lemma* pow_dvd_pow
- \+/\- *lemma* neg_one_pow_eq_pow_mod_two
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* inv_pow'
- \+/\- *lemma* pow_div
- \+/\- *lemma* pow_inv
- \+/\- *lemma* smul_le_smul_of_le_right
- \+/\- *lemma* pow_le_pow_of_le_left
- \+/\- *lemma* pow_lt_pow
- \+/\- *lemma* pow_le_pow_of_le_left
- \+/\- *lemma* lt_of_pow_lt_pow
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_le_one
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* with_bot.coe_smul
- \+/\- *lemma* zero_pow
- \+/\- *lemma* ring_hom.map_pow
- \+/\- *lemma* pow_dvd_pow
- \+/\- *lemma* neg_one_pow_eq_pow_mod_two
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* inv_pow'
- \+/\- *lemma* pow_div
- \+/\- *lemma* pow_inv
- \+/\- *lemma* smul_le_smul_of_le_right
- \+/\- *lemma* pow_le_pow_of_le_left
- \+/\- *lemma* pow_lt_pow
- \+/\- *lemma* pow_le_pow_of_le_left
- \+/\- *lemma* lt_of_pow_lt_pow
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_le_one
- \+/\- *theorem* pow_zero
- \+/\- *theorem* add_monoid.zero_smul
- \+/\- *theorem* pow_succ
- \+/\- *theorem* succ_smul
- \+/\- *theorem* pow_one
- \+/\- *theorem* add_monoid.one_smul
- \+/\- *theorem* pow_mul_comm'
- \+/\- *theorem* smul_add_comm'
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* succ_smul'
- \+/\- *theorem* pow_two
- \+/\- *theorem* two_smul
- \+/\- *theorem* pow_add
- \+/\- *theorem* add_monoid.add_smul
- \+/\- *theorem* one_pow
- \+/\- *theorem* add_monoid.smul_zero
- \+/\- *theorem* pow_mul
- \+/\- *theorem* add_monoid.mul_smul'
- \+/\- *theorem* pow_mul'
- \+/\- *theorem* add_monoid.mul_smul
- \+/\- *theorem* add_monoid.smul_one
- \+/\- *theorem* pow_bit0
- \+/\- *theorem* bit0_smul
- \+/\- *theorem* pow_bit1
- \+/\- *theorem* bit1_smul
- \+/\- *theorem* pow_mul_comm
- \+/\- *theorem* smul_add_comm
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat
- \+ *theorem* monoid_hom.map_pow
- \+ *theorem* add_monoid_hom.map_smul
- \+ *theorem* is_monoid_hom.map_pow
- \+ *theorem* is_add_monoid_hom.map_smul
- \+/\- *theorem* mul_pow
- \+/\- *theorem* add_monoid.smul_add
- \+/\- *theorem* inv_pow
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* pow_sub
- \+/\- *theorem* add_monoid.smul_sub
- \+/\- *theorem* pow_inv_comm
- \+/\- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gpow_neg_succ
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gpow_zero
- \+/\- *theorem* zero_gsmul
- \+/\- *theorem* gpow_one
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* one_gpow
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* gpow_neg
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* gsmul_neg
- \+/\- *theorem* gpow_add
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* gpow_add_one
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* gpow_one_add
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* gpow_mul_comm
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gpow_mul
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gpow_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* gpow_bit0
- \+/\- *theorem* bit0_gsmul
- \+/\- *theorem* gpow_bit1
- \+/\- *theorem* bit1_gsmul
- \+ *theorem* monoid_hom.map_gpow
- \+ *theorem* add_monoid_hom.map_gsmul
- \+/\- *theorem* mul_gpow
- \+/\- *theorem* gsmul_add
- \+/\- *theorem* gsmul_sub
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* add_monoid.smul_eq_mul
- \+/\- *theorem* add_monoid.mul_smul_left
- \+/\- *theorem* add_monoid.mul_smul_assoc
- \+/\- *theorem* nat.cast_pow
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* mul_gsmul_left
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* sq_sub_sq
- \+/\- *theorem* pow_eq_zero
- \+/\- *theorem* pow_ne_zero
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* div_pow
- \+/\- *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* smul_le_smul
- \+/\- *theorem* pow_pos
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* pow_le_one
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *theorem* pow_right_inj
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *theorem* pow_le_pow
- \+/\- *theorem* pow_two_nonneg
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow
- \+/\- *theorem* pow_zero
- \+/\- *theorem* add_monoid.zero_smul
- \+/\- *theorem* pow_succ
- \+/\- *theorem* succ_smul
- \+/\- *theorem* pow_one
- \+/\- *theorem* add_monoid.one_smul
- \+/\- *theorem* pow_mul_comm'
- \+/\- *theorem* smul_add_comm'
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* succ_smul'
- \+/\- *theorem* pow_two
- \+/\- *theorem* two_smul
- \+/\- *theorem* pow_add
- \+/\- *theorem* add_monoid.add_smul
- \+/\- *theorem* one_pow
- \+/\- *theorem* add_monoid.smul_zero
- \+/\- *theorem* pow_mul
- \+/\- *theorem* add_monoid.mul_smul'
- \+/\- *theorem* pow_mul'
- \+/\- *theorem* add_monoid.mul_smul
- \+/\- *theorem* add_monoid.smul_one
- \+/\- *theorem* pow_bit0
- \+/\- *theorem* bit0_smul
- \+/\- *theorem* pow_bit1
- \+/\- *theorem* bit1_smul
- \+/\- *theorem* pow_mul_comm
- \+/\- *theorem* smul_add_comm
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat
- \- *theorem* map_pow
- \- *theorem* map_smul
- \- *theorem* map_pow
- \- *theorem* map_smul
- \+/\- *theorem* mul_pow
- \+/\- *theorem* add_monoid.smul_add
- \+/\- *theorem* inv_pow
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* pow_sub
- \+/\- *theorem* add_monoid.smul_sub
- \+/\- *theorem* pow_inv_comm
- \+/\- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gpow_neg_succ
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gpow_zero
- \+/\- *theorem* zero_gsmul
- \+/\- *theorem* gpow_one
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* one_gpow
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* gpow_neg
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* gpow_add
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* gpow_add_one
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* gpow_one_add
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* gpow_mul_comm
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gpow_mul
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gpow_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* gpow_bit0
- \+/\- *theorem* bit0_gsmul
- \+/\- *theorem* gpow_bit1
- \+/\- *theorem* bit1_gsmul
- \+/\- *theorem* gsmul_neg
- \- *theorem* map_pow
- \- *theorem* map_gpow
- \- *theorem* map_smul
- \- *theorem* map_gsmul
- \- *theorem* map_gpow
- \- *theorem* map_gsmul
- \+/\- *theorem* mul_gpow
- \+/\- *theorem* gsmul_add
- \+/\- *theorem* gsmul_sub
- \- *theorem* is_add_group_hom.gsmul
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* add_monoid.smul_eq_mul
- \+/\- *theorem* add_monoid.mul_smul_left
- \+/\- *theorem* add_monoid.mul_smul_assoc
- \+/\- *theorem* nat.cast_pow
- \- *theorem* is_semiring_hom.map_pow
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* mul_gsmul_left
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* sq_sub_sq
- \+/\- *theorem* pow_eq_zero
- \+/\- *theorem* pow_ne_zero
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* div_pow
- \+/\- *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* smul_le_smul
- \+/\- *theorem* pow_pos
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* pow_le_one
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *theorem* pow_right_inj
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *theorem* pow_le_pow
- \+/\- *theorem* pow_two_nonneg
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow
- \+/\- *def* monoid.pow
- \+/\- *def* add_monoid.smul
- \+/\- *def* gpow
- \+/\- *def* gsmul
- \+/\- *def* monoid.pow
- \+/\- *def* add_monoid.smul
- \+/\- *def* gpow
- \+/\- *def* gsmul

Modified src/algebra/lie_algebra.lean

Modified src/analysis/complex/exponential.lean
- \+ *lemma* coe_smul
- \+/\- *lemma* coe_gsmul
- \+/\- *lemma* coe_gsmul

Modified src/category_theory/conj.lean

Modified src/group_theory/quotient_group.lean



## [2020-02-17 07:29:08](https://github.com/leanprover-community/mathlib/commit/d673e55)
feat(ring_theory/algebra): add ext_iff ([#1996](https://github.com/leanprover-community/mathlib/pull/1996))
* feat(ring_theory/algebra): add ext_iff
* also add eq_top_iff
* Update src/ring_theory/algebra.lean
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *theorem* ext_iff
- \+ *theorem* eq_top_iff



## [2020-02-17 05:59:51](https://github.com/leanprover-community/mathlib/commit/770c56b)
doc(topology/metric_space/basic): add 1 docstring ([#2000](https://github.com/leanprover-community/mathlib/pull/2000))
* doc(topology/metric_space/basic): add 1 docstring
* Update src/topology/metric_space/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/topology/metric_space/basic.lean



## [2020-02-17 04:35:05](https://github.com/leanprover-community/mathlib/commit/dbb21c8)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-17 02:59:50](https://github.com/leanprover-community/mathlib/commit/1b1b626)
chore(topology/sequences): use filter bases, minor fixes ([#2001](https://github.com/leanprover-community/mathlib/pull/2001))
#### Estimated changes
Modified src/topology/sequences.lean
- \+/\- *def* is_seq_closed
- \+/\- *def* is_seq_closed



## [2020-02-15 23:38:34](https://github.com/leanprover-community/mathlib/commit/c7eb6f8)
chore(algebra/group/hom): add a missing `simp` lemma ([#1994](https://github.com/leanprover-community/mathlib/pull/1994))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* coe_mk



## [2020-02-15 13:33:39](https://github.com/leanprover-community/mathlib/commit/dbb61ea)
feat(tactic/hint): try out a customisable list of tactics, and report which ones make progress ([#1955](https://github.com/leanprover-community/mathlib/pull/1955))
* feat(tactic/hint): try out a fixed list of tactics, and report which ones make progress
* add hint to tactic.default
* make the list of hint tactics customisable
* suggestion
* fix linting errors
* simplify use of add_hint, and add hints
* remove TODO
* Update src/tactic/hint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* various
* Update docs/tactics.md
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/basic.lean

Modified src/tactic/core.lean

Modified src/tactic/finish.lean

Created src/tactic/hint.lean

Modified src/tactic/linarith.lean

Modified src/tactic/norm_num.lean

Modified src/tactic/omega/main.lean

Modified src/tactic/ring.lean

Modified src/tactic/split_ifs.lean

Modified src/tactic/tauto.lean

Modified src/tactic/tidy.lean

Created test/hint.lean



## [2020-02-15 09:59:41](https://github.com/leanprover-community/mathlib/commit/0b6d398)
chore(algebra/group/basic): rename type vars ([#1989](https://github.com/leanprover-community/mathlib/pull/1989))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* sub_left_inj
- \+ *lemma* sub_right_inj
- \+ *lemma* sub_add_sub_cancel
- \+ *lemma* sub_sub_sub_cancel_right
- \+ *lemma* sub_sub_cancel
- \+ *lemma* sub_eq_neg_add
- \+ *lemma* neg_sub_neg
- \+ *lemma* eq_sub_iff_add_eq'
- \+ *lemma* sub_eq_iff_eq_add'
- \+ *lemma* add_sub_cancel'
- \+ *lemma* add_sub_cancel'_right
- \+ *lemma* add_add_neg_cancel'_right
- \+ *lemma* sub_right_comm
- \+ *lemma* add_add_sub_cancel
- \+ *lemma* sub_add_add_cancel
- \+ *lemma* sub_add_sub_cancel'
- \+ *lemma* add_sub_sub_cancel
- \+ *lemma* sub_sub_sub_cancel_left
- \+ *lemma* sub_eq_sub_iff_sub_eq_sub
- \+ *lemma* bit0_zero
- \+ *lemma* bit1_zero
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj
- \+ *theorem* mul_mul_mul_comm
- \+ *theorem* inv_inj'
- \+ *theorem* mul_left_surjective
- \+ *theorem* mul_right_surjective
- \+ *theorem* eq_of_inv_eq_inv
- \+ *theorem* mul_self_iff_eq_one
- \+ *theorem* inv_eq_one
- \+ *theorem* inv_ne_one
- \+ *theorem* left_inverse_inv
- \+ *theorem* eq_inv_iff_eq_inv
- \+ *theorem* inv_eq_iff_inv_eq
- \+ *theorem* mul_eq_one_iff_eq_inv
- \+ *theorem* mul_eq_one_iff_inv_eq
- \+ *theorem* eq_inv_iff_mul_eq_one
- \+ *theorem* inv_eq_iff_mul_eq_one
- \+ *theorem* eq_mul_inv_iff_mul_eq
- \+ *theorem* eq_inv_mul_iff_mul_eq
- \+ *theorem* inv_mul_eq_iff_eq_mul
- \+ *theorem* mul_inv_eq_iff_eq_mul
- \+ *theorem* mul_inv_eq_one
- \+ *theorem* inv_comm_of_comm
- \+ *theorem* sub_sub_assoc_swap
- \+ *theorem* sub_eq_zero
- \+ *theorem* sub_ne_zero
- \+ *theorem* eq_sub_iff_add_eq
- \+ *theorem* sub_eq_iff_eq_add
- \+ *theorem* eq_iff_eq_of_sub_eq_sub
- \+ *theorem* left_inverse_sub_add_left
- \+ *theorem* left_inverse_add_left_sub
- \+ *theorem* left_inverse_add_right_neg_add
- \+ *theorem* left_inverse_neg_add_add_right
- \+ *theorem* neg_add'
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj



## [2020-02-14 17:55:38](https://github.com/leanprover-community/mathlib/commit/d36930b)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-14 16:27:08](https://github.com/leanprover-community/mathlib/commit/edefe20)
feat(ci): update nolints.txt after master builds ([#1979](https://github.com/leanprover-community/mathlib/pull/1979))
* feat(ci): update nolints.txt after master builds
* avoid failure when no changes
* update for production
* update condition
* header override is already unset
#### Estimated changes
Modified .github/workflows/build.yml

Created scripts/update_nolints.sh



## [2020-02-14 10:30:14](https://github.com/leanprover-community/mathlib/commit/938960e)
fix(scripts/deploy_docs): remove last trace of nightly builds ([#1986](https://github.com/leanprover-community/mathlib/pull/1986))
#### Estimated changes
Modified scripts/deploy_docs.sh



## [2020-02-14 01:44:12](https://github.com/leanprover-community/mathlib/commit/4441394)
chore(category_theory/conj): avoid `is_mul_hom` ([#1984](https://github.com/leanprover-community/mathlib/pull/1984))
#### Estimated changes
Modified src/category_theory/conj.lean



## [2020-02-14 00:07:30](https://github.com/leanprover-community/mathlib/commit/9a91125)
chore(group_theory/sub*) : rename type vars ([#1982](https://github.com/leanprover-community/mathlib/pull/1982))
Use `M`, `G`, `A` instead of greek letters
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+/\- *lemma* injective_mul
- \+/\- *lemma* is_subgroup.coe_inv
- \+/\- *lemma* is_subgroup.coe_gpow
- \+/\- *lemma* is_add_subgroup.gsmul_coe
- \+/\- *lemma* is_subgroup.gpow_mem
- \+/\- *lemma* is_add_subgroup.gsmul_mem
- \+/\- *lemma* gpowers_subset
- \+/\- *lemma* gmultiples_subset
- \+/\- *lemma* mem_gpowers
- \+/\- *lemma* mem_gmultiples
- \+/\- *lemma* normal_subgroup_of_comm_group
- \+/\- *lemma* mem_norm_comm
- \+/\- *lemma* mem_norm_comm_iff
- \+/\- *lemma* mem_trivial
- \+/\- *lemma* eq_trivial_iff
- \+/\- *lemma* mem_center
- \+/\- *lemma* subset_normalizer
- \+/\- *lemma* mem_ker
- \+/\- *lemma* one_ker_inv
- \+/\- *lemma* one_ker_inv'
- \+/\- *lemma* inv_ker_one
- \+/\- *lemma* inv_ker_one'
- \+/\- *lemma* one_iff_ker_inv
- \+/\- *lemma* one_iff_ker_inv'
- \+/\- *lemma* inv_iff_ker
- \+/\- *lemma* inv_iff_ker'
- \+/\- *lemma* inj_of_trivial_ker
- \+/\- *lemma* trivial_ker_of_inj
- \+/\- *lemma* inj_iff_trivial_ker
- \+/\- *lemma* trivial_ker_iff_eq_one
- \+/\- *lemma* mem_closure
- \+/\- *lemma* closure_subset_iff
- \+/\- *lemma* closure_subgroup
- \+/\- *lemma* image_closure
- \+/\- *lemma* trivial_eq_closure
- \+/\- *lemma* mem_conjugates_self
- \+/\- *lemma* mem_conjugates_of_set_iff
- \+/\- *lemma* conjugates_subset
- \+/\- *lemma* conj_mem_conjugates_of_set
- \+/\- *lemma* normal_closure_subset_iff
- \+/\- *lemma* simple_group_of_surjective
- \+/\- *lemma* injective_mul
- \+/\- *lemma* is_subgroup.coe_inv
- \+/\- *lemma* is_subgroup.coe_gpow
- \+/\- *lemma* is_add_subgroup.gsmul_coe
- \+/\- *lemma* is_subgroup.gpow_mem
- \+/\- *lemma* is_add_subgroup.gsmul_mem
- \+/\- *lemma* gpowers_subset
- \+/\- *lemma* gmultiples_subset
- \+/\- *lemma* mem_gpowers
- \+/\- *lemma* mem_gmultiples
- \+/\- *lemma* normal_subgroup_of_comm_group
- \+/\- *lemma* mem_norm_comm
- \+/\- *lemma* mem_norm_comm_iff
- \+/\- *lemma* mem_trivial
- \+/\- *lemma* eq_trivial_iff
- \+/\- *lemma* mem_center
- \+/\- *lemma* subset_normalizer
- \+/\- *lemma* mem_ker
- \+/\- *lemma* one_ker_inv
- \+/\- *lemma* one_ker_inv'
- \+/\- *lemma* inv_ker_one
- \+/\- *lemma* inv_ker_one'
- \+/\- *lemma* one_iff_ker_inv
- \+/\- *lemma* one_iff_ker_inv'
- \+/\- *lemma* inv_iff_ker
- \+/\- *lemma* inv_iff_ker'
- \+/\- *lemma* inj_of_trivial_ker
- \+/\- *lemma* trivial_ker_of_inj
- \+/\- *lemma* inj_iff_trivial_ker
- \+/\- *lemma* trivial_ker_iff_eq_one
- \+/\- *lemma* mem_closure
- \+/\- *lemma* closure_subset_iff
- \+/\- *lemma* closure_subgroup
- \+/\- *lemma* image_closure
- \+/\- *lemma* trivial_eq_closure
- \+/\- *lemma* mem_conjugates_self
- \+/\- *lemma* mem_conjugates_of_set_iff
- \+/\- *lemma* conjugates_subset
- \+/\- *lemma* conj_mem_conjugates_of_set
- \+/\- *lemma* normal_closure_subset_iff
- \+/\- *lemma* simple_group_of_surjective
- \- *lemma* simple_add_group_of_surjective
- \+/\- *theorem* is_subgroup.of_div
- \+/\- *theorem* is_add_subgroup.of_sub
- \+/\- *theorem* is_add_subgroup.sub_mem
- \+/\- *theorem* additive.normal_add_subgroup_iff
- \+/\- *theorem* multiplicative.normal_subgroup_iff
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* gpowers_eq_closure
- \+/\- *theorem* conjugates_of_set_mono
- \+/\- *theorem* conjugates_of_set_subset
- \+/\- *theorem* normal_closure_subset
- \+/\- *theorem* normal_closure_mono
- \+/\- *theorem* additive.simple_add_group_iff
- \+/\- *theorem* multiplicative.simple_group_iff
- \+/\- *theorem* is_subgroup.of_div
- \+/\- *theorem* is_add_subgroup.of_sub
- \+/\- *theorem* is_add_subgroup.sub_mem
- \+/\- *theorem* additive.normal_add_subgroup_iff
- \+/\- *theorem* multiplicative.normal_subgroup_iff
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* gpowers_eq_closure
- \+/\- *theorem* conjugates_of_set_mono
- \+/\- *theorem* conjugates_of_set_subset
- \+/\- *theorem* normal_closure_subset
- \+/\- *theorem* normal_closure_mono
- \+/\- *theorem* additive.simple_add_group_iff
- \+/\- *theorem* multiplicative.simple_group_iff
- \+/\- *def* gpowers
- \+/\- *def* gmultiples
- \+/\- *def* trivial
- \+/\- *def* center
- \+/\- *def* normalizer
- \+/\- *def* ker
- \+/\- *def* closure
- \+/\- *def* conjugates
- \+/\- *def* conjugates_of_set
- \+/\- *def* normal_closure
- \+/\- *def* gpowers
- \+/\- *def* gmultiples
- \+/\- *def* trivial
- \+/\- *def* center
- \+/\- *def* normalizer
- \+/\- *def* ker
- \+/\- *def* closure
- \+/\- *def* conjugates
- \+/\- *def* conjugates_of_set
- \+/\- *def* normal_closure

Modified src/group_theory/submonoid.lean
- \+/\- *lemma* powers.one_mem
- \+/\- *lemma* multiples.zero_mem
- \+/\- *lemma* powers.self_mem
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* powers.mul_mem
- \+/\- *lemma* multiples.add_mem
- \+/\- *lemma* image.is_submonoid
- \+/\- *lemma* is_submonoid.pow_mem
- \+/\- *lemma* is_add_submonoid.smul_mem
- \+/\- *lemma* is_submonoid.power_subset
- \+/\- *lemma* is_add_submonoid.multiple_subset
- \+/\- *lemma* list_prod_mem
- \+/\- *lemma* multiset_prod_mem
- \+/\- *lemma* finset_prod_mem
- \+/\- *lemma* is_submonoid.coe_one
- \+/\- *lemma* is_submonoid.coe_mul
- \+/\- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* image_closure
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* smul_mem
- \+/\- *lemma* multiples_subset
- \+/\- *lemma* coe_smul
- \+/\- *lemma* powers.one_mem
- \+/\- *lemma* multiples.zero_mem
- \+/\- *lemma* powers.self_mem
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* powers.mul_mem
- \+/\- *lemma* multiples.add_mem
- \+/\- *lemma* image.is_submonoid
- \+/\- *lemma* is_submonoid.pow_mem
- \+/\- *lemma* is_add_submonoid.smul_mem
- \+/\- *lemma* is_submonoid.power_subset
- \+/\- *lemma* is_add_submonoid.multiple_subset
- \+/\- *lemma* list_prod_mem
- \+/\- *lemma* multiset_prod_mem
- \+/\- *lemma* finset_prod_mem
- \+/\- *lemma* is_submonoid.coe_one
- \+/\- *lemma* is_submonoid.coe_mul
- \+/\- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* image_closure
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* smul_mem
- \+/\- *lemma* multiples_subset
- \+/\- *lemma* coe_smul
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* closure_singleton
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* closure'_singleton
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* closure_singleton
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* closure'_singleton
- \+/\- *def* powers
- \+/\- *def* multiples
- \+/\- *def* closure
- \+/\- *def* submonoid.to_add_submonoid
- \+/\- *def* submonoid.of_add_submonoid
- \+/\- *def* add_submonoid.to_submonoid
- \+/\- *def* add_submonoid.of_submonoid
- \+/\- *def* submonoid.add_submonoid_equiv
- \+/\- *def* multiples
- \+/\- *def* powers
- \+/\- *def* multiples
- \+/\- *def* closure
- \+/\- *def* submonoid.to_add_submonoid
- \+/\- *def* submonoid.of_add_submonoid
- \+/\- *def* add_submonoid.to_submonoid
- \+/\- *def* add_submonoid.of_submonoid
- \+/\- *def* submonoid.add_submonoid_equiv
- \+/\- *def* multiples



## [2020-02-13 22:27:55](https://github.com/leanprover-community/mathlib/commit/db1c500)
refactor(data/set/function): use dot notation ([#1934](https://github.com/leanprover-community/mathlib/pull/1934))
#### Estimated changes
Modified src/data/equiv/local_equiv.lean

Modified src/data/finsupp.lean

Modified src/data/set/basic.lean
- \- *theorem* image_eq_image_of_eq_on
- \- *def* eq_on

Modified src/data/set/countable.lean

Modified src/data/set/finite.lean

Modified src/data/set/function.lean
- \+/\- *lemma* range_restrict
- \+ *lemma* eq_on.symm
- \+ *lemma* eq_on_comm
- \+ *lemma* eq_on_refl
- \+ *lemma* eq_on.trans
- \+ *lemma* eq_on.mono
- \+/\- *lemma* injective_iff_inj_on_univ
- \+/\- *lemma* inj_on_iff_injective
- \+ *lemma* inj_on.inv_fun_on_image
- \+/\- *lemma* inj_on_preimage
- \+/\- *lemma* surjective_iff_surj_on_univ
- \+/\- *lemma* surj_on_iff_surjective
- \+ *lemma* surj_on.image_eq_of_maps_to
- \+ *lemma* bij_on.maps_to
- \+ *lemma* bij_on.inj_on
- \+ *lemma* bij_on.surj_on
- \+/\- *lemma* bij_on.mk
- \+ *lemma* bij_on_empty
- \+ *lemma* inj_on.bij_on_image
- \+ *lemma* bij_on.image_eq
- \+/\- *lemma* bijective_iff_bij_on_univ
- \+ *lemma* left_inv_on.eq_on
- \+ *lemma* left_inv_on.eq
- \+ *lemma* left_inv_on.congr_left
- \+ *lemma* right_inv_on.eq_on
- \+ *lemma* right_inv_on.eq
- \+ *lemma* inv_on.symm
- \+ *lemma* injective.inj_on
- \+ *lemma* injective.comp_inj_on
- \+ *lemma* surjective.surj_on
- \+/\- *lemma* injective_iff_inj_on_univ
- \- *lemma* inj_on_of_injective
- \- *lemma* inj_on_comp_of_injective_left
- \+/\- *lemma* inj_on_iff_injective
- \- *lemma* inv_fun_on_image
- \+/\- *lemma* inj_on_preimage
- \- *lemma* subset_image_iff
- \- *lemma* subset_range_iff
- \+/\- *lemma* surjective_iff_surj_on_univ
- \+/\- *lemma* surj_on_iff_surjective
- \- *lemma* image_eq_of_maps_to_of_surj_on
- \- *lemma* maps_to_of_bij_on
- \- *lemma* inj_on_of_bij_on
- \- *lemma* surj_on_of_bij_on
- \+/\- *lemma* bij_on.mk
- \- *lemma* inj_on.to_bij_on
- \- *lemma* image_eq_of_bij_on
- \+/\- *lemma* bijective_iff_bij_on_univ
- \+/\- *lemma* range_restrict
- \+ *theorem* eq_on.image_eq
- \+/\- *theorem* maps_to'
- \+ *theorem* maps_to_empty
- \+ *theorem* maps_to.image_subset
- \+ *theorem* maps_to.congr
- \+ *theorem* eq_on.maps_to_iff
- \+ *theorem* maps_to.comp
- \+ *theorem* maps_to.mono
- \+/\- *theorem* maps_to_univ
- \+/\- *theorem* maps_to_image
- \+ *theorem* maps_to_preimage
- \+/\- *theorem* maps_to_range
- \+ *theorem* inj_on.congr
- \+ *theorem* eq_on.inj_on_iff
- \+ *theorem* inj_on.mono
- \+ *theorem* inj_on.comp
- \+ *theorem* surj_on_empty
- \+ *theorem* surj_on.comap_nonempty
- \+ *theorem* surj_on.congr
- \+ *theorem* eq_on.surj_on_iff
- \+ *theorem* surj_on.mono
- \+ *theorem* surj_on.comp
- \+ *theorem* bij_on.congr
- \+ *theorem* eq_on.bij_on_iff
- \+ *theorem* bij_on.comp
- \+ *theorem* left_inv_on.congr_right
- \+ *theorem* left_inv_on.inj_on
- \+ *theorem* left_inv_on.surj_on
- \+ *theorem* left_inv_on.comp
- \+ *theorem* right_inv_on.congr_left
- \+ *theorem* right_inv_on.congr_right
- \+ *theorem* right_inv_on.surj_on
- \+ *theorem* right_inv_on.comp
- \+ *theorem* inj_on.right_inv_on_of_left_inv_on
- \+/\- *theorem* eq_on_of_left_inv_of_right_inv
- \+ *theorem* surj_on.left_inv_on_of_right_inv_on
- \+ *theorem* inv_on.bij_on
- \+ *theorem* inj_on.left_inv_on_inv_fun_on
- \+ *theorem* surj_on.right_inv_on_inv_fun_on
- \+ *theorem* bij_on.inv_on_inv_fun_on
- \+ *theorem* surj_on.inv_on_inv_fun_on
- \+ *theorem* surj_on.maps_to_inv_fun_on
- \+ *theorem* surj_on.bij_on_subset
- \+ *theorem* surj_on_iff_exists_bij_on_subset
- \+/\- *theorem* maps_to'
- \- *theorem* maps_to_of_eq_on
- \- *theorem* maps_to_comp
- \+/\- *theorem* maps_to_univ
- \+/\- *theorem* maps_to_image
- \+/\- *theorem* maps_to_range
- \- *theorem* image_subset_of_maps_to_of_subset
- \- *theorem* image_subset_of_maps_to
- \- *theorem* inj_on_of_eq_on
- \- *theorem* inj_on_of_inj_on_of_subset
- \- *theorem* inj_on_comp
- \- *theorem* surj_on_of_eq_on
- \- *theorem* surj_on_comp
- \- *theorem* bij_on_of_eq_on
- \- *theorem* bij_on_comp
- \- *theorem* left_inv_on_of_eq_on_left
- \- *theorem* left_inv_on_of_eq_on_right
- \- *theorem* inj_on_of_left_inv_on
- \- *theorem* left_inv_on_comp
- \- *theorem* right_inv_on_of_eq_on_left
- \- *theorem* right_inv_on_of_eq_on_right
- \- *theorem* surj_on_of_right_inv_on
- \- *theorem* right_inv_on_comp
- \- *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \+/\- *theorem* eq_on_of_left_inv_of_right_inv
- \- *theorem* left_inv_on_of_surj_on_right_inv_on
- \- *theorem* bij_on_of_inv_on
- \+ *def* eq_on
- \+/\- *def* maps_to
- \+/\- *def* inj_on
- \+/\- *def* surj_on
- \+/\- *def* bij_on
- \+/\- *def* left_inv_on
- \+/\- *def* right_inv_on
- \+/\- *def* inv_on
- \+/\- *def* maps_to
- \+/\- *def* inj_on
- \+/\- *def* surj_on
- \+/\- *def* bij_on
- \+/\- *def* left_inv_on
- \+/\- *def* right_inv_on
- \+/\- *def* inv_on

Modified src/data/subtype.lean

Modified src/linear_algebra/basis.lean

Modified src/topology/continuous_on.lean

Modified src/topology/metric_space/closeds.lean

Modified src/topology/uniform_space/uniform_embedding.lean



## [2020-02-13 21:47:45+01:00](https://github.com/leanprover-community/mathlib/commit/0372fb0)
fix(scripts/deploy_docs.sh): header override is already unset
Before, the nightly and doc deploys were running in different builds.
Now they're in the same build, so we don't need to (and can't) unset the
variable twice.
#### Estimated changes
Modified scripts/deploy_docs.sh



## [2020-02-13 20:44:53](https://github.com/leanprover-community/mathlib/commit/56a5240)
feat(calculus/fderiv): invariance of fderiv under linear equivs ([#1977](https://github.com/leanprover-community/mathlib/pull/1977))
* feat(calculus/fderiv): invariance of fderiv under linear equivs
* missing material
* coherent naming conventions
* fix build
* coherent naming conventions
* yury's comments
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable.differentiable_at
- \+ *lemma* differentiable_on_congr
- \+ *lemma* fderiv_const_apply
- \+/\- *lemma* fderiv_const
- \+ *lemma* fderiv_within_const_apply
- \+ *lemma* differentiable_at.comp_differentiable_within_at
- \+ *lemma* fderiv.comp_fderiv_within
- \+ *lemma* differentiable.comp_differentiable_on
- \+ *lemma* continuous_linear_equiv.comp_differentiable_within_at_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_at_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_on_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_iff
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff'
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff'
- \+ *lemma* continuous_linear_equiv.comp_fderiv_within
- \+ *lemma* continuous_linear_equiv.comp_fderiv
- \+ *lemma* continuous_linear_equiv.unique_diff_on_preimage_iff
- \+/\- *lemma* fderiv_const
- \- *lemma* fderiv_within_const

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_prod_le_iff

Modified src/linear_algebra/basic.lean
- \+ *theorem* symm_symm
- \+ *theorem* symm_symm_apply

Modified src/topology/algebra/module.lean
- \+ *lemma* comp_continuous_on_iff
- \+ *lemma* comp_continuous_iff
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm
- \+ *theorem* comp_assoc
- \+ *theorem* symm_symm
- \+ *theorem* symm_symm_apply

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_congr

Modified src/topology/homeomorph.lean
- \+ *lemma* comp_continuous_on_iff
- \+ *lemma* comp_continuous_iff



## [2020-02-13 19:03:11](https://github.com/leanprover-community/mathlib/commit/a79a055)
refactor(group_theory/submonoid): redefine `subtype.monoid` manually ([#1981](https://github.com/leanprover-community/mathlib/pull/1981))
* refactor(group_theory/submonoid): redefine `subtype.monoid` manually
This way `group.to_monoid subtype.group` is defeq `subtype.monoid group.to_monoid`.
* Fix compile of `ring_theory/integral_closure`
#### Estimated changes
Modified src/group_theory/subgroup.lean

Modified src/group_theory/submonoid.lean

Modified src/ring_theory/integral_closure.lean

Modified src/ring_theory/subring.lean



## [2020-02-13 18:26:28+01:00](https://github.com/leanprover-community/mathlib/commit/b7ffc6f)
fix(mergify): remove references to nightly builds
#### Estimated changes
Modified .mergify.yml



## [2020-02-13 13:18:09+01:00](https://github.com/leanprover-community/mathlib/commit/aa4da84)
chore(ci): don't build with Lean nightly ([#1975](https://github.com/leanprover-community/mathlib/pull/1975))
* chore(ci): don't build with Lean nightly
* fix condition for doc upload
#### Estimated changes
Modified .github/workflows/build.yml



## [2020-02-11 15:33:16](https://github.com/leanprover-community/mathlib/commit/abd412b)
chore(scripts): update nolints ([#1976](https://github.com/leanprover-community/mathlib/pull/1976))
#### Estimated changes
Modified scripts/nolints.txt



## [2020-02-11 13:43:45](https://github.com/leanprover-community/mathlib/commit/176852d)
feat(tactic/lint): check if inhabited instances should be nonempty ([#1971](https://github.com/leanprover-community/mathlib/pull/1971))
* add inhabited vs nonempty linter
* add new linter to ci
* start updating files to pass linter
* more linter fixes
* fix more linter errors
* more fixes
* fix build
* remove unnecessary instances
* nicer proof
* adjust inhabit tactic
* improve proof
* move instance to better place
* generalize instance
* fix build
* inhabited -> nonempty
* fix build
#### Estimated changes
Modified scripts/mk_all.sh

Modified scripts/mk_nolint.lean

Modified src/data/list/basic.lean
- \+/\- *lemma* get_neg
- \+/\- *lemma* get_neg

Modified src/data/set/basic.lean
- \+/\- *theorem* empty_ne_univ
- \+/\- *theorem* empty_ne_univ

Modified src/data/set/countable.lean
- \+/\- *lemma* countable_iff_exists_surjective
- \+/\- *lemma* countable_iff_exists_surjective

Modified src/data/set/lattice.lean
- \+/\- *theorem* Union_const
- \+/\- *theorem* Inter_const
- \+/\- *theorem* union_Union
- \+/\- *theorem* Union_union
- \+/\- *theorem* inter_Inter
- \+/\- *theorem* Inter_inter
- \+/\- *theorem* diff_Union
- \+/\- *theorem* Union_const
- \+/\- *theorem* Inter_const
- \+/\- *theorem* union_Union
- \+/\- *theorem* Union_union
- \+/\- *theorem* inter_Inter
- \+/\- *theorem* Inter_inter
- \+/\- *theorem* diff_Union

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_range
- \+/\- *lemma* constr_range

Modified src/linear_algebra/finsupp.lean
- \+/\- *theorem* lmap_domain_supported
- \+/\- *theorem* lmap_domain_supported

Modified src/logic/basic.lean
- \+ *lemma* nonempty.elim_to_inhabited
- \+/\- *theorem* forall_const
- \+/\- *theorem* exists_const
- \+/\- *theorem* forall_const
- \+/\- *theorem* exists_const

Modified src/logic/function.lean

Modified src/measure_theory/integration.lean

Modified src/order/filter/basic.lean
- \+/\- *lemma* prod_at_top_at_top_eq
- \+/\- *lemma* prod_map_at_top_eq
- \+/\- *lemma* prod_at_top_at_top_eq
- \+/\- *lemma* prod_map_at_top_eq

Modified src/tactic/interactive.lean

Modified src/tactic/lint.lean

Modified src/topology/basic.lean

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* emetric.cauchy_seq_iff_le_tendsto_0
- \+/\- *lemma* emetric.cauchy_seq_iff_le_tendsto_0

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* cauchy_seq_iff_tendsto_dist_at_top_0
- \+/\- *lemma* cauchy_seq_iff_tendsto_dist_at_top_0

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* tendsto_at_top
- \+/\- *theorem* cauchy_seq_iff
- \+/\- *theorem* cauchy_seq_iff'
- \+/\- *theorem* cauchy_seq_iff_nnreal
- \+/\- *theorem* tendsto_at_top
- \+/\- *theorem* cauchy_seq_iff
- \+/\- *theorem* cauchy_seq_iff'
- \+/\- *theorem* cauchy_seq_iff_nnreal

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/separation.lean

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq_iff_tendsto
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff'
- \+/\- *lemma* cauchy_seq_of_controlled
- \+/\- *lemma* cauchy_seq_iff_tendsto
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff'
- \+/\- *lemma* cauchy_seq_of_controlled



## [2020-02-11 09:25:41](https://github.com/leanprover-community/mathlib/commit/4e2c7e3)
feat(topology/subset_properties): alternative definitions of irreducible and connected ([#1970](https://github.com/leanprover-community/mathlib/pull/1970))
* refactor(topology/*): irreducible and connected sets are nonempty
* Fix typos
* Fix more typos
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Refactor 'nonempty' fields
* Fix spacing in set-builder
* Use dot notation
* Write a comment on the nonempty assumption
* Apply suggestions from code review
* irreducible_iff statements
* Fix build
* Tiny improvements
* Justify that connected spaces are nonempty
* Add docstrings
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update subset_properties.lean
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* subtype.preirreducible_space
- \+ *lemma* subtype.irreducible_space
- \+ *lemma* is_irreducible_iff_sInter
- \+ *lemma* is_preirreducible_iff_closed_union_closed
- \+ *lemma* is_irreducible_iff_sUnion_closed
- \+ *lemma* subtype.preconnected_space
- \+ *lemma* subtype.connected_space
- \+ *lemma* is_preconnected_iff_subset_of_disjoint
- \+ *lemma* is_connected_iff_sUnion_disjoint_open



## [2020-02-10 16:32:09](https://github.com/leanprover-community/mathlib/commit/93ba8b6)
refactor(topology/metric_space): introduce&use `edist`/`dist` bases ([#1969](https://github.com/leanprover-community/mathlib/pull/1969))
* refactor(topology/metric_space): introduce&use `edist`/`dist` bases
* Introduce bases for `emetric_space` and `metric_space`.
* Make some proofs use general facts about filter bases.
* Fix some lint errors
* Update src/topology/metric_space/emetric_space.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* +2 docstrings
#### Estimated changes
Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/normed_space/banach.lean

Modified src/analysis/normed_space/basic.lean

Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.eventually_iff

Modified src/topology/algebra/infinite_sum.lean

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/instances/ennreal.lean

Modified src/topology/metric_space/baire.lean

Modified src/topology/metric_space/basic.lean
- \+ *theorem* uniformity_basis_dist
- \+ *theorem* uniformity_basis_dist_inv_nat_succ
- \+ *theorem* uniformity_basis_dist_inv_nat_pos
- \+ *theorem* uniformity_basis_dist_le
- \+ *theorem* nhds_basis_ball
- \+ *theorem* nhds_basis_closed_ball
- \+ *theorem* nhds_basis_ball_inv_nat_succ
- \+ *theorem* nhds_basis_ball_inv_nat_pos
- \+ *theorem* nhds_within_basis_ball
- \+ *theorem* metric.uniformity_edist
- \+ *theorem* mem_closure_iff
- \- *theorem* uniformity_dist
- \- *theorem* uniformity_dist'
- \- *theorem* nhds_eq
- \- *theorem* exists_delta_of_continuous
- \- *theorem* uniformity_edist
- \- *theorem* mem_closure_iff'

Modified src/topology/metric_space/closeds.lean

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniformity_edist
- \+ *theorem* uniformity_basis_edist
- \+ *theorem* uniformity_basis_edist_le
- \+ *theorem* uniformity_basis_edist'
- \+ *theorem* uniformity_basis_edist_le'
- \+ *theorem* uniformity_basis_edist_nnreal
- \+ *theorem* uniformity_basis_edist_inv_nat
- \+/\- *theorem* edist_mem_uniformity
- \+ *theorem* nhds_basis_eball
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \+ *theorem* mem_closure_iff
- \- *theorem* uniformity_edist'
- \- *theorem* uniformity_edist''
- \+/\- *theorem* edist_mem_uniformity
- \- *theorem* uniformity_edist_nnreal
- \- *theorem* mem_uniformity_edist_inv_nat
- \- *theorem* uniformity_edist_inv_nat
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \- *theorem* mem_closure_iff'

Modified src/topology/metric_space/hausdorff_distance.lean

Modified src/topology/metric_space/isometry.lean

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.has_basis.mem_uniformity_iff
- \+ *lemma* nhds_basis_uniformity'
- \+ *lemma* nhds_basis_uniformity
- \+/\- *lemma* nhds_eq_uniformity
- \+ *lemma* filter.has_basis.uniform_continuous_iff
- \+/\- *lemma* nhds_eq_uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* filter.has_basis.cauchy_iff
- \+ *lemma* cauchy_iff'
- \+ *lemma* cauchy_seq_iff_tendsto
- \+ *lemma* filter.has_basis.cauchy_seq_iff
- \+ *lemma* filter.has_basis.cauchy_seq_iff'
- \- *lemma* cauchy_seq_iff_prod_map



## [2020-02-09 09:33:32](https://github.com/leanprover-community/mathlib/commit/777f214)
refactor(data/matrix,linear_algebra): Use `matrix.mul` as default multiplication in matrix lemmas ([#1959](https://github.com/leanprover-community/mathlib/pull/1959))
* Change `has_mul.mul` to `matrix.mul` in a few `simp` lemmas
* Standardise more lemmas for matrix multiplication
* Generalize `to_pequiv_mul_matrix` to rectangular matrices
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *theorem* diagonal_mul_diagonal
- \+/\- *theorem* diagonal_mul_diagonal'
- \+/\- *theorem* diagonal_mul_diagonal'
- \+/\- *theorem* diagonal_mul_diagonal

Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* to_pequiv_mul_matrix
- \+/\- *lemma* to_pequiv_mul_matrix

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* det_mul
- \+/\- *lemma* det_transpose
- \+/\- *lemma* det_mul
- \+/\- *lemma* det_transpose



## [2020-02-08 13:25:39](https://github.com/leanprover-community/mathlib/commit/bcb63eb)
refactor(topology/*): irreducible and connected sets are nonempty ([#1964](https://github.com/leanprover-community/mathlib/pull/1964))
* refactor(topology/*): irreducible and connected sets are nonempty
* Fix typos
* Fix more typos
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Refactor 'nonempty' fields
* Fix spacing in set-builder
* Use dot notation
* Write a comment on the nonempty assumption
* Apply suggestions from code review
* Fix build
* Tiny improvements
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_preconnected.forall_Icc_subset
- \+ *lemma* is_preconnected.intermediate_value
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* is_connected_Icc
- \+ *lemma* is_preconnected_iff_forall_Icc_subset
- \+ *lemma* is_preconnected_Ici
- \+ *lemma* is_preconnected_Iic
- \+ *lemma* is_preconnected_Iio
- \+ *lemma* is_preconnected_Ioi
- \+/\- *lemma* is_connected_Ioo
- \+ *lemma* is_preconnected_Ioc
- \+ *lemma* is_preconnected_Ico
- \- *lemma* is_connected.forall_Icc_subset
- \- *lemma* is_connected.intermediate_value
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* is_connected_Icc
- \- *lemma* is_connected_iff_forall_Icc_subset
- \- *lemma* is_connected_Ici
- \- *lemma* is_connected_Iic
- \- *lemma* is_connected_Iio
- \- *lemma* is_connected_Ioi
- \+/\- *lemma* is_connected_Ioo
- \- *lemma* is_connected_Ioc
- \- *lemma* is_connected_Ico

Modified src/topology/basic.lean
- \+ *lemma* set.nonempty.closure

Modified src/topology/subset_properties.lean
- \+ *lemma* is_irreducible.nonempty
- \+ *lemma* is_irreducible.is_preirreducible
- \+ *lemma* is_irreducible.closure
- \+ *lemma* irreducible_component_property
- \+ *lemma* is_connected.nonempty
- \+ *lemma* is_connected.is_preconnected
- \+ *theorem* is_preirreducible_empty
- \+ *theorem* is_preirreducible.closure
- \+ *theorem* exists_preirreducible
- \+/\- *theorem* is_irreducible_irreducible_component
- \+ *theorem* nonempty_preirreducible_inter
- \+ *theorem* is_preirreducible.image
- \+ *theorem* is_irreducible.image
- \+ *theorem* is_preirreducible.is_preconnected
- \+ *theorem* is_irreducible.is_connected
- \+ *theorem* is_preconnected_empty
- \+ *theorem* is_preconnected_of_forall
- \+ *theorem* is_preconnected_of_forall_pair
- \+ *theorem* is_preconnected_sUnion
- \+ *theorem* is_preconnected.union
- \+/\- *theorem* is_connected.union
- \+ *theorem* is_preconnected.closure
- \+/\- *theorem* is_connected.closure
- \+ *theorem* is_preconnected.image
- \+/\- *theorem* is_connected.image
- \+ *theorem* is_preconnected_closed_iff
- \+/\- *theorem* is_connected_connected_component
- \+/\- *theorem* subset_connected_component
- \+ *theorem* nonempty_inter
- \+/\- *theorem* is_clopen_iff
- \- *theorem* is_irreducible_empty
- \- *theorem* is_irreducible_closure
- \- *theorem* exists_irreducible
- \+/\- *theorem* is_irreducible_irreducible_component
- \- *theorem* irreducible_exists_mem_inter
- \- *theorem* is_connected_of_is_irreducible
- \- *theorem* is_connected_empty
- \- *theorem* is_connected_of_forall
- \- *theorem* is_connected_of_forall_pair
- \- *theorem* is_connected_sUnion
- \+/\- *theorem* is_connected.union
- \+/\- *theorem* is_connected.closure
- \+/\- *theorem* is_connected.image
- \- *theorem* is_connected_closed_iff
- \+/\- *theorem* is_connected_connected_component
- \+/\- *theorem* subset_connected_component
- \- *theorem* exists_mem_inter
- \+/\- *theorem* is_clopen_iff
- \+ *def* is_preirreducible
- \+/\- *def* is_irreducible
- \+ *def* is_preconnected
- \+/\- *def* is_connected
- \+/\- *def* is_irreducible
- \+/\- *def* is_connected



## [2020-02-08 10:42:31](https://github.com/leanprover-community/mathlib/commit/2e18388)
feat(linear_algebra): The Special linear group SL(n, R) ([#1960](https://github.com/leanprover-community/mathlib/pull/1960))
* Define the special linear group
* Make definitions independent of PR [#1959](https://github.com/leanprover-community/mathlib/pull/1959)
That PR changes `det_mul` to have another, still definitionally equal, type.
If the invocations to `det_mul` are independent of syntactic equality, i.e. we
only pass `det_mul` to `erw`, this branch should be compatible with the state
before the change and after.
* Documentation and code style improvements
* Improve module docstring
* Fix documentation
`matrix.special_linear_group` is not a set but a type
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Don't directly coerce from SL to linear maps
Now we coerce from `matrix.special_linear_group n R` to `matrix n n R` instead
of `general_linear_group R (n -> R)`
* Whitespace fixes
* Fix failing build in `src/linear_algebra/dual.lean`
* Give an almost generic formula for `det_adjugate`
* Move `det_eq_one_of_card_eq_zero` to the correct section
* Replace the ad-hoc assumption of `det_adjugate_of_invertible` with `is_unit`
* Fix linting error
There was an unnecessary assumption [decidable_eq α] floating around
* Replace `special_linear_group.val` with the appropriate coercions
* whitespace
Correctly indent continued line
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Docstrings for the `det_adjugate_of_...` lemmas
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* to_fun_eq_coe

Modified src/data/fintype.lean
- \+ *lemma* univ_eq_singleton_of_card_one

Modified src/data/matrix/basic.lean
- \+ *lemma* smul_eq_diagonal_mul
- \+ *lemma* smul_eq_mul_diagonal
- \+ *lemma* mul_vec_one

Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_eq_one_of_card_eq_zero
- \+ *lemma* det_smul
- \+ *lemma* det_eq_zero_of_column_eq_zero

Modified src/linear_algebra/dual.lean

Modified src/linear_algebra/matrix.lean
- \+ *lemma* to_lin_one

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* det_adjugate_of_cancel
- \+ *lemma* adjugate_eq_one_of_card_eq_one
- \+ *lemma* adjugate_zero
- \+ *lemma* det_adjugate_eq_one
- \+ *lemma* det_adjugate_of_is_unit

Created src/linear_algebra/special_linear_group.lean
- \+ *lemma* ext_iff
- \+ *lemma* ext
- \+ *lemma* inv_val
- \+ *lemma* inv_apply
- \+ *lemma* mul_val
- \+ *lemma* mul_apply
- \+ *lemma* one_val
- \+ *lemma* one_apply
- \+ *lemma* det_coe_matrix
- \+ *lemma* det_coe_fun
- \+ *lemma* to_lin_mul
- \+ *lemma* to_lin_one
- \+ *lemma* coe_to_GL
- \+ *lemma* to_GL_one
- \+ *lemma* to_GL_mul
- \+ *def* special_linear_group
- \+ *def* to_lin
- \+ *def* to_linear_equiv
- \+ *def* to_GL
- \+ *def* embedding_GL



## [2020-02-07 16:57:48](https://github.com/leanprover-community/mathlib/commit/2007d34)
feat(analysis/normed_space/multilinear): norm on continuous multilinear maps ([#1956](https://github.com/leanprover-community/mathlib/pull/1956))
* feat(analysis/normed_space/multilinear): norm on continuous multilinear maps
* docstring
* improved docstrings
#### Estimated changes
Created src/analysis/normed_space/multilinear.lean
- \+ *lemma* norm_image_sub_le_of_bound'
- \+ *lemma* norm_image_sub_le_of_bound
- \+ *lemma* bounds_nonempty
- \+ *lemma* bounds_bdd_below
- \+ *lemma* op_norm_nonneg
- \+ *lemma* ratio_le_op_norm
- \+ *lemma* unit_le_op_norm
- \+ *lemma* op_norm_le_bound
- \+ *lemma* norm_zero
- \+ *lemma* op_norm_smul
- \+ *lemma* op_norm_neg
- \+ *lemma* norm_image_sub_le_of_bound'
- \+ *lemma* norm_image_sub_le_of_bound
- \+ *lemma* continuous_eval
- \+ *lemma* multilinear_map.mk_continuous_norm_le
- \+ *lemma* mk_pi_field_apply
- \+ *lemma* mk_pi_ring_apply_one_eq_self
- \+ *lemma* continuous_linear_map.norm_map_tail_right_le
- \+ *lemma* continuous_multilinear_map.norm_map_tail_left_le
- \+ *lemma* continuous_multilinear_map.norm_map_cons_le
- \+ *lemma* continuous_linear_map.uncurry_left_apply
- \+ *lemma* continuous_multilinear_map.curry_left_apply
- \+ *lemma* continuous_linear_map.curry_uncurry_left
- \+ *lemma* continuous_multilinear_map.uncurry_curry_left
- \+ *lemma* continuous_multilinear_map.curry_left_norm
- \+ *lemma* continuous_linear_map.uncurry_left_norm
- \+ *lemma* continuous_multilinear_map.uncurry_right_apply
- \+ *lemma* continuous_multilinear_map.curry_right_apply
- \+ *lemma* continuous_multilinear_map.curry_uncurry_right
- \+ *lemma* continuous_multilinear_map.uncurry_curry_right
- \+ *lemma* continuous_multilinear_map.curry_right_norm
- \+ *lemma* continuous_multilinear_map.uncurry_right_norm
- \+ *lemma* continuous_multilinear_map.curry0_apply
- \+ *lemma* continuous_multilinear_map.uncurry0_curry0
- \+ *lemma* continuous_multilinear_map.curry0_uncurry0
- \+ *lemma* continuous_multilinear_map.uncurry0_norm
- \+ *lemma* continuous_multilinear_map.curry0_norm
- \+ *theorem* exists_bound_of_continuous
- \+ *theorem* continuous_of_bound
- \+ *theorem* bound
- \+ *theorem* le_op_norm
- \+ *theorem* op_norm_add_le
- \+ *theorem* op_norm_zero_iff
- \+ *def* mk_continuous
- \+ *def* op_norm
- \+ *def* continuous_linear_map.uncurry_left
- \+ *def* continuous_multilinear_map.curry_left
- \+ *def* continuous_multilinear_curry_left_equiv_aux
- \+ *def* continuous_multilinear_curry_left_equiv
- \+ *def* continuous_multilinear_map.uncurry_right
- \+ *def* continuous_multilinear_map.curry_right
- \+ *def* continuous_multilinear_curry_right_equiv_aux
- \+ *def* continuous_multilinear_curry_right_equiv
- \+ *def* continuous_multilinear_map.uncurry0
- \+ *def* continuous_multilinear_map.curry0
- \+ *def* continuous_multilinear_curry_fin0_aux
- \+ *def* continuous_multilinear_curry_fin0



## [2020-02-07 06:21:24](https://github.com/leanprover-community/mathlib/commit/f912a6b)
feat(algebraic_geometry/prime_spectrum): first definitions ([#1957](https://github.com/leanprover-community/mathlib/pull/1957))
* Start on prime spectrum
* Define comap betwee prime spectra; prove continuity
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* chore(*): rename `filter.inhabited_of_mem_sets` to `nonempty_of_mem_sets` ([#1943](https://github.com/leanprover-community/mathlib/pull/1943))
In other names `inhabited` means that we have a `default` element.
* refactor(linear_algebra/multilinear): cleanup of multilinear maps ([#1921](https://github.com/leanprover-community/mathlib/pull/1921))
* staging [ci skip]
* staging
* staging
* cleanup norms
* complete currying
* docstrings
* docstrings
* cleanup
* nonterminal simp
* golf
* missing bits for derivatives
* sub_apply
* cleanup
* better docstrings
* remove two files
* reviewer's comments
* use fintype
* line too long
* feat(ring_theory/power_series): several simp lemmas ([#1945](https://github.com/leanprover-community/mathlib/pull/1945))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(ring_theory/power_series): several simp lemmas
* Remove file that shouldn't be there yet
* Update src/ring_theory/power_series.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Generalise lemma to canonically_ordered_monoid
* Update name
* Fix build
* feat(tactic/lint): Three new linters, update illegal_constants ([#1947](https://github.com/leanprover-community/mathlib/pull/1947))
* add three new linters
* fix failing declarations
* restrict and rename illegal_constants linter
* update doc
* update ge_or_gt test
* update mk_nolint
* fix error
* Update scripts/mk_nolint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* clarify unfolds_to_class
* fix names since name is no longer protected
also change one declaration back to instance, since it did not cause a linter failure
* fix errors, move notes to docstrings
* add comments to docstring
* update mk_all.sh
* fix linter errors
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers ([#1952](https://github.com/leanprover-community/mathlib/pull/1952))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers
* Remove old file
* Process comments
* feat(topology/algebra/multilinear): define continuous multilinear maps ([#1948](https://github.com/leanprover-community/mathlib/pull/1948))
* feat(data/set/intervals): define intervals and prove basic properties ([#1949](https://github.com/leanprover-community/mathlib/pull/1949))
* things about intervals
* better documentation
* better file name
* add segment_eq_interval
* better proof for is_measurable_interval
* better import and better proof
* better proof
* refactor(*): migrate from `≠ ∅` to `set.nonempty` ([#1954](https://github.com/leanprover-community/mathlib/pull/1954))
* refactor(*): migrate from `≠ ∅` to `set.nonempty`
Sorry for a huge PR but it's easier to do it in one go.
Basically, I got rid of all `≠ ∅` in theorem/def types, then fixed
compile.
I also removed most lemmas about `≠ ∅` from `set/basic` to make sure
that I didn't miss something I should change elsewhere. Should I
restore (some of) them?
* Fix compile of `archive/`
* Drop +1 unneeded argument, thanks @sgouezel.
* Fix build
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Change I to s, and little fixes
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Indentation
* Update prime_spectrum.lean
* fix build
#### Estimated changes
Created src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* ext
- \+ *lemma* mem_zero_locus
- \+ *lemma* zero_locus_empty_of_one_mem
- \+ *lemma* zero_locus_univ
- \+ *lemma* zero_locus_span
- \+ *lemma* union_zero_locus_ideal
- \+ *lemma* union_zero_locus
- \+ *lemma* zero_locus_Union
- \+ *lemma* Inter_zero_locus
- \+ *lemma* is_open_iff
- \+ *lemma* is_closed_iff_zero_locus
- \+ *lemma* zero_locus_is_closed
- \+ *lemma* comap_as_ideal
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* preimage_comap_zero_locus
- \+ *lemma* comap_continuous
- \+ *def* prime_spectrum
- \+ *def* zero_locus
- \+ *def* comap

Modified src/topology/basic.lean
- \+ *def* topological_space.of_closed



## [2020-02-06 15:25:57](https://github.com/leanprover-community/mathlib/commit/fb160f0)
refactor(topology/continuous_on): use filter bases ([#1968](https://github.com/leanprover-community/mathlib/pull/1968))
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_has_basis
- \+ *lemma* nhds_within_basis_open



## [2020-02-06 12:20:38](https://github.com/leanprover-community/mathlib/commit/0e533d0)
refactor(topology/basic): rewrite some proofs using filter bases ([#1967](https://github.com/leanprover-community/mathlib/pull/1967))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* nhds_basis_opens
- \+/\- *lemma* mem_nhds_sets_iff
- \- *lemma* nhds_sets
- \+/\- *lemma* mem_nhds_sets_iff
- \+ *theorem* mem_closure_iff_nhds_basis

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/order.lean



## [2020-02-06 10:51:04](https://github.com/leanprover-community/mathlib/commit/b4c2ec2)
chore(topology/metric_space/basic): simplify `tendsto_nhds` ([#1966](https://github.com/leanprover-community/mathlib/pull/1966))
* chore(topology/metric_space/basic): simplify `tendsto_nhds`
No reason to have an extra `∃ n ∈ f`.
* whitespace
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/analysis/normed_space/basic.lean

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/metric_space/basic.lean



## [2020-02-06 09:12:40](https://github.com/leanprover-community/mathlib/commit/34f9a17)
feat(*): a few simple lemmas ([#1965](https://github.com/leanprover-community/mathlib/pull/1965))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* nonempty.not_subset_empty

Modified src/order/complete_lattice.lean
- \+ *lemma* supr_subtype'

Modified src/order/filter/basic.lean
- \+ *lemma* nonempty_of_ne_bot

Modified src/topology/algebra/ordered.lean
- \+ *lemma* supr_of_continuous'
- \+/\- *lemma* supr_of_continuous
- \+ *lemma* infi_of_continuous'
- \+/\- *lemma* infi_of_continuous
- \+/\- *lemma* supr_of_continuous
- \+/\- *lemma* infi_of_continuous



## [2020-02-05 20:37:51](https://github.com/leanprover-community/mathlib/commit/8c086a6)
chore(tactic/basic,default): add missing tactics ([#1962](https://github.com/leanprover-community/mathlib/pull/1962))
#### Estimated changes
Modified src/tactic/basic.lean

Modified src/tactic/default.lean



## [2020-02-05 17:46:23](https://github.com/leanprover-community/mathlib/commit/8786ea6)
refactor(measure_theory/set_integral): move set integral into namespace set and add some lemmas ([#1950](https://github.com/leanprover-community/mathlib/pull/1950))
* move set integral into namespace set and add some lemmas
* Update bochner_integration.lean
* better theorem names
* Update set_integral.lean
* Update set_integral.lean
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* simple_func.integral_eq_integral
- \+/\- *lemma* integral_zero
- \+ *lemma* integral_nonneg_of_ae
- \- *lemma* integral_coe_eq_integral
- \+/\- *lemma* integral_zero
- \- *lemma* integral_nonneg_of_nonneg_ae

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* measurable_on_empty
- \+ *lemma* measurable.measurable_on_univ
- \+/\- *lemma* measurable_on_singleton
- \+/\- *lemma* measurable.measurable_on
- \+/\- *lemma* integrable_on_congr_ae
- \+/\- *lemma* integrable_on_empty
- \+ *lemma* measure_theory.integrable.integrable_on
- \+/\- *lemma* integrable_on.smul
- \+ *lemma* integral_on_undef
- \+ *lemma* integral_on_non_measurable
- \+ *lemma* integral_on_non_integrable
- \+/\- *lemma* integral_on_congr
- \+ *lemma* integral_on_nonneg_of_ae
- \+ *lemma* integral_on_nonneg
- \+ *lemma* integral_on_nonpos_of_ae
- \+ *lemma* integral_on_nonpos
- \+/\- *lemma* measurable_on_empty
- \- *lemma* measurable_on_univ
- \+/\- *lemma* measurable.measurable_on
- \+/\- *lemma* measurable_on_singleton
- \+/\- *lemma* integrable_on_congr_ae
- \+/\- *lemma* integrable_on_empty
- \- *lemma* integrable_on_of_integrable
- \+/\- *lemma* integrable_on.smul
- \+/\- *lemma* integral_on_congr
- \+/\- *def* measurable_on
- \+/\- *def* integrable_on
- \+/\- *def* measurable_on
- \+/\- *def* integrable_on



## [2020-02-05 14:27:45](https://github.com/leanprover-community/mathlib/commit/08581cc)
feat(tactic/rename): Add improved renaming tactic ([#1916](https://github.com/leanprover-community/mathlib/pull/1916))
* feat(tactic/rename): Add improved renaming tactic
We add a tactic `rename'` which works like `rename`, with the following
improvements:
* Multiple hypotheses can be renamed at once.
* Renaming always preserve the position of a hypothesis in the context.
* Move private def `drop_until_inclusive` to `list.after`
* Change `rename'` docs to rely less on knowledge of `rename`
* Improve formatting of list.after docs
#### Estimated changes
Modified docs/tactics.md

Modified src/data/list/defs.lean
- \+ *def* after

Modified src/tactic/basic.lean

Created src/tactic/rename.lean

Modified test/tactics.lean



## [2020-02-05 13:11:44+01:00](https://github.com/leanprover-community/mathlib/commit/6845aaa)
chore(*): bump Lean version to 3.5.1c ([#1958](https://github.com/leanprover-community/mathlib/pull/1958))
* chore(leanpkg.toml): bump lean version to 3.5.0
* update CI to build with 3.5.0
* update mergify
* update contribute docs
* update deploy_nightly.sh
* 3.5.0 -> 3.5.1
#### Estimated changes
Modified .github/workflows/build.yml

Modified .mergify.yml

Modified docs/contribute/index.md

Modified leanpkg.toml

Modified scripts/deploy_nightly.sh

Modified src/algebra/ring.lean

Modified src/tactic/squeeze.lean



## [2020-02-05 06:25:59](https://github.com/leanprover-community/mathlib/commit/dd8da51)
refactor(*): migrate from `≠ ∅` to `set.nonempty` ([#1954](https://github.com/leanprover-community/mathlib/pull/1954))
* refactor(*): migrate from `≠ ∅` to `set.nonempty`
Sorry for a huge PR but it's easier to do it in one go.
Basically, I got rid of all `≠ ∅` in theorem/def types, then fixed
compile.
I also removed most lemmas about `≠ ∅` from `set/basic` to make sure
that I didn't miss something I should change elsewhere. Should I
restore (some of) them?
* Fix compile of `archive/`
* Drop +1 unneeded argument, thanks @sgouezel.
#### Estimated changes
Modified archive/imo1988_q6.lean

Modified src/algebra/pointwise.lean
- \+ *lemma* nonempty.pointwise_mul
- \- *lemma* pointwise_mul_ne_empty

Modified src/analysis/calculus/local_extr.lean

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *theorem* unique_diff_on_convex
- \+/\- *theorem* unique_diff_on_convex

Modified src/analysis/complex/polynomial.lean

Modified src/analysis/normed_space/real_inner_product.lean
- \+/\- *theorem* exists_norm_eq_infi_of_complete_convex
- \+/\- *theorem* norm_eq_infi_iff_inner_le_zero
- \+/\- *theorem* exists_norm_eq_infi_of_complete_subspace
- \+/\- *theorem* norm_eq_infi_iff_inner_eq_zero
- \+/\- *theorem* exists_norm_eq_infi_of_complete_convex
- \+/\- *theorem* norm_eq_infi_iff_inner_le_zero
- \+/\- *theorem* exists_norm_eq_infi_of_complete_subspace
- \+/\- *theorem* norm_eq_infi_iff_inner_eq_zero

Modified src/analysis/normed_space/riesz_lemma.lean

Modified src/computability/halting.lean

Modified src/data/analysis/filter.lean

Modified src/data/analysis/topology.lean

Modified src/data/real/basic.lean

Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_Inf

Modified src/data/real/nnreal.lean

Modified src/data/semiquot.lean
- \+ *theorem* nonempty
- \- *theorem* ne_empty

Modified src/data/set/basic.lean
- \+/\- *lemma* univ_nonempty
- \+ *lemma* nonempty.to_subtype
- \+ *lemma* not_nonempty_iff_eq_empty
- \+ *lemma* empty_not_nonempty
- \+/\- *lemma* nmem_singleton_empty
- \+/\- *lemma* nonempty_compl
- \+ *lemma* range_nonempty_iff_nonempty
- \+ *lemma* range_nonempty
- \+/\- *lemma* range_eq_empty
- \+/\- *lemma* fst_image_prod
- \+/\- *lemma* snd_image_prod
- \+/\- *lemma* univ_nonempty
- \- *lemma* nonempty_iff_univ_ne_empty
- \- *lemma* univ_ne_empty
- \+/\- *lemma* nmem_singleton_empty
- \+/\- *lemma* nonempty_compl
- \- *lemma* inter_singleton_ne_empty
- \- *lemma* range_ne_empty_iff_nonempty
- \- *lemma* range_ne_empty
- \+/\- *lemma* range_eq_empty
- \+/\- *lemma* fst_image_prod
- \+/\- *lemma* snd_image_prod
- \+/\- *theorem* ne_empty_iff_nonempty
- \+/\- *theorem* ne_empty_iff_nonempty
- \- *theorem* ne_empty_iff_exists_mem
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* ne_empty_of_mem
- \- *theorem* coe_nonempty_iff_ne_empty
- \- *theorem* not_eq_empty_iff_exists
- \- *theorem* subset_ne_empty
- \- *theorem* nonempty_of_inter_nonempty_right
- \- *theorem* nonempty_of_inter_nonempty_left
- \- *theorem* insert_ne_empty
- \- *theorem* singleton_ne_empty
- \- *theorem* prod_ne_empty_iff

Modified src/data/set/countable.lean
- \+/\- *lemma* countable_iff_exists_surjective_to_subtype
- \+/\- *lemma* exists_surjective_of_countable
- \+/\- *lemma* countable_iff_exists_surjective_to_subtype
- \+/\- *lemma* exists_surjective_of_countable

Modified src/data/set/finite.lean
- \+/\- *lemma* finite.exists_maximal_wrt
- \+/\- *lemma* finite.exists_maximal_wrt

Modified src/data/set/intervals/basic.lean
- \- *lemma* Iio_ne_empty
- \- *lemma* Ioi_ne_empty
- \- *lemma* Iic_ne_empty
- \- *lemma* Ici_ne_empty

Modified src/data/set/lattice.lean

Modified src/data/setoid.lean
- \+ *lemma* nonempty_of_mem_partition
- \- *lemma* ne_empty_of_mem_partition

Modified src/geometry/manifold/manifold.lean

Modified src/geometry/manifold/real_instances.lean

Modified src/measure_theory/bochner_integration.lean

Modified src/measure_theory/decomposition.lean

Modified src/measure_theory/integration.lean

Modified src/measure_theory/measurable_space.lean

Modified src/measure_theory/measure_space.lean

Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* Inf_gen_nonempty1
- \+/\- *lemma* Inf_gen_nonempty1
- \+/\- *theorem* top_apply
- \+/\- *theorem* top_apply

Modified src/measure_theory/simple_func_dense.lean

Modified src/order/bounds.lean
- \+ *lemma* nonempty_of_is_lub
- \+ *lemma* nonempty_of_is_glb
- \- *lemma* ne_empty_of_is_lub
- \- *lemma* ne_empty_of_is_glb

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cSup_lower_bounds_eq_cInf
- \+/\- *lemma* cInf_upper_bounds_eq_cSup
- \+/\- *lemma* csupr_le_csupr
- \+/\- *lemma* csupr_le
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le_cinfi
- \+/\- *lemma* le_cinfi
- \+/\- *lemma* cinfi_le
- \+/\- *lemma* is_lub_cSup
- \+/\- *lemma* is_glb_cInf
- \+/\- *lemma* exists_lt_of_lt_cSup
- \+/\- *lemma* exists_lt_of_lt_csupr
- \+/\- *lemma* exists_lt_of_cInf_lt
- \+/\- *lemma* exists_lt_of_cinfi_lt
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* cSup_lower_bounds_eq_cInf
- \+/\- *lemma* cInf_upper_bounds_eq_cSup
- \+/\- *lemma* csupr_le_csupr
- \+/\- *lemma* csupr_le
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le_cinfi
- \+/\- *lemma* le_cinfi
- \+/\- *lemma* cinfi_le
- \+/\- *lemma* is_lub_cSup
- \+/\- *lemma* is_glb_cInf
- \+/\- *lemma* exists_lt_of_lt_cSup
- \+/\- *lemma* exists_lt_of_lt_csupr
- \+/\- *lemma* exists_lt_of_cInf_lt
- \+/\- *lemma* exists_lt_of_cinfi_lt
- \+/\- *lemma* coe_Inf
- \+/\- *theorem* cSup_le
- \+/\- *theorem* le_cInf
- \+/\- *theorem* cSup_le_cSup
- \+/\- *theorem* cInf_le_cInf
- \+/\- *theorem* cSup_le_iff
- \+/\- *theorem* le_cInf_iff
- \+/\- *theorem* cSup_intro
- \+/\- *theorem* cInf_intro
- \+/\- *theorem* cInf_le_cSup
- \+/\- *theorem* cSup_union
- \+/\- *theorem* cInf_union
- \+/\- *theorem* cSup_inter_le
- \+/\- *theorem* le_cInf_inter
- \+/\- *theorem* cSup_insert
- \+/\- *theorem* cInf_insert
- \+/\- *theorem* cinfi_const
- \+/\- *theorem* csupr_const
- \+/\- *theorem* cSup_intro'
- \+/\- *theorem* cSup_le
- \+/\- *theorem* le_cInf
- \+/\- *theorem* cSup_le_cSup
- \+/\- *theorem* cInf_le_cInf
- \+/\- *theorem* cSup_le_iff
- \+/\- *theorem* le_cInf_iff
- \+/\- *theorem* cSup_intro
- \+/\- *theorem* cInf_intro
- \+/\- *theorem* cInf_le_cSup
- \+/\- *theorem* cSup_union
- \+/\- *theorem* cInf_union
- \+/\- *theorem* cSup_inter_le
- \+/\- *theorem* le_cInf_inter
- \+/\- *theorem* cSup_insert
- \+/\- *theorem* cInf_insert
- \+/\- *theorem* cinfi_const
- \+/\- *theorem* csupr_const
- \+/\- *theorem* cSup_intro'

Modified src/order/filter/basic.lean
- \+/\- *lemma* nonempty_of_mem_sets
- \+ *lemma* principal_ne_bot_iff
- \+/\- *lemma* comap_ne_bot
- \+/\- *lemma* nonempty_of_mem_sets
- \- *lemma* forall_sets_ne_empty_iff_ne_bot
- \+/\- *lemma* comap_ne_bot

Modified src/order/filter/lift.lean
- \+/\- *lemma* lift'_ne_bot_iff
- \+/\- *lemma* lift'_ne_bot_iff

Modified src/order/filter/pointwise.lean

Modified src/order/liminf_limsup.lean
- \+/\- *theorem* Limsup_principal
- \+/\- *theorem* Liminf_principal
- \+/\- *theorem* Limsup_principal
- \+/\- *theorem* Liminf_principal

Modified src/order/zorn.lean

Modified src/topology/algebra/infinite_sum.lean

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* nhds_principal_ne_bot_of_is_lub
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb
- \+/\- *lemma* mem_closure_of_is_lub
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *lemma* mem_closure_of_is_glb
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *lemma* nhds_principal_ne_bot_of_is_lub
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb
- \+/\- *lemma* mem_closure_of_is_lub
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *lemma* mem_closure_of_is_glb
- \+/\- *lemma* mem_of_is_glb_of_is_closed

Modified src/topology/algebra/uniform_group.lean

Modified src/topology/bases.lean

Modified src/topology/basic.lean
- \+/\- *lemma* dense_iff_inter_open
- \+/\- *lemma* dense_iff_inter_open
- \+/\- *theorem* mem_closure_iff
- \+/\- *theorem* mem_closure_iff_nhds
- \+/\- *theorem* mem_closure_iff
- \+/\- *theorem* mem_closure_iff_nhds

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/constructions.lean

Modified src/topology/continuous_on.lean

Modified src/topology/dense_embedding.lean

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* Sup_add
- \+/\- *lemma* Sup_add

Modified src/topology/instances/real.lean

Modified src/topology/metric_space/baire.lean
- \+/\- *theorem* nonempty_interior_of_Union_of_closed
- \+/\- *theorem* nonempty_interior_of_Union_of_closed

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* diam_union'
- \+/\- *lemma* diam_union'

Modified src/topology/metric_space/closeds.lean

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* diam_union'
- \+/\- *lemma* diam_union'

Modified src/topology/metric_space/gluing.lean

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* Hausdorff_edist_le_ediam
- \+/\- *lemma* Hausdorff_edist_empty
- \+ *lemma* nonempty_of_Hausdorff_edist_ne_top
- \+ *lemma* empty_or_nonempty_of_Hausdorff_edist_ne_top
- \+/\- *lemma* inf_edist_ne_top
- \+/\- *lemma* inf_dist_le_inf_dist_of_subset
- \+/\- *lemma* exists_dist_lt_of_inf_dist_lt
- \+/\- *lemma* mem_closure_iff_inf_dist_zero
- \+/\- *lemma* mem_iff_inf_dist_zero_of_closed
- \+ *lemma* Hausdorff_edist_ne_top_of_nonempty_of_bounded
- \+/\- *lemma* Hausdorff_dist_le_diam
- \+/\- *lemma* Hausdorff_edist_le_ediam
- \+/\- *lemma* Hausdorff_edist_empty
- \- *lemma* ne_empty_of_Hausdorff_edist_ne_top
- \+/\- *lemma* inf_edist_ne_top
- \+/\- *lemma* inf_dist_le_inf_dist_of_subset
- \+/\- *lemma* exists_dist_lt_of_inf_dist_lt
- \+/\- *lemma* mem_closure_iff_inf_dist_zero
- \+/\- *lemma* mem_iff_inf_dist_zero_of_closed
- \- *lemma* Hausdorff_edist_ne_top_of_ne_empty_of_bounded
- \+/\- *lemma* Hausdorff_dist_le_diam

Modified src/topology/metric_space/isometry.lean

Modified src/topology/opens.lean
- \+/\- *def* nonempty_compacts
- \+/\- *def* nonempty_compacts

Modified src/topology/order.lean

Modified src/topology/sequences.lean

Modified src/topology/subset_properties.lean

Modified src/topology/uniform_space/basic.lean

Modified src/topology/uniform_space/cauchy.lean

Modified src/topology/uniform_space/completion.lean

Modified src/topology/uniform_space/uniform_embedding.lean



## [2020-02-04 22:11:27](https://github.com/leanprover-community/mathlib/commit/253f75c)
feat(data/set/intervals): define intervals and prove basic properties ([#1949](https://github.com/leanprover-community/mathlib/pull/1949))
* things about intervals
* better documentation
* better file name
* add segment_eq_interval
* better proof for is_measurable_interval
* better import and better proof
* better proof
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_sub_min_eq_abs'
- \+ *lemma* max_sub_min_eq_abs

Modified src/analysis/convex/basic.lean
- \+ *lemma* segment_eq_interval

Modified src/data/indicator_function.lean
- \+ *lemma* indicator_apply
- \+ *lemma* indicator_comp_of_zero
- \+ *lemma* indicator_mul
- \+ *lemma* indicator_nonneg'
- \+ *lemma* indicator_nonneg
- \+ *lemma* indicator_nonpos'
- \+ *lemma* indicator_nonpos

Modified src/data/set/intervals/basic.lean
- \+ *lemma* Icc_inter_Icc_eq_singleton

Modified src/data/set/intervals/default.lean

Created src/data/set/intervals/unordered_interval.lean
- \+ *lemma* interval_of_le
- \+ *lemma* interval_of_ge
- \+ *lemma* interval_swap
- \+ *lemma* interval_of_lt
- \+ *lemma* interval_of_gt
- \+ *lemma* interval_of_not_le
- \+ *lemma* interval_of_not_ge
- \+ *lemma* interval_self
- \+ *lemma* nonempty_interval
- \+ *lemma* left_mem_interval
- \+ *lemma* right_mem_interval
- \+ *lemma* Icc_subset_interval
- \+ *lemma* Icc_subset_interval'
- \+ *lemma* mem_interval_of_le
- \+ *lemma* mem_interval_of_ge
- \+ *lemma* interval_subset_interval
- \+ *lemma* interval_subset_interval_iff_mem
- \+ *lemma* interval_subset_interval_iff_le
- \+ *lemma* interval_subset_interval_right
- \+ *lemma* interval_subset_interval_left
- \+ *lemma* bdd_below_bdd_above_iff_subset_interval
- \+ *lemma* abs_sub_le_of_subinterval
- \+ *lemma* abs_sub_left_of_mem_interval
- \+ *lemma* abs_sub_right_of_mem_interval
- \+ *def* interval

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_interval

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* real.volume_interval
- \+ *lemma* real.volume_lt_top_of_bounded
- \+ *lemma* real.volume_lt_top_of_compact

Modified src/order/bounds.lean
- \+ *lemma* bdd_below_iff_subset_Ici
- \+ *lemma* bdd_above_iff_subset_Iic
- \+ *lemma* bdd_below_bdd_above_iff_subset_Icc



## [2020-02-04 19:56:41](https://github.com/leanprover-community/mathlib/commit/475a669)
feat(topology/algebra/multilinear): define continuous multilinear maps ([#1948](https://github.com/leanprover-community/mathlib/pull/1948))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_smul

Created src/topology/algebra/multilinear.lean
- \+ *lemma* map_add
- \+ *lemma* map_smul
- \+ *lemma* map_sub
- \+ *lemma* map_coord_zero
- \+ *lemma* map_zero
- \+ *lemma* zero_apply
- \+ *lemma* add_apply
- \+ *lemma* neg_apply
- \+ *lemma* sub_apply
- \+ *lemma* cons_add
- \+ *lemma* cons_smul
- \+ *lemma* map_piecewise_smul
- \+ *lemma* map_smul_univ
- \+ *lemma* map_piecewise_add
- \+ *lemma* map_add_univ
- \+ *lemma* smul_apply
- \+ *theorem* ext
- \+ *def* to_continuous_linear_map
- \+ *def* to_multilinear_map_linear



## [2020-02-04 14:32:21](https://github.com/leanprover-community/mathlib/commit/9dbc894)
feat(number_theory/bernoulli): Add definition of Bernoulli numbers ([#1952](https://github.com/leanprover-community/mathlib/pull/1952))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers
* Remove old file
* Process comments
#### Estimated changes
Created src/number_theory/bernoulli.lean
- \+ *lemma* bernoulli_def'
- \+ *lemma* bernoulli_def
- \+ *lemma* bernoulli_zero
- \+ *lemma* bernoulli_one
- \+ *lemma* bernoulli_two
- \+ *lemma* bernoulli_three
- \+ *lemma* bernoulli_four
- \+ *lemma* sum_bernoulli
- \+ *def* bernoulli



## [2020-02-04 12:42:22](https://github.com/leanprover-community/mathlib/commit/c5febb5)
feat(tactic/lint): Three new linters, update illegal_constants ([#1947](https://github.com/leanprover-community/mathlib/pull/1947))
* add three new linters
* fix failing declarations
* restrict and rename illegal_constants linter
* update doc
* update ge_or_gt test
* update mk_nolint
* fix error
* Update scripts/mk_nolint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* clarify unfolds_to_class
* fix names since name is no longer protected
also change one declaration back to instance, since it did not cause a linter failure
* fix errors, move notes to docstrings
* add comments to docstring
* update mk_all.sh
* fix linter errors
#### Estimated changes
Modified docs/commands.md

Modified scripts/mk_all.sh

Modified scripts/mk_nolint.lean

Modified src/algebra/lie_algebra.lean
- \+ *def* lie_subalgebra_lie_algebra

Modified src/category/monad/writer.lean

Modified src/category_theory/adjunction/limits.lean
- \+ *def* left_adjoint_preserves_colimits
- \+ *def* right_adjoint_preserves_limits

Modified src/category_theory/concrete_category/bundled_hom.lean

Modified src/data/list/defs.lean
- \+ *def* is_nil
- \+ *def* indexes_values_aux
- \+ *def* indexes_values

Modified src/meta/expr.lean

Modified src/order/filter/filter_product.lean

Modified src/order/fixed_points.lean

Modified src/order/pilex.lean

Modified src/ring_theory/ideal_operations.lean

Modified src/tactic/core.lean

Modified src/tactic/lint.lean

Modified src/topology/algebra/uniform_ring.lean

Created test/expr.lean

Modified test/lint.lean
- \+ *lemma* foo.bar
- \+ *def* incorrect_type_class_argument_test



## [2020-02-03 13:52:06](https://github.com/leanprover-community/mathlib/commit/bfa7055)
feat(ring_theory/power_series): several simp lemmas ([#1945](https://github.com/leanprover-community/mathlib/pull/1945))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(ring_theory/power_series): several simp lemmas
* Remove file that shouldn't be there yet
* Update src/ring_theory/power_series.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Generalise lemma to canonically_ordered_monoid
* Update name
* Fix build
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* add_eq_zero_iff

Modified src/data/mv_polynomial.lean

Modified src/data/polynomial.lean

Modified src/ring_theory/power_series.lean
- \+ *lemma* coeff_mul_C
- \+ *lemma* coeff_zero_mul_X
- \+ *lemma* coeff_mul_C
- \+ *lemma* coeff_succ_mul_X
- \+ *lemma* coeff_zero_mul_X



## [2020-02-03 11:26:46](https://github.com/leanprover-community/mathlib/commit/6264667)
refactor(linear_algebra/multilinear): cleanup of multilinear maps ([#1921](https://github.com/leanprover-community/mathlib/pull/1921))
* staging [ci skip]
* staging
* staging
* cleanup norms
* complete currying
* docstrings
* docstrings
* cleanup
* nonterminal simp
* golf
* missing bits for derivatives
* sub_apply
* cleanup
* better docstrings
* remove two files
* reviewer's comments
* use fintype
* line too long
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_update_of_not_mem
- \+ *lemma* prod_update_of_mem
- \+ *lemma* sum_update_of_mem

Modified src/analysis/complex/basic.lean

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_le_of_mem_closed_ball
- \+ *lemma* norm_lt_of_mem_ball
- \+ *lemma* norm_le_pi_norm

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.mk_continuous_coe
- \+ *lemma* linear_map.mk_continuous_apply
- \+ *lemma* linear_map.mk_continuous_of_exists_bound_coe
- \+ *lemma* linear_map.mk_continuous_of_exists_bound_apply
- \+ *lemma* linear_map.mk_continuous_norm_le
- \- *lemma* linear_map_with_bound_coe
- \- *lemma* linear_map_with_bound_apply
- \+ *def* linear_map.mk_continuous
- \+ *def* linear_map.mk_continuous_of_exists_bound
- \- *def* linear_map.with_bound

Modified src/data/finset.lean
- \+ *lemma* update_eq_piecewise

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* mk_pi_ring_apply
- \+ *lemma* mk_pi_ring_apply_one_eq_self
- \+ *lemma* linear_map.uncurry_left_apply
- \+ *lemma* multilinear_map.curry_left_apply
- \+ *lemma* linear_map.curry_uncurry_left
- \+ *lemma* multilinear_map.uncurry_curry_left
- \+ *lemma* multilinear_map.uncurry_right_apply
- \+ *lemma* multilinear_map.curry_right_apply
- \+ *lemma* multilinear_map.curry_uncurry_right
- \+ *lemma* multilinear_map.uncurry_curry_right
- \+ *def* linear_map.uncurry_left
- \+ *def* multilinear_map.curry_left
- \+ *def* multilinear_curry_left_equiv
- \+ *def* multilinear_map.uncurry_right
- \+ *def* multilinear_map.curry_right
- \+ *def* multilinear_curry_right_equiv
- \- *def* linear_to_multilinear_equiv_multilinear
- \- *def* multilinear_to_linear_equiv_multilinear

Modified src/measure_theory/bochner_integration.lean

Modified src/topology/constructions.lean
- \+ *lemma* continuous_update

Modified src/topology/metric_space/basic.lean
- \+ *theorem* continuous_at_iff

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* continuous_at_of_locally_lipschitz



## [2020-02-03 09:55:20](https://github.com/leanprover-community/mathlib/commit/59629da)
chore(*): rename `filter.inhabited_of_mem_sets` to `nonempty_of_mem_sets` ([#1943](https://github.com/leanprover-community/mathlib/pull/1943))
In other names `inhabited` means that we have a `default` element.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean

Modified src/order/filter/bases.lean

Modified src/order/filter/basic.lean
- \+ *lemma* nonempty_of_mem_sets
- \- *lemma* inhabited_of_mem_sets

Modified src/order/liminf_limsup.lean

Modified src/topology/algebra/ordered.lean

Modified src/topology/dense_embedding.lean

Modified src/topology/metric_space/basic.lean

Modified src/topology/order.lean

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* seq
- \+/\- *def* seq

Modified src/topology/uniform_space/completion.lean

Modified src/topology/uniform_space/uniform_embedding.lean



## [2020-02-03 07:14:34](https://github.com/leanprover-community/mathlib/commit/a342132)
refactor(topology/metric_space/emetric_space): redefine `diam` ([#1941](https://github.com/leanprover-community/mathlib/pull/1941))
* feat(data/set/basic): define `set.subsingleton`
Also rename `nonempty.of_subset` to `nonempty.mono`
* Add a missing lemma
* refactor(topology/metric_space/emetric_space): redefine `diam`
* Give a more readable definition of `emetric.diam`;
* Add a few lemmas including diameter of a pair and of a triple of
  points;
* Simplify some proofs;
* Reformulate some theorems to use `∀ (x ∈ s) (y ∈ s)` instead
  of `∀ x y ∈ s` because the former plays better with existing `simp`
  lemmas.
* Redefine `set.subsingleton` using `(x ∈ s) (y ∈ s)`, prove `metric.diam_triangle`
#### Estimated changes
Modified src/analysis/convex/topology.lean

Modified src/data/real/ennreal.lean
- \+ *lemma* of_real_to_real_le
- \+ *lemma* add_ne_top
- \+ *lemma* max_zero_left
- \+ *lemma* max_zero_right
- \+ *lemma* sup_eq_max
- \+ *lemma* to_real_add_le
- \+ *lemma* to_real_max
- \+ *lemma* to_real_le_of_le_of_real

Modified src/data/set/basic.lean
- \+ *lemma* subsingleton.mono
- \+/\- *lemma* subsingleton_empty
- \+/\- *lemma* subsingleton_empty

Modified src/order/bounded_lattice.lean
- \+ *theorem* ne_top_of_le_ne_top

Modified src/topology/metric_space/basic.lean
- \+ *lemma* edist_lt_top
- \+/\- *lemma* diam_nonneg
- \+ *lemma* diam_subsingleton
- \+ *lemma* diam_pair
- \+ *lemma* diam_triple
- \+ *lemma* ediam_le_of_forall_dist_le
- \+/\- *lemma* diam_le_of_forall_dist_le
- \+ *lemma* diam_le_of_forall_dist_le_of_nonempty
- \+ *lemma* dist_le_diam_of_mem'
- \+ *lemma* bounded_iff_ediam_ne_top
- \+ *lemma* bounded.ediam_ne_top
- \+/\- *lemma* dist_le_diam_of_mem
- \+/\- *lemma* diam_nonneg
- \- *lemma* bounded_iff_diam_ne_top
- \+/\- *lemma* dist_le_diam_of_mem
- \+/\- *lemma* diam_le_of_forall_dist_le

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* diam_le_iff_forall_edist_le
- \+/\- *lemma* diam_le_of_forall_edist_le
- \+ *lemma* diam_subsingleton
- \+ *lemma* diam_eq_zero_iff
- \+ *lemma* diam_pos_iff
- \+ *lemma* diam_insert
- \+ *lemma* diam_pair
- \+ *lemma* diam_triple
- \+/\- *lemma* diam_mono
- \+/\- *lemma* diam_le_of_forall_edist_le
- \+/\- *lemma* diam_mono
- \+/\- *def* diam
- \+/\- *def* diam

Modified src/topology/metric_space/isometry.lean

Modified src/topology/metric_space/lipschitz.lean



## [2020-02-02 12:18:31](https://github.com/leanprover-community/mathlib/commit/1843bfc)
feat(algebra/pointwise): pointwise scalar-multiplication lemmas ([#1925](https://github.com/leanprover-community/mathlib/pull/1925))
* feat(algebra/pointwise): more lemmas about scaling sets
- rename `smul_set` to `scale_set` for disambiguation
- define `scale_set_action`, which subsumes `one_smul_set`
- additional lemmas lemmas
* fix(analysis/convex): refactor proofs for `scale_set`
* feat(algebra/pointwise): re-organise file
- subsume `pointwise_mul_action`
* feat(algebra/pointwise): remove `pointwise_mul_action`
- subsumed by `smul_set_action` with left-regular action.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* mem_smul_set
- \+/\- *lemma* smul_set_eq_image
- \+/\- *lemma* smul_set_eq_pointwise_smul_singleton
- \+ *lemma* smul_mem_smul_set
- \+ *lemma* smul_set_union
- \+ *lemma* smul_set_empty
- \+ *lemma* smul_set_mono
- \+ *lemma* mem_inv_smul_set_iff
- \+ *lemma* mem_smul_set_iff_inv_smul_mem
- \+/\- *lemma* mem_smul_set
- \+/\- *lemma* smul_set_eq_image
- \+/\- *lemma* smul_set_eq_pointwise_smul_singleton
- \- *lemma* one_smul_set
- \+/\- *def* pointwise_smul
- \+/\- *def* smul_set
- \+ *def* smul_set_action
- \- *def* pointwise_mul_action
- \+/\- *def* pointwise_smul
- \+/\- *def* smul_set

Modified src/analysis/convex/basic.lean

Modified src/analysis/convex/topology.lean



## [2020-02-02 10:49:49](https://github.com/leanprover-community/mathlib/commit/58899d4)
feat(data/set/basic): define `set.subsingleton` ([#1939](https://github.com/leanprover-community/mathlib/pull/1939))
* feat(data/set/basic): define `set.subsingleton`
Also rename `nonempty.of_subset` to `nonempty.mono`
* Add a missing lemma
#### Estimated changes
Modified src/data/finset.lean

Modified src/data/set/basic.lean
- \+ *lemma* nonempty.mono
- \+ *lemma* nonempty_of_ssubset'
- \+ *lemma* eq_empty_or_nonempty
- \+ *lemma* subset_diff_union
- \+ *lemma* nonempty.image
- \+ *lemma* nonempty.of_image
- \+ *lemma* nonempty_image_iff
- \+ *lemma* subsingleton.image
- \+ *lemma* subsingleton.eq_singleton_of_mem
- \+ *lemma* subsingleton_empty
- \+ *lemma* subsingleton_singleton
- \+ *lemma* subsingleton.eq_empty_or_singleton
- \- *lemma* nonempty.of_subset
- \- *lemma* nonempty.of_ssubset'
- \- *lemma* subset_insert_diff
- \- *lemma* nonempty_image
- \+ *theorem* bex_insert_iff
- \+ *theorem* image_pair

Modified src/order/filter/bases.lean



## [2020-02-02 01:12:16](https://github.com/leanprover-community/mathlib/commit/bacd4da)
chore(data/subtype): fix `∀` vs `Π` ([#1940](https://github.com/leanprover-community/mathlib/pull/1940))
#### Estimated changes
Modified src/data/subtype.lean
- \+/\- *lemma* restrict_apply
- \+/\- *lemma* restrict_apply
- \+/\- *def* restrict
- \+/\- *def* restrict



## [2020-02-01 23:40:10](https://github.com/leanprover-community/mathlib/commit/11b9497)
feat(data/fintype): range_prod_eq_univ_prod ([#1937](https://github.com/leanprover-community/mathlib/pull/1937))
* feat(algebra/big_operators): range_prod_eq_univ_prod
* fix build, part 1
* fix build, part 2
* fix build, part 3
* Fix build, part 4
#### Estimated changes
Modified src/data/fintype.lean
- \+ *lemma* finset.range_prod_eq_univ_prod



## [2020-02-01 18:15:45](https://github.com/leanprover-community/mathlib/commit/6e6e6da)
feat(data/nat/basic): two identities for `choose` ([#1936](https://github.com/leanprover-community/mathlib/pull/1936))
* feat(data/nat/basic): two identities for `choose`
* fix build
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* choose_succ_self_right
- \+ *lemma* choose_mul_succ_eq



## [2020-02-01 16:26:13](https://github.com/leanprover-community/mathlib/commit/a500c24)
Update units.lean ([#1938](https://github.com/leanprover-community/mathlib/pull/1938))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_mk_of_mul_eq_one



## [2020-02-01 10:59:44](https://github.com/leanprover-community/mathlib/commit/50bbb8d)
fix(data/nat/basic): make arguments to `choose_succ_right_eq` explicit ([#1935](https://github.com/leanprover-community/mathlib/pull/1935))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+/\- *lemma* choose_succ_right_eq
- \+/\- *lemma* choose_succ_right_eq

