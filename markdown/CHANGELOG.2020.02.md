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
- \+/\- *lemma* omega.int.clauses_sat_dnf_core
- \+/\- *def* omega.int.dnf
- \+/\- *def* omega.int.dnf_core
- \+/\- *lemma* omega.int.implies_neg_elim
- \+/\- *def* omega.int.is_nnf
- \+/\- *lemma* omega.int.is_nnf_nnf
- \+/\- *lemma* omega.int.is_nnf_push_neg
- \+/\- *def* omega.int.neg_elim
- \+/\- *def* omega.int.neg_free
- \+/\- *lemma* omega.int.neg_free_neg_elim
- \+/\- *def* omega.int.nnf
- \+/\- *lemma* omega.int.nnf_equiv
- \+/\- *def* omega.int.push_neg
- \+/\- *lemma* omega.int.unsat_of_clauses_unsat

Modified src/tactic/omega/int/form.lean
- \- *def* omega.int.form.equiv
- \- *def* omega.int.form.fresh_index
- \- *def* omega.int.form.holds
- \- *def* omega.int.form.implies
- \- *def* omega.int.form.repr
- \- *def* omega.int.form.sat
- \- *lemma* omega.int.form.sat_of_implies_of_sat
- \- *lemma* omega.int.form.sat_or
- \- *def* omega.int.form.unsat
- \- *def* omega.int.form.valid
- \+ *def* omega.int.preform.equiv
- \+ *def* omega.int.preform.fresh_index
- \+ *def* omega.int.preform.holds
- \+ *def* omega.int.preform.implies
- \+ *def* omega.int.preform.repr
- \+ *def* omega.int.preform.sat
- \+ *lemma* omega.int.preform.sat_of_implies_of_sat
- \+ *lemma* omega.int.preform.sat_or
- \+ *def* omega.int.preform.unsat
- \+ *def* omega.int.preform.valid
- \+/\- *def* omega.int.univ_close
- \+/\- *lemma* omega.int.univ_close_of_valid
- \+/\- *lemma* omega.int.valid_of_unsat_not

Modified src/tactic/omega/int/main.lean
- \+/\- *lemma* omega.int.univ_close_of_unsat_clausify

Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/lin_comb.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean
- \+/\- *def* omega.nat.dnf
- \+/\- *def* omega.nat.dnf_core
- \+/\- *lemma* omega.nat.exists_clause_holds
- \+/\- *lemma* omega.nat.exists_clause_sat
- \+/\- *lemma* omega.nat.unsat_of_unsat_dnf

Modified src/tactic/omega/nat/form.lean
- \- *def* omega.nat.form.equiv
- \- *def* omega.nat.form.fresh_index
- \- *def* omega.nat.form.holds
- \- *lemma* omega.nat.form.holds_constant
- \- *def* omega.nat.form.implies
- \- *def* omega.nat.form.neg_free
- \- *def* omega.nat.form.repr
- \- *def* omega.nat.form.sat
- \- *lemma* omega.nat.form.sat_of_implies_of_sat
- \- *lemma* omega.nat.form.sat_or
- \- *def* omega.nat.form.sub_free
- \- *def* omega.nat.form.unsat
- \- *def* omega.nat.form.valid
- \+ *def* omega.nat.preform.equiv
- \+ *def* omega.nat.preform.fresh_index
- \+ *def* omega.nat.preform.holds
- \+ *lemma* omega.nat.preform.holds_constant
- \+ *def* omega.nat.preform.implies
- \+ *def* omega.nat.preform.neg_free
- \+ *def* omega.nat.preform.repr
- \+ *def* omega.nat.preform.sat
- \+ *lemma* omega.nat.preform.sat_of_implies_of_sat
- \+ *lemma* omega.nat.preform.sat_or
- \+ *def* omega.nat.preform.sub_free
- \+ *def* omega.nat.preform.unsat
- \+ *def* omega.nat.preform.valid
- \+/\- *def* omega.nat.univ_close
- \+/\- *lemma* omega.nat.univ_close_of_valid
- \+/\- *lemma* omega.nat.valid_of_unsat_not

Modified src/tactic/omega/nat/main.lean
- \+/\- *lemma* omega.nat.univ_close_of_unsat_neg_elim_not

Modified src/tactic/omega/nat/neg_elim.lean
- \+/\- *lemma* omega.nat.implies_neg_elim
- \+/\- *lemma* omega.nat.implies_neg_elim_core
- \+/\- *def* omega.nat.is_nnf
- \+/\- *lemma* omega.nat.is_nnf_nnf
- \+/\- *lemma* omega.nat.is_nnf_push_neg
- \+/\- *def* omega.nat.neg_elim
- \+/\- *def* omega.nat.neg_elim_core
- \+/\- *lemma* omega.nat.neg_free_neg_elim
- \+/\- *def* omega.nat.nnf
- \+/\- *lemma* omega.nat.nnf_equiv
- \+/\- *def* omega.nat.push_neg

Modified src/tactic/omega/nat/preterm.lean


Modified src/tactic/omega/nat/sub_elim.lean
- \- *def* omega.nat.form.sub_subst
- \- *def* omega.nat.form.sub_terms
- \+/\- *def* omega.nat.is_diff
- \+ *def* omega.nat.preform.sub_subst
- \+ *def* omega.nat.preform.sub_terms
- \+/\- *lemma* omega.nat.sat_sub_elim
- \+/\- *def* omega.nat.sub_elim
- \+/\- *def* omega.nat.sub_elim_core
- \+/\- *def* omega.nat.sub_fresh_index
- \+/\- *lemma* omega.nat.unsat_of_unsat_sub_elim

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
- \+ *lemma* submodule.le_div_iff
- \+ *lemma* submodule.mem_div_iff_forall_mul_mem
- \+ *lemma* submodule.mem_div_iff_smul_subset

Added src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.bot_eq_zero
- \+ *lemma* ring.fractional_ideal.coe_mem_one
- \+ *lemma* ring.fractional_ideal.div_nonzero
- \+ *lemma* ring.fractional_ideal.div_one
- \+ *lemma* ring.fractional_ideal.eq_zero_iff
- \+ *lemma* ring.fractional_ideal.ext
- \+ *lemma* ring.fractional_ideal.fractional_div_of_nonzero
- \+ *lemma* ring.fractional_ideal.fractional_inf
- \+ *lemma* ring.fractional_ideal.fractional_mul
- \+ *lemma* ring.fractional_ideal.fractional_of_subset_one
- \+ *lemma* ring.fractional_ideal.fractional_sup
- \+ *lemma* ring.fractional_ideal.inv_nonzero
- \+ *lemma* ring.fractional_ideal.le_iff
- \+ *lemma* ring.fractional_ideal.mem_one_iff
- \+ *lemma* ring.fractional_ideal.mem_zero_iff
- \+ *lemma* ring.fractional_ideal.mul_left_mono
- \+ *lemma* ring.fractional_ideal.mul_right_mono
- \+ *lemma* ring.fractional_ideal.nonzero_iff_val_nonzero
- \+ *theorem* ring.fractional_ideal.right_inverse_eq
- \+ *lemma* ring.fractional_ideal.sup_eq_add
- \+ *lemma* ring.fractional_ideal.val_add
- \+ *lemma* ring.fractional_ideal.val_mul
- \+ *lemma* ring.fractional_ideal.val_zero
- \+ *lemma* ring.fractional_ideal.zero_le
- \+ *def* ring.fractional_ideal
- \+ *def* ring.is_fractional

Modified src/ring_theory/localization.lean
- \+ *lemma* localization.coe_mul_eq_smul
- \+ *lemma* localization.coe_smul
- \+ *def* localization.is_integer
- \+ *lemma* localization.is_integer_add
- \+ *lemma* localization.is_integer_coe
- \+ *lemma* localization.is_integer_mul
- \+ *lemma* localization.is_integer_smul
- \+ *def* localization.lin_coe
- \+ *lemma* localization.lin_coe_apply
- \+ *lemma* localization.mul_coe_eq_smul
- \+ *lemma* localization.of_id
- \+ *lemma* localization.of_smul



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
- \+ *lemma* with_top.add_one_le_of_lt

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* continuous_linear_equiv.comp_times_cont_diff_on_iff
- \+ *lemma* continuous_linear_equiv.times_cont_diff_on_comp_iff
- \+ *lemma* continuous_linear_map.times_cont_diff
- \+ *def* formal_multilinear_series.shift
- \+ *def* formal_multilinear_series.unshift
- \+ *def* formal_multilinear_series
- \+ *def* ftaylor_series
- \+ *def* ftaylor_series_within
- \+ *lemma* ftaylor_series_within_univ
- \+ *lemma* has_ftaylor_series_up_to.continuous
- \+ *lemma* has_ftaylor_series_up_to.differentiable
- \+ *lemma* has_ftaylor_series_up_to.has_fderiv_at
- \+ *lemma* has_ftaylor_series_up_to.has_ftaylor_series_up_to_on
- \+ *lemma* has_ftaylor_series_up_to.of_le
- \+ *lemma* has_ftaylor_series_up_to.zero_eq'
- \+ *lemma* has_ftaylor_series_up_to_on.comp_continuous_linear_map
- \+ *lemma* has_ftaylor_series_up_to_on.congr
- \+ *lemma* has_ftaylor_series_up_to_on.continuous_linear_map_comp
- \+ *lemma* has_ftaylor_series_up_to_on.continuous_on
- \+ *lemma* has_ftaylor_series_up_to_on.differentiable_on
- \+ *theorem* has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on
- \+ *lemma* has_ftaylor_series_up_to_on.has_fderiv_within_at
- \+ *lemma* has_ftaylor_series_up_to_on.mono
- \+ *lemma* has_ftaylor_series_up_to_on.of_le
- \+ *lemma* has_ftaylor_series_up_to_on.prod
- \+ *lemma* has_ftaylor_series_up_to_on.zero_eq'
- \+ *theorem* has_ftaylor_series_up_to_on_succ_iff_left
- \+ *theorem* has_ftaylor_series_up_to_on_succ_iff_right
- \+ *lemma* has_ftaylor_series_up_to_on_top_iff
- \+ *lemma* has_ftaylor_series_up_to_on_univ_iff
- \+ *lemma* has_ftaylor_series_up_to_on_zero_iff
- \+ *theorem* has_ftaylor_series_up_to_succ_iff_right
- \+ *lemma* has_ftaylor_series_up_to_zero_iff
- \- *def* iterated_continuous_linear_map.normed_group_rec
- \- *def* iterated_continuous_linear_map.normed_space_rec
- \- *def* iterated_continuous_linear_map
- \- *def* iterated_fderiv
- \+ *lemma* iterated_fderiv_one_apply
- \- *lemma* iterated_fderiv_succ
- \+ *lemma* iterated_fderiv_succ_apply_left
- \+ *theorem* iterated_fderiv_succ_apply_right
- \+ *lemma* iterated_fderiv_succ_eq_comp_left
- \+ *lemma* iterated_fderiv_succ_eq_comp_right
- \- *def* iterated_fderiv_within
- \+/\- *lemma* iterated_fderiv_within_congr
- \+ *lemma* iterated_fderiv_within_inter'
- \+/\- *lemma* iterated_fderiv_within_inter
- \+/\- *lemma* iterated_fderiv_within_inter_open
- \+ *lemma* iterated_fderiv_within_one_apply
- \- *lemma* iterated_fderiv_within_succ
- \+ *lemma* iterated_fderiv_within_succ_apply_left
- \+ *theorem* iterated_fderiv_within_succ_apply_right
- \+ *lemma* iterated_fderiv_within_succ_eq_comp_left
- \+ *lemma* iterated_fderiv_within_succ_eq_comp_right
- \+ *lemma* iterated_fderiv_within_univ
- \- *theorem* iterated_fderiv_within_univ
- \- *lemma* iterated_fderiv_within_zero
- \+ *lemma* iterated_fderiv_within_zero_apply
- \+ *lemma* iterated_fderiv_within_zero_eq_comp
- \+ *lemma* iterated_fderiv_within_zero_fun
- \- *lemma* iterated_fderiv_zero
- \+ *lemma* iterated_fderiv_zero_apply
- \+ *lemma* iterated_fderiv_zero_eq_comp
- \+ *lemma* times_cont_diff.comp_continuous_linear_map
- \- *lemma* times_cont_diff.comp_is_bounded_linear
- \+/\- *lemma* times_cont_diff.continuous
- \+/\- *lemma* times_cont_diff.continuous_fderiv
- \+/\- *lemma* times_cont_diff.continuous_fderiv_apply
- \+ *lemma* times_cont_diff.continuous_linear_map_comp
- \+ *lemma* times_cont_diff.differentiable
- \+/\- *lemma* times_cont_diff.of_le
- \- *lemma* times_cont_diff.of_succ
- \+/\- *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \+/\- *lemma* times_cont_diff.times_cont_diff_on
- \- *def* times_cont_diff
- \+ *lemma* times_cont_diff_iff_continuous_differentiable
- \- *theorem* times_cont_diff_iff_times_cont_diff_rec
- \+ *lemma* times_cont_diff_of_differentiable_iterated_fderiv
- \+/\- *lemma* times_cont_diff_on.comp
- \+ *lemma* times_cont_diff_on.comp_continuous_linear_map
- \- *lemma* times_cont_diff_on.comp_is_bounded_linear
- \+/\- *lemma* times_cont_diff_on.congr
- \- *lemma* times_cont_diff_on.congr_mono'
- \+/\- *lemma* times_cont_diff_on.congr_mono
- \+ *lemma* times_cont_diff_on.continuous_linear_map_comp
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+/\- *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* times_cont_diff_on.continuous_on_iterated_fderiv_within
- \+/\- *lemma* times_cont_diff_on.differentiable_on
- \+ *lemma* times_cont_diff_on.differentiable_on_iterated_fderiv_within
- \+ *lemma* times_cont_diff_on.fderiv_within
- \+ *theorem* times_cont_diff_on.ftaylor_series_within
- \+/\- *lemma* times_cont_diff_on.mono
- \- *lemma* times_cont_diff_on.of_succ
- \- *def* times_cont_diff_on
- \+ *lemma* times_cont_diff_on_congr
- \+/\- *lemma* times_cont_diff_on_const
- \- *lemma* times_cont_diff_on_fderiv_within
- \- *lemma* times_cont_diff_on_fderiv_within_nat
- \+ *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on
- \+ *theorem* times_cont_diff_on_iff_ftaylor_series
- \- *theorem* times_cont_diff_on_iff_times_cont_diff_on_rec
- \+ *lemma* times_cont_diff_on_nat
- \+ *lemma* times_cont_diff_on_of_continuous_on_differentiable_on
- \+ *lemma* times_cont_diff_on_of_differentiable_on
- \+/\- *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \- *lemma* times_cont_diff_on_rec.continuous_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on_rec.differentiable_on
- \- *lemma* times_cont_diff_on_rec.of_succ
- \- *def* times_cont_diff_on_rec
- \- *lemma* times_cont_diff_on_rec_succ
- \- *lemma* times_cont_diff_on_rec_univ
- \- *lemma* times_cont_diff_on_rec_zero
- \- *lemma* times_cont_diff_on_succ
- \+ *theorem* times_cont_diff_on_succ_iff_fderiv_within
- \+ *theorem* times_cont_diff_on_succ_iff_has_fderiv_within_at
- \+ *theorem* times_cont_diff_on_top_iff_fderiv_within
- \+ *theorem* times_cont_diff_on_univ
- \- *lemma* times_cont_diff_on_univ
- \- *lemma* times_cont_diff_rec.continuous
- \- *lemma* times_cont_diff_rec.differentiable
- \- *lemma* times_cont_diff_rec.of_succ
- \- *def* times_cont_diff_rec
- \- *lemma* times_cont_diff_rec_succ
- \- *lemma* times_cont_diff_rec_zero
- \- *lemma* times_cont_diff_succ
- \+ *theorem* times_cont_diff_succ_iff_fderiv
- \+/\- *lemma* times_cont_diff_top
- \+ *theorem* times_cont_diff_top_iff_fderiv
- \+ *lemma* times_cont_diff_zero_fun

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_left
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_right
- \+ *lemma* is_bounded_bilinear_map_comp_multilinear
- \+ *lemma* is_bounded_linear_map_continuous_multilinear_map_comp_linear
- \+ *lemma* is_bounded_linear_map_prod_multilinear

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
- \+ *def* finsupp.comap_domain
- \+/\- *def* finsupp.frange
- \+/\- *lemma* finsupp.map_domain_id
- \+/\- *lemma* finsupp.neg_apply
- \+/\- *lemma* finsupp.one_def
- \+/\- *lemma* finsupp.single_apply
- \+/\- *lemma* finsupp.single_eq_of_ne
- \+/\- *lemma* finsupp.single_eq_same
- \+/\- *lemma* finsupp.smul_apply'
- \+ *def* finsupp.split
- \+ *def* finsupp.split_comp
- \+/\- *lemma* finsupp.sub_apply
- \+/\- *lemma* finsupp.support_zero
- \+/\- *lemma* finsupp.zero_apply



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
- \+ *def* fin_succ_equiv
- \+ *def* fin_zero_equiv'

Modified src/data/mv_polynomial.lean
- \+ *theorem* mv_polynomial.exists_fin_rename
- \+ *theorem* mv_polynomial.exists_finset_rename

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/polynomial.lean
- \- *theorem* is_noetherian_ring_mv_polynomial_fin
- \- *theorem* is_noetherian_ring_mv_polynomial_of_fintype
- \- *theorem* is_noetherian_ring_polynomial
- \+ *def* mv_polynomial.integral_domain_fintype
- \+ *lemma* mv_polynomial.is_integral_domain_fin
- \+ *lemma* mv_polynomial.is_integral_domain_fintype
- \+ *theorem* mv_polynomial.is_noetherian_ring_fin



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
- \- *theorem* list.append_foldl
- \- *theorem* list.append_foldr
- \+ *lemma* list.map_nil
- \+ *theorem* list.prod_singleton



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



## [2020-02-25 16:06:50](https://github.com/leanprover-community/mathlib/commit/089d058)
feat(tactic/lint): linter for commutativity lemmas that are marked simp ([#2045](https://github.com/leanprover-community/mathlib/pull/2045))
* feat(tactic/lint): linter for commutativity lemmas that are marked simp
* chore(*): remove simp from commutativity lemmas
* doc(*): document simp_comm linter
#### Estimated changes
Modified docs/commands.md


Modified src/data/finmap.lean
- \+/\- *theorem* finmap.erase_erase

Modified src/data/finset.lean
- \+/\- *theorem* finset.inter_comm
- \+/\- *theorem* finset.inter_left_comm
- \+/\- *theorem* finset.inter_right_comm
- \+/\- *theorem* finset.union_comm

Modified src/data/hash_map.lean


Modified src/data/list/alist.lean
- \+/\- *theorem* alist.erase_erase

Modified src/data/list/basic.lean
- \+/\- *theorem* list.disjoint_comm
- \+ *theorem* list.disjoint_nil_right

Modified src/data/multiset.lean
- \+/\- *theorem* multiset.disjoint_comm

Modified src/data/nat/dist.lean
- \+/\- *theorem* nat.dist_comm

Modified src/linear_algebra/basis.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/infinite_sum.lean


Added test/lint_simp_comm.lean
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
- \+ *lemma* bdd_above.insert
- \+ *lemma* bdd_above.inter_of_left
- \+ *lemma* bdd_above.inter_of_right
- \- *lemma* bdd_above.mk
- \+ *lemma* bdd_above.mono
- \+ *lemma* bdd_above.union
- \+/\- *def* bdd_above
- \+ *lemma* bdd_above_Icc
- \+ *lemma* bdd_above_Ico
- \+ *lemma* bdd_above_Iic
- \+ *lemma* bdd_above_Iio
- \+ *lemma* bdd_above_Ioc
- \+ *lemma* bdd_above_Ioo
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_above_iff_subset_Iic
- \+/\- *lemma* bdd_above_insert
- \- *lemma* bdd_above_inter_left
- \- *lemma* bdd_above_inter_right
- \- *lemma* bdd_above_of_bdd_above_of_monotone
- \+/\- *lemma* bdd_above_singleton
- \- *lemma* bdd_above_subset
- \- *lemma* bdd_above_top
- \+/\- *lemma* bdd_above_union
- \+ *lemma* bdd_below.insert
- \+ *lemma* bdd_below.inter_of_left
- \+ *lemma* bdd_below.inter_of_right
- \- *lemma* bdd_below.mk
- \+ *lemma* bdd_below.mono
- \+ *lemma* bdd_below.union
- \+/\- *def* bdd_below
- \+ *lemma* bdd_below_Ici
- \+ *lemma* bdd_below_Ioi
- \+/\- *lemma* bdd_below_bdd_above_iff_subset_Icc
- \- *lemma* bdd_below_bot
- \+/\- *lemma* bdd_below_empty
- \+/\- *lemma* bdd_below_iff_subset_Ici
- \+/\- *lemma* bdd_below_insert
- \- *lemma* bdd_below_inter_left
- \- *lemma* bdd_below_inter_right
- \- *lemma* bdd_below_of_bdd_below_of_monotone
- \+/\- *lemma* bdd_below_singleton
- \- *lemma* bdd_below_subset
- \+/\- *lemma* bdd_below_union
- \- *lemma* eq_of_is_glb_of_is_glb
- \- *lemma* eq_of_is_greatest_of_is_greatest
- \- *lemma* eq_of_is_least_of_is_least
- \- *lemma* eq_of_is_lub_of_is_lub
- \+ *lemma* is_glb.bdd_below
- \+ *lemma* is_glb.insert
- \+ *lemma* is_glb.lower_bounds_eq
- \+ *lemma* is_glb.nonempty
- \+ *lemma* is_glb.of_subset_of_superset
- \+ *lemma* is_glb.union
- \+ *lemma* is_glb.unique
- \+/\- *lemma* is_glb_Icc
- \+/\- *lemma* is_glb_Ici
- \+/\- *lemma* is_glb_Ico
- \+/\- *lemma* is_glb_Ioc
- \+/\- *lemma* is_glb_Ioi
- \+/\- *lemma* is_glb_Ioo
- \+/\- *lemma* is_glb_empty
- \- *lemma* is_glb_iff_eq_of_is_glb
- \- *lemma* is_glb_iff_inf_eq
- \- *lemma* is_glb_insert_inf
- \+ *lemma* is_glb_le_is_lub
- \+/\- *lemma* is_glb_lt_iff
- \+ *lemma* is_glb_pair
- \+/\- *lemma* is_glb_singleton
- \- *lemma* is_glb_union_inf
- \+ *lemma* is_glb_univ
- \+ *lemma* is_greatest.bdd_above
- \+ *lemma* is_greatest.insert
- \+ *lemma* is_greatest.is_greatest_iff_eq
- \+ *lemma* is_greatest.is_lub
- \+ *lemma* is_greatest.nonempty
- \+ *lemma* is_greatest.union
- \+ *lemma* is_greatest.unique
- \+ *lemma* is_greatest.upper_bounds_eq
- \+ *lemma* is_greatest_Icc
- \+ *lemma* is_greatest_Iic
- \+ *lemma* is_greatest_Ioc
- \- *lemma* is_greatest_iff_eq_of_is_greatest
- \+ *lemma* is_greatest_pair
- \+ *lemma* is_greatest_singleton
- \+ *lemma* is_greatest_union_iff
- \+ *lemma* is_greatest_univ
- \+ *lemma* is_least.bdd_below
- \+ *lemma* is_least.insert
- \+ *lemma* is_least.is_glb
- \+ *lemma* is_least.is_least_iff_eq
- \+ *lemma* is_least.lower_bounds_eq
- \+ *lemma* is_least.nonempty
- \+ *lemma* is_least.union
- \+ *lemma* is_least.unique
- \+ *lemma* is_least_Icc
- \+ *lemma* is_least_Ici
- \+ *lemma* is_least_Ico
- \- *lemma* is_least_iff_eq_of_is_least
- \+ *lemma* is_least_pair
- \+ *lemma* is_least_singleton
- \+ *lemma* is_least_union_iff
- \+ *lemma* is_least_univ
- \+ *lemma* is_lub.bdd_above
- \+ *lemma* is_lub.insert
- \+ *lemma* is_lub.nonempty
- \+ *lemma* is_lub.of_subset_of_superset
- \+ *lemma* is_lub.union
- \+ *lemma* is_lub.unique
- \+ *lemma* is_lub.upper_bounds_eq
- \+/\- *lemma* is_lub_Icc
- \+/\- *lemma* is_lub_Ico
- \+/\- *lemma* is_lub_Iic
- \+/\- *lemma* is_lub_Iio
- \+/\- *lemma* is_lub_Ioc
- \+/\- *lemma* is_lub_Ioo
- \+/\- *lemma* is_lub_empty
- \- *lemma* is_lub_iff_eq_of_is_lub
- \- *lemma* is_lub_iff_sup_eq
- \- *lemma* is_lub_insert_sup
- \+/\- *lemma* is_lub_le_iff
- \+ *lemma* is_lub_lt_iff
- \+ *lemma* is_lub_pair
- \+/\- *lemma* is_lub_singleton
- \- *lemma* is_lub_union_sup
- \+ *lemma* is_lub_univ
- \+/\- *lemma* le_is_glb_iff
- \+ *lemma* lower_bound_Ioc
- \+ *lemma* lower_bounds_Icc
- \+ *lemma* lower_bounds_Ici
- \+ *lemma* lower_bounds_Ico
- \+ *lemma* lower_bounds_Ioi
- \+ *lemma* lower_bounds_Ioo
- \+ *lemma* lower_bounds_empty
- \+ *lemma* lower_bounds_insert
- \+ *lemma* lower_bounds_le_upper_bounds
- \+/\- *lemma* lower_bounds_mono
- \+ *lemma* lower_bounds_mono_mem
- \+ *lemma* lower_bounds_mono_set
- \+ *lemma* lower_bounds_singleton
- \+ *lemma* lower_bounds_union
- \+ *lemma* lt_is_glb_iff
- \+/\- *lemma* lt_is_lub_iff
- \- *lemma* mem_lower_bounds_image
- \- *lemma* mem_upper_bounds_image
- \+ *lemma* monotone.is_lub_image_le
- \+ *lemma* monotone.le_is_glb_image_le
- \+ *lemma* monotone.map_bdd_above
- \+ *lemma* monotone.map_bdd_below
- \+ *lemma* monotone.map_is_greatest
- \+ *lemma* monotone.map_is_least
- \+ *lemma* monotone.mem_lower_bounds_image
- \+ *lemma* monotone.mem_upper_bounds_image
- \+ *lemma* no_bot_order.lower_bounds_univ
- \+ *lemma* no_top_order.upper_bounds_univ
- \- *lemma* nonempty_of_is_glb
- \- *lemma* nonempty_of_is_lub
- \+ *lemma* order_bot.lower_bounds_univ
- \+ *lemma* order_top.upper_bounds_univ
- \+ *lemma* union_lower_bounds_subset_lower_bounds_inter
- \+ *lemma* union_upper_bounds_subset_upper_bounds_inter
- \+ *lemma* upper_bounds_Icc
- \+ *lemma* upper_bounds_Ico
- \+ *lemma* upper_bounds_Iic
- \+ *lemma* upper_bounds_Iio
- \+ *lemma* upper_bounds_Ioc
- \+ *lemma* upper_bounds_Ioo
- \+ *lemma* upper_bounds_empty
- \+ *lemma* upper_bounds_insert
- \+/\- *lemma* upper_bounds_mono
- \+ *lemma* upper_bounds_mono_mem
- \+ *lemma* upper_bounds_mono_set
- \+ *lemma* upper_bounds_singleton
- \+ *lemma* upper_bounds_union

Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+/\- *theorem* lattice.Inf_le_Sup
- \+ *theorem* lattice.Inf_pair
- \+ *theorem* lattice.Sup_pair
- \+/\- *theorem* lattice.infi_const
- \+/\- *lemma* lattice.is_glb_Inf
- \- *lemma* lattice.is_glb_iff_Inf_eq
- \- *lemma* lattice.is_glb_iff_infi_eq
- \+/\- *lemma* lattice.is_glb_infi
- \+/\- *lemma* lattice.is_lub_Sup
- \- *lemma* lattice.is_lub_iff_Sup_eq
- \- *lemma* lattice.is_lub_iff_supr_eq
- \+/\- *lemma* lattice.is_lub_supr
- \+/\- *theorem* lattice.supr_const

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* lattice.cInf_Ici
- \+/\- *theorem* lattice.cInf_insert
- \- *lemma* lattice.cInf_interval
- \+/\- *theorem* lattice.cInf_le_cSup
- \- *theorem* lattice.cInf_of_mem_of_le
- \+/\- *theorem* lattice.cInf_union
- \+ *lemma* lattice.cSup_Iic
- \+/\- *theorem* lattice.cSup_insert
- \- *lemma* lattice.cSup_interval
- \+/\- *theorem* lattice.cSup_le_iff
- \- *theorem* lattice.cSup_of_mem_of_le
- \+/\- *theorem* lattice.cSup_union
- \+/\- *lemma* lattice.is_glb_cInf
- \+/\- *lemma* lattice.is_lub_cSup
- \+/\- *theorem* lattice.le_cInf_iff

Modified src/order/galois_connection.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/instances/ennreal.lean




## [2020-02-25 12:27:02](https://github.com/leanprover-community/mathlib/commit/a227e06)
Unify naming of lemmas related to the (co)lim functor ([#2040](https://github.com/leanprover-community/mathlib/pull/2040))
#### Estimated changes
Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/limits/limits.lean
- \- *lemma* category_theory.limits.colim.ι_map
- \+ *lemma* category_theory.limits.colimit.ι_map
- \- *lemma* category_theory.limits.lim.map_π
- \+ *lemma* category_theory.limits.limit.map_π

Modified src/topology/sheaves/stalks.lean




## [2020-02-25 10:39:52](https://github.com/leanprover-community/mathlib/commit/f77cb57)
chore(data/fintype): move  results depending on big_operators ([#2044](https://github.com/leanprover-community/mathlib/pull/2044))
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/data/fintype.lean
- \- *lemma* card_vector
- \- *theorem* fin.prod_univ_cast_succ
- \- *theorem* fin.prod_univ_succ
- \- *theorem* fin.prod_univ_zero
- \- *theorem* fin.sum_univ_cast_succ
- \- *theorem* fin.sum_univ_succ
- \- *lemma* finset.prod_attach_univ
- \- *lemma* finset.range_prod_eq_univ_prod
- \- *lemma* fintype.card_eq_sum_ones
- \- *lemma* fintype.card_fun
- \- *lemma* fintype.card_pi
- \- *theorem* fintype.card_sigma
- \- *theorem* fintype.card_sum

Added src/data/fintype/card.lean
- \+ *lemma* card_vector
- \+ *theorem* fin.prod_univ_cast_succ
- \+ *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_zero
- \+ *theorem* fin.sum_univ_cast_succ
- \+ *theorem* fin.sum_univ_succ
- \+ *lemma* finset.prod_attach_univ
- \+ *lemma* finset.range_prod_eq_univ_prod
- \+ *lemma* fintype.card_eq_sum_ones
- \+ *lemma* fintype.card_fun
- \+ *lemma* fintype.card_pi
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


Added src/order/copy.lean
- \+ *def* lattice.bounded_lattice.copy
- \+ *def* lattice.complete_distrib_lattice.copy
- \+ *def* lattice.complete_lattice.copy
- \+ *def* lattice.conditionally_complete_lattice.copy
- \+ *def* lattice.distrib_lattice.copy

Modified src/order/filter/basic.lean
- \- *def* lattice.complete_lattice.copy

Modified src/topology/opens.lean




## [2020-02-24 23:51:03](https://github.com/leanprover-community/mathlib/commit/5770369)
refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric ([#2051](https://github.com/leanprover-community/mathlib/pull/2051))
* refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric; it is automatic
* Alternative constructor for isometric bijections
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.isometry_inv_fun
- \+ *def* isometric.mk'



## [2020-02-24 22:06:59](https://github.com/leanprover-community/mathlib/commit/3ff50d9)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-02-24 19:58:16](https://github.com/leanprover-community/mathlib/commit/fb878e7)
feat(tactic/lint): add linter for simp lemmas whose lhs has a variable as head symbol ([#2038](https://github.com/leanprover-community/mathlib/pull/2038))
#### Estimated changes
Modified docs/commands.md


Modified src/algebra/field.lean
- \+/\- *lemma* is_ring_hom.map_div
- \+/\- *lemma* is_ring_hom.map_inv

Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map.map_add
- \+/\- *lemma* is_linear_map.map_neg
- \+/\- *lemma* is_linear_map.map_sub
- \+/\- *lemma* is_linear_map.map_zero

Modified src/data/list/basic.lean
- \+/\- *theorem* list.find_some

Modified src/tactic/lint.lean


Added test/lint_simp_var_head.lean




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
- \+/\- *def* functor.const

Modified src/category/monad/writer.lean


Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/number_theory/pell.lean
- \+/\- *def* pell.pell

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.mem_at_top_sets

Modified src/order/lattice.lean


Modified src/ring_theory/algebra.lean
- \+/\- *def* algebra.comap

Modified src/ring_theory/localization.lean


Modified src/set_theory/ordinal.lean
- \+/\- *def* cardinal.ord_eq_min
- \+/\- *def* ordinal.div_def

Modified src/tactic/core.lean


Modified src/tactic/interactive.lean
- \+/\- *lemma* tactic.interactive.{u}

Modified src/tactic/linarith.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* topological_fiber_bundle_core.base
- \+/\- *def* topological_fiber_bundle_core.fiber
- \+/\- *def* topological_fiber_bundle_core.index
- \+/\- *def* topological_fiber_bundle_core.total_space

Modified src/topology/uniform_space/cauchy.lean


Modified test/lint.lean
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
- \+/\- *theorem* set.compl_image_set_of
- \+/\- *lemma* set.empty_diff
- \+/\- *lemma* set.exists_of_ssubset
- \+/\- *theorem* set.mem_image
- \+/\- *theorem* set.mem_of_eq_of_mem
- \+/\- *theorem* set.mem_of_mem_of_subset
- \+/\- *lemma* set.sep_set_of
- \+/\- *theorem* set.set_of_subset_set_of
- \+/\- *lemma* set.univ_eq_empty_iff



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
- \+/\- *def* topological_space.nonempty_compacts.to_closeds

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* complete_space_iff_is_complete_univ

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* complete_space_coe_iff_is_complete
- \+ *lemma* complete_space_congr
- \+ *lemma* complete_space_iff_is_complete_range
- \+ *lemma* is_closed.complete_space_coe
- \+ *lemma* is_complete.complete_space_coe
- \+ *lemma* is_complete_of_complete_image
- \+ *lemma* uniform_embedding_set_inclusion
- \+ *lemma* uniform_embedding_subtype_coe
- \+ *lemma* uniform_embedding_subtype_val



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
- \+ *lemma* ennreal.div_le_of_le_mul
- \+ *lemma* ennreal.mul_lt_of_lt_div

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean
- \+ *lemma* contracting_with.dist_le
- \+/\- *def* contracting_with

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/lipschitz.lean
- \+/\- *lemma* lipschitz_with.diam_image_le
- \+/\- *lemma* lipschitz_with.ediam_image_le
- \+ *lemma* lipschitz_with.edist_iterate_succ_le_geometric
- \+ *lemma* lipschitz_with.edist_le
- \- *lemma* lipschitz_with.edist_map_le
- \+ *lemma* lipschitz_with.nndist_le
- \- *lemma* lipschitz_with.nndist_map_le
- \+/\- *def* lipschitz_with
- \+ *lemma* lipschitz_with_iff_dist_le



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
- \+ *lemma* submodule.mem_supr
- \+ *lemma* submodule.span_singleton_le_iff_mem
- \+ *lemma* submodule.supr_eq_span

Modified src/linear_algebra/finsupp.lean
- \+/\- *theorem* finsupp.mem_span_iff_total
- \+/\- *lemma* linear_map.map_finsupp_total
- \+ *lemma* submodule.exists_finset_of_mem_supr

Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.le_supr_iff



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
- \+ *lemma* set.range_inclusion

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_ne_bot_of_image_mem

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.is_closed_ball_top
- \+ *lemma* prod.edist_eq



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
- \+ *def* Module.kernel_cone
- \+ *def* Module.kernel_is_limit
- \+ *lemma* Module.of_apply

Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* category_theory.limits.coequalizer.condition
- \+ *lemma* category_theory.limits.cone_parallel_pair_ext
- \+ *lemma* category_theory.limits.cone_parallel_pair_left
- \+ *lemma* category_theory.limits.cone_parallel_pair_right
- \+ *def* category_theory.limits.cone_parallel_pair_self
- \+ *lemma* category_theory.limits.cone_parallel_pair_self_X
- \+ *lemma* category_theory.limits.cone_parallel_pair_self_π_app_zero
- \+ *def* category_theory.limits.epi_limit_cone_parallel_pair_is_iso
- \+/\- *lemma* category_theory.limits.equalizer.condition
- \+ *lemma* category_theory.limits.equalizer.hom_ext
- \+ *lemma* category_theory.limits.equalizer.ι.eq_app_zero
- \+ *lemma* category_theory.limits.equalizer.ι.fork
- \+ *lemma* category_theory.limits.equalizer.ι_mono
- \+ *lemma* category_theory.limits.fork.eq_of_ι_ι
- \+ *def* category_theory.limits.is_limit_cone_parallel_pair_self
- \+ *def* category_theory.limits.limit_cone_parallel_pair_self_is_iso

Added src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.cokernel.condition
- \+ *lemma* category_theory.limits.kernel.condition
- \+ *def* category_theory.limits.kernel.is_limit_cone_zero_cone
- \+ *def* category_theory.limits.kernel.zero_cone
- \+ *def* category_theory.limits.kernel.ι_zero_is_iso

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.has_initial_of_unique
- \+ *def* category_theory.limits.has_terminal_of_unique

Added src/category_theory/limits/shapes/zero.lean
- \+ *def* category_theory.limits.has_zero_object.has_initial_of_has_zero_object
- \+ *def* category_theory.limits.has_zero_object.has_terminal_of_has_zero_object
- \+ *def* category_theory.limits.has_zero_object.zero_morphisms_of_zero_object
- \+ *lemma* category_theory.limits.has_zero_object.zero_of_from_zero
- \+ *lemma* category_theory.limits.has_zero_object.zero_of_to_zero
- \+ *lemma* category_theory.limits.zero_of_comp_epi
- \+ *lemma* category_theory.limits.zero_of_comp_mono
- \+ *def* category_theory.limits.zero_of_zero_object



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
- \+ *lemma* category_theory.nat_trans.of_homs_app

Modified src/category_theory/equivalence.lean


Added src/category_theory/limits/shapes/constructions/binary_products.lean
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
- \+/\- *lemma* finset.sum_boole_mul
- \+/\- *lemma* finset.sum_mul_boole

Modified src/algebra/field.lean
- \- *theorem* units.mk0_inv

Modified src/algebra/group_power.lean
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* one_div_pow

Modified src/algebra/ring.lean
- \+ *lemma* ite_mul

Modified src/algebraic_geometry/prime_spectrum.lean
- \+/\- *lemma* prime_spectrum.zero_locus_bot
- \+ *lemma* prime_spectrum.zero_locus_singleton_zero

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.apply_zero_curry0
- \+/\- *lemma* continuous_multilinear_map.curry0_norm
- \+ *lemma* continuous_multilinear_map.fin0_apply_norm
- \+/\- *lemma* continuous_multilinear_map.uncurry0_curry0

Modified src/category_theory/const.lean
- \+/\- *def* category_theory.functor.const_comp
- \- *lemma* category_theory.functor.const_comp_hom_app
- \- *lemma* category_theory.functor.const_comp_inv_app

Modified src/category_theory/equivalence.lean
- \+/\- *lemma* category_theory.equivalence.functor_unit_comp

Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean
- \+ *lemma* category_theory.nat_trans.vcomp_app'

Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* category_theory.functor.map_hom_inv
- \+/\- *lemma* category_theory.functor.map_inv_hom

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.ι_cocone_morphism
- \+/\- *lemma* category_theory.limits.limit.cone_morphism_π

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.symmetry'
- \+/\- *lemma* category_theory.limits.coprod.symmetry
- \+ *lemma* category_theory.limits.prod.symmetry'
- \+/\- *lemma* category_theory.limits.prod.symmetry

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* category_theory.limits.cospan_map_id
- \+/\- *lemma* category_theory.limits.span_map_id

Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* category_theory.nat_iso.naturality_1
- \+/\- *lemma* category_theory.nat_iso.naturality_2

Modified src/category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.vcomp_app

Modified src/data/equiv/denumerable.lean
- \+/\- *theorem* denumerable.decode_is_some

Modified src/data/fin.lean


Modified src/data/finset.lean
- \+ *lemma* finset.inf_singleton'
- \+/\- *lemma* finset.inf_singleton
- \+ *theorem* finset.insert_singleton_self_eq'
- \+/\- *theorem* finset.insert_singleton_self_eq
- \+/\- *theorem* finset.max_singleton
- \+ *theorem* finset.min_singleton'
- \+/\- *theorem* finset.min_singleton
- \+ *lemma* finset.sup_singleton'
- \+/\- *lemma* finset.sup_singleton
- \+/\- *theorem* finset.supr_union

Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_coe_nat'
- \+/\- *theorem* int.cast_of_nat

Modified src/data/int/parity.lean
- \+/\- *theorem* int.mod_two_ne_zero
- \+ *theorem* int.two_dvd_ne_zero

Modified src/data/list/alist.lean
- \+/\- *theorem* alist.insert_insert_of_ne

Modified src/data/list/basic.lean
- \+/\- *theorem* list.concat_append
- \+/\- *theorem* list.concat_cons
- \+/\- *theorem* list.concat_ne_nil
- \+/\- *theorem* list.concat_nil
- \+/\- *theorem* list.count_concat
- \+/\- *theorem* list.exists_mem_cons_iff
- \+ *theorem* list.infix_append'
- \+/\- *theorem* list.infix_append
- \+/\- *theorem* list.length_concat
- \+/\- *theorem* list.prefix_concat

Modified src/data/list/sigma.lean
- \+/\- *theorem* list.lookup_kinsert
- \+/\- *theorem* list.lookup_kinsert_ne
- \+/\- *theorem* list.mem_keys_kinsert

Modified src/data/multiset.lean
- \+/\- *lemma* multiset.map_singleton
- \+/\- *lemma* multiset.prod_map_one
- \+/\- *lemma* multiset.sum_map_zero

Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.coeff_neg
- \+ *lemma* mv_polynomial.rename_neg

Modified src/data/option/basic.lean
- \+ *lemma* option.lift_or_get_none_left
- \+ *lemma* option.lift_or_get_none_right
- \+ *lemma* option.lift_or_get_some_some

Modified src/data/set/basic.lean
- \+/\- *theorem* set.nmem_set_of_eq
- \+/\- *theorem* set.subset_preimage_univ

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.bInter_empty
- \+/\- *theorem* set.bInter_univ
- \+/\- *theorem* set.bUnion_empty
- \+/\- *theorem* set.bUnion_univ

Modified src/data/zsqrtd/basic.lean
- \+/\- *theorem* zsqrtd.of_int_im
- \+/\- *theorem* zsqrtd.of_int_re

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.lintegral_nnnorm_zero

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_on_zero

Modified src/order/complete_lattice.lean
- \+/\- *theorem* lattice.infi_emptyset
- \+/\- *theorem* lattice.infi_insert
- \+/\- *theorem* lattice.infi_pair
- \+/\- *theorem* lattice.infi_singleton
- \+/\- *theorem* lattice.infi_union
- \+/\- *theorem* lattice.infi_univ
- \+/\- *theorem* lattice.supr_emptyset
- \+/\- *theorem* lattice.supr_insert
- \+/\- *theorem* lattice.supr_pair
- \+/\- *theorem* lattice.supr_singleton
- \+/\- *theorem* lattice.supr_union
- \+/\- *theorem* lattice.supr_univ

Modified src/order/filter/filter_product.lean
- \+/\- *lemma* filter.filter_product.abs_def
- \+/\- *lemma* filter.filter_product.of_seq_one
- \+/\- *lemma* filter.filter_product.of_seq_zero

Modified src/ring_theory/localization.lean
- \+/\- *lemma* localization.coe_is_unit'
- \+/\- *lemma* localization.coe_is_unit
- \+/\- *lemma* localization.coe_mul_mk
- \+/\- *lemma* localization.lift'_mk
- \+/\- *lemma* localization.mk_mul_mk
- \+/\- *lemma* localization.to_units_coe

Modified src/ring_theory/power_series.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/zfc.lean
- \+ *lemma* Set.eval_mk
- \+/\- *theorem* pSet.resp.eval_val

Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.self_comp_symm'
- \+/\- *lemma* continuous_linear_equiv.self_comp_symm
- \+ *lemma* continuous_linear_equiv.symm_comp_self'
- \+/\- *lemma* continuous_linear_equiv.symm_comp_self

Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* local_homeomorph.of_set_inv_fun
- \+/\- *lemma* local_homeomorph.of_set_source
- \+/\- *lemma* local_homeomorph.of_set_symm
- \+/\- *lemma* local_homeomorph.of_set_target
- \+/\- *lemma* local_homeomorph.of_set_to_fun
- \+/\- *lemma* local_homeomorph.prod_inv_fun
- \+/\- *lemma* local_homeomorph.prod_source
- \+/\- *lemma* local_homeomorph.prod_target
- \+/\- *lemma* local_homeomorph.prod_to_fun
- \+/\- *lemma* local_homeomorph.refl_inv_fun
- \+/\- *lemma* local_homeomorph.refl_source
- \+/\- *lemma* local_homeomorph.refl_target
- \+/\- *lemma* local_homeomorph.refl_to_fun
- \+/\- *lemma* local_homeomorph.restr_inv_fun
- \+/\- *lemma* local_homeomorph.restr_open_source
- \+/\- *lemma* local_homeomorph.restr_source
- \+/\- *lemma* local_homeomorph.restr_target
- \+/\- *lemma* local_homeomorph.restr_to_fun
- \+/\- *lemma* local_homeomorph.symm_inv_fun
- \+/\- *lemma* local_homeomorph.symm_source
- \+/\- *lemma* local_homeomorph.symm_target
- \+/\- *lemma* local_homeomorph.symm_to_fun
- \+/\- *lemma* local_homeomorph.trans_inv_fun
- \+/\- *lemma* local_homeomorph.trans_to_fun

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.diam_pair
- \+/\- *lemma* metric.diam_triple

Added test/lint_simp_nf.lean
- \+ *def* c
- \+ *lemma* c_eq_d
- \+ *def* d
- \+ *def* f
- \+ *lemma* f_c
- \+ *def* h
- \+ *lemma* h_c



## [2020-02-21 11:26:12](https://github.com/leanprover-community/mathlib/commit/bb7631f)
feat(algebraic_geometry/prime_spectrum): vanishing ideal ([#1972](https://github.com/leanprover-community/mathlib/pull/1972))
* wip
* wip
* Remove stuff for next PR
* Update prime_spectrum.lean
* Process comments
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \- *lemma* prime_spectrum.Inter_zero_locus
- \+ *lemma* prime_spectrum.coe_vanishing_ideal
- \+ *lemma* prime_spectrum.gc
- \+ *lemma* prime_spectrum.gc_set
- \+ *lemma* prime_spectrum.is_closed_zero_locus
- \+ *lemma* prime_spectrum.le_vanishing_ideal_zero_locus
- \+ *lemma* prime_spectrum.mem_vanishing_ideal
- \+ *lemma* prime_spectrum.subset_vanishing_ideal_zero_locus
- \+ *lemma* prime_spectrum.subset_zero_locus_iff_le_vanishing_ideal
- \+ *lemma* prime_spectrum.subset_zero_locus_iff_subset_vanishing_ideal
- \+ *lemma* prime_spectrum.subset_zero_locus_vanishing_ideal
- \+ *lemma* prime_spectrum.sup_vanishing_ideal_le
- \+/\- *lemma* prime_spectrum.union_zero_locus
- \- *lemma* prime_spectrum.union_zero_locus_ideal
- \+ *def* prime_spectrum.vanishing_ideal
- \+ *lemma* prime_spectrum.vanishing_ideal_Union
- \+ *lemma* prime_spectrum.vanishing_ideal_union
- \+ *lemma* prime_spectrum.vanishing_ideal_univ
- \+/\- *lemma* prime_spectrum.zero_locus_Union
- \+ *lemma* prime_spectrum.zero_locus_bot
- \+ *lemma* prime_spectrum.zero_locus_empty
- \+ *lemma* prime_spectrum.zero_locus_empty_iff_eq_top
- \+ *lemma* prime_spectrum.zero_locus_inf
- \- *lemma* prime_spectrum.zero_locus_is_closed
- \+ *lemma* prime_spectrum.zero_locus_sup
- \+ *lemma* prime_spectrum.zero_locus_supr
- \+ *lemma* prime_spectrum.zero_locus_union
- \+ *lemma* prime_spectrum.zero_locus_vanishing_ideal_eq_closure



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
- \- *lemma* continuous_linear_map.norm_map_tail_right_le
- \+ *lemma* continuous_multilinear_curry_fin0_apply
- \+ *lemma* continuous_multilinear_curry_fin0_symm_apply
- \+ *def* continuous_multilinear_curry_fin1
- \+ *lemma* continuous_multilinear_curry_fin1_apply
- \+ *lemma* continuous_multilinear_curry_fin1_symm_apply
- \+ *lemma* continuous_multilinear_curry_left_equiv_apply
- \+ *lemma* continuous_multilinear_curry_left_equiv_symm_apply
- \+ *lemma* continuous_multilinear_curry_right_equiv_apply
- \+ *lemma* continuous_multilinear_curry_right_equiv_symm_apply
- \+ *lemma* continuous_multilinear_map.norm_map_init_le
- \+ *lemma* continuous_multilinear_map.norm_map_snoc_le
- \- *lemma* continuous_multilinear_map.norm_map_tail_left_le
- \+ *lemma* continuous_multilinear_map.uncurry0_apply

Modified src/linear_algebra/multilinear.lean
- \+ *def* linear_map.comp_multilinear_map
- \+ *def* multilinear_map.comp_linear_map
- \+ *def* multilinear_map.prod
- \+ *lemma* multilinear_map.snoc_add
- \+ *lemma* multilinear_map.snoc_smul
- \+/\- *def* multilinear_map.uncurry_right

Modified src/topology/algebra/multilinear.lean
- \+ *def* continuous_linear_map.comp_continuous_multilinear_map
- \+ *lemma* continuous_linear_map.comp_continuous_multilinear_map_coe
- \+ *def* continuous_multilinear_map.comp_continuous_linear_map
- \+ *def* continuous_multilinear_map.prod
- \+ *lemma* continuous_multilinear_map.prod_apply



## [2020-02-20 15:52:23-08:00](https://github.com/leanprover-community/mathlib/commit/eeedc6a)
fix(*): remove loopy simp lemmas ([#2026](https://github.com/leanprover-community/mathlib/pull/2026))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.conj_comp

Modified src/order/basic.lean
- \+/\- *lemma* order_dual.dual_le
- \+/\- *lemma* order_dual.dual_lt



## [2020-02-20 21:25:20](https://github.com/leanprover-community/mathlib/commit/b0eeea4)
fix(data/bool): remove simp attribute from commutativity lemmas ([#2027](https://github.com/leanprover-community/mathlib/pull/2027))
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *theorem* bool.band_comm
- \+/\- *theorem* bool.band_left_comm
- \+/\- *theorem* bool.bor_comm
- \+/\- *theorem* bool.bor_left_comm
- \+/\- *theorem* bool.bxor_comm
- \+/\- *theorem* bool.bxor_left_comm

Modified src/data/int/basic.lean
- \+ *lemma* int.bodd_coe



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
- \+/\- *def* units.coe_hom
- \+/\- *lemma* units.coe_hom_apply
- \+ *lemma* units.coe_lift_right
- \+/\- *lemma* units.coe_map'
- \+/\- *lemma* units.coe_map
- \+ *def* units.lift_right
- \+/\- *def* units.map'
- \+/\- *def* units.map
- \+/\- *lemma* units.map_comp
- \+/\- *lemma* units.map_id



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
- \+ *lemma* deriv_fpow
- \+ *lemma* deriv_within_fpow
- \+ *lemma* differentiable_at_fpow
- \+ *lemma* differentiable_on_fpow
- \+ *lemma* differentiable_within_at_fpow
- \+ *lemma* has_deriv_at_fpow
- \+ *theorem* has_deriv_within_at_fpow
- \+ *lemma* iter_deriv_fpow
- \+ *lemma* iter_deriv_pow'
- \+ *lemma* iter_deriv_pow

Added src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_exp
- \+ *lemma* convex_on_fpow
- \+ *lemma* convex_on_pow
- \+ *lemma* convex_on_pow_of_even
- \+ *lemma* finset.prod_nonneg_of_card_nonpos_even
- \+ *lemma* int_prod_range_nonneg

Added src/analysis/mean_inequalities.lean
- \+ *theorem* nnreal.am_gm2_weighted
- \+ *theorem* nnreal.am_gm3_weighted
- \+ *theorem* nnreal.am_gm_weighted
- \+ *theorem* nnreal.pow_am_le_am_pow
- \+ *theorem* nnreal.young_inequality
- \+ *theorem* real.am_gm2_weighted
- \+ *theorem* real.am_gm_weighted
- \+ *theorem* real.fpow_am_le_am_fpow
- \+ *theorem* real.pow_am_le_am_pow
- \+ *theorem* real.pow_am_le_am_pow_of_even
- \+ *theorem* real.young_inequality

Modified src/data/nat/parity.lean
- \+ *theorem* nat.even.add
- \+ *theorem* nat.even.sub

Modified src/data/real/nnreal.lean
- \+ *theorem* nnreal.coe_mk

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.compl_Ici
- \+ *lemma* set.compl_Iic
- \+ *lemma* set.compl_Iio
- \+ *lemma* set.compl_Ioi

Modified src/topology/algebra/ordered.lean
- \+ *lemma* interior_Icc
- \+ *lemma* interior_Ici
- \+ *lemma* interior_Ico
- \+ *lemma* interior_Iic
- \+ *lemma* interior_Iio
- \+ *lemma* interior_Ioc
- \+ *lemma* interior_Ioi
- \+ *lemma* interior_Ioo
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
- \+ *lemma* submodule.smul_mem_iff'

Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* normed_field.punctured_nhds_ne_bot
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
- \- *lemma* is_unit.map'
- \- *lemma* is_unit.map
- \- *def* is_unit
- \- *theorem* is_unit_iff_exists_inv'
- \- *theorem* is_unit_iff_exists_inv
- \- *theorem* is_unit_nat
- \- *theorem* is_unit_of_mul_is_unit_left
- \- *theorem* is_unit_of_mul_is_unit_right
- \- *theorem* is_unit_of_mul_one
- \- *theorem* is_unit_one
- \- *lemma* is_unit_unit
- \- *theorem* units.is_unit_mul_units

Modified src/algebra/group/default.lean


Added src/algebra/group/is_unit.lean
- \+ *lemma* is_unit.map'
- \+ *lemma* is_unit.map
- \+ *def* is_unit
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_nat
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* is_unit_of_mul_one
- \+ *theorem* is_unit_one
- \+ *lemma* is_unit_unit
- \+ *theorem* units.is_unit_mul_units

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
Added roadmap/todo.lean


Added roadmap/topology/paracompact.lean
- \+ *lemma* normal_of_paracompact_t2
- \+ *lemma* paracompact_of_compact
- \+ *lemma* paracompact_of_metric
- \+ *lemma* paracompact_space.precise_refinement

Added roadmap/topology/shrinking_lemma.lean
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
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_zero

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
- \+ *lemma* filter.tendsto.smul
- \+ *lemma* tendsto_smul

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
- \+ *lemma* is_open_map.image_mem_nhds
- \+/\- *def* is_open_map
- \+/\- *lemma* is_open_map_iff_nhds_le



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
- \+ *lemma* fin.cast_succ_fin_succ
- \+ *lemma* fin.comp_cons
- \+ *lemma* fin.comp_init
- \+ *lemma* fin.comp_snoc
- \+ *lemma* fin.comp_tail
- \+ *lemma* fin.cons_snoc_eq_snoc_cons
- \+ *lemma* fin.eq_last_of_not_lt
- \+ *def* fin.init
- \+ *lemma* fin.init_snoc
- \+ *lemma* fin.init_update_cast_succ
- \+ *lemma* fin.init_update_last
- \+ *def* fin.snoc
- \+ *lemma* fin.snoc_cast_succ
- \+ *lemma* fin.snoc_init_self
- \+ *lemma* fin.snoc_last
- \+ *lemma* fin.snoc_update
- \+ *lemma* fin.succ_last
- \+ *lemma* fin.tail_init_eq_init_tail
- \+ *lemma* fin.update_snoc_last

Modified src/data/fintype.lean
- \+ *theorem* fin.prod_univ_cast_succ
- \+ *theorem* fin.sum_univ_cast_succ
- \+ *lemma* fin.univ_cast_succ

Modified src/logic/function.lean
- \+ *lemma* function.comp_update



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
- \+ *def* linear_map.smul_rightₗ
- \+ *lemma* linear_map.smul_rightₗ_apply

Added src/linear_algebra/contraction.lean
- \+ *def* contract_left
- \+ *lemma* contract_left_apply
- \+ *def* contract_right
- \+ *lemma* contract_right_apply
- \+ *def* dual_tensor_hom
- \+ *lemma* dual_tensor_hom_apply



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
- \+ *theorem* compact_iff_finite_subfamily_closed
- \+ *theorem* compact_of_finite_subfamily_closed
- \+ *theorem* compact_space_of_finite_subfamily_closed
- \+/\- *lemma* set.finite.compact_bUnion



## [2020-02-17 21:45:03](https://github.com/leanprover-community/mathlib/commit/bbf5d1a)
refactor(algebra/field): partially migrate to bundled homs ([#1999](https://github.com/leanprover-community/mathlib/pull/1999))
* refactor(algebra/field): partially migrate to bundled homs
* Add a few `@[simp]` attrs
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* is_ring_hom.injective
- \+/\- *lemma* is_ring_hom.map_div'
- \+/\- *lemma* is_ring_hom.map_div
- \+/\- *lemma* is_ring_hom.map_eq_zero
- \+/\- *lemma* is_ring_hom.map_inv'
- \+/\- *lemma* is_ring_hom.map_inv
- \+/\- *lemma* is_ring_hom.map_ne_zero
- \+ *lemma* ring_hom.injective
- \+ *lemma* ring_hom.map_div'
- \+ *lemma* ring_hom.map_div
- \+ *lemma* ring_hom.map_eq_zero
- \+ *lemma* ring_hom.map_inv'
- \+ *lemma* ring_hom.map_inv
- \+ *lemma* ring_hom.map_ne_zero

Modified src/algebra/field_power.lean
- \+ *lemma* ring_hom.map_fpow'
- \+ *lemma* ring_hom.map_fpow

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



## [2020-02-17 17:00:24](https://github.com/leanprover-community/mathlib/commit/5f06692)
feat(data/set/intervals): add `Ici_subset_Ici`, `Iic_subset_Iic` ([#2003](https://github.com/leanprover-community/mathlib/pull/2003))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ici_subset_Ici
- \+ *lemma* set.Iic_subset_Iic



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


Added src/tactic/rename_var.lean


Added test/rename_var.lean




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

Modified src/algebra/group_power.lean
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* add_monoid.add_smul
- \+/\- *theorem* add_monoid.mul_smul'
- \+/\- *theorem* add_monoid.mul_smul
- \+/\- *theorem* add_monoid.mul_smul_assoc
- \+/\- *theorem* add_monoid.mul_smul_left
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* add_monoid.one_smul
- \+/\- *def* add_monoid.smul
- \+/\- *theorem* add_monoid.smul_add
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* add_monoid.smul_eq_mul
- \+/\- *theorem* add_monoid.smul_le_smul
- \+/\- *lemma* add_monoid.smul_le_smul_of_le_right
- \+/\- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* add_monoid.smul_one
- \+/\- *theorem* add_monoid.smul_sub
- \+/\- *theorem* add_monoid.smul_zero
- \+/\- *theorem* add_monoid.zero_smul
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+/\- *theorem* add_monoid_hom.map_smul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* bit0_gsmul
- \+/\- *theorem* bit0_smul
- \+/\- *theorem* bit1_gsmul
- \+/\- *theorem* bit1_smul
- \+/\- *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \+/\- *theorem* canonically_ordered_semiring.pow_le_one
- \+/\- *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \+/\- *theorem* canonically_ordered_semiring.pow_pos
- \+/\- *theorem* div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *def* gpow
- \+/\- *theorem* gpow_add
- \+/\- *theorem* gpow_add_one
- \+/\- *theorem* gpow_bit0
- \+/\- *theorem* gpow_bit1
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gpow_mul'
- \+/\- *theorem* gpow_mul
- \+/\- *theorem* gpow_mul_comm
- \+/\- *theorem* gpow_neg
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* gpow_neg_succ
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gpow_one
- \+/\- *theorem* gpow_one_add
- \+/\- *theorem* gpow_zero
- \+/\- *def* gsmul
- \+/\- *theorem* gsmul_add
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* gsmul_neg
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* gsmul_sub
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* inv_gpow
- \+/\- *lemma* inv_pow'
- \+/\- *theorem* inv_pow
- \- *theorem* is_add_group_hom.gsmul
- \- *theorem* is_add_group_hom.map_gsmul
- \- *theorem* is_add_group_hom.map_smul
- \+/\- *theorem* is_add_monoid_hom.map_smul
- \- *theorem* is_group_hom.map_gpow
- \- *theorem* is_group_hom.map_pow
- \+/\- *theorem* is_monoid_hom.map_pow
- \+ *lemma* is_semiring_hom.map_pow
- \- *theorem* is_semiring_hom.map_pow
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* list.sum_repeat
- \+/\- *lemma* lt_of_pow_lt_pow
- \+/\- *def* monoid.pow
- \+/\- *theorem* monoid_hom.map_gpow
- \+/\- *theorem* monoid_hom.map_pow
- \+/\- *theorem* mul_gpow
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* mul_gsmul_left
- \+/\- *theorem* mul_pow
- \+/\- *theorem* nat.cast_pow
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *lemma* neg_one_pow_eq_pow_mod_two
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* one_gpow
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* one_le_pow_of_one_le
- \+/\- *theorem* one_pow
- \+/\- *lemma* pow_abs
- \+/\- *theorem* pow_add
- \+/\- *theorem* pow_bit0
- \+/\- *theorem* pow_bit1
- \+/\- *lemma* pow_div
- \+/\- *lemma* pow_dvd_pow
- \+/\- *theorem* pow_eq_zero
- \+/\- *lemma* pow_inv
- \+/\- *theorem* pow_inv_comm
- \+/\- *lemma* pow_le_one
- \+/\- *theorem* pow_le_pow
- \+/\- *lemma* pow_le_pow_of_le_left
- \+/\- *lemma* pow_le_pow_of_le_one
- \+/\- *lemma* pow_lt_pow
- \+/\- *theorem* pow_lt_pow_of_lt_left
- \+/\- *lemma* pow_lt_pow_of_lt_one
- \+/\- *theorem* pow_mul'
- \+/\- *theorem* pow_mul
- \+/\- *theorem* pow_mul_comm'
- \+/\- *theorem* pow_mul_comm
- \+/\- *theorem* pow_ne_zero
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_one
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_right_inj
- \+/\- *theorem* pow_sub
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_succ
- \+/\- *theorem* pow_two
- \+/\- *theorem* pow_two_nonneg
- \+/\- *theorem* pow_zero
- \+/\- *lemma* ring_hom.map_pow
- \+/\- *theorem* smul_add_comm'
- \+/\- *theorem* smul_add_comm
- \+/\- *theorem* sq_sub_sq
- \+/\- *theorem* succ_smul'
- \+/\- *theorem* succ_smul
- \+/\- *theorem* two_smul
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* with_bot.coe_smul
- \+/\- *theorem* zero_gsmul
- \+/\- *lemma* zero_pow

Modified src/algebra/lie_algebra.lean


Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* real.angle.coe_gsmul
- \+ *lemma* real.angle.coe_smul

Modified src/category_theory/conj.lean


Modified src/group_theory/quotient_group.lean




## [2020-02-17 07:29:08](https://github.com/leanprover-community/mathlib/commit/d673e55)
feat(ring_theory/algebra): add ext_iff ([#1996](https://github.com/leanprover-community/mathlib/pull/1996))
* feat(ring_theory/algebra): add ext_iff
* also add eq_top_iff
* Update src/ring_theory/algebra.lean
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *theorem* algebra.eq_top_iff
- \+ *theorem* subalgebra.ext_iff



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



## [2020-02-15 23:38:34](https://github.com/leanprover-community/mathlib/commit/c7eb6f8)
chore(algebra/group/hom): add a missing `simp` lemma ([#1994](https://github.com/leanprover-community/mathlib/pull/1994))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.coe_mk



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


Added src/tactic/hint.lean


Modified src/tactic/linarith.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/ring.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tidy.lean


Added test/hint.lean




## [2020-02-15 09:59:41](https://github.com/leanprover-community/mathlib/commit/0b6d398)
chore(algebra/group/basic): rename type vars ([#1989](https://github.com/leanprover-community/mathlib/pull/1989))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* add_sub_cancel'_right
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* bit0_zero
- \+/\- *lemma* bit1_zero
- \+/\- *theorem* eq_iff_eq_of_sub_eq_sub
- \+/\- *theorem* eq_inv_iff_eq_inv
- \+/\- *theorem* eq_inv_iff_mul_eq_one
- \+/\- *theorem* eq_inv_mul_iff_mul_eq
- \+/\- *theorem* eq_mul_inv_iff_mul_eq
- \+/\- *theorem* eq_of_inv_eq_inv
- \+/\- *lemma* eq_sub_iff_add_eq'
- \+/\- *theorem* eq_sub_iff_add_eq
- \+/\- *theorem* inv_comm_of_comm
- \+/\- *theorem* inv_eq_iff_inv_eq
- \+/\- *theorem* inv_eq_iff_mul_eq_one
- \+/\- *theorem* inv_eq_one
- \+/\- *theorem* inv_inj'
- \+/\- *theorem* inv_mul_eq_iff_eq_mul
- \+/\- *theorem* inv_ne_one
- \+/\- *theorem* left_inverse_add_left_sub
- \+/\- *theorem* left_inverse_add_right_neg_add
- \+/\- *theorem* left_inverse_inv
- \+/\- *theorem* left_inverse_neg_add_add_right
- \+/\- *theorem* left_inverse_sub_add_left
- \+/\- *theorem* mul_eq_one_iff_eq_inv
- \+/\- *theorem* mul_eq_one_iff_inv_eq
- \+/\- *theorem* mul_inv_eq_iff_eq_mul
- \+/\- *theorem* mul_inv_eq_one
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_left_surjective
- \+/\- *theorem* mul_mul_mul_comm
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_right_surjective
- \+/\- *theorem* mul_self_iff_eq_one
- \+/\- *theorem* neg_add'
- \+/\- *lemma* neg_sub_neg
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* sub_add_sub_cancel
- \+/\- *lemma* sub_eq_iff_eq_add'
- \+/\- *theorem* sub_eq_iff_eq_add
- \+/\- *lemma* sub_eq_neg_add
- \+/\- *lemma* sub_eq_sub_iff_sub_eq_sub
- \+/\- *theorem* sub_eq_zero
- \+/\- *lemma* sub_left_inj
- \+/\- *theorem* sub_ne_zero
- \+/\- *lemma* sub_right_comm
- \+/\- *lemma* sub_right_inj
- \+/\- *theorem* sub_sub_assoc_swap
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left
- \+/\- *lemma* sub_sub_sub_cancel_right



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


Added scripts/update_nolints.sh




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
- \+/\- *theorem* additive.normal_add_subgroup_iff
- \+/\- *theorem* additive.simple_add_group_iff
- \+/\- *def* gmultiples
- \+/\- *lemma* gmultiples_subset
- \+/\- *def* gpowers
- \+/\- *lemma* gpowers_subset
- \+/\- *def* group.closure
- \+/\- *theorem* group.closure_eq_mclosure
- \+/\- *theorem* group.closure_mono
- \+/\- *lemma* group.closure_subgroup
- \+/\- *theorem* group.closure_subset
- \+/\- *lemma* group.closure_subset_iff
- \+/\- *lemma* group.conj_mem_conjugates_of_set
- \+/\- *def* group.conjugates
- \+/\- *def* group.conjugates_of_set
- \+/\- *theorem* group.conjugates_of_set_mono
- \+/\- *theorem* group.conjugates_of_set_subset
- \+/\- *lemma* group.conjugates_subset
- \+/\- *theorem* group.exists_list_of_mem_closure
- \+/\- *theorem* group.gpowers_eq_closure
- \+/\- *lemma* group.image_closure
- \+/\- *theorem* group.mclosure_inv_subset
- \+/\- *theorem* group.mclosure_subset
- \+/\- *lemma* group.mem_closure
- \+/\- *theorem* group.mem_closure_union_iff
- \+/\- *lemma* group.mem_conjugates_of_set_iff
- \+/\- *lemma* group.mem_conjugates_self
- \+/\- *def* group.normal_closure
- \+/\- *theorem* group.normal_closure_mono
- \+/\- *theorem* group.normal_closure_subset
- \+/\- *lemma* group.normal_closure_subset_iff
- \+/\- *theorem* group.subset_closure
- \+/\- *lemma* injective_mul
- \+/\- *lemma* is_add_subgroup.gsmul_coe
- \+/\- *lemma* is_add_subgroup.gsmul_mem
- \+/\- *theorem* is_add_subgroup.of_sub
- \+/\- *theorem* is_add_subgroup.sub_mem
- \+/\- *lemma* is_group_hom.inj_iff_trivial_ker
- \+/\- *lemma* is_group_hom.inj_of_trivial_ker
- \+/\- *lemma* is_group_hom.inv_iff_ker'
- \+/\- *lemma* is_group_hom.inv_iff_ker
- \+/\- *lemma* is_group_hom.inv_ker_one'
- \+/\- *lemma* is_group_hom.inv_ker_one
- \+/\- *def* is_group_hom.ker
- \+/\- *lemma* is_group_hom.mem_ker
- \+/\- *lemma* is_group_hom.one_iff_ker_inv'
- \+/\- *lemma* is_group_hom.one_iff_ker_inv
- \+/\- *lemma* is_group_hom.one_ker_inv'
- \+/\- *lemma* is_group_hom.one_ker_inv
- \+/\- *lemma* is_group_hom.trivial_ker_iff_eq_one
- \+/\- *lemma* is_group_hom.trivial_ker_of_inj
- \+/\- *def* is_subgroup.center
- \+/\- *lemma* is_subgroup.coe_gpow
- \+/\- *lemma* is_subgroup.coe_inv
- \+/\- *lemma* is_subgroup.eq_trivial_iff
- \+/\- *lemma* is_subgroup.gpow_mem
- \+/\- *lemma* is_subgroup.mem_center
- \+/\- *lemma* is_subgroup.mem_norm_comm
- \+/\- *lemma* is_subgroup.mem_norm_comm_iff
- \+/\- *lemma* is_subgroup.mem_trivial
- \+/\- *def* is_subgroup.normalizer
- \+/\- *theorem* is_subgroup.of_div
- \+/\- *lemma* is_subgroup.subset_normalizer
- \+/\- *def* is_subgroup.trivial
- \+/\- *lemma* is_subgroup.trivial_eq_closure
- \+/\- *lemma* mem_gmultiples
- \+/\- *lemma* mem_gpowers
- \+/\- *theorem* multiplicative.normal_subgroup_iff
- \+/\- *theorem* multiplicative.simple_group_iff
- \+/\- *lemma* normal_subgroup_of_comm_group
- \- *lemma* simple_add_group_of_surjective
- \+/\- *lemma* simple_group_of_surjective

Modified src/group_theory/submonoid.lean
- \+/\- *theorem* add_monoid.closure'_singleton
- \+/\- *lemma* add_submonoid.coe_smul
- \+/\- *lemma* add_submonoid.multiples.self_mem
- \+/\- *def* add_submonoid.multiples
- \+/\- *lemma* add_submonoid.multiples_subset
- \+/\- *def* add_submonoid.of_submonoid
- \+/\- *lemma* add_submonoid.smul_mem
- \+/\- *def* add_submonoid.to_submonoid
- \+/\- *lemma* image.is_submonoid
- \+/\- *lemma* is_add_submonoid.multiple_subset
- \+/\- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* is_add_submonoid.smul_mem
- \+/\- *lemma* is_submonoid.coe_mul
- \+/\- *lemma* is_submonoid.coe_one
- \+/\- *lemma* is_submonoid.finset_prod_mem
- \+/\- *lemma* is_submonoid.list_prod_mem
- \+/\- *lemma* is_submonoid.multiset_prod_mem
- \+/\- *lemma* is_submonoid.pow_mem
- \+/\- *lemma* is_submonoid.power_subset
- \+/\- *def* monoid.closure
- \+/\- *theorem* monoid.closure_mono
- \+/\- *theorem* monoid.closure_singleton
- \+/\- *theorem* monoid.closure_subset
- \+/\- *theorem* monoid.exists_list_of_mem_closure
- \+/\- *lemma* monoid.image_closure
- \+/\- *theorem* monoid.mem_closure_union_iff
- \+/\- *theorem* monoid.subset_closure
- \+/\- *lemma* multiples.add_mem
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* multiples.zero_mem
- \+/\- *def* multiples
- \+/\- *lemma* powers.mul_mem
- \+/\- *lemma* powers.one_mem
- \+/\- *lemma* powers.self_mem
- \+/\- *def* powers
- \+/\- *def* submonoid.add_submonoid_equiv
- \+/\- *def* submonoid.of_add_submonoid
- \+/\- *def* submonoid.to_add_submonoid



## [2020-02-13 22:27:55](https://github.com/leanprover-community/mathlib/commit/db1c500)
refactor(data/set/function): use dot notation ([#1934](https://github.com/leanprover-community/mathlib/pull/1934))
#### Estimated changes
Modified src/data/equiv/local_equiv.lean


Modified src/data/finsupp.lean


Modified src/data/set/basic.lean
- \- *def* set.eq_on
- \- *theorem* set.image_eq_image_of_eq_on

Modified src/data/set/countable.lean


Modified src/data/set/finite.lean


Modified src/data/set/function.lean
- \+ *lemma* function.injective.comp_inj_on
- \+ *lemma* function.injective.inj_on
- \+ *lemma* function.surjective.surj_on
- \+ *theorem* set.bij_on.comp
- \+ *theorem* set.bij_on.congr
- \+ *lemma* set.bij_on.image_eq
- \+ *lemma* set.bij_on.inj_on
- \+ *theorem* set.bij_on.inv_on_inv_fun_on
- \+ *lemma* set.bij_on.maps_to
- \+/\- *lemma* set.bij_on.mk
- \+ *lemma* set.bij_on.surj_on
- \+/\- *def* set.bij_on
- \- *theorem* set.bij_on_comp
- \+ *lemma* set.bij_on_empty
- \- *theorem* set.bij_on_of_eq_on
- \- *theorem* set.bij_on_of_inv_on
- \+/\- *lemma* set.bijective_iff_bij_on_univ
- \+ *theorem* set.eq_on.bij_on_iff
- \+ *theorem* set.eq_on.image_eq
- \+ *theorem* set.eq_on.inj_on_iff
- \+ *theorem* set.eq_on.maps_to_iff
- \+ *lemma* set.eq_on.mono
- \+ *theorem* set.eq_on.surj_on_iff
- \+ *lemma* set.eq_on.symm
- \+ *lemma* set.eq_on.trans
- \+ *def* set.eq_on
- \+ *lemma* set.eq_on_comm
- \+/\- *theorem* set.eq_on_of_left_inv_of_right_inv
- \+ *lemma* set.eq_on_refl
- \- *lemma* set.image_eq_of_bij_on
- \- *lemma* set.image_eq_of_maps_to_of_surj_on
- \- *theorem* set.image_subset_of_maps_to
- \- *theorem* set.image_subset_of_maps_to_of_subset
- \+ *lemma* set.inj_on.bij_on_image
- \+ *theorem* set.inj_on.comp
- \+ *theorem* set.inj_on.congr
- \+ *lemma* set.inj_on.inv_fun_on_image
- \+ *theorem* set.inj_on.left_inv_on_inv_fun_on
- \+ *theorem* set.inj_on.mono
- \+ *theorem* set.inj_on.right_inv_on_of_left_inv_on
- \- *lemma* set.inj_on.to_bij_on
- \+/\- *def* set.inj_on
- \- *theorem* set.inj_on_comp
- \- *lemma* set.inj_on_comp_of_injective_left
- \+/\- *lemma* set.inj_on_iff_injective
- \- *lemma* set.inj_on_of_bij_on
- \- *theorem* set.inj_on_of_eq_on
- \- *theorem* set.inj_on_of_inj_on_of_subset
- \- *lemma* set.inj_on_of_injective
- \- *theorem* set.inj_on_of_left_inv_on
- \+/\- *lemma* set.inj_on_preimage
- \+/\- *lemma* set.injective_iff_inj_on_univ
- \- *lemma* set.inv_fun_on_image
- \+ *theorem* set.inv_on.bij_on
- \+ *lemma* set.inv_on.symm
- \+/\- *def* set.inv_on
- \+ *theorem* set.left_inv_on.comp
- \+ *lemma* set.left_inv_on.congr_left
- \+ *theorem* set.left_inv_on.congr_right
- \+ *lemma* set.left_inv_on.eq
- \+ *lemma* set.left_inv_on.eq_on
- \+ *theorem* set.left_inv_on.inj_on
- \+ *theorem* set.left_inv_on.surj_on
- \+/\- *def* set.left_inv_on
- \- *theorem* set.left_inv_on_comp
- \- *theorem* set.left_inv_on_of_eq_on_left
- \- *theorem* set.left_inv_on_of_eq_on_right
- \- *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \+/\- *theorem* set.maps_to'
- \+ *theorem* set.maps_to.comp
- \+ *theorem* set.maps_to.congr
- \+ *theorem* set.maps_to.image_subset
- \+ *theorem* set.maps_to.mono
- \+/\- *def* set.maps_to
- \- *theorem* set.maps_to_comp
- \+ *theorem* set.maps_to_empty
- \+/\- *theorem* set.maps_to_image
- \- *lemma* set.maps_to_of_bij_on
- \- *theorem* set.maps_to_of_eq_on
- \+ *theorem* set.maps_to_preimage
- \+/\- *theorem* set.maps_to_range
- \+/\- *theorem* set.maps_to_univ
- \+/\- *lemma* set.range_restrict
- \+ *theorem* set.right_inv_on.comp
- \+ *theorem* set.right_inv_on.congr_left
- \+ *theorem* set.right_inv_on.congr_right
- \+ *lemma* set.right_inv_on.eq
- \+ *lemma* set.right_inv_on.eq_on
- \+ *theorem* set.right_inv_on.surj_on
- \+/\- *def* set.right_inv_on
- \- *theorem* set.right_inv_on_comp
- \- *theorem* set.right_inv_on_of_eq_on_left
- \- *theorem* set.right_inv_on_of_eq_on_right
- \- *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \- *lemma* set.subset_image_iff
- \- *lemma* set.subset_range_iff
- \+ *theorem* set.surj_on.bij_on_subset
- \+ *theorem* set.surj_on.comap_nonempty
- \+ *theorem* set.surj_on.comp
- \+ *theorem* set.surj_on.congr
- \+ *lemma* set.surj_on.image_eq_of_maps_to
- \+ *theorem* set.surj_on.inv_on_inv_fun_on
- \+ *theorem* set.surj_on.left_inv_on_of_right_inv_on
- \+ *theorem* set.surj_on.maps_to_inv_fun_on
- \+ *theorem* set.surj_on.mono
- \+ *theorem* set.surj_on.right_inv_on_inv_fun_on
- \+/\- *def* set.surj_on
- \- *theorem* set.surj_on_comp
- \+ *theorem* set.surj_on_empty
- \+ *theorem* set.surj_on_iff_exists_bij_on_subset
- \+/\- *lemma* set.surj_on_iff_surjective
- \- *lemma* set.surj_on_of_bij_on
- \- *theorem* set.surj_on_of_eq_on
- \- *theorem* set.surj_on_of_right_inv_on
- \+/\- *lemma* set.surjective_iff_surj_on_univ

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
- \+ *lemma* continuous_linear_equiv.comp_differentiable_at_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_on_iff
- \+ *lemma* continuous_linear_equiv.comp_differentiable_within_at_iff
- \+ *lemma* continuous_linear_equiv.comp_fderiv
- \+ *lemma* continuous_linear_equiv.comp_fderiv_within
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff'
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff'
- \+ *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff
- \+ *lemma* continuous_linear_equiv.unique_diff_on_preimage_iff
- \+ *lemma* differentiable.comp_differentiable_on
- \+ *lemma* differentiable.differentiable_at
- \+ *lemma* differentiable_at.comp_differentiable_within_at
- \+ *lemma* differentiable_on_congr
- \+ *lemma* fderiv.comp_fderiv_within
- \+/\- *lemma* fderiv_const
- \+ *lemma* fderiv_const_apply
- \- *lemma* fderiv_within_const
- \+ *lemma* fderiv_within_const_apply

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_prod_le_iff

Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_equiv.symm_symm
- \+ *theorem* linear_equiv.symm_symm_apply

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.comp_continuous_iff
- \+ *lemma* continuous_linear_equiv.comp_continuous_on_iff
- \+ *lemma* continuous_linear_equiv.self_comp_symm
- \+ *lemma* continuous_linear_equiv.symm_comp_self
- \+ *theorem* continuous_linear_equiv.symm_symm
- \+ *theorem* continuous_linear_equiv.symm_symm_apply
- \+ *theorem* continuous_linear_map.comp_assoc

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_congr

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.comp_continuous_iff
- \+ *lemma* homeomorph.comp_continuous_on_iff



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
- \+/\- *lemma* list.func.get_neg

Modified src/data/set/basic.lean
- \+/\- *theorem* set.empty_ne_univ

Modified src/data/set/countable.lean
- \+/\- *lemma* set.countable_iff_exists_surjective

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Inter_const
- \+/\- *theorem* set.Inter_inter
- \+/\- *theorem* set.Union_const
- \+/\- *theorem* set.Union_union
- \+/\- *theorem* set.diff_Union
- \+/\- *theorem* set.inter_Inter
- \+/\- *theorem* set.union_Union

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_range

Modified src/linear_algebra/finsupp.lean
- \+/\- *theorem* finsupp.lmap_domain_supported

Modified src/logic/basic.lean
- \+/\- *theorem* exists_const
- \+/\- *theorem* forall_const
- \+ *lemma* nonempty.elim_to_inhabited

Modified src/logic/function.lean


Modified src/measure_theory/integration.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.prod_at_top_at_top_eq
- \+/\- *lemma* filter.prod_map_at_top_eq

Modified src/tactic/interactive.lean


Modified src/tactic/lint.lean


Modified src/topology/basic.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* emetric.cauchy_seq_iff_le_tendsto_0

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* cauchy_seq_iff_tendsto_dist_at_top_0

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.cauchy_seq_iff'
- \+/\- *theorem* emetric.cauchy_seq_iff
- \+/\- *theorem* emetric.cauchy_seq_iff_nnreal
- \+/\- *theorem* emetric.tendsto_at_top

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/separation.lean


Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq_iff_tendsto
- \+/\- *lemma* cauchy_seq_of_controlled
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff'
- \+/\- *lemma* filter.has_basis.cauchy_seq_iff



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
- \+ *lemma* is_connected_iff_sUnion_disjoint_open
- \+ *lemma* is_irreducible_iff_sInter
- \+ *lemma* is_irreducible_iff_sUnion_closed
- \+ *lemma* is_preconnected_iff_subset_of_disjoint
- \+ *lemma* is_preirreducible_iff_closed_union_closed
- \+ *lemma* subtype.connected_space
- \+ *lemma* subtype.irreducible_space
- \+ *lemma* subtype.preconnected_space
- \+ *lemma* subtype.preirreducible_space



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
- \+ *lemma* filter.has_basis.eventually_iff

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \- *theorem* metric.exists_delta_of_continuous
- \- *theorem* metric.mem_closure_iff'
- \+ *theorem* metric.mem_closure_iff
- \+ *theorem* metric.nhds_basis_ball
- \+ *theorem* metric.nhds_basis_ball_inv_nat_pos
- \+ *theorem* metric.nhds_basis_ball_inv_nat_succ
- \+ *theorem* metric.nhds_basis_closed_ball
- \- *theorem* metric.nhds_eq
- \+ *theorem* metric.nhds_within_basis_ball
- \+ *theorem* metric.uniformity_basis_dist
- \+ *theorem* metric.uniformity_basis_dist_inv_nat_pos
- \+ *theorem* metric.uniformity_basis_dist_inv_nat_succ
- \+ *theorem* metric.uniformity_basis_dist_le
- \- *theorem* metric.uniformity_dist'
- \- *theorem* metric.uniformity_dist
- \+ *theorem* metric.uniformity_edist
- \- *theorem* uniformity_edist

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \- *theorem* emetric.mem_closure_iff'
- \+ *theorem* emetric.mem_closure_iff
- \+/\- *theorem* emetric.mem_nhds_iff
- \+ *theorem* emetric.nhds_basis_eball
- \+/\- *theorem* emetric.nhds_eq
- \- *theorem* mem_uniformity_edist_inv_nat
- \+ *theorem* uniformity_basis_edist'
- \+ *theorem* uniformity_basis_edist
- \+ *theorem* uniformity_basis_edist_inv_nat
- \+ *theorem* uniformity_basis_edist_le'
- \+ *theorem* uniformity_basis_edist_le
- \+ *theorem* uniformity_basis_edist_nnreal
- \- *theorem* uniformity_edist''
- \- *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist
- \- *theorem* uniformity_edist_inv_nat
- \- *theorem* uniformity_edist_nnreal

Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.has_basis.mem_uniformity_iff
- \+ *lemma* filter.has_basis.uniform_continuous_iff
- \+ *lemma* nhds_basis_uniformity'
- \+ *lemma* nhds_basis_uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_iff'
- \- *lemma* cauchy_seq_iff_prod_map
- \+ *lemma* cauchy_seq_iff_tendsto
- \+ *lemma* filter.has_basis.cauchy_iff
- \+ *lemma* filter.has_basis.cauchy_seq_iff'
- \+ *lemma* filter.has_basis.cauchy_seq_iff



## [2020-02-09 09:33:32](https://github.com/leanprover-community/mathlib/commit/777f214)
refactor(data/matrix,linear_algebra): Use `matrix.mul` as default multiplication in matrix lemmas ([#1959](https://github.com/leanprover-community/mathlib/pull/1959))
* Change `has_mul.mul` to `matrix.mul` in a few `simp` lemmas
* Standardise more lemmas for matrix multiplication
* Generalize `to_pequiv_mul_matrix` to rectangular matrices
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *theorem* matrix.diagonal_mul_diagonal'
- \+/\- *theorem* matrix.diagonal_mul_diagonal

Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* pequiv.to_pequiv_mul_matrix

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* matrix.det_mul
- \+/\- *lemma* matrix.det_transpose



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
- \+/\- *lemma* intermediate_value_univ
- \- *lemma* is_connected.forall_Icc_subset
- \- *lemma* is_connected.intermediate_value
- \+/\- *lemma* is_connected_Icc
- \- *lemma* is_connected_Ici
- \- *lemma* is_connected_Ico
- \- *lemma* is_connected_Iic
- \- *lemma* is_connected_Iio
- \- *lemma* is_connected_Ioc
- \- *lemma* is_connected_Ioi
- \+/\- *lemma* is_connected_Ioo
- \- *lemma* is_connected_iff_forall_Icc_subset
- \+ *lemma* is_preconnected.forall_Icc_subset
- \+ *lemma* is_preconnected.intermediate_value
- \+ *lemma* is_preconnected_Ici
- \+ *lemma* is_preconnected_Ico
- \+ *lemma* is_preconnected_Iic
- \+ *lemma* is_preconnected_Iio
- \+ *lemma* is_preconnected_Ioc
- \+ *lemma* is_preconnected_Ioi
- \+ *lemma* is_preconnected_iff_forall_Icc_subset

Modified src/topology/basic.lean
- \+ *lemma* set.nonempty.closure

Modified src/topology/subset_properties.lean
- \- *theorem* exists_irreducible
- \- *theorem* exists_mem_inter
- \+ *theorem* exists_preirreducible
- \+ *lemma* irreducible_component_property
- \- *theorem* irreducible_exists_mem_inter
- \+/\- *theorem* is_clopen_iff
- \+ *lemma* is_connected.is_preconnected
- \+ *lemma* is_connected.nonempty
- \+/\- *theorem* is_connected.union
- \- *theorem* is_connected_closed_iff
- \- *theorem* is_connected_empty
- \- *theorem* is_connected_of_forall
- \- *theorem* is_connected_of_forall_pair
- \- *theorem* is_connected_of_is_irreducible
- \- *theorem* is_connected_sUnion
- \+ *lemma* is_irreducible.closure
- \+ *theorem* is_irreducible.image
- \+ *theorem* is_irreducible.is_connected
- \+ *lemma* is_irreducible.is_preirreducible
- \+ *lemma* is_irreducible.nonempty
- \- *theorem* is_irreducible_closure
- \- *theorem* is_irreducible_empty
- \+ *theorem* is_preconnected.closure
- \+ *theorem* is_preconnected.image
- \+ *theorem* is_preconnected.union
- \+ *def* is_preconnected
- \+ *theorem* is_preconnected_closed_iff
- \+ *theorem* is_preconnected_empty
- \+ *theorem* is_preconnected_of_forall
- \+ *theorem* is_preconnected_of_forall_pair
- \+ *theorem* is_preconnected_sUnion
- \+ *theorem* is_preirreducible.closure
- \+ *theorem* is_preirreducible.image
- \+ *theorem* is_preirreducible.is_preconnected
- \+ *def* is_preirreducible
- \+ *theorem* is_preirreducible_empty
- \+ *theorem* nonempty_inter
- \+ *theorem* nonempty_preirreducible_inter
- \+/\- *theorem* subset_connected_component



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
- \+ *lemma* linear_map.to_fun_eq_coe

Modified src/data/fintype.lean
- \+ *lemma* univ_eq_singleton_of_card_one

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.mul_vec_one
- \+ *lemma* matrix.smul_eq_diagonal_mul
- \+ *lemma* matrix.smul_eq_mul_diagonal

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_eq_one_of_card_eq_zero
- \+ *lemma* matrix.det_eq_zero_of_column_eq_zero
- \+ *lemma* matrix.det_smul

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.to_lin_one

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_eq_one_of_card_eq_one
- \+ *lemma* matrix.adjugate_zero
- \+ *lemma* matrix.det_adjugate_eq_one
- \+ *lemma* matrix.det_adjugate_of_cancel
- \+ *lemma* matrix.det_adjugate_of_is_unit

Added src/linear_algebra/special_linear_group.lean
- \+ *lemma* matrix.special_linear_group.coe_to_GL
- \+ *lemma* matrix.special_linear_group.det_coe_fun
- \+ *lemma* matrix.special_linear_group.det_coe_matrix
- \+ *def* matrix.special_linear_group.embedding_GL
- \+ *lemma* matrix.special_linear_group.ext
- \+ *lemma* matrix.special_linear_group.ext_iff
- \+ *lemma* matrix.special_linear_group.inv_apply
- \+ *lemma* matrix.special_linear_group.inv_val
- \+ *lemma* matrix.special_linear_group.mul_apply
- \+ *lemma* matrix.special_linear_group.mul_val
- \+ *lemma* matrix.special_linear_group.one_apply
- \+ *lemma* matrix.special_linear_group.one_val
- \+ *def* matrix.special_linear_group.to_GL
- \+ *lemma* matrix.special_linear_group.to_GL_mul
- \+ *lemma* matrix.special_linear_group.to_GL_one
- \+ *def* matrix.special_linear_group.to_lin
- \+ *lemma* matrix.special_linear_group.to_lin_mul
- \+ *lemma* matrix.special_linear_group.to_lin_one
- \+ *def* matrix.special_linear_group.to_linear_equiv
- \+ *def* matrix.special_linear_group



## [2020-02-07 16:57:48](https://github.com/leanprover-community/mathlib/commit/2007d34)
feat(analysis/normed_space/multilinear): norm on continuous multilinear maps ([#1956](https://github.com/leanprover-community/mathlib/pull/1956))
* feat(analysis/normed_space/multilinear): norm on continuous multilinear maps
* docstring
* improved docstrings
#### Estimated changes
Added src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_linear_map.curry_uncurry_left
- \+ *lemma* continuous_linear_map.norm_map_tail_right_le
- \+ *def* continuous_linear_map.uncurry_left
- \+ *lemma* continuous_linear_map.uncurry_left_apply
- \+ *lemma* continuous_linear_map.uncurry_left_norm
- \+ *def* continuous_multilinear_curry_fin0
- \+ *def* continuous_multilinear_curry_fin0_aux
- \+ *def* continuous_multilinear_curry_left_equiv
- \+ *def* continuous_multilinear_curry_left_equiv_aux
- \+ *def* continuous_multilinear_curry_right_equiv
- \+ *def* continuous_multilinear_curry_right_equiv_aux
- \+ *theorem* continuous_multilinear_map.bound
- \+ *lemma* continuous_multilinear_map.bounds_bdd_below
- \+ *lemma* continuous_multilinear_map.bounds_nonempty
- \+ *lemma* continuous_multilinear_map.continuous_eval
- \+ *def* continuous_multilinear_map.curry0
- \+ *lemma* continuous_multilinear_map.curry0_apply
- \+ *lemma* continuous_multilinear_map.curry0_norm
- \+ *lemma* continuous_multilinear_map.curry0_uncurry0
- \+ *def* continuous_multilinear_map.curry_left
- \+ *lemma* continuous_multilinear_map.curry_left_apply
- \+ *lemma* continuous_multilinear_map.curry_left_norm
- \+ *def* continuous_multilinear_map.curry_right
- \+ *lemma* continuous_multilinear_map.curry_right_apply
- \+ *lemma* continuous_multilinear_map.curry_right_norm
- \+ *lemma* continuous_multilinear_map.curry_uncurry_right
- \+ *theorem* continuous_multilinear_map.le_op_norm
- \+ *lemma* continuous_multilinear_map.mk_pi_field_apply
- \+ *lemma* continuous_multilinear_map.mk_pi_ring_apply_one_eq_self
- \+ *lemma* continuous_multilinear_map.norm_image_sub_le_of_bound'
- \+ *lemma* continuous_multilinear_map.norm_image_sub_le_of_bound
- \+ *lemma* continuous_multilinear_map.norm_map_cons_le
- \+ *lemma* continuous_multilinear_map.norm_map_tail_left_le
- \+ *lemma* continuous_multilinear_map.norm_zero
- \+ *def* continuous_multilinear_map.op_norm
- \+ *theorem* continuous_multilinear_map.op_norm_add_le
- \+ *lemma* continuous_multilinear_map.op_norm_le_bound
- \+ *lemma* continuous_multilinear_map.op_norm_neg
- \+ *lemma* continuous_multilinear_map.op_norm_nonneg
- \+ *lemma* continuous_multilinear_map.op_norm_smul
- \+ *theorem* continuous_multilinear_map.op_norm_zero_iff
- \+ *lemma* continuous_multilinear_map.ratio_le_op_norm
- \+ *def* continuous_multilinear_map.uncurry0
- \+ *lemma* continuous_multilinear_map.uncurry0_curry0
- \+ *lemma* continuous_multilinear_map.uncurry0_norm
- \+ *lemma* continuous_multilinear_map.uncurry_curry_left
- \+ *lemma* continuous_multilinear_map.uncurry_curry_right
- \+ *def* continuous_multilinear_map.uncurry_right
- \+ *lemma* continuous_multilinear_map.uncurry_right_apply
- \+ *lemma* continuous_multilinear_map.uncurry_right_norm
- \+ *lemma* continuous_multilinear_map.unit_le_op_norm
- \+ *theorem* multilinear_map.continuous_of_bound
- \+ *theorem* multilinear_map.exists_bound_of_continuous
- \+ *def* multilinear_map.mk_continuous
- \+ *lemma* multilinear_map.mk_continuous_norm_le
- \+ *lemma* multilinear_map.norm_image_sub_le_of_bound'
- \+ *lemma* multilinear_map.norm_image_sub_le_of_bound



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
Added src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.Inter_zero_locus
- \+ *def* prime_spectrum.comap
- \+ *lemma* prime_spectrum.comap_as_ideal
- \+ *lemma* prime_spectrum.comap_comp
- \+ *lemma* prime_spectrum.comap_continuous
- \+ *lemma* prime_spectrum.comap_id
- \+ *lemma* prime_spectrum.ext
- \+ *lemma* prime_spectrum.is_closed_iff_zero_locus
- \+ *lemma* prime_spectrum.is_open_iff
- \+ *lemma* prime_spectrum.mem_zero_locus
- \+ *lemma* prime_spectrum.preimage_comap_zero_locus
- \+ *lemma* prime_spectrum.union_zero_locus
- \+ *lemma* prime_spectrum.union_zero_locus_ideal
- \+ *def* prime_spectrum.zero_locus
- \+ *lemma* prime_spectrum.zero_locus_Union
- \+ *lemma* prime_spectrum.zero_locus_empty_of_one_mem
- \+ *lemma* prime_spectrum.zero_locus_is_closed
- \+ *lemma* prime_spectrum.zero_locus_span
- \+ *lemma* prime_spectrum.zero_locus_univ
- \+ *def* prime_spectrum

Modified src/topology/basic.lean
- \+ *def* topological_space.of_closed



## [2020-02-06 15:25:57](https://github.com/leanprover-community/mathlib/commit/fb160f0)
refactor(topology/continuous_on): use filter bases ([#1968](https://github.com/leanprover-community/mathlib/pull/1968))
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_basis_open
- \+ *lemma* nhds_within_has_basis



## [2020-02-06 12:20:38](https://github.com/leanprover-community/mathlib/commit/0e533d0)
refactor(topology/basic): rewrite some proofs using filter bases ([#1967](https://github.com/leanprover-community/mathlib/pull/1967))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *theorem* mem_closure_iff_nhds_basis
- \+ *lemma* nhds_basis_opens
- \- *lemma* nhds_sets

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
- \+ *theorem* set.nonempty.not_subset_empty

Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.supr_subtype'

Modified src/order/filter/basic.lean
- \+ *lemma* filter.nonempty_of_ne_bot

Modified src/topology/algebra/ordered.lean
- \+ *lemma* infi_of_continuous'
- \+/\- *lemma* infi_of_continuous
- \+ *lemma* supr_of_continuous'
- \+/\- *lemma* supr_of_continuous



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
- \+ *lemma* measure_theory.integral_nonneg_of_ae
- \- *lemma* measure_theory.integral_nonneg_of_nonneg_ae
- \+/\- *lemma* measure_theory.integral_zero
- \- *lemma* measure_theory.l1.integral_coe_eq_integral
- \+ *lemma* measure_theory.l1.simple_func.integral_eq_integral

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integrable_on.smul
- \+/\- *def* integrable_on
- \+/\- *lemma* integrable_on_congr_ae
- \+/\- *lemma* integrable_on_empty
- \- *lemma* integrable_on_of_integrable
- \+/\- *lemma* integral_on_congr
- \+ *lemma* integral_on_non_integrable
- \+ *lemma* integral_on_non_measurable
- \+ *lemma* integral_on_nonneg
- \+ *lemma* integral_on_nonneg_of_ae
- \+ *lemma* integral_on_nonpos
- \+ *lemma* integral_on_nonpos_of_ae
- \+ *lemma* integral_on_undef
- \+ *lemma* measurable.measurable_on_univ
- \+/\- *def* measurable_on
- \+/\- *lemma* measurable_on_empty
- \+/\- *lemma* measurable_on_singleton
- \- *lemma* measurable_on_univ
- \+ *lemma* measure_theory.integrable.integrable_on



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
- \+ *def* list.after

Modified src/tactic/basic.lean


Added src/tactic/rename.lean


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
- \+ *lemma* set.nonempty.pointwise_mul
- \- *lemma* set.pointwise_mul_ne_empty

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *theorem* unique_diff_on_convex

Modified src/analysis/complex/polynomial.lean


Modified src/analysis/normed_space/real_inner_product.lean
- \+/\- *theorem* exists_norm_eq_infi_of_complete_convex
- \+/\- *theorem* exists_norm_eq_infi_of_complete_subspace
- \+/\- *theorem* norm_eq_infi_iff_inner_eq_zero
- \+/\- *theorem* norm_eq_infi_iff_inner_le_zero

Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/computability/halting.lean


Modified src/data/analysis/filter.lean


Modified src/data/analysis/topology.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_Inf

Modified src/data/real/nnreal.lean


Modified src/data/semiquot.lean
- \- *theorem* semiquot.ne_empty
- \+ *theorem* semiquot.nonempty

Modified src/data/set/basic.lean
- \- *theorem* set.coe_nonempty_iff_ne_empty
- \+ *lemma* set.empty_not_nonempty
- \- *theorem* set.exists_mem_of_ne_empty
- \+/\- *lemma* set.fst_image_prod
- \- *theorem* set.insert_ne_empty
- \- *lemma* set.inter_singleton_ne_empty
- \- *theorem* set.ne_empty_iff_exists_mem
- \+/\- *theorem* set.ne_empty_iff_nonempty
- \- *theorem* set.ne_empty_of_mem
- \+/\- *lemma* set.nmem_singleton_empty
- \+ *lemma* set.nonempty.to_subtype
- \+/\- *lemma* set.nonempty_compl
- \- *lemma* set.nonempty_iff_univ_ne_empty
- \- *theorem* set.nonempty_of_inter_nonempty_left
- \- *theorem* set.nonempty_of_inter_nonempty_right
- \- *theorem* set.not_eq_empty_iff_exists
- \+ *lemma* set.not_nonempty_iff_eq_empty
- \- *theorem* set.prod_ne_empty_iff
- \+/\- *lemma* set.range_eq_empty
- \- *lemma* set.range_ne_empty
- \- *lemma* set.range_ne_empty_iff_nonempty
- \+ *lemma* set.range_nonempty
- \+ *lemma* set.range_nonempty_iff_nonempty
- \- *theorem* set.singleton_ne_empty
- \+/\- *lemma* set.snd_image_prod
- \- *theorem* set.subset_ne_empty
- \- *lemma* set.univ_ne_empty
- \+/\- *lemma* set.univ_nonempty

Modified src/data/set/countable.lean
- \+/\- *lemma* set.countable_iff_exists_surjective_to_subtype
- \+/\- *lemma* set.exists_surjective_of_countable

Modified src/data/set/finite.lean
- \+/\- *lemma* set.finite.exists_maximal_wrt

Modified src/data/set/intervals/basic.lean
- \- *lemma* set.Ici_ne_empty
- \- *lemma* set.Iic_ne_empty
- \- *lemma* set.Iio_ne_empty
- \- *lemma* set.Ioi_ne_empty

Modified src/data/set/lattice.lean


Modified src/data/setoid.lean
- \- *lemma* setoid.ne_empty_of_mem_partition
- \+ *lemma* setoid.nonempty_of_mem_partition

Modified src/geometry/manifold/manifold.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* measure_theory.outer_measure.Inf_gen_nonempty1
- \+/\- *theorem* measure_theory.outer_measure.top_apply

Modified src/measure_theory/simple_func_dense.lean


Modified src/order/bounds.lean
- \- *lemma* ne_empty_of_is_glb
- \- *lemma* ne_empty_of_is_lub
- \+ *lemma* nonempty_of_is_glb
- \+ *lemma* nonempty_of_is_lub

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* lattice.cInf_insert
- \+/\- *theorem* lattice.cInf_intro
- \+/\- *theorem* lattice.cInf_le_cInf
- \+/\- *theorem* lattice.cInf_le_cSup
- \+/\- *theorem* lattice.cInf_union
- \+/\- *lemma* lattice.cInf_upper_bounds_eq_cSup
- \+/\- *theorem* lattice.cSup_insert
- \+/\- *theorem* lattice.cSup_inter_le
- \+/\- *theorem* lattice.cSup_intro'
- \+/\- *theorem* lattice.cSup_intro
- \+/\- *theorem* lattice.cSup_le
- \+/\- *theorem* lattice.cSup_le_cSup
- \+/\- *theorem* lattice.cSup_le_iff
- \+/\- *lemma* lattice.cSup_lower_bounds_eq_cInf
- \+/\- *theorem* lattice.cSup_union
- \+/\- *theorem* lattice.cinfi_const
- \+/\- *lemma* lattice.cinfi_le
- \+/\- *lemma* lattice.cinfi_le_cinfi
- \+/\- *theorem* lattice.csupr_const
- \+/\- *lemma* lattice.csupr_le
- \+/\- *lemma* lattice.csupr_le_csupr
- \+/\- *lemma* lattice.exists_lt_of_cInf_lt
- \+/\- *lemma* lattice.exists_lt_of_cinfi_lt
- \+/\- *lemma* lattice.exists_lt_of_lt_cSup
- \+/\- *lemma* lattice.exists_lt_of_lt_csupr
- \+/\- *lemma* lattice.is_glb_cInf
- \+/\- *lemma* lattice.is_lub_cSup
- \+/\- *theorem* lattice.le_cInf
- \+/\- *theorem* lattice.le_cInf_iff
- \+/\- *theorem* lattice.le_cInf_inter
- \+/\- *lemma* lattice.le_cinfi
- \+/\- *lemma* lattice.le_csupr
- \+/\- *lemma* with_top.coe_Inf

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_ne_bot
- \- *lemma* filter.forall_sets_ne_empty_iff_ne_bot
- \+/\- *lemma* filter.nonempty_of_mem_sets
- \+ *lemma* filter.principal_ne_bot_iff

Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift'_ne_bot_iff

Modified src/order/filter/pointwise.lean


Modified src/order/liminf_limsup.lean
- \+/\- *theorem* filter.Liminf_principal
- \+/\- *theorem* filter.Limsup_principal

Modified src/order/zorn.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* mem_closure_of_is_glb
- \+/\- *lemma* mem_closure_of_is_lub
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb
- \+/\- *lemma* nhds_principal_ne_bot_of_is_lub

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+/\- *lemma* dense_iff_inter_open
- \+/\- *theorem* mem_closure_iff
- \+/\- *theorem* mem_closure_iff_nhds

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.Sup_add

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean
- \+/\- *theorem* nonempty_interior_of_Union_of_closed

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.diam_union'

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* emetric.diam_union'

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* emetric.Hausdorff_edist_empty
- \+/\- *lemma* emetric.Hausdorff_edist_le_ediam
- \+ *lemma* emetric.empty_or_nonempty_of_Hausdorff_edist_ne_top
- \- *lemma* emetric.ne_empty_of_Hausdorff_edist_ne_top
- \+ *lemma* emetric.nonempty_of_Hausdorff_edist_ne_top
- \+/\- *lemma* metric.Hausdorff_dist_le_diam
- \- *lemma* metric.Hausdorff_edist_ne_top_of_ne_empty_of_bounded
- \+ *lemma* metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded
- \+/\- *lemma* metric.exists_dist_lt_of_inf_dist_lt
- \+/\- *lemma* metric.inf_dist_le_inf_dist_of_subset
- \+/\- *lemma* metric.inf_edist_ne_top
- \+/\- *lemma* metric.mem_closure_iff_inf_dist_zero
- \+/\- *lemma* metric.mem_iff_inf_dist_zero_of_closed

Modified src/topology/metric_space/isometry.lean


Modified src/topology/opens.lean
- \+/\- *def* topological_space.nonempty_compacts

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
- \+ *lemma* set.indicator_apply
- \+ *lemma* set.indicator_comp_of_zero
- \+ *lemma* set.indicator_mul
- \+ *lemma* set.indicator_nonneg'
- \+ *lemma* set.indicator_nonneg
- \+ *lemma* set.indicator_nonpos'
- \+ *lemma* set.indicator_nonpos

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_inter_Icc_eq_singleton

Modified src/data/set/intervals/default.lean


Added src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.Icc_subset_interval'
- \+ *lemma* set.Icc_subset_interval
- \+ *lemma* set.abs_sub_le_of_subinterval
- \+ *lemma* set.abs_sub_left_of_mem_interval
- \+ *lemma* set.abs_sub_right_of_mem_interval
- \+ *lemma* set.bdd_below_bdd_above_iff_subset_interval
- \+ *def* set.interval
- \+ *lemma* set.interval_of_ge
- \+ *lemma* set.interval_of_gt
- \+ *lemma* set.interval_of_le
- \+ *lemma* set.interval_of_lt
- \+ *lemma* set.interval_of_not_ge
- \+ *lemma* set.interval_of_not_le
- \+ *lemma* set.interval_self
- \+ *lemma* set.interval_subset_interval
- \+ *lemma* set.interval_subset_interval_iff_le
- \+ *lemma* set.interval_subset_interval_iff_mem
- \+ *lemma* set.interval_subset_interval_left
- \+ *lemma* set.interval_subset_interval_right
- \+ *lemma* set.interval_swap
- \+ *lemma* set.left_mem_interval
- \+ *lemma* set.mem_interval_of_ge
- \+ *lemma* set.mem_interval_of_le
- \+ *lemma* set.nonempty_interval
- \+ *lemma* set.right_mem_interval

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_interval

Modified src/measure_theory/lebesgue_measure.lean
- \- *lemma* measure_theory.real.volume_Icc
- \- *lemma* measure_theory.real.volume_Ico
- \- *lemma* measure_theory.real.volume_Ioo
- \- *lemma* measure_theory.real.volume_singleton
- \- *theorem* measure_theory.real.volume_val
- \+ *lemma* real.volume_Icc
- \+ *lemma* real.volume_Ico
- \+ *lemma* real.volume_Ioo
- \+ *lemma* real.volume_interval
- \+ *lemma* real.volume_lt_top_of_bounded
- \+ *lemma* real.volume_lt_top_of_compact
- \+ *lemma* real.volume_singleton
- \+ *theorem* real.volume_val

Modified src/order/bounds.lean
- \+ *lemma* bdd_above_iff_subset_Iic
- \+ *lemma* bdd_below_bdd_above_iff_subset_Icc
- \+ *lemma* bdd_below_iff_subset_Ici



## [2020-02-04 19:56:41](https://github.com/leanprover-community/mathlib/commit/475a669)
feat(topology/algebra/multilinear): define continuous multilinear maps ([#1948](https://github.com/leanprover-community/mathlib/pull/1948))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* multilinear_map.map_smul

Added src/topology/algebra/multilinear.lean
- \+ *lemma* continuous_multilinear_map.add_apply
- \+ *lemma* continuous_multilinear_map.cons_add
- \+ *lemma* continuous_multilinear_map.cons_smul
- \+ *theorem* continuous_multilinear_map.ext
- \+ *lemma* continuous_multilinear_map.map_add
- \+ *lemma* continuous_multilinear_map.map_add_univ
- \+ *lemma* continuous_multilinear_map.map_coord_zero
- \+ *lemma* continuous_multilinear_map.map_piecewise_add
- \+ *lemma* continuous_multilinear_map.map_piecewise_smul
- \+ *lemma* continuous_multilinear_map.map_smul
- \+ *lemma* continuous_multilinear_map.map_smul_univ
- \+ *lemma* continuous_multilinear_map.map_sub
- \+ *lemma* continuous_multilinear_map.map_zero
- \+ *lemma* continuous_multilinear_map.neg_apply
- \+ *lemma* continuous_multilinear_map.smul_apply
- \+ *lemma* continuous_multilinear_map.sub_apply
- \+ *def* continuous_multilinear_map.to_continuous_linear_map
- \+ *def* continuous_multilinear_map.to_multilinear_map_linear
- \+ *lemma* continuous_multilinear_map.zero_apply



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
Added src/number_theory/bernoulli.lean
- \+ *def* bernoulli
- \+ *lemma* bernoulli_def'
- \+ *lemma* bernoulli_def
- \+ *lemma* bernoulli_four
- \+ *lemma* bernoulli_one
- \+ *lemma* bernoulli_three
- \+ *lemma* bernoulli_two
- \+ *lemma* bernoulli_zero
- \+ *lemma* sum_bernoulli



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
- \+ *def* category_theory.adjunction.left_adjoint_preserves_colimits
- \+ *def* category_theory.adjunction.right_adjoint_preserves_limits

Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/data/list/defs.lean
- \+ *def* list.indexes_values
- \+ *def* list.indexes_values_aux
- \+ *def* list.is_nil

Modified src/meta/expr.lean


Modified src/order/filter/filter_product.lean


Modified src/order/fixed_points.lean


Modified src/order/pilex.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/uniform_ring.lean


Added test/expr.lean


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
- \+ *lemma* finsupp.add_eq_zero_iff

Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/ring_theory/power_series.lean
- \+ *lemma* mv_power_series.coeff_mul_C
- \+ *lemma* mv_power_series.coeff_zero_mul_X
- \+ *lemma* power_series.coeff_mul_C
- \+ *lemma* power_series.coeff_succ_mul_X
- \+ *lemma* power_series.coeff_zero_mul_X



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
- \+ *lemma* finset.prod_update_of_mem
- \+ *lemma* finset.prod_update_of_not_mem
- \+ *lemma* finset.sum_update_of_mem

Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_le_of_mem_closed_ball
- \+ *lemma* norm_le_pi_norm
- \+ *lemma* norm_lt_of_mem_ball

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* linear_map.mk_continuous
- \+ *lemma* linear_map.mk_continuous_apply
- \+ *lemma* linear_map.mk_continuous_coe
- \+ *lemma* linear_map.mk_continuous_norm_le
- \+ *def* linear_map.mk_continuous_of_exists_bound
- \+ *lemma* linear_map.mk_continuous_of_exists_bound_apply
- \+ *lemma* linear_map.mk_continuous_of_exists_bound_coe
- \- *def* linear_map.with_bound
- \- *lemma* linear_map_with_bound_apply
- \- *lemma* linear_map_with_bound_coe

Modified src/data/finset.lean
- \+ *lemma* finset.update_eq_piecewise

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* linear_map.curry_uncurry_left
- \+ *def* linear_map.uncurry_left
- \+ *lemma* linear_map.uncurry_left_apply
- \+ *def* multilinear_curry_left_equiv
- \+ *def* multilinear_curry_right_equiv
- \+ *def* multilinear_map.curry_left
- \+ *lemma* multilinear_map.curry_left_apply
- \+ *def* multilinear_map.curry_right
- \+ *lemma* multilinear_map.curry_right_apply
- \+ *lemma* multilinear_map.curry_uncurry_right
- \- *def* multilinear_map.linear_to_multilinear_equiv_multilinear
- \+ *lemma* multilinear_map.mk_pi_ring_apply
- \+ *lemma* multilinear_map.mk_pi_ring_apply_one_eq_self
- \- *def* multilinear_map.multilinear_to_linear_equiv_multilinear
- \+ *lemma* multilinear_map.uncurry_curry_left
- \+ *lemma* multilinear_map.uncurry_curry_right
- \+ *def* multilinear_map.uncurry_right
- \+ *lemma* multilinear_map.uncurry_right_apply

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous_update

Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.continuous_at_iff

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* continuous_at_of_locally_lipschitz



## [2020-02-03 09:55:20](https://github.com/leanprover-community/mathlib/commit/59629da)
chore(*): rename `filter.inhabited_of_mem_sets` to `nonempty_of_mem_sets` ([#1943](https://github.com/leanprover-community/mathlib/pull/1943))
In other names `inhabited` means that we have a `default` element.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.inhabited_of_mem_sets
- \+ *lemma* filter.nonempty_of_mem_sets

Modified src/order/liminf_limsup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/order.lean


Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* sequentially_complete.seq

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
- \+ *lemma* ennreal.add_ne_top
- \+ *lemma* ennreal.max_zero_left
- \+ *lemma* ennreal.max_zero_right
- \+ *lemma* ennreal.of_real_to_real_le
- \+ *lemma* ennreal.sup_eq_max
- \+ *lemma* ennreal.to_real_add_le
- \+ *lemma* ennreal.to_real_le_of_le_of_real
- \+ *lemma* ennreal.to_real_max

Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton.mono
- \+/\- *lemma* set.subsingleton_empty

Modified src/order/bounded_lattice.lean
- \+ *theorem* lattice.ne_top_of_le_ne_top

Modified src/topology/metric_space/basic.lean
- \+ *lemma* edist_lt_top
- \+ *lemma* metric.bounded.ediam_ne_top
- \- *lemma* metric.bounded_iff_diam_ne_top
- \+ *lemma* metric.bounded_iff_ediam_ne_top
- \+/\- *lemma* metric.diam_le_of_forall_dist_le
- \+ *lemma* metric.diam_le_of_forall_dist_le_of_nonempty
- \+/\- *lemma* metric.diam_nonneg
- \+ *lemma* metric.diam_pair
- \+ *lemma* metric.diam_subsingleton
- \+ *lemma* metric.diam_triple
- \+ *lemma* metric.dist_le_diam_of_mem'
- \+ *lemma* metric.ediam_le_of_forall_dist_le

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *def* emetric.diam
- \+ *lemma* emetric.diam_eq_zero_iff
- \+ *lemma* emetric.diam_insert
- \+ *lemma* emetric.diam_le_iff_forall_edist_le
- \+/\- *lemma* emetric.diam_le_of_forall_edist_le
- \+ *lemma* emetric.diam_pair
- \+ *lemma* emetric.diam_pos_iff
- \+ *lemma* emetric.diam_subsingleton
- \+ *lemma* emetric.diam_triple

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
- \+ *lemma* mem_inv_smul_set_iff
- \+ *lemma* mem_smul_set_iff_inv_smul_mem
- \+/\- *lemma* set.mem_smul_set
- \- *lemma* set.one_smul_set
- \- *def* set.pointwise_mul_action
- \+ *lemma* set.smul_mem_smul_set
- \+ *def* set.smul_set_action
- \+ *lemma* set.smul_set_empty
- \+/\- *lemma* set.smul_set_eq_image
- \+ *lemma* set.smul_set_mono
- \+ *lemma* set.smul_set_union

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
- \+ *theorem* set.bex_insert_iff
- \+ *lemma* set.eq_empty_or_nonempty
- \+ *theorem* set.image_pair
- \+ *lemma* set.nonempty.image
- \+ *lemma* set.nonempty.mono
- \+ *lemma* set.nonempty.of_image
- \- *lemma* set.nonempty.of_ssubset'
- \- *lemma* set.nonempty.of_subset
- \- *lemma* set.nonempty_image
- \+ *lemma* set.nonempty_image_iff
- \+ *lemma* set.nonempty_of_ssubset'
- \+ *lemma* set.subset_diff_union
- \- *lemma* set.subset_insert_diff
- \+ *lemma* set.subsingleton.eq_empty_or_singleton
- \+ *lemma* set.subsingleton.eq_singleton_of_mem
- \+ *lemma* set.subsingleton.image
- \+ *lemma* set.subsingleton_empty
- \+ *lemma* set.subsingleton_singleton

Modified src/order/filter/bases.lean




## [2020-02-02 01:12:16](https://github.com/leanprover-community/mathlib/commit/bacd4da)
chore(data/subtype): fix `∀` vs `Π` ([#1940](https://github.com/leanprover-community/mathlib/pull/1940))
#### Estimated changes
Modified src/data/subtype.lean
- \+/\- *def* subtype.restrict
- \+/\- *lemma* subtype.restrict_apply



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
- \+ *lemma* nat.choose_mul_succ_eq
- \+ *lemma* nat.choose_succ_self_right



## [2020-02-01 16:26:13](https://github.com/leanprover-community/mathlib/commit/a500c24)
Update units.lean ([#1938](https://github.com/leanprover-community/mathlib/pull/1938))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_mk_of_mul_eq_one



## [2020-02-01 10:59:44](https://github.com/leanprover-community/mathlib/commit/50bbb8d)
fix(data/nat/basic): make arguments to `choose_succ_right_eq` explicit ([#1935](https://github.com/leanprover-community/mathlib/pull/1935))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+/\- *lemma* nat.choose_succ_right_eq

