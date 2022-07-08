## [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/50a03f7)
chore(test): fix test directory structure
#### Estimated changes
renamed test/tests/coinductive.lean to test/coinductive.lean

renamed test/tests/examples.lean to test/examples.lean

renamed test/tests/fin_cases.lean to test/fin_cases.lean

renamed test/tests/finish1.lean to test/finish1.lean

renamed test/tests/finish2.lean to test/finish2.lean

renamed test/tests/finish3.lean to test/finish3.lean

renamed test/tests/linarith.lean to test/linarith.lean

renamed test/tests/mk_iff_of_inductive.lean to test/mk_iff_of_inductive.lean

renamed test/tests/monotonicity.lean to test/monotonicity.lean

renamed test/tests/monotonicity/test_cases.lean to test/monotonicity/test_cases.lean

renamed test/tests/norm_num.lean to test/norm_num.lean

renamed test/tests/replacer.lean to test/replacer.lean

renamed test/tests/restate_axiom.lean to test/restate_axiom.lean

renamed test/tests/ring.lean to test/ring.lean

renamed test/tests/solve_by_elim.lean to test/solve_by_elim.lean

renamed test/tests/split_ifs.lean to test/split_ifs.lean

renamed test/tests/tactics.lean to test/tactics.lean

renamed test/tests/tidy.lean to test/tidy.lean



## [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/12be0aa)
refactor(category_theory/instances): rename `examples` to `instances`
#### Estimated changes
renamed src/category_theory/examples/measurable_space.lean to src/category_theory/instances/measurable_space.lean

renamed src/category_theory/examples/monoids.lean to src/category_theory/instances/monoids.lean

renamed src/category_theory/examples/rings.lean to src/category_theory/instances/rings.lean

renamed src/category_theory/examples/topological_spaces.lean to src/category_theory/instances/topological_spaces.lean



## [2019-01-30 17:15:23-05:00](https://github.com/leanprover-community/mathlib/commit/829b49b)
chore(.travis.yml): use git clean to clean out untracked files ([#659](https://github.com/leanprover-community/mathlib/pull/659))
* chore(.travis.yml): use git clean to clean out untracked files and delete more obsolete olean files
PR [#641](https://github.com/leanprover-community/mathlib/pull/641) involved renaming a directory. The old directory was still
present in the cache, and in this situation `git status` lists the
directory as a whole as untracked, so the grep did not find any
`.lean` files.
#### Estimated changes
modified .travis.yml

created purge_olean.sh



## [2019-01-30 17:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0eb9db6)
chore(linear_algebra/multivariate_polynomial): move rename to the right place
#### Estimated changes
modified src/data/equiv/algebra.lean
- \- *lemma* rename_C
- \- *lemma* rename_X
- \- *lemma* rename_rename
- \- *lemma* rename_id
- \- *lemma* hom_eq_hom
- \- *lemma* is_id
- \- *def* rename

modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* hom_eq_hom
- \+ *lemma* is_id
- \+ *lemma* rename_C
- \+ *lemma* rename_X
- \+ *lemma* rename_rename
- \+ *lemma* rename_id
- \+ *def* rename



## [2019-01-30 16:37:18+01:00](https://github.com/leanprover-community/mathlib/commit/a480160)
feat(data/polynomial): generalize theorems from nonzero_comm_ring to comm_ring ([#653](https://github.com/leanprover-community/mathlib/pull/653))
#### Estimated changes
modified src/data/polynomial.lean
- \+/\- *lemma* root_X_sub_C
- \+/\- *lemma* root_X_sub_C



## [2019-01-30 16:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/065f083)
feat(group_theory): monoid / group closure of union
#### Estimated changes
modified src/group_theory/subgroup.lean
- \+ *theorem* closure_mono
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mclosure_subset
- \+ *theorem* mclosure_inv_subset
- \+ *theorem* closure_eq_mclosure
- \+ *theorem* mem_closure_union_iff
- \+ *theorem* closure_mono
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mclosure_subset
- \+ *theorem* mclosure_inv_subset
- \+ *theorem* closure_eq_mclosure
- \+ *theorem* mem_closure_union_iff

modified src/group_theory/submonoid.lean
- \+ *theorem* closure_mono
- \+ *theorem* mem_closure_union_iff
- \+ *theorem* closure_mono
- \+ *theorem* mem_closure_union_iff



## [2019-01-30 16:16:31+01:00](https://github.com/leanprover-community/mathlib/commit/f7b9d6b)
refactor(data/equiv/algebra): mv_polynomial mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α)
#### Estimated changes
modified src/data/equiv/algebra.lean
- \+ *lemma* rename_C
- \+ *lemma* rename_X
- \+ *lemma* rename_rename
- \+ *lemma* rename_id
- \+ *lemma* hom_eq_hom
- \+ *lemma* is_id
- \+ *lemma* sum_to_iter_C
- \+ *lemma* sum_to_iter_Xl
- \+ *lemma* sum_to_iter_Xr
- \+ *lemma* iter_to_sum_C_C
- \+ *lemma* iter_to_sum_X
- \+ *lemma* iter_to_sum_C_X
- \- *theorem* of_option_C
- \- *theorem* of_option_X_none
- \- *theorem* of_option_X_some
- \- *theorem* of_option_add
- \- *theorem* of_option_mul
- \- *theorem* to_option_C
- \- *theorem* to_option_C_C
- \- *theorem* to_option_C_X
- \- *theorem* to_option_X
- \- *theorem* to_option_add
- \- *theorem* to_option_mul
- \- *theorem* to_option_of_option
- \- *theorem* of_option_to_option
- \+ *def* rename
- \+/\- *def* pempty_ring_equiv
- \+ *def* punit_ring_equiv
- \+ *def* ring_equiv_congr
- \+ *def* sum_to_iter
- \+ *def* iter_to_sum
- \+ *def* mv_polynomial_equiv_mv_polynomial
- \+ *def* sum_ring_equiv
- \+ *def* option_equiv_left
- \+ *def* option_equiv_right
- \- *def* of_option
- \- *def* to_option
- \- *def* option_ring_equiv
- \+/\- *def* pempty_ring_equiv

modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* eval₂_pow



## [2019-01-30 10:26:08+01:00](https://github.com/leanprover-community/mathlib/commit/aa944bf)
feat(analysis/exponential): real powers, `cpow_nat_inv_pow` ([#647](https://github.com/leanprover-community/mathlib/pull/647))
#### Estimated changes
modified src/analysis/exponential.lean
- \+ *lemma* cpow_def
- \+ *lemma* cpow_zero
- \+ *lemma* zero_cpow
- \+ *lemma* cpow_one
- \+ *lemma* one_cpow
- \+ *lemma* cpow_add
- \+ *lemma* cpow_mul
- \+ *lemma* cpow_neg
- \+ *lemma* cpow_nat_cast
- \+ *lemma* cpow_int_cast
- \+ *lemma* cpow_nat_inv_pow
- \+ *lemma* rpow_def
- \+ *lemma* rpow_def_of_nonneg
- \+ *lemma* of_real_cpow
- \+ *lemma* abs_cpow_real
- \+ *lemma* rpow_zero
- \+ *lemma* zero_rpow
- \+ *lemma* rpow_one
- \+ *lemma* one_rpow
- \+ *lemma* rpow_nonneg_of_nonneg
- \+ *lemma* rpow_add
- \+ *lemma* rpow_mul
- \+ *lemma* rpow_neg
- \+ *lemma* rpow_nat_cast
- \+ *lemma* rpow_int_cast
- \- *lemma* pow_def
- \- *lemma* pow_add
- \- *lemma* pow_mul
- \- *lemma* pow_nat_cast
- \- *lemma* pow_int_cast



## [2019-01-30 09:57:02+01:00](https://github.com/leanprover-community/mathlib/commit/626489a)
feat(topology/metric_space): diameter of a set in metric spaces ([#651](https://github.com/leanprover-community/mathlib/pull/651))
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+ *lemma* diam_nonneg
- \+ *lemma* diam_empty
- \+ *lemma* diam_singleton
- \+ *lemma* bounded_iff_diam_ne_top
- \+ *lemma* diam_eq_zero_of_unbounded
- \+ *lemma* diam_mono
- \+ *lemma* dist_le_diam_of_mem
- \+ *lemma* diam_le_of_forall_dist_le
- \+ *lemma* diam_union
- \+ *lemma* diam_union'
- \+ *lemma* diam_closed_ball
- \+ *lemma* diam_ball
- \+ *def* diam

modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_le_diam_of_mem
- \+ *lemma* diam_le_of_forall_edist_le
- \+ *lemma* diam_empty
- \+ *lemma* diam_singleton
- \+ *lemma* diam_mono
- \+ *lemma* diam_union
- \+ *lemma* diam_union'
- \+ *lemma* diam_closed_ball
- \+ *lemma* diam_ball
- \+ *def* diam



## [2019-01-30 09:55:58+01:00](https://github.com/leanprover-community/mathlib/commit/ef35c6c)
second countability criteria in metric spaces
#### Estimated changes
modified src/topology/continuity.lean
- \+ *lemma* compact_range

modified src/topology/metric_space/basic.lean
- \+ *lemma* second_countable_of_almost_dense_set
- \+ *lemma* second_countable_of_countable_discretization



## [2019-01-30 09:54:34+01:00](https://github.com/leanprover-community/mathlib/commit/30649f5)
cleanup instances/ennreal
#### Estimated changes
modified src/topology/instances/ennreal.lean
- \+ *lemma* emetric.cauchy_seq_iff_le_tendsto_0
- \+ *lemma* continuous_of_le_add_edist
- \- *lemma* continuous_edist
- \+ *theorem* continuous_edist'
- \+ *theorem* continuous_edist
- \+ *theorem* tendsto_edist



## [2019-01-30 09:49:08+01:00](https://github.com/leanprover-community/mathlib/commit/afa535e)
feat(ring_theory/polynomial): hilbert basis theorem
#### Estimated changes
created src/ring_theory/polynomial.lean
- \+ *theorem* mem_degree_le
- \+ *theorem* degree_le_mono
- \+ *theorem* degree_le_eq_span_X_pow
- \+ *theorem* mem_of_polynomial
- \+ *theorem* mem_leading_coeff_nth
- \+ *theorem* mem_leading_coeff_nth_zero
- \+ *theorem* leading_coeff_nth_mono
- \+ *theorem* mem_leading_coeff
- \+ *theorem* is_fg_degree_le
- \+ *theorem* is_noetherian_ring_polynomial
- \+ *def* degree_le
- \+ *def* of_polynomial
- \+ *def* degree_le
- \+ *def* leading_coeff_nth
- \+ *def* leading_coeff



## [2019-01-29 19:13:38+01:00](https://github.com/leanprover-community/mathlib/commit/860eba6)
chore(.): change occurrences of tests directory to test
#### Estimated changes
modified docs/mathlib-overview.md

modified src/tactic/basic.lean



## [2019-01-29 19:07:10+01:00](https://github.com/leanprover-community/mathlib/commit/247dcb2)
feat(linear_algebra): rules for kernel of `of_le`, `cod_restrict`, and `pair`
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* ker_cod_restrict
- \+ *lemma* range_cod_restrict
- \+ *lemma* ker_pair
- \+ *theorem* ker_of_le



## [2019-01-29 18:32:34+01:00](https://github.com/leanprover-community/mathlib/commit/4fb6c7d)
chore(test): rename the test directory so that `leanpkg` will find it
#### Estimated changes
renamed tests/coinductive.lean to test/tests/coinductive.lean

renamed tests/examples.lean to test/tests/examples.lean

renamed tests/fin_cases.lean to test/tests/fin_cases.lean

renamed tests/finish1.lean to test/tests/finish1.lean

renamed tests/finish2.lean to test/tests/finish2.lean

renamed tests/finish3.lean to test/tests/finish3.lean

renamed tests/linarith.lean to test/tests/linarith.lean

renamed tests/mk_iff_of_inductive.lean to test/tests/mk_iff_of_inductive.lean

renamed tests/monotonicity.lean to test/tests/monotonicity.lean

renamed tests/monotonicity/test_cases.lean to test/tests/monotonicity/test_cases.lean

renamed tests/norm_num.lean to test/tests/norm_num.lean

renamed tests/replacer.lean to test/tests/replacer.lean

renamed tests/restate_axiom.lean to test/tests/restate_axiom.lean

renamed tests/ring.lean to test/tests/ring.lean

renamed tests/solve_by_elim.lean to test/tests/solve_by_elim.lean

renamed tests/split_ifs.lean to test/tests/split_ifs.lean

renamed tests/tactics.lean to test/tests/tactics.lean

renamed tests/tidy.lean to test/tests/tidy.lean



## [2019-01-29 17:18:52+01:00](https://github.com/leanprover-community/mathlib/commit/fc529b6)
feat(data/complex/basic): of_real_fpow ([#640](https://github.com/leanprover-community/mathlib/pull/640))
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* map_fpow

modified src/data/complex/basic.lean
- \+/\- *lemma* of_real_inv
- \+ *lemma* of_real_fpow
- \+/\- *lemma* of_real_inv



## [2019-01-29 17:15:53+01:00](https://github.com/leanprover-community/mathlib/commit/d7d90fa)
docs(tactic/monotonicity/interactive): fix `mono` documentation [ci-skip]
#### Estimated changes
modified docs/tactics.md

modified src/tactic/monotonicity/interactive.lean



## [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/0924ac0)
fix build
#### Estimated changes
modified src/data/real/nnreal.lean



## [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/a0e2de9)
refactor(*): use decidable_linear_order.lift
#### Estimated changes
modified src/algebra/ordered_group.lean

modified src/data/fin.lean

modified src/data/real/nnreal.lean



## [2019-01-29 17:15:15+01:00](https://github.com/leanprover-community/mathlib/commit/7cfcce3)
feat(data/equiv/algebra): ring equiv for mv_polynomial
#### Estimated changes
modified src/data/equiv/algebra.lean
- \+ *theorem* of_option_C
- \+ *theorem* of_option_X_none
- \+ *theorem* of_option_X_some
- \+ *theorem* of_option_add
- \+ *theorem* of_option_mul
- \+ *theorem* to_option_C
- \+ *theorem* to_option_C_C
- \+ *theorem* to_option_C_X
- \+ *theorem* to_option_X
- \+ *theorem* to_option_add
- \+ *theorem* to_option_mul
- \+ *theorem* to_option_of_option
- \+ *theorem* of_option_to_option
- \+ *def* ring_equiv_of_equiv
- \+ *def* of_option
- \+ *def* to_option
- \+ *def* option_ring_equiv
- \+ *def* pempty_ring_equiv



## [2019-01-29 13:20:33+01:00](https://github.com/leanprover-community/mathlib/commit/54f4b29)
feat(tactic/interactive.lean): clear_aux_decl
#### Estimated changes
modified docs/tactics.md

modified src/tactic/basic.lean

modified src/tactic/interactive.lean

modified tests/tactics.lean



## [2019-01-29 13:20:13+01:00](https://github.com/leanprover-community/mathlib/commit/8faf8df)
feat(field_theory/splitting_field): splits predicate on polynomials
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* eq_X_add_C_of_degree_eq_one
- \+ *lemma* degree_eq_degree_of_associated

created src/field_theory/splitting_field.lean
- \+ *lemma* splits_zero
- \+ *lemma* splits_C
- \+ *lemma* splits_of_degree_eq_one
- \+ *lemma* splits_of_degree_le_one
- \+ *lemma* splits_mul
- \+ *lemma* splits_of_splits_mul
- \+ *lemma* splits_map_iff
- \+ *lemma* exists_root_of_splits
- \+ *lemma* exists_multiset_of_splits
- \+ *lemma* splits_of_exists_multiset
- \+ *lemma* splits_of_splits_id
- \+ *lemma* splits_iff_exists_multiset
- \+ *lemma* splits_comp_of_splits
- \+ *def* splits

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* exists_mem_factors_of_dvd



## [2019-01-29 13:17:09+01:00](https://github.com/leanprover-community/mathlib/commit/8ee4f2d)
move continuous_of_lipschitz around
#### Estimated changes
modified src/topology/bounded_continuous_function.lean
- \- *lemma* continuous_of_lipschitz

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* uniform_continuous_of_lipschitz
- \+ *lemma* continuous_of_lipschitz
- \+ *lemma* uniform_continuous_of_le_add



## [2019-01-29 11:39:45+01:00](https://github.com/leanprover-community/mathlib/commit/83edba4)
feat(measure_theory): integral is equal and monotone almost-everywhere and for measurable functions it is a.e. strict at 0
#### Estimated changes
modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_le_lintegral_ae
- \+ *lemma* lintegral_congr_ae
- \+ *lemma* lintegral_eq_zero_iff

modified src/measure_theory/measure_space.lean
- \+ *lemma* exists_is_measurable_superset_of_measure_eq_zero
- \+ *lemma* mem_a_e_iff
- \+ *lemma* all_ae_congr
- \+ *lemma* all_ae_iff
- \+ *lemma* all_ae_all_iff
- \+ *def* all_ae



## [2019-01-29 09:37:59+01:00](https://github.com/leanprover-community/mathlib/commit/cd41aca)
Move tendsto_div to a better place
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_one_div_add_at_top_nhds_0_nat

modified src/data/real/cau_seq_filter.lean
- \- *lemma* tendsto_div

modified src/topology/sequences.lean



## [2019-01-28 20:15:38+01:00](https://github.com/leanprover-community/mathlib/commit/042c290)
refactor(category_theory/opposites): Make `opposite` irreducible
#### Estimated changes
modified src/category_theory/adjunction.lean

modified src/category_theory/limits/cones.lean
- \+/\- *lemma* cones_obj
- \+/\- *lemma* cones_map_app
- \+/\- *lemma* cocones_obj
- \+/\- *lemma* cocones_map
- \+/\- *lemma* cones_obj
- \+/\- *lemma* cones_map_app
- \+/\- *lemma* cocones_obj
- \+/\- *lemma* cocones_map
- \+/\- *def* cocones
- \+/\- *def* extensions
- \+/\- *def* cocones
- \+/\- *def* extensions

modified src/category_theory/limits/limits.lean
- \+/\- *def* nat_iso
- \+/\- *def* limit.hom_iso
- \+/\- *def* nat_iso
- \+/\- *def* limit.hom_iso

modified src/category_theory/opposites.lean
- \+ *lemma* unop_op
- \+ *lemma* op_unop
- \+ *lemma* has_hom.hom.op_inj
- \+ *lemma* has_hom.hom.unop_inj
- \+ *lemma* has_hom.hom.unop_op
- \+ *lemma* has_hom.hom.op_unop
- \+ *lemma* op_comp
- \+ *lemma* op_id
- \+ *lemma* unop_comp
- \+ *lemma* unop_id
- \+/\- *lemma* op_obj
- \+/\- *lemma* op_map
- \+/\- *lemma* unop_obj
- \+/\- *lemma* unop_map
- \+/\- *lemma* op_hom.obj
- \+/\- *lemma* op_hom.map_app
- \+/\- *lemma* op_inv.obj
- \+/\- *lemma* hom_obj
- \+/\- *lemma* op_obj
- \+/\- *lemma* op_map
- \+/\- *lemma* unop_obj
- \+/\- *lemma* unop_map
- \+/\- *lemma* op_hom.obj
- \+/\- *lemma* op_hom.map_app
- \+/\- *lemma* op_inv.obj
- \- *lemma* op_id_app
- \- *lemma* op_comp_app
- \+/\- *lemma* hom_obj
- \+ *def* opposite
- \+/\- *def* op
- \+ *def* unop
- \+ *def* has_hom.hom.op
- \+ *def* has_hom.hom.unop
- \+/\- *def* op

modified src/category_theory/yoneda.lean
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *lemma* obj_map_id
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *lemma* obj_map_id
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *def* yoneda_sections
- \+/\- *def* yoneda_sections_small
- \+/\- *def* yoneda_sections
- \+/\- *def* yoneda_sections_small



## [2019-01-28 20:11:16+01:00](https://github.com/leanprover-community/mathlib/commit/d1b7d91)
feat(category_theory/limits/cones): forgetful functors
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+ *lemma* forget_obj
- \+ *lemma* forget_map
- \+ *lemma* forget_obj
- \+ *lemma* forget_map
- \+ *def* forget
- \+ *def* forget



## [2019-01-28 19:59:32+01:00](https://github.com/leanprover-community/mathlib/commit/b39d6d8)
feat(*) refactor module
#### Estimated changes
modified src/algebra/module.lean
- \+/\- *lemma* comp_apply
- \+/\- *lemma* neg_mem
- \+/\- *lemma* comp_apply
- \+/\- *lemma* neg_mem
- \+/\- *theorem* one_smul
- \+/\- *theorem* zero_smul
- \+/\- *theorem* is_linear
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mk'_apply
- \+/\- *theorem* one_smul
- \+/\- *theorem* zero_smul
- \+/\- *theorem* is_linear
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mk'_apply
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* mk'
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* mk'

modified src/algebra/pi_instances.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/data/dfinsupp.lean
- \+/\- *lemma* mk_smul
- \+/\- *lemma* lmk_apply
- \+/\- *lemma* lsingle_apply
- \+/\- *lemma* mk_smul
- \+/\- *lemma* lmk_apply
- \+/\- *lemma* lsingle_apply
- \+/\- *def* lmk
- \+/\- *def* lsingle
- \+/\- *def* lmk
- \+/\- *def* lsingle

modified src/data/finsupp.lean
- \+/\- *def* to_has_scalar'
- \+/\- *def* to_has_scalar'

modified src/linear_algebra/basic.lean
- \+/\- *lemma* zero_apply
- \+/\- *lemma* sum_apply
- \+/\- *lemma* one_app
- \+/\- *lemma* mul_app
- \+/\- *lemma* map_coe
- \+/\- *lemma* mem_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_mono
- \+/\- *lemma* comap_coe
- \+/\- *lemma* mem_comap
- \+/\- *lemma* comap_comp
- \+/\- *lemma* comap_mono
- \+/\- *lemma* comap_top
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_inf_eq_map_inf_comap
- \+/\- *lemma* mem_span
- \+/\- *lemma* subset_span
- \+/\- *lemma* span_le
- \+/\- *lemma* span_mono
- \+/\- *lemma* span_eq_of_le
- \+/\- *lemma* span_eq
- \+/\- *lemma* span_induction
- \+/\- *lemma* span_empty
- \+/\- *lemma* span_union
- \+/\- *lemma* span_Union
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* span_singleton_eq_range
- \+/\- *lemma* mem_span_insert
- \+/\- *lemma* mem_span_insert'
- \+/\- *lemma* span_insert_eq_span
- \+/\- *lemma* span_span
- \+/\- *lemma* span_eq_bot
- \+/\- *lemma* span_singleton_eq_bot
- \+/\- *lemma* span_image
- \+/\- *lemma* range_le_iff_comap
- \+/\- *lemma* le_ker_iff_map
- \+/\- *lemma* map_comap_eq
- \+/\- *lemma* map_comap_eq_self
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* comap_map_eq_self
- \- *lemma* classical.some_spec3
- \+/\- *lemma* zero_apply
- \+/\- *lemma* sum_apply
- \+/\- *lemma* one_app
- \+/\- *lemma* mul_app
- \+/\- *lemma* map_coe
- \+/\- *lemma* mem_map
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_mono
- \+/\- *lemma* comap_coe
- \+/\- *lemma* mem_comap
- \+/\- *lemma* comap_comp
- \+/\- *lemma* comap_mono
- \+/\- *lemma* comap_top
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_inf_eq_map_inf_comap
- \+/\- *lemma* mem_span
- \+/\- *lemma* subset_span
- \+/\- *lemma* span_le
- \+/\- *lemma* span_mono
- \+/\- *lemma* span_eq_of_le
- \+/\- *lemma* span_eq
- \+/\- *lemma* span_induction
- \+/\- *lemma* span_empty
- \+/\- *lemma* span_union
- \+/\- *lemma* span_Union
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* span_singleton_eq_range
- \+/\- *lemma* mem_span_insert
- \+/\- *lemma* mem_span_insert'
- \+/\- *lemma* span_insert_eq_span
- \+/\- *lemma* span_span
- \+/\- *lemma* span_eq_bot
- \+/\- *lemma* span_singleton_eq_bot
- \+/\- *lemma* span_image
- \+/\- *lemma* range_le_iff_comap
- \+/\- *lemma* le_ker_iff_map
- \+/\- *lemma* map_comap_eq
- \+/\- *lemma* map_comap_eq_self
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* comap_map_eq_self
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* cod_restrict_apply
- \+/\- *theorem* smul_right_apply
- \+/\- *theorem* fst_apply
- \+/\- *theorem* snd_apply
- \+/\- *theorem* pair_apply
- \+/\- *theorem* fst_pair
- \+/\- *theorem* snd_pair
- \+/\- *theorem* pair_fst_snd
- \+/\- *theorem* inl_apply
- \+/\- *theorem* inr_apply
- \+/\- *theorem* copair_apply
- \+/\- *theorem* copair_inl
- \+/\- *theorem* copair_inr
- \+/\- *theorem* copair_inl_inr
- \+/\- *theorem* fst_eq_copair
- \+/\- *theorem* snd_eq_copair
- \+/\- *theorem* inl_eq_pair
- \+/\- *theorem* inr_eq_pair
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* map_cod_restrict
- \+/\- *theorem* comap_cod_restrict
- \+/\- *theorem* range_coe
- \+/\- *theorem* mem_range
- \+/\- *theorem* range_id
- \+/\- *theorem* range_comp
- \+/\- *theorem* range_comp_le_range
- \+/\- *theorem* range_eq_top
- \+/\- *theorem* mem_ker
- \+/\- *theorem* ker_id
- \+/\- *theorem* ker_comp
- \+/\- *theorem* ker_le_ker_comp
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot
- \+/\- *theorem* ker_zero
- \+/\- *theorem* ker_eq_top
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* map_injective
- \+/\- *theorem* comap_le_comap_iff
- \+/\- *theorem* comap_injective
- \+/\- *theorem* map_copair_prod
- \+/\- *theorem* comap_pair_prod
- \+/\- *theorem* map_top
- \+/\- *theorem* comap_bot
- \+/\- *theorem* map_inl
- \+/\- *theorem* map_inr
- \+/\- *theorem* comap_fst
- \+/\- *theorem* comap_snd
- \+/\- *theorem* prod_comap_inl
- \+/\- *theorem* prod_comap_inr
- \+/\- *theorem* prod_map_fst
- \+/\- *theorem* prod_map_snd
- \+/\- *theorem* ker_inl
- \+/\- *theorem* ker_inr
- \+/\- *theorem* range_fst
- \+/\- *theorem* range_snd
- \+/\- *theorem* liftq_apply
- \+/\- *theorem* liftq_mkq
- \+/\- *theorem* mapq_apply
- \+/\- *theorem* mapq_mkq
- \+/\- *theorem* comap_liftq
- \+ *theorem* map_liftq
- \+/\- *theorem* ker_liftq
- \+ *theorem* range_liftq
- \+/\- *theorem* ker_liftq_eq_bot
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* coe_apply
- \+/\- *theorem* of_bijective_apply
- \+/\- *theorem* of_linear_apply
- \+/\- *theorem* of_linear_symm_apply
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* cod_restrict_apply
- \+/\- *theorem* smul_right_apply
- \+/\- *theorem* fst_apply
- \+/\- *theorem* snd_apply
- \+/\- *theorem* pair_apply
- \+/\- *theorem* fst_pair
- \+/\- *theorem* snd_pair
- \+/\- *theorem* pair_fst_snd
- \+/\- *theorem* inl_apply
- \+/\- *theorem* inr_apply
- \+/\- *theorem* copair_apply
- \+/\- *theorem* copair_inl
- \+/\- *theorem* copair_inr
- \+/\- *theorem* copair_inl_inr
- \+/\- *theorem* fst_eq_copair
- \+/\- *theorem* snd_eq_copair
- \+/\- *theorem* inl_eq_pair
- \+/\- *theorem* inr_eq_pair
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* map_cod_restrict
- \+/\- *theorem* comap_cod_restrict
- \+/\- *theorem* range_coe
- \+/\- *theorem* mem_range
- \+/\- *theorem* range_id
- \+/\- *theorem* range_comp
- \+/\- *theorem* range_comp_le_range
- \+/\- *theorem* range_eq_top
- \+/\- *theorem* mem_ker
- \+/\- *theorem* ker_id
- \+/\- *theorem* ker_comp
- \+/\- *theorem* ker_le_ker_comp
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot
- \+/\- *theorem* ker_zero
- \+/\- *theorem* ker_eq_top
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* map_injective
- \+/\- *theorem* comap_le_comap_iff
- \+/\- *theorem* comap_injective
- \+/\- *theorem* map_copair_prod
- \+/\- *theorem* comap_pair_prod
- \+/\- *theorem* map_top
- \+/\- *theorem* comap_bot
- \+/\- *theorem* map_inl
- \+/\- *theorem* map_inr
- \+/\- *theorem* comap_fst
- \+/\- *theorem* comap_snd
- \+/\- *theorem* prod_comap_inl
- \+/\- *theorem* prod_comap_inr
- \+/\- *theorem* prod_map_fst
- \+/\- *theorem* prod_map_snd
- \+/\- *theorem* ker_inl
- \+/\- *theorem* ker_inr
- \+/\- *theorem* range_fst
- \+/\- *theorem* range_snd
- \+/\- *theorem* liftq_apply
- \+/\- *theorem* liftq_mkq
- \+/\- *theorem* mapq_apply
- \+/\- *theorem* mapq_mkq
- \+/\- *theorem* comap_liftq
- \+/\- *theorem* ker_liftq
- \+/\- *theorem* ker_liftq_eq_bot
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* coe_apply
- \+/\- *theorem* of_bijective_apply
- \+/\- *theorem* of_linear_apply
- \+/\- *theorem* of_linear_symm_apply
- \+/\- *def* cod_restrict
- \+/\- *def* inverse
- \+/\- *def* smul_right
- \+/\- *def* endomorphism_ring
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* pair
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* copair
- \+/\- *def* congr_right
- \+/\- *def* of_le
- \+/\- *def* map
- \+/\- *def* comap
- \+/\- *def* range
- \+/\- *def* ker
- \+/\- *def* mkq
- \+/\- *def* liftq
- \+/\- *def* mapq
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* of_linear
- \+/\- *def* of_top
- \+/\- *def* congr_right
- \+ *def* sup_quotient_to_quotient_inf
- \+/\- *def* cod_restrict
- \+/\- *def* inverse
- \+/\- *def* smul_right
- \+/\- *def* endomorphism_ring
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* pair
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* copair
- \+/\- *def* congr_right
- \+/\- *def* of_le
- \+/\- *def* map
- \+/\- *def* comap
- \+/\- *def* range
- \+/\- *def* ker
- \+/\- *def* mkq
- \+/\- *def* liftq
- \+/\- *def* mapq
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* of_linear
- \+/\- *def* of_top
- \+/\- *def* congr_right

modified src/linear_algebra/basis.lean
- \+/\- *lemma* linear_independent_empty
- \+/\- *lemma* linear_independent.mono
- \+/\- *lemma* linear_independent.unique
- \+/\- *lemma* zero_not_mem_of_linear_independent
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* linear_independent.repr_range
- \+/\- *lemma* linear_independent.repr_eq
- \+/\- *lemma* linear_independent.repr_supported
- \+/\- *lemma* linear_independent.of_image
- \+/\- *lemma* linear_independent.disjoint_ker
- \+/\- *lemma* linear_independent.inj_span_iff_inj
- \+/\- *lemma* linear_independent.image
- \+/\- *lemma* is_basis.mem_span
- \+/\- *lemma* is_basis.total_repr
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_supported
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* constr_congr
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_zero
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_range
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* is_basis_injective
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* mem_span_insert_exchange
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_left_inverse_linear_map_of_injective
- \+/\- *lemma* exists_right_inverse_linear_map_of_surjective
- \+/\- *lemma* linear_independent_empty
- \+/\- *lemma* linear_independent.mono
- \+/\- *lemma* linear_independent.unique
- \+/\- *lemma* zero_not_mem_of_linear_independent
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* linear_independent.repr_range
- \+/\- *lemma* linear_independent.repr_eq
- \+/\- *lemma* linear_independent.repr_supported
- \+/\- *lemma* linear_independent.of_image
- \+/\- *lemma* linear_independent.disjoint_ker
- \+/\- *lemma* linear_independent.inj_span_iff_inj
- \+/\- *lemma* linear_independent.image
- \+/\- *lemma* is_basis.mem_span
- \+/\- *lemma* is_basis.total_repr
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_supported
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* constr_congr
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_zero
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_range
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* is_basis_injective
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* mem_span_insert_exchange
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_left_inverse_linear_map_of_injective
- \+/\- *lemma* exists_right_inverse_linear_map_of_surjective
- \+/\- *theorem* linear_independent_iff
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *theorem* linear_independent_iff
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *def* linear_independent.total_equiv
- \+/\- *def* linear_independent.repr
- \+/\- *def* is_basis
- \+/\- *def* module_equiv_lc
- \+/\- *def* linear_independent.total_equiv
- \+/\- *def* linear_independent.repr
- \+/\- *def* is_basis
- \+/\- *def* module_equiv_lc

modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_eq_surjective
- \+/\- *lemma* dim_le_surjective
- \+/\- *lemma* dim_eq_injective
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_eq_surjective
- \+/\- *lemma* dim_le_surjective
- \+/\- *lemma* dim_eq_injective
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *def* rank
- \+/\- *def* rank

modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* to_module_lof
- \+/\- *lemma* to_module_lof
- \+/\- *theorem* mk_smul
- \+/\- *theorem* of_smul
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+/\- *theorem* mk_smul
- \+/\- *theorem* of_smul
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+/\- *def* lmk
- \+/\- *def* lof
- \+/\- *def* to_module
- \+/\- *def* lmk
- \+/\- *def* lof
- \+/\- *def* to_module

modified src/linear_algebra/linear_combination.lean
- \+/\- *lemma* linear_eq_on
- \+/\- *lemma* linear_eq_on
- \+/\- *theorem* range_restrict_dom
- \+/\- *theorem* supported_empty
- \+/\- *theorem* supported_univ
- \+/\- *theorem* total_range
- \+/\- *theorem* map_id
- \+/\- *theorem* map_total
- \+/\- *theorem* span_eq_map_lc
- \+/\- *theorem* mem_span_iff_lc
- \+/\- *theorem* lc.total_on_range
- \+/\- *theorem* range_restrict_dom
- \+/\- *theorem* supported_empty
- \+/\- *theorem* supported_univ
- \+/\- *theorem* total_range
- \+/\- *theorem* map_id
- \+/\- *theorem* map_total
- \+/\- *theorem* span_eq_map_lc
- \+/\- *theorem* mem_span_iff_lc
- \+/\- *theorem* lc.total_on_range
- \+/\- *def* restrict_dom
- \+/\- *def* lc.total_on
- \+/\- *def* restrict_dom
- \+/\- *def* lc.total_on

modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* add_tmul
- \+/\- *lemma* tmul_add
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *lemma* zero_tmul
- \+/\- *lemma* tmul_zero
- \+/\- *lemma* neg_tmul
- \+/\- *lemma* tmul_neg
- \+/\- *lemma* lift_aux.smul
- \+/\- *lemma* add_tmul
- \+/\- *lemma* tmul_add
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *lemma* zero_tmul
- \+/\- *lemma* tmul_zero
- \+/\- *lemma* neg_tmul
- \+/\- *lemma* tmul_neg
- \+/\- *lemma* lift_aux.smul
- \+/\- *theorem* ext₂
- \+/\- *theorem* flip_inj
- \+/\- *theorem* map_smul₂
- \+/\- *theorem* lcomp_apply
- \+/\- *theorem* llcomp_apply
- \+/\- *theorem* compl₂_apply
- \+/\- *theorem* compr₂_apply
- \+/\- *theorem* lift.unique
- \+/\- *theorem* ext
- \+/\- *theorem* uncurry_apply
- \+/\- *theorem* lcurry_apply
- \+/\- *theorem* curry_apply
- \+/\- *theorem* map_tmul
- \+/\- *theorem* ext₂
- \+/\- *theorem* flip_inj
- \+/\- *theorem* map_smul₂
- \+/\- *theorem* lcomp_apply
- \+/\- *theorem* llcomp_apply
- \+/\- *theorem* compl₂_apply
- \+/\- *theorem* compr₂_apply
- \+/\- *theorem* lift.unique
- \+/\- *theorem* ext
- \+/\- *theorem* uncurry_apply
- \+/\- *theorem* lcurry_apply
- \+/\- *theorem* curry_apply
- \+/\- *theorem* map_tmul
- \+/\- *def* lflip
- \+/\- *def* lcomp
- \+/\- *def* llcomp
- \+/\- *def* compl₂
- \+/\- *def* tmul
- \+/\- *def* smul.aux
- \+/\- *def* lift_aux
- \+/\- *def* uncurry
- \+/\- *def* lcurry
- \+/\- *def* curry
- \+/\- *def* map
- \+/\- *def* congr
- \+/\- *def* direct_sum
- \+/\- *def* lflip
- \+/\- *def* lcomp
- \+/\- *def* llcomp
- \+/\- *def* compl₂
- \+/\- *def* tmul
- \+/\- *def* smul.aux
- \+/\- *def* lift_aux
- \+/\- *def* uncurry
- \+/\- *def* lcurry
- \+/\- *def* curry
- \+/\- *def* map
- \+/\- *def* congr
- \+/\- *def* direct_sum

modified src/measure_theory/outer_measure.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/ideal_operations.lean
- \+/\- *theorem* bot_smul
- \+/\- *theorem* top_smul
- \+/\- *theorem* span_smul_span
- \+/\- *theorem* bot_smul
- \+/\- *theorem* top_smul
- \+/\- *theorem* span_smul_span

modified src/ring_theory/ideals.lean
- \+/\- *def* span
- \+/\- *def* span

modified src/ring_theory/noetherian.lean
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *def* fg
- \+/\- *def* fg

modified src/ring_theory/principal_ideal_domain.lean



## [2019-01-28 19:52:47+01:00](https://github.com/leanprover-community/mathlib/commit/fd3e5a1)
fix(topology/instances/ennreal): fix merge
#### Estimated changes
modified src/topology/instances/ennreal.lean



## [2019-01-28 19:34:07+01:00](https://github.com/leanprover-community/mathlib/commit/e62c534)
add ennreal.to_real
#### Estimated changes
modified src/data/real/ennreal.lean
- \+ *lemma* of_real_to_real
- \+ *lemma* to_real_of_real
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+ *lemma* to_real_nonneg
- \+ *lemma* top_to_real
- \+ *lemma* zero_to_real
- \+ *lemma* of_real_zero
- \+ *lemma* of_real_one
- \+ *lemma* to_real_eq_zero_iff
- \+ *lemma* of_real_ne_top
- \+ *lemma* top_ne_of_real
- \+ *lemma* to_real_add
- \+ *lemma* of_real_add
- \+ *lemma* to_real_le_to_real
- \+ *lemma* to_real_lt_to_real
- \+ *lemma* of_real_le_of_real
- \+ *lemma* of_real_le_of_real_iff
- \+ *lemma* of_real_lt_of_real_iff
- \+ *lemma* of_real_pos
- \+ *lemma* of_real_eq_zero
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one

modified src/data/real/nnreal.lean
- \+ *lemma* of_real_one

modified src/topology/instances/ennreal.lean
- \+ *lemma* continuous_of_real
- \+ *lemma* tendsto_of_real

modified src/topology/metric_space/basic.lean
- \+ *lemma* nndist_edist
- \+ *lemma* edist_nndist
- \+ *lemma* dist_nndist
- \+ *lemma* nndist_dist
- \+ *lemma* dist_edist
- \+ *lemma* metric.emetric_ball
- \+ *lemma* metric.emetric_closed_ball
- \+ *lemma* sum.dist_eq
- \- *lemma* edist_eq_nndist
- \- *lemma* nndist_eq_edist
- \- *lemma* nndist_eq_dist
- \- *lemma* dist_eq_nndist
- \- *lemma* dist_eq_edist
- \- *lemma* edist_eq_dist
- \+/\- *theorem* edist_dist
- \+/\- *theorem* edist_dist
- \+/\- *def* metric_space.replace_uniformity
- \+ *def* emetric_space.to_metric_space
- \+/\- *def* metric_space.replace_uniformity

modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* mem_closed_ball_self
- \+ *theorem* ball_eq_empty_iff



## [2019-01-28 17:14:45+01:00](https://github.com/leanprover-community/mathlib/commit/8572c6b)
feat(topology): prove continuity of nndist and edist; `ball a r` is a metric space
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous_nnnorm
- \+ *lemma* continuous_smul

modified src/data/real/ennreal.lean
- \+/\- *lemma* mul_eq_top
- \+ *lemma* mul_lt_top
- \+ *lemma* infi_ennreal
- \+/\- *lemma* mul_eq_top

modified src/topology/instances/ennreal.lean
- \+ *lemma* infi_real_pos_eq_infi_nnreal_pos
- \+ *lemma* edist_ne_top_of_mem_ball
- \+ *lemma* nhds_eq_nhds_emetric_ball
- \+ *lemma* continuous_edist
- \+ *def* metric_space_emetric_ball

modified src/topology/instances/nnreal.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* uniform_continuous_nndist'
- \+ *lemma* continuous_nndist'
- \+ *lemma* tendsto_nndist'

modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniformity_edist_nnreal



## [2019-01-28 10:14:51+01:00](https://github.com/leanprover-community/mathlib/commit/afa31be)
refactor(linear_algebra/direct_sum_module): move to algebra/direct_sum
#### Estimated changes
created src/algebra/direct_sum.lean
- \+ *lemma* mk_zero
- \+ *lemma* mk_add
- \+ *lemma* mk_neg
- \+ *lemma* mk_sub
- \+ *lemma* of_zero
- \+ *lemma* of_add
- \+ *lemma* of_neg
- \+ *lemma* of_sub
- \+ *lemma* to_group_zero
- \+ *lemma* to_group_add
- \+ *lemma* to_group_neg
- \+ *lemma* to_group_sub
- \+ *lemma* to_group_of
- \+ *theorem* mk_inj
- \+ *theorem* of_inj
- \+ *theorem* to_group.unique
- \+ *def* direct_sum
- \+ *def* mk
- \+ *def* of
- \+ *def* to_group
- \+ *def* set_to_set

modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* to_module_lof
- \- *lemma* to_module_apply
- \- *lemma* to_module.of
- \+ *theorem* mk_smul
- \+ *theorem* of_smul
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \- *theorem* mk_inj
- \- *theorem* of_inj
- \- *theorem* to_module_aux.add
- \- *theorem* to_module_aux.smul
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+ *def* lmk
- \+ *def* lof
- \+/\- *def* to_module
- \+ *def* lset_to_set
- \- *def* direct_sum
- \- *def* mk
- \- *def* of
- \- *def* to_module_aux
- \+/\- *def* to_module
- \- *def* set_to_set

modified src/linear_algebra/tensor_product.lean
- \+/\- *def* direct_sum
- \+/\- *def* direct_sum



## [2019-01-28 08:02:17+01:00](https://github.com/leanprover-community/mathlib/commit/7199bb3)
chore(linear_algebra/dimension): simplify dim_add_le_dim_add_dim
#### Estimated changes
modified src/linear_algebra/dimension.lean

modified src/measure_theory/integration.lean
- \+ *lemma* add_apply

modified src/topology/instances/ennreal.lean



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/038e0b2)
feat(ring_theory/algebra): remove out_param
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *theorem* ext
- \+/\- *theorem* commutes
- \+/\- *theorem* to_linear_map_inj
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* to_comap_apply
- \+/\- *theorem* eval_unique
- \+/\- *theorem* eval_unique
- \+/\- *theorem* of_id_apply
- \+/\- *theorem* mem_bot
- \+/\- *theorem* ext
- \+/\- *theorem* commutes
- \+/\- *theorem* to_linear_map_inj
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* to_comap_apply
- \+/\- *theorem* eval_unique
- \+/\- *theorem* eval_unique
- \+/\- *theorem* of_id_apply
- \+/\- *theorem* mem_bot
- \+/\- *def* algebra_map
- \+/\- *def* comp
- \+ *def* comap.to_comap
- \+ *def* comap.of_comap
- \+/\- *def* to_comap
- \+/\- *def* comap
- \+/\- *def* aeval
- \+/\- *def* aeval
- \+/\- *def* val
- \+/\- *def* to_top
- \+/\- *def* algebra_map
- \- *def* of_subring
- \+/\- *def* comp
- \+/\- *def* to_comap
- \+/\- *def* comap
- \+/\- *def* aeval
- \+/\- *def* aeval
- \+/\- *def* val
- \+/\- *def* to_top



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/af7a7ee)
feat(ring_theory/algebra): remove of_core
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+ *lemma* mul_smul_comm
- \+ *lemma* smul_mul_assoc
- \- *lemma* smul_mul
- \+ *def* of_ring_hom
- \+/\- *def* of_subring
- \+/\- *def* ring.to_ℤ_algebra
- \- *def* of_core
- \+/\- *def* of_subring
- \+/\- *def* ring.to_ℤ_algebra



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/79ba61c)
feat(ring_theory/algebra): make algebra a class
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* smul_mul
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* smul_mul
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *theorem* smul_def
- \+/\- *theorem* commutes
- \+/\- *theorem* left_comm
- \+/\- *theorem* ext
- \+/\- *theorem* commutes
- \+/\- *theorem* to_linear_map_inj
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* to_comap_apply
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *theorem* mem_coe
- \+/\- *theorem* ext
- \+/\- *theorem* of_id_apply
- \+/\- *theorem* mem_bot
- \+/\- *theorem* mem_top
- \+/\- *theorem* smul_def
- \+/\- *theorem* commutes
- \+/\- *theorem* left_comm
- \+/\- *theorem* ext
- \+/\- *theorem* commutes
- \+/\- *theorem* to_linear_map_inj
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* to_comap_apply
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *theorem* mem_coe
- \+/\- *theorem* ext
- \+/\- *theorem* of_id_apply
- \+/\- *theorem* mem_bot
- \+/\- *theorem* mem_top
- \+ *def* algebra_map
- \+/\- *def* lmul
- \+/\- *def* lmul_left
- \+/\- *def* lmul_right
- \+/\- *def* to_linear_map
- \+/\- *def* comp
- \+/\- *def* comap
- \+/\- *def* to_comap
- \+/\- *def* comap
- \+/\- *def* aeval
- \+/\- *def* aeval
- \+/\- *def* val
- \+/\- *def* to_submodule
- \+/\- *def* of_id
- \+/\- *def* adjoin
- \+/\- *def* to_top
- \- *def* right
- \- *def* polynomial
- \- *def* mv_polynomial
- \+/\- *def* lmul
- \+/\- *def* lmul_left
- \+/\- *def* lmul_right
- \+/\- *def* to_linear_map
- \+/\- *def* comp
- \+/\- *def* comap
- \+/\- *def* to_comap
- \+/\- *def* comap
- \+/\- *def* aeval
- \+/\- *def* aeval
- \+/\- *def* val
- \+/\- *def* to_submodule
- \+/\- *def* of_id
- \+/\- *def* adjoin
- \+/\- *def* to_top



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/a0b6cae)
feat(ring_theory/algebra): define algebra over a commutative ring
#### Estimated changes
created src/ring_theory/algebra.lean
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* smul_mul
- \+ *lemma* lmul_apply
- \+ *lemma* lmul_left_apply
- \+ *lemma* lmul_right_apply
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* to_linear_map_apply
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *theorem* smul_def
- \+ *theorem* commutes
- \+ *theorem* left_comm
- \+ *theorem* ext
- \+ *theorem* commutes
- \+ *theorem* to_linear_map_inj
- \+ *theorem* comp_id
- \+ *theorem* id_comp
- \+ *theorem* comp_assoc
- \+ *theorem* to_comap_apply
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *theorem* mem_coe
- \+ *theorem* ext
- \+ *theorem* of_id_apply
- \+ *theorem* mem_bot
- \+ *theorem* mem_top
- \+ *def* right
- \+ *def* of_core
- \+ *def* polynomial
- \+ *def* mv_polynomial
- \+ *def* of_subring
- \+ *def* lmul
- \+ *def* lmul_left
- \+ *def* lmul_right
- \+ *def* to_linear_map
- \+ *def* comp
- \+ *def* comap
- \+ *def* to_comap
- \+ *def* comap
- \+ *def* aeval
- \+ *def* aeval
- \+ *def* ring.to_ℤ_algebra
- \+ *def* is_ring_hom.to_ℤ_alg_hom
- \+ *def* val
- \+ *def* to_submodule
- \+ *def* comap
- \+ *def* under
- \+ *def* of_id
- \+ *def* adjoin
- \+ *def* to_top



## [2019-01-27 22:44:50+01:00](https://github.com/leanprover-community/mathlib/commit/1d2eda7)
feat(category_theory/isomorphism): as_iso
Also clean up some proofs.
#### Estimated changes
modified src/category_theory/isomorphism.lean
- \+/\- *lemma* ext
- \+ *lemma* as_iso_hom
- \+ *lemma* as_iso_inv
- \+/\- *lemma* ext
- \+ *def* as_iso
- \+/\- *def* on_iso
- \+/\- *def* on_iso



## [2019-01-27 22:43:45+01:00](https://github.com/leanprover-community/mathlib/commit/ccd895f)
feat(category_theory/types): conversions between iso and equiv
#### Estimated changes
modified src/category_theory/types.lean
- \+ *lemma* to_iso_hom
- \+ *lemma* to_iso_inv
- \+ *lemma* to_equiv_fun
- \+ *lemma* to_equiv_symm_fun
- \+ *def* to_iso
- \+ *def* to_equiv



## [2019-01-27 22:42:53+01:00](https://github.com/leanprover-community/mathlib/commit/d074b51)
refactor(category_theory/concrete_category): move `bundled` to own file
#### Estimated changes
modified src/category_theory/category.lean
- \- *lemma* concrete_category_id
- \- *lemma* concrete_category_comp
- \- *lemma* bundled_hom_coe
- \- *def* mk_ob

created src/category_theory/concrete_category.lean
- \+ *lemma* concrete_category_id
- \+ *lemma* concrete_category_comp
- \+ *lemma* bundled_hom_coe
- \+ *def* mk_ob
- \+ *def* map
- \+ *def* concrete_functor
- \+ *def* forget

modified src/category_theory/examples/measurable_space.lean

modified src/category_theory/examples/monoids.lean

modified src/category_theory/examples/rings.lean

modified src/category_theory/examples/topological_spaces.lean

modified src/category_theory/functor.lean
- \- *def* bundled.map
- \- *def* concrete_functor

modified src/category_theory/types.lean
- \- *def* forget



## [2019-01-27 22:40:37+01:00](https://github.com/leanprover-community/mathlib/commit/50398e5)
feat(category_theory/full_subcategory): induced categories
#### Estimated changes
modified src/category_theory/full_subcategory.lean
- \+ *lemma* induced_functor.obj
- \+ *lemma* induced_functor.hom
- \+ *lemma* full_subcategory_inclusion.obj
- \+ *lemma* full_subcategory_inclusion.map
- \+ *def* induced_category
- \+ *def* induced_functor
- \+/\- *def* full_subcategory_inclusion
- \+/\- *def* full_subcategory_inclusion



## [2019-01-27 22:37:46+01:00](https://github.com/leanprover-community/mathlib/commit/19c2f68)
feat(analysis/exponential): complex powers
#### Estimated changes
modified src/analysis/exponential.lean
- \+ *lemma* log_mul
- \+ *lemma* exp_eq_one_iff
- \+ *lemma* exp_eq_exp_iff_exp_sub_eq_one
- \+ *lemma* exp_eq_exp_iff_exists_int
- \+ *lemma* pow_def
- \+ *lemma* pow_add
- \+ *lemma* pow_mul
- \+ *lemma* pow_nat_cast
- \+ *lemma* pow_int_cast



## [2019-01-27 22:33:10+01:00](https://github.com/leanprover-community/mathlib/commit/c057758)
feat(data/complex/exponential): exp_eq_one_iff
#### Estimated changes
modified src/data/complex/exponential.lean
- \+ *lemma* exp_eq_one_iff



## [2019-01-27 22:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/db69173)
refactor(algebra/field_power): notation for fpow
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* fpow_of_nat
- \+ *lemma* fpow_neg_succ_of_nat
- \+/\- *lemma* fpow_eq_gpow
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_ne_zero_of_ne_zero
- \+/\- *lemma* fpow_zero
- \+/\- *lemma* fpow_add
- \+/\- *lemma* zero_fpow
- \+/\- *lemma* fpow_neg
- \+/\- *lemma* fpow_sub
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* fpow_le_of_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+/\- *lemma* fpow_ge_one_of_nonneg
- \+/\- *lemma* fpow_eq_gpow
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_ne_zero_of_ne_zero
- \+/\- *lemma* fpow_zero
- \+/\- *lemma* fpow_add
- \+/\- *lemma* zero_fpow
- \+/\- *lemma* fpow_neg
- \+/\- *lemma* fpow_sub
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* fpow_le_of_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+/\- *lemma* fpow_ge_one_of_nonneg

modified src/data/padics/padic_integers.lean

modified src/data/padics/padic_norm.lean
- \+/\- *lemma* le_of_dvd
- \+/\- *lemma* le_of_dvd

modified src/data/padics/padic_numbers.lean



## [2019-01-27 22:31:44+01:00](https://github.com/leanprover-community/mathlib/commit/d359aa8)
feat(order/conditionally_complete_lattice): cinfi_const ([#634](https://github.com/leanprover-community/mathlib/pull/634))
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* range_const

modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le
- \+ *theorem* cinfi_const
- \+ *theorem* csupr_const



## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/06eba7f)
update authors on expr.lean (I don't know who's responsible for what)
#### Estimated changes
modified src/meta/expr.lean



## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/be5dba9)
fix(tactic/norm_num): only check core norm_num output up to numeral structure
#### Estimated changes
modified src/meta/expr.lean

modified src/tactic/norm_num.lean



## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/daa7684)
refactor(tactic/basic): move non-tactic decls to meta folder
#### Estimated changes
created src/meta/expr.lean

modified src/meta/rb_map.lean

modified src/tactic/basic.lean



## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/6781ff0)
feat(tactic/linarith): prefer type of goal if there are multiple types
#### Estimated changes
modified src/tactic/linarith.lean

modified tests/linarith.lean



## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/8affebd)
fix(tactic/linarith): remove unused code
#### Estimated changes
modified src/tactic/linarith.lean



## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/92508dc)
fix(tactic/linarith): properly handle problems with inequalities in multiple types
When problems have inequalities over multiple types, it's almost safe to process everything at once, since none of the
variables overlap. But linarith deals with constants by homogenizing them and the "constant" variables do overlap.
This fix creates one call to linarith for each type that appears in a hypothesis.
#### Estimated changes
modified src/tactic/linarith.lean

modified tests/linarith.lean



## [2019-01-27 00:35:53-05:00](https://github.com/leanprover-community/mathlib/commit/84d1c45)
feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton ([#630](https://github.com/leanprover-community/mathlib/pull/630))
* feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton
* feat(tactic/match-stub): add hole for listing relevant constructors
#### Estimated changes
modified src/tactic/basic.lean
- \+ *def* foo
- \+ *def* foo



## [2019-01-25 17:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/315a642)
feat(measure_theory): add Hahn decomposition
#### Estimated changes
modified src/data/real/ennreal.lean
- \+ *lemma* to_nnreal_add

modified src/data/real/nnreal.lean
- \+ *lemma* coe_nonneg

created src/measure_theory/decomposition.lean
- \+ *lemma* hahn_decomposition

modified src/measure_theory/measure_space.lean
- \+ *lemma* tendsto_at_top_supr_nat
- \+ *lemma* tendsto_at_top_infi_nat
- \+ *lemma* measure_eq_inter_diff
- \+ *lemma* tendsto_measure_Union
- \+ *lemma* tendsto_measure_Inter



## [2019-01-24 16:02:42+01:00](https://github.com/leanprover-community/mathlib/commit/ed2ab1a)
feat(measure_theory): measures form a complete lattice
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* empty_diff

modified src/measure_theory/measure_space.lean
- \+ *lemma* Inf_caratheodory
- \+ *lemma* Inf_apply

modified src/measure_theory/outer_measure.lean
- \+ *lemma* Inf_gen_empty
- \+ *lemma* Inf_gen_nonempty1
- \+ *lemma* Inf_gen_nonempty2
- \+ *lemma* Inf_eq_of_function_Inf_gen
- \+ *theorem* top_caratheodory
- \+ *def* Inf_gen



## [2019-01-24 09:18:32+01:00](https://github.com/leanprover-community/mathlib/commit/4aacae3)
feat(data/equiv/algebra): instances for transporting algebra across an equiv ([#618](https://github.com/leanprover-community/mathlib/pull/618))
#### Estimated changes
modified src/data/equiv/algebra.lean
- \+ *lemma* zero_def
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* add_def
- \+ *lemma* inv_def
- \+ *lemma* neg_def



## [2019-01-24 09:17:37+01:00](https://github.com/leanprover-community/mathlib/commit/c49e89d)
feat(category_theory/adjunction): definitions, basic proofs, and examples ([#619](https://github.com/leanprover-community/mathlib/pull/619))
#### Estimated changes
created src/category_theory/adjunction.lean
- \+ *lemma* hom_equiv_naturality_left_symm
- \+ *lemma* hom_equiv_naturality_left
- \+ *lemma* hom_equiv_naturality_right
- \+ *lemma* hom_equiv_naturality_right_symm
- \+ *lemma* left_triangle
- \+ *lemma* right_triangle
- \+ *lemma* left_triangle_components
- \+ *lemma* right_triangle_components
- \+ *lemma* hom_equiv_naturality_left
- \+ *lemma* hom_equiv_naturality_right_symm
- \+ *def* mk_of_hom_equiv
- \+ *def* mk_of_unit_counit
- \+ *def* id
- \+ *def* comp
- \+ *def* left_adjoint_of_equiv
- \+ *def* adjunction_of_equiv_left
- \+ *def* right_adjoint_of_equiv
- \+ *def* adjunction_of_equiv_right
- \+ *def* functoriality_is_left_adjoint
- \+ *def* left_adjoint_preserves_colimits
- \+ *def* functoriality_is_right_adjoint
- \+ *def* right_adjoint_preserves_limits
- \+ *def* cocones_iso
- \+ *def* cones_iso

modified src/category_theory/category.lean
- \+/\- *lemma* concrete_category_id
- \+/\- *lemma* concrete_category_comp
- \+/\- *lemma* bundled_hom_coe
- \+/\- *lemma* concrete_category_id
- \+/\- *lemma* concrete_category_comp
- \+/\- *lemma* bundled_hom_coe

modified src/category_theory/examples/monoids.lean

modified src/category_theory/examples/rings.lean
- \+ *lemma* id_val
- \+ *lemma* comp_val
- \+ *lemma* hom_coe_app
- \+ *lemma* polynomial_obj_α
- \+ *lemma* polynomial_map_val
- \- *lemma* CommRing_hom_coe_app
- \+ *def* Int
- \+ *def* Int.cast
- \+ *def* int.eq_cast'
- \+ *def* Int.hom_unique
- \+ *def* forget
- \+ *def* to_Ring
- \+/\- *def* forget_to_CommMon
- \+/\- *def* forget_to_CommMon

modified src/category_theory/examples/topological_spaces.lean
- \+ *def* discrete
- \+ *def* trivial
- \+ *def* adj₁
- \+ *def* adj₂

modified src/category_theory/fully_faithful.lean

modified src/category_theory/limits/cones.lean
- \+ *lemma* cones_map_app
- \+ *lemma* cocones_map_app
- \+ *lemma* postcompose_obj_X
- \+ *lemma* postcompose_obj_π
- \+ *lemma* postcompose_map_hom
- \+ *lemma* precompose_obj_X
- \+ *lemma* precompose_obj_ι
- \+ *lemma* precompose_map_hom
- \+/\- *def* postcompose
- \+/\- *def* precompose
- \+/\- *def* postcompose
- \+/\- *def* precompose

modified src/category_theory/limits/limits.lean
- \+ *def* is_limit_iso_unique_cone_morphism
- \+ *def* is_colimit_iso_unique_cocone_morphism

modified src/data/equiv/basic.lean
- \+/\- *def* unique_of_equiv
- \+/\- *def* unique_of_equiv



## [2019-01-23 16:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/0e6c358)
feat(set_theory/cardinal): more lemmas on cardinality ([#595](https://github.com/leanprover-community/mathlib/pull/595))
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* image_factorization_eq
- \+ *lemma* surjective_onto_image
- \+ *lemma* range_factorization_eq
- \+ *lemma* surjective_onto_range
- \+ *def* image_factorization
- \+ *def* range_factorization

modified src/set_theory/cardinal.lean
- \+ *theorem* mk_le_of_injective
- \+ *theorem* mk_le_of_surjective
- \+ *theorem* mk_quot_le
- \+ *theorem* mk_quotient_le
- \+ *theorem* mk_subtype_le
- \+/\- *theorem* mk_emptyc
- \+ *theorem* mk_univ
- \+ *theorem* mk_image_le
- \+ *theorem* mk_range_le
- \+/\- *theorem* mk_eq_of_injective
- \+/\- *theorem* mk_emptyc
- \+/\- *theorem* mk_eq_of_injective



## [2019-01-23 14:24:28+01:00](https://github.com/leanprover-community/mathlib/commit/9be8905)
refactor(topology/sequences): restructure proofs
#### Estimated changes
modified src/topology/sequences.lean
- \+/\- *lemma* topological_space.seq_tendsto_iff
- \+ *lemma* subset_sequential_closure
- \+/\- *lemma* is_seq_closed_of_def
- \+/\- *lemma* sequential_closure_subset_closure
- \+/\- *lemma* is_seq_closed_of_is_closed
- \+ *lemma* mem_of_is_seq_closed
- \+ *lemma* mem_of_is_closed_sequential
- \+/\- *lemma* is_seq_closed_iff_is_closed
- \+ *lemma* continuous.to_sequentially_continuous
- \+ *lemma* continuous_iff_sequentially_continuous
- \+/\- *lemma* topological_space.seq_tendsto_iff
- \- *lemma* const_seq_conv
- \- *lemma* subset_seq_closure
- \+/\- *lemma* is_seq_closed_of_def
- \+/\- *lemma* sequential_closure_subset_closure
- \+/\- *lemma* is_seq_closed_of_is_closed
- \- *lemma* is_mem_of_conv_to_of_is_seq_closed
- \- *lemma* is_mem_of_is_closed_of_conv_to
- \+/\- *lemma* is_seq_closed_iff_is_closed
- \- *lemma* cont_to_seq_cont
- \- *lemma* cont_iff_seq_cont
- \- *lemma* metric_space.seq_tendsto_iff
- \+/\- *def* sequential_closure
- \+/\- *def* is_seq_closed
- \+/\- *def* sequentially_continuous
- \+/\- *def* sequential_closure
- \+/\- *def* is_seq_closed
- \+/\- *def* sequentially_continuous



## [2019-01-23 14:24:12+01:00](https://github.com/leanprover-community/mathlib/commit/4018daf)
feat(topology): sequences, sequential spaces, and sequential continuity (closes [#440](https://github.com/leanprover-community/mathlib/pull/440))
Co-Authored-By: Reid Barton <rwbarton@gmail.com>
#### Estimated changes
created src/topology/sequences.lean
- \+ *lemma* topological_space.seq_tendsto_iff
- \+ *lemma* const_seq_conv
- \+ *lemma* subset_seq_closure
- \+ *lemma* is_seq_closed_of_def
- \+ *lemma* sequential_closure_subset_closure
- \+ *lemma* is_seq_closed_of_is_closed
- \+ *lemma* is_mem_of_conv_to_of_is_seq_closed
- \+ *lemma* is_mem_of_is_closed_of_conv_to
- \+ *lemma* is_seq_closed_iff_is_closed
- \+ *lemma* cont_to_seq_cont
- \+ *lemma* cont_iff_seq_cont
- \+ *lemma* metric_space.seq_tendsto_iff
- \+ *def* sequential_closure
- \+ *def* is_seq_closed
- \+ *def* sequentially_continuous



## [2019-01-23 13:24:31+01:00](https://github.com/leanprover-community/mathlib/commit/c06fb67)
refactor(category_theory/category): split off has_hom
This gives a little more flexibility when defining a category,
which will be used for opposite categories. It should also be
useful for defining the free category on a graph.
#### Estimated changes
modified src/category_theory/category.lean

modified src/category_theory/opposites.lean
- \+/\- *lemma* hom_obj
- \+/\- *lemma* hom_obj



## [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/2c95d2a)
maintain(vscode): add ruler at 100 in editor
#### Estimated changes
modified .vscode/settings.json



## [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/b2700dd)
maintain(.vscode): add default settings
#### Estimated changes
created .vscode/settings.json



## [2019-01-23 12:45:23+01:00](https://github.com/leanprover-community/mathlib/commit/6da9b21)
le_induction
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* le_induction



## [2019-01-23 12:38:43+01:00](https://github.com/leanprover-community/mathlib/commit/60efaec)
chore(topology): move contraction_mapping to metric_space/lipschitz
#### Estimated changes
renamed src/contraction_mapping.lean to src/topology/metric_space/lipschitz.lean



## [2019-01-23 11:48:36+01:00](https://github.com/leanprover-community/mathlib/commit/5317b59)
refactor(contraction_mapping): add more proves about Lipschitz continuous functions; cleanup proofs
#### Estimated changes
modified src/algebra/pi_instances.lean
- \- *def* prod_semilattice_sup

modified src/analysis/normed_space/basic.lean
- \- *lemma* squeeze_zero

modified src/contraction_mapping.lean
- \+ *lemma* fixed_point_of_tendsto_iterate
- \+/\- *lemma* dist_inequality_of_contraction
- \+/\- *lemma* dist_bound_of_contraction
- \- *lemma* fixed_point_of_iteration_limit
- \- *lemma* uniform_continuous_of_lipschitz
- \- *lemma* iterated_lipschitz_of_lipschitz
- \+/\- *lemma* dist_inequality_of_contraction
- \+/\- *lemma* dist_bound_of_contraction
- \- *lemma* continuous_prod_snd
- \- *lemma* tendsto_dist_bound_at_top_nhds_0
- \+/\- *theorem* fixed_point_unique_of_contraction
- \+ *theorem* exists_fixed_point_of_contraction
- \+/\- *theorem* fixed_point_unique_of_contraction
- \- *theorem* fixed_point_exists_of_contraction
- \+ *def* lipschitz_with
- \- *def* lipschitz

modified src/order/filter.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* squeeze_zero
- \- *lemma* dist_prod_eq_dist_0
- \+ *theorem* metric.uniformity_eq_comap_nhds_zero

modified src/topology/uniform_space/basic.lean



## [2019-01-23 11:48:20+01:00](https://github.com/leanprover-community/mathlib/commit/96198b9)
feat(contraction_mapping): proof the Banach fixed-point theorem (closes [#553](https://github.com/leanprover-community/mathlib/pull/553))
#### Estimated changes
modified src/algebra/pi_instances.lean
- \+ *def* prod_semilattice_sup

created src/contraction_mapping.lean
- \+ *lemma* fixed_point_of_iteration_limit
- \+ *lemma* uniform_continuous_of_lipschitz
- \+ *lemma* iterated_lipschitz_of_lipschitz
- \+ *lemma* dist_inequality_of_contraction
- \+ *lemma* dist_bound_of_contraction
- \+ *lemma* continuous_prod_snd
- \+ *lemma* tendsto_dist_bound_at_top_nhds_0
- \+ *theorem* fixed_point_unique_of_contraction
- \+ *theorem* fixed_point_exists_of_contraction
- \+ *def* lipschitz

modified src/data/prod.lean
- \+ *lemma* map_def

modified src/order/filter.lean
- \+ *lemma* prod_at_top_at_top_eq
- \+ *lemma* prod_map_at_top_eq

modified src/topology/metric_space/basic.lean
- \+ *lemma* dist_prod_eq_dist_0
- \+ *lemma* cauchy_seq_iff_tendsto_dist_at_top_0

modified src/topology/uniform_space/basic.lean
- \+ *lemma* cauchy_seq_iff_prod_map



## [2019-01-23 11:43:23+01:00](https://github.com/leanprover-community/mathlib/commit/8a0fd0b)
feat(order): add order instances for prod
#### Estimated changes
modified src/order/basic.lean

modified src/order/bounded_lattice.lean

modified src/order/complete_lattice.lean

modified src/order/lattice.lean



## [2019-01-23 08:09:04+01:00](https://github.com/leanprover-community/mathlib/commit/2ae2cf0)
feat(linear_algebra/multivariate_polynomial): C_mul'
#### Estimated changes
modified src/linear_algebra/multivariate_polynomial.lean
- \+ *theorem* C_mul'



## [2019-01-22 17:23:23-05:00](https://github.com/leanprover-community/mathlib/commit/8d44fee)
style(category_theory): adjust precedence of ⥤ ([#616](https://github.com/leanprover-community/mathlib/pull/616))
#### Estimated changes
modified src/category_theory/functor.lean

modified src/category_theory/opposites.lean

modified src/category_theory/products.lean
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* swap
- \+/\- *def* symmetry
- \+/\- *def* evaluation_uncurried
- \+/\- *def* prod
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* swap
- \+/\- *def* symmetry
- \+/\- *def* evaluation_uncurried
- \+/\- *def* prod

modified src/category_theory/types.lean
- \+/\- *def* ulift_functor
- \+/\- *def* ulift_functor

modified src/category_theory/yoneda.lean
- \+/\- *def* yoneda_evaluation
- \+/\- *def* yoneda_pairing
- \+/\- *def* yoneda_evaluation
- \+/\- *def* yoneda_pairing



## [2019-01-22 17:21:55-05:00](https://github.com/leanprover-community/mathlib/commit/c9a0b33)
refactor(category_theory/fully_faithful): move preimage_id ([#615](https://github.com/leanprover-community/mathlib/pull/615))
#### Estimated changes
modified src/category_theory/fully_faithful.lean
- \+ *lemma* preimage_id

modified src/category_theory/opposites.lean
- \- *lemma* preimage_id



## [2019-01-22 16:49:24+01:00](https://github.com/leanprover-community/mathlib/commit/edfa206)
feat(linear_algebra/dimension): more dimension theorems; rank of a linear map
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* image_preimage_eq_of_subset

modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis_injective
- \+ *lemma* is_basis_span
- \+ *lemma* is_basis_empty
- \+ *lemma* is_basis_empty_bot

modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_bot
- \+ *lemma* dim_span
- \+ *lemma* dim_range_le
- \+ *lemma* dim_map_le
- \+ *lemma* dim_range_of_surjective
- \+ *lemma* dim_eq_surjective
- \+ *lemma* dim_le_surjective
- \+ *lemma* dim_eq_injective
- \+ *lemma* dim_submodule_le
- \+ *lemma* dim_le_injective
- \+ *lemma* dim_le_of_submodule
- \+ *lemma* dim_add_le_dim_add_dim
- \+ *lemma* rank_le_domain
- \+ *lemma* rank_le_range
- \+ *lemma* rank_add_le
- \+ *lemma* rank_comp_le1
- \+ *lemma* rank_comp_le2
- \+ *def* rank

modified src/set_theory/cardinal.lean
- \+ *lemma* mk_le_mk_of_subset



## [2019-01-22 16:02:10+01:00](https://github.com/leanprover-community/mathlib/commit/6e4c9ba)
feat(linear_algebra/linear_combination): lc lifts vector spaces
#### Estimated changes
modified src/linear_algebra/linear_combination.lean



## [2019-01-22 16:00:18+01:00](https://github.com/leanprover-community/mathlib/commit/d5a302f)
chore(linear_algebra): rename file lc to linear_combination
#### Estimated changes
modified src/linear_algebra/basis.lean

renamed src/linear_algebra/lc.lean to src/linear_algebra/linear_combination.lean

modified src/ring_theory/noetherian.lean



## [2019-01-22 15:32:49+01:00](https://github.com/leanprover-community/mathlib/commit/7baf093)
feat(data/list,data/multiset,data/finset): add Ico intervals (closes [#496](https://github.com/leanprover-community/mathlib/pull/496))
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* union_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_ge_of_le_bot
- \+ *lemma* filter_ge_of_top_le
- \+ *lemma* filter_ge_of_ge
- \+ *lemma* filter_ge
- \+ *lemma* diff_left
- \+ *lemma* diff_right
- \+ *theorem* val
- \+ *theorem* to_finset
- \+ *theorem* map_add
- \+ *theorem* zero_bot
- \+ *theorem* card
- \+ *theorem* mem
- \+ *theorem* eq_empty_of_le
- \+ *theorem* self_eq_empty
- \+ *theorem* eq_empty_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* eq_cons
- \+ *theorem* pred_singleton
- \+ *theorem* not_mem_top
- \+ *def* Ico

modified src/data/list/basic.lean
- \+ *lemma* append_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_ge_of_le_bot
- \+ *lemma* filter_ge_of_top_le
- \+ *lemma* filter_ge_of_ge
- \+ *lemma* filter_ge
- \+/\- *theorem* range'_append
- \+ *theorem* map_add
- \+ *theorem* zero_bot
- \+ *theorem* length
- \+ *theorem* pairwise_lt
- \+ *theorem* nodup
- \+ *theorem* mem
- \+ *theorem* eq_nil_of_le
- \+ *theorem* self_empty
- \+ *theorem* eq_empty_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* eq_cons
- \+ *theorem* pred_singleton
- \+ *theorem* chain'_succ
- \+ *theorem* not_mem_top
- \+/\- *theorem* range'_append
- \+ *def* Ico

modified src/data/multiset.lean
- \+ *lemma* add_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_ge_of_le_bot
- \+ *lemma* filter_ge_of_top_le
- \+ *lemma* filter_ge_of_ge
- \+ *lemma* filter_ge
- \+ *theorem* coe_eq_zero
- \+ *theorem* map_add
- \+ *theorem* zero_bot
- \+ *theorem* card
- \+ *theorem* nodup
- \+ *theorem* mem
- \+ *theorem* eq_zero_of_le
- \+ *theorem* self_eq_zero
- \+ *theorem* eq_zero_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* eq_cons
- \+ *theorem* pred_singleton
- \+ *theorem* not_mem_top
- \+ *def* Ico



## [2019-01-21 20:02:01-05:00](https://github.com/leanprover-community/mathlib/commit/3dc9935)
fix(tactic/instance_stub): extend the applicability of instance_stub ([#612](https://github.com/leanprover-community/mathlib/pull/612))
#### Estimated changes
modified src/tactic/basic.lean



## [2019-01-21 11:12:50+01:00](https://github.com/leanprover-community/mathlib/commit/bc163a6)
fix(.travis.yml): produce mathlib.txt only from src/
#### Estimated changes
modified .travis.yml



## [2019-01-20 22:50:48-05:00](https://github.com/leanprover-community/mathlib/commit/c1e594b)
feat(meta, logic, tactic): lean 3.4.2: migrate coinductive_predicates, transfer, relator ([#610](https://github.com/leanprover-community/mathlib/pull/610))
#### Estimated changes
modified leanpkg.toml

modified src/data/list/defs.lean

modified src/logic/relator.lean
- \+ *lemma* rel_forall_of_right_total
- \+ *lemma* rel_exists_of_left_total
- \+ *lemma* rel_forall_of_total
- \+ *lemma* rel_exists_of_total
- \+ *lemma* left_unique_of_rel_eq
- \+ *lemma* rel_imp
- \+ *lemma* rel_not
- \+ *def* lift_fun
- \+ *def* right_total
- \+ *def* left_total
- \+ *def* bi_total
- \+ *def* left_unique
- \+ *def* right_unique

created src/meta/coinductive_predicates.lean
- \+ *lemma* monotonicity.pi
- \+ *lemma* monotonicity.imp
- \+ *lemma* monotonicity.const
- \+ *lemma* monotonicity.true
- \+ *lemma* monotonicity.false
- \+ *lemma* monotonicity.exists
- \+ *lemma* monotonicity.and
- \+ *lemma* monotonicity.or
- \+ *lemma* monotonicity.not
- \+ *def* last_string

modified src/tactic/alias.lean

modified src/tactic/explode.lean

modified src/tactic/mk_iff_of_inductive_prop.lean

created src/tactic/transfer.lean

created tests/coinductive.lean
- \+ *lemma* monotonicity.all_list



## [2019-01-20 20:42:15-05:00](https://github.com/leanprover-community/mathlib/commit/2c5bc21)
feat(topology/emetric_space): basic facts for emetric spaces ([#608](https://github.com/leanprover-community/mathlib/pull/608))
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \- *lemma* second_countable_of_separable_metric_space
- \- *lemma* countable_closure_of_compact

modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_triangle4
- \+ *lemma* countable_closure_of_compact
- \+ *lemma* second_countable_of_separable
- \- *lemma* cauchy_iff
- \+ *theorem* mem_ball
- \+ *theorem* mem_ball'
- \+ *theorem* mem_closed_ball
- \+ *theorem* ball_subset_closed_ball
- \+ *theorem* pos_of_mem_ball
- \+ *theorem* mem_ball_self
- \+ *theorem* mem_ball_comm
- \+ *theorem* ball_subset_ball
- \+ *theorem* closed_ball_subset_closed_ball
- \+ *theorem* ball_disjoint
- \+ *theorem* ball_subset
- \+ *theorem* exists_ball_subset_ball
- \+ *theorem* nhds_eq
- \+ *theorem* mem_nhds_iff
- \+ *theorem* is_open_iff
- \+ *theorem* is_open_ball
- \+ *theorem* ball_mem_nhds
- \+ *theorem* mem_closure_iff'
- \+ *theorem* tendsto_nhds
- \+ *theorem* tendsto_at_top
- \+ *theorem* cauchy_seq_iff
- \+ *theorem* cauchy_seq_iff'
- \+ *theorem* totally_bounded_iff
- \+ *theorem* totally_bounded_iff'
- \+ *def* ball
- \+ *def* closed_ball



## [2019-01-19 18:43:24-05:00](https://github.com/leanprover-community/mathlib/commit/fa2e399)
feat(topology/bounded_continuous_function): constructor in normed groups ([#607](https://github.com/leanprover-community/mathlib/pull/607))
#### Estimated changes
modified src/topology/bounded_continuous_function.lean
- \+ *def* of_normed_group
- \+ *def* of_normed_group_discrete



## [2019-01-18 19:50:09-05:00](https://github.com/leanprover-community/mathlib/commit/3fcba7d)
feat(logic/basic): add class 'unique' for uniquely inhabited types ([#605](https://github.com/leanprover-community/mathlib/pull/605))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* unique_of_equiv
- \+ *def* unique_congr
- \+ *def* unique_unique_equiv
- \+ *def* equiv_of_unique_of_unique
- \+ *def* equiv_punit_of_unique

created src/logic/unique.lean
- \+ *lemma* eq_default
- \+ *lemma* default_eq
- \+ *def* of_surjective



## [2019-01-18 16:30:23-05:00](https://github.com/leanprover-community/mathlib/commit/41b3fdd)
feat(topology/real): bounded iff bounded below above ([#606](https://github.com/leanprover-community/mathlib/pull/606))
#### Estimated changes
modified src/topology/instances/real.lean
- \+ *lemma* real.bounded_iff_bdd_below_bdd_above



## [2019-01-18 15:36:40+01:00](https://github.com/leanprover-community/mathlib/commit/eb1253f)
feat(measure_theory): add Giry monad
#### Estimated changes
created src/measure_theory/giry_monad.lean
- \+ *lemma* measurable_coe
- \+ *lemma* measurable_of_measurable_coe
- \+ *lemma* measurable_map
- \+ *lemma* measurable_dirac
- \+ *lemma* measurable_integral
- \+ *lemma* join_apply
- \+ *lemma* measurable_join
- \+ *lemma* integral_join
- \+ *lemma* bind_apply
- \+ *lemma* measurable_bind'
- \+ *lemma* integral_bind
- \+ *lemma* bind_bind
- \+ *lemma* bind_dirac
- \+ *lemma* dirac_bind
- \+ *def* join
- \+ *def* bind

modified src/measure_theory/integration.lean
- \+ *lemma* monotone_sequence_of_directed
- \+ *lemma* le_sequence_of_directed
- \+ *lemma* approx_comp
- \+ *lemma* eapprox_comp
- \+ *lemma* integral_map
- \+ *lemma* lintegral_finset_sum
- \+ *lemma* lintegral_tsum
- \+ *lemma* integral_zero
- \+ *lemma* integral_map
- \+ *lemma* integral_dirac
- \+ *lemma* with_density_apply
- \- *lemma* supr_eq_of_tendsto
- \+ *theorem* lintegral_supr_directed
- \+ *def* with_density
- \- *def* measure.with_density

modified src/measure_theory/measure_space.lean
- \+ *lemma* of_measurable_apply

modified src/order/basic.lean
- \+ *lemma* monotone_of_monotone_nat

modified src/topology/algebra/topological_structures.lean
- \+ *lemma* supr_eq_of_tendsto



## [2019-01-18 14:10:04+01:00](https://github.com/leanprover-community/mathlib/commit/739d28a)
refactor(ring_theory/multiplicity): replace padic_val with multiplicity ([#495](https://github.com/leanprover-community/mathlib/pull/495))
#### Estimated changes
modified src/data/padics/padic_norm.lean
- \+ *lemma* padic_val_rat_def
- \+/\- *lemma* padic_val_rat_self
- \+/\- *lemma* padic_val_rat_of_int
- \+ *lemma* finite_int_prime_iff
- \+ *lemma* padic_val_rat_le_padic_val_rat_iff
- \- *lemma* spec
- \- *lemma* is_greatest
- \- *lemma* unique
- \- *lemma* le_padic_val_of_pow_dvd
- \- *lemma* pow_dvd_of_le_padic_val
- \- *lemma* pow_dvd_iff_le_padic_val
- \- *lemma* padic_val_self
- \- *lemma* padic_val_eq_zero_of_not_dvd
- \- *lemma* padic_val_eq_zero_of_not_dvd'
- \- *lemma* min_le_padic_val_add
- \- *lemma* dvd_of_padic_val_pos
- \- *lemma* padic_val_eq_zero_of_coprime
- \+/\- *lemma* padic_val_rat_self
- \+/\- *lemma* padic_val_rat_of_int
- \+ *theorem* le_padic_val_rat_add_of_le
- \+/\- *theorem* min_le_padic_val_rat_add
- \+/\- *theorem* min_le_padic_val_rat_add
- \- *def* padic_val

modified src/data/padics/padic_numbers.lean

modified src/data/real/irrational.lean
- \+ *theorem* irr_nrt_of_n_not_dvd_multiplicity
- \+ *theorem* irr_sqrt_of_multiplicity_odd
- \- *theorem* irr_nrt_of_n_not_dvd_padic_val
- \- *theorem* irr_sqrt_of_padic_val_odd



## [2019-01-18 13:28:37+01:00](https://github.com/leanprover-community/mathlib/commit/6144710)
feat(measure_theory): add equivalence of measurable spaces
#### Estimated changes
modified src/data/equiv/basic.lean

modified src/data/set/basic.lean
- \+ *lemma* range_coe_subtype
- \+ *lemma* prod_eq

modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_of_continuous
- \+ *lemma* borel_induced
- \+ *lemma* borel_eq_subtype
- \+ *lemma* measurable_finset_sum
- \+ *lemma* measurable_coe
- \+ *lemma* measurable_of_measurable_nnreal
- \+ *lemma* measurable_of_measurable_nnreal_nnreal
- \+ *lemma* measurable_mul
- \+/\- *lemma* measurable_of_continuous
- \+/\- *def* borel
- \+ *def* homemorph.to_measurable_equiv
- \+ *def* ennreal_equiv_nnreal
- \+ *def* ennreal_equiv_sum
- \+/\- *def* borel

modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* comap_generate_from
- \+ *lemma* measurable_unit
- \+ *lemma* is_measurable_subtype_image
- \+ *lemma* measurable_of_measurable_union_cover
- \+ *lemma* measurable_inl
- \+ *lemma* measurable_inr
- \+ *lemma* measurable_sum
- \+ *lemma* measurable_sum_rec
- \+ *lemma* is_measurable_inl_image
- \+ *lemma* is_measurable_range_inl
- \+ *lemma* is_measurable_inr_image
- \+ *lemma* is_measurable_range_inr
- \+ *lemma* coe_eq
- \+ *lemma* trans_to_equiv
- \+ *lemma* symm_to_equiv
- \+/\- *lemma* comap_generate_from
- \+ *def* refl
- \+ *def* trans
- \+ *def* symm
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* sum_congr
- \+ *def* set.prod
- \+ *def* set.univ
- \+ *def* set.singleton
- \+ *def* set.range_inl
- \+ *def* set.range_inr
- \+ *def* sum_prod_distrib
- \+ *def* prod_sum_distrib
- \+ *def* sum_prod_sum



## [2019-01-18 13:26:32+01:00](https://github.com/leanprover-community/mathlib/commit/b352d2c)
refactor(topology): topological_space.induced resembles set.image; second_countable_topology on subtypes; simplify filter.map_comap
#### Estimated changes
modified src/order/filter.lean
- \+ *lemma* map_comap
- \+ *lemma* tendsto_comap'_iff
- \- *lemma* le_map_comap'
- \- *lemma* le_map_comap
- \- *lemma* tendsto_comap''

modified src/topology/basic.lean
- \+ *lemma* induced_generate_from_eq
- \+ *lemma* second_countable_topology_induced

modified src/topology/continuity.lean
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* embedding.map_nhds_eq
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* embedding.map_nhds_eq
- \+ *theorem* is_open_induced_eq

modified src/topology/instances/ennreal.lean
- \+ *lemma* coe_range_mem_nhds
- \- *lemma* coe_image_univ_mem_nhds

modified src/topology/instances/nnreal.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/completion.lean



## [2019-01-18 13:20:03+01:00](https://github.com/leanprover-community/mathlib/commit/6b6b04a)
feat(order/complete_lattice): add rules for supr/infi under image and under propositions
#### Estimated changes
modified src/order/complete_lattice.lean
- \+ *lemma* supr_eq_dif
- \+ *lemma* supr_eq_if
- \+ *lemma* infi_eq_dif
- \+ *lemma* infi_eq_if
- \+ *lemma* infi_image
- \+ *lemma* supr_image



## [2019-01-18 11:13:09+01:00](https://github.com/leanprover-community/mathlib/commit/f0f06ca)
refactor(*): analysis reorganization ([#598](https://github.com/leanprover-community/mathlib/pull/598))
* split `measure_theory` and `topology` out of analysis
* add `instances` sub directories for theories around type class instances
#### Estimated changes
modified docs/theories/topological_spaces.md

modified src/analysis/exponential.lean

renamed src/analysis/normed_space.lean to src/analysis/normed_space/basic.lean

renamed src/analysis/bounded_linear_maps.lean to src/analysis/normed_space/bounded_linear_maps.lean

renamed src/analysis/limits.lean to src/analysis/specific_limits.lean

modified src/category_theory/examples/measurable_space.lean

modified src/category_theory/examples/topological_spaces.lean

modified src/data/analysis/topology.lean

modified src/data/padics/hensel.lean

modified src/data/padics/padic_numbers.lean

modified src/data/real/cau_seq_filter.lean

renamed src/analysis/measure_theory/borel_space.lean to src/measure_theory/borel_space.lean

renamed src/analysis/measure_theory/integration.lean to src/measure_theory/integration.lean

renamed src/analysis/measure_theory/lebesgue_measure.lean to src/measure_theory/lebesgue_measure.lean

renamed src/analysis/measure_theory/measurable_space.lean to src/measure_theory/measurable_space.lean

renamed src/analysis/measure_theory/measure_space.lean to src/measure_theory/measure_space.lean

renamed src/analysis/measure_theory/outer_measure.lean to src/measure_theory/outer_measure.lean

renamed src/analysis/probability_mass_function.lean to src/measure_theory/probability_mass_function.lean

renamed src/analysis/topology/topological_groups.lean to src/topology/algebra/group.lean

renamed src/analysis/topology/infinite_sum.lean to src/topology/algebra/infinite_sum.lean

renamed src/analysis/topology/quotient_topological_structures.lean to src/topology/algebra/quotient.lean

renamed src/analysis/topology/topological_structures.lean to src/topology/algebra/topological_structures.lean

renamed src/analysis/topology/topological_space.lean to src/topology/basic.lean

renamed src/analysis/topology/bounded_continuous_function.lean to src/topology/bounded_continuous_function.lean

renamed src/analysis/topology/continuous_map.lean to src/topology/compact_open.lean

renamed src/analysis/topology/continuity.lean to src/topology/continuity.lean

renamed src/analysis/complex.lean to src/topology/instances/complex.lean

renamed src/analysis/ennreal.lean to src/topology/instances/ennreal.lean

renamed src/analysis/nnreal.lean to src/topology/instances/nnreal.lean

renamed src/analysis/polynomial.lean to src/topology/instances/polynomial.lean

renamed src/analysis/real.lean to src/topology/instances/real.lean

renamed src/analysis/metric_space.lean to src/topology/metric_space/basic.lean

renamed src/analysis/emetric_space.lean to src/topology/metric_space/emetric_space.lean

renamed src/analysis/topology/stone_cech.lean to src/topology/stone_cech.lean

renamed src/analysis/topology/uniform_space.lean to src/topology/uniform_space/basic.lean

renamed src/analysis/topology/completion.lean to src/topology/uniform_space/completion.lean



## [2019-01-17 19:21:33-05:00](https://github.com/leanprover-community/mathlib/commit/c1f162c)
fix(tactic/linarith): don't reject expressions with division by variables ([#604](https://github.com/leanprover-community/mathlib/pull/604))
norm_hyp_aux should have succeeded (without changing the type of h') in the case where lhs contains 1/x. But mk_single_comp_zero_pf is too clever when given the coeff 1. norm_hyp_aux will still do unnecessary work when it finds e.g. 1/(2*x), but shouldn't fail.
#### Estimated changes
modified src/tactic/linarith.lean

modified tests/linarith.lean



## [2019-01-17 14:37:38-05:00](https://github.com/leanprover-community/mathlib/commit/ae610a0)
feat(ring_theory/adjoin_root): adjoin roots to polynomials ([#603](https://github.com/leanprover-community/mathlib/pull/603))
#### Estimated changes
created src/ring_theory/adjoin_root.lean
- \+ *lemma* mk_self
- \+ *lemma* eval₂_root
- \+ *lemma* is_root_root
- \+ *lemma* lift_mk
- \+ *lemma* lift_root
- \+ *lemma* lift_of
- \+ *lemma* coe_injective
- \+ *lemma* mul_div_root_cancel
- \+ *def* adjoin_root
- \+ *def* mk
- \+ *def* root
- \+ *def* of
- \+ *def* lift



## [2019-01-16 08:50:38-05:00](https://github.com/leanprover-community/mathlib/commit/5c37507)
doc(elan.md): fix msys2 setup ([#594](https://github.com/leanprover-community/mathlib/pull/594)) [ci-skip]
For me, adding the suggested line to .profile did not change my path, even after restarting the terminal.
Moreover, elan is installed in $USERPROFILE/.elan/bin, not in $HOME/.elan/bin.
Adding $USERPROFILE/.elan/bin to the path did not work for me, so I give the full path.
#### Estimated changes
modified docs/elan.md



## [2019-01-16 08:33:19-05:00](https://github.com/leanprover-community/mathlib/commit/5dd9998)
doc(docs/tactics): document `convert` ([#601](https://github.com/leanprover-community/mathlib/pull/601)) [ci-skip]
#### Estimated changes
modified docs/tactics.md



## [2019-01-16 08:14:44-05:00](https://github.com/leanprover-community/mathlib/commit/ab5849e)
style(category_theory/opposites): increase binding power of ᵒᵖ ([#600](https://github.com/leanprover-community/mathlib/pull/600))
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+/\- *def* cones
- \+/\- *def* cones

modified src/category_theory/opposites.lean

modified src/category_theory/yoneda.lean



## [2019-01-15 17:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/024da40)
refactor(logic/schroeder_bernstein): move to set_theory/ ([#599](https://github.com/leanprover-community/mathlib/pull/599))
#### Estimated changes
modified src/set_theory/cardinal.lean

renamed src/logic/schroeder_bernstein.lean to src/set_theory/schroeder_bernstein.lean



## [2019-01-15 12:05:23-05:00](https://github.com/leanprover-community/mathlib/commit/d4f80f6)
refactor(*): Try again moving everything to src ([#597](https://github.com/leanprover-community/mathlib/pull/597))
#### Estimated changes
renamed category_theory/limits/over.lean to src/category_theory/limits/over.lean

renamed group_theory/sylow.lean to src/group_theory/sylow.lean

renamed ring_theory/euclidean_domain.lean to src/ring_theory/euclidean_domain.lean



## [2019-01-15 10:51:04-05:00](https://github.com/leanprover-community/mathlib/commit/78f1949)
refactor(*): move everything into `src` ([#583](https://github.com/leanprover-community/mathlib/pull/583))
#### Estimated changes
modified leanpkg.toml

renamed algebra/archimedean.lean to src/algebra/archimedean.lean

renamed algebra/big_operators.lean to src/algebra/big_operators.lean

renamed algebra/char_p.lean to src/algebra/char_p.lean

renamed algebra/char_zero.lean to src/algebra/char_zero.lean

renamed algebra/default.lean to src/algebra/default.lean

renamed algebra/euclidean_domain.lean to src/algebra/euclidean_domain.lean

renamed algebra/field.lean to src/algebra/field.lean

renamed algebra/field_power.lean to src/algebra/field_power.lean

renamed algebra/gcd_domain.lean to src/algebra/gcd_domain.lean

renamed algebra/group.lean to src/algebra/group.lean

renamed algebra/group_power.lean to src/algebra/group_power.lean

renamed algebra/module.lean to src/algebra/module.lean

renamed algebra/order.lean to src/algebra/order.lean

renamed algebra/order_functions.lean to src/algebra/order_functions.lean

renamed algebra/ordered_field.lean to src/algebra/ordered_field.lean

renamed algebra/ordered_group.lean to src/algebra/ordered_group.lean

renamed algebra/ordered_ring.lean to src/algebra/ordered_ring.lean

renamed algebra/pi_instances.lean to src/algebra/pi_instances.lean

renamed algebra/ring.lean to src/algebra/ring.lean

renamed analysis/bounded_linear_maps.lean to src/analysis/bounded_linear_maps.lean

renamed analysis/complex.lean to src/analysis/complex.lean

renamed analysis/emetric_space.lean to src/analysis/emetric_space.lean

renamed analysis/ennreal.lean to src/analysis/ennreal.lean

renamed analysis/exponential.lean to src/analysis/exponential.lean

renamed analysis/limits.lean to src/analysis/limits.lean

renamed analysis/measure_theory/borel_space.lean to src/analysis/measure_theory/borel_space.lean

renamed analysis/measure_theory/integration.lean to src/analysis/measure_theory/integration.lean

renamed analysis/measure_theory/lebesgue_measure.lean to src/analysis/measure_theory/lebesgue_measure.lean

renamed analysis/measure_theory/measurable_space.lean to src/analysis/measure_theory/measurable_space.lean

renamed analysis/measure_theory/measure_space.lean to src/analysis/measure_theory/measure_space.lean

renamed analysis/measure_theory/outer_measure.lean to src/analysis/measure_theory/outer_measure.lean

renamed analysis/metric_space.lean to src/analysis/metric_space.lean

renamed analysis/nnreal.lean to src/analysis/nnreal.lean

renamed analysis/normed_space.lean to src/analysis/normed_space.lean

renamed analysis/polynomial.lean to src/analysis/polynomial.lean

renamed analysis/probability_mass_function.lean to src/analysis/probability_mass_function.lean

renamed analysis/real.lean to src/analysis/real.lean

renamed analysis/topology/bounded_continuous_function.lean to src/analysis/topology/bounded_continuous_function.lean

renamed analysis/topology/completion.lean to src/analysis/topology/completion.lean

renamed analysis/topology/continuity.lean to src/analysis/topology/continuity.lean

renamed analysis/topology/continuous_map.lean to src/analysis/topology/continuous_map.lean

renamed analysis/topology/infinite_sum.lean to src/analysis/topology/infinite_sum.lean

renamed analysis/topology/quotient_topological_structures.lean to src/analysis/topology/quotient_topological_structures.lean

renamed analysis/topology/stone_cech.lean to src/analysis/topology/stone_cech.lean

renamed analysis/topology/topological_groups.lean to src/analysis/topology/topological_groups.lean

renamed analysis/topology/topological_space.lean to src/analysis/topology/topological_space.lean

renamed analysis/topology/topological_structures.lean to src/analysis/topology/topological_structures.lean

renamed analysis/topology/uniform_space.lean to src/analysis/topology/uniform_space.lean

renamed category/applicative.lean to src/category/applicative.lean

renamed category/basic.lean to src/category/basic.lean

renamed category/bifunctor.lean to src/category/bifunctor.lean

renamed category/bitraversable/basic.lean to src/category/bitraversable/basic.lean

renamed category/bitraversable/instances.lean to src/category/bitraversable/instances.lean

renamed category/bitraversable/lemmas.lean to src/category/bitraversable/lemmas.lean

renamed category/functor.lean to src/category/functor.lean

renamed category/traversable/basic.lean to src/category/traversable/basic.lean

renamed category/traversable/default.lean to src/category/traversable/default.lean

renamed category/traversable/derive.lean to src/category/traversable/derive.lean

renamed category/traversable/equiv.lean to src/category/traversable/equiv.lean

renamed category/traversable/instances.lean to src/category/traversable/instances.lean

renamed category/traversable/lemmas.lean to src/category/traversable/lemmas.lean

renamed category_theory/category.lean to src/category_theory/category.lean

renamed category_theory/comma.lean to src/category_theory/comma.lean

renamed category_theory/const.lean to src/category_theory/const.lean

renamed category_theory/discrete_category.lean to src/category_theory/discrete_category.lean

renamed category_theory/eq_to_hom.lean to src/category_theory/eq_to_hom.lean

renamed category_theory/equivalence.lean to src/category_theory/equivalence.lean

renamed category_theory/examples/measurable_space.lean to src/category_theory/examples/measurable_space.lean

renamed category_theory/examples/monoids.lean to src/category_theory/examples/monoids.lean

renamed category_theory/examples/rings.lean to src/category_theory/examples/rings.lean

renamed category_theory/examples/topological_spaces.lean to src/category_theory/examples/topological_spaces.lean

renamed category_theory/full_subcategory.lean to src/category_theory/full_subcategory.lean

renamed category_theory/fully_faithful.lean to src/category_theory/fully_faithful.lean

renamed category_theory/functor.lean to src/category_theory/functor.lean

renamed category_theory/functor_category.lean to src/category_theory/functor_category.lean

renamed category_theory/groupoid.lean to src/category_theory/groupoid.lean

renamed category_theory/isomorphism.lean to src/category_theory/isomorphism.lean

renamed category_theory/limits/cones.lean to src/category_theory/limits/cones.lean

renamed category_theory/limits/functor_category.lean to src/category_theory/limits/functor_category.lean

renamed category_theory/limits/limits.lean to src/category_theory/limits/limits.lean

renamed category_theory/limits/preserves.lean to src/category_theory/limits/preserves.lean

renamed category_theory/limits/types.lean to src/category_theory/limits/types.lean

renamed category_theory/natural_isomorphism.lean to src/category_theory/natural_isomorphism.lean

renamed category_theory/natural_transformation.lean to src/category_theory/natural_transformation.lean

renamed category_theory/opposites.lean to src/category_theory/opposites.lean

renamed category_theory/pempty.lean to src/category_theory/pempty.lean

renamed category_theory/products.lean to src/category_theory/products.lean

renamed category_theory/punit.lean to src/category_theory/punit.lean

renamed category_theory/types.lean to src/category_theory/types.lean

renamed category_theory/whiskering.lean to src/category_theory/whiskering.lean

renamed category_theory/yoneda.lean to src/category_theory/yoneda.lean

renamed computability/halting.lean to src/computability/halting.lean

renamed computability/partrec.lean to src/computability/partrec.lean

renamed computability/partrec_code.lean to src/computability/partrec_code.lean

renamed computability/primrec.lean to src/computability/primrec.lean

renamed computability/turing_machine.lean to src/computability/turing_machine.lean

renamed data/analysis/filter.lean to src/data/analysis/filter.lean

renamed data/analysis/topology.lean to src/data/analysis/topology.lean

renamed data/array/lemmas.lean to src/data/array/lemmas.lean

renamed data/bool.lean to src/data/bool.lean

renamed data/buffer/basic.lean to src/data/buffer/basic.lean

renamed data/char.lean to src/data/char.lean

renamed data/complex/basic.lean to src/data/complex/basic.lean

renamed data/complex/exponential.lean to src/data/complex/exponential.lean

renamed data/dfinsupp.lean to src/data/dfinsupp.lean

renamed data/dlist/basic.lean to src/data/dlist/basic.lean

renamed data/dlist/instances.lean to src/data/dlist/instances.lean

renamed data/equiv/algebra.lean to src/data/equiv/algebra.lean

renamed data/equiv/basic.lean to src/data/equiv/basic.lean

renamed data/equiv/denumerable.lean to src/data/equiv/denumerable.lean

renamed data/equiv/encodable.lean to src/data/equiv/encodable.lean

renamed data/equiv/fin.lean to src/data/equiv/fin.lean

renamed data/equiv/list.lean to src/data/equiv/list.lean

renamed data/equiv/nat.lean to src/data/equiv/nat.lean

renamed data/erased.lean to src/data/erased.lean

renamed data/fin.lean to src/data/fin.lean

renamed data/finmap.lean to src/data/finmap.lean

renamed data/finset.lean to src/data/finset.lean

renamed data/finsupp.lean to src/data/finsupp.lean

renamed data/fintype.lean to src/data/fintype.lean

renamed data/fp/basic.lean to src/data/fp/basic.lean

renamed data/hash_map.lean to src/data/hash_map.lean

renamed data/holor.lean to src/data/holor.lean

renamed data/int/basic.lean to src/data/int/basic.lean

renamed data/int/gcd.lean to src/data/int/gcd.lean

renamed data/int/modeq.lean to src/data/int/modeq.lean

renamed data/int/sqrt.lean to src/data/int/sqrt.lean

renamed data/lazy_list2.lean to src/data/lazy_list2.lean

renamed data/list/alist.lean to src/data/list/alist.lean

renamed data/list/basic.lean to src/data/list/basic.lean

renamed data/list/default.lean to src/data/list/default.lean

renamed data/list/defs.lean to src/data/list/defs.lean

renamed data/list/perm.lean to src/data/list/perm.lean

renamed data/list/sigma.lean to src/data/list/sigma.lean

renamed data/list/sort.lean to src/data/list/sort.lean

renamed data/multiset.lean to src/data/multiset.lean

renamed data/nat/basic.lean to src/data/nat/basic.lean

renamed data/nat/cast.lean to src/data/nat/cast.lean

renamed data/nat/choose.lean to src/data/nat/choose.lean

renamed data/nat/dist.lean to src/data/nat/dist.lean

renamed data/nat/enat.lean to src/data/nat/enat.lean

renamed data/nat/gcd.lean to src/data/nat/gcd.lean

renamed data/nat/modeq.lean to src/data/nat/modeq.lean

renamed data/nat/pairing.lean to src/data/nat/pairing.lean

renamed data/nat/prime.lean to src/data/nat/prime.lean

renamed data/nat/sqrt.lean to src/data/nat/sqrt.lean

renamed data/nat/totient.lean to src/data/nat/totient.lean

renamed data/num/basic.lean to src/data/num/basic.lean

renamed data/num/bitwise.lean to src/data/num/bitwise.lean

renamed data/num/lemmas.lean to src/data/num/lemmas.lean

renamed data/option/basic.lean to src/data/option/basic.lean

renamed data/option/defs.lean to src/data/option/defs.lean

renamed data/padics/default.lean to src/data/padics/default.lean

renamed data/padics/hensel.lean to src/data/padics/hensel.lean

renamed data/padics/padic_integers.lean to src/data/padics/padic_integers.lean

renamed data/padics/padic_norm.lean to src/data/padics/padic_norm.lean

renamed data/padics/padic_numbers.lean to src/data/padics/padic_numbers.lean

renamed data/pfun.lean to src/data/pfun.lean

renamed data/pnat.lean to src/data/pnat.lean

renamed data/polynomial.lean to src/data/polynomial.lean

renamed data/prod.lean to src/data/prod.lean

renamed data/quot.lean to src/data/quot.lean

renamed data/rat.lean to src/data/rat.lean

renamed data/real/basic.lean to src/data/real/basic.lean

renamed data/real/cau_seq.lean to src/data/real/cau_seq.lean

renamed data/real/cau_seq_completion.lean to src/data/real/cau_seq_completion.lean

renamed data/real/cau_seq_filter.lean to src/data/real/cau_seq_filter.lean

renamed data/real/ennreal.lean to src/data/real/ennreal.lean

renamed data/real/irrational.lean to src/data/real/irrational.lean

renamed data/real/nnreal.lean to src/data/real/nnreal.lean

renamed data/semiquot.lean to src/data/semiquot.lean

renamed data/seq/computation.lean to src/data/seq/computation.lean

renamed data/seq/parallel.lean to src/data/seq/parallel.lean

renamed data/seq/seq.lean to src/data/seq/seq.lean

renamed data/seq/wseq.lean to src/data/seq/wseq.lean

renamed data/set/basic.lean to src/data/set/basic.lean

renamed data/set/countable.lean to src/data/set/countable.lean

renamed data/set/default.lean to src/data/set/default.lean

renamed data/set/disjointed.lean to src/data/set/disjointed.lean

renamed data/set/enumerate.lean to src/data/set/enumerate.lean

renamed data/set/finite.lean to src/data/set/finite.lean

renamed data/set/function.lean to src/data/set/function.lean

renamed data/set/intervals.lean to src/data/set/intervals.lean

renamed data/set/lattice.lean to src/data/set/lattice.lean

renamed data/sigma/basic.lean to src/data/sigma/basic.lean

renamed data/sigma/default.lean to src/data/sigma/default.lean

renamed data/stream/basic.lean to src/data/stream/basic.lean

renamed data/string.lean to src/data/string.lean

renamed data/subtype.lean to src/data/subtype.lean

renamed data/sum.lean to src/data/sum.lean

renamed data/ulift.lean to src/data/ulift.lean

renamed data/vector2.lean to src/data/vector2.lean

renamed data/zmod/basic.lean to src/data/zmod/basic.lean

renamed data/zmod/quadratic_reciprocity.lean to src/data/zmod/quadratic_reciprocity.lean

renamed field_theory/finite.lean to src/field_theory/finite.lean

renamed field_theory/perfect_closure.lean to src/field_theory/perfect_closure.lean

renamed field_theory/subfield.lean to src/field_theory/subfield.lean

renamed group_theory/abelianization.lean to src/group_theory/abelianization.lean

renamed group_theory/coset.lean to src/group_theory/coset.lean

renamed group_theory/eckmann_hilton.lean to src/group_theory/eckmann_hilton.lean

renamed group_theory/free_abelian_group.lean to src/group_theory/free_abelian_group.lean

renamed group_theory/free_group.lean to src/group_theory/free_group.lean

renamed group_theory/group_action.lean to src/group_theory/group_action.lean

renamed group_theory/order_of_element.lean to src/group_theory/order_of_element.lean

renamed group_theory/perm.lean to src/group_theory/perm.lean

renamed group_theory/quotient_group.lean to src/group_theory/quotient_group.lean

renamed group_theory/subgroup.lean to src/group_theory/subgroup.lean

renamed group_theory/submonoid.lean to src/group_theory/submonoid.lean

renamed linear_algebra/basic.lean to src/linear_algebra/basic.lean

renamed linear_algebra/basis.lean to src/linear_algebra/basis.lean

renamed linear_algebra/default.lean to src/linear_algebra/default.lean

renamed linear_algebra/dimension.lean to src/linear_algebra/dimension.lean

renamed linear_algebra/direct_sum_module.lean to src/linear_algebra/direct_sum_module.lean

renamed linear_algebra/lc.lean to src/linear_algebra/lc.lean

renamed linear_algebra/multivariate_polynomial.lean to src/linear_algebra/multivariate_polynomial.lean

renamed linear_algebra/tensor_product.lean to src/linear_algebra/tensor_product.lean

renamed logic/basic.lean to src/logic/basic.lean

renamed logic/embedding.lean to src/logic/embedding.lean

renamed logic/function.lean to src/logic/function.lean

renamed logic/relation.lean to src/logic/relation.lean

renamed logic/relator.lean to src/logic/relator.lean

renamed logic/schroeder_bernstein.lean to src/logic/schroeder_bernstein.lean

renamed meta/rb_map.lean to src/meta/rb_map.lean

renamed number_theory/dioph.lean to src/number_theory/dioph.lean

renamed number_theory/pell.lean to src/number_theory/pell.lean

renamed order/basic.lean to src/order/basic.lean

renamed order/boolean_algebra.lean to src/order/boolean_algebra.lean

renamed order/bounded_lattice.lean to src/order/bounded_lattice.lean

renamed order/bounds.lean to src/order/bounds.lean

renamed order/complete_boolean_algebra.lean to src/order/complete_boolean_algebra.lean

renamed order/complete_lattice.lean to src/order/complete_lattice.lean

renamed order/conditionally_complete_lattice.lean to src/order/conditionally_complete_lattice.lean

renamed order/default.lean to src/order/default.lean

renamed order/filter.lean to src/order/filter.lean

renamed order/fixed_points.lean to src/order/fixed_points.lean

renamed order/galois_connection.lean to src/order/galois_connection.lean

renamed order/lattice.lean to src/order/lattice.lean

renamed order/liminf_limsup.lean to src/order/liminf_limsup.lean

renamed order/order_iso.lean to src/order/order_iso.lean

renamed order/zorn.lean to src/order/zorn.lean

renamed pending/default.lean to src/pending/default.lean

renamed ring_theory/associated.lean to src/ring_theory/associated.lean

renamed ring_theory/determinant.lean to src/ring_theory/determinant.lean

renamed ring_theory/ideal_operations.lean to src/ring_theory/ideal_operations.lean

renamed ring_theory/ideals.lean to src/ring_theory/ideals.lean

renamed ring_theory/localization.lean to src/ring_theory/localization.lean

renamed ring_theory/matrix.lean to src/ring_theory/matrix.lean

renamed ring_theory/multiplicity.lean to src/ring_theory/multiplicity.lean

renamed ring_theory/noetherian.lean to src/ring_theory/noetherian.lean

renamed ring_theory/principal_ideal_domain.lean to src/ring_theory/principal_ideal_domain.lean

renamed ring_theory/subring.lean to src/ring_theory/subring.lean

renamed ring_theory/unique_factorization_domain.lean to src/ring_theory/unique_factorization_domain.lean

renamed set_theory/cardinal.lean to src/set_theory/cardinal.lean

renamed set_theory/cofinality.lean to src/set_theory/cofinality.lean

renamed set_theory/lists.lean to src/set_theory/lists.lean

renamed set_theory/ordinal.lean to src/set_theory/ordinal.lean

renamed set_theory/ordinal_notation.lean to src/set_theory/ordinal_notation.lean

renamed set_theory/zfc.lean to src/set_theory/zfc.lean

renamed tactic/abel.lean to src/tactic/abel.lean

renamed tactic/algebra.lean to src/tactic/algebra.lean

renamed tactic/alias.lean to src/tactic/alias.lean

renamed tactic/auto_cases.lean to src/tactic/auto_cases.lean

renamed tactic/basic.lean to src/tactic/basic.lean

renamed tactic/cache.lean to src/tactic/cache.lean

renamed tactic/chain.lean to src/tactic/chain.lean

renamed tactic/converter/binders.lean to src/tactic/converter/binders.lean

renamed tactic/converter/interactive.lean to src/tactic/converter/interactive.lean

renamed tactic/converter/old_conv.lean to src/tactic/converter/old_conv.lean

renamed tactic/default.lean to src/tactic/default.lean

renamed tactic/elide.lean to src/tactic/elide.lean

renamed tactic/explode.lean to src/tactic/explode.lean

renamed tactic/ext.lean to src/tactic/ext.lean

renamed tactic/fin_cases.lean to src/tactic/fin_cases.lean

renamed tactic/find.lean to src/tactic/find.lean

renamed tactic/finish.lean to src/tactic/finish.lean

renamed tactic/generalize_proofs.lean to src/tactic/generalize_proofs.lean

renamed tactic/interactive.lean to src/tactic/interactive.lean

renamed tactic/linarith.lean to src/tactic/linarith.lean

renamed tactic/mk_iff_of_inductive_prop.lean to src/tactic/mk_iff_of_inductive_prop.lean

renamed tactic/monotonicity/basic.lean to src/tactic/monotonicity/basic.lean

renamed tactic/monotonicity/default.lean to src/tactic/monotonicity/default.lean

renamed tactic/monotonicity/interactive.lean to src/tactic/monotonicity/interactive.lean

renamed tactic/monotonicity/lemmas.lean to src/tactic/monotonicity/lemmas.lean

renamed tactic/norm_num.lean to src/tactic/norm_num.lean

renamed tactic/pi_instances.lean to src/tactic/pi_instances.lean

renamed tactic/rcases.lean to src/tactic/rcases.lean

renamed tactic/replacer.lean to src/tactic/replacer.lean

renamed tactic/restate_axiom.lean to src/tactic/restate_axiom.lean

renamed tactic/rewrite.lean to src/tactic/rewrite.lean

renamed tactic/ring.lean to src/tactic/ring.lean

renamed tactic/ring2.lean to src/tactic/ring2.lean

renamed tactic/scc.lean to src/tactic/scc.lean

renamed tactic/simpa.lean to src/tactic/simpa.lean

renamed tactic/slice.lean to src/tactic/slice.lean

renamed tactic/split_ifs.lean to src/tactic/split_ifs.lean

renamed tactic/squeeze.lean to src/tactic/squeeze.lean

renamed tactic/subtype_instance.lean to src/tactic/subtype_instance.lean

renamed tactic/tauto.lean to src/tactic/tauto.lean

renamed tactic/tfae.lean to src/tactic/tfae.lean

renamed tactic/tidy.lean to src/tactic/tidy.lean

renamed tactic/where.lean to src/tactic/where.lean

renamed tactic/wlog.lean to src/tactic/wlog.lean



## [2019-01-15 11:15:57+01:00](https://github.com/leanprover-community/mathlib/commit/0c71016)
feat(logic/basic): nonempty.map
#### Estimated changes
modified logic/basic.lean
- \+ *lemma* nonempty.map



## [2019-01-14 14:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/667dcf3)
feat(group_theory/sylow): first sylow theorem (closes [#591](https://github.com/leanprover-community/mathlib/pull/591))
#### Estimated changes
modified group_theory/group_action.lean
- \+ *lemma* comp_hom
- \+ *lemma* comp_hom
- \+ *def* mul_left_cosets

modified group_theory/sylow.lean
- \+/\- *lemma* mem_fixed_points_iff_card_orbit_eq_one
- \+/\- *lemma* card_modeq_card_fixed_points
- \+/\- *lemma* quotient_group.card_preimage_mk
- \+/\- *lemma* mk_vector_prod_eq_one_inj
- \+/\- *lemma* mem_vectors_prod_eq_one
- \+/\- *lemma* mem_vectors_prod_eq_one_iff
- \+/\- *lemma* one_mem_vectors_prod_eq_one
- \+/\- *lemma* one_mem_fixed_points_rotate
- \+/\- *lemma* exists_prime_order_of_dvd_card
- \+ *lemma* mem_fixed_points_mul_left_cosets_iff_mem_normalizer
- \+ *lemma* fixed_points_mul_left_cosets_equiv_quotient
- \+ *lemma* exists_subgroup_card_pow_prime
- \+/\- *lemma* mem_fixed_points_iff_card_orbit_eq_one
- \+/\- *lemma* card_modeq_card_fixed_points
- \+/\- *lemma* quotient_group.card_preimage_mk
- \+/\- *lemma* mk_vector_prod_eq_one_inj
- \+/\- *lemma* mem_vectors_prod_eq_one
- \+/\- *lemma* mem_vectors_prod_eq_one_iff
- \+/\- *lemma* one_mem_vectors_prod_eq_one
- \+/\- *lemma* one_mem_fixed_points_rotate
- \+/\- *lemma* exists_prime_order_of_dvd_card
- \+/\- *def* mk_vector_prod_eq_one
- \+/\- *def* vectors_prod_eq_one
- \+/\- *def* rotate_vectors_prod_eq_one
- \+/\- *def* mk_vector_prod_eq_one
- \+/\- *def* vectors_prod_eq_one
- \+/\- *def* rotate_vectors_prod_eq_one



## [2019-01-14 14:05:58+01:00](https://github.com/leanprover-community/mathlib/commit/f63fb54)
doc(tactic/simpa): rewrite simpa doc
#### Estimated changes
modified docs/tactics.md

modified tactic/simpa.lean



## [2019-01-14 13:34:42+01:00](https://github.com/leanprover-community/mathlib/commit/49c059a)
refactor(analysis): add metric namespace
combines changes from @sgouezel, @PatrickMassot, and @digama0
#### Estimated changes
modified analysis/bounded_linear_maps.lean

modified analysis/complex.lean

modified analysis/emetric_space.lean
- \+ *lemma* cauchy_iff
- \- *lemma* cauchy_of_emetric
- \+/\- *theorem* eq_of_forall_edist_le
- \+ *theorem* uniform_continuous_iff
- \+ *theorem* uniform_embedding_iff
- \- *theorem* uniform_continuous_of_emetric
- \- *theorem* uniform_embedding_of_emetric
- \+/\- *theorem* eq_of_forall_edist_le
- \+ *def* uniform_space_of_edist
- \+ *def* emetric_space.replace_uniformity
- \+ *def* emetric_space.induced
- \- *def* emetric_space.uniform_space_of_edist
- \- *def* replace_uniformity
- \- *def* induced

modified analysis/ennreal.lean

modified analysis/exponential.lean

modified analysis/limits.lean

modified analysis/metric_space.lean
- \- *lemma* cauchy_of_metric
- \- *lemma* mem_uniformity_dist_edist
- \+/\- *theorem* abs_dist
- \+/\- *theorem* eq_of_forall_dist_le
- \+ *theorem* uniform_continuous_iff
- \+ *theorem* uniform_embedding_iff
- \+ *theorem* totally_bounded_iff
- \+ *theorem* nhds_eq
- \+ *theorem* mem_nhds_iff
- \+ *theorem* is_open_iff
- \+ *theorem* tendsto_nhds_nhds
- \+ *theorem* continuous_iff
- \+ *theorem* tendsto_nhds
- \+ *theorem* continuous_iff'
- \+ *theorem* tendsto_at_top
- \+ *theorem* metric.cauchy_seq_iff
- \+ *theorem* metric.cauchy_seq_iff'
- \- *theorem* uniform_continuous_of_metric
- \- *theorem* uniform_embedding_of_metric
- \- *theorem* totally_bounded_of_metric
- \- *theorem* nhds_eq_metric
- \- *theorem* mem_nhds_iff_metric
- \- *theorem* is_open_metric
- \- *theorem* tendsto_nhds_of_metric
- \- *theorem* continuous_of_metric
- \- *theorem* tendsto_nhds_topo_metric
- \- *theorem* continuous_topo_metric
- \- *theorem* tendsto_at_top_metric
- \+/\- *theorem* eq_of_forall_dist_le
- \- *theorem* uniformity_edist'
- \+/\- *theorem* abs_dist
- \- *theorem* cauchy_seq_metric
- \- *theorem* cauchy_seq_metric'
- \+ *def* uniform_space_of_dist
- \+/\- *def* bounded
- \- *def* metric_space.uniform_space_of_dist
- \+/\- *def* bounded

modified analysis/nnreal.lean

modified analysis/normed_space.lean

modified analysis/real.lean

modified analysis/topology/bounded_continuous_function.lean

modified data/padics/hensel.lean

modified data/padics/padic_integers.lean

modified data/padics/padic_numbers.lean

modified data/real/cau_seq_filter.lean



## [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/2f9f3df)
doc(tactic/simpa): update simpa documentation
#### Estimated changes
modified docs/tactics.md

modified tactic/simpa.lean



## [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/263e8a0)
fix(tactic/simpa): only try given expression in "simpa using"
#### Estimated changes
modified data/padics/padic_norm.lean

modified tactic/simpa.lean



## [2019-01-14 12:27:12+01:00](https://github.com/leanprover-community/mathlib/commit/4de9682)
fix(PULL_REQUEST_TEMPLATE): use absolute urls
The relative urls do not resolve correctly.
#### Estimated changes
created .github/PULL_REQUEST_TEMPLATE.md

deleted PULL_REQUEST_TEMPLATE.md



## [2019-01-14 12:03:28+01:00](https://github.com/leanprover-community/mathlib/commit/c7f13fd)
feat(.vscode): add copyright snippet
#### Estimated changes
created .vscode/copyright.code-snippets



## [2019-01-13 19:02:05+01:00](https://github.com/leanprover-community/mathlib/commit/b03c0aa)
feat(group_theory/sylow): Cauchy's theorem ([#458](https://github.com/leanprover-community/mathlib/pull/458))
* feat(group_theory): adding add_subgroup and add_submonoid
* feat(data/list/basic): rotate a list
#### Estimated changes
modified data/equiv/basic.lean
- \+ *lemma* subtype_quotient_equiv_quotient_subtype

modified group_theory/coset.lean

modified group_theory/group_action.lean
- \+ *def* orbit_rel

created group_theory/sylow.lean
- \+ *lemma* mem_fixed_points_iff_card_orbit_eq_one
- \+ *lemma* card_modeq_card_fixed_points
- \+ *lemma* quotient_group.card_preimage_mk
- \+ *lemma* mk_vector_prod_eq_one_inj
- \+ *lemma* mem_vectors_prod_eq_one
- \+ *lemma* mem_vectors_prod_eq_one_iff
- \+ *lemma* one_mem_vectors_prod_eq_one
- \+ *lemma* one_mem_fixed_points_rotate
- \+ *lemma* exists_prime_order_of_dvd_card
- \+ *def* mk_vector_prod_eq_one
- \+ *def* vectors_prod_eq_one
- \+ *def* rotate_vectors_prod_eq_one



## [2019-01-12 10:19:18-05:00](https://github.com/leanprover-community/mathlib/commit/dc6c38a)
fix(field_theory/subfield): is_subfield should be a Prop ([#588](https://github.com/leanprover-community/mathlib/pull/588))
#### Estimated changes
modified field_theory/subfield.lean



## [2019-01-11 19:01:39+01:00](https://github.com/leanprover-community/mathlib/commit/e61a464)
feat(ring_theory/euclidean_domain): add more specific Euclidean domain stuff ([#527](https://github.com/leanprover-community/mathlib/pull/527))
#### Estimated changes
modified algebra/euclidean_domain.lean
- \+ *lemma* eq_div_of_mul_eq_left
- \+ *lemma* eq_div_of_mul_eq_right

created ring_theory/euclidean_domain.lean
- \+ *theorem* span_gcd
- \+ *theorem* gcd_is_unit_iff
- \+ *theorem* is_coprime_of_dvd
- \+ *theorem* dvd_or_coprime



## [2019-01-11 18:59:19+01:00](https://github.com/leanprover-community/mathlib/commit/5c323cd)
feat(category_theory): over and under categories  ([#549](https://github.com/leanprover-community/mathlib/pull/549))
#### Estimated changes
modified category_theory/comma.lean
- \+/\- *lemma* map_right_obj_hom
- \+ *lemma* over_morphism.ext
- \+ *lemma* over_right
- \+ *lemma* over_morphism_right
- \+ *lemma* id_left
- \+ *lemma* comp_left
- \+ *lemma* w
- \+ *lemma* mk_left
- \+ *lemma* mk_hom
- \+ *lemma* hom_mk_left
- \+ *lemma* forget_obj
- \+ *lemma* forget_map
- \+ *lemma* map_obj_left
- \+ *lemma* map_obj_hom
- \+ *lemma* map_map_left
- \+ *lemma* under_morphism.ext
- \+ *lemma* under_left
- \+ *lemma* under_morphism_left
- \+ *lemma* id_right
- \+ *lemma* comp_right
- \+ *lemma* w
- \+ *lemma* mk_right
- \+ *lemma* mk_hom
- \+ *lemma* hom_mk_right
- \+ *lemma* forget_obj
- \+ *lemma* forget_map
- \+ *lemma* map_obj_right
- \+ *lemma* map_obj_hom
- \+ *lemma* map_map_right
- \+/\- *lemma* map_right_obj_hom
- \+ *def* over
- \+ *def* mk
- \+ *def* hom_mk
- \+ *def* forget
- \+ *def* map
- \+ *def* post
- \+ *def* under
- \+ *def* mk
- \+ *def* hom_mk
- \+ *def* forget
- \+ *def* map
- \+ *def* post

created category_theory/limits/over.lean
- \+ *lemma* to_cocone_X
- \+ *lemma* to_cocone_ι
- \+ *lemma* to_cone_X
- \+ *lemma* to_cone_π
- \+ *lemma* colimit_X_hom
- \+ *lemma* colimit_ι_app
- \+ *lemma* limit_X_hom
- \+ *lemma* limit_π_app
- \+ *def* to_cocone
- \+ *def* to_cone
- \+ *def* colimit
- \+ *def* forget_colimit_is_colimit
- \+ *def* limit
- \+ *def* forget_limit_is_limit



## [2019-01-11 18:17:13+01:00](https://github.com/leanprover-community/mathlib/commit/c19b4be)
feat(meta/rb_map): add some monadic filtering
#### Estimated changes
modified meta/rb_map.lean



## [2019-01-11 17:06:02+01:00](https://github.com/leanprover-community/mathlib/commit/7a9b2e4)
Update PULL_REQUEST_TEMPLATE.md
#### Estimated changes
modified PULL_REQUEST_TEMPLATE.md



## [2019-01-11 17:04:58+01:00](https://github.com/leanprover-community/mathlib/commit/6516c34)
doc(README): elect new maintainers
#### Estimated changes
modified README.md



## [2019-01-11 15:35:42+01:00](https://github.com/leanprover-community/mathlib/commit/4f3f86d)
chore(ring_theory/subring): remove unused import
#### Estimated changes
modified ring_theory/subring.lean



## [2019-01-11 11:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/4578796)
feat(data/polynomial): various lemmas about degree and monic and coeff
#### Estimated changes
modified data/polynomial.lean
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_neg
- \+ *lemma* coeff_sub
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_neg
- \- *lemma* monic_X_sub_C
- \+ *theorem* degree_C_mul_X_pow_le
- \+ *theorem* degree_X_pow_le
- \+ *theorem* degree_X_le
- \+ *theorem* monic_of_degree_le
- \+ *theorem* monic_X_pow_add
- \+ *theorem* monic_X_add_C
- \+ *theorem* degree_le_iff_coeff_zero
- \+ *theorem* nat_degree_le_of_degree_le
- \+ *theorem* leading_coeff_mul_X_pow
- \+ *theorem* monic_X_sub_C
- \+ *theorem* monic_X_pow_sub
- \+ *theorem* degree_mod_by_monic_le



## [2019-01-10 15:26:30-05:00](https://github.com/leanprover-community/mathlib/commit/b1684fe)
fix(principal_ideal_domain): correct spelling mistake ([#582](https://github.com/leanprover-community/mathlib/pull/582))
#### Estimated changes
modified ring_theory/principal_ideal_domain.lean
- \+ *lemma* associates_irreducible_iff_prime
- \- *lemma* associates_iredducible_iff_prime



## [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/6e97721)
refactor(principal_ideal_domain): simplify proof of PID -> UFD
#### Estimated changes
modified ring_theory/noetherian.lean
- \+ *lemma* exists_factors

modified ring_theory/principal_ideal_domain.lean
- \+ *lemma* irreducible_iff_prime
- \+ *lemma* associates_iredducible_iff_prime
- \- *lemma* exists_factors
- \- *lemma* prime_of_irreducible
- \- *lemma* associates_prime_of_irreducible
- \- *lemma* eq_of_prod_eq_associates
- \- *lemma* associated_of_associated_prod_prod

modified ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* irreducible_factors
- \+/\- *lemma* irreducible_factors



## [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/f5bf277)
refactor(unique_factorization_domain): simplify definition of UFD
#### Estimated changes
modified data/multiset.lean
- \+ *lemma* dvd_prod

modified ring_theory/associated.lean
- \+ *lemma* is_unit_unit
- \+ *lemma* unit_mul_dvd_iff
- \+ *lemma* mul_unit_dvd_iff
- \+/\- *lemma* not_prime_zero
- \+ *lemma* exists_associated_mem_of_dvd_prod
- \+ *lemma* dvd_iff_dvd_of_rel_left
- \+ *lemma* dvd_mul_unit_iff
- \+ *lemma* dvd_iff_dvd_of_rel_right
- \+ *lemma* eq_zero_iff_of_associated
- \+ *lemma* ne_zero_iff_of_associated
- \+ *lemma* prime_of_associated
- \+ *lemma* prime_iff_of_associated
- \+ *lemma* is_unit_iff_of_associated
- \+ *lemma* irreducible_of_associated
- \+ *lemma* irreducible_iff_of_associated
- \+ *lemma* associated_mul_left_cancel
- \+ *lemma* associated_mul_right_cancel
- \+/\- *lemma* not_prime_zero

modified ring_theory/principal_ideal_domain.lean

modified ring_theory/unique_factorization_domain.lean
- \+ *lemma* induction_on_prime
- \+ *lemma* factors_irreducible
- \+ *lemma* irreducible_iff_prime
- \+ *lemma* irreducible_factors
- \+ *lemma* unique
- \+ *def* of_unique_irreducible_factorization



## [2019-01-10 09:46:28+01:00](https://github.com/leanprover-community/mathlib/commit/8b66ebd)
functions and cardinality ([#556](https://github.com/leanprover-community/mathlib/pull/556))
#### Estimated changes
modified data/set/countable.lean
- \+ *lemma* countable_of_injective_of_countable_image

modified data/set/finite.lean
- \+ *lemma* finite_subsets_of_finite

modified data/set/function.lean
- \+ *lemma* inv_fun_on_image
- \+ *theorem* maps_to'
- \+ *theorem* maps_to_image
- \+ *theorem* maps_to_range



## [2019-01-09 10:08:23+01:00](https://github.com/leanprover-community/mathlib/commit/f488635)
chore(tactic/monotonicity/interactive) use derive for has_reflect ([#578](https://github.com/leanprover-community/mathlib/pull/578))
#### Estimated changes
modified tactic/monotonicity/interactive.lean



## [2019-01-09 10:07:56+01:00](https://github.com/leanprover-community/mathlib/commit/af735a5)
feat(field_theory/finite): field_of_integral_domain ([#579](https://github.com/leanprover-community/mathlib/pull/579))
#### Estimated changes
modified field_theory/finite.lean
- \+ *def* field_of_integral_domain



## [2019-01-09 09:48:35+01:00](https://github.com/leanprover-community/mathlib/commit/d0532c1)
feat(data/polynomial): lemmas about map ([#530](https://github.com/leanprover-community/mathlib/pull/530))
#### Estimated changes
modified algebra/field.lean
- \+ *lemma* injective

modified algebra/group.lean
- \+ *lemma* injective_iff

modified data/polynomial.lean
- \+ *lemma* coeff_X
- \+/\- *lemma* eval_pow
- \+ *lemma* eval₂_hom
- \+ *lemma* map_map
- \+ *lemma* eval₂_map
- \+ *lemma* eval_map
- \+ *lemma* map_id
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* subsingleton_of_monic_zero
- \+ *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+ *lemma* degree_map_eq_of_injective
- \+ *lemma* monic_map
- \+ *lemma* ne_zero_of_monic_of_zero_ne_one
- \+ *lemma* eq_X_add_C_of_degree_le_one
- \+ *lemma* map_sub
- \+ *lemma* map_neg
- \+ *lemma* div_mod_by_monic_unique
- \+ *lemma* map_mod_div_by_monic
- \+ *lemma* map_div_by_monic
- \+ *lemma* map_mod_by_monic
- \+/\- *lemma* degree_mul_leading_coeff_inv
- \+ *lemma* div_zero
- \+ *lemma* degree_div_le
- \+ *lemma* degree_div_lt
- \+ *lemma* degree_map
- \+ *lemma* nat_degree_map
- \+ *lemma* leading_coeff_map
- \+ *lemma* map_div
- \+ *lemma* map_mod
- \+ *lemma* map_eq_zero
- \+ *lemma* exists_root_of_degree_eq_one
- \+/\- *lemma* eval_pow
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \- *lemma* degree_map_eq
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* degree_mul_leading_coeff_inv



## [2019-01-05 16:41:07-05:00](https://github.com/leanprover-community/mathlib/commit/2e63635)
feat(group_theory/subgroup): simple groups ([#572](https://github.com/leanprover-community/mathlib/pull/572))
#### Estimated changes
modified group_theory/subgroup.lean
- \+ *lemma* eq_trivial_iff
- \+ *lemma* simple_group_of_surjective
- \+ *lemma* simple_add_group_of_surjective
- \+ *theorem* additive.simple_add_group_iff
- \+ *theorem* multiplicative.simple_group_iff



## [2019-01-05 16:38:38-05:00](https://github.com/leanprover-community/mathlib/commit/d19c9bc)
feat(data/fintype): decidable_left_inverse_fintype ([#575](https://github.com/leanprover-community/mathlib/pull/575))
#### Estimated changes
modified data/fintype.lean



## [2019-01-05 16:37:57-05:00](https://github.com/leanprover-community/mathlib/commit/395aadd)
feat(group_theory/sign): sign_surjective ([#576](https://github.com/leanprover-community/mathlib/pull/576))
#### Estimated changes
modified group_theory/perm.lean
- \+ *lemma* sign_surjective



## [2019-01-05 14:19:05-05:00](https://github.com/leanprover-community/mathlib/commit/b9c5eb0)
feat(ring_theory/multiplicity): multiplicity of elements of a ring ([#523](https://github.com/leanprover-community/mathlib/pull/523))
#### Estimated changes
modified algebra/group_power.lean
- \+ *lemma* pow_dvd_pow

modified data/multiset.lean
- \+ *lemma* card_smul

modified data/nat/basic.lean

modified data/rat.lean
- \+ *lemma* num_one
- \+ *lemma* denom_one
- \+ *lemma* add_num_denom

created ring_theory/multiplicity.lean
- \+ *lemma* finite_iff_dom
- \+ *lemma* finite_def
- \+ *lemma* not_finite_iff_forall
- \+ *lemma* not_unit_of_finite
- \+ *lemma* ne_zero_of_finite
- \+ *lemma* finite_of_finite_mul_left
- \+ *lemma* finite_of_finite_mul_right
- \+ *lemma* pow_dvd_of_le_multiplicity
- \+ *lemma* pow_multiplicity_dvd
- \+ *lemma* is_greatest
- \+ *lemma* is_greatest'
- \+ *lemma* unique
- \+ *lemma* unique'
- \+ *lemma* le_multiplicity_of_pow_dvd
- \+ *lemma* pow_dvd_iff_le_multiplicity
- \+ *lemma* eq_some_iff
- \+ *lemma* eq_top_iff
- \+ *lemma* one_right
- \+ *lemma* get_one_right
- \+ *lemma* one_left
- \+ *lemma* multiplicity_unit
- \+ *lemma* multiplicity_eq_zero_of_not_dvd
- \+ *lemma* eq_top_iff_not_finite
- \+ *lemma* multiplicity_le_multiplicity_iff
- \+ *lemma* min_le_multiplicity_add
- \+ *lemma* dvd_of_multiplicity_pos
- \+ *lemma* finite_nat_iff
- \+ *lemma* finite_int_iff_nat_abs_finite
- \+ *lemma* finite_int_iff
- \+ *lemma* multiplicity_self
- \+ *lemma* get_multiplicity_self
- \+ *lemma* finite_mul_aux
- \+ *lemma* finite_mul
- \+ *lemma* finite_mul_iff
- \+ *lemma* finite_pow
- \+ *lemma* pow
- \+ *lemma* multiplicity_eq_zero_of_coprime
- \+ *def* multiplicity
- \+ *def* finite



## [2019-01-05 14:17:10-05:00](https://github.com/leanprover-community/mathlib/commit/bc96eca)
feat(group_theory/quotient_group): quotient_ker_equiv_range ([#574](https://github.com/leanprover-community/mathlib/pull/574))
#### Estimated changes
modified algebra/group.lean

modified group_theory/quotient_group.lean



## [2019-01-05 14:13:47-05:00](https://github.com/leanprover-community/mathlib/commit/3ff5e93)
feat(data/polynomial): polynomials over a field are a normalization domain ([#560](https://github.com/leanprover-community/mathlib/pull/560))
#### Estimated changes
modified data/polynomial.lean
- \+ *lemma* eq_C_of_degree_eq_zero
- \+ *lemma* degree_coe_units
- \+ *lemma* nat_degree_coe_units
- \+ *lemma* coeff_coe_units_zero_ne_zero
- \+ *lemma* coeff_inv_units
- \+ *lemma* monic_mul_norm_unit
- \+ *lemma* coe_norm_unit



## [2019-01-05 14:12:49-05:00](https://github.com/leanprover-community/mathlib/commit/87bf618)
feat(data/polynomial): C_neg and C_sub ([#561](https://github.com/leanprover-community/mathlib/pull/561))
#### Estimated changes
modified data/polynomial.lean
- \+ *lemma* C_neg
- \+ *lemma* C_sub



## [2019-01-05 14:12:25-05:00](https://github.com/leanprover-community/mathlib/commit/78d0ebf)
feat(data/multiset): prod_hom and exists_mem_of_rel_of_mem ([#562](https://github.com/leanprover-community/mathlib/pull/562))
#### Estimated changes
modified data/multiset.lean
- \+ *lemma* prod_hom
- \+ *lemma* sum_hom
- \+ *lemma* exists_mem_of_rel_of_mem



## [2019-01-05 14:11:58-05:00](https://github.com/leanprover-community/mathlib/commit/4e509a8)
feat(ring_theory/noetherian): irreducible_induction_on ([#563](https://github.com/leanprover-community/mathlib/pull/563))
#### Estimated changes
modified ring_theory/associated.lean
- \+ *lemma* dvd_and_not_dvd_iff
- \- *theorem* zero_mul

modified ring_theory/ideals.lean
- \+ *lemma* span_singleton_lt_span_singleton

modified ring_theory/noetherian.lean
- \+ *lemma* well_founded_dvd_not_unit
- \+ *lemma* exists_irreducible_factor
- \+ *lemma* irreducible_induction_on



## [2019-01-05 14:10:24-05:00](https://github.com/leanprover-community/mathlib/commit/ea0ff05)
doc(category_theory): update `category_theory` documentation ([#564](https://github.com/leanprover-community/mathlib/pull/564)) [ci-skip]
#### Estimated changes
modified docs/theories/category_theory.md



## [2019-01-05 14:09:18-05:00](https://github.com/leanprover-community/mathlib/commit/33df7ec)
feat(data/nat/enat): has_well_founded for enat ([#565](https://github.com/leanprover-community/mathlib/pull/565))
#### Estimated changes
modified data/nat/enat.lean
- \+ *lemma* coe_ne_bot
- \+ *lemma* to_with_top_top
- \+ *lemma* to_with_top_top'
- \+ *lemma* to_with_top_zero
- \+ *lemma* to_with_top_zero'
- \+ *lemma* to_with_top_coe
- \+ *lemma* to_with_top_coe'
- \+ *lemma* to_with_top_le
- \+ *lemma* to_with_top_lt
- \+ *lemma* lt_wf
- \+ *def* to_with_top



## [2019-01-05 14:06:39-05:00](https://github.com/leanprover-community/mathlib/commit/4bacdf2)
feat(logic/basic): inhabited_of_nonempty with instance parameter ([#566](https://github.com/leanprover-community/mathlib/pull/566))
#### Estimated changes
modified logic/basic.lean



## [2019-01-05 14:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/125feb6)
feat(data/multiset): forall_of_pairwise ([#569](https://github.com/leanprover-community/mathlib/pull/569))
#### Estimated changes
modified data/list/basic.lean
- \+ *lemma* forall_of_pairwise

modified data/multiset.lean
- \+ *lemma* forall_of_pairwise



## [2019-01-05 14:05:30-05:00](https://github.com/leanprover-community/mathlib/commit/da6ec21)
feat(algebra/group): is_conj_one_right ([#570](https://github.com/leanprover-community/mathlib/pull/570))
#### Estimated changes
modified algebra/group.lean
- \+/\- *lemma* is_conj_symm
- \+/\- *lemma* is_conj_trans
- \+ *lemma* is_conj_one_right
- \+ *lemma* is_conj_one_left
- \+/\- *lemma* is_conj_symm
- \+/\- *lemma* is_conj_trans



## [2019-01-05 14:05:06-05:00](https://github.com/leanprover-community/mathlib/commit/a32fa18)
feat(data/finset): finset.card_eq_one ([#571](https://github.com/leanprover-community/mathlib/pull/571))
#### Estimated changes
modified data/finset.lean
- \+ *theorem* card_eq_one



## [2019-01-05 04:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/40fa9ad)
fix(analysis/measure_theory): fix build
#### Estimated changes
modified analysis/measure_theory/lebesgue_measure.lean

modified data/real/nnreal.lean
- \+ *lemma* of_real_add_of_real



## [2019-01-04 20:28:21-05:00](https://github.com/leanprover-community/mathlib/commit/93a330e)
fix(data/real/cau_seq_filter): fix build
#### Estimated changes
modified data/real/cau_seq_filter.lean



## [2019-01-04 19:43:43-05:00](https://github.com/leanprover-community/mathlib/commit/19e7b1f)
feat(analysis/topology): Bounded continuous functions ([#464](https://github.com/leanprover-community/mathlib/pull/464))
#### Estimated changes
modified algebra/group.lean

modified analysis/metric_space.lean
- \+ *lemma* dist_triangle4
- \+ *lemma* dist_triangle4_left
- \+ *lemma* dist_triangle4_right
- \+ *lemma* totally_bounded_of_finite_discretization
- \+ *lemma* cauchy_seq_iff_le_tendsto_0
- \+ *lemma* bounded_empty
- \+ *lemma* bounded_iff_mem_bounded
- \+ *lemma* bounded.subset
- \+ *lemma* bounded_closed_ball
- \+ *lemma* bounded_ball
- \+ *lemma* bounded_iff_subset_ball
- \+ *lemma* bounded_union
- \+ *lemma* bounded_bUnion
- \+ *lemma* bounded_of_compact
- \+ *lemma* bounded_of_finite
- \+ *lemma* bounded_singleton
- \+ *lemma* bounded_range_iff
- \+ *lemma* bounded_of_compact_space
- \+ *lemma* compact_iff_closed_bounded
- \+ *theorem* closed_ball_subset_closed_ball
- \+/\- *theorem* tendsto_at_top_metric
- \+/\- *theorem* cauchy_seq_metric
- \+/\- *theorem* cauchy_seq_metric'
- \+ *theorem* cauchy_seq_bdd
- \+ *theorem* mem_of_closed'
- \+/\- *theorem* tendsto_at_top_metric
- \+/\- *theorem* cauchy_seq_metric
- \+/\- *theorem* cauchy_seq_metric'
- \+ *def* bounded

modified analysis/normed_space.lean
- \+ *def* normed_group.of_add_dist
- \+ *def* normed_group.of_add_dist'

created analysis/topology/bounded_continuous_function.lean
- \+ *lemma* continuous_of_locally_uniform_limit_of_continuous
- \+ *lemma* continuous_of_uniform_limit_of_continuous
- \+ *lemma* continuous_of_lipschitz
- \+ *lemma* bounded_range
- \+ *lemma* dist_eq
- \+ *lemma* dist_set_exists
- \+ *lemma* dist_coe_le_dist
- \+ *lemma* ext
- \+ *lemma* dist_le
- \+ *lemma* dist_zero_of_empty
- \+ *lemma* continuous_comp
- \+ *lemma* equicontinuous_of_continuity_modulus
- \+ *lemma* coe_zero
- \+ *lemma* norm_def
- \+ *lemma* norm_coe_le_norm
- \+ *lemma* norm_le
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* forall_coe_zero_iff_zero
- \+ *lemma* coe_diff
- \+ *lemma* abs_diff_coe_le_dist
- \+ *lemma* coe_le_coe_add_dist
- \+ *theorem* continuous_eval
- \+ *theorem* continuous_evalx
- \+ *theorem* continuous_evalf
- \+ *theorem* arzela_ascoli₁
- \+ *theorem* arzela_ascoli₂
- \+ *theorem* arzela_ascoli
- \+ *def* bounded_continuous_function
- \+ *def* mk_of_compact
- \+ *def* mk_of_discrete
- \+ *def* const
- \+ *def* comp
- \+ *def* cod_restrict

modified analysis/topology/continuity.lean
- \+ *lemma* continuous_of_discrete_topology
- \+ *lemma* compact_iff_compact_space

modified analysis/topology/uniform_space.lean
- \+ *lemma* totally_bounded_empty

modified data/real/ennreal.lean
- \+ *lemma* coe_nonneg
- \+ *lemma* coe_pos
- \+ *lemma* lt_iff_exists_rat_btwn
- \+ *lemma* lt_iff_exists_real_btwn

modified data/real/nnreal.lean
- \+ *lemma* of_real_pos
- \+/\- *lemma* of_real_eq_zero
- \+/\- *lemma* of_real_of_nonpos
- \+ *lemma* of_real_lt_of_real_iff'
- \+/\- *lemma* of_real_lt_of_real_iff
- \+ *lemma* of_real_add
- \- *lemma* zero_lt_of_real
- \+/\- *lemma* of_real_eq_zero
- \+/\- *lemma* of_real_lt_of_real_iff
- \- *lemma* of_real_add_of_real
- \+/\- *lemma* of_real_of_nonpos

modified data/set/basic.lean
- \+ *lemma* range_const_subset

modified data/set/finite.lean
- \+ *theorem* finite.of_fintype



## [2019-01-02 10:12:17-05:00](https://github.com/leanprover-community/mathlib/commit/dcd0466)
feat(analysis/topology): complete sets, minor modifications ([#557](https://github.com/leanprover-community/mathlib/pull/557))
#### Estimated changes
modified analysis/limits.lean

modified analysis/metric_space.lean

modified analysis/normed_space.lean

modified analysis/topology/infinite_sum.lean

modified analysis/topology/topological_space.lean
- \+ *lemma* is_closed_of_closure_subset
- \+ *lemma* mem_of_closed_of_tendsto'
- \+/\- *lemma* mem_closure_of_tendsto
- \+/\- *lemma* mem_closure_of_tendsto

modified analysis/topology/topological_structures.lean
- \+ *lemma* le_of_tendsto_of_tendsto
- \+/\- *lemma* le_of_tendsto
- \+ *lemma* ge_of_tendsto
- \+ *lemma* Sup_of_continuous'
- \+ *lemma* Sup_of_continuous
- \+ *lemma* supr_of_continuous
- \+ *lemma* Inf_of_continuous'
- \+ *lemma* Inf_of_continuous
- \+ *lemma* infi_of_continuous
- \+/\- *lemma* le_of_tendsto
- \- *lemma* Sup_of_Sup_of_monotone_of_continuous
- \- *lemma* supr_of_supr_of_monotone_of_continuous
- \- *lemma* Inf_of_Inf_of_monotone_of_continuous
- \- *lemma* infi_of_infi_of_monotone_of_continuous

modified analysis/topology/uniform_space.lean
- \+ *lemma* is_complete_image_iff
- \+ *lemma* is_closed_of_is_complete
- \+ *lemma* compact_iff_totally_bounded_complete
- \+ *lemma* complete_univ
- \+ *lemma* complete_space_of_is_complete_univ
- \+ *lemma* is_complete_of_is_closed
- \- *lemma* compact_of_totally_bounded_complete
- \- *lemma* complete_of_is_closed
- \- *lemma* complete_of_compact_set
- \+ *def* is_complete



## [2019-01-02 08:57:30-05:00](https://github.com/leanprover-community/mathlib/commit/f59f5d5)
feat(data/real/ennreal): minor additions to ennreal ([#558](https://github.com/leanprover-community/mathlib/pull/558))
#### Estimated changes
modified analysis/ennreal.lean

modified analysis/metric_space.lean

modified data/real/ennreal.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* add_lt_top
- \+ *lemma* add_lt_add_iff_right
- \+ *lemma* mul_eq_top
- \+ *lemma* mul_eq_zero
- \+ *lemma* sub_eq_zero_iff_le
- \+ *lemma* zero_lt_sub_iff_lt
- \+ *lemma* bit0_inj
- \+ *lemma* bit0_eq_zero_iff
- \+ *lemma* bit0_eq_top_iff
- \+ *lemma* bit1_inj
- \+ *lemma* bit1_ne_zero
- \+ *lemma* bit1_eq_one_iff
- \+ *lemma* bit1_eq_top_iff
- \+ *lemma* coe_inv
- \+/\- *lemma* coe_div
- \+/\- *lemma* inv_inv
- \+/\- *lemma* inv_eq_top
- \+/\- *lemma* inv_ne_top
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_ne_zero
- \+/\- *lemma* div_le_iff_le_mul
- \+ *lemma* div_zero_iff
- \+/\- *lemma* div_pos_iff
- \+ *lemma* half_pos
- \+ *lemma* half_lt_self
- \+ *lemma* exists_inv_nat_lt
- \- *lemma* inv_coe
- \+/\- *lemma* coe_div
- \+/\- *lemma* inv_eq_top
- \+/\- *lemma* inv_ne_top
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_ne_zero
- \+/\- *lemma* inv_inv
- \+/\- *lemma* div_le_iff_le_mul
- \+/\- *lemma* div_pos_iff

modified data/real/nnreal.lean
- \+/\- *lemma* of_real_le_of_real_iff
- \+ *lemma* of_real_lt_of_real_iff
- \+/\- *lemma* add_halves
- \+ *lemma* half_lt_self
- \+/\- *lemma* of_real_le_of_real_iff
- \+/\- *lemma* add_halves



## [2019-01-02 06:39:37-05:00](https://github.com/leanprover-community/mathlib/commit/50583b9)
feat(algebra/order): additional theorems on cmp
#### Estimated changes
modified algebra/order.lean
- \+ *theorem* swap_or_else
- \+ *theorem* or_else_eq_lt
- \+ *theorem* cmp_compares
- \+ *theorem* cmp_swap

modified order/basic.lean
- \+ *def* decidable_linear_order.lift

