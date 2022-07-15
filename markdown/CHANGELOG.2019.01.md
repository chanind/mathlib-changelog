## [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/50a03f7)
chore(test): fix test directory structure
#### Estimated changes
Renamed test/tests/coinductive.lean to test/coinductive.lean


Renamed test/tests/examples.lean to test/examples.lean


Renamed test/tests/fin_cases.lean to test/fin_cases.lean


Renamed test/tests/finish1.lean to test/finish1.lean


Renamed test/tests/finish2.lean to test/finish2.lean


Renamed test/tests/finish3.lean to test/finish3.lean


Renamed test/tests/linarith.lean to test/linarith.lean


Renamed test/tests/mk_iff_of_inductive.lean to test/mk_iff_of_inductive.lean


Renamed test/tests/monotonicity.lean to test/monotonicity.lean


Renamed test/tests/monotonicity/test_cases.lean to test/monotonicity/test_cases.lean


Renamed test/tests/norm_num.lean to test/norm_num.lean


Renamed test/tests/replacer.lean to test/replacer.lean


Renamed test/tests/restate_axiom.lean to test/restate_axiom.lean


Renamed test/tests/ring.lean to test/ring.lean


Renamed test/tests/solve_by_elim.lean to test/solve_by_elim.lean


Renamed test/tests/split_ifs.lean to test/split_ifs.lean


Renamed test/tests/tactics.lean to test/tactics.lean


Renamed test/tests/tidy.lean to test/tidy.lean




## [2019-01-30 18:20:41-05:00](https://github.com/leanprover-community/mathlib/commit/12be0aa)
refactor(category_theory/instances): rename `examples` to `instances`
#### Estimated changes
Renamed src/category_theory/examples/measurable_space.lean to src/category_theory/instances/measurable_space.lean
- \- *def* category_theory.examples.Borel
- \- *def* category_theory.examples.Meas
- \+ *def* category_theory.instances.Borel
- \+ *def* category_theory.instances.Meas

Renamed src/category_theory/examples/monoids.lean to src/category_theory/instances/monoids.lean
- \- *def* category_theory.examples.CommMon.forget_to_Mon
- \- *def* category_theory.examples.CommMon
- \- *def* category_theory.examples.Mon
- \- *def* category_theory.examples.is_comm_monoid_hom
- \+ *def* category_theory.instances.CommMon.forget_to_Mon
- \+ *def* category_theory.instances.CommMon
- \+ *def* category_theory.instances.Mon
- \+ *def* category_theory.instances.is_comm_monoid_hom

Renamed src/category_theory/examples/rings.lean to src/category_theory/instances/rings.lean
- \- *def* category_theory.examples.CommRing.Int.cast
- \- *def* category_theory.examples.CommRing.Int.hom_unique
- \- *def* category_theory.examples.CommRing.Int
- \- *lemma* category_theory.examples.CommRing.comp_val
- \- *def* category_theory.examples.CommRing.forget
- \- *def* category_theory.examples.CommRing.forget_to_CommMon
- \- *lemma* category_theory.examples.CommRing.hom_coe_app
- \- *lemma* category_theory.examples.CommRing.id_val
- \- *def* category_theory.examples.CommRing.int.eq_cast'
- \- *lemma* category_theory.examples.CommRing.polynomial_map_val
- \- *lemma* category_theory.examples.CommRing.polynomial_obj_α
- \- *def* category_theory.examples.CommRing.to_Ring
- \- *def* category_theory.examples.CommRing
- \- *def* category_theory.examples.Ring
- \+ *def* category_theory.instances.CommRing.Int.cast
- \+ *def* category_theory.instances.CommRing.Int.hom_unique
- \+ *def* category_theory.instances.CommRing.Int
- \+ *lemma* category_theory.instances.CommRing.comp_val
- \+ *def* category_theory.instances.CommRing.forget
- \+ *def* category_theory.instances.CommRing.forget_to_CommMon
- \+ *lemma* category_theory.instances.CommRing.hom_coe_app
- \+ *lemma* category_theory.instances.CommRing.id_val
- \+ *def* category_theory.instances.CommRing.int.eq_cast'
- \+ *lemma* category_theory.instances.CommRing.polynomial_map_val
- \+ *lemma* category_theory.instances.CommRing.polynomial_obj_α
- \+ *def* category_theory.instances.CommRing.to_Ring
- \+ *def* category_theory.instances.CommRing
- \+ *def* category_theory.instances.Ring

Renamed src/category_theory/examples/topological_spaces.lean to src/category_theory/instances/topological_spaces.lean
- \- *def* category_theory.examples.Top.adj₁
- \- *def* category_theory.examples.Top.adj₂
- \- *def* category_theory.examples.Top.colimit
- \- *def* category_theory.examples.Top.colimit_is_colimit
- \- *def* category_theory.examples.Top.discrete
- \- *def* category_theory.examples.Top.limit
- \- *def* category_theory.examples.Top.limit_is_limit
- \- *def* category_theory.examples.Top.trivial
- \- *def* category_theory.examples.Top
- \- *def* category_theory.examples.nbhd
- \- *def* category_theory.examples.nbhds
- \+ *def* category_theory.instances.Top.adj₁
- \+ *def* category_theory.instances.Top.adj₂
- \+ *def* category_theory.instances.Top.colimit
- \+ *def* category_theory.instances.Top.colimit_is_colimit
- \+ *def* category_theory.instances.Top.discrete
- \+ *def* category_theory.instances.Top.limit
- \+ *def* category_theory.instances.Top.limit_is_limit
- \+ *def* category_theory.instances.Top.trivial
- \+ *def* category_theory.instances.Top
- \+ *def* category_theory.instances.nbhd
- \+ *def* category_theory.instances.nbhds



## [2019-01-30 17:15:23-05:00](https://github.com/leanprover-community/mathlib/commit/829b49b)
chore(.travis.yml): use git clean to clean out untracked files ([#659](https://github.com/leanprover-community/mathlib/pull/659))
* chore(.travis.yml): use git clean to clean out untracked files and delete more obsolete olean files
PR [#641](https://github.com/leanprover-community/mathlib/pull/641) involved renaming a directory. The old directory was still
present in the cache, and in this situation `git status` lists the
directory as a whole as untracked, so the grep did not find any
`.lean` files.
#### Estimated changes
Modified .travis.yml


Added purge_olean.sh




## [2019-01-30 17:07:18+01:00](https://github.com/leanprover-community/mathlib/commit/0eb9db6)
chore(linear_algebra/multivariate_polynomial): move rename to the right place
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \- *lemma* mv_polynomial.hom_eq_hom
- \- *lemma* mv_polynomial.is_id
- \- *def* mv_polynomial.rename
- \- *lemma* mv_polynomial.rename_C
- \- *lemma* mv_polynomial.rename_X
- \- *lemma* mv_polynomial.rename_id
- \- *lemma* mv_polynomial.rename_rename

Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* mv_polynomial.hom_eq_hom
- \+ *lemma* mv_polynomial.is_id
- \+ *def* mv_polynomial.rename
- \+ *lemma* mv_polynomial.rename_C
- \+ *lemma* mv_polynomial.rename_X
- \+ *lemma* mv_polynomial.rename_id
- \+ *lemma* mv_polynomial.rename_rename



## [2019-01-30 16:37:18+01:00](https://github.com/leanprover-community/mathlib/commit/a480160)
feat(data/polynomial): generalize theorems from nonzero_comm_ring to comm_ring ([#653](https://github.com/leanprover-community/mathlib/pull/653))
#### Estimated changes
Modified src/data/polynomial.lean




## [2019-01-30 16:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/065f083)
feat(group_theory): monoid / group closure of union
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *theorem* add_group.closure_eq_mclosure
- \+ *theorem* add_group.closure_mono
- \+ *theorem* add_group.exists_list_of_mem_closure
- \+ *theorem* add_group.mclosure_inv_subset
- \+ *theorem* add_group.mclosure_subset
- \+ *theorem* add_group.mem_closure_union_iff
- \+ *theorem* group.closure_eq_mclosure
- \+ *theorem* group.closure_mono
- \+ *theorem* group.exists_list_of_mem_closure
- \+ *theorem* group.mclosure_inv_subset
- \+ *theorem* group.mclosure_subset
- \+ *theorem* group.mem_closure_union_iff

Modified src/group_theory/submonoid.lean
- \+ *theorem* add_monoid.closure_mono
- \+ *theorem* add_monoid.mem_closure_union_iff
- \+ *theorem* monoid.closure_mono
- \+ *theorem* monoid.mem_closure_union_iff



## [2019-01-30 16:16:31+01:00](https://github.com/leanprover-community/mathlib/commit/f7b9d6b)
refactor(data/equiv/algebra): mv_polynomial mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α)
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *lemma* mv_polynomial.hom_eq_hom
- \+ *lemma* mv_polynomial.is_id
- \+ *def* mv_polynomial.iter_to_sum
- \+ *lemma* mv_polynomial.iter_to_sum_C_C
- \+ *lemma* mv_polynomial.iter_to_sum_C_X
- \+ *lemma* mv_polynomial.iter_to_sum_X
- \+ *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \- *def* mv_polynomial.of_option
- \- *theorem* mv_polynomial.of_option_C
- \- *theorem* mv_polynomial.of_option_X_none
- \- *theorem* mv_polynomial.of_option_X_some
- \- *theorem* mv_polynomial.of_option_add
- \- *theorem* mv_polynomial.of_option_mul
- \- *theorem* mv_polynomial.of_option_to_option
- \+ *def* mv_polynomial.option_equiv_left
- \+ *def* mv_polynomial.option_equiv_right
- \- *def* mv_polynomial.option_ring_equiv
- \+ *def* mv_polynomial.punit_ring_equiv
- \+ *def* mv_polynomial.rename
- \+ *lemma* mv_polynomial.rename_C
- \+ *lemma* mv_polynomial.rename_X
- \+ *lemma* mv_polynomial.rename_id
- \+ *lemma* mv_polynomial.rename_rename
- \+ *def* mv_polynomial.ring_equiv_congr
- \+ *def* mv_polynomial.sum_ring_equiv
- \+ *def* mv_polynomial.sum_to_iter
- \+ *lemma* mv_polynomial.sum_to_iter_C
- \+ *lemma* mv_polynomial.sum_to_iter_Xl
- \+ *lemma* mv_polynomial.sum_to_iter_Xr
- \- *def* mv_polynomial.to_option
- \- *theorem* mv_polynomial.to_option_C
- \- *theorem* mv_polynomial.to_option_C_C
- \- *theorem* mv_polynomial.to_option_C_X
- \- *theorem* mv_polynomial.to_option_X
- \- *theorem* mv_polynomial.to_option_add
- \- *theorem* mv_polynomial.to_option_mul
- \- *theorem* mv_polynomial.to_option_of_option

Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* mv_polynomial.eval₂_pow



## [2019-01-30 10:26:08+01:00](https://github.com/leanprover-community/mathlib/commit/aa944bf)
feat(analysis/exponential): real powers, `cpow_nat_inv_pow` ([#647](https://github.com/leanprover-community/mathlib/pull/647))
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* complex.abs_cpow_real
- \+ *lemma* complex.cpow_add
- \+ *lemma* complex.cpow_def
- \+ *lemma* complex.cpow_int_cast
- \+ *lemma* complex.cpow_mul
- \+ *lemma* complex.cpow_nat_cast
- \+ *lemma* complex.cpow_nat_inv_pow
- \+ *lemma* complex.cpow_neg
- \+ *lemma* complex.cpow_one
- \+ *lemma* complex.cpow_zero
- \+ *lemma* complex.of_real_cpow
- \+ *lemma* complex.one_cpow
- \- *lemma* complex.pow_add
- \- *lemma* complex.pow_def
- \- *lemma* complex.pow_int_cast
- \- *lemma* complex.pow_mul
- \- *lemma* complex.pow_nat_cast
- \+ *lemma* complex.zero_cpow
- \+ *lemma* real.one_rpow
- \+ *lemma* real.rpow_add
- \+ *lemma* real.rpow_def
- \+ *lemma* real.rpow_def_of_nonneg
- \+ *lemma* real.rpow_int_cast
- \+ *lemma* real.rpow_mul
- \+ *lemma* real.rpow_nat_cast
- \+ *lemma* real.rpow_neg
- \+ *lemma* real.rpow_nonneg_of_nonneg
- \+ *lemma* real.rpow_one
- \+ *lemma* real.rpow_zero
- \+ *lemma* real.zero_rpow



## [2019-01-30 09:57:02+01:00](https://github.com/leanprover-community/mathlib/commit/626489a)
feat(topology/metric_space): diameter of a set in metric spaces ([#651](https://github.com/leanprover-community/mathlib/pull/651))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded_iff_diam_ne_top
- \+ *def* metric.diam
- \+ *lemma* metric.diam_ball
- \+ *lemma* metric.diam_closed_ball
- \+ *lemma* metric.diam_empty
- \+ *lemma* metric.diam_eq_zero_of_unbounded
- \+ *lemma* metric.diam_le_of_forall_dist_le
- \+ *lemma* metric.diam_mono
- \+ *lemma* metric.diam_nonneg
- \+ *lemma* metric.diam_singleton
- \+ *lemma* metric.diam_union'
- \+ *lemma* metric.diam_union
- \+ *lemma* metric.dist_le_diam_of_mem

Modified src/topology/metric_space/emetric_space.lean
- \+ *def* emetric.diam
- \+ *lemma* emetric.diam_ball
- \+ *lemma* emetric.diam_closed_ball
- \+ *lemma* emetric.diam_empty
- \+ *lemma* emetric.diam_le_of_forall_edist_le
- \+ *lemma* emetric.diam_mono
- \+ *lemma* emetric.diam_singleton
- \+ *lemma* emetric.diam_union'
- \+ *lemma* emetric.diam_union
- \+ *lemma* emetric.edist_le_diam_of_mem



## [2019-01-30 09:55:58+01:00](https://github.com/leanprover-community/mathlib/commit/ef35c6c)
second countability criteria in metric spaces
#### Estimated changes
Modified src/topology/continuity.lean
- \+ *lemma* compact_range

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.second_countable_of_almost_dense_set
- \+ *lemma* metric.second_countable_of_countable_discretization



## [2019-01-30 09:54:34+01:00](https://github.com/leanprover-community/mathlib/commit/30649f5)
cleanup instances/ennreal
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *theorem* continuous_edist'
- \+ *theorem* continuous_edist
- \+ *lemma* continuous_of_le_add_edist
- \+ *lemma* edist_ne_top_of_mem_ball
- \+ *lemma* emetric.cauchy_seq_iff_le_tendsto_0
- \- *lemma* emetric.continuous_edist
- \- *lemma* emetric.edist_ne_top_of_mem_ball
- \- *def* emetric.metric_space_emetric_ball
- \- *lemma* emetric.nhds_eq_nhds_emetric_ball
- \+ *def* metric_space_emetric_ball
- \+ *lemma* nhds_eq_nhds_emetric_ball
- \+ *theorem* tendsto_edist



## [2019-01-30 09:49:08+01:00](https://github.com/leanprover-community/mathlib/commit/afa535e)
feat(ring_theory/polynomial): hilbert basis theorem
#### Estimated changes
Added src/ring_theory/polynomial.lean
- \+ *def* ideal.degree_le
- \+ *theorem* ideal.is_fg_degree_le
- \+ *def* ideal.leading_coeff
- \+ *def* ideal.leading_coeff_nth
- \+ *theorem* ideal.leading_coeff_nth_mono
- \+ *theorem* ideal.mem_leading_coeff
- \+ *theorem* ideal.mem_leading_coeff_nth
- \+ *theorem* ideal.mem_leading_coeff_nth_zero
- \+ *theorem* ideal.mem_of_polynomial
- \+ *def* ideal.of_polynomial
- \+ *theorem* is_noetherian_ring_polynomial
- \+ *def* polynomial.degree_le
- \+ *theorem* polynomial.degree_le_eq_span_X_pow
- \+ *theorem* polynomial.degree_le_mono
- \+ *theorem* polynomial.mem_degree_le



## [2019-01-29 19:13:38+01:00](https://github.com/leanprover-community/mathlib/commit/860eba6)
chore(.): change occurrences of tests directory to test
#### Estimated changes
Modified docs/mathlib-overview.md


Modified src/tactic/basic.lean




## [2019-01-29 19:07:10+01:00](https://github.com/leanprover-community/mathlib/commit/247dcb2)
feat(linear_algebra): rules for kernel of `of_le`, `cod_restrict`, and `pair`
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.ker_cod_restrict
- \+ *lemma* linear_map.ker_pair
- \+ *lemma* linear_map.range_cod_restrict
- \+ *theorem* submodule.ker_of_le



## [2019-01-29 18:32:34+01:00](https://github.com/leanprover-community/mathlib/commit/4fb6c7d)
chore(test): rename the test directory so that `leanpkg` will find it
#### Estimated changes
Renamed tests/coinductive.lean to test/tests/coinductive.lean


Renamed tests/examples.lean to test/tests/examples.lean


Renamed tests/fin_cases.lean to test/tests/fin_cases.lean


Renamed tests/finish1.lean to test/tests/finish1.lean


Renamed tests/finish2.lean to test/tests/finish2.lean


Renamed tests/finish3.lean to test/tests/finish3.lean


Renamed tests/linarith.lean to test/tests/linarith.lean


Renamed tests/mk_iff_of_inductive.lean to test/tests/mk_iff_of_inductive.lean


Renamed tests/monotonicity.lean to test/tests/monotonicity.lean


Renamed tests/monotonicity/test_cases.lean to test/tests/monotonicity/test_cases.lean


Renamed tests/norm_num.lean to test/tests/norm_num.lean


Renamed tests/replacer.lean to test/tests/replacer.lean


Renamed tests/restate_axiom.lean to test/tests/restate_axiom.lean


Renamed tests/ring.lean to test/tests/ring.lean


Renamed tests/solve_by_elim.lean to test/tests/solve_by_elim.lean


Renamed tests/split_ifs.lean to test/tests/split_ifs.lean


Renamed tests/tactics.lean to test/tests/tactics.lean


Renamed tests/tidy.lean to test/tests/tidy.lean




## [2019-01-29 17:18:52+01:00](https://github.com/leanprover-community/mathlib/commit/fc529b6)
feat(data/complex/basic): of_real_fpow ([#640](https://github.com/leanprover-community/mathlib/pull/640))
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* is_field_hom.map_fpow

Modified src/data/complex/basic.lean
- \+ *lemma* complex.of_real_fpow
- \+/\- *lemma* complex.of_real_inv



## [2019-01-29 17:15:53+01:00](https://github.com/leanprover-community/mathlib/commit/d7d90fa)
docs(tactic/monotonicity/interactive): fix `mono` documentation [ci-skip]
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/monotonicity/interactive.lean




## [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/0924ac0)
fix build
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2019-01-29 17:15:30+01:00](https://github.com/leanprover-community/mathlib/commit/a0e2de9)
refactor(*): use decidable_linear_order.lift
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/data/fin.lean


Modified src/data/real/nnreal.lean




## [2019-01-29 17:15:15+01:00](https://github.com/leanprover-community/mathlib/commit/7cfcce3)
feat(data/equiv/algebra): ring equiv for mv_polynomial
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *def* mv_polynomial.of_option
- \+ *theorem* mv_polynomial.of_option_C
- \+ *theorem* mv_polynomial.of_option_X_none
- \+ *theorem* mv_polynomial.of_option_X_some
- \+ *theorem* mv_polynomial.of_option_add
- \+ *theorem* mv_polynomial.of_option_mul
- \+ *theorem* mv_polynomial.of_option_to_option
- \+ *def* mv_polynomial.option_ring_equiv
- \+ *def* mv_polynomial.pempty_ring_equiv
- \+ *def* mv_polynomial.ring_equiv_of_equiv
- \+ *def* mv_polynomial.to_option
- \+ *theorem* mv_polynomial.to_option_C
- \+ *theorem* mv_polynomial.to_option_C_C
- \+ *theorem* mv_polynomial.to_option_C_X
- \+ *theorem* mv_polynomial.to_option_X
- \+ *theorem* mv_polynomial.to_option_add
- \+ *theorem* mv_polynomial.to_option_mul
- \+ *theorem* mv_polynomial.to_option_of_option



## [2019-01-29 13:20:33+01:00](https://github.com/leanprover-community/mathlib/commit/54f4b29)
feat(tactic/interactive.lean): clear_aux_decl
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Modified tests/tactics.lean




## [2019-01-29 13:20:13+01:00](https://github.com/leanprover-community/mathlib/commit/8faf8df)
feat(field_theory/splitting_field): splits predicate on polynomials
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_eq_degree_of_associated
- \+ *lemma* polynomial.eq_X_add_C_of_degree_eq_one

Added src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.exists_multiset_of_splits
- \+ *lemma* polynomial.exists_root_of_splits
- \+ *def* polynomial.splits
- \+ *lemma* polynomial.splits_C
- \+ *lemma* polynomial.splits_comp_of_splits
- \+ *lemma* polynomial.splits_iff_exists_multiset
- \+ *lemma* polynomial.splits_map_iff
- \+ *lemma* polynomial.splits_mul
- \+ *lemma* polynomial.splits_of_degree_eq_one
- \+ *lemma* polynomial.splits_of_degree_le_one
- \+ *lemma* polynomial.splits_of_exists_multiset
- \+ *lemma* polynomial.splits_of_splits_id
- \+ *lemma* polynomial.splits_of_splits_mul
- \+ *lemma* polynomial.splits_zero

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_domain.exists_mem_factors_of_dvd



## [2019-01-29 13:17:09+01:00](https://github.com/leanprover-community/mathlib/commit/8ee4f2d)
move continuous_of_lipschitz around
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \- *lemma* continuous_of_lipschitz

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* continuous_of_lipschitz
- \+ *lemma* uniform_continuous_of_le_add
- \+ *lemma* uniform_continuous_of_lipschitz



## [2019-01-29 11:39:45+01:00](https://github.com/leanprover-community/mathlib/commit/83edba4)
feat(measure_theory): integral is equal and monotone almost-everywhere and for measurable functions it is a.e. strict at 0
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_congr_ae
- \+ *lemma* measure_theory.lintegral_eq_zero_iff
- \+ *lemma* measure_theory.lintegral_le_lintegral_ae

Modified src/measure_theory/measure_space.lean
- \+ *def* measure_theory.all_ae
- \+ *lemma* measure_theory.all_ae_all_iff
- \+ *lemma* measure_theory.all_ae_congr
- \+ *lemma* measure_theory.all_ae_iff
- \+ *lemma* measure_theory.exists_is_measurable_superset_of_measure_eq_zero
- \+ *lemma* measure_theory.measure.mem_a_e_iff



## [2019-01-29 09:37:59+01:00](https://github.com/leanprover-community/mathlib/commit/cd41aca)
Move tendsto_div to a better place
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_one_div_add_at_top_nhds_0_nat

Modified src/data/real/cau_seq_filter.lean
- \- *lemma* sequentially_complete.tendsto_div

Modified src/topology/sequences.lean




## [2019-01-28 20:15:38+01:00](https://github.com/leanprover-community/mathlib/commit/042c290)
refactor(category_theory/opposites): Make `opposite` irreducible
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* category_theory.cocones_map
- \+/\- *lemma* category_theory.cocones_obj
- \+/\- *def* category_theory.functor.cocones
- \+/\- *lemma* category_theory.functor.cones_map_app
- \+/\- *lemma* category_theory.functor.cones_obj
- \+/\- *def* category_theory.limits.cocone.extensions

Modified src/category_theory/limits/limits.lean
- \+/\- *def* category_theory.limits.is_colimit.nat_iso
- \+/\- *def* category_theory.limits.limit.hom_iso

Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.functor.category.op_comp_app
- \- *lemma* category_theory.functor.category.op_id_app
- \+/\- *lemma* category_theory.functor.hom_obj
- \+/\- *lemma* category_theory.functor.op_hom.map_app
- \+/\- *lemma* category_theory.functor.op_hom.obj
- \+/\- *lemma* category_theory.functor.op_inv.obj
- \+/\- *lemma* category_theory.functor.op_map
- \+/\- *lemma* category_theory.functor.op_obj
- \+/\- *lemma* category_theory.functor.unop_map
- \+/\- *lemma* category_theory.functor.unop_obj
- \+ *def* category_theory.has_hom.hom.op
- \+ *lemma* category_theory.has_hom.hom.op_inj
- \+ *lemma* category_theory.has_hom.hom.op_unop
- \+ *def* category_theory.has_hom.hom.unop
- \+ *lemma* category_theory.has_hom.hom.unop_inj
- \+ *lemma* category_theory.has_hom.hom.unop_op
- \+/\- *def* category_theory.op
- \+ *lemma* category_theory.op_comp
- \+ *lemma* category_theory.op_id
- \+ *lemma* category_theory.op_unop
- \+ *def* category_theory.opposite
- \+ *def* category_theory.unop
- \+ *lemma* category_theory.unop_comp
- \+ *lemma* category_theory.unop_id
- \+ *lemma* category_theory.unop_op

Modified src/category_theory/yoneda.lean
- \+/\- *lemma* category_theory.coyoneda.map_app
- \+/\- *lemma* category_theory.coyoneda.obj_map
- \+/\- *lemma* category_theory.coyoneda.obj_obj
- \+/\- *lemma* category_theory.yoneda.map_app
- \+/\- *lemma* category_theory.yoneda.obj_map
- \+/\- *lemma* category_theory.yoneda.obj_map_id
- \+/\- *lemma* category_theory.yoneda.obj_obj
- \+/\- *def* category_theory.yoneda_sections
- \+/\- *def* category_theory.yoneda_sections_small



## [2019-01-28 20:11:16+01:00](https://github.com/leanprover-community/mathlib/commit/d1b7d91)
feat(category_theory/limits/cones): forgetful functors
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocones.forget
- \+ *lemma* category_theory.limits.cocones.forget_map
- \+ *lemma* category_theory.limits.cocones.forget_obj
- \+ *def* category_theory.limits.cones.forget
- \+ *lemma* category_theory.limits.cones.forget_map
- \+ *lemma* category_theory.limits.cones.forget_obj



## [2019-01-28 19:59:32+01:00](https://github.com/leanprover-community/mathlib/commit/b39d6d8)
feat(*) refactor module
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *def* is_linear_map.mk'
- \+/\- *theorem* is_linear_map.mk'_apply
- \+/\- *def* linear_map.comp
- \+/\- *lemma* linear_map.comp_apply
- \+/\- *theorem* linear_map.ext
- \+/\- *theorem* linear_map.ext_iff
- \+/\- *def* linear_map.id
- \+/\- *theorem* linear_map.is_linear
- \+/\- *theorem* one_smul
- \+/\- *lemma* submodule.neg_mem
- \+/\- *theorem* zero_smul

Modified src/algebra/pi_instances.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/data/dfinsupp.lean
- \+/\- *def* dfinsupp.lmk
- \+/\- *lemma* dfinsupp.lmk_apply
- \+/\- *def* dfinsupp.lsingle
- \+/\- *lemma* dfinsupp.lsingle_apply
- \+/\- *lemma* dfinsupp.mk_smul

Modified src/data/finsupp.lean
- \+/\- *def* finsupp.to_has_scalar'

Modified src/linear_algebra/basic.lean
- \- *lemma* classical.some_spec3
- \+/\- *theorem* linear_equiv.apply_symm_apply
- \+/\- *theorem* linear_equiv.coe_apply
- \+/\- *def* linear_equiv.congr_right
- \+/\- *theorem* linear_equiv.of_bijective_apply
- \+/\- *def* linear_equiv.of_linear
- \+/\- *theorem* linear_equiv.of_linear_apply
- \+/\- *theorem* linear_equiv.of_linear_symm_apply
- \+/\- *def* linear_equiv.of_top
- \+/\- *def* linear_equiv.refl
- \+/\- *def* linear_equiv.symm
- \+/\- *theorem* linear_equiv.symm_apply_apply
- \+/\- *def* linear_equiv.trans
- \+/\- *def* linear_map.cod_restrict
- \+/\- *theorem* linear_map.cod_restrict_apply
- \+/\- *theorem* linear_map.comap_cod_restrict
- \+/\- *theorem* linear_map.comap_injective
- \+/\- *theorem* linear_map.comap_le_comap_iff
- \+/\- *lemma* linear_map.comap_map_eq
- \+/\- *lemma* linear_map.comap_map_eq_self
- \+/\- *theorem* linear_map.comap_pair_prod
- \+/\- *theorem* linear_map.comp_id
- \+/\- *def* linear_map.congr_right
- \+/\- *def* linear_map.copair
- \+/\- *theorem* linear_map.copair_apply
- \+/\- *theorem* linear_map.copair_inl
- \+/\- *theorem* linear_map.copair_inl_inr
- \+/\- *theorem* linear_map.copair_inr
- \+/\- *theorem* linear_map.disjoint_ker'
- \+/\- *theorem* linear_map.disjoint_ker
- \+/\- *def* linear_map.endomorphism_ring
- \+/\- *def* linear_map.fst
- \+/\- *theorem* linear_map.fst_apply
- \+/\- *theorem* linear_map.fst_eq_copair
- \+/\- *theorem* linear_map.fst_pair
- \+/\- *theorem* linear_map.id_comp
- \+/\- *theorem* linear_map.inj_of_disjoint_ker
- \+/\- *def* linear_map.inl
- \+/\- *theorem* linear_map.inl_apply
- \+/\- *theorem* linear_map.inl_eq_pair
- \+/\- *def* linear_map.inr
- \+/\- *theorem* linear_map.inr_apply
- \+/\- *theorem* linear_map.inr_eq_pair
- \+/\- *def* linear_map.inverse
- \+/\- *def* linear_map.ker
- \+/\- *theorem* linear_map.ker_comp
- \+/\- *theorem* linear_map.ker_eq_bot
- \+/\- *theorem* linear_map.ker_eq_top
- \+/\- *theorem* linear_map.ker_id
- \+/\- *theorem* linear_map.ker_le_ker_comp
- \+/\- *theorem* linear_map.ker_zero
- \+/\- *lemma* linear_map.le_ker_iff_map
- \+/\- *theorem* linear_map.map_cod_restrict
- \+/\- *lemma* linear_map.map_comap_eq
- \+/\- *lemma* linear_map.map_comap_eq_self
- \+/\- *theorem* linear_map.map_copair_prod
- \+/\- *theorem* linear_map.map_injective
- \+/\- *theorem* linear_map.map_le_map_iff
- \+/\- *theorem* linear_map.mem_ker
- \+/\- *theorem* linear_map.mem_range
- \+/\- *lemma* linear_map.mul_app
- \+/\- *lemma* linear_map.one_app
- \+/\- *def* linear_map.pair
- \+/\- *theorem* linear_map.pair_apply
- \+/\- *theorem* linear_map.pair_fst_snd
- \+/\- *def* linear_map.range
- \+/\- *theorem* linear_map.range_coe
- \+/\- *theorem* linear_map.range_comp
- \+/\- *theorem* linear_map.range_comp_le_range
- \+/\- *theorem* linear_map.range_eq_top
- \+/\- *theorem* linear_map.range_id
- \+/\- *lemma* linear_map.range_le_iff_comap
- \+/\- *def* linear_map.smul_right
- \+/\- *theorem* linear_map.smul_right_apply
- \+/\- *def* linear_map.snd
- \+/\- *theorem* linear_map.snd_apply
- \+/\- *theorem* linear_map.snd_eq_copair
- \+/\- *theorem* linear_map.snd_pair
- \+/\- *theorem* linear_map.sub_mem_ker_iff
- \+/\- *lemma* linear_map.sum_apply
- \+ *def* linear_map.sup_quotient_to_quotient_inf
- \+/\- *lemma* linear_map.zero_apply
- \+/\- *def* submodule.comap
- \+/\- *theorem* submodule.comap_bot
- \+/\- *lemma* submodule.comap_coe
- \+/\- *lemma* submodule.comap_comp
- \+/\- *theorem* submodule.comap_fst
- \+/\- *theorem* submodule.comap_liftq
- \+/\- *lemma* submodule.comap_mono
- \+/\- *theorem* submodule.comap_snd
- \+/\- *lemma* submodule.comap_top
- \+/\- *theorem* submodule.ker_inl
- \+/\- *theorem* submodule.ker_inr
- \+/\- *theorem* submodule.ker_liftq
- \+/\- *theorem* submodule.ker_liftq_eq_bot
- \+/\- *lemma* submodule.le_comap_map
- \+/\- *def* submodule.liftq
- \+/\- *theorem* submodule.liftq_apply
- \+/\- *theorem* submodule.liftq_mkq
- \+/\- *def* submodule.map
- \+/\- *lemma* submodule.map_bot
- \+/\- *lemma* submodule.map_coe
- \+/\- *lemma* submodule.map_comap_le
- \+/\- *lemma* submodule.map_comp
- \+/\- *lemma* submodule.map_inf_eq_map_inf_comap
- \+/\- *theorem* submodule.map_inl
- \+/\- *theorem* submodule.map_inr
- \+/\- *lemma* submodule.map_le_iff_le_comap
- \+ *theorem* submodule.map_liftq
- \+/\- *lemma* submodule.map_mono
- \+/\- *theorem* submodule.map_top
- \+/\- *def* submodule.mapq
- \+/\- *theorem* submodule.mapq_apply
- \+/\- *theorem* submodule.mapq_mkq
- \+/\- *lemma* submodule.mem_comap
- \+/\- *lemma* submodule.mem_map
- \+/\- *theorem* submodule.mem_map_of_mem
- \+/\- *lemma* submodule.mem_span
- \+/\- *lemma* submodule.mem_span_insert'
- \+/\- *lemma* submodule.mem_span_insert
- \+/\- *lemma* submodule.mem_span_singleton
- \+/\- *def* submodule.mkq
- \+/\- *def* submodule.of_le
- \+/\- *theorem* submodule.prod_comap_inl
- \+/\- *theorem* submodule.prod_comap_inr
- \+/\- *theorem* submodule.prod_map_fst
- \+/\- *theorem* submodule.prod_map_snd
- \+/\- *theorem* submodule.range_fst
- \+ *theorem* submodule.range_liftq
- \+/\- *theorem* submodule.range_snd
- \+/\- *lemma* submodule.span_Union
- \+/\- *lemma* submodule.span_empty
- \+/\- *lemma* submodule.span_eq
- \+/\- *lemma* submodule.span_eq_bot
- \+/\- *lemma* submodule.span_eq_of_le
- \+/\- *lemma* submodule.span_image
- \+/\- *lemma* submodule.span_induction
- \+/\- *lemma* submodule.span_insert_eq_span
- \+/\- *lemma* submodule.span_le
- \+/\- *lemma* submodule.span_mono
- \+/\- *lemma* submodule.span_singleton_eq_bot
- \+/\- *lemma* submodule.span_singleton_eq_range
- \+/\- *lemma* submodule.span_span
- \+/\- *lemma* submodule.span_union
- \+/\- *lemma* submodule.subset_span

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_congr
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_range
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_zero
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_left_inverse_linear_map_of_injective
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_right_inverse_linear_map_of_surjective
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* is_basis.mem_span
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_supported
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.total_repr
- \+/\- *def* is_basis
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* is_basis_injective
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* linear_independent.disjoint_ker
- \+/\- *lemma* linear_independent.image
- \+/\- *lemma* linear_independent.inj_span_iff_inj
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* linear_independent.mono
- \+/\- *lemma* linear_independent.of_image
- \+/\- *def* linear_independent.repr
- \+/\- *lemma* linear_independent.repr_eq
- \+/\- *lemma* linear_independent.repr_range
- \+/\- *lemma* linear_independent.repr_supported
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *def* linear_independent.total_equiv
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.unique
- \+/\- *lemma* linear_independent_empty
- \+/\- *theorem* linear_independent_iff
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* mem_span_insert_exchange
- \+/\- *def* module_equiv_lc
- \+/\- *lemma* zero_not_mem_of_linear_independent

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_eq_injective
- \+/\- *lemma* dim_eq_surjective
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* dim_le_surjective
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_span
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *def* rank
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range

Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *def* direct_sum.lmk
- \+/\- *def* direct_sum.lof
- \+/\- *theorem* direct_sum.mk_smul
- \+/\- *theorem* direct_sum.of_smul
- \+/\- *theorem* direct_sum.to_module.ext
- \+/\- *theorem* direct_sum.to_module.unique
- \+/\- *def* direct_sum.to_module
- \+/\- *lemma* direct_sum.to_module_lof

Modified src/linear_algebra/linear_combination.lean
- \+/\- *theorem* lc.map_id
- \+/\- *theorem* lc.map_total
- \+/\- *theorem* lc.range_restrict_dom
- \+/\- *def* lc.restrict_dom
- \+/\- *theorem* lc.supported_empty
- \+/\- *theorem* lc.supported_univ
- \+/\- *def* lc.total_on
- \+/\- *theorem* lc.total_on_range
- \+/\- *theorem* lc.total_range
- \+/\- *lemma* linear_eq_on
- \+/\- *theorem* mem_span_iff_lc
- \+/\- *theorem* span_eq_map_lc

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* linear_map.compl₂
- \+/\- *theorem* linear_map.compl₂_apply
- \+/\- *theorem* linear_map.compr₂_apply
- \+/\- *theorem* linear_map.ext₂
- \+/\- *theorem* linear_map.flip_inj
- \+/\- *def* linear_map.lcomp
- \+/\- *theorem* linear_map.lcomp_apply
- \+/\- *def* linear_map.lflip
- \+/\- *def* linear_map.llcomp
- \+/\- *theorem* linear_map.llcomp_apply
- \+/\- *theorem* linear_map.map_smul₂
- \+/\- *lemma* tensor_product.add_tmul
- \+/\- *def* tensor_product.congr
- \+/\- *def* tensor_product.curry
- \+/\- *theorem* tensor_product.curry_apply
- \+/\- *def* tensor_product.direct_sum
- \+/\- *theorem* tensor_product.ext
- \+/\- *def* tensor_product.lcurry
- \+/\- *theorem* tensor_product.lcurry_apply
- \+/\- *theorem* tensor_product.lift.unique
- \+/\- *lemma* tensor_product.lift_aux.smul
- \+/\- *def* tensor_product.lift_aux
- \+/\- *def* tensor_product.map
- \+/\- *theorem* tensor_product.map_tmul
- \+/\- *lemma* tensor_product.neg_tmul
- \+/\- *def* tensor_product.smul.aux
- \+/\- *lemma* tensor_product.smul_tmul
- \+/\- *def* tensor_product.tmul
- \+/\- *lemma* tensor_product.tmul_add
- \+/\- *lemma* tensor_product.tmul_neg
- \+/\- *lemma* tensor_product.tmul_smul
- \+/\- *lemma* tensor_product.tmul_zero
- \+/\- *def* tensor_product.uncurry
- \+/\- *theorem* tensor_product.uncurry_apply
- \+/\- *lemma* tensor_product.zero_tmul

Modified src/measure_theory/outer_measure.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal_operations.lean
- \+/\- *theorem* submodule.bot_smul
- \+/\- *theorem* submodule.span_smul_span
- \+/\- *theorem* submodule.top_smul

Modified src/ring_theory/ideals.lean
- \+/\- *def* ideal.span

Modified src/ring_theory/noetherian.lean
- \+/\- *theorem* is_noetherian_of_linear_equiv
- \+/\- *theorem* is_noetherian_of_surjective
- \+/\- *def* submodule.fg

Modified src/ring_theory/principal_ideal_domain.lean




## [2019-01-28 19:52:47+01:00](https://github.com/leanprover-community/mathlib/commit/fd3e5a1)
fix(topology/instances/ennreal): fix merge
#### Estimated changes
Modified src/topology/instances/ennreal.lean




## [2019-01-28 19:34:07+01:00](https://github.com/leanprover-community/mathlib/commit/e62c534)
add ennreal.to_real
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_add
- \+ *lemma* ennreal.of_real_eq_zero
- \+ *lemma* ennreal.of_real_le_of_real
- \+ *lemma* ennreal.of_real_le_of_real_iff
- \+ *lemma* ennreal.of_real_lt_of_real_iff
- \+ *lemma* ennreal.of_real_ne_top
- \+ *lemma* ennreal.of_real_one
- \+ *lemma* ennreal.of_real_pos
- \+ *lemma* ennreal.of_real_to_real
- \+ *lemma* ennreal.of_real_zero
- \+ *lemma* ennreal.to_real_add
- \+ *lemma* ennreal.to_real_eq_zero_iff
- \+ *lemma* ennreal.to_real_le_to_real
- \+ *lemma* ennreal.to_real_lt_to_real
- \+ *lemma* ennreal.to_real_nonneg
- \+ *lemma* ennreal.to_real_of_real
- \+ *lemma* ennreal.top_ne_of_real
- \+ *lemma* ennreal.top_to_real
- \+ *lemma* ennreal.zero_to_real

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_one

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.continuous_of_real
- \+ *lemma* ennreal.tendsto_of_real

Modified src/topology/metric_space/basic.lean
- \+ *lemma* dist_edist
- \- *lemma* dist_eq_edist
- \- *lemma* dist_eq_nndist
- \+ *lemma* dist_nndist
- \+/\- *theorem* edist_dist
- \- *lemma* edist_eq_dist
- \- *lemma* edist_eq_nndist
- \+ *lemma* edist_nndist
- \+ *def* emetric_space.to_metric_space
- \+ *lemma* metric.emetric_ball
- \+ *lemma* metric.emetric_closed_ball
- \+ *lemma* nndist_dist
- \+ *lemma* nndist_edist
- \- *lemma* nndist_eq_dist
- \- *lemma* nndist_eq_edist
- \+ *lemma* sum.dist_eq

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.ball_eq_empty_iff
- \+ *theorem* emetric.mem_closed_ball_self



## [2019-01-28 17:14:45+01:00](https://github.com/leanprover-community/mathlib/commit/8572c6b)
feat(topology): prove continuity of nndist and edist; `ball a r` is a metric space
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous_nnnorm
- \+ *lemma* continuous_smul

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.infi_ennreal
- \+ *lemma* ennreal.mul_lt_top

Modified src/topology/instances/ennreal.lean
- \+ *lemma* emetric.continuous_edist
- \+ *lemma* emetric.edist_ne_top_of_mem_ball
- \+ *def* emetric.metric_space_emetric_ball
- \+ *lemma* emetric.nhds_eq_nhds_emetric_ball
- \+ *lemma* infi_real_pos_eq_infi_nnreal_pos

Modified src/topology/instances/nnreal.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* continuous_nndist'
- \+ *lemma* tendsto_nndist'
- \+ *lemma* uniform_continuous_nndist'

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniformity_edist_nnreal



## [2019-01-28 10:14:51+01:00](https://github.com/leanprover-community/mathlib/commit/afa31be)
refactor(linear_algebra/direct_sum_module): move to algebra/direct_sum
#### Estimated changes
Added src/algebra/direct_sum.lean
- \+ *def* direct_sum.mk
- \+ *lemma* direct_sum.mk_add
- \+ *theorem* direct_sum.mk_inj
- \+ *lemma* direct_sum.mk_neg
- \+ *lemma* direct_sum.mk_sub
- \+ *lemma* direct_sum.mk_zero
- \+ *def* direct_sum.of
- \+ *lemma* direct_sum.of_add
- \+ *theorem* direct_sum.of_inj
- \+ *lemma* direct_sum.of_neg
- \+ *lemma* direct_sum.of_sub
- \+ *lemma* direct_sum.of_zero
- \+ *def* direct_sum.set_to_set
- \+ *theorem* direct_sum.to_group.unique
- \+ *def* direct_sum.to_group
- \+ *lemma* direct_sum.to_group_add
- \+ *lemma* direct_sum.to_group_neg
- \+ *lemma* direct_sum.to_group_of
- \+ *lemma* direct_sum.to_group_sub
- \+ *lemma* direct_sum.to_group_zero
- \+ *def* direct_sum

Modified src/linear_algebra/direct_sum_module.lean
- \+ *def* direct_sum.lmk
- \+ *def* direct_sum.lof
- \+ *def* direct_sum.lset_to_set
- \- *def* direct_sum.mk
- \- *theorem* direct_sum.mk_inj
- \+ *theorem* direct_sum.mk_smul
- \- *def* direct_sum.of
- \- *theorem* direct_sum.of_inj
- \+ *theorem* direct_sum.of_smul
- \- *def* direct_sum.set_to_set
- \+/\- *theorem* direct_sum.to_module.ext
- \- *lemma* direct_sum.to_module.of
- \+/\- *theorem* direct_sum.to_module.unique
- \+/\- *def* direct_sum.to_module
- \- *lemma* direct_sum.to_module_apply
- \- *theorem* direct_sum.to_module_aux.add
- \- *theorem* direct_sum.to_module_aux.smul
- \- *def* direct_sum.to_module_aux
- \+ *lemma* direct_sum.to_module_lof
- \- *def* direct_sum

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* tensor_product.direct_sum



## [2019-01-28 08:02:17+01:00](https://github.com/leanprover-community/mathlib/commit/7199bb3)
chore(linear_algebra/dimension): simplify dim_add_le_dim_add_dim
#### Estimated changes
Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.simple_func.add_apply

Modified src/topology/instances/ennreal.lean




## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/038e0b2)
feat(ring_theory/algebra): remove out_param
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+/\- *def* alg_hom.comap
- \+/\- *theorem* alg_hom.commutes
- \+/\- *def* alg_hom.comp
- \+/\- *lemma* alg_hom.comp_apply
- \+/\- *theorem* alg_hom.comp_assoc
- \+/\- *theorem* alg_hom.comp_id
- \+/\- *theorem* alg_hom.ext
- \+/\- *lemma* alg_hom.id_apply
- \+/\- *theorem* alg_hom.id_comp
- \+/\- *theorem* alg_hom.to_linear_map_inj
- \+ *def* algebra.comap.of_comap
- \+ *def* algebra.comap.to_comap
- \+/\- *lemma* algebra.lmul_apply
- \+/\- *lemma* algebra.lmul_left_apply
- \+/\- *lemma* algebra.lmul_right_apply
- \+/\- *lemma* algebra.map_add
- \+/\- *lemma* algebra.map_mul
- \+/\- *lemma* algebra.map_neg
- \+/\- *lemma* algebra.map_one
- \+/\- *lemma* algebra.map_sub
- \+/\- *lemma* algebra.map_zero
- \+/\- *theorem* algebra.mem_bot
- \+/\- *theorem* algebra.of_id_apply
- \- *def* algebra.of_subring
- \+/\- *def* algebra.to_comap
- \+/\- *theorem* algebra.to_comap_apply
- \+/\- *def* algebra.to_top
- \+/\- *def* algebra_map
- \+/\- *def* mv_polynomial.aeval
- \+/\- *theorem* mv_polynomial.eval_unique
- \+/\- *def* polynomial.aeval
- \+/\- *theorem* polynomial.eval_unique
- \+/\- *def* subalgebra.val



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/af7a7ee)
feat(ring_theory/algebra): remove of_core
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.mul_smul_comm
- \- *def* algebra.of_core
- \+ *def* algebra.of_ring_hom
- \+/\- *def* algebra.of_subring
- \- *lemma* algebra.smul_mul
- \+ *lemma* algebra.smul_mul_assoc
- \+/\- *def* ring.to_ℤ_algebra



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/79ba61c)
feat(ring_theory/algebra): make algebra a class
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+/\- *def* alg_hom.comap
- \+/\- *theorem* alg_hom.commutes
- \+/\- *def* alg_hom.comp
- \+/\- *lemma* alg_hom.comp_apply
- \+/\- *theorem* alg_hom.comp_assoc
- \+/\- *theorem* alg_hom.comp_id
- \+/\- *theorem* alg_hom.ext
- \+/\- *lemma* alg_hom.id_apply
- \+/\- *theorem* alg_hom.id_comp
- \+/\- *def* alg_hom.to_linear_map
- \+/\- *theorem* alg_hom.to_linear_map_inj
- \+/\- *def* algebra.adjoin
- \+/\- *def* algebra.comap
- \+/\- *theorem* algebra.commutes
- \+/\- *theorem* algebra.left_comm
- \+/\- *def* algebra.lmul
- \+/\- *lemma* algebra.lmul_apply
- \+/\- *def* algebra.lmul_left
- \+/\- *lemma* algebra.lmul_left_apply
- \+/\- *def* algebra.lmul_right
- \+/\- *lemma* algebra.lmul_right_apply
- \+/\- *lemma* algebra.map_add
- \+/\- *lemma* algebra.map_mul
- \+/\- *lemma* algebra.map_neg
- \+/\- *lemma* algebra.map_one
- \+/\- *lemma* algebra.map_sub
- \+/\- *lemma* algebra.map_zero
- \+/\- *theorem* algebra.mem_bot
- \+/\- *theorem* algebra.mem_top
- \- *def* algebra.mv_polynomial
- \+/\- *def* algebra.of_id
- \+/\- *theorem* algebra.of_id_apply
- \- *def* algebra.polynomial
- \- *def* algebra.right
- \+/\- *theorem* algebra.smul_def
- \+/\- *lemma* algebra.smul_mul
- \+/\- *def* algebra.to_comap
- \+/\- *theorem* algebra.to_comap_apply
- \+/\- *def* algebra.to_top
- \+ *def* algebra_map
- \+/\- *def* mv_polynomial.aeval
- \+/\- *theorem* mv_polynomial.aeval_def
- \+/\- *theorem* mv_polynomial.eval_unique
- \+/\- *def* polynomial.aeval
- \+/\- *theorem* polynomial.aeval_def
- \+/\- *theorem* polynomial.eval_unique
- \+/\- *theorem* subalgebra.ext
- \+/\- *theorem* subalgebra.mem_coe
- \+/\- *def* subalgebra.to_submodule
- \+/\- *def* subalgebra.val



## [2019-01-27 22:50:42+01:00](https://github.com/leanprover-community/mathlib/commit/a0b6cae)
feat(ring_theory/algebra): define algebra over a commutative ring
#### Estimated changes
Added src/ring_theory/algebra.lean
- \+ *def* alg_hom.comap
- \+ *theorem* alg_hom.commutes
- \+ *def* alg_hom.comp
- \+ *lemma* alg_hom.comp_apply
- \+ *theorem* alg_hom.comp_assoc
- \+ *theorem* alg_hom.comp_id
- \+ *theorem* alg_hom.ext
- \+ *lemma* alg_hom.id_apply
- \+ *theorem* alg_hom.id_comp
- \+ *lemma* alg_hom.map_add
- \+ *lemma* alg_hom.map_mul
- \+ *lemma* alg_hom.map_neg
- \+ *lemma* alg_hom.map_one
- \+ *lemma* alg_hom.map_sub
- \+ *lemma* alg_hom.map_zero
- \+ *def* alg_hom.to_linear_map
- \+ *lemma* alg_hom.to_linear_map_apply
- \+ *theorem* alg_hom.to_linear_map_inj
- \+ *def* algebra.adjoin
- \+ *def* algebra.comap
- \+ *theorem* algebra.commutes
- \+ *theorem* algebra.left_comm
- \+ *def* algebra.lmul
- \+ *lemma* algebra.lmul_apply
- \+ *def* algebra.lmul_left
- \+ *lemma* algebra.lmul_left_apply
- \+ *def* algebra.lmul_right
- \+ *lemma* algebra.lmul_right_apply
- \+ *lemma* algebra.map_add
- \+ *lemma* algebra.map_mul
- \+ *lemma* algebra.map_neg
- \+ *lemma* algebra.map_one
- \+ *lemma* algebra.map_sub
- \+ *lemma* algebra.map_zero
- \+ *theorem* algebra.mem_bot
- \+ *theorem* algebra.mem_top
- \+ *def* algebra.mv_polynomial
- \+ *def* algebra.of_core
- \+ *def* algebra.of_id
- \+ *theorem* algebra.of_id_apply
- \+ *def* algebra.of_subring
- \+ *def* algebra.polynomial
- \+ *def* algebra.right
- \+ *theorem* algebra.smul_def
- \+ *lemma* algebra.smul_mul
- \+ *def* algebra.to_comap
- \+ *theorem* algebra.to_comap_apply
- \+ *def* algebra.to_top
- \+ *def* is_ring_hom.to_ℤ_alg_hom
- \+ *def* mv_polynomial.aeval
- \+ *theorem* mv_polynomial.aeval_def
- \+ *theorem* mv_polynomial.eval_unique
- \+ *def* polynomial.aeval
- \+ *theorem* polynomial.aeval_def
- \+ *theorem* polynomial.eval_unique
- \+ *def* ring.to_ℤ_algebra
- \+ *def* subalgebra.comap
- \+ *theorem* subalgebra.ext
- \+ *theorem* subalgebra.mem_coe
- \+ *def* subalgebra.to_submodule
- \+ *def* subalgebra.under
- \+ *def* subalgebra.val



## [2019-01-27 22:44:50+01:00](https://github.com/leanprover-community/mathlib/commit/1d2eda7)
feat(category_theory/isomorphism): as_iso
Also clean up some proofs.
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *def* category_theory.as_iso
- \+ *lemma* category_theory.as_iso_hom
- \+ *lemma* category_theory.as_iso_inv
- \+/\- *def* category_theory.functor.on_iso
- \+/\- *lemma* category_theory.iso.ext



## [2019-01-27 22:43:45+01:00](https://github.com/leanprover-community/mathlib/commit/ccd895f)
feat(category_theory/types): conversions between iso and equiv
#### Estimated changes
Modified src/category_theory/types.lean
- \+ *def* category_theory.iso.to_equiv
- \+ *lemma* category_theory.iso.to_equiv_fun
- \+ *lemma* category_theory.iso.to_equiv_symm_fun
- \+ *def* equiv.to_iso
- \+ *lemma* equiv.to_iso_hom
- \+ *lemma* equiv.to_iso_inv



## [2019-01-27 22:42:53+01:00](https://github.com/leanprover-community/mathlib/commit/d074b51)
refactor(category_theory/concrete_category): move `bundled` to own file
#### Estimated changes
Modified src/category_theory/category.lean
- \- *lemma* category_theory.bundled_hom_coe
- \- *lemma* category_theory.concrete_category_comp
- \- *lemma* category_theory.concrete_category_id
- \- *def* category_theory.mk_ob

Added src/category_theory/concrete_category.lean
- \+ *lemma* category_theory.bundled.bundled_hom_coe
- \+ *lemma* category_theory.bundled.concrete_category_comp
- \+ *lemma* category_theory.bundled.concrete_category_id
- \+ *def* category_theory.bundled.map
- \+ *def* category_theory.concrete_functor
- \+ *def* category_theory.forget
- \+ *def* category_theory.mk_ob

Modified src/category_theory/examples/measurable_space.lean


Modified src/category_theory/examples/monoids.lean


Modified src/category_theory/examples/rings.lean


Modified src/category_theory/examples/topological_spaces.lean


Modified src/category_theory/functor.lean
- \- *def* category_theory.bundled.map
- \- *def* category_theory.concrete_functor

Modified src/category_theory/types.lean
- \- *def* category_theory.forget



## [2019-01-27 22:40:37+01:00](https://github.com/leanprover-community/mathlib/commit/50398e5)
feat(category_theory/full_subcategory): induced categories
#### Estimated changes
Modified src/category_theory/full_subcategory.lean
- \+ *lemma* category_theory.full_subcategory_inclusion.map
- \+ *lemma* category_theory.full_subcategory_inclusion.obj
- \+/\- *def* category_theory.full_subcategory_inclusion
- \+ *def* category_theory.induced_category
- \+ *lemma* category_theory.induced_functor.hom
- \+ *lemma* category_theory.induced_functor.obj
- \+ *def* category_theory.induced_functor



## [2019-01-27 22:37:46+01:00](https://github.com/leanprover-community/mathlib/commit/19c2f68)
feat(analysis/exponential): complex powers
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* complex.exp_eq_exp_iff_exists_int
- \+ *lemma* complex.exp_eq_exp_iff_exp_sub_eq_one
- \+ *lemma* complex.exp_eq_one_iff
- \+ *lemma* complex.pow_add
- \+ *lemma* complex.pow_def
- \+ *lemma* complex.pow_int_cast
- \+ *lemma* complex.pow_mul
- \+ *lemma* complex.pow_nat_cast
- \+ *lemma* real.log_mul



## [2019-01-27 22:33:10+01:00](https://github.com/leanprover-community/mathlib/commit/c057758)
feat(data/complex/exponential): exp_eq_one_iff
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_eq_one_iff



## [2019-01-27 22:32:41+01:00](https://github.com/leanprover-community/mathlib/commit/db69173)
refactor(algebra/field_power): notation for fpow
#### Estimated changes
Modified src/algebra/field_power.lean
- \+/\- *lemma* fpow_add
- \+/\- *lemma* fpow_eq_gpow
- \+/\- *lemma* fpow_ge_one_of_nonneg
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_le_of_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+/\- *lemma* fpow_ne_zero_of_ne_zero
- \+/\- *lemma* fpow_neg
- \+ *lemma* fpow_neg_succ_of_nat
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+ *lemma* fpow_of_nat
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* fpow_sub
- \+/\- *lemma* fpow_zero
- \+/\- *lemma* zero_fpow

Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean
- \+/\- *lemma* padic_norm.le_of_dvd

Modified src/data/padics/padic_numbers.lean




## [2019-01-27 22:31:44+01:00](https://github.com/leanprover-community/mathlib/commit/d359aa8)
feat(order/conditionally_complete_lattice): cinfi_const ([#634](https://github.com/leanprover-community/mathlib/pull/634))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.range_const

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* lattice.cinfi_const
- \+/\- *lemma* lattice.cinfi_le
- \+ *theorem* lattice.csupr_const
- \+/\- *lemma* lattice.le_csupr



## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/06eba7f)
update authors on expr.lean (I don't know who's responsible for what)
#### Estimated changes
Modified src/meta/expr.lean




## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/be5dba9)
fix(tactic/norm_num): only check core norm_num output up to numeral structure
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/norm_num.lean




## [2019-01-27 22:30:58+01:00](https://github.com/leanprover-community/mathlib/commit/daa7684)
refactor(tactic/basic): move non-tactic decls to meta folder
#### Estimated changes
Added src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/tactic/basic.lean




## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/6781ff0)
feat(tactic/linarith): prefer type of goal if there are multiple types
#### Estimated changes
Modified src/tactic/linarith.lean


Modified tests/linarith.lean




## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/8affebd)
fix(tactic/linarith): remove unused code
#### Estimated changes
Modified src/tactic/linarith.lean




## [2019-01-27 22:28:46+01:00](https://github.com/leanprover-community/mathlib/commit/92508dc)
fix(tactic/linarith): properly handle problems with inequalities in multiple types
When problems have inequalities over multiple types, it's almost safe to process everything at once, since none of the
variables overlap. But linarith deals with constants by homogenizing them and the "constant" variables do overlap.
This fix creates one call to linarith for each type that appears in a hypothesis.
#### Estimated changes
Modified src/tactic/linarith.lean


Modified tests/linarith.lean




## [2019-01-27 00:35:53-05:00](https://github.com/leanprover-community/mathlib/commit/84d1c45)
feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton ([#630](https://github.com/leanprover-community/mathlib/pull/630))
* feat(tactic/match-stub): use Lean holes to create a pattern matching skeleton
* feat(tactic/match-stub): add hole for listing relevant constructors
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-01-25 17:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/315a642)
feat(measure_theory): add Hahn decomposition
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_nnreal_add

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_nonneg

Added src/measure_theory/decomposition.lean
- \+ *lemma* measure_theory.hahn_decomposition

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure_eq_inter_diff
- \+ *lemma* measure_theory.tendsto_measure_Inter
- \+ *lemma* measure_theory.tendsto_measure_Union
- \+ *lemma* tendsto_at_top_infi_nat
- \+ *lemma* tendsto_at_top_supr_nat



## [2019-01-24 16:02:42+01:00](https://github.com/leanprover-community/mathlib/commit/ed2ab1a)
feat(measure_theory): measures form a complete lattice
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.empty_diff

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.Inf_apply
- \+ *lemma* measure_theory.measure.Inf_caratheodory

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.Inf_eq_of_function_Inf_gen
- \+ *def* measure_theory.outer_measure.Inf_gen
- \+ *lemma* measure_theory.outer_measure.Inf_gen_empty
- \+ *lemma* measure_theory.outer_measure.Inf_gen_nonempty1
- \+ *lemma* measure_theory.outer_measure.Inf_gen_nonempty2
- \+ *theorem* measure_theory.outer_measure.top_caratheodory



## [2019-01-24 09:18:32+01:00](https://github.com/leanprover-community/mathlib/commit/4aacae3)
feat(data/equiv/algebra): instances for transporting algebra across an equiv ([#618](https://github.com/leanprover-community/mathlib/pull/618))
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *lemma* equiv.add_def
- \+ *lemma* equiv.inv_def
- \+ *lemma* equiv.mul_def
- \+ *lemma* equiv.neg_def
- \+ *lemma* equiv.one_def
- \+ *lemma* equiv.zero_def



## [2019-01-24 09:17:37+01:00](https://github.com/leanprover-community/mathlib/commit/c49e89d)
feat(category_theory/adjunction): definitions, basic proofs, and examples ([#619](https://github.com/leanprover-community/mathlib/pull/619))
#### Estimated changes
Added src/category_theory/adjunction.lean
- \+ *def* category_theory.adjunction.adjunction_of_equiv_left
- \+ *def* category_theory.adjunction.adjunction_of_equiv_right
- \+ *def* category_theory.adjunction.cocones_iso
- \+ *def* category_theory.adjunction.comp
- \+ *def* category_theory.adjunction.cones_iso
- \+ *lemma* category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_left
- \+ *lemma* category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_right_symm
- \+ *def* category_theory.adjunction.functoriality_is_left_adjoint
- \+ *def* category_theory.adjunction.functoriality_is_right_adjoint
- \+ *lemma* category_theory.adjunction.hom_equiv_naturality_left
- \+ *lemma* category_theory.adjunction.hom_equiv_naturality_left_symm
- \+ *lemma* category_theory.adjunction.hom_equiv_naturality_right
- \+ *lemma* category_theory.adjunction.hom_equiv_naturality_right_symm
- \+ *def* category_theory.adjunction.id
- \+ *def* category_theory.adjunction.left_adjoint_of_equiv
- \+ *def* category_theory.adjunction.left_adjoint_preserves_colimits
- \+ *lemma* category_theory.adjunction.left_triangle
- \+ *lemma* category_theory.adjunction.left_triangle_components
- \+ *def* category_theory.adjunction.mk_of_hom_equiv
- \+ *def* category_theory.adjunction.mk_of_unit_counit
- \+ *def* category_theory.adjunction.right_adjoint_of_equiv
- \+ *def* category_theory.adjunction.right_adjoint_preserves_limits
- \+ *lemma* category_theory.adjunction.right_triangle
- \+ *lemma* category_theory.adjunction.right_triangle_components

Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.bundled_hom_coe
- \+/\- *lemma* category_theory.concrete_category_comp
- \+/\- *lemma* category_theory.concrete_category_id

Modified src/category_theory/examples/monoids.lean


Modified src/category_theory/examples/rings.lean
- \+ *def* category_theory.examples.CommRing.Int.cast
- \+ *def* category_theory.examples.CommRing.Int.hom_unique
- \+ *def* category_theory.examples.CommRing.Int
- \+ *lemma* category_theory.examples.CommRing.comp_val
- \+ *def* category_theory.examples.CommRing.forget
- \+/\- *def* category_theory.examples.CommRing.forget_to_CommMon
- \+ *lemma* category_theory.examples.CommRing.hom_coe_app
- \+ *lemma* category_theory.examples.CommRing.id_val
- \+ *def* category_theory.examples.CommRing.int.eq_cast'
- \+ *lemma* category_theory.examples.CommRing.polynomial_map_val
- \+ *lemma* category_theory.examples.CommRing.polynomial_obj_α
- \+ *def* category_theory.examples.CommRing.to_Ring
- \- *lemma* category_theory.examples.CommRing_hom_coe_app

Modified src/category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.Top.adj₁
- \+ *def* category_theory.examples.Top.adj₂
- \+ *def* category_theory.examples.Top.discrete
- \+ *def* category_theory.examples.Top.trivial

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.functor.cocones_map_app
- \+ *lemma* category_theory.functor.cones_map_app
- \- *def* category_theory.limits.cocone.precompose
- \+ *def* category_theory.limits.cocones.precompose
- \+ *lemma* category_theory.limits.cocones.precompose_map_hom
- \+ *lemma* category_theory.limits.cocones.precompose_obj_X
- \+ *lemma* category_theory.limits.cocones.precompose_obj_ι
- \- *def* category_theory.limits.cone.postcompose
- \+ *def* category_theory.limits.cones.postcompose
- \+ *lemma* category_theory.limits.cones.postcompose_map_hom
- \+ *lemma* category_theory.limits.cones.postcompose_obj_X
- \+ *lemma* category_theory.limits.cones.postcompose_obj_π

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit_iso_unique_cocone_morphism
- \+ *def* category_theory.limits.is_limit_iso_unique_cone_morphism

Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.unique_of_equiv



## [2019-01-23 16:35:39+01:00](https://github.com/leanprover-community/mathlib/commit/0e6c358)
feat(set_theory/cardinal): more lemmas on cardinality ([#595](https://github.com/leanprover-community/mathlib/pull/595))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *def* set.image_factorization
- \+ *lemma* set.image_factorization_eq
- \+ *def* set.range_factorization
- \+ *lemma* set.range_factorization_eq
- \+ *lemma* set.surjective_onto_image
- \+ *lemma* set.surjective_onto_range

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_image_le
- \+ *theorem* cardinal.mk_le_of_injective
- \+ *theorem* cardinal.mk_le_of_surjective
- \+ *theorem* cardinal.mk_quot_le
- \+ *theorem* cardinal.mk_quotient_le
- \+ *theorem* cardinal.mk_range_le
- \+ *theorem* cardinal.mk_subtype_le
- \+ *theorem* cardinal.mk_univ



## [2019-01-23 14:24:28+01:00](https://github.com/leanprover-community/mathlib/commit/9be8905)
refactor(topology/sequences): restructure proofs
#### Estimated changes
Modified src/topology/sequences.lean
- \+ *lemma* continuous.to_sequentially_continuous
- \+ *lemma* continuous_iff_sequentially_continuous
- \+ *def* is_seq_closed
- \+ *lemma* is_seq_closed_iff_is_closed
- \+ *lemma* is_seq_closed_of_def
- \+ *lemma* is_seq_closed_of_is_closed
- \+ *lemma* mem_of_is_closed_sequential
- \+ *lemma* mem_of_is_seq_closed
- \- *lemma* sequence.const_seq_conv
- \- *lemma* sequence.cont_iff_seq_cont
- \- *lemma* sequence.cont_to_seq_cont
- \- *lemma* sequence.is_mem_of_conv_to_of_is_seq_closed
- \- *lemma* sequence.is_mem_of_is_closed_of_conv_to
- \- *def* sequence.is_seq_closed
- \- *lemma* sequence.is_seq_closed_iff_is_closed
- \- *lemma* sequence.is_seq_closed_of_def
- \- *lemma* sequence.is_seq_closed_of_is_closed
- \- *lemma* sequence.metric_space.seq_tendsto_iff
- \- *def* sequence.sequential_closure
- \- *lemma* sequence.sequential_closure_subset_closure
- \- *def* sequence.sequentially_continuous
- \- *lemma* sequence.subset_seq_closure
- \- *lemma* sequence.topological_space.seq_tendsto_iff
- \+ *def* sequential_closure
- \+ *lemma* sequential_closure_subset_closure
- \+ *def* sequentially_continuous
- \+ *lemma* subset_sequential_closure
- \+ *lemma* topological_space.seq_tendsto_iff



## [2019-01-23 14:24:12+01:00](https://github.com/leanprover-community/mathlib/commit/4018daf)
feat(topology): sequences, sequential spaces, and sequential continuity (closes [#440](https://github.com/leanprover-community/mathlib/pull/440))
Co-Authored-By: Reid Barton <rwbarton@gmail.com>
#### Estimated changes
Added src/topology/sequences.lean
- \+ *lemma* sequence.const_seq_conv
- \+ *lemma* sequence.cont_iff_seq_cont
- \+ *lemma* sequence.cont_to_seq_cont
- \+ *lemma* sequence.is_mem_of_conv_to_of_is_seq_closed
- \+ *lemma* sequence.is_mem_of_is_closed_of_conv_to
- \+ *def* sequence.is_seq_closed
- \+ *lemma* sequence.is_seq_closed_iff_is_closed
- \+ *lemma* sequence.is_seq_closed_of_def
- \+ *lemma* sequence.is_seq_closed_of_is_closed
- \+ *lemma* sequence.metric_space.seq_tendsto_iff
- \+ *def* sequence.sequential_closure
- \+ *lemma* sequence.sequential_closure_subset_closure
- \+ *def* sequence.sequentially_continuous
- \+ *lemma* sequence.subset_seq_closure
- \+ *lemma* sequence.topological_space.seq_tendsto_iff



## [2019-01-23 13:24:31+01:00](https://github.com/leanprover-community/mathlib/commit/c06fb67)
refactor(category_theory/category): split off has_hom
This gives a little more flexibility when defining a category,
which will be used for opposite categories. It should also be
useful for defining the free category on a graph.
#### Estimated changes
Modified src/category_theory/category.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* category_theory.functor.hom_obj



## [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/2c95d2a)
maintain(vscode): add ruler at 100 in editor
#### Estimated changes
Modified .vscode/settings.json




## [2019-01-23 12:52:40+01:00](https://github.com/leanprover-community/mathlib/commit/b2700dd)
maintain(.vscode): add default settings
#### Estimated changes
Added .vscode/settings.json




## [2019-01-23 12:45:23+01:00](https://github.com/leanprover-community/mathlib/commit/6da9b21)
le_induction
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_induction



## [2019-01-23 12:38:43+01:00](https://github.com/leanprover-community/mathlib/commit/60efaec)
chore(topology): move contraction_mapping to metric_space/lipschitz
#### Estimated changes
Renamed src/contraction_mapping.lean to src/topology/metric_space/lipschitz.lean




## [2019-01-23 11:48:36+01:00](https://github.com/leanprover-community/mathlib/commit/5317b59)
refactor(contraction_mapping): add more proves about Lipschitz continuous functions; cleanup proofs
#### Estimated changes
Modified src/algebra/pi_instances.lean
- \- *def* prod.prod_semilattice_sup

Modified src/analysis/normed_space/basic.lean
- \- *lemma* squeeze_zero

Modified src/contraction_mapping.lean
- \- *lemma* continuous_prod_snd
- \- *lemma* dist_bound_of_contraction
- \- *lemma* dist_inequality_of_contraction
- \- *theorem* fixed_point_exists_of_contraction
- \- *lemma* fixed_point_of_iteration_limit
- \+ *lemma* fixed_point_of_tendsto_iterate
- \- *theorem* fixed_point_unique_of_contraction
- \- *lemma* iterated_lipschitz_of_lipschitz
- \- *def* lipschitz
- \+ *lemma* lipschitz_with.dist_bound_of_contraction
- \+ *lemma* lipschitz_with.dist_inequality_of_contraction
- \+ *theorem* lipschitz_with.exists_fixed_point_of_contraction
- \+ *theorem* lipschitz_with.fixed_point_unique_of_contraction
- \+ *def* lipschitz_with
- \- *lemma* tendsto_dist_bound_at_top_nhds_0
- \- *lemma* uniform_continuous_of_lipschitz

Modified src/order/filter.lean


Modified src/topology/metric_space/basic.lean
- \- *lemma* dist_prod_eq_dist_0
- \+ *theorem* metric.uniformity_eq_comap_nhds_zero
- \+ *lemma* squeeze_zero

Modified src/topology/uniform_space/basic.lean




## [2019-01-23 11:48:20+01:00](https://github.com/leanprover-community/mathlib/commit/96198b9)
feat(contraction_mapping): proof the Banach fixed-point theorem (closes [#553](https://github.com/leanprover-community/mathlib/pull/553))
#### Estimated changes
Modified src/algebra/pi_instances.lean
- \+ *def* prod.prod_semilattice_sup

Added src/contraction_mapping.lean
- \+ *lemma* continuous_prod_snd
- \+ *lemma* dist_bound_of_contraction
- \+ *lemma* dist_inequality_of_contraction
- \+ *theorem* fixed_point_exists_of_contraction
- \+ *lemma* fixed_point_of_iteration_limit
- \+ *theorem* fixed_point_unique_of_contraction
- \+ *lemma* iterated_lipschitz_of_lipschitz
- \+ *def* lipschitz
- \+ *lemma* tendsto_dist_bound_at_top_nhds_0
- \+ *lemma* uniform_continuous_of_lipschitz

Modified src/data/prod.lean
- \+ *lemma* prod.map_def

Modified src/order/filter.lean
- \+ *lemma* filter.prod_at_top_at_top_eq
- \+ *lemma* filter.prod_map_at_top_eq

Modified src/topology/metric_space/basic.lean
- \+ *lemma* cauchy_seq_iff_tendsto_dist_at_top_0
- \+ *lemma* dist_prod_eq_dist_0

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* cauchy_seq_iff_prod_map



## [2019-01-23 11:43:23+01:00](https://github.com/leanprover-community/mathlib/commit/8a0fd0b)
feat(order): add order instances for prod
#### Estimated changes
Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean


Modified src/order/complete_lattice.lean


Modified src/order/lattice.lean




## [2019-01-23 08:09:04+01:00](https://github.com/leanprover-community/mathlib/commit/2ae2cf0)
feat(linear_algebra/multivariate_polynomial): C_mul'
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *theorem* mv_polynomial.C_mul'



## [2019-01-22 17:23:23-05:00](https://github.com/leanprover-community/mathlib/commit/8d44fee)
style(category_theory): adjust precedence of ⥤ ([#616](https://github.com/leanprover-community/mathlib/pull/616))
#### Estimated changes
Modified src/category_theory/functor.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/products.lean
- \+/\- *def* category_theory.evaluation_uncurried
- \+/\- *def* category_theory.functor.prod
- \+/\- *def* category_theory.prod.fst
- \+/\- *def* category_theory.prod.inl
- \+/\- *def* category_theory.prod.inr
- \+/\- *def* category_theory.prod.snd
- \+/\- *def* category_theory.prod.swap
- \+/\- *def* category_theory.prod.symmetry

Modified src/category_theory/types.lean
- \+/\- *def* category_theory.ulift_functor

Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.yoneda_evaluation
- \+/\- *def* category_theory.yoneda_pairing



## [2019-01-22 17:21:55-05:00](https://github.com/leanprover-community/mathlib/commit/c9a0b33)
refactor(category_theory/fully_faithful): move preimage_id ([#615](https://github.com/leanprover-community/mathlib/pull/615))
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *lemma* category_theory.preimage_id

Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.functor.preimage_id



## [2019-01-22 16:49:24+01:00](https://github.com/leanprover-community/mathlib/commit/edfa206)
feat(linear_algebra/dimension): more dimension theorems; rank of a linear map
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.image_preimage_eq_of_subset

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis_empty
- \+ *lemma* is_basis_empty_bot
- \+ *lemma* is_basis_injective
- \+ *lemma* is_basis_span

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_add_le_dim_add_dim
- \+ *lemma* dim_bot
- \+ *lemma* dim_eq_injective
- \+ *lemma* dim_eq_surjective
- \+ *lemma* dim_le_injective
- \+ *lemma* dim_le_of_submodule
- \+ *lemma* dim_le_surjective
- \+ *lemma* dim_map_le
- \+ *lemma* dim_range_le
- \+ *lemma* dim_range_of_surjective
- \+ *lemma* dim_span
- \+ *lemma* dim_submodule_le
- \+ *def* rank
- \+ *lemma* rank_add_le
- \+ *lemma* rank_comp_le1
- \+ *lemma* rank_comp_le2
- \+ *lemma* rank_le_domain
- \+ *lemma* rank_le_range

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.mk_le_mk_of_subset



## [2019-01-22 16:02:10+01:00](https://github.com/leanprover-community/mathlib/commit/6e4c9ba)
feat(linear_algebra/linear_combination): lc lifts vector spaces
#### Estimated changes
Modified src/linear_algebra/linear_combination.lean




## [2019-01-22 16:00:18+01:00](https://github.com/leanprover-community/mathlib/commit/d5a302f)
chore(linear_algebra): rename file lc to linear_combination
#### Estimated changes
Modified src/linear_algebra/basis.lean


Renamed src/linear_algebra/lc.lean to src/linear_algebra/linear_combination.lean


Modified src/ring_theory/noetherian.lean




## [2019-01-22 15:32:49+01:00](https://github.com/leanprover-community/mathlib/commit/7baf093)
feat(data/list,data/multiset,data/finset): add Ico intervals (closes [#496](https://github.com/leanprover-community/mathlib/pull/496))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.Ico.card
- \+ *lemma* finset.Ico.diff_left
- \+ *lemma* finset.Ico.diff_right
- \+ *theorem* finset.Ico.eq_cons
- \+ *theorem* finset.Ico.eq_empty_iff
- \+ *theorem* finset.Ico.eq_empty_of_le
- \+ *lemma* finset.Ico.filter_ge
- \+ *lemma* finset.Ico.filter_ge_of_ge
- \+ *lemma* finset.Ico.filter_ge_of_le_bot
- \+ *lemma* finset.Ico.filter_ge_of_top_le
- \+ *lemma* finset.Ico.filter_lt
- \+ *lemma* finset.Ico.filter_lt_of_ge
- \+ *lemma* finset.Ico.filter_lt_of_le_bot
- \+ *lemma* finset.Ico.filter_lt_of_top_le
- \+ *theorem* finset.Ico.map_add
- \+ *theorem* finset.Ico.mem
- \+ *theorem* finset.Ico.not_mem_top
- \+ *theorem* finset.Ico.pred_singleton
- \+ *theorem* finset.Ico.self_eq_empty
- \+ *theorem* finset.Ico.succ_singleton
- \+ *theorem* finset.Ico.succ_top
- \+ *theorem* finset.Ico.to_finset
- \+ *lemma* finset.Ico.union_consecutive
- \+ *theorem* finset.Ico.val
- \+ *theorem* finset.Ico.zero_bot
- \+ *def* finset.Ico

Modified src/data/list/basic.lean
- \+ *lemma* list.Ico.append_consecutive
- \+ *theorem* list.Ico.chain'_succ
- \+ *theorem* list.Ico.eq_cons
- \+ *theorem* list.Ico.eq_empty_iff
- \+ *theorem* list.Ico.eq_nil_of_le
- \+ *lemma* list.Ico.filter_ge
- \+ *lemma* list.Ico.filter_ge_of_ge
- \+ *lemma* list.Ico.filter_ge_of_le_bot
- \+ *lemma* list.Ico.filter_ge_of_top_le
- \+ *lemma* list.Ico.filter_lt
- \+ *lemma* list.Ico.filter_lt_of_ge
- \+ *lemma* list.Ico.filter_lt_of_le_bot
- \+ *lemma* list.Ico.filter_lt_of_top_le
- \+ *theorem* list.Ico.length
- \+ *theorem* list.Ico.map_add
- \+ *theorem* list.Ico.mem
- \+ *theorem* list.Ico.nodup
- \+ *theorem* list.Ico.not_mem_top
- \+ *theorem* list.Ico.pairwise_lt
- \+ *theorem* list.Ico.pred_singleton
- \+ *theorem* list.Ico.self_empty
- \+ *theorem* list.Ico.succ_singleton
- \+ *theorem* list.Ico.succ_top
- \+ *theorem* list.Ico.zero_bot
- \+ *def* list.Ico
- \+/\- *theorem* list.range'_append

Modified src/data/multiset.lean
- \+ *lemma* multiset.Ico.add_consecutive
- \+ *theorem* multiset.Ico.card
- \+ *theorem* multiset.Ico.eq_cons
- \+ *theorem* multiset.Ico.eq_zero_iff
- \+ *theorem* multiset.Ico.eq_zero_of_le
- \+ *lemma* multiset.Ico.filter_ge
- \+ *lemma* multiset.Ico.filter_ge_of_ge
- \+ *lemma* multiset.Ico.filter_ge_of_le_bot
- \+ *lemma* multiset.Ico.filter_ge_of_top_le
- \+ *lemma* multiset.Ico.filter_lt
- \+ *lemma* multiset.Ico.filter_lt_of_ge
- \+ *lemma* multiset.Ico.filter_lt_of_le_bot
- \+ *lemma* multiset.Ico.filter_lt_of_top_le
- \+ *theorem* multiset.Ico.map_add
- \+ *theorem* multiset.Ico.mem
- \+ *theorem* multiset.Ico.nodup
- \+ *theorem* multiset.Ico.not_mem_top
- \+ *theorem* multiset.Ico.pred_singleton
- \+ *theorem* multiset.Ico.self_eq_zero
- \+ *theorem* multiset.Ico.succ_singleton
- \+ *theorem* multiset.Ico.succ_top
- \+ *theorem* multiset.Ico.zero_bot
- \+ *def* multiset.Ico
- \+ *theorem* multiset.coe_eq_zero



## [2019-01-21 20:02:01-05:00](https://github.com/leanprover-community/mathlib/commit/3dc9935)
fix(tactic/instance_stub): extend the applicability of instance_stub ([#612](https://github.com/leanprover-community/mathlib/pull/612))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-01-21 11:12:50+01:00](https://github.com/leanprover-community/mathlib/commit/bc163a6)
fix(.travis.yml): produce mathlib.txt only from src/
#### Estimated changes
Modified .travis.yml




## [2019-01-20 22:50:48-05:00](https://github.com/leanprover-community/mathlib/commit/c1e594b)
feat(meta, logic, tactic): lean 3.4.2: migrate coinductive_predicates, transfer, relator ([#610](https://github.com/leanprover-community/mathlib/pull/610))
#### Estimated changes
Modified leanpkg.toml


Modified src/data/list/defs.lean


Modified src/logic/relator.lean
- \+ *def* relator.bi_total
- \+ *def* relator.left_total
- \+ *def* relator.left_unique
- \+ *lemma* relator.left_unique_of_rel_eq
- \+ *def* relator.lift_fun
- \+ *lemma* relator.rel_exists_of_left_total
- \+ *lemma* relator.rel_exists_of_total
- \+ *lemma* relator.rel_forall_of_right_total
- \+ *lemma* relator.rel_forall_of_total
- \+ *lemma* relator.rel_imp
- \+ *lemma* relator.rel_not
- \+ *def* relator.right_total
- \+ *def* relator.right_unique

Added src/meta/coinductive_predicates.lean
- \+ *lemma* monotonicity.and
- \+ *lemma* monotonicity.const
- \+ *lemma* monotonicity.exists
- \+ *lemma* monotonicity.false
- \+ *lemma* monotonicity.imp
- \+ *lemma* monotonicity.not
- \+ *lemma* monotonicity.or
- \+ *lemma* monotonicity.pi
- \+ *lemma* monotonicity.true
- \+ *def* name.last_string

Modified src/tactic/alias.lean


Modified src/tactic/explode.lean


Modified src/tactic/mk_iff_of_inductive_prop.lean


Added src/tactic/transfer.lean


Added tests/coinductive.lean
- \+ *lemma* monotonicity.all_list



## [2019-01-20 20:42:15-05:00](https://github.com/leanprover-community/mathlib/commit/2c5bc21)
feat(topology/emetric_space): basic facts for emetric spaces ([#608](https://github.com/leanprover-community/mathlib/pull/608))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \- *lemma* countable_closure_of_compact
- \- *lemma* second_countable_of_separable_metric_space

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_triangle4
- \+ *def* emetric.ball
- \+ *theorem* emetric.ball_disjoint
- \+ *theorem* emetric.ball_mem_nhds
- \+ *theorem* emetric.ball_subset
- \+ *theorem* emetric.ball_subset_ball
- \+ *theorem* emetric.ball_subset_closed_ball
- \- *lemma* emetric.cauchy_iff
- \+ *theorem* emetric.cauchy_seq_iff'
- \+ *theorem* emetric.cauchy_seq_iff
- \+ *def* emetric.closed_ball
- \+ *theorem* emetric.closed_ball_subset_closed_ball
- \+ *lemma* emetric.countable_closure_of_compact
- \+ *theorem* emetric.exists_ball_subset_ball
- \+ *theorem* emetric.is_open_ball
- \+ *theorem* emetric.is_open_iff
- \+ *theorem* emetric.mem_ball'
- \+ *theorem* emetric.mem_ball
- \+ *theorem* emetric.mem_ball_comm
- \+ *theorem* emetric.mem_ball_self
- \+ *theorem* emetric.mem_closed_ball
- \+ *theorem* emetric.mem_closure_iff'
- \+ *theorem* emetric.mem_nhds_iff
- \+ *theorem* emetric.nhds_eq
- \+ *theorem* emetric.pos_of_mem_ball
- \+ *lemma* emetric.second_countable_of_separable
- \+ *theorem* emetric.tendsto_at_top
- \+ *theorem* emetric.tendsto_nhds
- \+ *theorem* emetric.totally_bounded_iff'
- \+ *theorem* emetric.totally_bounded_iff



## [2019-01-19 18:43:24-05:00](https://github.com/leanprover-community/mathlib/commit/fa2e399)
feat(topology/bounded_continuous_function): constructor in normed groups ([#607](https://github.com/leanprover-community/mathlib/pull/607))
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+ *def* bounded_continuous_function.of_normed_group
- \+ *def* bounded_continuous_function.of_normed_group_discrete



## [2019-01-18 19:50:09-05:00](https://github.com/leanprover-community/mathlib/commit/3fcba7d)
feat(logic/basic): add class 'unique' for uniquely inhabited types ([#605](https://github.com/leanprover-community/mathlib/pull/605))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.unique_congr
- \+ *def* equiv.unique_of_equiv
- \+ *def* equiv_of_unique_of_unique
- \+ *def* equiv_punit_of_unique
- \+ *def* unique_unique_equiv

Added src/logic/unique.lean
- \+ *lemma* unique.default_eq
- \+ *lemma* unique.eq_default
- \+ *def* unique.of_surjective



## [2019-01-18 16:30:23-05:00](https://github.com/leanprover-community/mathlib/commit/41b3fdd)
feat(topology/real): bounded iff bounded below above ([#606](https://github.com/leanprover-community/mathlib/pull/606))
#### Estimated changes
Modified src/topology/instances/real.lean
- \+ *lemma* real.bounded_iff_bdd_below_bdd_above



## [2019-01-18 15:36:40+01:00](https://github.com/leanprover-community/mathlib/commit/eb1253f)
feat(measure_theory): add Giry monad
#### Estimated changes
Added src/measure_theory/giry_monad.lean
- \+ *def* measure_theory.measure.bind
- \+ *lemma* measure_theory.measure.bind_apply
- \+ *lemma* measure_theory.measure.bind_bind
- \+ *lemma* measure_theory.measure.bind_dirac
- \+ *lemma* measure_theory.measure.dirac_bind
- \+ *lemma* measure_theory.measure.integral_bind
- \+ *lemma* measure_theory.measure.integral_join
- \+ *def* measure_theory.measure.join
- \+ *lemma* measure_theory.measure.join_apply
- \+ *lemma* measure_theory.measure.measurable_bind'
- \+ *lemma* measure_theory.measure.measurable_coe
- \+ *lemma* measure_theory.measure.measurable_dirac
- \+ *lemma* measure_theory.measure.measurable_integral
- \+ *lemma* measure_theory.measure.measurable_join
- \+ *lemma* measure_theory.measure.measurable_map
- \+ *lemma* measure_theory.measure.measurable_of_measurable_coe

Modified src/measure_theory/integration.lean
- \+ *lemma* le_sequence_of_directed
- \+ *lemma* measure_theory.lintegral_finset_sum
- \+ *theorem* measure_theory.lintegral_supr_directed
- \+ *lemma* measure_theory.lintegral_tsum
- \+ *def* measure_theory.measure.integral
- \+ *lemma* measure_theory.measure.integral_dirac
- \+ *lemma* measure_theory.measure.integral_map
- \+ *lemma* measure_theory.measure.integral_zero
- \+ *def* measure_theory.measure.with_density
- \+ *lemma* measure_theory.measure.with_density_apply
- \+ *lemma* measure_theory.simple_func.approx_comp
- \+ *lemma* measure_theory.simple_func.eapprox_comp
- \+ *lemma* measure_theory.simple_func.integral_map
- \+ *lemma* monotone_sequence_of_directed
- \- *lemma* supr_eq_of_tendsto

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.of_measurable_apply

Modified src/order/basic.lean
- \+ *lemma* monotone_of_monotone_nat

Modified src/topology/algebra/topological_structures.lean
- \+ *lemma* supr_eq_of_tendsto



## [2019-01-18 14:10:04+01:00](https://github.com/leanprover-community/mathlib/commit/739d28a)
refactor(ring_theory/multiplicity): replace padic_val with multiplicity ([#495](https://github.com/leanprover-community/mathlib/pull/495))
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \- *lemma* padic_val.dvd_of_padic_val_pos
- \- *lemma* padic_val.is_greatest
- \- *lemma* padic_val.le_padic_val_of_pow_dvd
- \- *lemma* padic_val.min_le_padic_val_add
- \- *lemma* padic_val.padic_val_eq_zero_of_coprime
- \- *lemma* padic_val.padic_val_eq_zero_of_not_dvd'
- \- *lemma* padic_val.padic_val_eq_zero_of_not_dvd
- \- *lemma* padic_val.padic_val_self
- \- *lemma* padic_val.pow_dvd_iff_le_padic_val
- \- *lemma* padic_val.pow_dvd_of_le_padic_val
- \- *lemma* padic_val.spec
- \- *lemma* padic_val.unique
- \- *def* padic_val
- \+ *lemma* padic_val_rat.finite_int_prime_iff
- \+ *theorem* padic_val_rat.le_padic_val_rat_add_of_le
- \+/\- *theorem* padic_val_rat.min_le_padic_val_rat_add
- \+ *lemma* padic_val_rat.padic_val_rat_le_padic_val_rat_iff
- \+/\- *lemma* padic_val_rat.padic_val_rat_of_int
- \+/\- *lemma* padic_val_rat.padic_val_rat_self
- \+ *lemma* padic_val_rat_def

Modified src/data/padics/padic_numbers.lean


Modified src/data/real/irrational.lean
- \+ *theorem* irr_nrt_of_n_not_dvd_multiplicity
- \- *theorem* irr_nrt_of_n_not_dvd_padic_val
- \+ *theorem* irr_sqrt_of_multiplicity_odd
- \- *theorem* irr_sqrt_of_padic_val_odd



## [2019-01-18 13:28:37+01:00](https://github.com/leanprover-community/mathlib/commit/6144710)
feat(measure_theory): add equivalence of measurable spaces
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.prod_eq
- \+ *lemma* set.range_coe_subtype

Modified src/measure_theory/borel_space.lean
- \+ *def* ennreal.ennreal_equiv_nnreal
- \+ *def* ennreal.ennreal_equiv_sum
- \+ *lemma* ennreal.measurable_coe
- \+ *lemma* ennreal.measurable_mul
- \+ *lemma* ennreal.measurable_of_measurable_nnreal
- \+ *lemma* ennreal.measurable_of_measurable_nnreal_nnreal
- \+ *def* homemorph.to_measurable_equiv
- \+/\- *def* measure_theory.borel
- \+ *lemma* measure_theory.borel_eq_subtype
- \+ *lemma* measure_theory.borel_induced
- \+ *lemma* measure_theory.measurable_finset_sum
- \+/\- *lemma* measure_theory.measurable_of_continuous

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable_inl_image
- \+ *lemma* is_measurable_inr_image
- \+ *lemma* is_measurable_range_inl
- \+ *lemma* is_measurable_range_inr
- \+ *lemma* is_measurable_subtype_image
- \+ *lemma* measurable_equiv.coe_eq
- \+ *def* measurable_equiv.prod_comm
- \+ *def* measurable_equiv.prod_congr
- \+ *def* measurable_equiv.prod_sum_distrib
- \+ *def* measurable_equiv.refl
- \+ *def* measurable_equiv.set.prod
- \+ *def* measurable_equiv.set.range_inl
- \+ *def* measurable_equiv.set.range_inr
- \+ *def* measurable_equiv.set.singleton
- \+ *def* measurable_equiv.set.univ
- \+ *def* measurable_equiv.sum_congr
- \+ *def* measurable_equiv.sum_prod_distrib
- \+ *def* measurable_equiv.sum_prod_sum
- \+ *def* measurable_equiv.symm
- \+ *lemma* measurable_equiv.symm_to_equiv
- \+ *def* measurable_equiv.trans
- \+ *lemma* measurable_equiv.trans_to_equiv
- \+ *lemma* measurable_inl
- \+ *lemma* measurable_inr
- \+ *lemma* measurable_of_measurable_union_cover
- \+ *lemma* measurable_sum
- \+ *lemma* measurable_sum_rec
- \+ *lemma* measurable_unit



## [2019-01-18 13:26:32+01:00](https://github.com/leanprover-community/mathlib/commit/b352d2c)
refactor(topology): topological_space.induced resembles set.image; second_countable_topology on subtypes; simplify filter.map_comap
#### Estimated changes
Modified src/order/filter.lean
- \- *lemma* filter.le_map_comap'
- \- *lemma* filter.le_map_comap
- \+ *lemma* filter.map_comap
- \- *lemma* filter.tendsto_comap''
- \+ *lemma* filter.tendsto_comap'_iff

Modified src/topology/basic.lean
- \+ *lemma* induced_generate_from_eq
- \+ *lemma* topological_space.second_countable_topology_induced

Modified src/topology/continuity.lean
- \+/\- *lemma* embedding.map_nhds_eq
- \+ *theorem* is_open_induced_eq
- \+/\- *lemma* map_nhds_induced_eq

Modified src/topology/instances/ennreal.lean
- \- *lemma* ennreal.coe_image_univ_mem_nhds
- \+ *lemma* ennreal.coe_range_mem_nhds

Modified src/topology/instances/nnreal.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean




## [2019-01-18 13:20:03+01:00](https://github.com/leanprover-community/mathlib/commit/6b6b04a)
feat(order/complete_lattice): add rules for supr/infi under image and under propositions
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.infi_eq_dif
- \+ *lemma* lattice.infi_eq_if
- \+ *lemma* lattice.infi_image
- \+ *lemma* lattice.supr_eq_dif
- \+ *lemma* lattice.supr_eq_if
- \+ *lemma* lattice.supr_image



## [2019-01-18 11:13:09+01:00](https://github.com/leanprover-community/mathlib/commit/f0f06ca)
refactor(*): analysis reorganization ([#598](https://github.com/leanprover-community/mathlib/pull/598))
* split `measure_theory` and `topology` out of analysis
* add `instances` sub directories for theories around type class instances
#### Estimated changes
Modified docs/theories/topological_spaces.md


Modified src/analysis/exponential.lean


Renamed src/analysis/normed_space.lean to src/analysis/normed_space/basic.lean


Renamed src/analysis/bounded_linear_maps.lean to src/analysis/normed_space/bounded_linear_maps.lean


Renamed src/analysis/limits.lean to src/analysis/specific_limits.lean


Modified src/category_theory/examples/measurable_space.lean


Modified src/category_theory/examples/topological_spaces.lean


Modified src/data/analysis/topology.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/real/cau_seq_filter.lean


Renamed src/analysis/measure_theory/borel_space.lean to src/measure_theory/borel_space.lean


Renamed src/analysis/measure_theory/integration.lean to src/measure_theory/integration.lean


Renamed src/analysis/measure_theory/lebesgue_measure.lean to src/measure_theory/lebesgue_measure.lean


Renamed src/analysis/measure_theory/measurable_space.lean to src/measure_theory/measurable_space.lean


Renamed src/analysis/measure_theory/measure_space.lean to src/measure_theory/measure_space.lean


Renamed src/analysis/measure_theory/outer_measure.lean to src/measure_theory/outer_measure.lean


Renamed src/analysis/probability_mass_function.lean to src/measure_theory/probability_mass_function.lean


Renamed src/analysis/topology/topological_groups.lean to src/topology/algebra/group.lean


Renamed src/analysis/topology/infinite_sum.lean to src/topology/algebra/infinite_sum.lean


Renamed src/analysis/topology/quotient_topological_structures.lean to src/topology/algebra/quotient.lean


Renamed src/analysis/topology/topological_structures.lean to src/topology/algebra/topological_structures.lean


Renamed src/analysis/topology/topological_space.lean to src/topology/basic.lean


Renamed src/analysis/topology/bounded_continuous_function.lean to src/topology/bounded_continuous_function.lean


Renamed src/analysis/topology/continuous_map.lean to src/topology/compact_open.lean


Renamed src/analysis/topology/continuity.lean to src/topology/continuity.lean


Renamed src/analysis/complex.lean to src/topology/instances/complex.lean


Renamed src/analysis/ennreal.lean to src/topology/instances/ennreal.lean


Renamed src/analysis/nnreal.lean to src/topology/instances/nnreal.lean


Renamed src/analysis/polynomial.lean to src/topology/instances/polynomial.lean


Renamed src/analysis/real.lean to src/topology/instances/real.lean


Renamed src/analysis/metric_space.lean to src/topology/metric_space/basic.lean


Renamed src/analysis/emetric_space.lean to src/topology/metric_space/emetric_space.lean


Renamed src/analysis/topology/stone_cech.lean to src/topology/stone_cech.lean


Renamed src/analysis/topology/uniform_space.lean to src/topology/uniform_space/basic.lean


Renamed src/analysis/topology/completion.lean to src/topology/uniform_space/completion.lean




## [2019-01-17 19:21:33-05:00](https://github.com/leanprover-community/mathlib/commit/c1f162c)
fix(tactic/linarith): don't reject expressions with division by variables ([#604](https://github.com/leanprover-community/mathlib/pull/604))
norm_hyp_aux should have succeeded (without changing the type of h') in the case where lhs contains 1/x. But mk_single_comp_zero_pf is too clever when given the coeff 1. norm_hyp_aux will still do unnecessary work when it finds e.g. 1/(2*x), but shouldn't fail.
#### Estimated changes
Modified src/tactic/linarith.lean


Modified tests/linarith.lean




## [2019-01-17 14:37:38-05:00](https://github.com/leanprover-community/mathlib/commit/ae610a0)
feat(ring_theory/adjoin_root): adjoin roots to polynomials ([#603](https://github.com/leanprover-community/mathlib/pull/603))
#### Estimated changes
Added src/ring_theory/adjoin_root.lean
- \+ *def* adjoin_root.adjoin_root
- \+ *lemma* adjoin_root.coe_injective
- \+ *lemma* adjoin_root.eval₂_root
- \+ *lemma* adjoin_root.is_root_root
- \+ *def* adjoin_root.lift
- \+ *lemma* adjoin_root.lift_mk
- \+ *lemma* adjoin_root.lift_of
- \+ *lemma* adjoin_root.lift_root
- \+ *def* adjoin_root.mk
- \+ *lemma* adjoin_root.mk_self
- \+ *lemma* adjoin_root.mul_div_root_cancel
- \+ *def* adjoin_root.of
- \+ *def* adjoin_root.root



## [2019-01-16 08:50:38-05:00](https://github.com/leanprover-community/mathlib/commit/5c37507)
doc(elan.md): fix msys2 setup ([#594](https://github.com/leanprover-community/mathlib/pull/594)) [ci-skip]
For me, adding the suggested line to .profile did not change my path, even after restarting the terminal.
Moreover, elan is installed in $USERPROFILE/.elan/bin, not in $HOME/.elan/bin.
Adding $USERPROFILE/.elan/bin to the path did not work for me, so I give the full path.
#### Estimated changes
Modified docs/elan.md




## [2019-01-16 08:33:19-05:00](https://github.com/leanprover-community/mathlib/commit/5dd9998)
doc(docs/tactics): document `convert` ([#601](https://github.com/leanprover-community/mathlib/pull/601)) [ci-skip]
#### Estimated changes
Modified docs/tactics.md




## [2019-01-16 08:14:44-05:00](https://github.com/leanprover-community/mathlib/commit/ab5849e)
style(category_theory/opposites): increase binding power of ᵒᵖ ([#600](https://github.com/leanprover-community/mathlib/pull/600))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.functor.cones

Modified src/category_theory/opposites.lean


Modified src/category_theory/yoneda.lean




## [2019-01-15 17:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/024da40)
refactor(logic/schroeder_bernstein): move to set_theory/ ([#599](https://github.com/leanprover-community/mathlib/pull/599))
#### Estimated changes
Modified src/set_theory/cardinal.lean


Renamed src/logic/schroeder_bernstein.lean to src/set_theory/schroeder_bernstein.lean




## [2019-01-15 12:05:23-05:00](https://github.com/leanprover-community/mathlib/commit/d4f80f6)
refactor(*): Try again moving everything to src ([#597](https://github.com/leanprover-community/mathlib/pull/597))
#### Estimated changes
Renamed category_theory/limits/over.lean to src/category_theory/limits/over.lean


Renamed group_theory/sylow.lean to src/group_theory/sylow.lean


Renamed ring_theory/euclidean_domain.lean to src/ring_theory/euclidean_domain.lean




## [2019-01-15 10:51:04-05:00](https://github.com/leanprover-community/mathlib/commit/78f1949)
refactor(*): move everything into `src` ([#583](https://github.com/leanprover-community/mathlib/pull/583))
#### Estimated changes
Modified leanpkg.toml


Renamed algebra/archimedean.lean to src/algebra/archimedean.lean


Renamed algebra/big_operators.lean to src/algebra/big_operators.lean


Renamed algebra/char_p.lean to src/algebra/char_p.lean


Renamed algebra/char_zero.lean to src/algebra/char_zero.lean


Renamed algebra/default.lean to src/algebra/default.lean


Renamed algebra/euclidean_domain.lean to src/algebra/euclidean_domain.lean


Renamed algebra/field.lean to src/algebra/field.lean


Renamed algebra/field_power.lean to src/algebra/field_power.lean


Renamed algebra/gcd_domain.lean to src/algebra/gcd_domain.lean


Renamed algebra/group.lean to src/algebra/group.lean


Renamed algebra/group_power.lean to src/algebra/group_power.lean


Renamed algebra/module.lean to src/algebra/module.lean


Renamed algebra/order.lean to src/algebra/order.lean


Renamed algebra/order_functions.lean to src/algebra/order_functions.lean


Renamed algebra/ordered_field.lean to src/algebra/ordered_field.lean


Renamed algebra/ordered_group.lean to src/algebra/ordered_group.lean


Renamed algebra/ordered_ring.lean to src/algebra/ordered_ring.lean


Renamed algebra/pi_instances.lean to src/algebra/pi_instances.lean


Renamed algebra/ring.lean to src/algebra/ring.lean


Renamed analysis/bounded_linear_maps.lean to src/analysis/bounded_linear_maps.lean


Renamed analysis/complex.lean to src/analysis/complex.lean


Renamed analysis/emetric_space.lean to src/analysis/emetric_space.lean


Renamed analysis/ennreal.lean to src/analysis/ennreal.lean


Renamed analysis/exponential.lean to src/analysis/exponential.lean


Renamed analysis/limits.lean to src/analysis/limits.lean


Renamed analysis/measure_theory/borel_space.lean to src/analysis/measure_theory/borel_space.lean


Renamed analysis/measure_theory/integration.lean to src/analysis/measure_theory/integration.lean


Renamed analysis/measure_theory/lebesgue_measure.lean to src/analysis/measure_theory/lebesgue_measure.lean


Renamed analysis/measure_theory/measurable_space.lean to src/analysis/measure_theory/measurable_space.lean


Renamed analysis/measure_theory/measure_space.lean to src/analysis/measure_theory/measure_space.lean


Renamed analysis/measure_theory/outer_measure.lean to src/analysis/measure_theory/outer_measure.lean


Renamed analysis/metric_space.lean to src/analysis/metric_space.lean


Renamed analysis/nnreal.lean to src/analysis/nnreal.lean


Renamed analysis/normed_space.lean to src/analysis/normed_space.lean


Renamed analysis/polynomial.lean to src/analysis/polynomial.lean


Renamed analysis/probability_mass_function.lean to src/analysis/probability_mass_function.lean


Renamed analysis/real.lean to src/analysis/real.lean


Renamed analysis/topology/bounded_continuous_function.lean to src/analysis/topology/bounded_continuous_function.lean


Renamed analysis/topology/completion.lean to src/analysis/topology/completion.lean


Renamed analysis/topology/continuity.lean to src/analysis/topology/continuity.lean


Renamed analysis/topology/continuous_map.lean to src/analysis/topology/continuous_map.lean


Renamed analysis/topology/infinite_sum.lean to src/analysis/topology/infinite_sum.lean


Renamed analysis/topology/quotient_topological_structures.lean to src/analysis/topology/quotient_topological_structures.lean


Renamed analysis/topology/stone_cech.lean to src/analysis/topology/stone_cech.lean


Renamed analysis/topology/topological_groups.lean to src/analysis/topology/topological_groups.lean


Renamed analysis/topology/topological_space.lean to src/analysis/topology/topological_space.lean


Renamed analysis/topology/topological_structures.lean to src/analysis/topology/topological_structures.lean


Renamed analysis/topology/uniform_space.lean to src/analysis/topology/uniform_space.lean


Renamed category/applicative.lean to src/category/applicative.lean


Renamed category/basic.lean to src/category/basic.lean


Renamed category/bifunctor.lean to src/category/bifunctor.lean


Renamed category/bitraversable/basic.lean to src/category/bitraversable/basic.lean


Renamed category/bitraversable/instances.lean to src/category/bitraversable/instances.lean


Renamed category/bitraversable/lemmas.lean to src/category/bitraversable/lemmas.lean


Renamed category/functor.lean to src/category/functor.lean


Renamed category/traversable/basic.lean to src/category/traversable/basic.lean


Renamed category/traversable/default.lean to src/category/traversable/default.lean


Renamed category/traversable/derive.lean to src/category/traversable/derive.lean


Renamed category/traversable/equiv.lean to src/category/traversable/equiv.lean


Renamed category/traversable/instances.lean to src/category/traversable/instances.lean


Renamed category/traversable/lemmas.lean to src/category/traversable/lemmas.lean


Renamed category_theory/category.lean to src/category_theory/category.lean


Renamed category_theory/comma.lean to src/category_theory/comma.lean


Renamed category_theory/const.lean to src/category_theory/const.lean


Renamed category_theory/discrete_category.lean to src/category_theory/discrete_category.lean


Renamed category_theory/eq_to_hom.lean to src/category_theory/eq_to_hom.lean


Renamed category_theory/equivalence.lean to src/category_theory/equivalence.lean


Renamed category_theory/examples/measurable_space.lean to src/category_theory/examples/measurable_space.lean


Renamed category_theory/examples/monoids.lean to src/category_theory/examples/monoids.lean


Renamed category_theory/examples/rings.lean to src/category_theory/examples/rings.lean


Renamed category_theory/examples/topological_spaces.lean to src/category_theory/examples/topological_spaces.lean


Renamed category_theory/full_subcategory.lean to src/category_theory/full_subcategory.lean


Renamed category_theory/fully_faithful.lean to src/category_theory/fully_faithful.lean


Renamed category_theory/functor.lean to src/category_theory/functor.lean


Renamed category_theory/functor_category.lean to src/category_theory/functor_category.lean


Renamed category_theory/groupoid.lean to src/category_theory/groupoid.lean


Renamed category_theory/isomorphism.lean to src/category_theory/isomorphism.lean


Renamed category_theory/limits/cones.lean to src/category_theory/limits/cones.lean


Renamed category_theory/limits/functor_category.lean to src/category_theory/limits/functor_category.lean


Renamed category_theory/limits/limits.lean to src/category_theory/limits/limits.lean


Renamed category_theory/limits/preserves.lean to src/category_theory/limits/preserves.lean


Renamed category_theory/limits/types.lean to src/category_theory/limits/types.lean


Renamed category_theory/natural_isomorphism.lean to src/category_theory/natural_isomorphism.lean


Renamed category_theory/natural_transformation.lean to src/category_theory/natural_transformation.lean


Renamed category_theory/opposites.lean to src/category_theory/opposites.lean


Renamed category_theory/pempty.lean to src/category_theory/pempty.lean


Renamed category_theory/products.lean to src/category_theory/products.lean


Renamed category_theory/punit.lean to src/category_theory/punit.lean


Renamed category_theory/types.lean to src/category_theory/types.lean


Renamed category_theory/whiskering.lean to src/category_theory/whiskering.lean


Renamed category_theory/yoneda.lean to src/category_theory/yoneda.lean


Renamed computability/halting.lean to src/computability/halting.lean


Renamed computability/partrec.lean to src/computability/partrec.lean


Renamed computability/partrec_code.lean to src/computability/partrec_code.lean


Renamed computability/primrec.lean to src/computability/primrec.lean


Renamed computability/turing_machine.lean to src/computability/turing_machine.lean


Renamed data/analysis/filter.lean to src/data/analysis/filter.lean


Renamed data/analysis/topology.lean to src/data/analysis/topology.lean


Renamed data/array/lemmas.lean to src/data/array/lemmas.lean


Renamed data/bool.lean to src/data/bool.lean


Renamed data/buffer/basic.lean to src/data/buffer/basic.lean


Renamed data/char.lean to src/data/char.lean


Renamed data/complex/basic.lean to src/data/complex/basic.lean


Renamed data/complex/exponential.lean to src/data/complex/exponential.lean


Renamed data/dfinsupp.lean to src/data/dfinsupp.lean


Renamed data/dlist/basic.lean to src/data/dlist/basic.lean


Renamed data/dlist/instances.lean to src/data/dlist/instances.lean


Renamed data/equiv/algebra.lean to src/data/equiv/algebra.lean


Renamed data/equiv/basic.lean to src/data/equiv/basic.lean


Renamed data/equiv/denumerable.lean to src/data/equiv/denumerable.lean


Renamed data/equiv/encodable.lean to src/data/equiv/encodable.lean


Renamed data/equiv/fin.lean to src/data/equiv/fin.lean


Renamed data/equiv/list.lean to src/data/equiv/list.lean


Renamed data/equiv/nat.lean to src/data/equiv/nat.lean


Renamed data/erased.lean to src/data/erased.lean


Renamed data/fin.lean to src/data/fin.lean


Renamed data/finmap.lean to src/data/finmap.lean


Renamed data/finset.lean to src/data/finset.lean


Renamed data/finsupp.lean to src/data/finsupp.lean


Renamed data/fintype.lean to src/data/fintype.lean


Renamed data/fp/basic.lean to src/data/fp/basic.lean


Renamed data/hash_map.lean to src/data/hash_map.lean


Renamed data/holor.lean to src/data/holor.lean


Renamed data/int/basic.lean to src/data/int/basic.lean


Renamed data/int/gcd.lean to src/data/int/gcd.lean


Renamed data/int/modeq.lean to src/data/int/modeq.lean


Renamed data/int/sqrt.lean to src/data/int/sqrt.lean


Renamed data/lazy_list2.lean to src/data/lazy_list2.lean


Renamed data/list/alist.lean to src/data/list/alist.lean


Renamed data/list/basic.lean to src/data/list/basic.lean


Renamed data/list/default.lean to src/data/list/default.lean


Renamed data/list/defs.lean to src/data/list/defs.lean


Renamed data/list/perm.lean to src/data/list/perm.lean


Renamed data/list/sigma.lean to src/data/list/sigma.lean


Renamed data/list/sort.lean to src/data/list/sort.lean


Renamed data/multiset.lean to src/data/multiset.lean


Renamed data/nat/basic.lean to src/data/nat/basic.lean


Renamed data/nat/cast.lean to src/data/nat/cast.lean


Renamed data/nat/choose.lean to src/data/nat/choose.lean


Renamed data/nat/dist.lean to src/data/nat/dist.lean


Renamed data/nat/enat.lean to src/data/nat/enat.lean


Renamed data/nat/gcd.lean to src/data/nat/gcd.lean


Renamed data/nat/modeq.lean to src/data/nat/modeq.lean


Renamed data/nat/pairing.lean to src/data/nat/pairing.lean


Renamed data/nat/prime.lean to src/data/nat/prime.lean


Renamed data/nat/sqrt.lean to src/data/nat/sqrt.lean


Renamed data/nat/totient.lean to src/data/nat/totient.lean


Renamed data/num/basic.lean to src/data/num/basic.lean


Renamed data/num/bitwise.lean to src/data/num/bitwise.lean


Renamed data/num/lemmas.lean to src/data/num/lemmas.lean


Renamed data/option/basic.lean to src/data/option/basic.lean


Renamed data/option/defs.lean to src/data/option/defs.lean


Renamed data/padics/default.lean to src/data/padics/default.lean


Renamed data/padics/hensel.lean to src/data/padics/hensel.lean


Renamed data/padics/padic_integers.lean to src/data/padics/padic_integers.lean


Renamed data/padics/padic_norm.lean to src/data/padics/padic_norm.lean


Renamed data/padics/padic_numbers.lean to src/data/padics/padic_numbers.lean


Renamed data/pfun.lean to src/data/pfun.lean


Renamed data/pnat.lean to src/data/pnat.lean


Renamed data/polynomial.lean to src/data/polynomial.lean


Renamed data/prod.lean to src/data/prod.lean


Renamed data/quot.lean to src/data/quot.lean


Renamed data/rat.lean to src/data/rat.lean


Renamed data/real/basic.lean to src/data/real/basic.lean


Renamed data/real/cau_seq.lean to src/data/real/cau_seq.lean


Renamed data/real/cau_seq_completion.lean to src/data/real/cau_seq_completion.lean


Renamed data/real/cau_seq_filter.lean to src/data/real/cau_seq_filter.lean


Renamed data/real/ennreal.lean to src/data/real/ennreal.lean


Renamed data/real/irrational.lean to src/data/real/irrational.lean


Renamed data/real/nnreal.lean to src/data/real/nnreal.lean


Renamed data/semiquot.lean to src/data/semiquot.lean


Renamed data/seq/computation.lean to src/data/seq/computation.lean


Renamed data/seq/parallel.lean to src/data/seq/parallel.lean


Renamed data/seq/seq.lean to src/data/seq/seq.lean


Renamed data/seq/wseq.lean to src/data/seq/wseq.lean


Renamed data/set/basic.lean to src/data/set/basic.lean


Renamed data/set/countable.lean to src/data/set/countable.lean


Renamed data/set/default.lean to src/data/set/default.lean


Renamed data/set/disjointed.lean to src/data/set/disjointed.lean


Renamed data/set/enumerate.lean to src/data/set/enumerate.lean


Renamed data/set/finite.lean to src/data/set/finite.lean


Renamed data/set/function.lean to src/data/set/function.lean


Renamed data/set/intervals.lean to src/data/set/intervals.lean


Renamed data/set/lattice.lean to src/data/set/lattice.lean


Renamed data/sigma/basic.lean to src/data/sigma/basic.lean


Renamed data/sigma/default.lean to src/data/sigma/default.lean


Renamed data/stream/basic.lean to src/data/stream/basic.lean


Renamed data/string.lean to src/data/string.lean


Renamed data/subtype.lean to src/data/subtype.lean


Renamed data/sum.lean to src/data/sum.lean


Renamed data/ulift.lean to src/data/ulift.lean


Renamed data/vector2.lean to src/data/vector2.lean


Renamed data/zmod/basic.lean to src/data/zmod/basic.lean


Renamed data/zmod/quadratic_reciprocity.lean to src/data/zmod/quadratic_reciprocity.lean


Renamed field_theory/finite.lean to src/field_theory/finite.lean


Renamed field_theory/perfect_closure.lean to src/field_theory/perfect_closure.lean


Renamed field_theory/subfield.lean to src/field_theory/subfield.lean


Renamed group_theory/abelianization.lean to src/group_theory/abelianization.lean


Renamed group_theory/coset.lean to src/group_theory/coset.lean


Renamed group_theory/eckmann_hilton.lean to src/group_theory/eckmann_hilton.lean


Renamed group_theory/free_abelian_group.lean to src/group_theory/free_abelian_group.lean


Renamed group_theory/free_group.lean to src/group_theory/free_group.lean


Renamed group_theory/group_action.lean to src/group_theory/group_action.lean


Renamed group_theory/order_of_element.lean to src/group_theory/order_of_element.lean


Renamed group_theory/perm.lean to src/group_theory/perm.lean


Renamed group_theory/quotient_group.lean to src/group_theory/quotient_group.lean


Renamed group_theory/subgroup.lean to src/group_theory/subgroup.lean


Renamed group_theory/submonoid.lean to src/group_theory/submonoid.lean


Renamed linear_algebra/basic.lean to src/linear_algebra/basic.lean


Renamed linear_algebra/basis.lean to src/linear_algebra/basis.lean


Renamed linear_algebra/default.lean to src/linear_algebra/default.lean


Renamed linear_algebra/dimension.lean to src/linear_algebra/dimension.lean


Renamed linear_algebra/direct_sum_module.lean to src/linear_algebra/direct_sum_module.lean


Renamed linear_algebra/lc.lean to src/linear_algebra/lc.lean


Renamed linear_algebra/multivariate_polynomial.lean to src/linear_algebra/multivariate_polynomial.lean


Renamed linear_algebra/tensor_product.lean to src/linear_algebra/tensor_product.lean


Renamed logic/basic.lean to src/logic/basic.lean


Renamed logic/embedding.lean to src/logic/embedding.lean


Renamed logic/function.lean to src/logic/function.lean


Renamed logic/relation.lean to src/logic/relation.lean


Renamed logic/relator.lean to src/logic/relator.lean


Renamed logic/schroeder_bernstein.lean to src/logic/schroeder_bernstein.lean


Renamed meta/rb_map.lean to src/meta/rb_map.lean


Renamed number_theory/dioph.lean to src/number_theory/dioph.lean


Renamed number_theory/pell.lean to src/number_theory/pell.lean


Renamed order/basic.lean to src/order/basic.lean


Renamed order/boolean_algebra.lean to src/order/boolean_algebra.lean


Renamed order/bounded_lattice.lean to src/order/bounded_lattice.lean


Renamed order/bounds.lean to src/order/bounds.lean


Renamed order/complete_boolean_algebra.lean to src/order/complete_boolean_algebra.lean


Renamed order/complete_lattice.lean to src/order/complete_lattice.lean


Renamed order/conditionally_complete_lattice.lean to src/order/conditionally_complete_lattice.lean


Renamed order/default.lean to src/order/default.lean


Renamed order/filter.lean to src/order/filter.lean


Renamed order/fixed_points.lean to src/order/fixed_points.lean


Renamed order/galois_connection.lean to src/order/galois_connection.lean


Renamed order/lattice.lean to src/order/lattice.lean


Renamed order/liminf_limsup.lean to src/order/liminf_limsup.lean


Renamed order/order_iso.lean to src/order/order_iso.lean


Renamed order/zorn.lean to src/order/zorn.lean


Renamed pending/default.lean to src/pending/default.lean


Renamed ring_theory/associated.lean to src/ring_theory/associated.lean


Renamed ring_theory/determinant.lean to src/ring_theory/determinant.lean


Renamed ring_theory/ideal_operations.lean to src/ring_theory/ideal_operations.lean


Renamed ring_theory/ideals.lean to src/ring_theory/ideals.lean


Renamed ring_theory/localization.lean to src/ring_theory/localization.lean


Renamed ring_theory/matrix.lean to src/ring_theory/matrix.lean


Renamed ring_theory/multiplicity.lean to src/ring_theory/multiplicity.lean


Renamed ring_theory/noetherian.lean to src/ring_theory/noetherian.lean


Renamed ring_theory/principal_ideal_domain.lean to src/ring_theory/principal_ideal_domain.lean


Renamed ring_theory/subring.lean to src/ring_theory/subring.lean


Renamed ring_theory/unique_factorization_domain.lean to src/ring_theory/unique_factorization_domain.lean


Renamed set_theory/cardinal.lean to src/set_theory/cardinal.lean


Renamed set_theory/cofinality.lean to src/set_theory/cofinality.lean


Renamed set_theory/lists.lean to src/set_theory/lists.lean


Renamed set_theory/ordinal.lean to src/set_theory/ordinal.lean


Renamed set_theory/ordinal_notation.lean to src/set_theory/ordinal_notation.lean


Renamed set_theory/zfc.lean to src/set_theory/zfc.lean


Renamed tactic/abel.lean to src/tactic/abel.lean


Renamed tactic/algebra.lean to src/tactic/algebra.lean


Renamed tactic/alias.lean to src/tactic/alias.lean


Renamed tactic/auto_cases.lean to src/tactic/auto_cases.lean


Renamed tactic/basic.lean to src/tactic/basic.lean


Renamed tactic/cache.lean to src/tactic/cache.lean


Renamed tactic/chain.lean to src/tactic/chain.lean


Renamed tactic/converter/binders.lean to src/tactic/converter/binders.lean


Renamed tactic/converter/interactive.lean to src/tactic/converter/interactive.lean


Renamed tactic/converter/old_conv.lean to src/tactic/converter/old_conv.lean


Renamed tactic/default.lean to src/tactic/default.lean


Renamed tactic/elide.lean to src/tactic/elide.lean


Renamed tactic/explode.lean to src/tactic/explode.lean


Renamed tactic/ext.lean to src/tactic/ext.lean


Renamed tactic/fin_cases.lean to src/tactic/fin_cases.lean


Renamed tactic/find.lean to src/tactic/find.lean


Renamed tactic/finish.lean to src/tactic/finish.lean


Renamed tactic/generalize_proofs.lean to src/tactic/generalize_proofs.lean


Renamed tactic/interactive.lean to src/tactic/interactive.lean


Renamed tactic/linarith.lean to src/tactic/linarith.lean


Renamed tactic/mk_iff_of_inductive_prop.lean to src/tactic/mk_iff_of_inductive_prop.lean


Renamed tactic/monotonicity/basic.lean to src/tactic/monotonicity/basic.lean


Renamed tactic/monotonicity/default.lean to src/tactic/monotonicity/default.lean


Renamed tactic/monotonicity/interactive.lean to src/tactic/monotonicity/interactive.lean


Renamed tactic/monotonicity/lemmas.lean to src/tactic/monotonicity/lemmas.lean


Renamed tactic/norm_num.lean to src/tactic/norm_num.lean


Renamed tactic/pi_instances.lean to src/tactic/pi_instances.lean


Renamed tactic/rcases.lean to src/tactic/rcases.lean


Renamed tactic/replacer.lean to src/tactic/replacer.lean


Renamed tactic/restate_axiom.lean to src/tactic/restate_axiom.lean


Renamed tactic/rewrite.lean to src/tactic/rewrite.lean


Renamed tactic/ring.lean to src/tactic/ring.lean


Renamed tactic/ring2.lean to src/tactic/ring2.lean


Renamed tactic/scc.lean to src/tactic/scc.lean


Renamed tactic/simpa.lean to src/tactic/simpa.lean


Renamed tactic/slice.lean to src/tactic/slice.lean


Renamed tactic/split_ifs.lean to src/tactic/split_ifs.lean


Renamed tactic/squeeze.lean to src/tactic/squeeze.lean


Renamed tactic/subtype_instance.lean to src/tactic/subtype_instance.lean


Renamed tactic/tauto.lean to src/tactic/tauto.lean


Renamed tactic/tfae.lean to src/tactic/tfae.lean


Renamed tactic/tidy.lean to src/tactic/tidy.lean


Renamed tactic/where.lean to src/tactic/where.lean


Renamed tactic/wlog.lean to src/tactic/wlog.lean




## [2019-01-15 11:15:57+01:00](https://github.com/leanprover-community/mathlib/commit/0c71016)
feat(logic/basic): nonempty.map
#### Estimated changes
Modified logic/basic.lean
- \+ *lemma* nonempty.map



## [2019-01-14 14:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/667dcf3)
feat(group_theory/sylow): first sylow theorem (closes [#591](https://github.com/leanprover-community/mathlib/pull/591))
#### Estimated changes
Modified group_theory/group_action.lean
- \+ *lemma* is_group_action.comp_hom
- \+ *def* is_group_action.mul_left_cosets
- \+ *lemma* is_monoid_action.comp_hom

Modified group_theory/sylow.lean
- \+ *lemma* sylow.exists_subgroup_card_pow_prime
- \+ *lemma* sylow.fixed_points_mul_left_cosets_equiv_quotient
- \+ *lemma* sylow.mem_fixed_points_mul_left_cosets_iff_mem_normalizer



## [2019-01-14 14:05:58+01:00](https://github.com/leanprover-community/mathlib/commit/f63fb54)
doc(tactic/simpa): rewrite simpa doc
#### Estimated changes
Modified docs/tactics.md


Modified tactic/simpa.lean




## [2019-01-14 13:34:42+01:00](https://github.com/leanprover-community/mathlib/commit/49c059a)
refactor(analysis): add metric namespace
combines changes from @sgouezel, @PatrickMassot, and @digama0
#### Estimated changes
Modified analysis/bounded_linear_maps.lean


Modified analysis/complex.lean


Modified analysis/emetric_space.lean
- \+ *theorem* edist_eq_zero
- \+ *theorem* edist_mem_uniformity
- \+ *theorem* edist_triangle_left
- \+ *theorem* edist_triangle_right
- \+ *lemma* emetric.cauchy_iff
- \+ *theorem* emetric.uniform_continuous_iff
- \+ *theorem* emetric.uniform_embedding_iff
- \- *lemma* emetric_space.cauchy_of_emetric
- \- *theorem* emetric_space.edist_eq_zero
- \- *theorem* emetric_space.edist_mem_uniformity
- \- *theorem* emetric_space.edist_triangle_left
- \- *theorem* emetric_space.edist_triangle_right
- \- *theorem* emetric_space.eq_of_forall_edist_le
- \+/\- *def* emetric_space.induced
- \- *theorem* emetric_space.mem_uniformity_edist
- \+/\- *def* emetric_space.replace_uniformity
- \- *theorem* emetric_space.subtype.edist_eq
- \- *theorem* emetric_space.uniform_continuous_of_emetric
- \- *theorem* emetric_space.uniform_embedding_of_emetric
- \- *def* emetric_space.uniform_space_of_edist
- \- *theorem* emetric_space.uniformity_edist''
- \- *theorem* emetric_space.uniformity_edist'
- \- *theorem* emetric_space.zero_eq_edist
- \+ *theorem* eq_of_forall_edist_le
- \+ *theorem* mem_uniformity_edist
- \+ *theorem* subtype.edist_eq
- \+ *def* uniform_space_of_edist
- \+ *theorem* uniformity_edist''
- \+ *theorem* uniformity_edist'
- \+ *theorem* zero_eq_edist

Modified analysis/ennreal.lean


Modified analysis/exponential.lean


Modified analysis/limits.lean


Modified analysis/metric_space.lean
- \- *def* ball
- \- *theorem* ball_disjoint
- \- *theorem* ball_disjoint_same
- \- *theorem* ball_eq_empty_iff_nonpos
- \- *theorem* ball_half_subset
- \- *theorem* ball_mem_nhds
- \- *theorem* ball_subset
- \- *theorem* ball_subset_ball
- \- *theorem* ball_subset_closed_ball
- \- *lemma* bounded.subset
- \- *def* bounded
- \- *lemma* bounded_bUnion
- \- *lemma* bounded_ball
- \- *lemma* bounded_closed_ball
- \- *lemma* bounded_empty
- \- *lemma* bounded_iff_mem_bounded
- \- *lemma* bounded_iff_subset_ball
- \- *lemma* bounded_of_compact
- \- *lemma* bounded_of_compact_space
- \- *lemma* bounded_of_finite
- \- *lemma* bounded_range_iff
- \- *lemma* bounded_singleton
- \- *lemma* bounded_union
- \- *lemma* cauchy_of_metric
- \- *theorem* cauchy_seq_metric'
- \- *theorem* cauchy_seq_metric
- \- *def* closed_ball
- \- *theorem* closed_ball_subset_closed_ball
- \- *lemma* compact_iff_closed_bounded
- \- *theorem* continuous_of_metric
- \- *theorem* continuous_topo_metric
- \- *theorem* dist_mem_uniformity
- \- *theorem* exists_ball_subset_ball
- \- *theorem* exists_delta_of_continuous
- \- *theorem* is_closed_ball
- \- *theorem* is_open_ball
- \- *theorem* is_open_metric
- \- *theorem* mem_ball'
- \- *theorem* mem_ball
- \- *theorem* mem_ball_comm
- \- *theorem* mem_ball_self
- \- *theorem* mem_closed_ball
- \- *theorem* mem_closure_iff'
- \- *theorem* mem_nhds_iff_metric
- \- *theorem* mem_of_closed'
- \- *theorem* mem_uniformity_dist
- \- *lemma* mem_uniformity_dist_edist
- \+ *def* metric.ball
- \+ *theorem* metric.ball_disjoint
- \+ *theorem* metric.ball_disjoint_same
- \+ *theorem* metric.ball_eq_empty_iff_nonpos
- \+ *theorem* metric.ball_half_subset
- \+ *theorem* metric.ball_mem_nhds
- \+ *theorem* metric.ball_subset
- \+ *theorem* metric.ball_subset_ball
- \+ *theorem* metric.ball_subset_closed_ball
- \+ *lemma* metric.bounded.subset
- \+ *def* metric.bounded
- \+ *lemma* metric.bounded_bUnion
- \+ *lemma* metric.bounded_ball
- \+ *lemma* metric.bounded_closed_ball
- \+ *lemma* metric.bounded_empty
- \+ *lemma* metric.bounded_iff_mem_bounded
- \+ *lemma* metric.bounded_iff_subset_ball
- \+ *lemma* metric.bounded_of_compact
- \+ *lemma* metric.bounded_of_compact_space
- \+ *lemma* metric.bounded_of_finite
- \+ *lemma* metric.bounded_range_iff
- \+ *lemma* metric.bounded_singleton
- \+ *lemma* metric.bounded_union
- \+ *theorem* metric.cauchy_seq_iff'
- \+ *theorem* metric.cauchy_seq_iff
- \+ *def* metric.closed_ball
- \+ *theorem* metric.closed_ball_subset_closed_ball
- \+ *lemma* metric.compact_iff_closed_bounded
- \+ *theorem* metric.continuous_iff'
- \+ *theorem* metric.continuous_iff
- \+ *theorem* metric.dist_mem_uniformity
- \+ *theorem* metric.exists_ball_subset_ball
- \+ *theorem* metric.exists_delta_of_continuous
- \+ *theorem* metric.is_closed_ball
- \+ *theorem* metric.is_open_ball
- \+ *theorem* metric.is_open_iff
- \+ *theorem* metric.mem_ball'
- \+ *theorem* metric.mem_ball
- \+ *theorem* metric.mem_ball_comm
- \+ *theorem* metric.mem_ball_self
- \+ *theorem* metric.mem_closed_ball
- \+ *theorem* metric.mem_closure_iff'
- \+ *theorem* metric.mem_nhds_iff
- \+ *theorem* metric.mem_of_closed'
- \+ *theorem* metric.mem_uniformity_dist
- \+ *theorem* metric.nhds_eq
- \+ *theorem* metric.pos_of_mem_ball
- \+ *theorem* metric.tendsto_at_top
- \+ *theorem* metric.tendsto_nhds
- \+ *theorem* metric.tendsto_nhds_nhds
- \+ *theorem* metric.totally_bounded_iff
- \+ *lemma* metric.totally_bounded_of_finite_discretization
- \+ *theorem* metric.uniform_continuous_iff
- \+ *theorem* metric.uniform_embedding_iff
- \+ *theorem* metric.uniformity_dist'
- \+ *theorem* metric.uniformity_dist
- \- *def* metric_space.uniform_space_of_dist
- \- *theorem* nhds_eq_metric
- \- *theorem* pos_of_mem_ball
- \- *theorem* tendsto_at_top_metric
- \- *theorem* tendsto_nhds_of_metric
- \- *theorem* tendsto_nhds_topo_metric
- \- *lemma* totally_bounded_of_finite_discretization
- \- *theorem* totally_bounded_of_metric
- \- *theorem* uniform_continuous_of_metric
- \- *theorem* uniform_embedding_of_metric
- \+ *def* uniform_space_of_dist
- \- *theorem* uniformity_dist'
- \- *theorem* uniformity_dist
- \- *theorem* uniformity_edist'

Modified analysis/nnreal.lean


Modified analysis/normed_space.lean


Modified analysis/real.lean


Modified analysis/topology/bounded_continuous_function.lean


Modified data/padics/hensel.lean


Modified data/padics/padic_integers.lean


Modified data/padics/padic_numbers.lean


Modified data/real/cau_seq_filter.lean




## [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/2f9f3df)
doc(tactic/simpa): update simpa documentation
#### Estimated changes
Modified docs/tactics.md


Modified tactic/simpa.lean




## [2019-01-14 13:34:16+01:00](https://github.com/leanprover-community/mathlib/commit/263e8a0)
fix(tactic/simpa): only try given expression in "simpa using"
#### Estimated changes
Modified data/padics/padic_norm.lean


Modified tactic/simpa.lean




## [2019-01-14 12:27:12+01:00](https://github.com/leanprover-community/mathlib/commit/4de9682)
fix(PULL_REQUEST_TEMPLATE): use absolute urls
The relative urls do not resolve correctly.
#### Estimated changes
Added .github/PULL_REQUEST_TEMPLATE.md


Deleted PULL_REQUEST_TEMPLATE.md




## [2019-01-14 12:03:28+01:00](https://github.com/leanprover-community/mathlib/commit/c7f13fd)
feat(.vscode): add copyright snippet
#### Estimated changes
Added .vscode/copyright.code-snippets




## [2019-01-13 19:02:05+01:00](https://github.com/leanprover-community/mathlib/commit/b03c0aa)
feat(group_theory/sylow): Cauchy's theorem ([#458](https://github.com/leanprover-community/mathlib/pull/458))
* feat(group_theory): adding add_subgroup and add_submonoid
* feat(data/list/basic): rotate a list
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *lemma* equiv.subtype_quotient_equiv_quotient_subtype

Modified group_theory/coset.lean


Modified group_theory/group_action.lean
- \+ *def* is_group_action.orbit_rel

Added group_theory/sylow.lean
- \+ *lemma* is_group_action.card_modeq_card_fixed_points
- \+ *lemma* is_group_action.mem_fixed_points_iff_card_orbit_eq_one
- \+ *lemma* quotient_group.card_preimage_mk
- \+ *lemma* sylow.exists_prime_order_of_dvd_card
- \+ *lemma* sylow.mem_vectors_prod_eq_one
- \+ *lemma* sylow.mem_vectors_prod_eq_one_iff
- \+ *def* sylow.mk_vector_prod_eq_one
- \+ *lemma* sylow.mk_vector_prod_eq_one_inj
- \+ *lemma* sylow.one_mem_fixed_points_rotate
- \+ *lemma* sylow.one_mem_vectors_prod_eq_one
- \+ *def* sylow.rotate_vectors_prod_eq_one
- \+ *def* sylow.vectors_prod_eq_one



## [2019-01-12 10:19:18-05:00](https://github.com/leanprover-community/mathlib/commit/dc6c38a)
fix(field_theory/subfield): is_subfield should be a Prop ([#588](https://github.com/leanprover-community/mathlib/pull/588))
#### Estimated changes
Modified field_theory/subfield.lean




## [2019-01-11 19:01:39+01:00](https://github.com/leanprover-community/mathlib/commit/e61a464)
feat(ring_theory/euclidean_domain): add more specific Euclidean domain stuff ([#527](https://github.com/leanprover-community/mathlib/pull/527))
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.eq_div_of_mul_eq_left
- \+ *lemma* euclidean_domain.eq_div_of_mul_eq_right

Added ring_theory/euclidean_domain.lean
- \+ *theorem* dvd_or_coprime
- \+ *theorem* gcd_is_unit_iff
- \+ *theorem* is_coprime_of_dvd
- \+ *theorem* span_gcd



## [2019-01-11 18:59:19+01:00](https://github.com/leanprover-community/mathlib/commit/5c323cd)
feat(category_theory): over and under categories  ([#549](https://github.com/leanprover-community/mathlib/pull/549))
#### Estimated changes
Modified category_theory/comma.lean
- \+/\- *lemma* category_theory.comma.map_right_obj_hom
- \+ *lemma* category_theory.over.comp_left
- \+ *def* category_theory.over.forget
- \+ *lemma* category_theory.over.forget_map
- \+ *lemma* category_theory.over.forget_obj
- \+ *def* category_theory.over.hom_mk
- \+ *lemma* category_theory.over.hom_mk_left
- \+ *lemma* category_theory.over.id_left
- \+ *def* category_theory.over.map
- \+ *lemma* category_theory.over.map_map_left
- \+ *lemma* category_theory.over.map_obj_hom
- \+ *lemma* category_theory.over.map_obj_left
- \+ *def* category_theory.over.mk
- \+ *lemma* category_theory.over.mk_hom
- \+ *lemma* category_theory.over.mk_left
- \+ *lemma* category_theory.over.over_morphism.ext
- \+ *lemma* category_theory.over.over_morphism_right
- \+ *lemma* category_theory.over.over_right
- \+ *def* category_theory.over.post
- \+ *lemma* category_theory.over.w
- \+ *def* category_theory.over
- \+ *lemma* category_theory.under.comp_right
- \+ *def* category_theory.under.forget
- \+ *lemma* category_theory.under.forget_map
- \+ *lemma* category_theory.under.forget_obj
- \+ *def* category_theory.under.hom_mk
- \+ *lemma* category_theory.under.hom_mk_right
- \+ *lemma* category_theory.under.id_right
- \+ *def* category_theory.under.map
- \+ *lemma* category_theory.under.map_map_right
- \+ *lemma* category_theory.under.map_obj_hom
- \+ *lemma* category_theory.under.map_obj_right
- \+ *def* category_theory.under.mk
- \+ *lemma* category_theory.under.mk_hom
- \+ *lemma* category_theory.under.mk_right
- \+ *def* category_theory.under.post
- \+ *lemma* category_theory.under.under_left
- \+ *lemma* category_theory.under.under_morphism.ext
- \+ *lemma* category_theory.under.under_morphism_left
- \+ *lemma* category_theory.under.w
- \+ *def* category_theory.under

Added category_theory/limits/over.lean
- \+ *def* category_theory.functor.to_cocone
- \+ *lemma* category_theory.functor.to_cocone_X
- \+ *lemma* category_theory.functor.to_cocone_ι
- \+ *def* category_theory.functor.to_cone
- \+ *lemma* category_theory.functor.to_cone_X
- \+ *lemma* category_theory.functor.to_cone_π
- \+ *def* category_theory.over.colimit
- \+ *lemma* category_theory.over.colimit_X_hom
- \+ *lemma* category_theory.over.colimit_ι_app
- \+ *def* category_theory.over.forget_colimit_is_colimit
- \+ *def* category_theory.under.forget_limit_is_limit
- \+ *def* category_theory.under.limit
- \+ *lemma* category_theory.under.limit_X_hom
- \+ *lemma* category_theory.under.limit_π_app



## [2019-01-11 18:17:13+01:00](https://github.com/leanprover-community/mathlib/commit/c19b4be)
feat(meta/rb_map): add some monadic filtering
#### Estimated changes
Modified meta/rb_map.lean




## [2019-01-11 17:06:02+01:00](https://github.com/leanprover-community/mathlib/commit/7a9b2e4)
Update PULL_REQUEST_TEMPLATE.md
#### Estimated changes
Modified PULL_REQUEST_TEMPLATE.md




## [2019-01-11 17:04:58+01:00](https://github.com/leanprover-community/mathlib/commit/6516c34)
doc(README): elect new maintainers
#### Estimated changes
Modified README.md




## [2019-01-11 15:35:42+01:00](https://github.com/leanprover-community/mathlib/commit/4f3f86d)
chore(ring_theory/subring): remove unused import
#### Estimated changes
Modified ring_theory/subring.lean




## [2019-01-11 11:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/4578796)
feat(data/polynomial): various lemmas about degree and monic and coeff
#### Estimated changes
Modified data/polynomial.lean
- \+/\- *lemma* polynomial.coeff_X
- \+/\- *lemma* polynomial.coeff_add
- \+/\- *lemma* polynomial.coeff_neg
- \+ *lemma* polynomial.coeff_sub
- \+ *theorem* polynomial.degree_C_mul_X_pow_le
- \+ *theorem* polynomial.degree_X_le
- \+ *theorem* polynomial.degree_X_pow_le
- \+ *theorem* polynomial.degree_le_iff_coeff_zero
- \+ *theorem* polynomial.degree_mod_by_monic_le
- \+ *theorem* polynomial.leading_coeff_mul_X_pow
- \+ *theorem* polynomial.monic_X_add_C
- \+ *theorem* polynomial.monic_X_pow_add
- \+ *theorem* polynomial.monic_X_pow_sub
- \+ *theorem* polynomial.monic_X_sub_C
- \- *lemma* polynomial.monic_X_sub_C
- \+ *theorem* polynomial.monic_of_degree_le
- \+ *theorem* polynomial.nat_degree_le_of_degree_le



## [2019-01-10 15:26:30-05:00](https://github.com/leanprover-community/mathlib/commit/b1684fe)
fix(principal_ideal_domain): correct spelling mistake ([#582](https://github.com/leanprover-community/mathlib/pull/582))
#### Estimated changes
Modified ring_theory/principal_ideal_domain.lean
- \- *lemma* principal_ideal_domain.associates_iredducible_iff_prime
- \+ *lemma* principal_ideal_domain.associates_irreducible_iff_prime



## [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/6e97721)
refactor(principal_ideal_domain): simplify proof of PID -> UFD
#### Estimated changes
Modified ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_ring.exists_factors

Modified ring_theory/principal_ideal_domain.lean
- \- *lemma* principal_ideal_domain.associated_of_associated_prod_prod
- \+ *lemma* principal_ideal_domain.associates_iredducible_iff_prime
- \- *lemma* principal_ideal_domain.associates_prime_of_irreducible
- \- *lemma* principal_ideal_domain.eq_of_prod_eq_associates
- \- *lemma* principal_ideal_domain.exists_factors
- \+ *lemma* principal_ideal_domain.irreducible_iff_prime
- \- *lemma* principal_ideal_domain.prime_of_irreducible

Modified ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* unique_factorization_domain.irreducible_factors



## [2019-01-10 12:11:24+01:00](https://github.com/leanprover-community/mathlib/commit/f5bf277)
refactor(unique_factorization_domain): simplify definition of UFD
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* multiset.dvd_prod

Modified ring_theory/associated.lean
- \+ *lemma* associated_mul_left_cancel
- \+ *lemma* associated_mul_right_cancel
- \+ *lemma* dvd_iff_dvd_of_rel_left
- \+ *lemma* dvd_iff_dvd_of_rel_right
- \+ *lemma* dvd_mul_unit_iff
- \+ *lemma* eq_zero_iff_of_associated
- \+ *lemma* exists_associated_mem_of_dvd_prod
- \+ *lemma* irreducible_iff_of_associated
- \+ *lemma* irreducible_of_associated
- \+ *lemma* is_unit_iff_of_associated
- \+ *lemma* is_unit_unit
- \+ *lemma* mul_unit_dvd_iff
- \+ *lemma* ne_zero_iff_of_associated
- \+/\- *lemma* not_prime_zero
- \+ *lemma* prime_iff_of_associated
- \+ *lemma* prime_of_associated
- \+ *lemma* unit_mul_dvd_iff

Modified ring_theory/principal_ideal_domain.lean


Modified ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_domain.factors_irreducible
- \+ *lemma* unique_factorization_domain.induction_on_prime
- \+ *lemma* unique_factorization_domain.irreducible_factors
- \+ *lemma* unique_factorization_domain.irreducible_iff_prime
- \+ *def* unique_factorization_domain.of_unique_irreducible_factorization
- \+ *lemma* unique_factorization_domain.unique



## [2019-01-10 09:46:28+01:00](https://github.com/leanprover-community/mathlib/commit/8b66ebd)
functions and cardinality ([#556](https://github.com/leanprover-community/mathlib/pull/556))
#### Estimated changes
Modified data/set/countable.lean
- \+ *lemma* set.countable_of_injective_of_countable_image

Modified data/set/finite.lean
- \+ *lemma* set.finite_subsets_of_finite

Modified data/set/function.lean
- \+ *lemma* set.inv_fun_on_image
- \+ *theorem* set.maps_to'
- \+ *theorem* set.maps_to_image
- \+ *theorem* set.maps_to_range



## [2019-01-09 10:08:23+01:00](https://github.com/leanprover-community/mathlib/commit/f488635)
chore(tactic/monotonicity/interactive) use derive for has_reflect ([#578](https://github.com/leanprover-community/mathlib/pull/578))
#### Estimated changes
Modified tactic/monotonicity/interactive.lean




## [2019-01-09 10:07:56+01:00](https://github.com/leanprover-community/mathlib/commit/af735a5)
feat(field_theory/finite): field_of_integral_domain ([#579](https://github.com/leanprover-community/mathlib/pull/579))
#### Estimated changes
Modified field_theory/finite.lean
- \+ *def* finite_field.field_of_integral_domain



## [2019-01-09 09:48:35+01:00](https://github.com/leanprover-community/mathlib/commit/d0532c1)
feat(data/polynomial): lemmas about map ([#530](https://github.com/leanprover-community/mathlib/pull/530))
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* is_field_hom.injective

Modified algebra/group.lean
- \+ *lemma* is_group_hom.injective_iff

Modified data/polynomial.lean
- \+ *lemma* polynomial.coeff_X
- \+ *lemma* polynomial.degree_div_le
- \+ *lemma* polynomial.degree_div_lt
- \+ *lemma* polynomial.degree_map
- \- *lemma* polynomial.degree_map_eq
- \+ *lemma* polynomial.degree_map_eq_of_injective
- \+ *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* polynomial.degree_mul_leading_coeff_inv
- \+ *lemma* polynomial.div_mod_by_monic_unique
- \+ *lemma* polynomial.div_zero
- \+ *lemma* polynomial.eq_X_add_C_of_degree_le_one
- \+ *lemma* polynomial.eval_map
- \+/\- *lemma* polynomial.eval_pow
- \+ *lemma* polynomial.eval₂_hom
- \+ *lemma* polynomial.eval₂_map
- \+ *lemma* polynomial.exists_root_of_degree_eq_one
- \+ *lemma* polynomial.leading_coeff_map
- \+ *lemma* polynomial.map_div
- \+ *lemma* polynomial.map_div_by_monic
- \+ *lemma* polynomial.map_eq_zero
- \+ *lemma* polynomial.map_id
- \+ *lemma* polynomial.map_map
- \+ *lemma* polynomial.map_mod
- \+ *lemma* polynomial.map_mod_by_monic
- \+ *lemma* polynomial.map_mod_div_by_monic
- \+ *lemma* polynomial.map_neg
- \+ *lemma* polynomial.map_sub
- \+ *lemma* polynomial.monic_map
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+ *lemma* polynomial.nat_degree_map
- \+ *lemma* polynomial.ne_zero_of_monic_of_zero_ne_one



## [2019-01-05 16:41:07-05:00](https://github.com/leanprover-community/mathlib/commit/2e63635)
feat(group_theory/subgroup): simple groups ([#572](https://github.com/leanprover-community/mathlib/pull/572))
#### Estimated changes
Modified group_theory/subgroup.lean
- \+ *theorem* additive.simple_add_group_iff
- \+ *lemma* is_subgroup.eq_trivial_iff
- \+ *theorem* multiplicative.simple_group_iff
- \+ *lemma* simple_add_group_of_surjective
- \+ *lemma* simple_group_of_surjective



## [2019-01-05 16:38:38-05:00](https://github.com/leanprover-community/mathlib/commit/d19c9bc)
feat(data/fintype): decidable_left_inverse_fintype ([#575](https://github.com/leanprover-community/mathlib/pull/575))
#### Estimated changes
Modified data/fintype.lean




## [2019-01-05 16:37:57-05:00](https://github.com/leanprover-community/mathlib/commit/395aadd)
feat(group_theory/sign): sign_surjective ([#576](https://github.com/leanprover-community/mathlib/pull/576))
#### Estimated changes
Modified group_theory/perm.lean
- \+ *lemma* equiv.perm.sign_surjective



## [2019-01-05 14:19:05-05:00](https://github.com/leanprover-community/mathlib/commit/b9c5eb0)
feat(ring_theory/multiplicity): multiplicity of elements of a ring ([#523](https://github.com/leanprover-community/mathlib/pull/523))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* pow_dvd_pow

Modified data/multiset.lean
- \+ *lemma* multiset.card_smul

Modified data/nat/basic.lean


Modified data/rat.lean
- \+ *lemma* rat.add_num_denom
- \+ *lemma* rat.denom_one
- \+ *lemma* rat.num_one

Added ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.dvd_of_multiplicity_pos
- \+ *lemma* multiplicity.eq_some_iff
- \+ *lemma* multiplicity.eq_top_iff
- \+ *lemma* multiplicity.eq_top_iff_not_finite
- \+ *def* multiplicity.finite
- \+ *lemma* multiplicity.finite_def
- \+ *lemma* multiplicity.finite_iff_dom
- \+ *lemma* multiplicity.finite_int_iff
- \+ *lemma* multiplicity.finite_int_iff_nat_abs_finite
- \+ *lemma* multiplicity.finite_mul
- \+ *lemma* multiplicity.finite_mul_aux
- \+ *lemma* multiplicity.finite_mul_iff
- \+ *lemma* multiplicity.finite_nat_iff
- \+ *lemma* multiplicity.finite_of_finite_mul_left
- \+ *lemma* multiplicity.finite_of_finite_mul_right
- \+ *lemma* multiplicity.finite_pow
- \+ *lemma* multiplicity.get_multiplicity_self
- \+ *lemma* multiplicity.get_one_right
- \+ *lemma* multiplicity.is_greatest'
- \+ *lemma* multiplicity.is_greatest
- \+ *lemma* multiplicity.le_multiplicity_of_pow_dvd
- \+ *lemma* multiplicity.min_le_multiplicity_add
- \+ *lemma* multiplicity.multiplicity_eq_zero_of_not_dvd
- \+ *lemma* multiplicity.multiplicity_le_multiplicity_iff
- \+ *lemma* multiplicity.multiplicity_self
- \+ *lemma* multiplicity.multiplicity_unit
- \+ *lemma* multiplicity.ne_zero_of_finite
- \+ *lemma* multiplicity.not_finite_iff_forall
- \+ *lemma* multiplicity.not_unit_of_finite
- \+ *lemma* multiplicity.one_left
- \+ *lemma* multiplicity.one_right
- \+ *lemma* multiplicity.pow
- \+ *lemma* multiplicity.pow_dvd_iff_le_multiplicity
- \+ *lemma* multiplicity.pow_dvd_of_le_multiplicity
- \+ *lemma* multiplicity.pow_multiplicity_dvd
- \+ *lemma* multiplicity.unique'
- \+ *lemma* multiplicity.unique
- \+ *def* multiplicity
- \+ *lemma* multiplicity_eq_zero_of_coprime



## [2019-01-05 14:17:10-05:00](https://github.com/leanprover-community/mathlib/commit/bc96eca)
feat(group_theory/quotient_group): quotient_ker_equiv_range ([#574](https://github.com/leanprover-community/mathlib/pull/574))
#### Estimated changes
Modified algebra/group.lean


Modified group_theory/quotient_group.lean




## [2019-01-05 14:13:47-05:00](https://github.com/leanprover-community/mathlib/commit/3ff5e93)
feat(data/polynomial): polynomials over a field are a normalization domain ([#560](https://github.com/leanprover-community/mathlib/pull/560))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.coe_norm_unit
- \+ *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \+ *lemma* polynomial.coeff_inv_units
- \+ *lemma* polynomial.degree_coe_units
- \+ *lemma* polynomial.eq_C_of_degree_eq_zero
- \+ *lemma* polynomial.monic_mul_norm_unit
- \+ *lemma* polynomial.nat_degree_coe_units



## [2019-01-05 14:12:49-05:00](https://github.com/leanprover-community/mathlib/commit/87bf618)
feat(data/polynomial): C_neg and C_sub ([#561](https://github.com/leanprover-community/mathlib/pull/561))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.C_neg
- \+ *lemma* polynomial.C_sub



## [2019-01-05 14:12:25-05:00](https://github.com/leanprover-community/mathlib/commit/78d0ebf)
feat(data/multiset): prod_hom and exists_mem_of_rel_of_mem ([#562](https://github.com/leanprover-community/mathlib/pull/562))
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* multiset.exists_mem_of_rel_of_mem
- \+ *lemma* multiset.prod_hom
- \+ *lemma* multiset.sum_hom



## [2019-01-05 14:11:58-05:00](https://github.com/leanprover-community/mathlib/commit/4e509a8)
feat(ring_theory/noetherian): irreducible_induction_on ([#563](https://github.com/leanprover-community/mathlib/pull/563))
#### Estimated changes
Modified ring_theory/associated.lean
- \- *theorem* associates.zero_mul
- \+ *lemma* dvd_and_not_dvd_iff

Modified ring_theory/ideals.lean
- \+ *lemma* ideal.span_singleton_lt_span_singleton

Modified ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_ring.exists_irreducible_factor
- \+ *lemma* is_noetherian_ring.irreducible_induction_on
- \+ *lemma* is_noetherian_ring.well_founded_dvd_not_unit



## [2019-01-05 14:10:24-05:00](https://github.com/leanprover-community/mathlib/commit/ea0ff05)
doc(category_theory): update `category_theory` documentation ([#564](https://github.com/leanprover-community/mathlib/pull/564)) [ci-skip]
#### Estimated changes
Modified docs/theories/category_theory.md




## [2019-01-05 14:09:18-05:00](https://github.com/leanprover-community/mathlib/commit/33df7ec)
feat(data/nat/enat): has_well_founded for enat ([#565](https://github.com/leanprover-community/mathlib/pull/565))
#### Estimated changes
Modified data/nat/enat.lean
- \+ *lemma* enat.coe_ne_bot
- \+ *lemma* enat.lt_wf
- \+ *def* enat.to_with_top
- \+ *lemma* enat.to_with_top_coe'
- \+ *lemma* enat.to_with_top_coe
- \+ *lemma* enat.to_with_top_le
- \+ *lemma* enat.to_with_top_lt
- \+ *lemma* enat.to_with_top_top'
- \+ *lemma* enat.to_with_top_top
- \+ *lemma* enat.to_with_top_zero'
- \+ *lemma* enat.to_with_top_zero



## [2019-01-05 14:06:39-05:00](https://github.com/leanprover-community/mathlib/commit/4bacdf2)
feat(logic/basic): inhabited_of_nonempty with instance parameter ([#566](https://github.com/leanprover-community/mathlib/pull/566))
#### Estimated changes
Modified logic/basic.lean




## [2019-01-05 14:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/125feb6)
feat(data/multiset): forall_of_pairwise ([#569](https://github.com/leanprover-community/mathlib/pull/569))
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.forall_of_pairwise

Modified data/multiset.lean
- \+ *lemma* multiset.forall_of_pairwise



## [2019-01-05 14:05:30-05:00](https://github.com/leanprover-community/mathlib/commit/da6ec21)
feat(algebra/group): is_conj_one_right ([#570](https://github.com/leanprover-community/mathlib/pull/570))
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* is_conj_one_left
- \+ *lemma* is_conj_one_right
- \+/\- *lemma* is_conj_symm
- \+/\- *lemma* is_conj_trans



## [2019-01-05 14:05:06-05:00](https://github.com/leanprover-community/mathlib/commit/a32fa18)
feat(data/finset): finset.card_eq_one ([#571](https://github.com/leanprover-community/mathlib/pull/571))
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.card_eq_one



## [2019-01-05 04:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/40fa9ad)
fix(analysis/measure_theory): fix build
#### Estimated changes
Modified analysis/measure_theory/lebesgue_measure.lean


Modified data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_add_of_real



## [2019-01-04 20:28:21-05:00](https://github.com/leanprover-community/mathlib/commit/93a330e)
fix(data/real/cau_seq_filter): fix build
#### Estimated changes
Modified data/real/cau_seq_filter.lean




## [2019-01-04 19:43:43-05:00](https://github.com/leanprover-community/mathlib/commit/19e7b1f)
feat(analysis/topology): Bounded continuous functions ([#464](https://github.com/leanprover-community/mathlib/pull/464))
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* neg_sub_neg

Modified analysis/metric_space.lean
- \+ *lemma* bounded.subset
- \+ *def* bounded
- \+ *lemma* bounded_bUnion
- \+ *lemma* bounded_ball
- \+ *lemma* bounded_closed_ball
- \+ *lemma* bounded_empty
- \+ *lemma* bounded_iff_mem_bounded
- \+ *lemma* bounded_iff_subset_ball
- \+ *lemma* bounded_of_compact
- \+ *lemma* bounded_of_compact_space
- \+ *lemma* bounded_of_finite
- \+ *lemma* bounded_range_iff
- \+ *lemma* bounded_singleton
- \+ *lemma* bounded_union
- \+ *theorem* cauchy_seq_bdd
- \+ *lemma* cauchy_seq_iff_le_tendsto_0
- \+ *theorem* closed_ball_subset_closed_ball
- \+ *lemma* compact_iff_closed_bounded
- \+ *lemma* dist_triangle4
- \+ *lemma* dist_triangle4_left
- \+ *lemma* dist_triangle4_right
- \+ *theorem* mem_of_closed'
- \+/\- *theorem* tendsto_at_top_metric
- \+ *lemma* totally_bounded_of_finite_discretization

Modified analysis/normed_space.lean
- \+ *def* normed_group.of_add_dist'
- \+ *def* normed_group.of_add_dist

Added analysis/topology/bounded_continuous_function.lean
- \+ *lemma* bounded_continuous_function.abs_diff_coe_le_dist
- \+ *theorem* bounded_continuous_function.arzela_ascoli
- \+ *theorem* bounded_continuous_function.arzela_ascoli₁
- \+ *theorem* bounded_continuous_function.arzela_ascoli₂
- \+ *lemma* bounded_continuous_function.bounded_range
- \+ *def* bounded_continuous_function.cod_restrict
- \+ *lemma* bounded_continuous_function.coe_add
- \+ *lemma* bounded_continuous_function.coe_diff
- \+ *lemma* bounded_continuous_function.coe_le_coe_add_dist
- \+ *lemma* bounded_continuous_function.coe_neg
- \+ *lemma* bounded_continuous_function.coe_zero
- \+ *def* bounded_continuous_function.comp
- \+ *def* bounded_continuous_function.const
- \+ *lemma* bounded_continuous_function.continuous_comp
- \+ *theorem* bounded_continuous_function.continuous_eval
- \+ *theorem* bounded_continuous_function.continuous_evalf
- \+ *theorem* bounded_continuous_function.continuous_evalx
- \+ *lemma* bounded_continuous_function.dist_coe_le_dist
- \+ *lemma* bounded_continuous_function.dist_eq
- \+ *lemma* bounded_continuous_function.dist_le
- \+ *lemma* bounded_continuous_function.dist_set_exists
- \+ *lemma* bounded_continuous_function.dist_zero_of_empty
- \+ *lemma* bounded_continuous_function.equicontinuous_of_continuity_modulus
- \+ *lemma* bounded_continuous_function.ext
- \+ *lemma* bounded_continuous_function.forall_coe_zero_iff_zero
- \+ *def* bounded_continuous_function.mk_of_compact
- \+ *def* bounded_continuous_function.mk_of_discrete
- \+ *lemma* bounded_continuous_function.norm_coe_le_norm
- \+ *lemma* bounded_continuous_function.norm_def
- \+ *lemma* bounded_continuous_function.norm_le
- \+ *def* bounded_continuous_function
- \+ *lemma* continuous_of_lipschitz
- \+ *lemma* continuous_of_locally_uniform_limit_of_continuous
- \+ *lemma* continuous_of_uniform_limit_of_continuous

Modified analysis/topology/continuity.lean
- \+ *lemma* compact_iff_compact_space
- \+ *lemma* continuous_of_discrete_topology

Modified analysis/topology/uniform_space.lean
- \+ *lemma* totally_bounded_empty

Modified data/real/ennreal.lean
- \+ *lemma* ennreal.coe_nonneg
- \+ *lemma* ennreal.coe_pos
- \+ *lemma* ennreal.lt_iff_exists_rat_btwn
- \+ *lemma* ennreal.lt_iff_exists_real_btwn

Modified data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_add
- \- *lemma* nnreal.of_real_add_of_real
- \+/\- *lemma* nnreal.of_real_eq_zero
- \+ *lemma* nnreal.of_real_lt_of_real_iff'
- \+/\- *lemma* nnreal.of_real_lt_of_real_iff
- \+/\- *lemma* nnreal.of_real_of_nonpos
- \+ *lemma* nnreal.of_real_pos
- \- *lemma* nnreal.zero_lt_of_real

Modified data/set/basic.lean
- \+ *lemma* set.range_const_subset

Modified data/set/finite.lean
- \+ *theorem* set.finite.of_fintype



## [2019-01-02 10:12:17-05:00](https://github.com/leanprover-community/mathlib/commit/dcd0466)
feat(analysis/topology): complete sets, minor modifications ([#557](https://github.com/leanprover-community/mathlib/pull/557))
#### Estimated changes
Modified analysis/limits.lean


Modified analysis/metric_space.lean


Modified analysis/normed_space.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* is_closed_of_closure_subset
- \+/\- *lemma* mem_closure_of_tendsto
- \+ *lemma* mem_of_closed_of_tendsto'

Modified analysis/topology/topological_structures.lean
- \- *lemma* Inf_of_Inf_of_monotone_of_continuous
- \+ *lemma* Inf_of_continuous'
- \+ *lemma* Inf_of_continuous
- \- *lemma* Sup_of_Sup_of_monotone_of_continuous
- \+ *lemma* Sup_of_continuous'
- \+ *lemma* Sup_of_continuous
- \+ *lemma* ge_of_tendsto
- \+ *lemma* infi_of_continuous
- \- *lemma* infi_of_infi_of_monotone_of_continuous
- \+/\- *lemma* le_of_tendsto
- \+ *lemma* le_of_tendsto_of_tendsto
- \+ *lemma* supr_of_continuous
- \- *lemma* supr_of_supr_of_monotone_of_continuous

Modified analysis/topology/uniform_space.lean
- \+ *lemma* compact_iff_totally_bounded_complete
- \- *lemma* compact_of_totally_bounded_complete
- \- *lemma* complete_of_compact_set
- \- *lemma* complete_of_is_closed
- \+ *lemma* complete_space_of_is_complete_univ
- \+ *lemma* complete_univ
- \+ *lemma* is_closed_of_is_complete
- \+ *def* is_complete
- \+ *lemma* is_complete_image_iff
- \+ *lemma* is_complete_of_is_closed



## [2019-01-02 08:57:30-05:00](https://github.com/leanprover-community/mathlib/commit/f59f5d5)
feat(data/real/ennreal): minor additions to ennreal ([#558](https://github.com/leanprover-community/mathlib/pull/558))
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/metric_space.lean


Modified data/real/ennreal.lean
- \+ *lemma* ennreal.add_lt_add_iff_right
- \+ *lemma* ennreal.add_lt_top
- \+ *lemma* ennreal.bit0_eq_top_iff
- \+ *lemma* ennreal.bit0_eq_zero_iff
- \+ *lemma* ennreal.bit0_inj
- \+ *lemma* ennreal.bit1_eq_one_iff
- \+ *lemma* ennreal.bit1_eq_top_iff
- \+ *lemma* ennreal.bit1_inj
- \+ *lemma* ennreal.bit1_ne_zero
- \+ *lemma* ennreal.coe_bit0
- \+ *lemma* ennreal.coe_bit1
- \+/\- *lemma* ennreal.coe_div
- \+ *lemma* ennreal.coe_inv
- \+/\- *lemma* ennreal.div_le_iff_le_mul
- \+/\- *lemma* ennreal.div_pos_iff
- \+ *lemma* ennreal.div_zero_iff
- \+ *lemma* ennreal.exists_inv_nat_lt
- \+ *lemma* ennreal.half_lt_self
- \+ *lemma* ennreal.half_pos
- \- *lemma* ennreal.inv_coe
- \+/\- *lemma* ennreal.inv_eq_top
- \+/\- *lemma* ennreal.inv_eq_zero
- \+/\- *lemma* ennreal.inv_inv
- \+/\- *lemma* ennreal.inv_ne_top
- \+/\- *lemma* ennreal.inv_ne_zero
- \+ *lemma* ennreal.mul_eq_top
- \+ *lemma* ennreal.mul_eq_zero
- \+ *lemma* ennreal.sub_eq_zero_iff_le
- \+ *lemma* ennreal.zero_lt_sub_iff_lt

Modified data/real/nnreal.lean
- \+/\- *lemma* nnreal.add_halves
- \+ *lemma* nnreal.half_lt_self
- \+/\- *lemma* nnreal.of_real_le_of_real_iff
- \+ *lemma* nnreal.of_real_lt_of_real_iff



## [2019-01-02 06:39:37-05:00](https://github.com/leanprover-community/mathlib/commit/50583b9)
feat(algebra/order): additional theorems on cmp
#### Estimated changes
Modified algebra/order.lean
- \+ *theorem* cmp_compares
- \+ *theorem* cmp_swap
- \+ *theorem* ordering.or_else_eq_lt
- \+ *theorem* ordering.swap_or_else

Modified order/basic.lean
- \+ *def* decidable_linear_order.lift

