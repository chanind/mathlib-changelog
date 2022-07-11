## [2019-12-29 08:52:23](https://github.com/leanprover-community/mathlib/commit/acf2038)
feat(analysis/calculus/mean_value): more corollaries of the MVT ([#1819](https://github.com/leanprover-community/mathlib/pull/1819))
* feat(analysis/calculus/mean_value): more corolaries of the MVT
* Fix compile, add "strict inequalities" versions of some theorems, add docs
* Update src/analysis/calculus/mean_value.lean
* Add theorems for `convex_on univ`
* Fix comments
* @sgouezel adds missing articles
Thanks a lot! We don't have them in Russian, so it's hard for me to put them right.
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/calculus/mean_value.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Add more `univ` versions
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* is_const_of_fderiv_eq_zero
- \+ *theorem* convex.mul_sub_lt_image_sub_of_lt_deriv
- \+ *theorem* mul_sub_lt_image_sub_of_lt_deriv
- \+ *theorem* convex.mul_sub_le_image_sub_of_le_deriv
- \+ *theorem* mul_sub_le_image_sub_of_le_deriv
- \+ *theorem* convex.image_sub_lt_mul_sub_of_deriv_lt
- \+ *theorem* image_sub_lt_mul_sub_of_deriv_lt
- \+ *theorem* convex.image_sub_le_mul_sub_of_deriv_le
- \+ *theorem* image_sub_le_mul_sub_of_deriv_le
- \+ *theorem* convex.strict_mono_of_deriv_pos
- \+ *theorem* strict_mono_of_deriv_pos
- \+ *theorem* convex.mono_of_deriv_nonneg
- \+ *theorem* mono_of_deriv_nonneg
- \+ *theorem* convex.strict_antimono_of_deriv_neg
- \+ *theorem* strict_antimono_of_deriv_neg
- \+ *theorem* convex.antimono_of_deriv_nonpos
- \+ *theorem* antimono_of_deriv_nonpos
- \+ *theorem* convex_on_of_deriv_mono
- \+ *theorem* convex_on_univ_of_deriv_mono
- \+ *theorem* convex_on_of_deriv2_nonneg
- \+ *theorem* convex_on_univ_of_deriv2_nonneg

Modified src/analysis/convex.lean
- \+ *lemma* linear_order.convex_on_of_lt
- \+ *lemma* convex_on_real_of_slope_mono_adjacent
- \- *lemma* convex_on_linorder



## [2019-12-28 20:31:03](https://github.com/leanprover-community/mathlib/commit/64770a8)
feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition ([#1834](https://github.com/leanprover-community/mathlib/pull/1834))
* feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition
* Fix a typo
* Move, change doc, add versions for `has_deriv_within_at` and `has_deriv_at`.
* Fix docstring, remove an unsed argument
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at_filter_iff_tendsto_slope
- \+ *lemma* has_deriv_within_at_iff_tendsto_slope
- \+ *lemma* has_deriv_at_iff_tendsto_slope

Modified src/analysis/calculus/fderiv.lean


Modified src/order/filter/basic.lean
- \+ *lemma* tendsto_congr'
- \+ *theorem* tendsto_congr
- \- *theorem* tendsto.congr'r

Modified src/topology/basic.lean
- \+ *lemma* tendsto_inf_principal_nhds_iff_of_forall_eq



## [2019-12-28 13:01:45](https://github.com/leanprover-community/mathlib/commit/e43905b)
refactor(topology/algebra/ordered): formulate a few "Icc induction" principles ([#1833](https://github.com/leanprover-community/mathlib/pull/1833))
* refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within`
* Add missing `order_dual.*` instances
* Try to fix the build
* Fix formatting, rename some variables
* refactor(topology/algebra/ordered): formulate a few "Icc induction" principles
They have other applications than proving `is_connected_Icc`.
* Fix doc
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Rephraze docs
* Drop an unused argument
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_closed.mem_of_ge_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within



## [2019-12-28 11:42:42](https://github.com/leanprover-community/mathlib/commit/a6a8a11)
refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep` ([#1825](https://github.com/leanprover-community/mathlib/pull/1825))
* refactor(data/equiv/encodable): bring `directed.sequence*` from `integration`, use `quotient.rep` instead of `quot.rep`
`sequence_of_directed` in `measure_theory/integration` did not belong
there.
Also add some docstrings.
* doc/style fixes by @sgouezel
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Remove an unused argument, add a docstring
* Completely remove the `reflexive r` assumption
#### Estimated changes
Modified src/data/equiv/encodable.lean
- \+ *lemma* sequence_mono_nat
- \+ *lemma* rel_sequence
- \+ *lemma* sequence_mono
- \+ *lemma* le_sequence
- \+ *theorem* quotient.rep_spec
- \- *theorem* rep_spec
- \+ *def* quotient.rep
- \- *def* rep

Modified src/measure_theory/integration.lean
- \+ *lemma* seq_apply
- \- *lemma* monotone_sequence_of_directed
- \- *lemma* le_sequence_of_directed

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* all_ae_of_all



## [2019-12-28 10:05:30](https://github.com/leanprover-community/mathlib/commit/340fa14)
feat(analysis/specific_limits): add a few more limits ([#1832](https://github.com/leanprover-community/mathlib/pull/1832))
* feat(analysis/specific_limits): add a few more limits
* Drop 1 lemma, generalize two others.
* Rename `tendsto_inverse_at_top_nhds_0`, fix compile
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_norm_at_top_at_top
- \+ *lemma* tendsto_inv_at_top_zero'
- \+ *lemma* tendsto_inv_at_top_zero
- \+ *lemma* lim_norm_zero'
- \+ *lemma* normed_field.tendsto_norm_inverse_nhds_within_0_at_top
- \- *lemma* tendsto_inverse_at_top_nhds_0

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_abs_at_top_at_top



## [2019-12-27 20:26:09](https://github.com/leanprover-community/mathlib/commit/0a9a1ff)
refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within` ([#1831](https://github.com/leanprover-community/mathlib/pull/1831))
* refactor(topology/algebra/ordered): use `tfae`, prove equality of some `nhds_within`
* Add missing `order_dual.*` instances
* Try to fix the build
* Fix formatting, rename some variables
* Fix compile
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean


Modified src/order/basic.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* tfae_mem_nhds_within_Ioi
- \+ *lemma* nhds_within_Ioc_eq_nhds_within_Ioi
- \+ *lemma* nhds_within_Ioo_eq_nhds_within_Ioi
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset'
- \+ *lemma* tfae_mem_nhds_within_Iio
- \+ *lemma* nhds_within_Ico_eq_nhds_within_Iio
- \+ *lemma* nhds_within_Ioo_eq_nhds_within_Iio



## [2019-12-27 18:11:30](https://github.com/leanprover-community/mathlib/commit/82ca731)
refactor(calculus): simplify derivative extension ([#1826](https://github.com/leanprover-community/mathlib/pull/1826))
* refactor(calculus): simplify derivative extension
* generalize continuous_within_at.closure_le
* Simplify proof following Sébastien
* Update src/analysis/calculus/extend_deriv.lean
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_within_at.closure_le

Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_prod_eq
- \+ *lemma* continuous_within_at.mem_closure
- \+ *lemma* continuous_within_at.image_closure



## [2019-12-27 15:35:17](https://github.com/leanprover-community/mathlib/commit/3a78f49)
feat(order/basic): add `dual_le` and `dual_lt` lemmas ([#1830](https://github.com/leanprover-community/mathlib/pull/1830))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* dual_le
- \+ *lemma* dual_lt



## [2019-12-27 14:05:28](https://github.com/leanprover-community/mathlib/commit/c9a81b0)
refactor(*): unify API of `list/multiset/finset.prod_hom` ([#1820](https://github.com/leanprover-community/mathlib/pull/1820))
* refactor(*): unify API of `list/multiset/finset.prod_hom`
Also remove `is_group_hom.map_prod`; use `*.prod_hom.symm` or
`monoid_hom.map_*prod` instead.
* Update src/ring_theory/ideal_operations.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Restore explicit args of `list.fold(l/r)_hom`
* Fix `group_theory/perm/sign`
* Fix `quadratic_reciprocity`
* Fix compile
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_hom
- \+ *lemma* monoid_hom.map_prod
- \- *lemma* is_group_hom.map_multiset_prod
- \- *lemma* is_group_hom.map_finset_prod
- \- *theorem* is_group_hom.map_prod

Modified src/algebra/module.lean


Modified src/algebra/pi_instances.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/fold.lean


Modified src/data/complex/exponential.lean
- \+ *lemma* exp_list_sum
- \+ *lemma* exp_multiset_sum
- \+ *lemma* exp_sum

Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* foldl_map
- \+/\- *theorem* foldr_map
- \+/\- *theorem* foldl_hom
- \+/\- *theorem* foldr_hom
- \+ *theorem* prod_hom_rel
- \+ *theorem* prod_hom
- \+ *theorem* monoid_hom.map_list_prod

Modified src/data/matrix/basic.lean


Modified src/data/multiset.lean
- \+/\- *lemma* prod_hom
- \- *lemma* sum_hom
- \+ *theorem* prod_hom_rel
- \+ *theorem* monoid_hom.map_multiset_prod

Modified src/data/mv_polynomial.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* coe_list_sum
- \+ *lemma* coe_list_prod
- \+ *lemma* coe_multiset_sum
- \+ *lemma* coe_multiset_prod
- \+ *lemma* coe_sum
- \+ *lemma* coe_prod
- \- *lemma* sum_coe
- \- *lemma* prod_coe

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basic.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/order/order_iso.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean




## [2019-12-27 12:40:25](https://github.com/leanprover-community/mathlib/commit/0a87dd8)
feat(topology/basic): a few simple lemmas ([#1829](https://github.com/leanprover-community/mathlib/pull/1829))
* feat(topology/basic): a few simple lemmas
* Fix compile
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* monotone_closure
- \+ *lemma* closure_inter_subset_inter_closure
- \+ *lemma* frontier_inter_subset
- \+ *lemma* frontier_union_subset
- \+ *lemma* is_closed.frontier_eq
- \+ *lemma* is_open.frontier_eq



## [2019-12-27 11:08:24](https://github.com/leanprover-community/mathlib/commit/89854fa)
refactor(analysis/calculus/deriv): Use equality of functions ([#1818](https://github.com/leanprover-community/mathlib/pull/1818))
* refactor(analysis/calculus/deriv): Use equality of functions
This way we can rewrite, e.g., in `deriv (deriv sin)`.
* Restore some old lemmas
* Restore old `deriv_cos`, fix `deriv_id'`
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix compile
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_id
- \+ *lemma* deriv_id'
- \+ *lemma* deriv_const'
- \+/\- *lemma* deriv_neg
- \+ *lemma* deriv_neg'
- \+/\- *lemma* deriv_pow
- \+ *lemma* deriv_pow'

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* deriv_exp
- \+ *lemma* iter_deriv_exp
- \+/\- *lemma* deriv_sin
- \+/\- *lemma* deriv_cos
- \+ *lemma* deriv_cos'
- \+/\- *lemma* deriv_sinh
- \+/\- *lemma* deriv_cosh



## [2019-12-27 09:41:58](https://github.com/leanprover-community/mathlib/commit/c1a993d)
feat(data/set/intervals): unions of adjacent intervals ([#1827](https://github.com/leanprover-community/mathlib/pull/1827))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* nonempty_Ici
- \+/\- *lemma* nonempty_Iic
- \+ *lemma* nonempty_Ioo
- \+/\- *lemma* Iic_union_Ici
- \+/\- *lemma* Iio_union_Ici
- \+/\- *lemma* Iic_union_Ioi
- \+ *lemma* Ioc_union_Ici_eq_Ioi
- \+ *lemma* Icc_union_Ici_eq_Ioi
- \+ *lemma* Ioo_union_Ici_eq_Ioi
- \+ *lemma* Ico_union_Ici_eq_Ioi
- \+ *lemma* Ioc_union_Ioi_eq_Ioi
- \+ *lemma* Icc_union_Ioi_eq_Ioi
- \+ *lemma* Iic_union_Icc_eq_Iic
- \+ *lemma* Iic_union_Ico_eq_Iio
- \+ *lemma* Iio_union_Icc_eq_Iic
- \+ *lemma* Iio_union_Ico_eq_Iio
- \+ *lemma* Iic_union_Ioc_eq_Iic
- \+ *lemma* Iic_union_Ioo_eq_Iio
- \+ *lemma* Ioc_union_Ico_eq_Ioo
- \+ *lemma* Icc_union_Ico_eq_Ico
- \+ *lemma* Icc_union_Icc_eq_Icc
- \+ *lemma* Ioc_union_Icc_eq_Ioc
- \+ *lemma* Ioo_union_Ico_eq_Ioo
- \+ *lemma* Ico_union_Ico_eq_Ico
- \+ *lemma* Ico_union_Icc_eq_Icc
- \+ *lemma* Ioo_union_Icc_eq_Ioc
- \+ *lemma* Ioc_union_Ioo_eq_Ioo
- \+ *lemma* Icc_union_Ioo_eq_Ico
- \+ *lemma* Icc_union_Ioc_eq_Icc
- \+ *lemma* Ioc_union_Ioc_eq_Ioc



## [2019-12-26 16:34:12](https://github.com/leanprover-community/mathlib/commit/7e2d4b8)
feat(analysis/calculus/extend_deriv): extend differentiability to the boundary ([#1794](https://github.com/leanprover-community/mathlib/pull/1794))
* feat(analysis/calculus/extend_deriv): extend differentiability to the boundary
* fix build
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.union
- \+ *lemma* has_deriv_within_at.congr

Created src/analysis/calculus/extend_deriv.lean
- \+ *lemma* has_deriv_at_interval_left_endpoint_of_tendsto_deriv
- \+ *lemma* has_fderiv_at_interval_right_endpoint_of_tendsto_deriv
- \+ *theorem* has_fderiv_at_boundary_of_tendsto_fderiv_aux
- \+ *theorem* has_fderiv_at_boundary_of_tendsto_fderiv

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.union
- \+ *lemma* has_fderiv_within_at.congr

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_inv_zero_at_top

Modified src/data/set/intervals/basic.lean
- \+ *lemma* Iic_union_Ici
- \+ *lemma* Iio_union_Ici
- \+ *lemma* Iic_union_Ioi



## [2019-12-24 05:40:16](https://github.com/leanprover-community/mathlib/commit/9a9f617)
fix(topology/algebra/infinite_sum): add a hint to speed up elaboration ([#1824](https://github.com/leanprover-community/mathlib/pull/1824))
Fix suggested by Joe on Zulip.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2019-12-23 23:32:58](https://github.com/leanprover-community/mathlib/commit/64921a4)
refactor(topology/*): migrate to `uniform_space.complete_of_convergent_controlled_sequences` ([#1821](https://github.com/leanprover-community/mathlib/pull/1821))
* refactor(topology/*): migrate to `uniform_space.complete_of_convergent_controlled_sequences`
Also rewrite
`uniform_space.complete_of_convergent_controlled_sequences` in terms
of `has_countable_basis`, and add a lemma useful to prove
`l = ⨅ i, f i` for filters.
* Revert some implicit/explicit argument changes
No reason to have them, at least in this PR
* Fix docstrings
* Fix a docstring
* Fix imports
* `cau_seq_filter`: change namespaces, adjust `hensel`
* Fix compile
* Update src/topology/metric_space/cau_seq_filter.lean
* Update src/topology/uniform_space/cauchy.lean
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_numbers.lean


Modified src/order/filter/basic.lean
- \+ *lemma* eq_Inf_of_mem_sets_iff_exists_mem
- \+ *lemma* eq_infi_of_mem_sets_iff_exists_mem
- \+ *lemma* eq_binfi_of_mem_sets_iff_exists_mem

Modified src/topology/bases.lean
- \+ *lemma* has_countable_basis_iff_mono_seq'
- \+ *lemma* has_countable_basis.comap

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.complete_of_convergent_controlled_sequences
- \+ *theorem* metric.complete_of_cauchy_seq_tendsto

Modified src/topology/metric_space/cau_seq_filter.lean
- \+ *lemma* cau_seq.tendsto_limit
- \+ *lemma* cauchy_seq.is_cau_seq
- \+ *lemma* cau_seq.cauchy_seq
- \- *lemma* half_pow_pos
- \- *lemma* half_pow_tendsto_zero
- \- *lemma* half_pow_add_succ
- \- *lemma* half_pow_mono
- \- *lemma* edist_le_two_mul_half_pow
- \- *lemma* cauchy_seq_of_edist_le_half_pow
- \- *lemma* B2_pos
- \- *lemma* B2_lim
- \- *lemma* set_seq_of_cau_filter_mem_sets
- \- *lemma* set_seq_of_cau_filter_inhabited
- \- *lemma* set_seq_of_cau_filter_spec
- \- *lemma* mono_of_mono_succ
- \- *lemma* set_seq_of_cau_filter_monotone'
- \- *lemma* set_seq_of_cau_filter_monotone
- \- *lemma* seq_of_cau_filter_mem_set_seq
- \- *lemma* seq_of_cau_filter_bound
- \- *lemma* seq_of_cau_filter_is_cauchy
- \- *lemma* le_nhds_cau_filter_lim
- \- *lemma* tendsto_limit
- \- *lemma* cauchy_of_filter_cauchy
- \- *lemma* filter_cauchy_of_cauchy
- \- *theorem* complete_of_cauchy_seq_tendsto
- \- *theorem* emetric.complete_of_convergent_controlled_sequences
- \- *theorem* metric.complete_of_convergent_controlled_sequences
- \- *def* set_seq_of_cau_filter

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* uniformity_edist_nnreal
- \+ *theorem* mem_uniformity_edist_inv_nat
- \+ *theorem* uniformity_edist_inv_nat
- \+ *theorem* uniformity_has_countable_basis
- \+ *theorem* complete_of_convergent_controlled_sequences
- \+ *theorem* complete_of_cauchy_seq_tendsto

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *theorem* complete_of_convergent_controlled_sequences



## [2019-12-23 22:13:46](https://github.com/leanprover-community/mathlib/commit/439ac4e)
feat(analysis/calculus/local_extr): Fermat's Theorem, Rolle's Theorem, Lagrange's MVT, Cauchy's MVT ([#1807](https://github.com/leanprover-community/mathlib/pull/1807))
* feat(analysis/calculus/local_extr): Rolle's Theorem, Lagrange's MVT, Cauchy's MVT
* feat(order/filter/extr,topology/algebra/local_extr): local min/max points
This commit contains facts that do not require smooth structure on the domain.
* Rewrite: introduce `is_min_filter`, `pos_tangent_cone_at`.
* Fix compile, move code around
* Drop a TODO, add some docs
* Fix compile
* Fix a typo
* Fix #lint error
* Add some docstrings
* Add some missing lemmas
* Use `differentiable_on`
* Add/rewrite file-level docs, rename some lemmas.
* Update src/analysis/calculus/local_extr.lean
* Update src/order/filter/extr.lean
* Fix a docstring, add Wiki links
* Add refs and tags
* File docstring: provide Lean names of the main lemmas.
* Update src/analysis/calculus/local_extr.lean
* Update src/analysis/calculus/local_extr.lean
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.has_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.has_fderiv_at

Created src/analysis/calculus/local_extr.lean
- \+ *lemma* pos_tangent_cone_at_mono
- \+ *lemma* mem_pos_tangent_cone_at_of_segment_subset
- \+ *lemma* pos_tangent_cone_at_univ
- \+ *lemma* is_local_max_on.has_fderiv_within_at_nonpos
- \+ *lemma* is_local_max_on.fderiv_within_nonpos
- \+ *lemma* is_local_max_on.has_fderiv_within_at_eq_zero
- \+ *lemma* is_local_max_on.fderiv_within_eq_zero
- \+ *lemma* is_local_min_on.has_fderiv_within_at_nonneg
- \+ *lemma* is_local_min_on.fderiv_within_nonneg
- \+ *lemma* is_local_min_on.has_fderiv_within_at_eq_zero
- \+ *lemma* is_local_min_on.fderiv_within_eq_zero
- \+ *lemma* is_local_min.has_fderiv_at_eq_zero
- \+ *lemma* is_local_min.fderiv_eq_zero
- \+ *lemma* is_local_max.has_fderiv_at_eq_zero
- \+ *lemma* is_local_max.fderiv_eq_zero
- \+ *lemma* is_local_extr.has_fderiv_at_eq_zero
- \+ *lemma* is_local_extr.fderiv_eq_zero
- \+ *lemma* is_local_min.has_deriv_at_eq_zero
- \+ *lemma* is_local_min.deriv_eq_zero
- \+ *lemma* is_local_max.has_deriv_at_eq_zero
- \+ *lemma* is_local_max.deriv_eq_zero
- \+ *lemma* is_local_extr.has_deriv_at_eq_zero
- \+ *lemma* is_local_extr.deriv_eq_zero
- \+ *lemma* exists_Ioo_extr_on_Icc
- \+ *lemma* exists_local_extr_Ioo
- \+ *lemma* exists_has_deriv_at_eq_zero
- \+ *lemma* exists_deriv_eq_zero
- \+ *def* pos_tangent_cone_at

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* exists_ratio_has_deriv_at_eq_ratio_slope
- \+ *lemma* exists_has_deriv_at_eq_slope
- \+ *lemma* exists_ratio_deriv_eq_ratio_slope
- \+ *lemma* exists_deriv_eq_slope
- \+ *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \+ *theorem* convex.is_const_of_fderiv_within_eq_zero
- \- *theorem* norm_image_sub_le_of_norm_deriv_le_convex

Modified src/analysis/complex/polynomial.lean


Modified src/order/filter/basic.lean


Created src/order/filter/extr.lean
- \+ *lemma* is_extr_on.elim
- \+ *lemma* is_min_on_iff
- \+ *lemma* is_max_on_iff
- \+ *lemma* is_min_on_univ_iff
- \+ *lemma* is_max_on_univ_iff
- \+ *lemma* is_min_filter.is_extr
- \+ *lemma* is_max_filter.is_extr
- \+ *lemma* is_min_on.is_extr
- \+ *lemma* is_max_on.is_extr
- \+ *lemma* is_min_filter_const
- \+ *lemma* is_max_filter_const
- \+ *lemma* is_extr_filter_const
- \+ *lemma* is_min_on_const
- \+ *lemma* is_max_on_const
- \+ *lemma* is_extr_on_const
- \+ *lemma* is_min_filter_dual_iff
- \+ *lemma* is_max_filter_dual_iff
- \+ *lemma* is_extr_filter_dual_iff
- \+ *lemma* is_min_on_dual_iff
- \+ *lemma* is_max_on_dual_iff
- \+ *lemma* is_extr_on_dual_iff
- \+ *lemma* is_min_filter.filter_mono
- \+ *lemma* is_max_filter.filter_mono
- \+ *lemma* is_extr_filter.filter_mono
- \+ *lemma* is_min_filter.filter_inf
- \+ *lemma* is_max_filter.filter_inf
- \+ *lemma* is_extr_filter.filter_inf
- \+ *lemma* is_min_on.on_subset
- \+ *lemma* is_max_on.on_subset
- \+ *lemma* is_extr_on.on_subset
- \+ *lemma* is_min_on.inter
- \+ *lemma* is_max_on.inter
- \+ *lemma* is_extr_on.inter
- \+ *lemma* is_min_filter.comp_mono
- \+ *lemma* is_max_filter.comp_mono
- \+ *lemma* is_extr_filter.comp_mono
- \+ *lemma* is_min_filter.comp_antimono
- \+ *lemma* is_max_filter.comp_antimono
- \+ *lemma* is_extr_filter.comp_antimono
- \+ *lemma* is_min_on.comp_mono
- \+ *lemma* is_max_on.comp_mono
- \+ *lemma* is_extr_on.comp_mono
- \+ *lemma* is_min_on.comp_antimono
- \+ *lemma* is_max_on.comp_antimono
- \+ *lemma* is_extr_on.comp_antimono
- \+ *lemma* is_min_filter.bicomp_mono
- \+ *lemma* is_max_filter.bicomp_mono
- \+ *lemma* is_min_on.bicomp_mono
- \+ *lemma* is_max_on.bicomp_mono
- \+ *lemma* is_min_filter.comp_tendsto
- \+ *lemma* is_max_filter.comp_tendsto
- \+ *lemma* is_extr_filter.comp_tendsto
- \+ *lemma* is_min_on.on_preimage
- \+ *lemma* is_max_on.on_preimage
- \+ *lemma* is_extr_on.on_preimage
- \+ *lemma* is_min_filter.add
- \+ *lemma* is_max_filter.add
- \+ *lemma* is_min_on.add
- \+ *lemma* is_max_on.add
- \+ *lemma* is_min_filter.neg
- \+ *lemma* is_max_filter.neg
- \+ *lemma* is_extr_filter.neg
- \+ *lemma* is_min_on.neg
- \+ *lemma* is_max_on.neg
- \+ *lemma* is_extr_on.neg
- \+ *lemma* is_min_filter.sub
- \+ *lemma* is_max_filter.sub
- \+ *lemma* is_min_on.sub
- \+ *lemma* is_max_on.sub
- \+ *lemma* is_min_filter.sup
- \+ *lemma* is_max_filter.sup
- \+ *lemma* is_min_on.sup
- \+ *lemma* is_max_on.sup
- \+ *lemma* is_min_filter.inf
- \+ *lemma* is_max_filter.inf
- \+ *lemma* is_min_on.inf
- \+ *lemma* is_max_on.inf
- \+ *lemma* is_min_filter.min
- \+ *lemma* is_max_filter.min
- \+ *lemma* is_min_on.min
- \+ *lemma* is_max_on.min
- \+ *lemma* is_min_filter.max
- \+ *lemma* is_max_filter.max
- \+ *lemma* is_min_on.max
- \+ *lemma* is_max_on.max
- \+ *def* is_min_filter
- \+ *def* is_max_filter
- \+ *def* is_extr_filter
- \+ *def* is_min_on
- \+ *def* is_max_on
- \+ *def* is_extr_on

Modified src/topology/algebra/ordered.lean


Created src/topology/local_extr.lean
- \+ *lemma* is_local_extr_on.elim
- \+ *lemma* is_local_extr.elim
- \+ *lemma* is_local_min.on
- \+ *lemma* is_local_max.on
- \+ *lemma* is_local_extr.on
- \+ *lemma* is_local_min_on.on_subset
- \+ *lemma* is_local_max_on.on_subset
- \+ *lemma* is_local_extr_on.on_subset
- \+ *lemma* is_local_min_on.inter
- \+ *lemma* is_local_max_on.inter
- \+ *lemma* is_local_extr_on.inter
- \+ *lemma* is_min_on.localize
- \+ *lemma* is_max_on.localize
- \+ *lemma* is_extr_on.localize
- \+ *lemma* is_local_min_on.is_local_min
- \+ *lemma* is_local_max_on.is_local_max
- \+ *lemma* is_local_extr_on.is_local_extr
- \+ *lemma* is_min_on.is_local_min
- \+ *lemma* is_max_on.is_local_max
- \+ *lemma* is_extr_on.is_local_extr
- \+ *lemma* is_local_min_on_const
- \+ *lemma* is_local_max_on_const
- \+ *lemma* is_local_extr_on_const
- \+ *lemma* is_local_min_const
- \+ *lemma* is_local_max_const
- \+ *lemma* is_local_extr_const
- \+ *lemma* is_local_min.comp_mono
- \+ *lemma* is_local_max.comp_mono
- \+ *lemma* is_local_extr.comp_mono
- \+ *lemma* is_local_min.comp_antimono
- \+ *lemma* is_local_max.comp_antimono
- \+ *lemma* is_local_extr.comp_antimono
- \+ *lemma* is_local_min_on.comp_mono
- \+ *lemma* is_local_max_on.comp_mono
- \+ *lemma* is_local_extr_on.comp_mono
- \+ *lemma* is_local_min_on.comp_antimono
- \+ *lemma* is_local_max_on.comp_antimono
- \+ *lemma* is_local_extr_on.comp_antimono
- \+ *lemma* is_local_min.bicomp_mono
- \+ *lemma* is_local_max.bicomp_mono
- \+ *lemma* is_local_min_on.bicomp_mono
- \+ *lemma* is_local_max_on.bicomp_mono
- \+ *lemma* is_local_min.comp_continuous
- \+ *lemma* is_local_max.comp_continuous
- \+ *lemma* is_local_extr.comp_continuous
- \+ *lemma* is_local_min.comp_continuous_on
- \+ *lemma* is_local_max.comp_continuous_on
- \+ *lemma* is_local_extr.comp_continuous_on
- \+ *lemma* is_local_min.add
- \+ *lemma* is_local_max.add
- \+ *lemma* is_local_min_on.add
- \+ *lemma* is_local_max_on.add
- \+ *lemma* is_local_min.neg
- \+ *lemma* is_local_max.neg
- \+ *lemma* is_local_extr.neg
- \+ *lemma* is_local_min_on.neg
- \+ *lemma* is_local_max_on.neg
- \+ *lemma* is_local_extr_on.neg
- \+ *lemma* is_local_min.sub
- \+ *lemma* is_local_max.sub
- \+ *lemma* is_local_min_on.sub
- \+ *lemma* is_local_max_on.sub
- \+ *lemma* is_local_min.sup
- \+ *lemma* is_local_max.sup
- \+ *lemma* is_local_min_on.sup
- \+ *lemma* is_local_max_on.sup
- \+ *lemma* is_local_min.inf
- \+ *lemma* is_local_max.inf
- \+ *lemma* is_local_min_on.inf
- \+ *lemma* is_local_max_on.inf
- \+ *lemma* is_local_min.min
- \+ *lemma* is_local_max.min
- \+ *lemma* is_local_min_on.min
- \+ *lemma* is_local_max_on.min
- \+ *lemma* is_local_min.max
- \+ *lemma* is_local_max.max
- \+ *lemma* is_local_min_on.max
- \+ *lemma* is_local_max_on.max
- \+ *def* is_local_min_on
- \+ *def* is_local_max_on
- \+ *def* is_local_extr_on
- \+ *def* is_local_min
- \+ *def* is_local_max
- \+ *def* is_local_extr

Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2019-12-20 20:34:56](https://github.com/leanprover-community/mathlib/commit/883d974)
feat(algebra/module): sum_smul' (for semimodules) ([#1752](https://github.com/leanprover-community/mathlib/pull/1752))
* feat(algebra/module): sum_smul' (for semimodules)
* adding docstring
* use `classical` tactic
* moving ' name to the weaker theorem
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_smul'
- \- *lemma* sum_smul

Modified src/algebra/module.lean
- \+ *lemma* finset.sum_smul



## [2019-12-19 06:24:53](https://github.com/leanprover-community/mathlib/commit/e875492)
chore(algebra/module) remove an unneeded commutativity assumption ([#1813](https://github.com/leanprover-community/mathlib/pull/1813))
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map_smul'



## [2019-12-18 12:57:28](https://github.com/leanprover-community/mathlib/commit/5dae5d2)
chore(ring_theory/algebra): redefine module structure of Z-algebra instance ([#1812](https://github.com/leanprover-community/mathlib/pull/1812))
This redefines the Z-algebra instance, so that the module structure is definitionally equal to the Z-module structure of any `add_comm_group`
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2019-12-18 09:23:47](https://github.com/leanprover-community/mathlib/commit/bec46af)
refactor(topology/*): use dot notation with `compact`, prove `compact.image` with `continuous_on` ([#1809](https://github.com/leanprover-community/mathlib/pull/1809))
* refactor(topology/*): use dot notation, prove `compact.image` with `continuous_on`
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix compile, update some proofs
* Make `range_quot_mk` a `simp` lemma
* Fix lint errors
#### Estimated changes
Modified src/analysis/complex/polynomial.lean


Modified src/data/set/basic.lean
- \+ *theorem* range_inl_union_range_inr
- \+ *theorem* range_quot_mk

Modified src/measure_theory/lebesgue_measure.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* map_mono
- \+/\- *lemma* comap_mono
- \+ *lemma* comap_ne_bot_of_range_mem
- \+ *lemma* comap_inf_principal_ne_bot_of_image_mem
- \+/\- *lemma* comap_neq_bot_of_surj
- \+ *lemma* map_inf_le
- \+/\- *lemma* map_inf
- \+ *lemma* tendsto.ne_bot
- \+ *lemma* tendsto.inf
- \- *lemma* monotone_map
- \- *lemma* monotone_comap

Modified src/order/filter/lift.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* compact.exists_forall_le
- \+ *lemma* compact.exists_forall_ge
- \- *lemma* exists_forall_le_of_compact_of_continuous
- \- *lemma* exists_forall_ge_of_compact_of_continuous

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_ne_bot_of_mem
- \+ *lemma* is_closed.mem_of_nhds_within_ne_bot

Modified src/topology/homeomorph.lean


Modified src/topology/instances/complex.lean
- \+/\- *def* real_prod_homeo

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* compact.inter_right
- \+ *lemma* compact.inter_left
- \+ *lemma* compact.adherence_nhdset
- \+ *lemma* compact.elim_finite_subcover
- \+ *lemma* compact.elim_finite_subcover_image
- \+ *lemma* set.finite.compact_bUnion
- \+ *lemma* compact_Union
- \+ *lemma* set.finite.compact
- \+ *lemma* compact.union
- \+ *lemma* is_closed.compact
- \+ *lemma* compact.image_of_continuous_on
- \+ *lemma* compact.image
- \+ *lemma* embedding.compact_iff_compact_image
- \+ *lemma* compact.prod
- \- *lemma* compact_inter
- \- *lemma* compact_adherence_nhdset
- \- *lemma* compact_elim_finite_subcover
- \- *lemma* compact_elim_finite_subcover_image
- \- *lemma* compact_bUnion_of_compact
- \- *lemma* compact_Union_of_compact
- \- *lemma* compact_of_finite
- \- *lemma* compact_union_of_compact
- \- *lemma* compact_of_closed
- \- *lemma* compact_image
- \- *lemma* compact_iff_compact_image_of_embedding
- \- *lemma* compact_prod

Modified src/topology/uniform_space/basic.lean




## [2019-12-18 06:01:42](https://github.com/leanprover-community/mathlib/commit/1207518)
feat(*): add command for declaring library notes ([#1810](https://github.com/leanprover-community/mathlib/pull/1810))
* feat(*): add command for declaring library notes
* add missing file
* make note names private
* update docs
* Update library_note.lean
* Update library_note.lean
#### Estimated changes
Modified docs/tactics.md
- \+ *def* f

Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/module.lean


Modified src/category_theory/limits/preserves.lean


Modified src/group_theory/coset.lean


Modified src/logic/basic.lean


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Created src/tactic/library_note.lean
- \+ *def* string.hash

Modified src/tactic/lint.lean


Modified src/tactic/localized.lean
- \- *def* string_hash



## [2019-12-17 22:12:07](https://github.com/leanprover-community/mathlib/commit/acdf272)
chore(data/fintype): use `list.fin_range` for `fin.fintype` ([#1811](https://github.com/leanprover-community/mathlib/pull/1811))
#### Estimated changes
Modified src/data/fintype.lean


Modified src/data/list/basic.lean




## [2019-12-17 18:02:26](https://github.com/leanprover-community/mathlib/commit/52e1872)
refactor(topology/algebra/ordered): prove IVT for a connected set ([#1806](https://github.com/leanprover-community/mathlib/pull/1806))
* refactor(topology/algebra/ordered): prove IVT for a connected set
Also prove that intervals are connected, and deduce the classical IVT
from this.
* Rewrite the proof, move `min_le_max` to the root namespace
* Adjust `analysis/complex/exponential`
* Add comments/`obtain`
* Add some docs
* Add more docs
* Move some proofs to a section with weaker running assumptions
* Remove empty lines, fix a docstring
* +1 docstring
#### Estimated changes
Modified src/algebra/order.lean
- \- *lemma* min_le_max

Modified src/algebra/order_functions.lean
- \+ *lemma* min_le_max

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* exists_cos_eq_zero
- \+/\- *lemma* exists_sin_eq

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_connected.forall_Icc_subset
- \+ *lemma* is_connected.intermediate_value
- \+ *lemma* intermediate_value_univ
- \+ *lemma* is_connected_Icc
- \+ *lemma* is_connected_iff_forall_Icc_subset
- \+ *lemma* is_connected_Ici
- \+ *lemma* is_connected_Iic
- \+ *lemma* is_connected_Iio
- \+ *lemma* is_connected_Ioi
- \+ *lemma* is_connected_Ioo
- \+ *lemma* is_connected_Ioc
- \+ *lemma* is_connected_Ico
- \+ *lemma* intermediate_value_Icc
- \+ *lemma* intermediate_value_Icc'

Modified src/topology/instances/real.lean
- \- *lemma* real.intermediate_value
- \- *lemma* real.intermediate_value'

Modified src/topology/subset_properties.lean
- \+ *theorem* is_connected_of_forall
- \+ *theorem* is_connected_of_forall_pair
- \+ *theorem* is_connected.union
- \+ *theorem* is_connected.closure
- \+ *theorem* is_connected.image
- \+ *theorem* is_connected_closed_iff
- \- *theorem* is_connected_union
- \- *theorem* is_connected_closure



## [2019-12-17 14:48:50](https://github.com/leanprover-community/mathlib/commit/d8dc144)
feat(geometry/manifold): smooth bundles, tangent bundle ([#1607](https://github.com/leanprover-community/mathlib/pull/1607))
* feat(geometry/manifold): smooth bundles, tangent bundle
* remove decidable in preamble
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/geometry/manifold/basic_smooth_bundle.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* comments
* cleanup
* oops, forgot squeeze_simp
* simpa instead of simp
* oops
* much better docstrings
* improved formatting
* space after forall
* fix build
* fix build, continuous.smul
* minor improvements
#### Estimated changes
Modified src/algebra/module.lean


Modified src/analysis/convex.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/operator_norm.lean


Created src/geometry/manifold/basic_smooth_bundle.lean
- \+ *lemma* base_set
- \+ *lemma* chart_source
- \+ *lemma* chart_target
- \+ *lemma* mem_atlas_iff
- \+ *lemma* mem_chart_source_iff
- \+ *lemma* mem_chart_target_iff
- \+ *lemma* chart_at_to_fun_fst
- \+ *lemma* chart_at_inv_fun_fst
- \+ *lemma* tangent_bundle_proj_continuous
- \+ *lemma* tangent_bundle_proj_open
- \+ *lemma* tangent_bundle_model_space_chart_at
- \+ *lemma* tangent_bundle_model_space_topology_eq_prod
- \+ *def* to_topological_fiber_bundle_core
- \+ *def* chart
- \+ *def* tangent_bundle_core
- \+ *def* tangent_bundle
- \+ *def* tangent_bundle.proj
- \+ *def* tangent_space

Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_smul
- \+ *lemma* continuous.smul
- \- *lemma* continuous_smul'

Modified src/topology/topological_fiber_bundle.lean




## [2019-12-17 13:38:54](https://github.com/leanprover-community/mathlib/commit/308a08c)
refactor(topology/metric_space/closeds): migrate to `cauchy_seq_of_edist_le_geometric_two` ([#1760](https://github.com/leanprover-community/mathlib/pull/1760))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile
* Rewrite `cauchy_seq_of_edist_le_geometric` etc in terms of `ennreal`s
I tried to actually use `nnreal`s, and it leads to coercions nightmare.
* Simplify some proofs using new lemmas
* Fix compile
* Fix compile
* refactor(topology/metric_space/closeds): migrate to `cauchy_seq_of_edist_le_geometric_two`
#### Estimated changes
Modified src/topology/metric_space/closeds.lean




## [2019-12-17 08:52:57](https://github.com/leanprover-community/mathlib/commit/3053a16)
feat(tactic/field_simp): tactic to reduce to one division in fields ([#1792](https://github.com/leanprover-community/mathlib/pull/1792))
* feat(algebra/field): simp set to reduce to one division in fields
* tactic field_simp
* fix docstring
* fix build
#### Estimated changes
Modified docs/tactics.md


Modified src/algebra/char_zero.lean
- \+/\- *lemma* two_ne_zero'

Modified src/algebra/field.lean
- \+ *lemma* div_eq_iff
- \+ *lemma* eq_div_iff
- \+ *lemma* add_div'
- \+ *lemma* div_add'
- \+ *lemma* mul_div_assoc'
- \+ *lemma* neg_div'

Modified src/algebra/group_power.lean
- \+/\- *lemma* inv_pow'
- \+ *lemma* pow_div
- \+/\- *theorem* pow_ne_zero

Modified src/data/real/nnreal.lean


Modified src/field_theory/perfect_closure.lean


Modified src/tactic/interactive.lean


Modified test/ring.lean


Modified test/ring_exp.lean




## [2019-12-17 07:44:28](https://github.com/leanprover-community/mathlib/commit/abea298)
refactor(analysis/specific_limits): use `ennreal`s instead of `nnreal`s in `*_edist_le_geometric` ([#1759](https://github.com/leanprover-community/mathlib/pull/1759))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile
* Rewrite `cauchy_seq_of_edist_le_geometric` etc in terms of `ennreal`s
I tried to actually use `nnreal`s, and it leads to coercions nightmare.
* Simplify some proofs using new lemmas
* Fix compile
* Fix compile
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* nnreal.has_sum_geometric
- \+ *lemma* nnreal.summable_geometric
- \+ *lemma* ennreal.tsum_geometric
- \+ *lemma* cauchy_seq_of_edist_le_geometric_two
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \- *lemma* has_sum_geometric_nnreal
- \- *lemma* summable_geometric_nnreal

Modified src/topology/instances/ennreal.lean
- \+ *lemma* cauchy_seq_of_edist_le_of_tsum_ne_top
- \+/\- *lemma* edist_le_tsum_of_edist_le_of_tendsto
- \+/\- *lemma* edist_le_tsum_of_edist_le_of_tendsto₀

Modified src/topology/metric_space/cau_seq_filter.lean




## [2019-12-16 14:15:11](https://github.com/leanprover-community/mathlib/commit/cd53e27)
chore(topology/algebra/ordered): use interval notation here and there ([#1802](https://github.com/leanprover-community/mathlib/pull/1802))
* chore(topology/algebra/ordered): use interval notation here and there
Also prove a slightly more general version of `mem_nhds_orderable_dest`
* Fix a few compile errors
* Rename a lemma, fix compile, add docs and `dual_I??` lemmas
* Fix names, add comments
* Make some lemmas simp
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* dual_Ici
- \+ *lemma* dual_Iic
- \+ *lemma* dual_Ioi
- \+ *lemma* dual_Iio
- \+ *lemma* dual_Icc
- \+ *lemma* dual_Ioc
- \+ *lemma* dual_Ico
- \+ *lemma* dual_Ioo
- \+/\- *lemma* nonempty_Icc
- \+/\- *lemma* nonempty_Ico
- \+/\- *lemma* nonempty_Ioc
- \+ *lemma* Ici_subset_Ioi
- \+ *lemma* Iic_subset_Iio

Modified src/measure_theory/borel_space.lean


Modified src/order/basic.lean


Modified src/order/filter/basic.lean
- \+ *lemma* binfi_sets_eq
- \+ *lemma* mem_binfi
- \- *lemma* infi_sets_eq'

Modified src/order/filter/lift.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* closure_lt_subset_le
- \+/\- *lemma* is_open_Ioo
- \+/\- *lemma* nhds_eq_orderable
- \+ *lemma* exists_Ioc_subset_of_mem_nhds'
- \+ *lemma* exists_Ico_subset_of_mem_nhds'
- \+ *lemma* exists_Ioc_subset_of_mem_nhds
- \+ *lemma* exists_Ico_subset_of_mem_nhds
- \- *lemma* mem_nhds_orderable_dest

Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/instances/ennreal.lean




## [2019-12-16 10:20:01](https://github.com/leanprover-community/mathlib/commit/de25b10)
refactor(analysis/convex): simplify proofs, use implicit args and  dot notation ([#1804](https://github.com/leanprover-community/mathlib/pull/1804))
* feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc`
* refactor(analysis/convex): simplify proofs, use implicit args and  dot notation
* Use dot notation.
* Swap LHS and RHS of `image_Icc_zero_one_eq_segment`.
* Introduce `finset.center_mass`, prove basic properties.
* Deduce Jensen's inequality from the corresponding property of convex
  sets; rename corresponding lemmas.
* Fix a typo
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/convex.lean
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_pair

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/convex.lean
- \+/\- *lemma* left_mem_segment
- \+/\- *lemma* right_mem_segment
- \+ *lemma* segment_eq_image_Icc_zero_one
- \+ *lemma* segment_eq_image_Icc_zero_one'
- \+ *lemma* segment_eq_Icc'
- \+/\- *lemma* segment_translate
- \+ *lemma* segment_translate_preimage
- \+/\- *lemma* segment_translate_image
- \+ *lemma* convex.inter
- \+ *lemma* convex_sInter
- \+/\- *lemma* convex_Inter
- \+ *lemma* convex.prod
- \+ *lemma* convex.is_linear_image
- \+ *lemma* convex.linear_image
- \+ *lemma* convex.is_linear_preimage
- \+ *lemma* convex.linear_preimage
- \+ *lemma* convex.neg
- \+ *lemma* convex.neg_preimage
- \+ *lemma* convex.smul
- \+ *lemma* convex.smul_preimage
- \+ *lemma* convex.add
- \+ *lemma* convex.sub
- \+ *lemma* convex.translate
- \+ *lemma* convex.affinity
- \+ *lemma* convex_real_iff
- \+/\- *lemma* convex_Iio
- \+/\- *lemma* convex_Iic
- \+/\- *lemma* convex_halfspace_lt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_gt
- \+/\- *lemma* convex_halfspace_ge
- \+ *lemma* convex_hyperplane
- \+ *lemma* submodule.convex
- \+ *lemma* subspace.convex
- \+/\- *lemma* convex_on_linorder
- \+ *lemma* convex_on.subset
- \+ *lemma* convex_on.add
- \+ *lemma* convex_on.smul
- \+ *lemma* convex_on.le_on_interval
- \+ *lemma* convex_on.convex_le
- \+ *lemma* convex_on.convex_lt
- \+ *lemma* convex_on.convex_epigraph
- \+ *lemma* convex_on_iff_convex_epigraph
- \+ *lemma* finset.center_mass_empty
- \+ *lemma* finset.center_mass_insert
- \+ *lemma* finset.center_mass_singleton
- \+ *lemma* finset.center_mass_pair
- \+ *lemma* convex.center_mass_mem
- \+ *lemma* convex.sum_mem
- \+ *lemma* convex_iff_sum_mem
- \+ *lemma* convex_on.map_center_mass_le
- \+ *lemma* convex_on.map_sum_le
- \+ *lemma* convex.interior
- \+ *lemma* convex.closure
- \- *lemma* image_Icc_zero_one_eq_segment
- \- *lemma* convex_inter
- \- *lemma* convex_prod
- \- *lemma* convex_linear_image
- \- *lemma* convex_linear_image'
- \- *lemma* convex_linear_preimage
- \- *lemma* convex_linear_preimage'
- \- *lemma* convex_neg
- \- *lemma* convex_neg_preimage
- \- *lemma* convex_smul
- \- *lemma* convex_smul_preimage
- \- *lemma* convex_add
- \- *lemma* convex_sub
- \- *lemma* convex_translation
- \- *lemma* convex_affinity
- \- *lemma* convex_halfplane
- \- *lemma* convex_submodule
- \- *lemma* convex_subspace
- \- *lemma* convex_sum
- \- *lemma* convex_sum_iff
- \- *lemma* convex_on_sum
- \- *lemma* convex_on_subset
- \- *lemma* convex_on_add
- \- *lemma* convex_on_smul
- \- *lemma* convex_le_of_convex_on
- \- *lemma* convex_lt_of_convex_on
- \- *lemma* le_on_interval_of_convex_on
- \- *lemma* convex_interior
- \- *lemma* convex_closure
- \+/\- *def* segment

Modified src/analysis/normed_space/real_inner_product.lean




## [2019-12-16 08:11:28](https://github.com/leanprover-community/mathlib/commit/6188b99)
feat(topology/instances/ennreal): more lemmas about tsum ([#1756](https://github.com/leanprover-community/mathlib/pull/1756))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
* feat(topology/instances/ennreal): more lemmas
* Fix compile
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* tendsto_coe
- \+ *lemma* tendsto_nat_nhds_top
- \+ *lemma* tsum_coe_ne_top_iff_summable



## [2019-12-16 07:01:34](https://github.com/leanprover-community/mathlib/commit/ee981c2)
refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter ([#1805](https://github.com/leanprover-community/mathlib/pull/1805))
* refactor(analysis/calculus/fderiv): prove `has_fderiv_within_at.lim` for any filter
Also prove two versions of "directional derivative agrees with
`has_fderiv_at`": `has_fderiv_at.lim` and `has_fderiv_at.lim_real`.
* Rename a lemma as suggested by @sgouezel
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.lim
- \+ *lemma* has_fderiv_at.lim_real
- \+/\- *theorem* has_fderiv_within_at.lim
- \+/\- *theorem* has_fderiv_at_filter_real_equiv

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_at.lim_zero

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* ne_mem_of_tendsto_norm_at_top



## [2019-12-15 22:29:01](https://github.com/leanprover-community/mathlib/commit/699da42)
feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc` ([#1803](https://github.com/leanprover-community/mathlib/pull/1803))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \- *lemma* ivl_translate
- \- *lemma* ivl_stretch

Modified src/data/set/basic.lean
- \+/\- *lemma* inter_singleton_ne_empty
- \+ *theorem* nonempty.image_const

Modified src/data/set/intervals/basic.lean
- \+ *lemma* nonempty_Icc
- \+ *lemma* nonempty_Ico
- \+ *lemma* nonempty_Ioc
- \+ *lemma* nonempty_Ici
- \+ *lemma* nonempty_Iic
- \+ *lemma* image_add_left_Icc
- \+ *lemma* image_add_right_Icc
- \+ *lemma* image_mul_right_Icc'
- \+ *lemma* image_mul_right_Icc
- \+ *lemma* image_mul_left_Icc'
- \+ *lemma* image_mul_left_Icc



## [2019-12-15 21:28:53](https://github.com/leanprover-community/mathlib/commit/7cda8bb)
feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic ([#1754](https://github.com/leanprover-community/mathlib/pull/1754))
* feat(data/real/ennreal): more lemmas, `*_cast` tags, use `lift` tactic
* Undo name change
* Fix compile
* nnreal: add `move_cast`
* ennreal: more lemmas
* Fix compile
#### Estimated changes
Modified src/analysis/specific_limits.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* to_nnreal_coe
- \+ *lemma* coe_two
- \+ *lemma* one_lt_two
- \+ *lemma* two_pos
- \+ *lemma* two_ne_zero
- \+ *lemma* two_ne_top
- \+ *lemma* top_pow
- \+ *lemma* mul_ne_top
- \+ *lemma* pow_eq_top
- \+ *lemma* pow_ne_top
- \+ *lemma* pow_lt_top
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* zero_lt_coe_iff
- \+/\- *lemma* one_le_coe_iff
- \+/\- *lemma* coe_le_one_iff
- \+/\- *lemma* coe_lt_one_iff
- \+/\- *lemma* one_lt_coe_iff
- \+/\- *lemma* coe_nat
- \+ *lemma* max_eq_zero_iff
- \+ *lemma* coe_nat_lt_coe
- \+ *lemma* coe_lt_coe_nat
- \+ *lemma* coe_nat_lt_coe_nat
- \+ *lemma* coe_nat_ne_top
- \+ *lemma* mul_le_mul
- \+ *lemma* mul_left_mono
- \+ *lemma* mul_right_mono
- \+ *lemma* max_mul
- \+ *lemma* mul_max
- \+ *lemma* mul_eq_mul_right
- \+ *lemma* mul_le_mul_right
- \+ *lemma* mul_lt_mul_left
- \+ *lemma* mul_lt_mul_right
- \+ *lemma* coe_sub_infty
- \+ *lemma* le_sub_add_self
- \+ *lemma* sub_eq_of_add_eq
- \+ *lemma* sub_le_sub_add_sub
- \+ *lemma* sub_mul
- \+ *lemma* mul_sub
- \+ *lemma* coe_inv_two
- \+/\- *lemma* coe_div
- \+ *lemma* inv_one
- \+ *lemma* inv_lt_one
- \+ *lemma* top_div
- \+ *lemma* div_top
- \+ *lemma* zero_div
- \+/\- *lemma* mul_inv_cancel
- \+ *lemma* inv_mul_cancel
- \+ *lemma* mul_le_iff_le_inv
- \+/\- *lemma* div_self
- \+ *lemma* mul_div_cancel
- \+ *lemma* mul_div_cancel'
- \+ *lemma* inv_two_add_inv_two
- \+ *lemma* one_half_lt_one
- \+ *lemma* sub_half
- \+ *lemma* one_sub_inv_two
- \- *lemma* mul_le_if_le_inv

Modified src/data/real/nnreal.lean
- \+ *lemma* inv_one
- \+ *lemma* two_inv_lt_one



## [2019-12-15 19:32:42](https://github.com/leanprover-community/mathlib/commit/871a36f)
feat(group_theory/monoid_localization) add localizations of commutative monoids at submonoids ([#1798](https://github.com/leanprover-community/mathlib/pull/1798))
* 1st half of monoid_localization
* change in implementation notes
* fixing naming clashes
* change additive version's name
* oops, had a /- instead of /--
* generalize comm_monoid instance
* remove notes to self
* responding to PR comments
#### Estimated changes
Modified src/group_theory/congruence.lean
- \+/\- *def* ker_lift

Created src/group_theory/monoid_localization.lean
- \+ *lemma* r'.transitive
- \+ *lemma* r'.add
- \+ *lemma* one_rel
- \+ *lemma* exists_rep
- \+ *lemma* mk_eq_of_eq
- \+ *lemma* mk_self'
- \+ *lemma* mk_self
- \+ *lemma* mk_mul_mk
- \+ *lemma* lift_on_beta
- \+ *lemma* of_ker_iff
- \+ *lemma* of_eq_mk
- \+ *lemma* of_mul_mk
- \+ *lemma* mk_eq_mul_mk_one
- \+ *lemma* mk_mul_cancel_right
- \+ *lemma* mk_mul_cancel_left
- \+ *lemma* to_units_mk
- \+ *lemma* mk_is_unit
- \+ *lemma* mk_is_unit'
- \+ *lemma* to_units_inv
- \+ *lemma* of_is_unit
- \+ *lemma* of_is_unit'
- \+ *lemma* to_units_map_inv
- \+ *lemma* mk_eq
- \+ *lemma* is_unit_of_of_comp
- \+ *lemma* units_restrict_mul
- \+ *lemma* r_le_ker_aux
- \+ *lemma* lift'_mk
- \+ *lemma* lift_mk
- \+ *lemma* lift'_of
- \+ *lemma* lift_of
- \+ *lemma* lift'_eq_iff
- \+ *lemma* lift_eq_iff
- \+ *lemma* mk_eq_iff_of_eq
- \+ *lemma* lift'_comp_of
- \+ *lemma* lift_comp_of
- \+ *lemma* lift'_apply_of
- \+ *lemma* lift_apply_of
- \+ *lemma* map_eq
- \+ *lemma* map_of
- \+ *lemma* map_comp_of
- \+ *lemma* map_mk
- \+ *lemma* map_id
- \+ *lemma* map_comp_map
- \+ *lemma* map_map
- \+ *lemma* map_ext
- \+ *theorem* r_eq_r'
- \+ *theorem* ind
- \+ *theorem* induction_on
- \+ *def* r
- \+ *def* r'
- \+ *def* monoid_localization
- \+ *def* mk
- \+ *def* of
- \+ *def* to_units
- \+ *def* units_restrict
- \+ *def* aux
- \+ *def* lift'
- \+ *def* map



## [2019-12-15 17:52:56](https://github.com/leanprover-community/mathlib/commit/7dfbcdd)
(docs/tactics.md) adding `norm_num` [ci skip] ([#1799](https://github.com/leanprover-community/mathlib/pull/1799))
* (docs/tactics.md) adding `norm_num` [ci skip]
* fixing example
* clarifying explanation, adding more examples
* one more example
* one more example
* editing norm_num docstring
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/norm_num.lean




## [2019-12-15 16:39:49](https://github.com/leanprover-community/mathlib/commit/9a37e3f)
refactor(*): make vector_space an abbreviation for module ([#1793](https://github.com/leanprover-community/mathlib/pull/1793))
* refactor(*): make vector_space an abbreviation for module
* Remove superfluous instances
* Fix build
* Add Note[vector space definition]
* Update src/algebra/module.lean
* Fix build (hopefully)
* Update src/measure_theory/bochner_integration.lean
#### Estimated changes
Modified src/algebra/module.lean


Modified src/algebra/pi_instances.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/linear_algebra/basic.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/ring_theory/algebra.lean




## [2019-12-13 22:04:36](https://github.com/leanprover-community/mathlib/commit/a3844c8)
chore(algebra/group/basic): DRY, add `mul_left_surjective` ([#1801](https://github.com/leanprover-community/mathlib/pull/1801))
Some lemmas explicitly listed arguments already declared using
`variables`, remove them.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *lemma* mul_left_eq_self
- \+/\- *lemma* mul_right_eq_self



## [2019-12-13 18:10:30+01:00](https://github.com/leanprover-community/mathlib/commit/bb7d4c9)
chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range` ([#1800](https://github.com/leanprover-community/mathlib/pull/1800))
* chore(data/set/lattice): drop `Union_eq_sUnion_range` and `Inter_eq_sInter_range`
Two reasons:
* we already have `sUnion_range` and `sInter_range`, no need to repeat
  ourselves;
* proofs used wrong universes.
* Try to fix compile
#### Estimated changes
Modified src/data/set/lattice.lean
- \- *theorem* Union_eq_sUnion_range
- \- *theorem* Inter_eq_sInter_range

Modified src/set_theory/cofinality.lean




## [2019-12-12 21:45:20](https://github.com/leanprover-community/mathlib/commit/3281698)
feat(data/padics/padic_integers): algebra structure Z_p -> Q_p ([#1796](https://github.com/leanprover-community/mathlib/pull/1796))
* feat(data/padics/padic_integers): algebra structure Z_p -> Q_p
* Update src/data/padics/padic_integers.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* Fix build
#### Estimated changes
Modified src/data/padics/padic_integers.lean




## [2019-12-12 09:05:22](https://github.com/leanprover-community/mathlib/commit/69e861e)
feat(measure_theory/bochner_integration): connecting the Bochner integral with the integral on `ennreal`-valued functions ([#1790](https://github.com/leanprover-community/mathlib/pull/1790))
* shorter proof
* feat(measure_theory/bochner_integration): connecting the Bochner integral with the integral on `ennreal`
This PR proves that `∫ f = ∫ f⁺ - ∫ f⁻`, with the first integral sign being the Bochner integral of a real-valued function `f : α → ℝ`, and second and third integral sign being the integral on `ennreal`-valued functions. See `integral_eq_lintegral_max_sub_lintegral_min`.
I feel that most of the basic properties of the Bochner integral are proved. Please let me know if you think something else is needed.
* various things :
* add guides for typeclass inference;
* add `norm_cast` tags;
* prove some corollaries;
* add doc strings;
* other fixes
* Update bochner_integration.lean
* add some doc strings
* Fix doc strings
* Update bochner_integration.lean
* Update bochner_integration.lean
* fix doc strings
* Update bochner_integration.lean
* Use dot notation
* use dot notation
* Update Meas.lean
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_zero_sub_eq_self
- \+ *lemma* abs_max_sub_max_le_abs

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* neg_mk
- \+ *lemma* pos_part_to_fun
- \+ *def* pos_part

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* pos_part_map_norm
- \+ *lemma* neg_part_map_norm
- \+ *lemma* pos_part_sub_neg_part
- \+ *lemma* bintegral_neg
- \+ *lemma* bintegral_sub
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_smul
- \+ *lemma* coe_pos_part
- \+ *lemma* coe_neg_part
- \+ *lemma* integral_eq_bintegral
- \+ *lemma* pos_part_to_simple_func
- \+ *lemma* neg_part_to_simple_func
- \+ *lemma* integral_eq_norm_pos_part_sub
- \+ *lemma* integral_coe_eq_integral
- \+ *lemma* integral_eq_lintegral_max_sub_lintegral_min
- \+ *lemma* integral_eq_lintegral_of_nonneg_ae
- \+ *lemma* integral_nonneg_of_nonneg_ae
- \+ *lemma* integral_nonpos_of_nonpos_ae
- \+ *lemma* integral_le_integral_of_le_ae
- \+ *lemma* norm_integral_le_integral_norm
- \- *lemma* of_real_norm_integral_le_lintegral_norm
- \+ *def* pos_part
- \+ *def* neg_part
- \+/\- *def* integral

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.add
- \+ *lemma* measurable.neg
- \+ *lemma* measurable.sub
- \+ *lemma* measurable.mul
- \+ *lemma* is_measurable_le
- \+ *lemma* measurable.max
- \+ *lemma* measurable.min
- \- *lemma* measurable_add
- \- *lemma* measurable_neg
- \- *lemma* measurable_sub
- \- *lemma* measurable_mul
- \- *lemma* measurable_le

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_of_le_ae
- \+ *lemma* lintegral_norm_eq_lintegral_edist
- \+/\- *lemma* lintegral_nnnorm_add
- \+ *lemma* integrable.add
- \+ *lemma* integrable.neg
- \+ *lemma* integrable.sub
- \+ *lemma* integrable.norm
- \+ *lemma* integrable.max_zero
- \+ *lemma* integrable.min_zero
- \+ *lemma* integrable.smul
- \+ *lemma* integrable.smul_iff
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_smul
- \+ *lemma* of_fun_sub
- \+ *lemma* norm_of_fun_eq_lintegral_norm
- \+ *lemma* coe_pos_part
- \+ *lemma* pos_part_to_fun
- \+ *lemma* neg_part_to_fun_eq_max
- \+ *lemma* neg_part_to_fun_eq_min
- \+ *lemma* norm_le_norm_of_ae_le
- \+ *lemma* continuous_pos_part
- \+ *lemma* continuous_neg_part
- \- *lemma* integrable_add
- \- *lemma* integrable_neg
- \- *lemma* integrable_sub
- \- *lemma* integrable_norm
- \- *lemma* integrable_smul
- \- *lemma* integrable_smul_iff
- \+ *def* pos_part
- \+ *def* neg_part

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.subtype_val
- \+ *lemma* measurable.subtype_mk
- \+ *lemma* measurable.fst
- \+ *lemma* measurable.snd
- \+ *lemma* measurable.prod_mk
- \- *lemma* measurable_subtype_val
- \- *lemma* measurable_subtype_mk
- \- *lemma* measurable_fst
- \- *lemma* measurable_snd
- \- *lemma* measurable_prod_mk

Modified src/measure_theory/simple_func_dense.lean




## [2019-12-11 17:17:17](https://github.com/leanprover-community/mathlib/commit/a8f6e23)
feat(data/list/basic): list.lex.not_nil_right ([#1797](https://github.com/leanprover-community/mathlib/pull/1797))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* not_nil_right



## [2019-12-11 09:52:57](https://github.com/leanprover-community/mathlib/commit/23e8ac7)
feat(ring_theory/algebra): elementary simp-lemmas for aeval ([#1795](https://github.com/leanprover-community/mathlib/pull/1795))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* aeval_X
- \+ *lemma* aeval_C



## [2019-12-10 19:03:24+01:00](https://github.com/leanprover-community/mathlib/commit/3a10c60)
chore(.mergify.yml): don't wait for travis when [ci skip] is present ([#1789](https://github.com/leanprover-community/mathlib/pull/1789))
#### Estimated changes
Modified .mergify.yml




## [2019-12-10 16:39:32](https://github.com/leanprover-community/mathlib/commit/361793a)
refactor(linear_algebra/finite_dimensional): universe polymorphism, doc  ([#1784](https://github.com/leanprover-community/mathlib/pull/1784))
* refactor(linear_algebra/finite_dimensional): universe polymorphism, doc
* docstrings
* improvements
* typo
* Update src/linear_algebra/dimension.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/finite_dimensional.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/finite_dimensional.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix comments
* fix build
* fix build
* remove pp.universe
* keep docstring in sync
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *lemma* linear_map.continuous_on_pi
- \+/\- *lemma* continuous_equiv_fun_basis

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* pi_apply_eq_sum_univ
- \+ *lemma* map_subtype_top

Modified src/linear_algebra/basis.lean
- \- *lemma* linear_equiv.is_basis

Modified src/linear_algebra/dimension.lean
- \+ *theorem* dim_quotient_add_dim
- \+ *theorem* dim_quotient_le
- \- *theorem* dim_quotient

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* exists_is_basis_finite
- \+ *lemma* iff_fg
- \+ *lemma* of_finite_basis
- \+ *lemma* dim_eq_card_basis
- \+ *lemma* findim_eq_card_basis
- \+ *lemma* findim_eq_card_basis'
- \+ *lemma* findim_le
- \+ *lemma* findim_quotient_le
- \+ *lemma* comp_eq_id_comm
- \+ *lemma* finite_dimensional_of_surjective
- \- *lemma* of_fg
- \- *lemma* card_eq_findim
- \- *lemma* findim_submodule_le
- \- *lemma* fg_of_finite_basis
- \- *lemma* finite_dimensional_of_finite_basis
- \- *lemma* dim_eq_card
- \- *lemma* findim_eq_card
- \+ *theorem* span_of_finite
- \+ *theorem* fg_iff_finite_dimensional
- \+ *theorem* findim_quotient_add_findim
- \+ *theorem* findim_eq

Modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_span_of_finite



## [2019-12-10 14:22:20](https://github.com/leanprover-community/mathlib/commit/6bb1728)
feat(analysis/convex): interiors/closures of convex sets are convex in a tvs ([#1781](https://github.com/leanprover-community/mathlib/pull/1781))
* feat(topology/algebra/module): scalar multiplication homeomorphisms
* feat(topology/algebra/module): more lemmas
- homeomorphisms given by scalar multiplication by unit is open/closed map.
* feat(analysis/convex): interior of convex set is convex in a tvs
- in separate file for interpretation time reasons.
* feat(analysis/convex): extract lemma
* feat(analysis/convex): closure of a convext set is convex
* style(analysis/convex): place lemmas at reasonable locations
* style(topology/algebra/module): fix bracketing style
* feat(analysis/convex): introduce `smul_set` and `pointwise_mul`
- also additional equivalent statements for convexity using those definitions.
* feat(algebra/pointwise): lemmas for `smul_set`
* doc(algebra/pointwise): add docstrings
* doc(algebra/pointwise): add global docstring
* docs(algebra/pointwise): amend global docstring
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* smul_set_eq_pointwise_smul_singleton
- \+ *lemma* one_smul_set
- \+ *lemma* zero_smul_set
- \+ *def* pointwise_smul
- \+ *def* smul_set

Modified src/analysis/convex.lean
- \+ *lemma* convex_iff₂:
- \+ *lemma* convex_iff₃:
- \+ *lemma* convex_interior
- \+ *lemma* convex_closure

Modified src/topology/algebra/module.lean
- \+ *lemma* is_open_map_smul_of_unit
- \+ *lemma* is_closed_map_smul_of_unit
- \+ *lemma* is_open_map_smul_of_ne_zero
- \+ *lemma* is_closed_map_smul_of_ne_zero



## [2019-12-09 20:49:33](https://github.com/leanprover-community/mathlib/commit/5c09372)
A `ring_exp` tactic for dealing with exponents in rings ([#1715](https://github.com/leanprover-community/mathlib/pull/1715))
* Test for ring_exp
* Implement -a/b * -a/b = a/b * a/b
* Hide extra information in the `ex` type in `ex_info`
* Some attempts to make the proof returned by ring_exp shorter
* Fix that ring_exp wouldn't handle pow that isn't monomial.has_pow
* Some optimizations in ring_exp
* Make all proofs explicit, halving execution time more or less
* Cache `has_add` and `has_mul` instances for another 2x speedup
* ring_exp can replace ring to compile mathlib
* Revert `ring` to non-test version
* Code cleanup and documentation
* Revert the test changes to `linarith`
* Undo the test changes to `ring2`
* Whitespace cleanup
* Fix overzealous error handling
Instead of catching any `fail` in eval, we just catch the operations that can
safely `fail` (i.e. `invert` and `negate`). This should make internal errors
visible again.
* Fix the TODO's
* Example use of ring_exp in data.polynomial
* Check that `ring_exp` deals well with natural number subtraction
* Fix incorrect docstring
* Improve documentation
* Small stylistic fixes
* Fix slow behaviour on large exponents
* Add `ring_exp` to the default tactics
* Use applicative notation where appropriate
* The `ring_exp` tactic also does normalization
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Move `normalize` from `tactic.interactive` to `ring_exp` namespace
* Fix name collision between `equiv` in data.equiv.basic and `equiv` in `test/tactics.lean`
I just renamed the definition in `test/tactics.lean` to `my_equiv`
and the operator to `my≅`.
* Fixes for the linter
* Fix the usage of type classes for `sub_pf` and `div_pf`
* Fix an additional linting error
* Optimization: we don't need norm_num to determine `x * 1 = x`
* Improve documentation of `test/ring_exp.lean`
* Rename `resolve_atoms` to `resolve_atom_aux` for clarity
* Small stylistic fixes
* Remove unneccessary hidden fields to `ex`
* Control how much unfolding `ring_exp` does by putting a `!` after it
* Reword comment for `ex_type`
* Use `ring_exp!` to deal with `(n : ℕ) + 1 - 1 = n`
* Document the `!` flag for `ring`, `ring_exp` and `ring_exp_eq`
* Get rid of searching for another cached instance
* Fix `ring_exp` failing on terms on the form `0^succ (succ ...)`
#### Estimated changes
Modified docs/tactics.md


Modified src/data/polynomial.lean


Modified src/tactic/default.lean


Created src/tactic/ring_exp.lean
- \+ *lemma* sum_congr
- \+ *lemma* prod_congr
- \+ *lemma* exp_congr
- \+ *lemma* base_to_exp_pf
- \+ *lemma* exp_to_prod_pf
- \+ *lemma* prod_to_sum_pf
- \+ *lemma* atom_to_sum_pf
- \+ *lemma* mul_coeff_pf_one_mul
- \+ *lemma* mul_coeff_pf_mul_one
- \+ *lemma* add_overlap_pf
- \+ *lemma* add_overlap_pf_zero
- \+ *lemma* add_pf_z_sum
- \+ *lemma* add_pf_sum_z
- \+ *lemma* add_pf_sum_overlap
- \+ *lemma* add_pf_sum_overlap_zero
- \+ *lemma* add_pf_sum_lt
- \+ *lemma* add_pf_sum_gt
- \+ *lemma* mul_pf_c_c
- \+ *lemma* mul_pf_c_prod
- \+ *lemma* mul_pf_prod_c
- \+ *lemma* mul_pp_pf_overlap
- \+ *lemma* mul_pp_pf_prod_lt
- \+ *lemma* mul_pp_pf_prod_gt
- \+ *lemma* mul_p_pf_zero
- \+ *lemma* mul_p_pf_sum
- \+ *lemma* mul_pf_zero
- \+ *lemma* mul_pf_sum
- \+ *lemma* pow_e_pf_exp
- \+ *lemma* pow_pp_pf_one
- \+ *lemma* pow_pp_pf_c
- \+ *lemma* pow_pp_pf_prod
- \+ *lemma* pow_p_pf_one
- \+ *lemma* pow_p_pf_zero
- \+ *lemma* pow_p_pf_succ
- \+ *lemma* pow_p_pf_singleton
- \+ *lemma* pow_p_pf_cons
- \+ *lemma* pow_pf_zero
- \+ *lemma* pow_pf_sum
- \+ *lemma* simple_pf_sum_zero
- \+ *lemma* simple_pf_prod_one
- \+ *lemma* simple_pf_prod_neg_one
- \+ *lemma* simple_pf_var_one
- \+ *lemma* simple_pf_exp_one
- \+ *lemma* negate_pf
- \+ *lemma* inverse_pf
- \+ *lemma* sub_pf
- \+ *lemma* div_pf

Created test/ring_exp.lean
- \+ *def* pow_sub_pow_factor

Modified test/tactics.lean
- \+/\- *def* eta_expansion_test2



## [2019-12-09 11:40:19](https://github.com/leanprover-community/mathlib/commit/1809eb4)
feat(tactic/default): import suggest ([#1791](https://github.com/leanprover-community/mathlib/pull/1791))
#### Estimated changes
Modified src/tactic/default.lean




## [2019-12-09 07:40:52](https://github.com/leanprover-community/mathlib/commit/acd769a)
feat(analysis/calculus/deriv): derivative of division and polynomials ([#1769](https://github.com/leanprover-community/mathlib/pull/1769))
* feat(data/set/intervals): more properties of intervals
* fix docstrings
* blank space
* iff versions
* fix docstring
* more details in docstrings
* initial commit
* div_deriv
* more derivatives
* cleanup
* better docstring
* fix
* better
* minor fix
* simp attributes
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/analysis/calculus/deriv.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* nolint
* pow derivative
* Update src/topology/continuous_on.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* comp_add and friends
* remove useless variable
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.nhds_within
- \+ *lemma* has_deriv_at_inv_one
- \+ *lemma* differentiable_at_inv
- \+ *lemma* differentiable_within_at_inv
- \+ *lemma* differentiable_on_inv
- \+ *lemma* deriv_inv
- \+ *lemma* deriv_within_inv
- \+ *lemma* has_fderiv_at_inv
- \+ *lemma* has_fderiv_within_at_inv
- \+ *lemma* fderiv_inv
- \+ *lemma* fderiv_within_inv
- \+ *lemma* has_deriv_within_at.div
- \+ *lemma* has_deriv_at.div
- \+ *lemma* differentiable_within_at.div
- \+ *lemma* differentiable_at.div
- \+ *lemma* differentiable_on.div
- \+ *lemma* differentiable.div
- \+ *lemma* deriv_within_div
- \+ *lemma* deriv_div
- \+ *lemma* has_deriv_at_pow
- \+ *lemma* differentiable_at_pow
- \+ *lemma* differentiable_within_at_pow
- \+ *lemma* differentiable_pow
- \+ *lemma* differentiable_on_pow
- \+ *lemma* deriv_pow
- \+ *lemma* deriv_within_pow
- \+ *theorem* has_deriv_at_inv
- \+ *theorem* has_deriv_within_at_inv
- \+ *theorem* has_deriv_within_at_pow

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.nhds_within
- \+ *lemma* has_fderiv_within_at_of_not_mem_closure
- \+ *lemma* is_bounded_bilinear_map.continuous_left
- \+ *lemma* is_bounded_bilinear_map.continuous_right
- \- *lemma* continuous_linear_map.has_fderiv_within_at
- \- *lemma* continuous_linear_map.has_fderiv_at
- \- *lemma* continuous_linear_map.differentiable_at
- \- *lemma* continuous_linear_map.differentiable_within_at
- \- *lemma* continuous_linear_map.fderiv
- \- *lemma* continuous_linear_map.fderiv_within
- \- *lemma* continuous_linear_map.differentiable
- \- *lemma* continuous_linear_map.differentiable_on

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* tendsto_inv
- \+ *lemma* continuous_on_inv
- \+ *lemma* filter.tendsto.inv'
- \+ *lemma* filter.tendsto.div

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map_smul_right

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* comp_add
- \+ *lemma* add_comp
- \+ *lemma* smul_comp
- \+ *lemma* comp_smul
- \+ *theorem* comp_id
- \+ *theorem* id_comp
- \+ *theorem* comp_zero
- \+ *theorem* zero_comp

Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* mem_nhds_within_iff
- \+ *theorem* tendsto_nhds_within_nhds_within
- \+ *theorem* tendsto_nhds_within_nhds

Modified src/topology/sequences.lean
- \+ *lemma* mem_closure_iff_seq_limit



## [2019-12-07 19:47:19](https://github.com/leanprover-community/mathlib/commit/4c382b1)
(tactic/tidy): add docstring [skip ci] ([#1788](https://github.com/leanprover-community/mathlib/pull/1788))
* (tactic/tidy): add docstring [skip ci]
* Update src/tactic/tidy.lean
* mention [tidy] attribute
#### Estimated changes
Modified src/tactic/tidy.lean




## [2019-12-07 17:48:37](https://github.com/leanprover-community/mathlib/commit/3c9f8f0)
feat(algebra/field_power): fpow is a strict mono ([#1778](https://github.com/leanprover-community/mathlib/pull/1778))
* WIP
* feat(algebra/field): remove is_field_hom
A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.
* Fix up nolints.txt
* Process comments from reviews
* Rename lemma
#### Estimated changes
Modified src/algebra/field_power.lean
- \+/\- *lemma* zero_gpow
- \+/\- *lemma* fpow_of_nat
- \+/\- *lemma* fpow_neg_succ_of_nat
- \+/\- *lemma* unit_pow
- \+/\- *lemma* fpow_eq_gpow
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_ne_zero_of_ne_zero
- \+/\- *lemma* fpow_zero
- \+/\- *lemma* fpow_add
- \+/\- *lemma* one_fpow
- \+/\- *lemma* fpow_one
- \+ *lemma* map_fpow'
- \+/\- *lemma* zero_fpow
- \+/\- *lemma* fpow_neg
- \+/\- *lemma* fpow_sub
- \+/\- *lemma* fpow_mul
- \+/\- *lemma* mul_fpow
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_pos_of_pos
- \+/\- *lemma* fpow_le_of_le
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+/\- *lemma* one_le_fpow_of_nonneg
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* one_lt_fpow
- \+ *lemma* nat.fpow_pos_of_pos
- \+ *lemma* nat.fpow_ne_zero_of_pos
- \+ *lemma* fpow_strict_mono
- \+ *lemma* fpow_lt_iff_lt
- \+ *lemma* fpow_le_iff_le
- \+ *lemma* injective_fpow
- \+ *lemma* fpow_inj
- \+ *lemma* fpow_eq_zero
- \+ *theorem* fpow_neg_mul_fpow_self
- \+ *theorem* cast_fpow
- \+/\- *def* fpow



## [2019-12-07 13:49:21](https://github.com/leanprover-community/mathlib/commit/0455962)
refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice` ([#1783](https://github.com/leanprover-community/mathlib/pull/1783))
* refactor(order/bounds,*): move code around to make `order.bounds` not depend on `complete_lattice`
In another PR I'm going to prove more facts in `order/bounds`, then
replace many proofs of lemmas about `(c)Sup`/`(c)Inf` with references to lemmas
about `is_lub`/`is_glb`.
* Move more code to `basic`, rewrite the only remaining proof in `default`
* Rename
* Add `default.lean`
#### Estimated changes
Modified archive/cubing_a_cube.lean


Modified src/data/set/finite.lean
- \+ *lemma* bdd_above_finite
- \+ *lemma* bdd_above_finite_union
- \+ *lemma* bdd_below_finite
- \+ *lemma* bdd_below_finite_union

Renamed src/data/set/intervals.lean to src/data/set/intervals/basic.lean
- \- *lemma* is_glb_Ici
- \- *lemma* is_glb_Icc
- \- *lemma* is_glb_Ico
- \- *lemma* is_lub_Iic
- \- *lemma* is_lub_Icc
- \- *lemma* is_lub_Ioc
- \- *lemma* eq_of_Ico_disjoint
- \- *lemma* is_glb_Ioi
- \- *lemma* is_glb_Ioo
- \- *lemma* is_glb_Ioc
- \- *lemma* is_lub_Iio
- \- *lemma* is_lub_Ioo
- \- *lemma* is_lub_Ico

Created src/data/set/intervals/default.lean


Created src/data/set/intervals/disjoint.lean
- \+ *lemma* Ico_disjoint_Ico
- \+ *lemma* eq_of_Ico_disjoint

Modified src/order/bounds.lean
- \+ *lemma* is_glb_Ici
- \+ *lemma* is_glb_Icc
- \+ *lemma* is_glb_Ico
- \+ *lemma* is_lub_Iic
- \+ *lemma* is_lub_Icc
- \+ *lemma* is_lub_Ioc
- \+ *lemma* is_glb_Ioi
- \+ *lemma* is_lub_Iio
- \+ *lemma* is_glb_Ioo
- \+ *lemma* is_glb_Ioc
- \+ *lemma* is_lub_Ioo
- \+ *lemma* is_lub_Ico
- \+ *lemma* bdd_above.mk
- \+ *lemma* bdd_below.mk
- \+ *lemma* bdd_above_empty
- \+ *lemma* bdd_below_empty
- \+ *lemma* bdd_above_singleton
- \+ *lemma* bdd_below_singleton
- \+ *lemma* bdd_above_subset
- \+ *lemma* bdd_below_subset
- \+ *lemma* bdd_above_inter_left
- \+ *lemma* bdd_above_inter_right
- \+ *lemma* bdd_below_inter_left
- \+ *lemma* bdd_below_inter_right
- \+ *lemma* bdd_above_of_bdd_above_of_monotone
- \+ *lemma* bdd_below_of_bdd_below_of_monotone
- \+ *lemma* bdd_above_top
- \+ *lemma* bdd_below_bot
- \+ *lemma* bdd_above_union
- \+ *lemma* bdd_above_insert
- \+ *lemma* bdd_below_union
- \+ *lemma* bdd_below_insert
- \- *lemma* is_lub_Sup
- \- *lemma* is_lub_supr
- \- *lemma* is_lub_iff_supr_eq
- \- *lemma* is_lub_iff_Sup_eq
- \- *lemma* is_glb_Inf
- \- *lemma* is_glb_infi
- \- *lemma* is_glb_iff_infi_eq
- \- *lemma* is_glb_iff_Inf_eq
- \+ *def* bdd_above
- \+ *def* bdd_below

Modified src/order/complete_lattice.lean
- \+ *lemma* is_lub_Sup
- \+ *lemma* is_lub_iff_Sup_eq
- \+ *lemma* is_glb_Inf
- \+ *lemma* is_glb_iff_Inf_eq
- \+ *lemma* is_lub_supr
- \+ *lemma* is_lub_iff_supr_eq
- \+ *lemma* is_glb_infi
- \+ *lemma* is_glb_iff_infi_eq

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* bdd_above.mk
- \- *lemma* bdd_below.mk
- \- *lemma* bdd_above_empty
- \- *lemma* bdd_below_empty
- \- *lemma* bdd_above_singleton
- \- *lemma* bdd_below_singleton
- \- *lemma* bdd_above_subset
- \- *lemma* bdd_below_subset
- \- *lemma* bdd_above_inter_left
- \- *lemma* bdd_above_inter_right
- \- *lemma* bdd_below_inter_left
- \- *lemma* bdd_below_inter_right
- \- *lemma* bdd_above_of_bdd_above_of_monotone
- \- *lemma* bdd_below_of_bdd_below_of_monotone
- \- *lemma* bdd_above_top
- \- *lemma* bdd_below_bot
- \- *lemma* bdd_above_union
- \- *lemma* bdd_above_insert
- \- *lemma* bdd_above_finite
- \- *lemma* bdd_above_finite_union
- \- *lemma* bdd_below_union
- \- *lemma* bdd_below_insert
- \- *lemma* bdd_below_finite
- \- *lemma* bdd_below_finite_union
- \- *def* bdd_above
- \- *def* bdd_below

Modified src/order/galois_connection.lean




## [2019-12-06 22:09:41](https://github.com/leanprover-community/mathlib/commit/6968d74)
chore(travis): add instance priority linter to CI ([#1787](https://github.com/leanprover-community/mathlib/pull/1787))
* add instance priority to linter
* Update mk_nolint.lean
* fix fintype.compact_space prio
#### Estimated changes
Modified scripts/mk_all.sh


Modified scripts/mk_nolint.lean


Modified src/topology/subset_properties.lean




## [2019-12-06 16:24:38](https://github.com/leanprover-community/mathlib/commit/8ca9263)
feat(topology/subset_properties): fintype.compact_space ([#1786](https://github.com/leanprover-community/mathlib/pull/1786))
Finite topological spaces are compact.
#### Estimated changes
Modified src/topology/subset_properties.lean




## [2019-12-06 15:20:53](https://github.com/leanprover-community/mathlib/commit/7084182)
feat(topology/dense_embedding): dense_range.equalizer ([#1785](https://github.com/leanprover-community/mathlib/pull/1785))
* feat(topology/dense_embedding): dense_range.equalizer
Two continuous functions to a t2-space
that agree on a dense set are equal.
* Fix docstring
#### Estimated changes
Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_range.equalizer



## [2019-12-05 21:00:24](https://github.com/leanprover-community/mathlib/commit/7221900)
feat(data/set/basic): more lemmas about `set.nonempty` ([#1780](https://github.com/leanprover-community/mathlib/pull/1780))
* feat(data/set/basic): more lemmas about `set.nonempty`
* Fix compile
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* nonempty.ne_empty
- \+ *theorem* insert_nonempty
- \+ *theorem* singleton_nonempty
- \+/\- *theorem* singleton_ne_empty



## [2019-12-05 17:22:16](https://github.com/leanprover-community/mathlib/commit/2adc122)
feat(data/set/finite): remove exists_finset_of_finite ([#1782](https://github.com/leanprover-community/mathlib/pull/1782))
* feat(data/set/finite): remove exists_finset_of_finite
exists_finset_of_finite is a duplicate of finite.exists_finset_coe
At same time, provide a `can_lift` instance to lift sets to finsets.
* Add docstring
#### Estimated changes
Modified src/data/set/finite.lean
- \- *lemma* exists_finset_of_finite



## [2019-12-05 15:23:56](https://github.com/leanprover-community/mathlib/commit/3e6fe84)
feat(meta/expr): use structure_fields ([#1766](https://github.com/leanprover-community/mathlib/pull/1766))
removes is_structure_like
simplifies definition of is_structure
renames and simplifies definition get_projections. It is now called structure_fields_full
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/simps.lean


Modified test/simps.lean


Modified test/tactics.lean




## [2019-12-05 06:07:31](https://github.com/leanprover-community/mathlib/commit/de377ea)
feat(algebra/field): remove is_field_hom ([#1777](https://github.com/leanprover-community/mathlib/pull/1777))
* feat(algebra/field): remove is_field_hom
A field homomorphism is just a ring homomorphism.
This is one trivial tiny step in moving over to bundled homs.
* Fix up nolints.txt
* Remove duplicate instances
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/direct_limit.lean


Modified src/algebra/field.lean
- \- *def* is_field_hom

Modified src/algebra/field_power.lean
- \+/\- *lemma* map_fpow

Modified src/data/complex/basic.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* degree_map
- \+/\- *lemma* nat_degree_map
- \+/\- *lemma* leading_coeff_map
- \+/\- *lemma* map_div
- \+/\- *lemma* map_mod
- \+/\- *lemma* map_eq_zero

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* splits_map_iff
- \+/\- *lemma* splits_comp_of_splits

Modified src/field_theory/subfield.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/localization.lean




## [2019-12-05 01:31:42](https://github.com/leanprover-community/mathlib/commit/324ae4b)
feat(data/set/basic): define `set.nonempty` ([#1779](https://github.com/leanprover-community/mathlib/pull/1779))
* Define `set.nonempty` and prove some basic lemmas
* Migrate `well_founded.min` to `set.nonempty`
* Fix a docstring and a few names
Based on comments in PR
* More docs
* Linebreaks
* +2 docstrings
* Fix compile
* Fix compile of `archive/imo1988_q6`
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified src/data/set/basic.lean
- \+ *lemma* nonempty_of_mem
- \+ *lemma* nonempty.of_subset
- \+ *lemma* nonempty_of_ssubset
- \+ *lemma* nonempty.of_diff
- \+ *lemma* nonempty.of_ssubset'
- \+ *lemma* nonempty.inl
- \+ *lemma* nonempty.inr
- \+ *lemma* union_nonempty
- \+ *lemma* nonempty.left
- \+ *lemma* nonempty.right
- \+ *lemma* nonempty_iff_univ_nonempty
- \+ *lemma* univ_nonempty
- \+ *theorem* ne_empty_iff_nonempty
- \+/\- *theorem* ne_empty_iff_exists_mem
- \+/\- *theorem* ne_empty_of_mem
- \+/\- *theorem* prod_empty
- \+/\- *theorem* empty_prod
- \+ *theorem* nonempty.prod
- \+ *theorem* nonempty.fst
- \+ *theorem* nonempty.snd
- \+ *theorem* prod_nonempty_iff
- \+ *theorem* prod_ne_empty_iff
- \- *theorem* prod_neq_empty_iff

Modified src/field_theory/minimal_polynomial.lean


Modified src/logic/basic.lean


Modified src/order/basic.lean


Modified src/order/pilex.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean


Modified src/topology/constructions.lean




## [2019-12-04 19:03:55](https://github.com/leanprover-community/mathlib/commit/d4ee5b6)
fix(order.basic|ring_theory.algebra): lower instance priority ([#1729](https://github.com/leanprover-community/mathlib/pull/1729))
* algebra
* algebra2
* algebra3
* algebra4
* order.basic
* module
* algebra/ring
* explain default priority of 100
* undo priority changes
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* gsmul_eq_smul

Modified src/order/basic.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* smul_def''
- \+ *lemma* smul_def
- \+ *lemma* range_le
- \- *theorem* smul_def

Modified src/ring_theory/integral_closure.lean


Modified src/tactic/lint.lean




## [2019-12-04 15:51:17](https://github.com/leanprover-community/mathlib/commit/4353167)
doc(topology/basic): add a few doc strings [skip ci] ([#1775](https://github.com/leanprover-community/mathlib/pull/1775))
* doc(topology/basic): add a few doc strings
* Apply suggestions from code review
#### Estimated changes
Modified src/topology/basic.lean




## [2019-12-04 13:46:21](https://github.com/leanprover-community/mathlib/commit/c43b332)
feat(data/set/intervals): more properties of intervals ([#1753](https://github.com/leanprover-community/mathlib/pull/1753))
* feat(data/set/intervals): more properties of intervals
* fix docstrings
* blank space
* iff versions
* fix docstring
* more details in docstrings
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/data/set/intervals.lean
- \+ *lemma* Ioo_subset_Ioc_self
- \+ *lemma* Ioc_subset_Icc_self
- \+/\- *lemma* Ico_subset_Iio_self
- \+ *lemma* Ioo_subset_Iio_self
- \+ *lemma* Ioc_subset_Ioi_self
- \+ *lemma* Ioo_subset_Ioi_self
- \+ *lemma* Ioi_subset_Ici_self
- \+ *lemma* Iio_subset_Iic_self
- \+ *lemma* Ioi_subset_Ioi
- \+ *lemma* Ioi_subset_Ici
- \+ *lemma* Iio_subset_Iio
- \+ *lemma* Iio_subset_Iic
- \+ *lemma* Ioi_subset_Ioi_iff
- \+ *lemma* Ioi_subset_Ici_iff
- \+ *lemma* Iio_subset_Iio_iff
- \+ *lemma* Iio_subset_Iic_iff
- \+ *lemma* is_glb_Ici
- \+ *lemma* is_glb_Icc
- \+ *lemma* is_glb_Ico
- \+ *lemma* is_lub_Iic
- \+ *lemma* is_lub_Icc
- \+ *lemma* is_lub_Ioc
- \+ *lemma* is_glb_Ioi
- \+ *lemma* is_glb_Ioo
- \+ *lemma* is_glb_Ioc
- \+ *lemma* is_lub_Iio
- \+ *lemma* is_lub_Ioo
- \+ *lemma* is_lub_Ico

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_closed_Iic
- \+ *lemma* is_closed_Ici
- \+ *lemma* mem_nhds_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_iff_exists_Ioo_subset
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioc_subset
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ico_subset
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset'
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset'
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset
- \+ *lemma* closure_Ioi'
- \+ *lemma* closure_Ioi
- \+ *lemma* closure_Iio'
- \+ *lemma* closure_Iio
- \+ *lemma* closure_Ioo
- \+ *lemma* closure_Ioc
- \+ *lemma* closure_Ico

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_iff_exists_mem_nhds_inter
- \+ *lemma* continuous_within_at.tendsto
- \+ *lemma* continuous.continuous_within_at
- \+/\- *theorem* mem_nhds_within



## [2019-12-04 09:12:47](https://github.com/leanprover-community/mathlib/commit/2c2cbb0)
feat(data/nat/prime): monoid.prime_pow and docs ([#1772](https://github.com/leanprover-community/mathlib/pull/1772))
* feat(data/nat/prime): monoid.prime_pow and docs
From the perfectoid project.
Also add some documentation.
* Add backticks in docs
#### Estimated changes
Modified src/data/nat/prime.lean




## [2019-12-04 06:44:31](https://github.com/leanprover-community/mathlib/commit/71247eb)
feat(lift): check whether target is proposition ([#1767](https://github.com/leanprover-community/mathlib/pull/1767))
* feat(lift): check whether target is proposition
* simplify
#### Estimated changes
Modified src/tactic/lift.lean


Modified test/tactics.lean




## [2019-12-04 04:29:28](https://github.com/leanprover-community/mathlib/commit/c1105de)
feat(tactic): mk_simp_attribute command that includes doc string ([#1763](https://github.com/leanprover-community/mathlib/pull/1763))
* feat(tactic): mk_simp_attr command that includes doc string
* Update tactics.md
* rename mk_simp_attr to mk_simp_set
* rename again to mk_simp_attribute
* explain  syntax better
* simp with, not simp using
* simp with, not simp using
* avoid parsing ambiguity
* fix build
* Update docs/tactics.md
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
Modified docs/tactics.md


Modified scripts/nolints.txt


Modified src/category/basic.lean


Modified src/category/monad/basic.lean


Modified src/data/nat/parity.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/tactic/core.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/split_ifs.lean




## [2019-12-04 00:28:08](https://github.com/leanprover-community/mathlib/commit/b031290)
feat(data/finset): lemmas for folding min and max ([#1774](https://github.com/leanprover-community/mathlib/pull/1774))
From the perfectoid project.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* fold_op_rel_iff_and
- \+ *lemma* fold_op_rel_iff_or
- \+ *lemma* le_fold_min
- \+ *lemma* fold_min_le
- \+ *lemma* lt_fold_min
- \+ *lemma* fold_min_lt
- \+ *lemma* fold_max_le
- \+ *lemma* le_fold_max
- \+ *lemma* fold_max_lt
- \+ *lemma* lt_fold_max



## [2019-12-03 20:55:07](https://github.com/leanprover-community/mathlib/commit/827e78b)
feat(lint): avoid Travis error when declarations are renamed ([#1771](https://github.com/leanprover-community/mathlib/pull/1771))
#### Estimated changes
Modified scripts/mk_nolint.lean


Modified scripts/nolints.txt


Modified src/tactic/lint.lean




## [2019-12-03 18:35:15](https://github.com/leanprover-community/mathlib/commit/866be5f)
feat(data/polynomial): monic.as_sum ([#1773](https://github.com/leanprover-community/mathlib/pull/1773))
From the perfectoid project.
It is often useful to write a monic polynomial f in the form
`X^n + sum of lower degree terms`.
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* monic.as_sum



## [2019-12-03 16:50:35](https://github.com/leanprover-community/mathlib/commit/922a4eb)
feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty ([#1770](https://github.com/leanprover-community/mathlib/pull/1770))
* feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty
From the perfectoid project
* Update src/set_theory/cardinal.lean
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* eq_one_iff_subsingleton_and_nonempty



## [2019-12-03 14:47:38](https://github.com/leanprover-community/mathlib/commit/3266b96)
feat(tactic/lift): automatically handle pi types ([#1755](https://github.com/leanprover-community/mathlib/pull/1755))
* feat(tactic/lift): automatically handle pi types
* Add missing docs
* Update docs/tactics.md
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/lift.lean


Modified test/tactics.lean




## [2019-12-03 07:46:12](https://github.com/leanprover-community/mathlib/commit/89e7f6f)
feat(README): add link to Lean Links [skip ci] ([#1768](https://github.com/leanprover-community/mathlib/pull/1768))
#### Estimated changes
Modified README.md




## [2019-12-02 17:29:31](https://github.com/leanprover-community/mathlib/commit/3913d30)
refactor(topology/algebra): use dot notation in tendsto.add and friends ([#1765](https://github.com/leanprover-community/mathlib/pull/1765))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/data/real/hyperreal.lean


Modified src/measure_theory/decomposition.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* filter.tendsto.inv
- \+ *lemma* filter.tendsto.sub
- \- *lemma* tendsto.inv
- \- *lemma* tendsto.sub

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* filter.tendsto.mul
- \- *lemma* tendsto.mul

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2019-12-02 14:48:24](https://github.com/leanprover-community/mathlib/commit/87929bf)
doc(*): correct bad markdown ([#1764](https://github.com/leanprover-community/mathlib/pull/1764))
* Update bochner_integration.lean
* Update mean_value.lean
* Update expr.lean
* Update doc.md
#### Estimated changes
Modified docs/contribute/doc.md


Modified src/analysis/calculus/mean_value.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/meta/expr.lean




## [2019-12-02 09:14:36](https://github.com/leanprover-community/mathlib/commit/1c4a296)
chore(topology/*): dots for continuity proofs ([#1762](https://github.com/leanprover-community/mathlib/pull/1762))
* chore(topology/*): dots for continuity proofs
This is a sequel to 431551a891a270260b6ece53dcdff39a0527cf78
* fix build
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2019-12-02 07:57:47](https://github.com/leanprover-community/mathlib/commit/89fd088)
feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete ([#1761](https://github.com/leanprover-community/mathlib/pull/1761))
* feat(topology/uniform_space/cauchy): sequentially complete space with a countable basis is complete
This is a more general version of what is currently proved in
`cau_seq_filter`. Migration of the latter file to the new code will be
done in a separate PR.
* Add docs, drop unused section vars, make arguments `U` and `U'` explicit.
* Update src/topology/uniform_space/cauchy.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix some comments
#### Estimated changes
Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* le_nhds_of_cauchy_adhp_aux
- \+ *lemma* cauchy_seq_of_controlled
- \+ *lemma* set_seq_mem
- \+ *lemma* set_seq_mono
- \+ *lemma* set_seq_sub_aux
- \+ *lemma* set_seq_prod_subset
- \+ *lemma* seq_mem
- \+ *lemma* seq_pair_mem
- \+ *theorem* seq_is_cauchy_seq
- \+ *theorem* le_nhds_of_seq_tendsto_nhds
- \+ *theorem* complete_of_convergent_controlled_sequences
- \+ *theorem* complete_of_cauchy_seq_tendsto
- \+ *def* set_seq_aux
- \+ *def* set_seq
- \+ *def* seq



## [2019-12-01 17:32:14](https://github.com/leanprover-community/mathlib/commit/177cced)
feat(measure/bochner_integration): dominated convergence theorem ([#1757](https://github.com/leanprover-community/mathlib/pull/1757))
* feat(measure/bochner_integration): dominated convergence theorem
This PR
* proves the dominated convergence theorem
* and some other lemmas including `integral_congr_ae`, `norm_integral_le_lintegral_norm`.
* adds several equivalent definitions of the predicate `integrable` and shortens some proofs.
* fix linting error
* Add some section doc strings
* Indentation is very wrong
* Remove useless assumptions; fix doc strings
* remove `private`; add a doc string for Lebesgue's dominated convergence theorem
* Update basic.lean
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* of_real_norm_eq_coe_nnnorm
- \+ *lemma* edist_eq_coe_nnnorm

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* norm_Integral_le_one
- \+ *lemma* norm_integral_le
- \+/\- *lemma* integral_smul
- \+ *lemma* integral_congr_ae
- \+ *lemma* of_real_norm_integral_le_lintegral_norm
- \+ *lemma* norm_integral_le_lintegral_norm
- \+ *theorem* tendsto_integral_of_dominated_convergence

Modified src/measure_theory/integration.lean
- \+ *lemma* tendsto_lintegral_of_dominated_convergence
- \- *lemma* dominated_convergence_nn

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_iff_norm
- \+ *lemma* integrable_iff_edist
- \+ *lemma* integrable_iff_of_real
- \+/\- *lemma* integrable_iff_of_ae_eq
- \+ *lemma* integrable_norm_iff
- \+ *lemma* integrable_of_integrable_bound
- \+ *lemma* all_ae_of_real_F_le_bound
- \+ *lemma* all_ae_tendsto_of_real_norm
- \+ *lemma* all_ae_of_real_f_le_bound
- \+ *lemma* integrable_of_dominated_convergence
- \+ *lemma* tendsto_lintegral_norm_of_dominated_convergence
- \+ *lemma* norm_eq_nnnorm_to_fun
- \+ *lemma* norm_eq_norm_to_fun
- \- *lemma* integrable_iff_lintegral_edist
- \- *lemma* norm_to_fun

Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_to_real



## [2019-12-01 16:14:54](https://github.com/leanprover-community/mathlib/commit/8a89b06)
refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative ([#1740](https://github.com/leanprover-community/mathlib/pull/1740))
* refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative
* docstring
* use iff.rfl
* fix build
* fix docstring
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* fderiv_within.comp_deriv_within
- \+ *lemma* fderiv.comp_deriv
- \+ *lemma* deriv_within_smul'
- \+ *lemma* deriv_smul'
- \+ *theorem* has_fderiv_within_at.comp_has_deriv_within_at
- \+ *theorem* has_fderiv_at.comp_has_deriv_at
- \+ *theorem* has_fderiv_at.comp_has_deriv_within_at
- \+ *theorem* has_deriv_within_at.smul'
- \+ *theorem* has_deriv_at.smul'

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_at.fderiv_within
- \- *lemma* differentiable.fderiv_within

Modified src/analysis/calculus/mean_value.lean




## [2019-12-01 15:07:11](https://github.com/leanprover-community/mathlib/commit/431551a)
refactor(topology/algebra): use the dot notation in `continuous_mul` and friends ([#1758](https://github.com/leanprover-community/mathlib/pull/1758))
* continuous_add
* fixes
* more fixes
* fix
* tendsto_add
* fix tendsto
* last fix
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/data/real/hyperreal.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/order/filter/pointwise.lean
- \+ *lemma* tendsto.mul_mul
- \- *lemma* tendsto_mul_mul

Modified src/topology/algebra/group.lean
- \+/\- *lemma* continuous_inv
- \+ *lemma* continuous.inv
- \+ *lemma* tendsto.inv
- \+ *lemma* continuous.sub
- \+/\- *lemma* continuous_sub
- \+ *lemma* tendsto.sub
- \- *lemma* continuous_inv'
- \- *lemma* tendsto_inv
- \- *lemma* continuous_sub'
- \- *lemma* tendsto_sub

Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_mul
- \+ *lemma* continuous.mul
- \+/\- *lemma* tendsto_mul
- \+ *lemma* tendsto.mul
- \- *lemma* continuous_mul'
- \- *lemma* tendsto_mul'

Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.max
- \+ *lemma* continuous.min
- \+ *lemma* tendsto.max
- \+ *lemma* tendsto.min
- \- *lemma* continuous_max
- \- *lemma* continuous_min
- \- *lemma* tendsto_max
- \- *lemma* tendsto_min

Modified src/topology/algebra/polynomial.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniform_continuous_sub
- \+ *lemma* uniform_continuous.sub
- \+ *lemma* uniform_continuous.neg
- \+/\- *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous.add
- \+/\- *lemma* uniform_continuous_add
- \- *lemma* uniform_continuous_sub'
- \- *lemma* uniform_continuous_neg'
- \- *lemma* uniform_continuous_add'

Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* continuous_mul
- \+ *lemma* continuous.mul
- \- *lemma* continuous_mul'

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/complex.lean
- \+/\- *lemma* continuous_inv
- \+ *lemma* continuous.inv
- \- *lemma* continuous_inv'

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+ *lemma* tendsto.sub
- \+/\- *lemma* continuous_sub
- \+ *lemma* continuous.sub
- \- *lemma* tendsto_sub
- \- *lemma* continuous_sub'

Modified src/topology/instances/real.lean
- \+/\- *lemma* real.continuous_inv
- \+ *lemma* real.continuous.inv
- \- *lemma* real.continuous_inv'

Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* mem_uniformity_of_uniform_continuous_invariant
- \- *lemma* mem_uniformity_of_uniform_continuous_invarant

Modified test/apply.lean




## [2019-12-01 15:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/a350f03)
chore(scripts/nolint.txt): regenerate
#### Estimated changes
Modified scripts/nolints.txt


