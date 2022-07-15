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
- \+ *theorem* antimono_of_deriv_nonpos
- \+ *theorem* convex.antimono_of_deriv_nonpos
- \+ *theorem* convex.image_sub_le_mul_sub_of_deriv_le
- \+ *theorem* convex.image_sub_lt_mul_sub_of_deriv_lt
- \+ *theorem* convex.mono_of_deriv_nonneg
- \+ *theorem* convex.mul_sub_le_image_sub_of_le_deriv
- \+ *theorem* convex.mul_sub_lt_image_sub_of_lt_deriv
- \+ *theorem* convex.strict_antimono_of_deriv_neg
- \+ *theorem* convex.strict_mono_of_deriv_pos
- \+ *theorem* convex_on_of_deriv2_nonneg
- \+ *theorem* convex_on_of_deriv_mono
- \+ *theorem* convex_on_univ_of_deriv2_nonneg
- \+ *theorem* convex_on_univ_of_deriv_mono
- \+ *theorem* image_sub_le_mul_sub_of_deriv_le
- \+ *theorem* image_sub_lt_mul_sub_of_deriv_lt
- \+ *theorem* is_const_of_fderiv_eq_zero
- \+ *theorem* mono_of_deriv_nonneg
- \+ *theorem* mul_sub_le_image_sub_of_le_deriv
- \+ *theorem* mul_sub_lt_image_sub_of_lt_deriv
- \+ *theorem* strict_antimono_of_deriv_neg
- \+ *theorem* strict_mono_of_deriv_pos

Modified src/analysis/convex.lean
- \- *lemma* convex_on_linorder
- \+ *lemma* convex_on_real_of_slope_mono_adjacent
- \+ *lemma* linear_order.convex_on_of_lt



## [2019-12-28 20:31:03](https://github.com/leanprover-community/mathlib/commit/64770a8)
feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition ([#1834](https://github.com/leanprover-community/mathlib/pull/1834))
* feat(analysis/calculus/deriv): Prove equivalence of Fréchet derivative and the classical definition
* Fix a typo
* Move, change doc, add versions for `has_deriv_within_at` and `has_deriv_at`.
* Fix docstring, remove an unsed argument
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at_filter_iff_tendsto_slope
- \+ *lemma* has_deriv_at_iff_tendsto_slope
- \+ *lemma* has_deriv_within_at_iff_tendsto_slope

Modified src/analysis/calculus/fderiv.lean


Modified src/order/filter/basic.lean
- \- *theorem* filter.tendsto.congr'r
- \+ *lemma* filter.tendsto_congr'
- \+ *theorem* filter.tendsto_congr

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
- \+ *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within
- \+ *lemma* is_closed.mem_of_ge_of_forall_exists_gt



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
- \+ *lemma* directed.le_sequence
- \+ *lemma* directed.rel_sequence
- \+ *lemma* directed.sequence_mono
- \+ *lemma* directed.sequence_mono_nat
- \+ *def* encodable_quotient
- \- *def* quot.encodable_quotient
- \- *def* quot.rep
- \- *theorem* quot.rep_spec
- \+ *def* quotient.rep
- \+ *theorem* quotient.rep_spec

Modified src/measure_theory/integration.lean
- \- *lemma* le_sequence_of_directed
- \+ *lemma* measure_theory.simple_func.seq_apply
- \- *lemma* monotone_sequence_of_directed

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.all_ae_of_all



## [2019-12-28 10:05:30](https://github.com/leanprover-community/mathlib/commit/340fa14)
feat(analysis/specific_limits): add a few more limits ([#1832](https://github.com/leanprover-community/mathlib/pull/1832))
* feat(analysis/specific_limits): add a few more limits
* Drop 1 lemma, generalize two others.
* Rename `tendsto_inverse_at_top_nhds_0`, fix compile
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* lim_norm_zero'
- \+ *lemma* normed_field.tendsto_norm_inverse_nhds_within_0_at_top
- \+ *lemma* tendsto_inv_at_top_zero'
- \+ *lemma* tendsto_inv_at_top_zero
- \- *lemma* tendsto_inverse_at_top_nhds_0
- \+ *lemma* tendsto_norm_at_top_at_top

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
- \+ *lemma* nhds_within_Ico_eq_nhds_within_Iio
- \+ *lemma* nhds_within_Ioc_eq_nhds_within_Ioi
- \+ *lemma* nhds_within_Ioo_eq_nhds_within_Iio
- \+ *lemma* nhds_within_Ioo_eq_nhds_within_Ioi
- \+ *lemma* tfae_mem_nhds_within_Iio
- \+ *lemma* tfae_mem_nhds_within_Ioi



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
- \+ *lemma* continuous_within_at.image_closure
- \+ *lemma* continuous_within_at.mem_closure
- \+ *lemma* nhds_within_prod_eq



## [2019-12-27 15:35:17](https://github.com/leanprover-community/mathlib/commit/3a78f49)
feat(order/basic): add `dual_le` and `dual_lt` lemmas ([#1830](https://github.com/leanprover-community/mathlib/pull/1830))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* order_dual.dual_le
- \+ *lemma* order_dual.dual_lt



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
- \+/\- *lemma* finset.prod_hom
- \- *lemma* is_group_hom.map_finset_prod
- \- *lemma* is_group_hom.map_multiset_prod
- \- *theorem* is_group_hom.map_prod
- \+ *lemma* monoid_hom.map_prod

Modified src/algebra/module.lean


Modified src/algebra/pi_instances.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/fold.lean


Modified src/data/complex/exponential.lean
- \+ *lemma* complex.exp_list_sum
- \+ *lemma* complex.exp_multiset_sum
- \+ *lemma* complex.exp_sum
- \+ *lemma* real.exp_list_sum
- \+ *lemma* real.exp_multiset_sum
- \+ *lemma* real.exp_sum

Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.foldl_hom
- \+/\- *theorem* list.foldl_map
- \+/\- *theorem* list.foldr_hom
- \+/\- *theorem* list.foldr_map
- \+ *theorem* list.prod_hom
- \+ *theorem* list.prod_hom_rel
- \+ *theorem* monoid_hom.map_list_prod

Modified src/data/matrix/basic.lean


Modified src/data/multiset.lean
- \+ *theorem* monoid_hom.map_multiset_prod
- \+/\- *lemma* multiset.prod_hom
- \+ *theorem* multiset.prod_hom_rel
- \- *lemma* multiset.sum_hom

Modified src/data/mv_polynomial.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_list_prod
- \+ *lemma* nnreal.coe_list_sum
- \+ *lemma* nnreal.coe_multiset_prod
- \+ *lemma* nnreal.coe_multiset_sum
- \+ *lemma* nnreal.coe_prod
- \+ *lemma* nnreal.coe_sum
- \- *lemma* nnreal.prod_coe
- \- *lemma* nnreal.sum_coe

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
- \+ *lemma* closure_inter_subset_inter_closure
- \+ *lemma* frontier_inter_subset
- \+ *lemma* frontier_union_subset
- \+ *lemma* is_closed.frontier_eq
- \+ *lemma* is_open.frontier_eq
- \+ *lemma* monotone_closure



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
- \+ *lemma* deriv_const'
- \+ *lemma* deriv_id'
- \+/\- *lemma* deriv_id
- \+ *lemma* deriv_neg'
- \+/\- *lemma* deriv_neg
- \+ *lemma* deriv_pow'
- \+/\- *lemma* deriv_pow

Modified src/analysis/complex/exponential.lean
- \+ *lemma* complex.deriv_cos'
- \+/\- *lemma* complex.deriv_cos
- \+/\- *lemma* complex.deriv_cosh
- \+/\- *lemma* complex.deriv_exp
- \+/\- *lemma* complex.deriv_sin
- \+/\- *lemma* complex.deriv_sinh
- \+ *lemma* complex.iter_deriv_exp
- \+ *lemma* real.deriv_cos'
- \+/\- *lemma* real.deriv_cos
- \+/\- *lemma* real.deriv_cosh
- \+/\- *lemma* real.deriv_exp
- \+/\- *lemma* real.deriv_sin
- \+/\- *lemma* real.deriv_sinh
- \+ *lemma* real.iter_deriv_exp



## [2019-12-27 09:41:58](https://github.com/leanprover-community/mathlib/commit/c1a993d)
feat(data/set/intervals): unions of adjacent intervals ([#1827](https://github.com/leanprover-community/mathlib/pull/1827))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_union_Icc_eq_Icc
- \+ *lemma* set.Icc_union_Ici_eq_Ioi
- \+ *lemma* set.Icc_union_Ico_eq_Ico
- \+ *lemma* set.Icc_union_Ioc_eq_Icc
- \+ *lemma* set.Icc_union_Ioi_eq_Ioi
- \+ *lemma* set.Icc_union_Ioo_eq_Ico
- \+ *lemma* set.Ico_union_Icc_eq_Icc
- \+ *lemma* set.Ico_union_Ici_eq_Ioi
- \+ *lemma* set.Ico_union_Ico_eq_Ico
- \+ *lemma* set.Iic_union_Icc_eq_Iic
- \+/\- *lemma* set.Iic_union_Ici
- \+ *lemma* set.Iic_union_Ico_eq_Iio
- \+ *lemma* set.Iic_union_Ioc_eq_Iic
- \+/\- *lemma* set.Iic_union_Ioi
- \+ *lemma* set.Iic_union_Ioo_eq_Iio
- \+ *lemma* set.Iio_union_Icc_eq_Iic
- \+/\- *lemma* set.Iio_union_Ici
- \+ *lemma* set.Iio_union_Ico_eq_Iio
- \+ *lemma* set.Ioc_union_Icc_eq_Ioc
- \+ *lemma* set.Ioc_union_Ici_eq_Ioi
- \+ *lemma* set.Ioc_union_Ico_eq_Ioo
- \+ *lemma* set.Ioc_union_Ioc_eq_Ioc
- \+ *lemma* set.Ioc_union_Ioi_eq_Ioi
- \+ *lemma* set.Ioc_union_Ioo_eq_Ioo
- \+ *lemma* set.Ioo_union_Icc_eq_Ioc
- \+ *lemma* set.Ioo_union_Ici_eq_Ioi
- \+ *lemma* set.Ioo_union_Ico_eq_Ioo
- \+/\- *lemma* set.nonempty_Ici
- \+/\- *lemma* set.nonempty_Iic
- \+ *lemma* set.nonempty_Ioo



## [2019-12-26 16:34:12](https://github.com/leanprover-community/mathlib/commit/7e2d4b8)
feat(analysis/calculus/extend_deriv): extend differentiability to the boundary ([#1794](https://github.com/leanprover-community/mathlib/pull/1794))
* feat(analysis/calculus/extend_deriv): extend differentiability to the boundary
* fix build
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.congr
- \+ *lemma* has_deriv_within_at.union

Added src/analysis/calculus/extend_deriv.lean
- \+ *lemma* has_deriv_at_interval_left_endpoint_of_tendsto_deriv
- \+ *theorem* has_fderiv_at_boundary_of_tendsto_fderiv
- \+ *theorem* has_fderiv_at_boundary_of_tendsto_fderiv_aux
- \+ *lemma* has_fderiv_at_interval_right_endpoint_of_tendsto_deriv

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.congr
- \+ *lemma* has_fderiv_within_at.union

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_inv_zero_at_top

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Iic_union_Ici
- \+ *lemma* set.Iic_union_Ioi
- \+ *lemma* set.Iio_union_Ici



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
- \+ *lemma* filter.eq_Inf_of_mem_sets_iff_exists_mem
- \+ *lemma* filter.eq_binfi_of_mem_sets_iff_exists_mem
- \+ *lemma* filter.eq_infi_of_mem_sets_iff_exists_mem

Modified src/topology/bases.lean
- \+ *lemma* filter.has_countable_basis.comap
- \+ *lemma* filter.has_countable_basis_iff_mono_seq'

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.complete_of_cauchy_seq_tendsto
- \+ *theorem* metric.complete_of_convergent_controlled_sequences

Modified src/topology/metric_space/cau_seq_filter.lean
- \+ *lemma* cau_seq.cauchy_seq
- \+ *lemma* cau_seq.tendsto_limit
- \- *lemma* cauchy_of_filter_cauchy
- \+ *lemma* cauchy_seq.is_cau_seq
- \- *theorem* complete_of_cauchy_seq_tendsto
- \- *theorem* emetric.complete_of_convergent_controlled_sequences
- \- *lemma* ennreal.cauchy_seq_of_edist_le_half_pow
- \- *lemma* ennreal.edist_le_two_mul_half_pow
- \- *lemma* ennreal.half_pow_add_succ
- \- *lemma* ennreal.half_pow_mono
- \- *lemma* ennreal.half_pow_pos
- \- *lemma* ennreal.half_pow_tendsto_zero
- \- *lemma* filter_cauchy_of_cauchy
- \- *theorem* metric.complete_of_convergent_controlled_sequences
- \- *lemma* sequentially_complete.B2_lim
- \- *lemma* sequentially_complete.B2_pos
- \- *lemma* sequentially_complete.le_nhds_cau_filter_lim
- \- *lemma* sequentially_complete.mono_of_mono_succ
- \- *lemma* sequentially_complete.seq_of_cau_filter_bound
- \- *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy
- \- *lemma* sequentially_complete.seq_of_cau_filter_mem_set_seq
- \- *def* sequentially_complete.set_seq_of_cau_filter
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_inhabited
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_monotone'
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_monotone
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_spec
- \- *lemma* tendsto_limit

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.complete_of_cauchy_seq_tendsto
- \+ *theorem* emetric.complete_of_convergent_controlled_sequences
- \+ *theorem* emetric.uniformity_has_countable_basis
- \+ *theorem* mem_uniformity_edist_inv_nat
- \+ *theorem* uniformity_edist_inv_nat

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *theorem* uniform_space.complete_of_convergent_controlled_sequences



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

Added src/analysis/calculus/local_extr.lean
- \+ *lemma* exists_Ioo_extr_on_Icc
- \+ *lemma* exists_deriv_eq_zero
- \+ *lemma* exists_has_deriv_at_eq_zero
- \+ *lemma* exists_local_extr_Ioo
- \+ *lemma* is_local_extr.deriv_eq_zero
- \+ *lemma* is_local_extr.fderiv_eq_zero
- \+ *lemma* is_local_extr.has_deriv_at_eq_zero
- \+ *lemma* is_local_extr.has_fderiv_at_eq_zero
- \+ *lemma* is_local_max.deriv_eq_zero
- \+ *lemma* is_local_max.fderiv_eq_zero
- \+ *lemma* is_local_max.has_deriv_at_eq_zero
- \+ *lemma* is_local_max.has_fderiv_at_eq_zero
- \+ *lemma* is_local_max_on.fderiv_within_eq_zero
- \+ *lemma* is_local_max_on.fderiv_within_nonpos
- \+ *lemma* is_local_max_on.has_fderiv_within_at_eq_zero
- \+ *lemma* is_local_max_on.has_fderiv_within_at_nonpos
- \+ *lemma* is_local_min.deriv_eq_zero
- \+ *lemma* is_local_min.fderiv_eq_zero
- \+ *lemma* is_local_min.has_deriv_at_eq_zero
- \+ *lemma* is_local_min.has_fderiv_at_eq_zero
- \+ *lemma* is_local_min_on.fderiv_within_eq_zero
- \+ *lemma* is_local_min_on.fderiv_within_nonneg
- \+ *lemma* is_local_min_on.has_fderiv_within_at_eq_zero
- \+ *lemma* is_local_min_on.has_fderiv_within_at_nonneg
- \+ *lemma* mem_pos_tangent_cone_at_of_segment_subset
- \+ *def* pos_tangent_cone_at
- \+ *lemma* pos_tangent_cone_at_mono
- \+ *lemma* pos_tangent_cone_at_univ

Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.is_const_of_fderiv_within_eq_zero
- \+ *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \+ *lemma* exists_deriv_eq_slope
- \+ *lemma* exists_has_deriv_at_eq_slope
- \+ *lemma* exists_ratio_deriv_eq_ratio_slope
- \+ *lemma* exists_ratio_has_deriv_at_eq_ratio_slope
- \- *theorem* norm_image_sub_le_of_norm_deriv_le_convex

Modified src/analysis/complex/polynomial.lean


Modified src/order/filter/basic.lean


Added src/order/filter/extr.lean
- \+ *lemma* is_extr_filter.comp_antimono
- \+ *lemma* is_extr_filter.comp_mono
- \+ *lemma* is_extr_filter.comp_tendsto
- \+ *lemma* is_extr_filter.filter_inf
- \+ *lemma* is_extr_filter.filter_mono
- \+ *lemma* is_extr_filter.neg
- \+ *def* is_extr_filter
- \+ *lemma* is_extr_filter_const
- \+ *lemma* is_extr_filter_dual_iff
- \+ *lemma* is_extr_on.comp_antimono
- \+ *lemma* is_extr_on.comp_mono
- \+ *lemma* is_extr_on.elim
- \+ *lemma* is_extr_on.inter
- \+ *lemma* is_extr_on.neg
- \+ *lemma* is_extr_on.on_preimage
- \+ *lemma* is_extr_on.on_subset
- \+ *def* is_extr_on
- \+ *lemma* is_extr_on_const
- \+ *lemma* is_extr_on_dual_iff
- \+ *lemma* is_max_filter.add
- \+ *lemma* is_max_filter.bicomp_mono
- \+ *lemma* is_max_filter.comp_antimono
- \+ *lemma* is_max_filter.comp_mono
- \+ *lemma* is_max_filter.comp_tendsto
- \+ *lemma* is_max_filter.filter_inf
- \+ *lemma* is_max_filter.filter_mono
- \+ *lemma* is_max_filter.inf
- \+ *lemma* is_max_filter.is_extr
- \+ *lemma* is_max_filter.max
- \+ *lemma* is_max_filter.min
- \+ *lemma* is_max_filter.neg
- \+ *lemma* is_max_filter.sub
- \+ *lemma* is_max_filter.sup
- \+ *def* is_max_filter
- \+ *lemma* is_max_filter_const
- \+ *lemma* is_max_filter_dual_iff
- \+ *lemma* is_max_on.add
- \+ *lemma* is_max_on.bicomp_mono
- \+ *lemma* is_max_on.comp_antimono
- \+ *lemma* is_max_on.comp_mono
- \+ *lemma* is_max_on.inf
- \+ *lemma* is_max_on.inter
- \+ *lemma* is_max_on.is_extr
- \+ *lemma* is_max_on.max
- \+ *lemma* is_max_on.min
- \+ *lemma* is_max_on.neg
- \+ *lemma* is_max_on.on_preimage
- \+ *lemma* is_max_on.on_subset
- \+ *lemma* is_max_on.sub
- \+ *lemma* is_max_on.sup
- \+ *def* is_max_on
- \+ *lemma* is_max_on_const
- \+ *lemma* is_max_on_dual_iff
- \+ *lemma* is_max_on_iff
- \+ *lemma* is_max_on_univ_iff
- \+ *lemma* is_min_filter.add
- \+ *lemma* is_min_filter.bicomp_mono
- \+ *lemma* is_min_filter.comp_antimono
- \+ *lemma* is_min_filter.comp_mono
- \+ *lemma* is_min_filter.comp_tendsto
- \+ *lemma* is_min_filter.filter_inf
- \+ *lemma* is_min_filter.filter_mono
- \+ *lemma* is_min_filter.inf
- \+ *lemma* is_min_filter.is_extr
- \+ *lemma* is_min_filter.max
- \+ *lemma* is_min_filter.min
- \+ *lemma* is_min_filter.neg
- \+ *lemma* is_min_filter.sub
- \+ *lemma* is_min_filter.sup
- \+ *def* is_min_filter
- \+ *lemma* is_min_filter_const
- \+ *lemma* is_min_filter_dual_iff
- \+ *lemma* is_min_on.add
- \+ *lemma* is_min_on.bicomp_mono
- \+ *lemma* is_min_on.comp_antimono
- \+ *lemma* is_min_on.comp_mono
- \+ *lemma* is_min_on.inf
- \+ *lemma* is_min_on.inter
- \+ *lemma* is_min_on.is_extr
- \+ *lemma* is_min_on.max
- \+ *lemma* is_min_on.min
- \+ *lemma* is_min_on.neg
- \+ *lemma* is_min_on.on_preimage
- \+ *lemma* is_min_on.on_subset
- \+ *lemma* is_min_on.sub
- \+ *lemma* is_min_on.sup
- \+ *def* is_min_on
- \+ *lemma* is_min_on_const
- \+ *lemma* is_min_on_dual_iff
- \+ *lemma* is_min_on_iff
- \+ *lemma* is_min_on_univ_iff

Modified src/topology/algebra/ordered.lean


Added src/topology/local_extr.lean
- \+ *lemma* is_extr_on.is_local_extr
- \+ *lemma* is_extr_on.localize
- \+ *lemma* is_local_extr.comp_antimono
- \+ *lemma* is_local_extr.comp_continuous
- \+ *lemma* is_local_extr.comp_continuous_on
- \+ *lemma* is_local_extr.comp_mono
- \+ *lemma* is_local_extr.elim
- \+ *lemma* is_local_extr.neg
- \+ *lemma* is_local_extr.on
- \+ *def* is_local_extr
- \+ *lemma* is_local_extr_const
- \+ *lemma* is_local_extr_on.comp_antimono
- \+ *lemma* is_local_extr_on.comp_mono
- \+ *lemma* is_local_extr_on.elim
- \+ *lemma* is_local_extr_on.inter
- \+ *lemma* is_local_extr_on.is_local_extr
- \+ *lemma* is_local_extr_on.neg
- \+ *lemma* is_local_extr_on.on_subset
- \+ *def* is_local_extr_on
- \+ *lemma* is_local_extr_on_const
- \+ *lemma* is_local_max.add
- \+ *lemma* is_local_max.bicomp_mono
- \+ *lemma* is_local_max.comp_antimono
- \+ *lemma* is_local_max.comp_continuous
- \+ *lemma* is_local_max.comp_continuous_on
- \+ *lemma* is_local_max.comp_mono
- \+ *lemma* is_local_max.inf
- \+ *lemma* is_local_max.max
- \+ *lemma* is_local_max.min
- \+ *lemma* is_local_max.neg
- \+ *lemma* is_local_max.on
- \+ *lemma* is_local_max.sub
- \+ *lemma* is_local_max.sup
- \+ *def* is_local_max
- \+ *lemma* is_local_max_const
- \+ *lemma* is_local_max_on.add
- \+ *lemma* is_local_max_on.bicomp_mono
- \+ *lemma* is_local_max_on.comp_antimono
- \+ *lemma* is_local_max_on.comp_mono
- \+ *lemma* is_local_max_on.inf
- \+ *lemma* is_local_max_on.inter
- \+ *lemma* is_local_max_on.is_local_max
- \+ *lemma* is_local_max_on.max
- \+ *lemma* is_local_max_on.min
- \+ *lemma* is_local_max_on.neg
- \+ *lemma* is_local_max_on.on_subset
- \+ *lemma* is_local_max_on.sub
- \+ *lemma* is_local_max_on.sup
- \+ *def* is_local_max_on
- \+ *lemma* is_local_max_on_const
- \+ *lemma* is_local_min.add
- \+ *lemma* is_local_min.bicomp_mono
- \+ *lemma* is_local_min.comp_antimono
- \+ *lemma* is_local_min.comp_continuous
- \+ *lemma* is_local_min.comp_continuous_on
- \+ *lemma* is_local_min.comp_mono
- \+ *lemma* is_local_min.inf
- \+ *lemma* is_local_min.max
- \+ *lemma* is_local_min.min
- \+ *lemma* is_local_min.neg
- \+ *lemma* is_local_min.on
- \+ *lemma* is_local_min.sub
- \+ *lemma* is_local_min.sup
- \+ *def* is_local_min
- \+ *lemma* is_local_min_const
- \+ *lemma* is_local_min_on.add
- \+ *lemma* is_local_min_on.bicomp_mono
- \+ *lemma* is_local_min_on.comp_antimono
- \+ *lemma* is_local_min_on.comp_mono
- \+ *lemma* is_local_min_on.inf
- \+ *lemma* is_local_min_on.inter
- \+ *lemma* is_local_min_on.is_local_min
- \+ *lemma* is_local_min_on.max
- \+ *lemma* is_local_min_on.min
- \+ *lemma* is_local_min_on.neg
- \+ *lemma* is_local_min_on.on_subset
- \+ *lemma* is_local_min_on.sub
- \+ *lemma* is_local_min_on.sup
- \+ *def* is_local_min_on
- \+ *lemma* is_local_min_on_const
- \+ *lemma* is_max_on.is_local_max
- \+ *lemma* is_max_on.localize
- \+ *lemma* is_min_on.is_local_min
- \+ *lemma* is_min_on.localize

Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2019-12-20 20:34:56](https://github.com/leanprover-community/mathlib/commit/883d974)
feat(algebra/module): sum_smul' (for semimodules) ([#1752](https://github.com/leanprover-community/mathlib/pull/1752))
* feat(algebra/module): sum_smul' (for semimodules)
* adding docstring
* use `classical` tactic
* moving ' name to the weaker theorem
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_smul'
- \- *lemma* finset.sum_smul

Modified src/algebra/module.lean
- \+ *lemma* finset.sum_smul



## [2019-12-19 06:24:53](https://github.com/leanprover-community/mathlib/commit/e875492)
chore(algebra/module) remove an unneeded commutativity assumption ([#1813](https://github.com/leanprover-community/mathlib/pull/1813))
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map.is_linear_map_smul'



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
- \+ *theorem* set.range_inl_union_range_inr
- \+ *theorem* set.range_quot_mk

Modified src/measure_theory/lebesgue_measure.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_inf_principal_ne_bot_of_image_mem
- \+/\- *lemma* filter.comap_mono
- \+ *lemma* filter.comap_ne_bot_of_range_mem
- \+/\- *lemma* filter.map_inf
- \+ *lemma* filter.map_inf_le
- \+/\- *lemma* filter.map_mono
- \- *lemma* filter.monotone_comap
- \- *lemma* filter.monotone_map
- \+ *lemma* filter.tendsto.inf
- \+ *lemma* filter.tendsto.ne_bot

Modified src/order/filter/lift.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* compact.exists_forall_ge
- \+ *lemma* compact.exists_forall_le
- \- *lemma* exists_forall_ge_of_compact_of_continuous
- \- *lemma* exists_forall_le_of_compact_of_continuous

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* is_closed.mem_of_nhds_within_ne_bot
- \+ *lemma* nhds_within_ne_bot_of_mem

Modified src/topology/homeomorph.lean


Modified src/topology/instances/complex.lean
- \+/\- *def* complex.real_prod_homeo

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* compact.adherence_nhdset
- \+ *lemma* compact.elim_finite_subcover
- \+ *lemma* compact.elim_finite_subcover_image
- \+ *lemma* compact.image
- \+ *lemma* compact.image_of_continuous_on
- \+ *lemma* compact.inter_left
- \+ *lemma* compact.inter_right
- \+ *lemma* compact.prod
- \+ *lemma* compact.union
- \+ *lemma* compact_Union
- \- *lemma* compact_Union_of_compact
- \- *lemma* compact_adherence_nhdset
- \- *lemma* compact_bUnion_of_compact
- \- *lemma* compact_elim_finite_subcover
- \- *lemma* compact_elim_finite_subcover_image
- \- *lemma* compact_iff_compact_image_of_embedding
- \- *lemma* compact_image
- \- *lemma* compact_inter
- \- *lemma* compact_of_closed
- \- *lemma* compact_of_finite
- \- *lemma* compact_prod
- \- *lemma* compact_union_of_compact
- \+ *lemma* embedding.compact_iff_compact_image
- \+ *lemma* is_closed.compact
- \+ *lemma* set.finite.compact
- \+ *lemma* set.finite.compact_bUnion

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


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/module.lean


Modified src/category_theory/limits/preserves.lean


Modified src/group_theory/coset.lean


Modified src/logic/basic.lean


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Added src/tactic/library_note.lean
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
- \- *lemma* decidable.min_le_max

Modified src/algebra/order_functions.lean
- \+ *lemma* min_le_max

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* real.exists_cos_eq_zero
- \+/\- *lemma* real.exists_sin_eq

Modified src/topology/algebra/ordered.lean
- \+ *lemma* intermediate_value_Icc'
- \+ *lemma* intermediate_value_Icc
- \+ *lemma* intermediate_value_univ
- \+ *lemma* is_connected.forall_Icc_subset
- \+ *lemma* is_connected.intermediate_value
- \+ *lemma* is_connected_Icc
- \+ *lemma* is_connected_Ici
- \+ *lemma* is_connected_Ico
- \+ *lemma* is_connected_Iic
- \+ *lemma* is_connected_Iio
- \+ *lemma* is_connected_Ioc
- \+ *lemma* is_connected_Ioi
- \+ *lemma* is_connected_Ioo
- \+ *lemma* is_connected_iff_forall_Icc_subset

Modified src/topology/instances/real.lean
- \- *lemma* real.intermediate_value'
- \- *lemma* real.intermediate_value

Modified src/topology/subset_properties.lean
- \+ *theorem* is_connected.closure
- \+ *theorem* is_connected.image
- \+ *theorem* is_connected.union
- \+ *theorem* is_connected_closed_iff
- \- *theorem* is_connected_closure
- \+ *theorem* is_connected_of_forall
- \+ *theorem* is_connected_of_forall_pair
- \- *theorem* is_connected_union



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


Added src/geometry/manifold/basic_smooth_bundle.lean
- \+ *lemma* basic_smooth_bundle_core.base_set
- \+ *def* basic_smooth_bundle_core.chart
- \+ *lemma* basic_smooth_bundle_core.chart_at_inv_fun_fst
- \+ *lemma* basic_smooth_bundle_core.chart_at_to_fun_fst
- \+ *lemma* basic_smooth_bundle_core.chart_source
- \+ *lemma* basic_smooth_bundle_core.chart_target
- \+ *lemma* basic_smooth_bundle_core.mem_atlas_iff
- \+ *lemma* basic_smooth_bundle_core.mem_chart_source_iff
- \+ *lemma* basic_smooth_bundle_core.mem_chart_target_iff
- \+ *def* basic_smooth_bundle_core.to_topological_fiber_bundle_core
- \+ *structure* basic_smooth_bundle_core
- \+ *def* tangent_bundle.proj
- \+ *def* tangent_bundle
- \+ *def* tangent_bundle_core
- \+ *lemma* tangent_bundle_model_space_chart_at
- \+ *lemma* tangent_bundle_model_space_topology_eq_prod
- \+ *lemma* tangent_bundle_proj_continuous
- \+ *lemma* tangent_bundle_proj_open
- \+ *def* tangent_space

Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous.smul
- \- *lemma* continuous_smul'
- \+/\- *lemma* continuous_smul
- \+ *abbreviation* topological_vector_space

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
- \+ *lemma* add_div'
- \+ *lemma* div_add'
- \+ *lemma* div_eq_iff
- \+ *lemma* eq_div_iff
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
- \+ *lemma* cauchy_seq_of_edist_le_geometric_two
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \+ *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* ennreal.tsum_geometric
- \- *lemma* has_sum_geometric_nnreal
- \+ *lemma* nnreal.has_sum_geometric
- \+ *lemma* nnreal.summable_geometric
- \+ *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
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
- \+ *lemma* set.Ici_subset_Ioi
- \+ *lemma* set.Iic_subset_Iio
- \+ *lemma* set.dual_Icc
- \+ *lemma* set.dual_Ici
- \+ *lemma* set.dual_Ico
- \+ *lemma* set.dual_Iic
- \+ *lemma* set.dual_Iio
- \+ *lemma* set.dual_Ioc
- \+ *lemma* set.dual_Ioi
- \+ *lemma* set.dual_Ioo
- \+/\- *lemma* set.nonempty_Icc
- \+/\- *lemma* set.nonempty_Ico
- \+/\- *lemma* set.nonempty_Ioc

Modified src/measure_theory/borel_space.lean


Modified src/order/basic.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.binfi_sets_eq
- \- *lemma* filter.infi_sets_eq'
- \+ *lemma* filter.mem_binfi

Modified src/order/filter/lift.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* closure_lt_subset_le
- \+ *lemma* exists_Ico_subset_of_mem_nhds'
- \+ *lemma* exists_Ico_subset_of_mem_nhds
- \+ *lemma* exists_Ioc_subset_of_mem_nhds'
- \+ *lemma* exists_Ioc_subset_of_mem_nhds
- \- *lemma* mem_nhds_orderable_dest
- \+/\- *lemma* nhds_eq_orderable

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
- \+ *lemma* finset.prod_pair

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/convex.lean
- \+ *lemma* convex.add
- \+ *lemma* convex.affinity
- \+ *lemma* convex.center_mass_mem
- \+ *lemma* convex.closure
- \+ *lemma* convex.inter
- \+ *lemma* convex.interior
- \+ *lemma* convex.is_linear_image
- \+ *lemma* convex.is_linear_preimage
- \+ *lemma* convex.linear_image
- \+ *lemma* convex.linear_preimage
- \+ *lemma* convex.neg
- \+ *lemma* convex.neg_preimage
- \+ *lemma* convex.prod
- \+ *lemma* convex.smul
- \+ *lemma* convex.smul_preimage
- \+ *lemma* convex.sub
- \+ *lemma* convex.sum_mem
- \+ *lemma* convex.translate
- \+/\- *lemma* convex_Inter
- \- *lemma* convex_add
- \- *lemma* convex_affinity
- \- *lemma* convex_closure
- \- *lemma* convex_halfplane
- \+/\- *lemma* convex_halfspace_ge
- \+/\- *lemma* convex_halfspace_gt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_lt
- \+ *lemma* convex_hyperplane
- \+ *lemma* convex_iff_sum_mem
- \- *lemma* convex_inter
- \- *lemma* convex_interior
- \- *lemma* convex_le_of_convex_on
- \- *lemma* convex_linear_image'
- \- *lemma* convex_linear_image
- \- *lemma* convex_linear_preimage'
- \- *lemma* convex_linear_preimage
- \- *lemma* convex_lt_of_convex_on
- \- *lemma* convex_neg
- \- *lemma* convex_neg_preimage
- \+ *lemma* convex_on.add
- \+ *lemma* convex_on.convex_epigraph
- \+ *lemma* convex_on.convex_le
- \+ *lemma* convex_on.convex_lt
- \+ *lemma* convex_on.le_on_interval
- \+ *lemma* convex_on.map_center_mass_le
- \+ *lemma* convex_on.map_sum_le
- \+ *lemma* convex_on.smul
- \+ *lemma* convex_on.subset
- \- *lemma* convex_on_add
- \+ *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* convex_on_linorder
- \- *lemma* convex_on_smul
- \- *lemma* convex_on_subset
- \- *lemma* convex_on_sum
- \- *lemma* convex_prod
- \+ *lemma* convex_real_iff
- \+ *lemma* convex_sInter
- \- *lemma* convex_smul
- \- *lemma* convex_smul_preimage
- \- *lemma* convex_sub
- \- *lemma* convex_submodule
- \- *lemma* convex_subspace
- \- *lemma* convex_sum
- \- *lemma* convex_sum_iff
- \- *lemma* convex_translation
- \+ *lemma* finset.center_mass_empty
- \+ *lemma* finset.center_mass_insert
- \+ *lemma* finset.center_mass_pair
- \+ *lemma* finset.center_mass_singleton
- \- *lemma* image_Icc_zero_one_eq_segment
- \- *lemma* le_on_interval_of_convex_on
- \+/\- *lemma* left_mem_segment
- \+/\- *lemma* right_mem_segment
- \+/\- *def* segment
- \+ *lemma* segment_eq_Icc'
- \+ *lemma* segment_eq_image_Icc_zero_one'
- \+ *lemma* segment_eq_image_Icc_zero_one
- \+/\- *lemma* segment_translate
- \+ *lemma* segment_translate_preimage
- \+ *lemma* submodule.convex
- \+ *lemma* subspace.convex

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
- \+/\- *lemma* ennreal.tendsto_coe
- \+ *lemma* ennreal.tendsto_nat_nhds_top
- \+ *lemma* ennreal.tsum_coe_ne_top_iff_summable



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
- \+/\- *theorem* has_fderiv_at_filter_real_equiv
- \+/\- *theorem* has_fderiv_within_at.lim

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_at.lim_zero

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* ne_mem_of_tendsto_norm_at_top



## [2019-12-15 22:29:01](https://github.com/leanprover-community/mathlib/commit/699da42)
feat(data/set/intervals): add `nonempty_Icc` etc, `image_(add/mul)_(left/right)_Icc` ([#1803](https://github.com/leanprover-community/mathlib/pull/1803))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \- *lemma* ivl_stretch
- \- *lemma* ivl_translate

Modified src/data/set/basic.lean
- \+/\- *lemma* set.inter_singleton_ne_empty
- \+ *theorem* set.nonempty.image_const

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.image_add_left_Icc
- \+ *lemma* set.image_add_right_Icc
- \+ *lemma* set.image_mul_left_Icc'
- \+ *lemma* set.image_mul_left_Icc
- \+ *lemma* set.image_mul_right_Icc'
- \+ *lemma* set.image_mul_right_Icc
- \+ *lemma* set.nonempty_Icc
- \+ *lemma* set.nonempty_Ici
- \+ *lemma* set.nonempty_Ico
- \+ *lemma* set.nonempty_Iic
- \+ *lemma* set.nonempty_Ioc



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
- \+/\- *lemma* ennreal.coe_div
- \+ *lemma* ennreal.coe_inv_two
- \+/\- *lemma* ennreal.coe_le_one_iff
- \+ *lemma* ennreal.coe_lt_coe_nat
- \+/\- *lemma* ennreal.coe_lt_one_iff
- \+/\- *lemma* ennreal.coe_nat
- \+ *lemma* ennreal.coe_nat_lt_coe
- \+ *lemma* ennreal.coe_nat_lt_coe_nat
- \+ *lemma* ennreal.coe_nat_ne_top
- \+ *lemma* ennreal.coe_sub_infty
- \+ *lemma* ennreal.coe_two
- \+/\- *lemma* ennreal.div_self
- \+ *lemma* ennreal.div_top
- \+ *lemma* ennreal.inv_lt_one
- \+ *lemma* ennreal.inv_mul_cancel
- \+ *lemma* ennreal.inv_one
- \+ *lemma* ennreal.inv_two_add_inv_two
- \+ *lemma* ennreal.le_sub_add_self
- \+ *lemma* ennreal.max_eq_zero_iff
- \+ *lemma* ennreal.max_mul
- \+ *lemma* ennreal.mul_div_cancel'
- \+ *lemma* ennreal.mul_div_cancel
- \+ *lemma* ennreal.mul_eq_mul_right
- \+/\- *lemma* ennreal.mul_inv_cancel
- \- *lemma* ennreal.mul_le_if_le_inv
- \+ *lemma* ennreal.mul_le_iff_le_inv
- \+ *lemma* ennreal.mul_le_mul
- \+ *lemma* ennreal.mul_le_mul_right
- \+ *lemma* ennreal.mul_left_mono
- \+ *lemma* ennreal.mul_lt_mul_left
- \+ *lemma* ennreal.mul_lt_mul_right
- \+ *lemma* ennreal.mul_max
- \+ *lemma* ennreal.mul_ne_top
- \+ *lemma* ennreal.mul_right_mono
- \+ *lemma* ennreal.mul_sub
- \+ *lemma* ennreal.one_half_lt_one
- \+/\- *lemma* ennreal.one_le_coe_iff
- \+/\- *lemma* ennreal.one_lt_coe_iff
- \+ *lemma* ennreal.one_lt_two
- \+ *lemma* ennreal.one_sub_inv_two
- \+ *lemma* ennreal.pow_eq_top
- \+ *lemma* ennreal.pow_lt_top
- \+ *lemma* ennreal.pow_ne_top
- \+ *lemma* ennreal.sub_eq_of_add_eq
- \+ *lemma* ennreal.sub_half
- \+ *lemma* ennreal.sub_le_sub_add_sub
- \+ *lemma* ennreal.sub_mul
- \+/\- *lemma* ennreal.to_nnreal_coe
- \+ *lemma* ennreal.top_div
- \+ *lemma* ennreal.top_pow
- \+ *lemma* ennreal.two_ne_top
- \+ *lemma* ennreal.two_ne_zero
- \+ *lemma* ennreal.two_pos
- \+ *lemma* ennreal.zero_div
- \+/\- *lemma* ennreal.zero_lt_coe_iff

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.inv_one
- \+ *lemma* nnreal.two_inv_lt_one



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
- \+/\- *def* con.ker_lift

Added src/group_theory/monoid_localization.lean
- \+ *lemma* add_submonoid.r'.add
- \+ *lemma* add_submonoid.r'.transitive
- \+ *def* add_submonoid.r'
- \+ *def* monoid_localization.aux
- \+ *lemma* monoid_localization.exists_rep
- \+ *lemma* monoid_localization.funext
- \+ *theorem* monoid_localization.ind
- \+ *theorem* monoid_localization.induction_on
- \+ *lemma* monoid_localization.is_unit_of_of_comp
- \+ *def* monoid_localization.lift'
- \+ *lemma* monoid_localization.lift'_apply_of
- \+ *lemma* monoid_localization.lift'_comp_of
- \+ *lemma* monoid_localization.lift'_eq_iff
- \+ *lemma* monoid_localization.lift'_mk
- \+ *lemma* monoid_localization.lift'_of
- \+ *lemma* monoid_localization.lift_apply_of
- \+ *lemma* monoid_localization.lift_comp_of
- \+ *lemma* monoid_localization.lift_eq_iff
- \+ *lemma* monoid_localization.lift_mk
- \+ *lemma* monoid_localization.lift_of
- \+ *lemma* monoid_localization.lift_on_beta
- \+ *def* monoid_localization.map
- \+ *lemma* monoid_localization.map_comp_map
- \+ *lemma* monoid_localization.map_comp_of
- \+ *lemma* monoid_localization.map_eq
- \+ *lemma* monoid_localization.map_ext
- \+ *lemma* monoid_localization.map_id
- \+ *lemma* monoid_localization.map_map
- \+ *lemma* monoid_localization.map_mk
- \+ *lemma* monoid_localization.map_of
- \+ *def* monoid_localization.mk
- \+ *lemma* monoid_localization.mk_eq
- \+ *lemma* monoid_localization.mk_eq_iff_of_eq
- \+ *lemma* monoid_localization.mk_eq_mul_mk_one
- \+ *lemma* monoid_localization.mk_eq_of_eq
- \+ *lemma* monoid_localization.mk_is_unit'
- \+ *lemma* monoid_localization.mk_is_unit
- \+ *lemma* monoid_localization.mk_mul_cancel_left
- \+ *lemma* monoid_localization.mk_mul_cancel_right
- \+ *lemma* monoid_localization.mk_mul_mk
- \+ *lemma* monoid_localization.mk_self'
- \+ *lemma* monoid_localization.mk_self
- \+ *def* monoid_localization.of
- \+ *lemma* monoid_localization.of_eq_mk
- \+ *lemma* monoid_localization.of_is_unit'
- \+ *lemma* monoid_localization.of_is_unit
- \+ *lemma* monoid_localization.of_ker_iff
- \+ *lemma* monoid_localization.of_mul_mk
- \+ *lemma* monoid_localization.one_rel
- \+ *lemma* monoid_localization.r_le_ker_aux
- \+ *def* monoid_localization.to_units
- \+ *lemma* monoid_localization.to_units_inv
- \+ *lemma* monoid_localization.to_units_map_inv
- \+ *lemma* monoid_localization.to_units_mk
- \+ *def* monoid_localization.units_restrict
- \+ *lemma* monoid_localization.units_restrict_mul
- \+ *def* monoid_localization
- \+ *def* submonoid.r'
- \+ *def* submonoid.r
- \+ *theorem* submonoid.r_eq_r'



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
- \+ *abbreviation* vector_space

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
- \+/\- *theorem* inv_comm_of_comm
- \+/\- *theorem* mul_inv_eq_one
- \+/\- *lemma* mul_left_eq_self
- \+ *theorem* mul_left_surjective
- \+/\- *lemma* mul_right_eq_self
- \+ *theorem* mul_right_surjective



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
- \- *theorem* set.Inter_eq_sInter_range
- \- *theorem* set.Union_eq_sUnion_range

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
- \+ *lemma* abs_max_sub_max_le_abs
- \+ *lemma* max_zero_sub_eq_self

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.neg_mk
- \+ *def* measure_theory.ae_eq_fun.pos_part
- \+ *lemma* measure_theory.ae_eq_fun.pos_part_to_fun

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_eq_lintegral_max_sub_lintegral_min
- \+ *lemma* measure_theory.integral_eq_lintegral_of_nonneg_ae
- \+ *lemma* measure_theory.integral_le_integral_of_le_ae
- \+ *lemma* measure_theory.integral_nonneg_of_nonneg_ae
- \+ *lemma* measure_theory.integral_nonpos_of_nonpos_ae
- \+ *lemma* measure_theory.l1.integral_coe_eq_integral
- \+ *lemma* measure_theory.l1.integral_eq_norm_pos_part_sub
- \+/\- *lemma* measure_theory.l1.simple_func.coe_add
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg
- \+ *lemma* measure_theory.l1.simple_func.coe_neg_part
- \+ *lemma* measure_theory.l1.simple_func.coe_pos_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_smul
- \+/\- *lemma* measure_theory.l1.simple_func.coe_sub
- \+/\- *lemma* measure_theory.l1.simple_func.coe_zero
- \+/\- *def* measure_theory.l1.simple_func.integral
- \+ *lemma* measure_theory.l1.simple_func.integral_eq_bintegral
- \+ *lemma* measure_theory.l1.simple_func.integral_eq_norm_pos_part_sub
- \+ *def* measure_theory.l1.simple_func.neg_part
- \+ *lemma* measure_theory.l1.simple_func.neg_part_to_simple_func
- \+ *def* measure_theory.l1.simple_func.pos_part
- \+ *lemma* measure_theory.l1.simple_func.pos_part_to_simple_func
- \+ *lemma* measure_theory.norm_integral_le_integral_norm
- \- *lemma* measure_theory.of_real_norm_integral_le_lintegral_norm
- \+ *lemma* measure_theory.simple_func.bintegral_neg
- \+ *lemma* measure_theory.simple_func.bintegral_sub
- \+ *def* measure_theory.simple_func.neg_part
- \+ *lemma* measure_theory.simple_func.neg_part_map_norm
- \+ *def* measure_theory.simple_func.pos_part
- \+ *lemma* measure_theory.simple_func.pos_part_map_norm
- \+ *lemma* measure_theory.simple_func.pos_part_sub_neg_part

Modified src/measure_theory/borel_space.lean
- \+ *def* borel
- \+ *lemma* borel_comap
- \+ *lemma* borel_eq_generate_Iio
- \+ *lemma* borel_eq_generate_Ioi
- \+ *lemma* borel_eq_generate_from_of_subbasis
- \+ *lemma* borel_eq_subtype
- \+ *lemma* borel_induced
- \+ *lemma* borel_prod
- \+ *lemma* borel_prod_le
- \+ *lemma* ennreal.measurable.add
- \+ *lemma* ennreal.measurable.mul
- \+ *lemma* ennreal.measurable.sub
- \- *lemma* ennreal.measurable_add
- \- *lemma* ennreal.measurable_mul
- \- *lemma* ennreal.measurable_sub
- \+ *lemma* is_measurable_Ico
- \+ *lemma* is_measurable_Iio
- \+ *lemma* is_measurable_Ioo
- \+ *lemma* is_measurable_ball
- \+ *lemma* is_measurable_closure
- \+ *lemma* is_measurable_interior
- \+ *lemma* is_measurable_le
- \+ *lemma* is_measurable_of_is_closed
- \+ *lemma* is_measurable_of_is_open
- \+ *lemma* is_measurable_singleton
- \+ *lemma* measurable.add
- \+ *lemma* measurable.infi
- \+ *lemma* measurable.infi_Prop
- \+ *lemma* measurable.is_glb
- \+ *lemma* measurable.is_lub
- \+ *lemma* measurable.max
- \+ *lemma* measurable.min
- \+ *lemma* measurable.mul
- \+ *lemma* measurable.neg
- \+ *lemma* measurable.sub
- \+ *lemma* measurable.supr
- \+ *lemma* measurable.supr_Prop
- \+ *lemma* measurable_coe_int_real
- \+ *lemma* measurable_finset_sum
- \+ *lemma* measurable_neg_iff
- \+ *lemma* measurable_of_continuous2
- \+ *lemma* measurable_of_continuous
- \- *def* measure_theory.borel
- \- *lemma* measure_theory.borel_comap
- \- *lemma* measure_theory.borel_eq_generate_Iio
- \- *lemma* measure_theory.borel_eq_generate_Ioi
- \- *lemma* measure_theory.borel_eq_generate_from_of_subbasis
- \- *lemma* measure_theory.borel_eq_subtype
- \- *lemma* measure_theory.borel_induced
- \- *lemma* measure_theory.borel_prod
- \- *lemma* measure_theory.borel_prod_le
- \- *lemma* measure_theory.is_measurable_Ico
- \- *lemma* measure_theory.is_measurable_Iio
- \- *lemma* measure_theory.is_measurable_Ioo
- \- *lemma* measure_theory.is_measurable_ball
- \- *lemma* measure_theory.is_measurable_closure
- \- *lemma* measure_theory.is_measurable_interior
- \- *lemma* measure_theory.is_measurable_of_is_closed
- \- *lemma* measure_theory.is_measurable_of_is_open
- \- *lemma* measure_theory.is_measurable_singleton
- \- *lemma* measure_theory.measurable.infi
- \- *lemma* measure_theory.measurable.infi_Prop
- \- *lemma* measure_theory.measurable.is_glb
- \- *lemma* measure_theory.measurable.is_lub
- \- *lemma* measure_theory.measurable.supr
- \- *lemma* measure_theory.measurable.supr_Prop
- \- *lemma* measure_theory.measurable_add
- \- *lemma* measure_theory.measurable_coe_int_real
- \- *lemma* measure_theory.measurable_finset_sum
- \- *lemma* measure_theory.measurable_le
- \- *lemma* measure_theory.measurable_mul
- \- *lemma* measure_theory.measurable_neg
- \- *lemma* measure_theory.measurable_neg_iff
- \- *lemma* measure_theory.measurable_of_continuous2
- \- *lemma* measure_theory.measurable_of_continuous
- \- *lemma* measure_theory.measurable_sub
- \+ *lemma* nnreal.measurable.add
- \+ *lemma* nnreal.measurable.mul
- \+ *lemma* nnreal.measurable.sub
- \- *lemma* nnreal.measurable_add
- \- *lemma* nnreal.measurable_mul
- \- *lemma* nnreal.measurable_sub

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.ae_eq_fun.integrable.add
- \+ *lemma* measure_theory.ae_eq_fun.integrable.neg
- \+ *lemma* measure_theory.ae_eq_fun.integrable.smul
- \+ *lemma* measure_theory.ae_eq_fun.integrable.sub
- \- *lemma* measure_theory.ae_eq_fun.integrable_add
- \- *lemma* measure_theory.ae_eq_fun.integrable_neg
- \- *lemma* measure_theory.ae_eq_fun.integrable_smul
- \- *lemma* measure_theory.ae_eq_fun.integrable_sub
- \+ *lemma* measure_theory.integrable.add
- \+ *lemma* measure_theory.integrable.max_zero
- \+ *lemma* measure_theory.integrable.min_zero
- \+ *lemma* measure_theory.integrable.neg
- \+ *lemma* measure_theory.integrable.norm
- \+ *lemma* measure_theory.integrable.smul
- \+ *lemma* measure_theory.integrable.smul_iff
- \+ *lemma* measure_theory.integrable.sub
- \- *lemma* measure_theory.integrable_add
- \- *lemma* measure_theory.integrable_neg
- \- *lemma* measure_theory.integrable_norm
- \+ *lemma* measure_theory.integrable_of_le_ae
- \- *lemma* measure_theory.integrable_smul
- \- *lemma* measure_theory.integrable_smul_iff
- \- *lemma* measure_theory.integrable_sub
- \+/\- *lemma* measure_theory.l1.coe_add
- \+/\- *lemma* measure_theory.l1.coe_neg
- \+ *lemma* measure_theory.l1.coe_pos_part
- \+/\- *lemma* measure_theory.l1.coe_smul
- \+/\- *lemma* measure_theory.l1.coe_sub
- \+/\- *lemma* measure_theory.l1.coe_zero
- \+ *lemma* measure_theory.l1.continuous_neg_part
- \+ *lemma* measure_theory.l1.continuous_pos_part
- \+ *def* measure_theory.l1.neg_part
- \+ *lemma* measure_theory.l1.neg_part_to_fun_eq_max
- \+ *lemma* measure_theory.l1.neg_part_to_fun_eq_min
- \+ *lemma* measure_theory.l1.norm_le_norm_of_ae_le
- \+ *lemma* measure_theory.l1.norm_of_fun_eq_lintegral_norm
- \+ *lemma* measure_theory.l1.of_fun_sub
- \+ *def* measure_theory.l1.pos_part
- \+ *lemma* measure_theory.l1.pos_part_to_fun
- \+/\- *lemma* measure_theory.lintegral_nnnorm_add
- \+ *lemma* measure_theory.lintegral_norm_eq_lintegral_edist

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.fst
- \+ *lemma* measurable.prod_mk
- \+ *lemma* measurable.snd
- \+ *lemma* measurable.subtype_mk
- \+ *lemma* measurable.subtype_val
- \- *lemma* measurable_fst
- \- *lemma* measurable_prod_mk
- \- *lemma* measurable_snd
- \- *lemma* measurable_subtype_mk
- \- *lemma* measurable_subtype_val

Modified src/measure_theory/simple_func_dense.lean




## [2019-12-11 17:17:17](https://github.com/leanprover-community/mathlib/commit/a8f6e23)
feat(data/list/basic): list.lex.not_nil_right ([#1797](https://github.com/leanprover-community/mathlib/pull/1797))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.lex.not_nil_right



## [2019-12-11 09:52:57](https://github.com/leanprover-community/mathlib/commit/23e8ac7)
feat(ring_theory/algebra): elementary simp-lemmas for aeval ([#1795](https://github.com/leanprover-community/mathlib/pull/1795))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* mv_polynomial.aeval_C
- \+ *lemma* mv_polynomial.aeval_X
- \+ *lemma* polynomial.aeval_C
- \+ *lemma* polynomial.aeval_X



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
- \+/\- *lemma* continuous_equiv_fun_basis
- \+/\- *lemma* linear_map.continuous_on_pi

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.pi_apply_eq_sum_univ
- \+ *lemma* submodule.map_subtype_top

Modified src/linear_algebra/basis.lean
- \- *lemma* linear_equiv.is_basis

Modified src/linear_algebra/dimension.lean
- \- *theorem* dim_quotient
- \+ *theorem* dim_quotient_add_dim
- \+ *theorem* dim_quotient_le

Modified src/linear_algebra/finite_dimensional.lean
- \- *lemma* finite_dimensional.card_eq_findim
- \- *lemma* finite_dimensional.dim_eq_card
- \+ *lemma* finite_dimensional.dim_eq_card_basis
- \+/\- *lemma* finite_dimensional.exists_is_basis_finite
- \- *lemma* finite_dimensional.fg_of_finite_basis
- \- *lemma* finite_dimensional.findim_eq_card
- \+ *lemma* finite_dimensional.findim_eq_card_basis'
- \+ *lemma* finite_dimensional.findim_eq_card_basis
- \- *lemma* finite_dimensional.findim_submodule_le
- \- *lemma* finite_dimensional.finite_dimensional_of_finite_basis
- \+ *lemma* finite_dimensional.iff_fg
- \- *lemma* finite_dimensional.of_fg
- \+ *lemma* finite_dimensional.of_finite_basis
- \+ *theorem* finite_dimensional.span_of_finite
- \+ *theorem* linear_equiv.findim_eq
- \+ *lemma* linear_map.comp_eq_id_comm
- \+ *lemma* linear_map.finite_dimensional_of_surjective
- \+ *theorem* submodule.fg_iff_finite_dimensional
- \+ *lemma* submodule.findim_le
- \+ *theorem* submodule.findim_quotient_add_findim
- \+ *lemma* submodule.findim_quotient_le

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
- \+ *lemma* set.one_smul_set
- \+ *def* set.pointwise_smul
- \+ *def* set.smul_set
- \+ *lemma* set.smul_set_eq_pointwise_smul_singleton
- \+ *lemma* zero_smul_set

Modified src/analysis/convex.lean
- \+ *lemma* convex_closure
- \+ *lemma* convex_iff₂:
- \+ *lemma* convex_iff₃:
- \+ *lemma* convex_interior

Modified src/topology/algebra/module.lean
- \+ *lemma* is_closed_map_smul_of_ne_zero
- \+ *lemma* is_closed_map_smul_of_unit
- \+ *lemma* is_open_map_smul_of_ne_zero
- \+ *lemma* is_open_map_smul_of_unit



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


Added src/tactic/ring_exp.lean
- \+ *lemma* tactic.ring_exp.add_overlap_pf
- \+ *lemma* tactic.ring_exp.add_overlap_pf_zero
- \+ *lemma* tactic.ring_exp.add_pf_sum_gt
- \+ *lemma* tactic.ring_exp.add_pf_sum_lt
- \+ *lemma* tactic.ring_exp.add_pf_sum_overlap
- \+ *lemma* tactic.ring_exp.add_pf_sum_overlap_zero
- \+ *lemma* tactic.ring_exp.add_pf_sum_z
- \+ *lemma* tactic.ring_exp.add_pf_z_sum
- \+ *lemma* tactic.ring_exp.atom_to_sum_pf
- \+ *lemma* tactic.ring_exp.base_to_exp_pf
- \+ *structure* tactic.ring_exp.coeff
- \+ *lemma* tactic.ring_exp.div_pf
- \+ *inductive* tactic.ring_exp.ex_type
- \+ *lemma* tactic.ring_exp.exp_congr
- \+ *lemma* tactic.ring_exp.exp_to_prod_pf
- \+ *lemma* tactic.ring_exp.inverse_pf
- \+ *lemma* tactic.ring_exp.mul_coeff_pf_mul_one
- \+ *lemma* tactic.ring_exp.mul_coeff_pf_one_mul
- \+ *lemma* tactic.ring_exp.mul_p_pf_sum
- \+ *lemma* tactic.ring_exp.mul_p_pf_zero
- \+ *lemma* tactic.ring_exp.mul_pf_c_c
- \+ *lemma* tactic.ring_exp.mul_pf_c_prod
- \+ *lemma* tactic.ring_exp.mul_pf_prod_c
- \+ *lemma* tactic.ring_exp.mul_pf_sum
- \+ *lemma* tactic.ring_exp.mul_pf_zero
- \+ *lemma* tactic.ring_exp.mul_pp_pf_overlap
- \+ *lemma* tactic.ring_exp.mul_pp_pf_prod_gt
- \+ *lemma* tactic.ring_exp.mul_pp_pf_prod_lt
- \+ *lemma* tactic.ring_exp.negate_pf
- \+ *lemma* tactic.ring_exp.pow_e_pf_exp
- \+ *lemma* tactic.ring_exp.pow_p_pf_cons
- \+ *lemma* tactic.ring_exp.pow_p_pf_one
- \+ *lemma* tactic.ring_exp.pow_p_pf_singleton
- \+ *lemma* tactic.ring_exp.pow_p_pf_succ
- \+ *lemma* tactic.ring_exp.pow_p_pf_zero
- \+ *lemma* tactic.ring_exp.pow_pf_sum
- \+ *lemma* tactic.ring_exp.pow_pf_zero
- \+ *lemma* tactic.ring_exp.pow_pp_pf_c
- \+ *lemma* tactic.ring_exp.pow_pp_pf_one
- \+ *lemma* tactic.ring_exp.pow_pp_pf_prod
- \+ *lemma* tactic.ring_exp.prod_congr
- \+ *lemma* tactic.ring_exp.prod_to_sum_pf
- \+ *lemma* tactic.ring_exp.simple_pf_exp_one
- \+ *lemma* tactic.ring_exp.simple_pf_prod_neg_one
- \+ *lemma* tactic.ring_exp.simple_pf_prod_one
- \+ *lemma* tactic.ring_exp.simple_pf_sum_zero
- \+ *lemma* tactic.ring_exp.simple_pf_var_one
- \+ *lemma* tactic.ring_exp.sub_pf
- \+ *lemma* tactic.ring_exp.sum_congr

Added test/ring_exp.lean
- \+ *def* pow_sub_pow_factor

Modified test/tactics.lean
- \- *structure* equiv
- \+/\- *def* eta_expansion_test2
- \+ *structure* my_equiv



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
- \+ *lemma* deriv_div
- \+ *lemma* deriv_inv
- \+ *lemma* deriv_pow
- \+ *lemma* deriv_within_div
- \+ *lemma* deriv_within_inv
- \+ *lemma* deriv_within_pow
- \+ *lemma* differentiable.div
- \+ *lemma* differentiable_at.div
- \+ *lemma* differentiable_at_inv
- \+ *lemma* differentiable_at_pow
- \+ *lemma* differentiable_on.div
- \+ *lemma* differentiable_on_inv
- \+ *lemma* differentiable_on_pow
- \+ *lemma* differentiable_pow
- \+ *lemma* differentiable_within_at.div
- \+ *lemma* differentiable_within_at_inv
- \+ *lemma* differentiable_within_at_pow
- \+ *lemma* fderiv_inv
- \+ *lemma* fderiv_within_inv
- \+ *lemma* has_deriv_at.div
- \+ *theorem* has_deriv_at_inv
- \+ *lemma* has_deriv_at_inv_one
- \+ *lemma* has_deriv_at_pow
- \+ *lemma* has_deriv_within_at.div
- \+ *lemma* has_deriv_within_at.nhds_within
- \+ *theorem* has_deriv_within_at_inv
- \+ *theorem* has_deriv_within_at_pow
- \+ *lemma* has_fderiv_at_inv
- \+ *lemma* has_fderiv_within_at_inv

Modified src/analysis/calculus/fderiv.lean
- \- *lemma* continuous_linear_map.differentiable
- \- *lemma* continuous_linear_map.differentiable_at
- \- *lemma* continuous_linear_map.differentiable_on
- \- *lemma* continuous_linear_map.differentiable_within_at
- \- *lemma* continuous_linear_map.fderiv
- \- *lemma* continuous_linear_map.fderiv_within
- \- *lemma* continuous_linear_map.has_fderiv_at
- \- *lemma* continuous_linear_map.has_fderiv_within_at
- \+ *lemma* has_fderiv_within_at.nhds_within
- \+ *lemma* has_fderiv_within_at_of_not_mem_closure
- \+ *lemma* is_bounded_bilinear_map.continuous_left
- \+ *lemma* is_bounded_bilinear_map.continuous_right

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.tendsto.div
- \+ *lemma* filter.tendsto.inv'
- \+ *lemma* normed_field.continuous_on_inv
- \+ *lemma* normed_field.tendsto_inv

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map_smul_right

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.add_comp
- \+ *lemma* continuous_linear_map.comp_add
- \+ *theorem* continuous_linear_map.comp_id
- \+ *lemma* continuous_linear_map.comp_smul
- \+ *theorem* continuous_linear_map.comp_zero
- \+ *theorem* continuous_linear_map.id_comp
- \+ *lemma* continuous_linear_map.smul_comp
- \+ *theorem* continuous_linear_map.zero_comp

Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.mem_nhds_within_iff
- \+ *theorem* metric.tendsto_nhds_within_nhds
- \+ *theorem* metric.tendsto_nhds_within_nhds_within

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
- \+ *theorem* cast_fpow
- \+/\- *def* fpow
- \+/\- *lemma* fpow_add
- \+/\- *lemma* fpow_eq_gpow
- \+ *lemma* fpow_eq_zero
- \+ *lemma* fpow_inj
- \+/\- *lemma* fpow_inv
- \+ *lemma* fpow_le_iff_le
- \+/\- *lemma* fpow_le_of_le
- \+/\- *lemma* fpow_le_one_of_nonpos
- \+ *lemma* fpow_lt_iff_lt
- \+/\- *lemma* fpow_mul
- \+/\- *lemma* fpow_ne_zero_of_ne_zero
- \+/\- *lemma* fpow_neg
- \+ *theorem* fpow_neg_mul_fpow_self
- \+/\- *lemma* fpow_neg_succ_of_nat
- \+/\- *lemma* fpow_nonneg_of_nonneg
- \+/\- *lemma* fpow_of_nat
- \+/\- *lemma* fpow_one
- \+/\- *lemma* fpow_pos_of_pos
- \+ *lemma* fpow_strict_mono
- \+/\- *lemma* fpow_sub
- \+/\- *lemma* fpow_zero
- \+ *lemma* injective_fpow
- \+ *lemma* is_ring_hom.map_fpow'
- \+/\- *lemma* mul_fpow
- \+ *lemma* nat.fpow_ne_zero_of_pos
- \+ *lemma* nat.fpow_pos_of_pos
- \+/\- *lemma* one_fpow
- \+/\- *lemma* one_le_fpow_of_nonneg
- \+/\- *lemma* one_lt_fpow
- \+/\- *lemma* one_lt_pow
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* unit_pow
- \+/\- *lemma* zero_fpow
- \+/\- *lemma* zero_gpow



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
- \+ *lemma* set.bdd_above_finite
- \+ *lemma* set.bdd_above_finite_union
- \+ *lemma* set.bdd_below_finite
- \+ *lemma* set.bdd_below_finite_union

Renamed src/data/set/intervals.lean to src/data/set/intervals/basic.lean
- \- *lemma* set.eq_of_Ico_disjoint
- \- *lemma* set.is_glb_Icc
- \- *lemma* set.is_glb_Ici
- \- *lemma* set.is_glb_Ico
- \- *lemma* set.is_glb_Ioc
- \- *lemma* set.is_glb_Ioi
- \- *lemma* set.is_glb_Ioo
- \- *lemma* set.is_lub_Icc
- \- *lemma* set.is_lub_Ico
- \- *lemma* set.is_lub_Iic
- \- *lemma* set.is_lub_Iio
- \- *lemma* set.is_lub_Ioc
- \- *lemma* set.is_lub_Ioo

Added src/data/set/intervals/default.lean


Added src/data/set/intervals/disjoint.lean
- \+ *lemma* set.Ico_disjoint_Ico
- \+ *lemma* set.eq_of_Ico_disjoint

Modified src/order/bounds.lean
- \+ *lemma* bdd_above.mk
- \+ *def* bdd_above
- \+ *lemma* bdd_above_empty
- \+ *lemma* bdd_above_insert
- \+ *lemma* bdd_above_inter_left
- \+ *lemma* bdd_above_inter_right
- \+ *lemma* bdd_above_of_bdd_above_of_monotone
- \+ *lemma* bdd_above_singleton
- \+ *lemma* bdd_above_subset
- \+ *lemma* bdd_above_top
- \+ *lemma* bdd_above_union
- \+ *lemma* bdd_below.mk
- \+ *def* bdd_below
- \+ *lemma* bdd_below_bot
- \+ *lemma* bdd_below_empty
- \+ *lemma* bdd_below_insert
- \+ *lemma* bdd_below_inter_left
- \+ *lemma* bdd_below_inter_right
- \+ *lemma* bdd_below_of_bdd_below_of_monotone
- \+ *lemma* bdd_below_singleton
- \+ *lemma* bdd_below_subset
- \+ *lemma* bdd_below_union
- \+ *lemma* is_glb_Icc
- \+ *lemma* is_glb_Ici
- \+ *lemma* is_glb_Ico
- \- *lemma* is_glb_Inf
- \+ *lemma* is_glb_Ioc
- \+ *lemma* is_glb_Ioi
- \+ *lemma* is_glb_Ioo
- \- *lemma* is_glb_iff_Inf_eq
- \- *lemma* is_glb_iff_infi_eq
- \- *lemma* is_glb_infi
- \+ *lemma* is_lub_Icc
- \+ *lemma* is_lub_Ico
- \+ *lemma* is_lub_Iic
- \+ *lemma* is_lub_Iio
- \+ *lemma* is_lub_Ioc
- \+ *lemma* is_lub_Ioo
- \- *lemma* is_lub_Sup
- \- *lemma* is_lub_iff_Sup_eq
- \- *lemma* is_lub_iff_supr_eq
- \- *lemma* is_lub_supr

Modified src/order/complete_lattice.lean
- \+ *lemma* lattice.is_glb_Inf
- \+ *lemma* lattice.is_glb_iff_Inf_eq
- \+ *lemma* lattice.is_glb_iff_infi_eq
- \+ *lemma* lattice.is_glb_infi
- \+ *lemma* lattice.is_lub_Sup
- \+ *lemma* lattice.is_lub_iff_Sup_eq
- \+ *lemma* lattice.is_lub_iff_supr_eq
- \+ *lemma* lattice.is_lub_supr

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* bdd_above.mk
- \- *def* bdd_above
- \- *lemma* bdd_above_empty
- \- *lemma* bdd_above_finite
- \- *lemma* bdd_above_finite_union
- \- *lemma* bdd_above_insert
- \- *lemma* bdd_above_inter_left
- \- *lemma* bdd_above_inter_right
- \- *lemma* bdd_above_of_bdd_above_of_monotone
- \- *lemma* bdd_above_singleton
- \- *lemma* bdd_above_subset
- \- *lemma* bdd_above_top
- \- *lemma* bdd_above_union
- \- *lemma* bdd_below.mk
- \- *def* bdd_below
- \- *lemma* bdd_below_bot
- \- *lemma* bdd_below_empty
- \- *lemma* bdd_below_finite
- \- *lemma* bdd_below_finite_union
- \- *lemma* bdd_below_insert
- \- *lemma* bdd_below_inter_left
- \- *lemma* bdd_below_inter_right
- \- *lemma* bdd_below_of_bdd_below_of_monotone
- \- *lemma* bdd_below_singleton
- \- *lemma* bdd_below_subset
- \- *lemma* bdd_below_union

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
- \+ *theorem* set.insert_nonempty
- \+ *theorem* set.nonempty.ne_empty
- \+/\- *theorem* set.singleton_ne_empty
- \+ *theorem* set.singleton_nonempty



## [2019-12-05 17:22:16](https://github.com/leanprover-community/mathlib/commit/2adc122)
feat(data/set/finite): remove exists_finset_of_finite ([#1782](https://github.com/leanprover-community/mathlib/pull/1782))
* feat(data/set/finite): remove exists_finset_of_finite
exists_finset_of_finite is a duplicate of finite.exists_finset_coe
At same time, provide a `can_lift` instance to lift sets to finsets.
* Add docstring
#### Estimated changes
Modified src/data/set/finite.lean
- \- *lemma* set.exists_finset_of_finite



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
- \- *lemma* is_field_hom.injective
- \- *lemma* is_field_hom.map_div'
- \- *lemma* is_field_hom.map_div
- \- *lemma* is_field_hom.map_eq_zero
- \- *lemma* is_field_hom.map_inv'
- \- *lemma* is_field_hom.map_inv
- \- *lemma* is_field_hom.map_ne_zero
- \- *def* is_field_hom
- \+ *lemma* is_ring_hom.injective
- \+ *lemma* is_ring_hom.map_div'
- \+ *lemma* is_ring_hom.map_div
- \+ *lemma* is_ring_hom.map_eq_zero
- \+ *lemma* is_ring_hom.map_inv'
- \+ *lemma* is_ring_hom.map_inv
- \+ *lemma* is_ring_hom.map_ne_zero

Modified src/algebra/field_power.lean
- \- *lemma* is_field_hom.map_fpow
- \+ *lemma* is_ring_hom.map_fpow

Modified src/data/complex/basic.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.leading_coeff_map
- \+/\- *lemma* polynomial.map_div
- \+/\- *lemma* polynomial.map_eq_zero
- \+/\- *lemma* polynomial.map_mod
- \+/\- *lemma* polynomial.nat_degree_map

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* polynomial.splits_comp_of_splits
- \+/\- *lemma* polynomial.splits_map_iff

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
- \+/\- *theorem* set.empty_prod
- \+/\- *theorem* set.ne_empty_iff_exists_mem
- \+ *theorem* set.ne_empty_iff_nonempty
- \+ *theorem* set.nonempty.fst
- \+ *lemma* set.nonempty.inl
- \+ *lemma* set.nonempty.inr
- \+ *lemma* set.nonempty.left
- \+ *lemma* set.nonempty.of_diff
- \+ *lemma* set.nonempty.of_ssubset'
- \+ *lemma* set.nonempty.of_subset
- \+ *theorem* set.nonempty.prod
- \+ *lemma* set.nonempty.right
- \+ *theorem* set.nonempty.snd
- \+ *lemma* set.nonempty_iff_univ_nonempty
- \+ *lemma* set.nonempty_of_mem
- \+ *lemma* set.nonempty_of_ssubset
- \+/\- *theorem* set.prod_empty
- \+ *theorem* set.prod_ne_empty_iff
- \- *theorem* set.prod_neq_empty_iff
- \+ *theorem* set.prod_nonempty_iff
- \+ *lemma* set.union_nonempty
- \+ *lemma* set.univ_nonempty

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
- \+ *lemma* algebra.smul_def''
- \+ *lemma* algebra.smul_def
- \- *theorem* algebra.smul_def
- \+ *lemma* subalgebra.range_le

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
- \+/\- *lemma* set.Ico_subset_Iio_self
- \+ *lemma* set.Iio_subset_Iic
- \+ *lemma* set.Iio_subset_Iic_iff
- \+ *lemma* set.Iio_subset_Iic_self
- \+ *lemma* set.Iio_subset_Iio
- \+ *lemma* set.Iio_subset_Iio_iff
- \+ *lemma* set.Ioc_subset_Icc_self
- \+ *lemma* set.Ioc_subset_Ioi_self
- \+ *lemma* set.Ioi_subset_Ici
- \+ *lemma* set.Ioi_subset_Ici_iff
- \+ *lemma* set.Ioi_subset_Ici_self
- \+ *lemma* set.Ioi_subset_Ioi
- \+ *lemma* set.Ioi_subset_Ioi_iff
- \+ *lemma* set.Ioo_subset_Iio_self
- \+ *lemma* set.Ioo_subset_Ioc_self
- \+ *lemma* set.Ioo_subset_Ioi_self
- \+ *lemma* set.is_glb_Icc
- \+ *lemma* set.is_glb_Ici
- \+ *lemma* set.is_glb_Ico
- \+ *lemma* set.is_glb_Ioc
- \+ *lemma* set.is_glb_Ioi
- \+ *lemma* set.is_glb_Ioo
- \+ *lemma* set.is_lub_Icc
- \+ *lemma* set.is_lub_Ico
- \+ *lemma* set.is_lub_Iic
- \+ *lemma* set.is_lub_Iio
- \+ *lemma* set.is_lub_Ioc
- \+ *lemma* set.is_lub_Ioo

Modified src/topology/algebra/ordered.lean
- \+ *lemma* closure_Ico
- \+ *lemma* closure_Iio'
- \+ *lemma* closure_Iio
- \+ *lemma* closure_Ioc
- \+ *lemma* closure_Ioi'
- \+ *lemma* closure_Ioi
- \+ *lemma* closure_Ioo
- \+ *lemma* is_closed_Ici
- \+ *lemma* is_closed_Iic
- \+ *lemma* mem_nhds_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_iff_exists_Ioo_subset
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset'
- \+ *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset'
- \+ *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ico_subset
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioc_subset
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset'
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous.continuous_within_at
- \+ *lemma* continuous_within_at.tendsto
- \+/\- *theorem* mem_nhds_within
- \+ *lemma* mem_nhds_within_iff_exists_mem_nhds_inter



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
- \+ *lemma* finset.fold_max_le
- \+ *lemma* finset.fold_max_lt
- \+ *lemma* finset.fold_min_le
- \+ *lemma* finset.fold_min_lt
- \+ *lemma* finset.fold_op_rel_iff_and
- \+ *lemma* finset.fold_op_rel_iff_or
- \+ *lemma* finset.le_fold_max
- \+ *lemma* finset.le_fold_min
- \+ *lemma* finset.lt_fold_max
- \+ *lemma* finset.lt_fold_min



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
- \+ *lemma* polynomial.monic.as_sum



## [2019-12-03 16:50:35](https://github.com/leanprover-community/mathlib/commit/922a4eb)
feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty ([#1770](https://github.com/leanprover-community/mathlib/pull/1770))
* feat(set_theory/cardinal): eq_one_iff_subsingleton_and_nonempty
From the perfectoid project
* Update src/set_theory/cardinal.lean
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.eq_one_iff_subsingleton_and_nonempty



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
- \+ *lemma* cauchy_seq_of_controlled
- \+ *lemma* le_nhds_of_cauchy_adhp_aux
- \+ *theorem* sequentially_complete.le_nhds_of_seq_tendsto_nhds
- \+ *def* sequentially_complete.seq
- \+ *theorem* sequentially_complete.seq_is_cauchy_seq
- \+ *lemma* sequentially_complete.seq_mem
- \+ *lemma* sequentially_complete.seq_pair_mem
- \+ *def* sequentially_complete.set_seq
- \+ *def* sequentially_complete.set_seq_aux
- \+ *lemma* sequentially_complete.set_seq_mem
- \+ *lemma* sequentially_complete.set_seq_mono
- \+ *lemma* sequentially_complete.set_seq_prod_subset
- \+ *lemma* sequentially_complete.set_seq_sub_aux
- \+ *theorem* uniform_space.complete_of_cauchy_seq_tendsto
- \+ *theorem* uniform_space.complete_of_convergent_controlled_sequences



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
- \+ *lemma* edist_eq_coe_nnnorm
- \+ *lemma* of_real_norm_eq_coe_nnnorm

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_congr_ae
- \+/\- *lemma* measure_theory.integral_smul
- \+ *lemma* measure_theory.l1.norm_Integral_le_one
- \+ *lemma* measure_theory.l1.norm_integral_le
- \+ *lemma* measure_theory.norm_integral_le_lintegral_norm
- \+ *lemma* measure_theory.of_real_norm_integral_le_lintegral_norm
- \+ *theorem* measure_theory.tendsto_integral_of_dominated_convergence

Modified src/measure_theory/integration.lean
- \- *lemma* measure_theory.dominated_convergence_nn
- \+ *lemma* measure_theory.tendsto_lintegral_of_dominated_convergence

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.all_ae_of_real_F_le_bound
- \+ *lemma* measure_theory.all_ae_of_real_f_le_bound
- \+ *lemma* measure_theory.all_ae_tendsto_of_real_norm
- \+ *lemma* measure_theory.integrable_iff_edist
- \- *lemma* measure_theory.integrable_iff_lintegral_edist
- \+ *lemma* measure_theory.integrable_iff_norm
- \+/\- *lemma* measure_theory.integrable_iff_of_ae_eq
- \+ *lemma* measure_theory.integrable_iff_of_real
- \+ *lemma* measure_theory.integrable_norm_iff
- \+ *lemma* measure_theory.integrable_of_dominated_convergence
- \+ *lemma* measure_theory.integrable_of_integrable_bound
- \+ *lemma* measure_theory.l1.norm_eq_nnnorm_to_fun
- \+ *lemma* measure_theory.l1.norm_eq_norm_to_fun
- \- *lemma* measure_theory.l1.norm_to_fun
- \+ *lemma* measure_theory.tendsto_lintegral_norm_of_dominated_convergence

Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_to_real



## [2019-12-01 16:14:54](https://github.com/leanprover-community/mathlib/commit/8a89b06)
refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative ([#1740](https://github.com/leanprover-community/mathlib/pull/1740))
* refactor(analysis/calculus/mean_value): prove the mean value theorem using 1D derivative
* docstring
* use iff.rfl
* fix build
* fix docstring
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_smul'
- \+ *lemma* deriv_within_smul'
- \+ *lemma* fderiv.comp_deriv
- \+ *lemma* fderiv_within.comp_deriv_within
- \+ *theorem* has_deriv_at.smul'
- \+ *theorem* has_deriv_within_at.smul'
- \+ *theorem* has_fderiv_at.comp_has_deriv_at
- \+ *theorem* has_fderiv_at.comp_has_deriv_within_at
- \+ *theorem* has_fderiv_within_at.comp_has_deriv_within_at

Modified src/analysis/calculus/fderiv.lean
- \- *lemma* differentiable.fderiv_within
- \+ *lemma* differentiable_at.fderiv_within

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
- \+ *lemma* filter.tendsto.mul_mul
- \- *lemma* filter.tendsto_mul_mul

Modified src/topology/algebra/group.lean
- \+ *lemma* continuous.inv
- \+ *lemma* continuous.sub
- \- *lemma* continuous_inv'
- \+/\- *lemma* continuous_inv
- \- *lemma* continuous_sub'
- \+/\- *lemma* continuous_sub
- \+ *lemma* tendsto.inv
- \+ *lemma* tendsto.sub
- \- *lemma* tendsto_inv
- \- *lemma* tendsto_sub

Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous.mul
- \- *lemma* continuous_mul'
- \+/\- *lemma* continuous_mul
- \+ *lemma* tendsto.mul
- \- *lemma* tendsto_mul'
- \+/\- *lemma* tendsto_mul

Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.max
- \+ *lemma* continuous.min
- \- *lemma* continuous_max
- \- *lemma* continuous_min
- \+ *lemma* tendsto.max
- \+ *lemma* tendsto.min
- \- *lemma* tendsto_max
- \- *lemma* tendsto_min

Modified src/topology/algebra/polynomial.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_continuous.add
- \+ *lemma* uniform_continuous.neg
- \+ *lemma* uniform_continuous.sub
- \- *lemma* uniform_continuous_add'
- \+/\- *lemma* uniform_continuous_add
- \- *lemma* uniform_continuous_neg'
- \+/\- *lemma* uniform_continuous_neg
- \- *lemma* uniform_continuous_sub'
- \+/\- *lemma* uniform_continuous_sub

Modified src/topology/algebra/uniform_ring.lean
- \+ *lemma* uniform_space.completion.continuous.mul
- \- *lemma* uniform_space.completion.continuous_mul'
- \+/\- *lemma* uniform_space.completion.continuous_mul

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/complex.lean
- \+ *lemma* complex.continuous.inv
- \- *lemma* complex.continuous_inv'
- \+/\- *lemma* complex.continuous_inv

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.continuous.sub
- \- *lemma* nnreal.continuous_sub'
- \+/\- *lemma* nnreal.continuous_sub
- \+ *lemma* nnreal.tendsto.sub
- \- *lemma* nnreal.tendsto_sub

Modified src/topology/instances/real.lean
- \+ *lemma* real.continuous.inv
- \- *lemma* real.continuous_inv'
- \+/\- *lemma* real.continuous_inv

Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/uniform_space/basic.lean
- \- *lemma* mem_uniformity_of_uniform_continuous_invarant
- \+ *lemma* mem_uniformity_of_uniform_continuous_invariant

Modified test/apply.lean




## [2019-12-01 15:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/a350f03)
chore(scripts/nolint.txt): regenerate
#### Estimated changes
Modified scripts/nolints.txt


