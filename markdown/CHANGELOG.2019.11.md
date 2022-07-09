## [2019-11-30 16:23:56](https://github.com/leanprover-community/mathlib/commit/343c54d)
feat(analysis/complex/exponential): limits of exp ([#1744](https://github.com/leanprover-community/mathlib/pull/1744))
* staging
* exp div pow
* cleanup
* oops
* better proof
* cleanup
* docstring
* typo in docstring
#### Estimated changes
Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* sin_gt_sub_cube
- \+ *lemma* tendsto_exp_at_top
- \+ *lemma* tendsto_exp_neg_at_top_nhds_0
- \+ *lemma* tendsto_exp_div_pow_at_top
- \+ *lemma* tendsto_pow_mul_exp_neg_at_top_nhds_0
- \+/\- *lemma* sin_gt_sub_cube

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_at_top_mul_left
- \+ *lemma* tendsto_at_top_mul_right
- \+ *lemma* tendsto_at_top_mul_left'
- \+ *lemma* tendsto_at_top_mul_right'
- \+ *lemma* tendsto_at_top_div
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1



## [2019-11-29 21:47:26](https://github.com/leanprover-community/mathlib/commit/e68b2be)
doc(docs/contribute, meta/expr): sectioning doc strings  ([#1723](https://github.com/leanprover-community/mathlib/pull/1723))
* doc(docs/contribute, meta/expr): explain sectioning doc strings and show in practice
* updates
#### Estimated changes
Modified docs/contribute/doc.md
- \+ *def* brackets
- \+ *def* map_prefix

Modified src/meta/expr.lean



## [2019-11-29 20:59:58](https://github.com/leanprover-community/mathlib/commit/b46ef84)
doc(windows.md): update [ci skip] ([#1742](https://github.com/leanprover-community/mathlib/pull/1742))
* doc(windows.md): update [ci skip]
* small
* Update docs/install/windows.md
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* wording
#### Estimated changes
Modified docs/install/windows.md



## [2019-11-29 18:51:59](https://github.com/leanprover-community/mathlib/commit/9bb69dc)
feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric` ([#1743](https://github.com/leanprover-community/mathlib/pull/1743))
* feat(analysis/specific_limits): add `cauchy_seq_of_edist_le_geometric`
Other changes:
* Estimates on the convergence rate both in `edist` and `dist` cases.
* Swap lhs with lhs in `ennreal.tsum_coe` and `nnreal.tsum_coe`,
  rename accordingly
* Use `(1 - r)⁻¹` instead of `1 / (1 - r)` in `has_sum_geometric`
* Add some docstrings
* Update src/analysis/specific_limits.lean
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tsum_geometric
- \+ *lemma* has_sum_geometric_nnreal
- \+ *lemma* summable_geometric_nnreal
- \+ *lemma* tsum_geometric_nnreal
- \+ *lemma* cauchy_seq_of_edist_le_geometric
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto₀
- \+ *lemma* aux_has_sum_of_le_geometric
- \+/\- *lemma* cauchy_seq_of_le_geometric
- \+ *lemma* dist_le_of_le_geometric_of_tendsto₀
- \+ *lemma* dist_le_of_le_geometric_of_tendsto
- \+ *lemma* cauchy_seq_of_le_geometric_two
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto₀
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto
- \+/\- *lemma* tsum_geometric
- \+/\- *lemma* cauchy_seq_of_le_geometric

Modified src/data/real/cardinality.lean

Modified src/measure_theory/probability_mass_function.lean

Modified src/topology/instances/ennreal.lean
- \+ *lemma* edist_le_tsum_of_edist_le_of_tendsto
- \+ *lemma* edist_le_tsum_of_edist_le_of_tendsto₀

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* summable_coe
- \+ *lemma* coe_tsum
- \+ *lemma* summable_comp_injective
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* summable_coe
- \- *lemma* tsum_coe



## [2019-11-29 16:54:30](https://github.com/leanprover-community/mathlib/commit/817711d)
feat(measure_theory/bochner_integration): linearity of the Bochner Integral ([#1745](https://github.com/leanprover-community/mathlib/pull/1745))
* Linearity of the Bochner Integral
* prove integral_neg and integral_smul with less assumptions; make integral irreducible
* remove simp tag
* create simp set for integral
* Add simp_attr.integral to nolint
* Make it possible to unfold the definition of `integral`
and other things.
* Update nolints.txt
* Make it possible to unfold l1.integral
* Update bochner_integration.lean
* Update bochner_integration.lean
#### Estimated changes
Modified scripts/nolints.txt

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* extend_zero
- \+/\- *lemma* extend_zero

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* smul_mk
- \+/\- *lemma* smul_mk

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_eq
- \+ *lemma* integral_zero
- \+ *lemma* integral_add
- \+ *lemma* integral_neg
- \+ *lemma* integral_sub
- \+ *lemma* integral_smul
- \+ *lemma* integral_eq
- \+ *lemma* integral_eq_zero_of_non_measurable
- \+ *lemma* integral_eq_zero_of_non_integrable
- \+ *lemma* integral_zero
- \+ *lemma* integral_add
- \+ *lemma* integral_neg
- \+ *lemma* integral_sub
- \+ *lemma* integral_smul
- \+ *def* integral_clm
- \+ *def* integral
- \+ *def* integral

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable_neg_iff
- \+ *lemma* measurable_smul_iff

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_neg_iff
- \+ *lemma* integrable_smul_iff



## [2019-11-29 14:50:53](https://github.com/leanprover-community/mathlib/commit/65bdbab)
chore(topology/instances/ennreal): simplify some statements&proofs ([#1750](https://github.com/leanprover-community/mathlib/pull/1750))
API changes:
* `nhds_top`: use `⨅a ≠ ∞` instead of `⨅a:{a:ennreal // a ≠ ⊤}`
* `nhds_zero`, `nhds_of_ne_top` : similarly to `nhds_top`
* `tendsto_nhds`: get rid of the intermediate set `n`.
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* nhds_top
- \+/\- *lemma* nhds_zero
- \+/\- *lemma* nhds_of_ne_top
- \+/\- *lemma* nhds_top
- \+/\- *lemma* nhds_zero
- \+/\- *lemma* nhds_of_ne_top



## [2019-11-29 13:45:43](https://github.com/leanprover-community/mathlib/commit/8f11c46)
feat(data/real/ennreal): more simp lemmas about `inv` and continuity of `inv` ([#1749](https://github.com/leanprover-community/mathlib/pull/1749))
* Prove some algebraic properties of `ennreal.inv`
* More algebraic lemmas
* Prove continuity of `inv`
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+ *lemma* inv_involutive
- \+ *lemma* inv_bijective
- \+ *lemma* inv_eq_inv
- \+ *lemma* inv_pos
- \+ *lemma* inv_lt_inv
- \+ *lemma* inv_lt_iff_inv_lt
- \+ *lemma* lt_inv_iff_lt_inv
- \+ *lemma* inv_le_inv
- \+ *lemma* inv_le_iff_inv_le
- \+ *lemma* le_inv_iff_le_inv
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one

Modified src/topology/instances/ennreal.lean



## [2019-11-29 11:45:14](https://github.com/leanprover-community/mathlib/commit/1b3347d)
feat(algebra/*,data/real/*): add some inequalities about `canonically_ordered_comm_semiring`s ([#1746](https://github.com/leanprover-community/mathlib/pull/1746))
Use them for `nnreal` and `ennreal`.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* pow_le_pow_of_le_left
- \+ *theorem* pow_pos
- \+ *theorem* one_le_pow_of_one_le
- \+ *theorem* pow_le_one

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_mul
- \+ *lemma* zero_lt_one
- \+ *lemma* mul_pos
- \+/\- *lemma* mul_le_mul

Modified src/data/real/ennreal.lean



## [2019-11-29 07:22:29](https://github.com/leanprover-community/mathlib/commit/8e74c62)
chore(data/finset,order/filter): simplify a few proofs ([#1747](https://github.com/leanprover-community/mathlib/pull/1747))
Also add `finset.image_mono` and `finset.range_mono`.
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* range_mono
- \+ *theorem* image_mono
- \+ *theorem* subset_range_sup_succ
- \+/\- *theorem* exists_nat_subset_range
- \+/\- *theorem* exists_nat_subset_range

Modified src/order/filter/basic.lean



## [2019-11-27 19:49:59](https://github.com/leanprover-community/mathlib/commit/198fb09)
feat(analysis/complex/exponential): derivatives ([#1695](https://github.com/leanprover-community/mathlib/pull/1695))
* feat(analysis/complex/exponential): derivatives
* nhds
* nhds
* remove omega
* remove set_option
* simp attributes, field type
* restrict scalar
* staging
* complete proof
* staging
* cleanup
* staging
* cleanup
* docstring
* docstring
* reviewer's comments
* real derivatives of exp, sin, cos, sinh, cosh
* fix build
* remove priority
* better proofs
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_O_const_mul_left
- \+/\- *theorem* is_O_const_mul_left_iff
- \+/\- *theorem* is_o_const_mul_left
- \+/\- *theorem* is_o_const_mul_left_iff
- \+/\- *theorem* is_O_of_is_O_const_mul_right
- \+/\- *theorem* is_O_const_mul_right_iff
- \+/\- *theorem* is_o_of_is_o_const_mul_right
- \+/\- *theorem* is_o_const_mul_right
- \+/\- *theorem* is_O_mul
- \+/\- *theorem* is_o_mul_left
- \+/\- *theorem* is_o_mul_right
- \+/\- *theorem* is_o_mul
- \+/\- *theorem* is_O_const_smul_left
- \+/\- *theorem* is_O_const_smul_left_iff
- \+/\- *theorem* is_o_const_smul_left
- \+/\- *theorem* is_o_const_smul_left_iff
- \+/\- *theorem* is_O_const_smul_right
- \+/\- *theorem* is_o_const_smul_right
- \+/\- *theorem* is_O_smul
- \+/\- *theorem* is_o_smul
- \+/\- *theorem* tendsto_nhds_zero_of_is_o
- \+/\- *theorem* is_o_iff_tendsto
- \+ *theorem* is_o_pow_pow
- \+ *theorem* is_o_pow_id
- \+/\- *theorem* is_O_const_mul_left
- \+/\- *theorem* is_O_const_mul_left_iff
- \+/\- *theorem* is_o_const_mul_left
- \+/\- *theorem* is_o_const_mul_left_iff
- \+/\- *theorem* is_O_of_is_O_const_mul_right
- \+/\- *theorem* is_O_const_mul_right_iff
- \+/\- *theorem* is_o_of_is_o_const_mul_right
- \+/\- *theorem* is_o_const_mul_right
- \+/\- *theorem* is_O_mul
- \+/\- *theorem* is_o_mul_left
- \+/\- *theorem* is_o_mul_right
- \+/\- *theorem* is_o_mul
- \+/\- *theorem* is_O_const_smul_left
- \+/\- *theorem* is_O_const_smul_left_iff
- \+/\- *theorem* is_o_const_smul_left
- \+/\- *theorem* is_o_const_smul_left_iff
- \+/\- *theorem* is_O_const_smul_right
- \+/\- *theorem* is_o_const_smul_right
- \+/\- *theorem* is_O_smul
- \+/\- *theorem* is_o_smul
- \+/\- *theorem* tendsto_nhds_zero_of_is_o
- \+/\- *theorem* is_o_iff_tendsto

Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_deriv_within_at_inter
- \+/\- *lemma* deriv_within_inter
- \+/\- *lemma* deriv_congr_of_mem_nhds
- \+/\- *lemma* has_deriv_within_at_inter
- \+/\- *lemma* deriv_within_inter
- \+/\- *lemma* deriv_congr_of_mem_nhds
- \+ *theorem* has_deriv_at_iff_is_o_nhds_zero
- \+/\- *theorem* has_deriv_at.has_deriv_at_filter
- \+/\- *theorem* has_deriv_at.has_deriv_at_filter

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_fderiv_at_iff_is_o_nhds_zero

Modified src/analysis/complex/exponential.lean
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* differentiable_exp
- \+ *lemma* deriv_exp
- \+ *lemma* has_deriv_at_sin
- \+ *lemma* differentiable_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_deriv_at_cos
- \+ *lemma* differentiable_cos
- \+ *lemma* deriv_cos
- \+ *lemma* has_deriv_at_sinh
- \+ *lemma* differentiable_sinh
- \+ *lemma* deriv_sinh
- \+ *lemma* has_deriv_at_cosh
- \+ *lemma* differentiable_cosh
- \+ *lemma* deriv_cosh
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* differentiable_exp
- \+ *lemma* deriv_exp
- \+ *lemma* has_deriv_at_sin
- \+ *lemma* differentiable_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_deriv_at_cos
- \+ *lemma* differentiable_cos
- \+ *lemma* deriv_cos
- \+ *lemma* has_deriv_at_sinh
- \+ *lemma* differentiable_sinh
- \+ *lemma* deriv_sinh
- \+ *lemma* has_deriv_at_cosh
- \+ *lemma* differentiable_cosh
- \+ *lemma* deriv_cosh
- \+/\- *lemma* continuous_cosh
- \- *lemma* tendsto_exp_zero_one
- \+/\- *lemma* continuous_cosh

Modified src/analysis/normed_space/real_inner_product.lean

Modified src/data/complex/exponential.lean
- \+ *lemma* abs_exp_sub_one_sub_id_le



## [2019-11-27 17:34:07](https://github.com/leanprover-community/mathlib/commit/01b1576)
feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable` ([#1739](https://github.com/leanprover-community/mathlib/pull/1739))
* feat(topology/algebra/infinite_sum): prove `cauchy_seq_of_edist_le_of_summable`
Other changes:
* Add estimates on the distance to the limit (`dist` version only)
* Simplify some proofs
* Add some supporting lemmas
* Fix a typo in a lemma name in `ennreal`
* Add `move_cast` attrs
* More `*_cast` tags, use `norm_cast`
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_eq_coe
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+ *lemma* coe_mono
- \+/\- *lemma* coe_eq_zero
- \+/\- *lemma* zero_eq_coe
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* one_eq_coe
- \+/\- *lemma* coe_nonneg
- \+/\- *lemma* coe_pos
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_bit0
- \+/\- *lemma* coe_bit1
- \+ *lemma* coe_pow
- \+/\- *lemma* coe_finset_sum
- \+/\- *lemma* coe_finset_prod
- \+ *lemma* one_lt_coe_iff
- \+ *lemma* coe_min
- \+ *lemma* coe_max
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_eq_coe
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_eq_zero
- \+/\- *lemma* zero_eq_coe
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* one_eq_coe
- \+/\- *lemma* coe_nonneg
- \+/\- *lemma* coe_pos
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_bit0
- \+/\- *lemma* coe_bit1
- \+/\- *lemma* coe_finset_sum
- \+/\- *lemma* coe_finset_prod
- \- *lemma* one_lt_zero_iff
- \+/\- *lemma* coe_sub

Modified src/data/real/nnreal.lean
- \+ *lemma* coe_pow
- \+/\- *lemma* sum_coe
- \+/\- *lemma* prod_coe
- \+/\- *lemma* smul_coe
- \+ *lemma* sub_def
- \+ *lemma* sub_pos
- \+ *lemma* mul_le_iff_le_inv
- \+ *lemma* le_div_iff_mul_le
- \+/\- *lemma* sum_coe
- \+/\- *lemma* prod_coe
- \+/\- *lemma* smul_coe
- \- *lemma* mul_le_if_le_inv

Modified src/order/filter/basic.lean
- \+ *lemma* tendsto_finset_range

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* cauchy_seq_of_edist_le_of_summable
- \+ *lemma* cauchy_seq_of_dist_le_of_summable
- \+ *lemma* dist_le_tsum_of_dist_le_of_tendsto
- \+ *lemma* dist_le_tsum_of_dist_le_of_tendsto₀
- \+ *lemma* dist_le_tsum_dist_of_tendsto
- \+ *lemma* dist_le_tsum_dist_of_tendsto₀

Modified src/topology/metric_space/basic.lean
- \+ *lemma* nnreal.dist_eq
- \+ *lemma* nnreal.nndist_eq

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* cauchy_seq_iff_nnreal

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq_of_tendsto_nhds



## [2019-11-26 14:35:37](https://github.com/leanprover-community/mathlib/commit/255bebc)
feat(data/nat/multiplicity): multiplicity_choose and others ([#1704](https://github.com/leanprover-community/mathlib/pull/1704))
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* le_mod_add_mod_of_dvd_add_of_not_dvd

Created src/data/nat/multiplicity.lean
- \+ *lemma* multiplicity_eq_card_pow_dvd
- \+ *lemma* multiplicity_one
- \+ *lemma* multiplicity_mul
- \+ *lemma* multiplicity_pow
- \+ *lemma* multiplicity_self
- \+ *lemma* multiplicity_pow_self
- \+ *lemma* multiplicity_fact
- \+ *lemma* pow_dvd_fact_iff
- \+ *lemma* multiplicity_choose_aux
- \+ *lemma* multiplicity_choose
- \+ *lemma* multiplicity_le_multiplicity_choose_add
- \+ *lemma* multiplicity_choose_prime_pow



## [2019-11-26 12:10:33](https://github.com/leanprover-community/mathlib/commit/3443a7d)
feat(analysis/complex/basic): restriction of scalars, real differentiability of complex functions ([#1716](https://github.com/leanprover-community/mathlib/pull/1716))
* restrict scalar
* staging
* complete proof
* staging
* cleanup
* staging
* cleanup
* docstring
* docstring
* reviewer's comments
* Update src/analysis/complex/basic.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/analysis/calculus/fderiv.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* add ! in docstrings [ci skip]
* more doc formatting in fderiv
* fix comments
* add docstrings
#### Estimated changes
Modified src/algebra/module.lean

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at_iff_has_fderiv_within_at
- \+ *lemma* has_deriv_at_iff_has_fderiv_at
- \+/\- *lemma* deriv_within_fderiv_within
- \+/\- *lemma* deriv_fderiv
- \+/\- *lemma* deriv_within_fderiv_within
- \+/\- *lemma* deriv_fderiv

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* continuous_linear_map.has_fderiv_at_filter
- \+ *lemma* continuous_linear_map.has_fderiv_within_at
- \+ *lemma* continuous_linear_map.has_fderiv_at
- \+ *lemma* continuous_linear_map.differentiable_at
- \+ *lemma* continuous_linear_map.differentiable_within_at
- \+ *lemma* continuous_linear_map.fderiv
- \+ *lemma* continuous_linear_map.fderiv_within
- \+ *lemma* continuous_linear_map.differentiable
- \+ *lemma* continuous_linear_map.differentiable_on
- \+ *lemma* has_fderiv_at.restrict_scalars
- \+ *lemma* has_fderiv_within_at.restrict_scalars
- \+ *lemma* differentiable_at.restrict_scalars
- \+ *lemma* differentiable_within_at.restrict_scalars
- \+ *lemma* differentiable_on.restrict_scalars
- \+ *lemma* differentiable.restrict_scalars

Modified src/analysis/calculus/mean_value.lean

Created src/analysis/complex/basic.lean
- \+ *lemma* norm_eq_abs
- \+ *lemma* norm_real
- \+ *lemma* norm_rat
- \+ *lemma* norm_nat
- \+ *lemma* norm_int
- \+ *lemma* norm_int_of_nonneg
- \+ *lemma* linear_map.re_apply
- \+ *lemma* continuous_linear_map.re_coe
- \+ *lemma* continuous_linear_map.re_apply
- \+ *lemma* continuous_linear_map.re_norm
- \+ *lemma* linear_map.im_apply
- \+ *lemma* continuous_linear_map.im_coe
- \+ *lemma* continuous_linear_map.im_apply
- \+ *lemma* continuous_linear_map.im_norm
- \+ *lemma* linear_map.of_real_apply
- \+ *lemma* continuous_linear_map.of_real_coe
- \+ *lemma* continuous_linear_map.of_real_apply
- \+ *lemma* continuous_linear_map.of_real_norm
- \+ *lemma* continuous_linear_map.of_real_isometry
- \+ *theorem* has_deriv_at_real_of_complex
- \+ *def* linear_map.re
- \+ *def* continuous_linear_map.re
- \+ *def* linear_map.im
- \+ *def* continuous_linear_map.im
- \+ *def* linear_map.of_real
- \+ *def* continuous_linear_map.of_real

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_algebra_map_eq
- \- *lemma* norm_real
- \- *lemma* norm_rat
- \- *lemma* norm_nat
- \- *lemma* norm_int
- \- *lemma* norm_int_of_nonneg
- \+ *def* normed_space.restrict_scalars

Modified src/analysis/normed_space/finite_dimension.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* isometry_iff_norm_image_eq_norm
- \+ *lemma* restrict_scalars_coe_eq_coe
- \+ *lemma* restrict_scalars_coe_eq_coe'
- \+ *def* restrict_scalars

Modified src/ring_theory/algebra.lean
- \+ *lemma* linear_map.coe_restrict_scalars_eq_coe
- \+ *def* module.restrict_scalars
- \+ *def* linear_map.restrict_scalars

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* algebra_map_isometry



## [2019-11-26 09:03:27](https://github.com/leanprover-community/mathlib/commit/33df7e8)
feat(order/conditionally_complete_lattice): with_top (with_bot L) ins… ([#1725](https://github.com/leanprover-community/mathlib/pull/1725))
* feat(order/conditionally_complete_lattice): with_top (with_bot L) instances
* dealing with most of Sebastien's comments
* initial defs. Now what happens?
* half way there
* compiles!
* tidy
* removing dead code
* docstring tinkering
* removing unused code
* is_lub_Sup' added
* refactor final proofs
* conforming to mathlib conventions
* def -> lemma
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* is_lub_Sup'
- \+/\- *lemma* is_lub_Sup
- \+ *lemma* is_glb_Inf'
- \+/\- *lemma* is_glb_Inf
- \- *lemma* has_lub
- \- *lemma* has_glb
- \+/\- *lemma* is_lub_Sup
- \+/\- *lemma* is_glb_Inf
- \+ *theorem* with_bot.cSup_empty



## [2019-11-25 19:40:41](https://github.com/leanprover-community/mathlib/commit/ef47de4)
chore(data/nat/basic): add some docs, drop unused arguments ([#1741](https://github.com/leanprover-community/mathlib/pull/1741))
* add a docstring
* chore(data/nat/basic): add some docs, drop unused arguments
#### Estimated changes
Modified src/data/nat/basic.lean
- \+/\- *lemma* pow_left_injective
- \+/\- *lemma* pow_left_injective



## [2019-11-25 17:00:45](https://github.com/leanprover-community/mathlib/commit/73735ad)
feat(topology/metric_space/basic): define `cauchy_seq_of_le_tendsto_0` ([#1738](https://github.com/leanprover-community/mathlib/pull/1738))
* Define `cauchy_seq_of_le_tendsto_0`
Sometimes it is convenient to avoid proving `0 ≤ b n`.
* Fix the comment, generalize to an inhabitted `sup`-semilattice.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* cauchy_seq_of_le_tendsto_0



## [2019-11-25 09:29:09](https://github.com/leanprover-community/mathlib/commit/242159f)
feat(measure_theory/bochner_integration): bochner integral of simple functions ([#1676](https://github.com/leanprover-community/mathlib/pull/1676))
* Bochner integral of simple functions
* Update bochner_integration.lean
* Change notation for simple functions in L1 space; Fill in blanks in `calc` proofs
* Better definitions of operations on integrable simple functions
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/measure_theory/bochner_integration.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Several fixes - listed below
* K -> \bbk
* remove indentation after `calc`
* use local instances
* one tactic per line
* add `elim_cast` attributes
* remove definitions from nolints.txt
* use `linear_map.with_bound` to get continuity
* Update documentation and comments
* Fix things
* norm_triangle_sum -> norm_sum_le
* fix documentations and comments (The Bochner integral)
* Fix typos and grammatical errors
* Update src/measure_theory/ae_eq_fun.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Modified scripts/nolints.txt

Modified src/linear_algebra/basic.lean
- \+ *lemma* smul_sum'

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* smul_mk
- \+/\- *lemma* smul_to_fun
- \+/\- *lemma* edist_smul
- \+/\- *lemma* smul_mk
- \+/\- *lemma* smul_to_fun
- \+/\- *lemma* edist_smul

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integrable_iff_integral_lt_top
- \+ *lemma* fin_vol_supp_of_integrable
- \+ *lemma* integrable_of_fin_vol_supp
- \+ *lemma* integrable_iff_fin_vol_supp
- \+ *lemma* integrable_pair
- \+ *lemma* map_bintegral
- \+ *lemma* bintegral_eq_integral
- \+ *lemma* bintegral_eq_lintegral
- \+ *lemma* bintegral_congr
- \+ *lemma* bintegral_eq_integral'
- \+ *lemma* bintegral_eq_lintegral'
- \+ *lemma* bintegral_add
- \+ *lemma* bintegral_smul
- \+ *lemma* norm_bintegral_le_bintegral_norm
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* edist_eq
- \+ *lemma* dist_eq
- \+ *lemma* norm_eq
- \+ *lemma* norm_eq'
- \+ *lemma* coe_smul
- \+ *lemma* of_simple_func_eq_of_fun
- \+ *lemma* of_simple_func_eq_mk
- \+ *lemma* of_simple_func_zero
- \+ *lemma* of_simple_func_add
- \+ *lemma* of_simple_func_neg
- \+ *lemma* of_simple_func_sub
- \+ *lemma* of_simple_func_smul
- \+ *lemma* norm_of_simple_func
- \+ *lemma* of_simple_func_to_simple_func
- \+ *lemma* to_simple_func_of_simple_func
- \+ *lemma* to_simple_func_eq_to_fun
- \+ *lemma* zero_to_simple_func
- \+ *lemma* add_to_simple_func
- \+ *lemma* neg_to_simple_func
- \+ *lemma* sub_to_simple_func
- \+ *lemma* smul_to_simple_func
- \+ *lemma* lintegral_edist_to_simple_func_lt_top
- \+ *lemma* dist_to_simple_func
- \+ *lemma* norm_to_simple_func
- \+ *lemma* norm_eq_bintegral
- \+/\- *lemma* exists_simple_func_near
- \+ *lemma* integral_eq_lintegral
- \+ *lemma* integral_congr
- \+ *lemma* integral_add
- \+ *lemma* integral_smul
- \+ *lemma* norm_integral_le_norm
- \+ *lemma* norm_Integral_le_one
- \+/\- *lemma* exists_simple_func_near
- \- *lemma* uniform_continuous_of_simple_func
- \- *lemma* uniform_embedding_of_simple_func
- \- *lemma* dense_embedding_of_simple_func
- \+ *def* bintegral
- \+ *def* of_simple_func
- \+/\- *def* to_simple_func
- \+ *def* coe_to_l1
- \+/\- *def* integral
- \+ *def* integral_clm
- \- *def* mk
- \+/\- *def* to_simple_func
- \+/\- *def* integral
- \+/\- *def* integral
- \+/\- *def* integral

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* integrable_smul
- \+/\- *lemma* integrable_smul
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* edist_eq
- \+ *lemma* dist_eq
- \+ *lemma* norm_eq
- \+ *lemma* coe_smul
- \+ *lemma* of_fun_eq_mk
- \+ *lemma* of_fun_eq_of_fun
- \+ *lemma* of_fun_zero
- \+ *lemma* of_fun_add
- \+ *lemma* of_fun_neg
- \+ *lemma* norm_of_fun
- \+ *lemma* of_fun_smul
- \+ *lemma* of_fun_to_fun
- \+ *lemma* mk_to_fun
- \+ *lemma* to_fun_of_fun
- \+/\- *lemma* neg_to_fun
- \+/\- *lemma* smul_to_fun
- \+/\- *lemma* integrable_smul
- \+/\- *lemma* integrable_smul
- \- *lemma* mk_eq_mk
- \- *lemma* ext_iff
- \- *lemma* all_ae_mk_to_fun
- \- *lemma* self_eq_mk
- \- *lemma* zero_def
- \- *lemma* mk_zero
- \- *lemma* add_def
- \- *lemma* mk_add
- \- *lemma* neg_mk
- \+/\- *lemma* neg_to_fun
- \- *lemma* dist_def
- \- *lemma* norm_def
- \- *lemma* norm_mk
- \- *lemma* smul_def
- \- *lemma* smul_mk
- \+/\- *lemma* smul_to_fun
- \+ *def* of_fun
- \- *def* mk



## [2019-11-25 00:45:56](https://github.com/leanprover-community/mathlib/commit/6af35ec)
feat(topology/algebra/infinite_sum): add `has_sum` versions of a few `tsum` lemmas ([#1737](https://github.com/leanprover-community/mathlib/pull/1737))
Also add a few lemmas in `analysis/specific_limits`
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* summable_geometric_two'
- \+ *lemma* tsum_geometric_two'
- \- *lemma* tendsto_one_div_at_top_nhds_0_nat

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_fintype
- \+ *lemma* has_sum_single
- \+ *lemma* sum_le_has_sum
- \+ *lemma* sum_le_tsum



## [2019-11-24 23:51:18](https://github.com/leanprover-community/mathlib/commit/bf509d7)
feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top` ([#1713](https://github.com/leanprover-community/mathlib/pull/1713))
* feat(order/filter/basic): add more lemmas about `tendsto _ _ at_top`
* Use explicit arguments as suggested by @sgouezel
* Add lemmas for an `ordered_comm_group`
* Add a missing lemma
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* tendsto_at_top_mono'
- \+ *lemma* tendsto_at_top_mono
- \+ *lemma* tendsto_at_top_add_nonneg_left'
- \+ *lemma* tendsto_at_top_add_nonneg_left
- \+ *lemma* tendsto_at_top_add_nonneg_right'
- \+ *lemma* tendsto_at_top_add_nonneg_right
- \+ *lemma* tendsto_at_top_of_add_const_left
- \+ *lemma* tendsto_at_top_of_add_const_right
- \+ *lemma* tendsto_at_top_of_add_bdd_above_left'
- \+ *lemma* tendsto_at_top_of_add_bdd_above_left
- \+ *lemma* tendsto_at_top_of_add_bdd_above_right'
- \+ *lemma* tendsto_at_top_of_add_bdd_above_right
- \+ *lemma* tendsto_at_top_add_left_of_le'
- \+ *lemma* tendsto_at_top_add_left_of_le
- \+ *lemma* tendsto_at_top_add_right_of_le'
- \+ *lemma* tendsto_at_top_add_right_of_le
- \+ *lemma* tendsto_at_top_add_const_left
- \+ *lemma* tendsto_at_top_add_const_right
- \+ *lemma* tendsto_at_top_at_top_of_monotone



## [2019-11-24 23:02:27](https://github.com/leanprover-community/mathlib/commit/a03a072)
chore(topology/metric_space/emetric_space): define `edist_le_zero` ([#1735](https://github.com/leanprover-community/mathlib/pull/1735))
This makes a few proofs slightly more readable.
#### Estimated changes
Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* edist_le_zero



## [2019-11-24 20:38:04](https://github.com/leanprover-community/mathlib/commit/13fedc1)
feat(algebra/group): define `mul/add_left/right_injective` ([#1730](https://github.com/leanprover-community/mathlib/pull/1730))
Same as `mul_left_cancel` etc but uses `function.injective`.
This makes it easier to use functions from `function.injective` namespace.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *theorem* mul_left_injective
- \+ *theorem* mul_right_injective



## [2019-11-24 19:51:44](https://github.com/leanprover-community/mathlib/commit/7b1cdd4)
feat(topology/metric_space/emetric_space): polygonal inequalities ([#1736](https://github.com/leanprover-community/mathlib/pull/1736))
Migrate [#1572](https://github.com/leanprover-community/mathlib/pull/1572) from `dist` to `edist`
#### Estimated changes
Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_le_Ico_sum_edist
- \+ *lemma* edist_le_range_sum_edist
- \+ *lemma* edist_le_Ico_sum_of_edist_le
- \+ *lemma* edist_le_range_sum_of_edist_le



## [2019-11-24 17:44:38](https://github.com/leanprover-community/mathlib/commit/ca53b5d)
feat(data/real/ennreal): 3 simple lemmas ([#1734](https://github.com/leanprover-community/mathlib/pull/1734))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* coe_to_real
- \+ *lemma* to_nnreal_pos_iff
- \+ *lemma* to_real_pos_iff



## [2019-11-24 10:11:36](https://github.com/leanprover-community/mathlib/commit/2d54a70)
feat(analysis/normed_space): prove more lemmas, rename some old lemmas ([#1733](https://github.com/leanprover-community/mathlib/pull/1733))
Renamed lemmas:
* `norm_triangle` → `norm_add_le`
* `norm_triangle_sub` → `norm_sub_le`
* `norm_triangle_sum` → `norm_sum_le`
* `norm_reverse_triangle'` → `norm_sub_norm_le`
* `norm_reverse_triangle`: deleted; was a duplicate of `abs_norm_sub_norm_le`
* `nnorm_triangle` → `nnorm_add_le`
New lemmas:
* `dist_add_left`, `dist_add_right`, `dist_neg_neg`, dist_sub_left`,
  dist_sub_right`, `dist_smul`, `dist_add_add_le`, `dist_sub_sub_le`:
  operate with distances without rewriting them as norms.
* `norm_add_le_of_le`, `dist_add_add_le_of_le`,
  `dist_sub_sub_le_of_le`, `norm_sum_le_of_le` : chain a triangle-like
  inequality with an appropriate estimates on the right hand side.
Also simplify a few proofs and fix a typo in a comment.
#### Estimated changes
Modified archive/sensitivity.lean

Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/convex.lean

Modified src/analysis/normed_space/banach.lean

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_sub_rev
- \+/\- *lemma* norm_neg
- \+ *lemma* dist_add_left
- \+ *lemma* dist_add_right
- \+ *lemma* dist_neg_neg
- \+ *lemma* dist_sub_left
- \+ *lemma* dist_sub_right
- \+ *lemma* norm_add_le
- \+ *lemma* norm_add_le_of_le
- \+ *lemma* dist_add_add_le
- \+ *lemma* dist_add_add_le_of_le
- \+ *lemma* dist_sub_sub_le
- \+ *lemma* dist_sub_sub_le_of_le
- \+/\- *lemma* norm_zero
- \+ *lemma* norm_sum_le
- \+ *lemma* norm_sum_le_of_le
- \+ *lemma* norm_sub_le
- \+ *lemma* norm_sub_le_of_le
- \+ *lemma* dist_le_norm_add_norm
- \+ *lemma* norm_sub_norm_le
- \+ *lemma* nnnorm_add_le
- \+ *lemma* dist_smul
- \- *lemma* norm_triangle
- \+/\- *lemma* norm_zero
- \- *lemma* norm_triangle_sum
- \+/\- *lemma* norm_neg
- \- *lemma* norm_reverse_triangle'
- \- *lemma* norm_reverse_triangle
- \- *lemma* norm_triangle_sub
- \+/\- *lemma* norm_sub_rev
- \- *lemma* nnnorm_triangle

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* op_norm_add_le
- \- *theorem* op_norm_triangle

Modified src/data/padics/padic_integers.lean

Modified src/data/padics/padic_numbers.lean

Modified src/measure_theory/l1_space.lean

Modified src/topology/bounded_continuous_function.lean
- \+ *lemma* dist_le_two_norm

Modified src/topology/metric_space/cau_seq_filter.lean



## [2019-11-23 11:38:03](https://github.com/leanprover-community/mathlib/commit/f95c01e)
feat(algebra/ordered_*): add three simple lemmas ([#1731](https://github.com/leanprover-community/mathlib/pull/1731))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_div_of_le_of_nonneg

Modified src/algebra/ordered_ring.lean
- \+ *lemma* zero_lt_two
- \+ *lemma* abs_two



## [2019-11-23 00:15:59](https://github.com/leanprover-community/mathlib/commit/f86abc7)
fix(*): lower instance priority ([#1724](https://github.com/leanprover-community/mathlib/pull/1724))
* fix(*): lower instance priority
use lower instance priority for instances that always apply
also do this for automatically generated instances using the `extend` keyword
also add a comment to most places where we short-circuit type-class inference. This can lead to greatly increased search times (see issue [#1561](https://github.com/leanprover-community/mathlib/pull/1561)), so we might want to delete some/all of them.
* put default_priority option inside section
Default priority also applies to all instances, not just automatically-generates ones
the scope of set_option is limited to a section
* two more low priorities
* fix some broken proofs
* fix proof
* more fixes
* more fixes
* increase max_depth a bit
* update notes
* fix linter issues
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean

Modified src/algebra/category/Group.lean

Modified src/algebra/category/Mon/basic.lean

Modified src/algebra/char_zero.lean

Modified src/algebra/euclidean_domain.lean

Modified src/algebra/field.lean

Modified src/algebra/gcd_domain.lean

Modified src/algebra/group/hom.lean

Modified src/algebra/lie_algebra.lean

Modified src/algebra/module.lean

Modified src/algebra/order_functions.lean

Modified src/algebra/ordered_field.lean

Modified src/algebra/ordered_group.lean

Modified src/algebra/ordered_ring.lean

Modified src/algebra/ring.lean

Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/normed_space/basic.lean

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/real_inner_product.lean

Modified src/category/basic.lean

Modified src/category/bitraversable/basic.lean

Modified src/category/monad/cont.lean

Modified src/category/monad/writer.lean

Modified src/category/traversable/basic.lean

Modified src/category_theory/adjunction/limits.lean

Modified src/category_theory/category/default.lean

Modified src/category_theory/concrete_category/basic.lean

Modified src/category_theory/equivalence.lean

Modified src/category_theory/groupoid.lean

Modified src/category_theory/isomorphism.lean

Modified src/category_theory/limits/lattice.lean

Modified src/category_theory/limits/limits.lean

Modified src/category_theory/limits/preserves.lean

Modified src/category_theory/limits/shapes/binary_products.lean

Modified src/category_theory/limits/shapes/finite_limits.lean

Modified src/category_theory/limits/shapes/finite_products.lean

Modified src/category_theory/limits/shapes/terminal.lean

Modified src/category_theory/monad/adjunction.lean

Modified src/computability/primrec.lean

Modified src/data/analysis/topology.lean
- \+ *def* to_topsp

Modified src/data/equiv/denumerable.lean

Modified src/data/fintype.lean
- \+/\- *theorem* fintype.card_subtype_lt
- \+/\- *theorem* fintype.card_subtype_lt

Modified src/data/int/basic.lean
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

Modified src/data/string/basic.lean

Modified src/field_theory/subfield.lean

Modified src/geometry/manifold/real_instances.lean

Modified src/group_theory/group_action.lean

Modified src/group_theory/subgroup.lean

Modified src/logic/relator.lean

Modified src/logic/unique.lean

Modified src/measure_theory/measure_space.lean

Modified src/order/basic.lean

Modified src/order/boolean_algebra.lean

Modified src/order/bounded_lattice.lean

Modified src/order/complete_boolean_algebra.lean

Modified src/order/complete_lattice.lean

Modified src/order/conditionally_complete_lattice.lean

Modified src/order/lattice.lean

Modified src/ring_theory/adjoin_root.lean

Modified src/ring_theory/algebra.lean

Modified src/ring_theory/ideals.lean

Modified src/ring_theory/maps.lean

Modified src/ring_theory/noetherian.lean

Modified src/ring_theory/principal_ideal_domain.lean

Modified src/ring_theory/subring.lean

Modified src/set_theory/cardinal.lean

Modified src/tactic/linarith.lean

Modified src/tactic/lint.lean

Modified src/tactic/ring.lean

Modified src/topology/algebra/group.lean

Modified src/topology/algebra/module.lean

Modified src/topology/algebra/ordered.lean
- \+ *lemma* orderable_topology.t2_space

Modified src/topology/algebra/ring.lean

Modified src/topology/algebra/uniform_ring.lean

Modified src/topology/bases.lean

Modified src/topology/instances/complex.lean

Modified src/topology/instances/ennreal.lean

Modified src/topology/instances/nnreal.lean

Modified src/topology/instances/real.lean

Modified src/topology/metric_space/basic.lean

Modified src/topology/metric_space/cau_seq_filter.lean

Modified src/topology/metric_space/emetric_space.lean

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/premetric_space.lean

Modified src/topology/separation.lean

Modified src/topology/sequences.lean

Modified src/topology/subset_properties.lean

Modified src/topology/uniform_space/basic.lean

Modified src/topology/uniform_space/cauchy.lean

Modified src/topology/uniform_space/pi.lean
- \- *lemma* Pi.uniform_space_topology

Modified src/topology/uniform_space/separation.lean



## [2019-11-22 21:37:11](https://github.com/leanprover-community/mathlib/commit/2b3eaa8)
feat(README) Point users to the tutorial project ([#1728](https://github.com/leanprover-community/mathlib/pull/1728))
I think the tutorial project is a good place to start, and if other people don't think it is then I think they might want to consider adding more files to the tutorial project. I think mathlib is intimidating for beginners and this is a much better idea. However the link to the tutorial project is not even available on the main page -- you have to click through an installation procedure and find it at the bottom, and even then the first thing is suggests is that you make a new project, which I think is harder than getting the tutorial project up and running. This PR proposes that we point people directly to the tutorial project -- they will probably notice the existence of the tutorial project before they have even installed Lean/mathlib and will hence have it at the back of their mind once they've got things up and running.
#### Estimated changes
Modified README.md



## [2019-11-22 21:18:35](https://github.com/leanprover-community/mathlib/commit/013e914)
fix(docs/install/project) compiling is quick ([#1727](https://github.com/leanprover-community/mathlib/pull/1727))
I think the "it takes a long time" comment must either have been from before `update-mathlib` or from when we were pointing people to the perfectoid project.
#### Estimated changes
Modified docs/install/project.md



## [2019-11-22 20:20:52](https://github.com/leanprover-community/mathlib/commit/62c1bc5)
doc(topology/metric_space,measure_theory): move text in copyright docs to module docs ([#1726](https://github.com/leanprover-community/mathlib/pull/1726))
#### Estimated changes
Modified src/measure_theory/measure_space.lean

Modified src/topology/metric_space/baire.lean

Modified src/topology/metric_space/closeds.lean

Modified src/topology/metric_space/completion.lean

Modified src/topology/metric_space/emetric_space.lean

Modified src/topology/metric_space/isometry.lean

Modified src/topology/metric_space/premetric_space.lean



## [2019-11-22 17:45:25+01:00](https://github.com/leanprover-community/mathlib/commit/5a1a469)
docs(README): revert 96ebf8cc
Revert "docs(README): Remove Patrick from the maintainer list."
This reverts commit 96ebf8cc7c446e977637a13740645a7f8e0c8992.
#### Estimated changes
Modified README.md



## [2019-11-21 22:11:03](https://github.com/leanprover-community/mathlib/commit/004618a)
feat(data/nat): two lemmas about choose ([#1717](https://github.com/leanprover-community/mathlib/pull/1717))
* Two lemmas about choose
* swap choose_symm order
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* choose_symm
- \+ *lemma* choose_succ_right_eq



## [2019-11-21 19:22:23](https://github.com/leanprover-community/mathlib/commit/58fc830)
fix(tactic/ext): handle case where goal is solved early ([#1721](https://github.com/leanprover-community/mathlib/pull/1721))
* fix(tactic/ext): handle case where goal is solved early
* add test
#### Estimated changes
Modified src/tactic/ext.lean

Modified test/ext.lean



## [2019-11-21 17:17:19](https://github.com/leanprover-community/mathlib/commit/a13027a)
feat(data/finset): add cardinality of map ([#1722](https://github.com/leanprover-community/mathlib/pull/1722))
* Add cardinality of map
* Update src/data/finset.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* card_map



## [2019-11-21 11:57:54](https://github.com/leanprover-community/mathlib/commit/faf3289)
add div_le_div_iff ([#1720](https://github.com/leanprover-community/mathlib/pull/1720))
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_div_iff



## [2019-11-21 07:04:43](https://github.com/leanprover-community/mathlib/commit/af9dcb9)
make  set_of_eq_eq_singleton a simp lemma ([#1719](https://github.com/leanprover-community/mathlib/pull/1719))
#### Estimated changes
Modified src/data/set/basic.lean



## [2019-11-20 20:03:27](https://github.com/leanprover-community/mathlib/commit/9d031be)
feat(group_theory/congruence): quotients of monoids by congruence relations ([#1710](https://github.com/leanprover-community/mathlib/pull/1710))
* add congruence.lean
* add has_mul
* add definition of congruence relation
* minor changes
* Tidy up second half of congruence.lean
* tidying docstrings
* tidying
* constructive 3rd isom in setoid used in congruence
* remove import
* open namespaces earlier
* responding to PR comments
#### Estimated changes
Modified src/data/setoid.lean
- \+ *lemma* comap_eq
- \+/\- *def* map
- \+/\- *def* comap
- \+ *def* quotient_quotient_equiv_quotient
- \+/\- *def* map
- \+/\- *def* comap

Modified src/group_theory/congruence.lean
- \+ *lemma* map_of_surjective_eq_map_gen
- \+ *lemma* coe_one
- \+ *lemma* mem_coe
- \+ *lemma* le_iff
- \+ *lemma* ker_rel
- \+ *lemma* mk'_ker
- \+ *lemma* mk'_surjective
- \+ *lemma* comp_mk'_apply
- \+ *lemma* ker_apply_eq_preimage
- \+ *lemma* comap_eq
- \+ *lemma* lift_mk'
- \+ *lemma* lift_coe
- \+ *lemma* lift_apply_mk'
- \+ *lemma* lift_funext
- \+ *lemma* lift_surjective_of_surjective
- \+ *lemma* ker_eq_lift_of_injective
- \+ *lemma* ker_lift_mk
- \+ *lemma* ker_lift_range_eq
- \+ *lemma* injective_ker_lift
- \+ *lemma* map_apply
- \+ *theorem* to_submonoid_inj
- \+ *theorem* lift_comp_mk'
- \+ *theorem* lift_unique
- \+ *theorem* lift_range
- \+ *def* map_gen
- \+ *def* map_of_surjective
- \+ *def* comap
- \+ *def* of_submonoid
- \+ *def* ker
- \+ *def* mk'
- \+ *def* lift
- \+ *def* ker_lift
- \+ *def* map
- \+ *def* quotient_quotient_equiv_quotient

Modified src/group_theory/submonoid.lean
- \+ *def* submonoid_congr



## [2019-11-20 17:12:35](https://github.com/leanprover-community/mathlib/commit/f34bb6b)
refactor(topology/metric_space/lipschitz): review API of `lipschitz_with` ([#1700](https://github.com/leanprover-community/mathlib/pull/1700))
* refactor(topology/metric_space/lipschitz): review API of `lipschitz_with`
* Take `K : ℝ≥0` instead of using a conjuction;
* Rename each `*_of_lipschitz` to `lipschitz_with.*`;
* Define convenience constructors (e.g., `of_le_add`);
* Move facts about contracting maps to a separate file&namespace;
* Adjust other files to API changes.
* Make the first argument of `lipschitz_with.weaken` implicit
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix compile
* Fix 'unused args' bug reported by `#lint`
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.lipschitz_of_bound
- \+ *lemma* linear_map.uniform_continuous_of_bound
- \+/\- *theorem* lipschitz
- \+/\- *theorem* lipschitz

Modified src/topology/bounded_continuous_function.lean
- \+ *lemma* lipschitz_comp
- \+ *lemma* uniform_continuous_comp
- \+/\- *lemma* continuous_comp
- \+/\- *lemma* continuous_comp
- \+/\- *def* comp
- \+/\- *def* comp

Modified src/topology/metric_space/closeds.lean
- \+ *lemma* lipschitz_inf_dist_set
- \+ *lemma* lipschitz_inf_dist

Created src/topology/metric_space/contracting.lean
- \+ *lemma* fixed_point_of_tendsto_iterate
- \+ *lemma* to_lipschitz_with
- \+ *lemma* one_sub_K_pos
- \+ *lemma* dist_inequality
- \+ *lemma* dist_le_of_fixed_point
- \+ *lemma* dist_fixed_point_fixed_point_of_dist_le'
- \+ *lemma* fixed_point_is_fixed
- \+ *lemma* fixed_point_unique
- \+ *lemma* dist_fixed_point_le
- \+ *lemma* aposteriori_dist_iterate_fixed_point_le
- \+ *lemma* apriori_dist_iterate_fixed_point_le
- \+ *lemma* fixed_point_lipschitz_in_map
- \+ *theorem* fixed_point_unique'
- \+ *theorem* exists_fixed_point
- \+ *def* contracting_with

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* lipschitz_inf_dist_pt
- \+ *lemma* uniform_continuous_inf_dist_pt
- \+ *lemma* continuous_inf_dist_pt
- \- *lemma* uniform_continuous_inf_dist
- \- *lemma* continuous_inf_dist

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* nndist_map_le
- \+ *lemma* edist_map_le
- \+ *lemma* ediam_image_le
- \+ *lemma* diam_image_le
- \+ *lemma* dist_iterate_succ_le_geometric
- \- *lemma* fixed_point_of_tendsto_iterate
- \- *lemma* uniform_continuous_of_lipschitz
- \- *lemma* continuous_of_lipschitz
- \- *lemma* uniform_continuous_of_le_add
- \- *lemma* dist_inequality_of_contraction
- \- *theorem* fixed_point_unique_of_contraction
- \- *theorem* exists_fixed_point_of_contraction
- \+/\- *def* lipschitz_with
- \+/\- *def* lipschitz_with



## [2019-11-20 15:36:42](https://github.com/leanprover-community/mathlib/commit/5a6a67f)
fix(data/padics): misstated lemma ([#1718](https://github.com/leanprover-community/mathlib/pull/1718))
#### Estimated changes
Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_zero



## [2019-11-20 01:38:56](https://github.com/leanprover-community/mathlib/commit/0744a3a)
feat(analysis/normed_space/operator_norm): extension of a uniform continuous function ([#1649](https://github.com/leanprover-community/mathlib/pull/1649))
* Extension of a uniform continuous function
* Use characteristic properties of an extended function, instead of the explicit construction
* Add documentation on similar results in the library
* Update src/topology/algebra/uniform_extension.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Travis failed for no reason
* Update uniform_extension.lean
* eliminate `uniform_extension.lean`
* Update operator_norm.lean
* Update operator_norm.lean
* Remove `M`
* Fix docstring; extend_zero should be a simp lemma
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* extend_zero
- \+ *lemma* op_norm_extend_le
- \- *theorem* uniform_continuous
- \+ *def* extend



## [2019-11-19 23:41:43](https://github.com/leanprover-community/mathlib/commit/d67e527)
feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2` ([#1709](https://github.com/leanprover-community/mathlib/pull/1709))
* feat(algebra/group_power): prove Bernoulli's inequality for `a ≥ -2`
* Restate inequalities as suggested by @fpvandoorn
* Fix docs
#### Estimated changes
Modified src/algebra/archimedean.lean

Modified src/algebra/group_power.lean
- \+ *theorem* one_add_mul_le_pow'
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_mul_le_pow

Modified src/algebra/ordered_group.lean
- \+ *lemma* neg_le_iff_add_nonneg
- \+ *lemma* le_neg_iff_add_nonpos
- \+ *lemma* neg_le_self
- \+ *lemma* self_le_neg

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1



## [2019-11-19 20:49:00](https://github.com/leanprover-community/mathlib/commit/d4fd722)
feat(algebra/group; data/nat) lemmas for sub sub assoc ([#1712](https://github.com/leanprover-community/mathlib/pull/1712))
* Lemmas for sub sub assoc
* Removed a lemma
#### Estimated changes
Modified src/algebra/group/basic.lean

Modified src/data/nat/basic.lean
- \+/\- *lemma* succ_div_of_dvd
- \+/\- *lemma* succ_div_of_not_dvd
- \+/\- *lemma* succ_div_of_dvd
- \+/\- *lemma* succ_div_of_not_dvd
- \+ *theorem* sub_sub_assoc



## [2019-11-19 18:41:34](https://github.com/leanprover-community/mathlib/commit/db6eab2)
fix(tactic/ring): bugfix ring sub ([#1714](https://github.com/leanprover-community/mathlib/pull/1714))
#### Estimated changes
Modified src/tactic/ring.lean

Modified test/ring.lean



## [2019-11-19 18:03:43](https://github.com/leanprover-community/mathlib/commit/740168b)
feat(.travis): add linting of new changes to CI ([#1634](https://github.com/leanprover-community/mathlib/pull/1634))
* feat(.travis): add linting of new changes to CI
* explicitly list which linters to use
* upate nolints
* fix nolints.txt
* fix nolints
* remove instance_priority test
#### Estimated changes
Modified .gitignore

Modified .travis.yml

Modified scripts/mk_all.sh

Modified scripts/rm_all.sh



## [2019-11-19 16:06:05+01:00](https://github.com/leanprover-community/mathlib/commit/02659d6)
chore(scripts/nolint): regenerate nolints
#### Estimated changes
Modified scripts/mk_nolint.lean

Modified scripts/nolints.txt



## [2019-11-19 13:09:36](https://github.com/leanprover-community/mathlib/commit/8d7f093)
fix(tactic/omega): use eval_expr' ([#1711](https://github.com/leanprover-community/mathlib/pull/1711))
* fix(tactic/omega): use eval_expr'
* add test
#### Estimated changes
Modified src/tactic/omega/int/main.lean

Modified src/tactic/omega/nat/main.lean

Modified test/omega.lean



## [2019-11-19 11:07:21](https://github.com/leanprover-community/mathlib/commit/e3be70d)
lemmas about powers of elements ([#1688](https://github.com/leanprover-community/mathlib/pull/1688))
* feat(algebra/archimedean): add alternative version of exists_int_pow_near
- also add docstrings
* feat(analysis/normed_space/basic): additional inequality lemmas
- that there exists elements with large and small norms in a nondiscrete normed field.
* doc(algebra/archimedean): edit docstrings
* Apply suggestions from code review
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* exists_int_pow_near'

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* exists_lt_norm
- \+ *lemma* exists_norm_lt



## [2019-11-19 04:28:27](https://github.com/leanprover-community/mathlib/commit/b0520a3)
feat(algebra/order): define `forall_lt_iff_le` and `forall_lt_iff_le'` ([#1707](https://github.com/leanprover-community/mathlib/pull/1707))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* forall_lt_iff_le
- \+ *lemma* forall_lt_iff_le'



## [2019-11-19 02:27:10](https://github.com/leanprover-community/mathlib/commit/5d5da7e)
feat(data/set/intervals): more lemmas ([#1665](https://github.com/leanprover-community/mathlib/pull/1665))
* feat(data/set/intervals): more lemmas
* Use `simp` in more proofs, drop two `@[simp]` attrs
* Drop more `@[simp]` attrs
It's not clear which side is simpler.
#### Estimated changes
Modified src/data/set/intervals.lean
- \+/\- *lemma* left_mem_Ioo
- \+/\- *lemma* left_mem_Ico
- \+/\- *lemma* left_mem_Icc
- \+/\- *lemma* left_mem_Ioc
- \+ *lemma* left_mem_Ici
- \+/\- *lemma* right_mem_Ioo
- \+/\- *lemma* right_mem_Ico
- \+/\- *lemma* right_mem_Icc
- \+/\- *lemma* right_mem_Ioc
- \+ *lemma* right_mem_Iic
- \+ *lemma* Ici_inter_Iic
- \+ *lemma* Ici_inter_Iio
- \+ *lemma* Ioi_inter_Iic
- \+ *lemma* Ioi_inter_Iio
- \+ *lemma* Ioc_diff_Ioo_eq_singleton
- \+ *lemma* Icc_diff_Ioc_eq_singleton
- \+ *lemma* Iic_inter_Iic
- \+ *lemma* Iio_inter_Iio
- \+ *lemma* Ici_inter_Ici
- \+ *lemma* Ioi_inter_Ioi
- \+ *lemma* Icc_inter_Icc
- \+ *lemma* Ico_inter_Ico
- \+ *lemma* Ioc_inter_Ioc
- \+/\- *lemma* Ioo_inter_Ioo
- \+/\- *lemma* left_mem_Ioo
- \+/\- *lemma* left_mem_Ico
- \+/\- *lemma* left_mem_Icc
- \+/\- *lemma* left_mem_Ioc
- \+/\- *lemma* right_mem_Ioo
- \+/\- *lemma* right_mem_Ico
- \+/\- *lemma* right_mem_Icc
- \+/\- *lemma* right_mem_Ioc
- \+/\- *lemma* Ioo_inter_Ioo



## [2019-11-18 23:52:03](https://github.com/leanprover-community/mathlib/commit/895f1ae)
feat(data/option): add `some_ne_none`, `bex_ne_none`, `ball_ne_none` ([#1708](https://github.com/leanprover-community/mathlib/pull/1708))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* some_ne_none
- \+ *lemma* bex_ne_none
- \+ *lemma* ball_ne_none



## [2019-11-18 20:32:48](https://github.com/leanprover-community/mathlib/commit/6b408eb)
feat(data/real/nnreal): define `nnreal.gi : galois_insertion of_real coe` ([#1699](https://github.com/leanprover-community/mathlib/pull/1699))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* le_coe_of_real
- \+/\- *lemma* of_real_coe
- \+/\- *lemma* of_real_coe

Modified src/order/galois_connection.lean
- \+ *def* galois_insertion.monotone_intro



## [2019-11-18 18:18:25](https://github.com/leanprover-community/mathlib/commit/af43a2b)
feat(data/nat/enat): add_right_cancel and other ([#1705](https://github.com/leanprover-community/mathlib/pull/1705))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* ne_top_iff_dom
- \+ *lemma* add_eq_top_iff



## [2019-11-18 16:16:44](https://github.com/leanprover-community/mathlib/commit/0d94020)
feat(algebra/order_functions): define `min/max_mul_of_nonneg` ([#1698](https://github.com/leanprover-community/mathlib/pull/1698))
Also define `monotone_mul_right_of_nonneg` and rename
`monotone_mul_of_nonneg` to `monotone_mul_left_of_nonneg`.
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* monotone_mul_left_of_nonneg
- \+ *lemma* monotone_mul_right_of_nonneg
- \+ *lemma* max_mul_of_nonneg
- \+ *lemma* min_mul_of_nonneg
- \- *lemma* monotone_mul_of_nonneg



## [2019-11-18 14:10:09](https://github.com/leanprover-community/mathlib/commit/3f9c4d8)
chore(data/set): use `Sort*` in more lemmas ([#1706](https://github.com/leanprover-community/mathlib/pull/1706))
Also replace `nonempty_of_nonempty_range` with
`range_ne_empty_iff_nonempty` and `range_ne_empty`.
The old lemma is equivalent to `range_ne_empty_iff_nonempty.mp`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* range_ne_empty_iff_nonempty
- \+ *lemma* range_ne_empty
- \+/\- *lemma* range_const_subset
- \+/\- *lemma* range_const
- \- *lemma* nonempty_of_nonempty_range
- \+/\- *lemma* range_const_subset
- \+/\- *lemma* range_const
- \+/\- *theorem* range_subset_iff
- \+/\- *theorem* range_subset_iff



## [2019-11-18 12:21:07](https://github.com/leanprover-community/mathlib/commit/428aec9)
feat(group_theory/congruence): create file about congruence relations ([#1690](https://github.com/leanprover-community/mathlib/pull/1690))
* add congruence.lean
* add has_mul
* add definition of congruence relation
* minor changes
* responding to review comments
* fix docstring mistake in setoid.lean
#### Estimated changes
Modified src/data/setoid.lean

Created src/group_theory/congruence.lean
- \+ *lemma* ext'
- \+ *lemma* ext
- \+ *lemma* to_setoid_inj
- \+ *lemma* ext_iff
- \+ *lemma* ext'_iff
- \+ *lemma* coe_eq
- \+ *lemma* mul_ker_mk_eq
- \+ *lemma* coe_mul
- \+ *lemma* Inf_to_setoid
- \+ *lemma* Inf_def
- \+ *lemma* le_Inf
- \+ *lemma* Inf_le
- \+ *lemma* inf_def
- \+ *lemma* con_gen_of_con
- \+ *lemma* con_gen_idem
- \+ *lemma* sup_eq_con_gen
- \+ *lemma* sup_def
- \+ *lemma* Sup_eq_con_gen
- \+ *lemma* Sup_def
- \+ *theorem* le_def
- \+ *theorem* inf_iff_and
- \+ *theorem* con_gen_eq
- \+ *theorem* con_gen_le
- \+ *theorem* con_gen_mono
- \+ *def* con_gen
- \+ *def* mul_ker
- \+ *def* pi



## [2019-11-18 10:15:17](https://github.com/leanprover-community/mathlib/commit/0a794fa)
feat(data/finset): new union, set difference, singleton lemmas ([#1702](https://github.com/leanprover-community/mathlib/pull/1702))
* Singleton iff unique element lemma
* Set difference lemmas
* Changes from review
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* eq_singleton_iff_unique_mem
- \+ *lemma* singleton_iff_unique_mem
- \+ *lemma* union_sdiff_symm
- \+ *lemma* sdiff_eq_empty_iff_subset
- \+ *theorem* union_sdiff_self_eq_union
- \+ *theorem* sdiff_union_self_eq_union



## [2019-11-18 08:08:24](https://github.com/leanprover-community/mathlib/commit/fafdcfd)
chore(data/set/lattice): get most proofs from `pi` instance. ([#1685](https://github.com/leanprover-community/mathlib/pull/1685))
This way we only provide proofs that don't come from `pi`
#### Estimated changes
Modified src/data/set/lattice.lean



## [2019-11-18 04:03:50](https://github.com/leanprover-community/mathlib/commit/d19f7bc)
feat(analysis/normed_space/finite_dimension): finite-dimensional spaces on complete fields ([#1687](https://github.com/leanprover-community/mathlib/pull/1687))
* feat(analysis/normed_space/finite_dimension): equivalence of norms, continuity of linear maps
* improve doc
* cleanup
* cleanup
* Update src/data/equiv/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* exact_mod_cast, remove classical
* unfreezeI
* remove typeclass assumption
* Update src/analysis/normed_space/finite_dimension.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/linear_algebra/basic.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Update src/linear_algebra/finite_dimensional.lean
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* cleanup
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* pi_norm_le_iff

Created src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* linear_map.continuous_on_pi
- \+ *lemma* continuous_equiv_fun_basis
- \+ *lemma* finite_dimensional.complete
- \+ *lemma* submodule.complete_of_finite_dimensional
- \+ *lemma* submodule.closed_of_finite_dimensional
- \+ *lemma* finite_dimensional.proper
- \+ *theorem* linear_map.continuous_of_finite_dimensional

Modified src/data/equiv/basic.lean
- \+ *lemma* range_eq_univ

Modified src/linear_algebra/basic.lean
- \+ *lemma* pi_eq_sum_univ
- \+ *lemma* pi_apply_eq_sum_univ

Modified src/linear_algebra/basis.lean
- \+ *lemma* equiv_fun_basis_symm_apply

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_submodule_le
- \+ *lemma* findim_of_field
- \+ *lemma* findim_eq_card
- \+ *theorem* findim_range_add_findim_ker

Modified src/topology/metric_space/basic.lean
- \+ *lemma* proper_image_of_proper



## [2019-11-18 02:08:50](https://github.com/leanprover-community/mathlib/commit/7c5f282)
chore(algebra/order_functions): rename `min/max_distrib_of_monotone` ([#1697](https://github.com/leanprover-community/mathlib/pull/1697))
New names `monotone.map_min/max` better align with `monoid_hom.map_mul` etc.
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* monotone.map_max
- \+ *lemma* monotone.map_min
- \- *lemma* max_distrib_of_monotone
- \- *lemma* min_distrib_of_monotone

Modified src/topology/metric_space/basic.lean



## [2019-11-18 00:18:22](https://github.com/leanprover-community/mathlib/commit/9607bbf)
feat(algebra/big_operators): sum_Ico_succ_top and others ([#1692](https://github.com/leanprover-community/mathlib/pull/1692))
* feat(Ico): sum_Ico_succ_top and others
* get rid of succ_bot and rename eq_cons
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_Ico_succ_top
- \+ *lemma* prod_Ico_succ_top
- \+ *lemma* sum_eq_sum_Ico_succ_bot
- \+ *lemma* prod_eq_prod_Ico_succ_bot

Modified src/data/finset.lean
- \+ *theorem* insert_succ_bot
- \- *theorem* eq_cons



## [2019-11-17 21:17:19](https://github.com/leanprover-community/mathlib/commit/f5385fe)
chore(order_functions): use weakly implicit brackets in strict mono ([#1701](https://github.com/leanprover-community/mathlib/pull/1701))
* chore(order_functions): use weakly implicit brackets in strict mono
* fix build
#### Estimated changes
Modified src/algebra/order_functions.lean

Modified src/data/finsupp.lean



## [2019-11-17 19:31:14](https://github.com/leanprover-community/mathlib/commit/474004f)
fix(topology/dense_embeddings): tweaks ([#1684](https://github.com/leanprover-community/mathlib/pull/1684))
* fix(topology/dense_embeddings): tweaks
This fixes some small issues with last summer dense embedding refactors.
This is preparation for helping with Bochner integration. Some of those
fixes are backported from the perfectoid project.
* chore(dense_embedding): remove is_closed_property'
* Update src/topology/uniform_space/completion.lean
* Update src/topology/dense_embedding.lean
#### Estimated changes
Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_range_iff_closure_range
- \+ *lemma* dense_range.closure_range
- \+ *lemma* dense_range.prod
- \+/\- *lemma* is_closed_property2
- \+/\- *lemma* is_closed_property3
- \+ *lemma* dense_range.induction_on
- \+ *lemma* dense_range.induction_on₂
- \+ *lemma* dense_range.induction_on₃
- \- *lemma* dense_range_iff_closure_eq
- \- *lemma* dense_range_prod
- \+/\- *lemma* is_closed_property2
- \+/\- *lemma* is_closed_property3

Modified src/topology/uniform_space/abstract_completion.lean

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* dense
- \+/\- *lemma* dense₂
- \+/\- *lemma* dense
- \+/\- *lemma* dense₂
- \- *lemma* induction_on₄



## [2019-11-17 17:46:28](https://github.com/leanprover-community/mathlib/commit/1805f16)
refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit ([#1691](https://github.com/leanprover-community/mathlib/pull/1691))
* refactor(order/bounds): make the first argument of `x ∈ upper_bounds s` implicit
* Use `∈ *_bounds` in the definition of `conditionally_complete_lattice`.
#### Estimated changes
Modified src/data/real/basic.lean

Modified src/data/real/nnreal.lean

Modified src/order/bounds.lean
- \+/\- *def* upper_bounds
- \+/\- *def* lower_bounds
- \+/\- *def* upper_bounds
- \+/\- *def* lower_bounds

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_above.mk
- \+/\- *lemma* bdd_below.mk
- \+/\- *lemma* bdd_above.mk
- \+/\- *lemma* bdd_below.mk
- \+/\- *def* bdd_above
- \+/\- *def* bdd_below
- \+/\- *def* bdd_above
- \+/\- *def* bdd_below

Modified src/order/galois_connection.lean

Modified src/topology/algebra/ordered.lean

Modified src/topology/instances/real.lean

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean



## [2019-11-17 15:38:07](https://github.com/leanprover-community/mathlib/commit/1034357)
feat(data/int/parity): not_even_iff ([#1694](https://github.com/leanprover-community/mathlib/pull/1694))
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *lemma* not_even_iff

Modified src/data/nat/parity.lean
- \+ *lemma* not_even_iff



## [2019-11-17 05:49:52](https://github.com/leanprover-community/mathlib/commit/e863c08)
feat(algebra/pointwise): set.add_comm_monoid ([#1696](https://github.com/leanprover-community/mathlib/pull/1696))
* feat(algebra/pointwise): set.add_comm_monoid
* defs not instances
* fixing instance names
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *def* comm_monoid
- \+ *def* add_comm_monoid

Modified src/measure_theory/ae_eq_fun.lean

Modified src/measure_theory/integration.lean

Modified src/measure_theory/measure_space.lean

Modified src/measure_theory/outer_measure.lean



## [2019-11-17 01:34:34](https://github.com/leanprover-community/mathlib/commit/6b1ab64)
Add lemma for injective pow ([#1683](https://github.com/leanprover-community/mathlib/pull/1683))
* Add lemma for injective pow
* Rename lemma and remove spaces
* Use strict-mono for monotonic pow
* Rename iff statements
* Add left injective pow as well
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* pow_right_strict_mono
- \+ *lemma* pow_le_iff_le_right
- \+ *lemma* pow_lt_iff_lt_right
- \+ *lemma* pow_right_injective
- \+ *lemma* pow_left_strict_mono
- \+ *lemma* pow_le_iff_le_left
- \+ *lemma* pow_lt_iff_lt_left
- \+ *lemma* pow_left_injective



## [2019-11-15 16:11:27](https://github.com/leanprover-community/mathlib/commit/6ebb7e7)
feat(data/nat/modeq): add_div and others ([#1689](https://github.com/leanprover-community/mathlib/pull/1689))
* feat(data/nat/modeq): add_div and others
* remove unnecessary positivity assumptions.
* fix build
* brackets
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* add_mod_add_ite
- \+ *lemma* add_mod_of_add_mod_lt
- \+ *lemma* add_mod_add_of_le_add_mod
- \+ *lemma* add_div
- \+ *lemma* add_div_eq_of_add_mod_lt
- \+ *lemma* add_div_eq_of_le_mod_add_mod
- \+ *lemma* add_div_le_add_div



## [2019-11-14 21:06:24](https://github.com/leanprover-community/mathlib/commit/40de4fc)
doc(order/bounds,order/conditionaly_complete_lattice): add some docs ([#1686](https://github.com/leanprover-community/mathlib/pull/1686))
* doc(order/bounds,order/conditionaly_complete_lattice): add some docs
* Fixes by @jcommelin
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix docs: `is_least` are not unique unless we have a partial order.
#### Estimated changes
Modified src/order/bounds.lean

Modified src/order/conditionally_complete_lattice.lean



## [2019-11-13 22:27:06](https://github.com/leanprover-community/mathlib/commit/6fbf9f7)
doc(*): proper markdown urls [ci skip] ([#1680](https://github.com/leanprover-community/mathlib/pull/1680))
#### Estimated changes
Modified .vscode/settings.json

Modified src/algebra/continued_fractions/basic.lean

Modified src/analysis/complex/polynomial.lean

Modified src/analysis/normed_space/real_inner_product.lean

Modified src/category/bitraversable/basic.lean

Modified src/category/bitraversable/instances.lean

Modified src/category/bitraversable/lemmas.lean

Modified src/category/monad/cont.lean

Modified src/category/traversable/basic.lean

Modified src/category/traversable/lemmas.lean

Modified src/category_theory/adjunction/fully_faithful.lean

Modified src/category_theory/elements.lean

Modified src/category_theory/monoidal/category.lean

Modified src/category_theory/monoidal/of_has_finite_products.lean

Modified src/data/holor.lean

Modified src/data/padics/hensel.lean

Modified src/data/padics/padic_integers.lean

Modified src/data/padics/padic_norm.lean

Modified src/data/padics/padic_numbers.lean

Modified src/data/real/pi.lean

Modified src/data/tree.lean

Modified src/group_theory/coset.lean

Modified src/linear_algebra/basis.lean

Modified src/linear_algebra/bilinear_form.lean

Modified src/linear_algebra/sesquilinear_form.lean

Modified src/logic/basic.lean

Modified src/measure_theory/giry_monad.lean

Modified src/measure_theory/measurable_space.lean

Modified src/ring_theory/maps.lean

Modified src/set_theory/cardinal.lean

Modified src/tactic/omega/eq_elim.lean

Modified src/tactic/ring.lean

Modified src/tactic/scc.lean

Modified src/topology/maps.lean

Modified src/topology/sheaves/stalks.lean



## [2019-11-13 20:20:04](https://github.com/leanprover-community/mathlib/commit/10ced76)
doc(*): move detailed headers into real module docs ([#1681](https://github.com/leanprover-community/mathlib/pull/1681))
* doc(*): move detailed headers into real module docs
* update zmod
#### Estimated changes
Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/fderiv.lean

Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/complex/exponential.lean

Modified src/category_theory/category/default.lean

Modified src/data/zmod/basic.lean

Modified src/data/zmod/quadratic_reciprocity.lean

Modified src/linear_algebra/finite_dimensional.lean

Modified src/tactic/finish.lean

Modified src/tactic/localized.lean

Modified src/topology/metric_space/gluing.lean

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/hausdorff_distance.lean

Modified src/topology/sequences.lean



## [2019-11-13 17:53:09](https://github.com/leanprover-community/mathlib/commit/4729624)
doc(data/rel): add docs to some definitions ([#1678](https://github.com/leanprover-community/mathlib/pull/1678))
* doc(data/rel): add docs to some definitions
* Update src/data/rel.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/rel.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/rel.lean



## [2019-11-13 14:36:39](https://github.com/leanprover-community/mathlib/commit/6f5ad3c)
add dvd_gcd_iff for nat ([#1682](https://github.com/leanprover-community/mathlib/pull/1682))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* dvd_gcd_iff



## [2019-11-13 12:44:49](https://github.com/leanprover-community/mathlib/commit/6625f66)
feat(analysis/calculus/deriv): one-dimensional derivatives ([#1670](https://github.com/leanprover-community/mathlib/pull/1670))
* feat(analysis/calculus/deriv): one-dimensional derivatives
* Typos.
* Define deriv f x as fderiv 𝕜 f x 1
* Proof style.
* Fix failing proofs.
#### Estimated changes
Created src/analysis/calculus/deriv.lean
- \+ *lemma* has_fderiv_at_filter_iff_has_deriv_at_filter
- \+ *lemma* has_fderiv_within_at_iff_has_deriv_within_at
- \+ *lemma* has_fderiv_at_iff_has_deriv_at
- \+ *lemma* deriv_within_zero_of_not_differentiable_within_at
- \+ *lemma* deriv_zero_of_not_differentiable_at
- \+ *lemma* has_deriv_within_at.differentiable_within_at
- \+ *lemma* has_deriv_at.differentiable_at
- \+ *lemma* has_deriv_within_at_univ
- \+ *lemma* has_deriv_within_at_inter'
- \+ *lemma* has_deriv_within_at_inter
- \+ *lemma* differentiable_within_at.has_deriv_within_at
- \+ *lemma* differentiable_at.has_deriv_at
- \+ *lemma* has_deriv_at.deriv
- \+ *lemma* has_deriv_within_at.deriv_within
- \+ *lemma* fderiv_within_deriv_within
- \+ *lemma* deriv_within_fderiv_within
- \+ *lemma* fderiv_deriv
- \+ *lemma* deriv_fderiv
- \+ *lemma* differentiable_at.deriv_within
- \+ *lemma* deriv_within_subset
- \+ *lemma* deriv_within_univ
- \+ *lemma* deriv_within_inter
- \+ *lemma* has_deriv_at_filter.congr_of_mem_sets
- \+ *lemma* has_deriv_within_at.congr_mono
- \+ *lemma* has_deriv_within_at.congr_of_mem_nhds_within
- \+ *lemma* has_deriv_at.congr_of_mem_nhds
- \+ *lemma* deriv_within_congr_of_mem_nhds_within
- \+ *lemma* deriv_within_congr
- \+ *lemma* deriv_congr_of_mem_nhds
- \+ *lemma* deriv_id
- \+ *lemma* deriv_within_id
- \+ *lemma* deriv_const
- \+ *lemma* deriv_within_const
- \+ *lemma* is_linear_map.has_deriv_at_filter
- \+ *lemma* is_linear_map.has_deriv_within_at
- \+ *lemma* is_linear_map.has_deriv_at
- \+ *lemma* is_linear_map.differentiable_at
- \+ *lemma* is_linear_map.differentiable_within_at
- \+ *lemma* is_linear_map.deriv
- \+ *lemma* is_linear_map.deriv_within
- \+ *lemma* is_linear_map.differentiable
- \+ *lemma* is_linear_map.differentiable_on
- \+ *lemma* deriv_within_add
- \+ *lemma* deriv_add
- \+ *lemma* deriv_within_neg
- \+ *lemma* deriv_neg
- \+ *lemma* deriv_within_sub
- \+ *lemma* deriv_sub
- \+ *lemma* has_deriv_at_filter.prod
- \+ *lemma* has_deriv_within_at.prod
- \+ *lemma* has_deriv_at.prod
- \+ *lemma* deriv_within.comp
- \+ *lemma* deriv.comp
- \+ *lemma* deriv_within_mul
- \+ *lemma* deriv_mul
- \+ *theorem* unique_diff_within_at.eq_deriv
- \+ *theorem* has_deriv_at_filter_iff_tendsto
- \+ *theorem* has_deriv_within_at_iff_tendsto
- \+ *theorem* has_deriv_at_iff_tendsto
- \+ *theorem* has_deriv_at_filter.mono
- \+ *theorem* has_deriv_within_at.mono
- \+ *theorem* has_deriv_at.has_deriv_at_filter
- \+ *theorem* has_deriv_at.has_deriv_within_at
- \+ *theorem* has_deriv_at_unique
- \+ *theorem* has_deriv_at_filter_congr_of_mem_sets
- \+ *theorem* has_deriv_at_filter_id
- \+ *theorem* has_deriv_within_at_id
- \+ *theorem* has_deriv_at_id
- \+ *theorem* has_deriv_at_filter_const
- \+ *theorem* has_deriv_within_at_const
- \+ *theorem* has_deriv_at_const
- \+ *theorem* has_deriv_at_filter.add
- \+ *theorem* has_deriv_within_at.add
- \+ *theorem* has_deriv_at.add
- \+ *theorem* has_deriv_at_filter.neg
- \+ *theorem* has_deriv_within_at.neg
- \+ *theorem* has_deriv_at.neg
- \+ *theorem* has_deriv_at_filter.sub
- \+ *theorem* has_deriv_within_at.sub
- \+ *theorem* has_deriv_at.sub
- \+ *theorem* has_deriv_at_filter.is_O_sub
- \+ *theorem* has_deriv_at_filter.tendsto_nhds
- \+ *theorem* has_deriv_within_at.continuous_within_at
- \+ *theorem* has_deriv_at.continuous_at
- \+ *theorem* has_deriv_at_filter.comp
- \+ *theorem* has_deriv_within_at.comp
- \+ *theorem* has_deriv_at.comp
- \+ *theorem* has_deriv_at.comp_has_deriv_within_at
- \+ *theorem* has_deriv_within_at.mul
- \+ *theorem* has_deriv_at.mul
- \+ *def* has_deriv_at_filter
- \+ *def* has_deriv_within_at
- \+ *def* has_deriv_at
- \+ *def* deriv_within
- \+ *def* deriv

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_zero_of_not_differentiable_within_at
- \+ *lemma* fderiv_zero_of_not_differentiable_at

Modified src/ring_theory/algebra.lean
- \+ *lemma* map_eq_self
- \+ *lemma* smul_eq_mul

Modified src/topology/algebra/module.lean
- \+ *lemma* one_apply
- \+ *lemma* smul_right_apply
- \+ *lemma* smul_right_one_one
- \+ *lemma* smul_right_one_eq_iff



## [2019-11-13 10:53:30](https://github.com/leanprover-community/mathlib/commit/3bb2b5c)
feat(algebra/big_operators): dvd_sum ([#1679](https://github.com/leanprover-community/mathlib/pull/1679))
* feat(data/multiset): dvd_sum
* feat(algebra/big_operators): dvd_sum
* fix build
* fix build
* fix build
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *theorem* dvd_sum

Modified src/data/list/basic.lean
- \+ *theorem* dvd_sum

Modified src/data/multiset.lean
- \+ *theorem* dvd_sum



## [2019-11-12 23:38:13](https://github.com/leanprover-community/mathlib/commit/dfd25ff)
chore(meta/expr): delete local_binder_info; rename to_implicit ([#1668](https://github.com/leanprover-community/mathlib/pull/1668))
* chore(meta/expr): delete local_binder_info; rename to_implicit
local_binder_info duplicated local_binding_info.
to_implicit has been renamed to_implicit_local_const, to distinguish it
from to_implicit_binder
* file missing from commit
#### Estimated changes
Modified src/meta/expr.lean

Modified src/tactic/core.lean

Modified src/tactic/ext.lean



## [2019-11-12 18:51:50](https://github.com/leanprover-community/mathlib/commit/1749a8d)
feat(group_theory/submonoid): add bundled submonoids and various lemmas ([#1623](https://github.com/leanprover-community/mathlib/pull/1623))
* WIP -- removing  and everything is broken
* test
* test
* tidy
* fixed localization
* starting on coset
* WIP
* submonoid.lean now compiles but no to_additive stuff
* submonoid.lean compiles
* putting is_submonoid back
* docstrings
* terrible docstrings up to line 370
* finished docstrings
* more to_additive stuff
* WIP -- removing  and everything is broken
* test
* test
* tidy
* fixed localization
* starting on coset
* WIP
* submonoid.lean now compiles but no to_additive stuff
* submonoid.lean compiles
* putting is_submonoid back
* docstrings
* terrible docstrings up to line 370
* finished docstrings
* more to_additive stuff
* WIP quotient monoids
* quotient monoids WIP
* quotient_monoid w/o ideals.lean all compiles
* removing lemma
* adjunction
* some tidying
* remove pointless equiv
* completion compiles (very slowly)
* add lemma
* tidying
* more tidying
* mul -> smul oops
* might now compile
* tidied! I think
* fix
* breaking/adding stuff & switching branch
* add Inf relation
* removing sorrys
* nearly updated quotient_monoid
* updated quotient_monoid
* resurrecting computability
* tidied congruence.lean, added some docstrings
* extending setoids instead, WIP
* starting Galois insertion
* a few more bits of to_additive and docs
* no battery
* up to line 800
* congruence'll compile when data.setoid exists now
* more updates modulo existence of data.setoid
* rearranging stuff
* docstrings
* starting additive docstrings
* using newer additive docstring format in submonoid
* docstrings, tidying
* fixes and to_additive stuff, all WIP
* temporary congruence fixes
* slightly better approach to kernels, general chaos
* aahh
* more mess
* deleting doomed inductive congruence closure
* many fixes and better char pred isoms
* docstrings for group_theory.submonoid
* removing everything but bundled submonoids/lemmas
* removing things etc
* removing random empty folder
* tidy
* adding lemma back
* tidying
* responding to PR comments
* change 2 defs to lemmas
* @[simp] group_power.lean lemmas
* responding to commute.lean comments
* Remove unnecessary add_semiconj_by.eq
* Change prod.submonoid to submonoid.prod
* replacing a / at the end of docstring
Sorry - don't make commits on your phone when your laptop's playing up :/
* removing some not very useful to_additives
* fix pi_instances namespaces
* remove unnecessary prefix
* change extensionality to ext
not sure this is necessary because surely merging will change this automatically, but Travis told me to, and I really want it to compile, and I am not at my laptop
#### Estimated changes
Modified src/algebra/commute.lean
- \+ *def* submonoid.centralizer
- \+ *def* submonoid.set.centralizer
- \+ *def* centralizer.add_submonoid
- \+ *def* set.centralizer.add_submonoid

Modified src/algebra/group/hom.lean
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* injective_iff

Modified src/algebra/group/units.lean
- \+ *theorem* eq_mul_inv_iff_mul_eq
- \+ *theorem* eq_inv_mul_iff_mul_eq
- \+ *theorem* inv_mul_eq_iff_eq_mul
- \+ *theorem* mul_inv_eq_iff_eq_mul

Modified src/algebra/group_power.lean
- \+ *lemma* ring_hom.map_pow
- \+ *theorem* map_pow
- \+ *theorem* map_smul
- \+ *theorem* map_gpow
- \+ *theorem* map_gsmul

Modified src/algebra/pi_instances.lean
- \+ *def* monoid_hom.fst
- \+ *def* monoid_hom.snd
- \+ *def* prod

Modified src/algebra/ring.lean
- \+ *lemma* comp_assoc
- \+ *theorem* injective_iff

Modified src/data/equiv/algebra.lean
- \+ *def* mk'
- \+ *def* to_ring_equiv

Modified src/group_theory/coset.lean
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_right_coset_right_coset
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_right_coset_right_coset

Modified src/group_theory/submonoid.lean
- \+/\- *lemma* powers.mul_mem
- \+/\- *lemma* multiples.add_mem
- \+/\- *lemma* is_submonoid.coe_pow
- \+ *lemma* mem_coe
- \+ *lemma* prod_mem
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* subtype_eq_val
- \+ *lemma* powers.self_mem
- \+ *lemma* pow_mem
- \+ *lemma* powers_subset
- \+ *lemma* coe_pow
- \+ *lemma* multiples.self_mem
- \+ *lemma* smul_mem
- \+ *lemma* multiples_subset
- \+ *lemma* coe_smul
- \+ *lemma* le_def
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* mem_inf
- \+ *lemma* Inf_le'
- \+ *lemma* le_Inf'
- \+ *lemma* mem_Inf
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* finset_prod_mem
- \+ *lemma* range_top_of_surjective
- \+ *lemma* image_closure'
- \+/\- *lemma* powers.mul_mem
- \+/\- *lemma* multiples.add_mem
- \+/\- *lemma* is_submonoid.coe_pow
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *theorem* subtype_apply
- \+ *theorem* le_closure'
- \+ *theorem* closure'_le
- \+ *theorem* closure'_mono
- \+ *theorem* closure'_singleton
- \+ *theorem* exists_list_of_mem_closure'
- \+ *theorem* mem_closure'_union_iff
- \+ *theorem* closure'_singleton
- \+ *def* submonoid.to_add_submonoid
- \+ *def* submonoid.of_add_submonoid
- \+ *def* add_submonoid.to_submonoid
- \+ *def* add_submonoid.of_submonoid
- \+ *def* submonoid.add_submonoid_equiv
- \+ *def* Union_of_directed
- \+ *def* subtype
- \+ *def* powers
- \+ *def* multiples
- \+ *def* univ
- \+ *def* bot
- \+ *def* inf
- \+ *def* comap
- \+ *def* map
- \+ *def* range
- \+ *def* subtype_mk
- \+ *def* range_mk
- \+ *def* set_inclusion
- \+ *def* closure'



## [2019-11-12 16:51:10](https://github.com/leanprover-community/mathlib/commit/7b07932)
feat(analysis/normed_space/operator_norm): continuity of linear forms; swap directions of `nnreal.coe_*` ([#1655](https://github.com/leanprover-community/mathlib/pull/1655))
* feat(analysis/normed_space/operator_norm): continuity of linear forms
* use lift, change nnreal.coe_le direction
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* linear_map.continuous_of_bound
- \+/\- *lemma* linear_map_with_bound_coe
- \+/\- *lemma* linear_map_with_bound_apply
- \+ *lemma* linear_map.continuous_iff_is_closed_ker
- \+ *lemma* linear_map.bound_of_continuous
- \+ *lemma* linear_equiv.uniform_embedding
- \+/\- *lemma* linear_map.continuous_of_bound
- \+/\- *lemma* linear_map_with_bound_coe
- \+/\- *lemma* linear_map_with_bound_apply
- \+/\- *theorem* bound
- \+ *theorem* uniform_continuous
- \+ *theorem* uniform_embedding_of_bound
- \+ *theorem* bound_of_uniform_embedding
- \+/\- *theorem* bound
- \+/\- *def* linear_map.with_bound
- \+/\- *def* linear_map.with_bound

Modified src/analysis/normed_space/riesz_lemma.lean

Modified src/data/real/ennreal.lean

Modified src/data/real/nnreal.lean

Modified src/measure_theory/decomposition.lean

Modified src/measure_theory/simple_func_dense.lean

Modified src/topology/metric_space/basic.lean
- \+ *lemma* dist_pi_lt_iff
- \+ *lemma* dist_pi_le_iff
- \+ *lemma* ball_pi
- \+ *lemma* closed_ball_pi
- \+ *lemma* proper_space_of_compact_closed_ball_of_le
- \+ *theorem* uniform_embedding_iff'

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniform_embedding_iff'

Modified src/topology/metric_space/isometry.lean



## [2019-11-12 15:22:02](https://github.com/leanprover-community/mathlib/commit/14435eb)
feat(algebra/lie_algebra): Define lie algebras ([#1644](https://github.com/leanprover-community/mathlib/pull/1644))
* feat(algebra/module): define abbreviation module.End
The algebra of endomorphisms of a module over a commutative ring.
* feat(ring_theory/algebra): define algebra structure on square matrices over a commutative ring
* feat(algebra/lie_algebras.lean): define Lie algebras
* feat(algebra/lie_algebras.lean): simp lemmas for Lie rings
Specifically:
  * zero_left
  * zero_right
  * neg_left
  * leg_right
* feat(algebra/lie_algebras): more simp lemmas for Lie rings
Specifically:
  * gsmul_left
  * gsmul_right
* style(algebra/lie_algebras): more systematic naming
* Update src/algebra/lie_algebras.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebras.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebras.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebras.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebras.lean
Catch up with renaming in recent Co-authored commits
* Rename src/algebra/lie_algebras.lean --> src/algebra/lie_algebra.lean
* Place lie_ring simp lemmas into global namespace
* Place lie_smul simp lemma into global namespace
* Drop now-redundant namespace qualifiers
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Catch up after recent Co-authored commits making carrier types implicit
* Add missing docstrings
* feat(algebra/lie_algebra): replace `instance` definitions with vanilla `def`s
* style(algebra/lie_algebra): Apply suggestions from code review
Co-Authored-By: Patrick Massot
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Minor tidy ups
#### Estimated changes
Modified docs/references.bib

Created src/algebra/lie_algebra.lean
- \+ *lemma* add_left
- \+ *lemma* add_right
- \+ *lemma* alternate
- \+ *lemma* jacobi
- \+ *lemma* add_lie
- \+ *lemma* lie_add
- \+ *lemma* lie_self
- \+ *lemma* lie_skew
- \+ *lemma* lie_zero
- \+ *lemma* zero_lie
- \+ *lemma* neg_lie
- \+ *lemma* lie_neg
- \+ *lemma* gsmul_lie
- \+ *lemma* lie_gsmul
- \+ *lemma* lie_smul
- \+ *lemma* smul_lie
- \+ *def* commutator
- \+ *def* lie_ring.of_associative_ring
- \+ *def* Ad
- \+ *def* bil_lie
- \+ *def* of_associative_algebra
- \+ *def* of_endomorphism_algebra
- \+ *def* matrix.lie_algebra

Modified src/algebra/module.lean

Modified src/ring_theory/algebra.lean



## [2019-11-12 13:20:50](https://github.com/leanprover-community/mathlib/commit/08880c9)
feat(data/equiv,category_theory): prove equivalences are the same as isos ([#1587](https://github.com/leanprover-community/mathlib/pull/1587))
* refactor(category_theory,algebra/category): make algebraic categories not [reducible]
Adapted from part of [#1438](https://github.com/leanprover-community/mathlib/pull/1438).
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* adding missing forget2 instances
* Converting Reid's comment to a [Note]
* adding examples testing coercions
* feat(data/equiv/algebra): equivalence of algebraic equivalences and categorical isomorphisms
* more @[simps]
* more @[simps]
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \+ *def* to_Ring_iso
- \+ *def* to_CommRing_iso
- \+ *def* Ring_iso_to_ring_equiv
- \+ *def* CommRing_iso_to_ring_equiv
- \+ *def* ring_equiv_iso_Ring_iso
- \+ *def* ring_equiv_iso_CommRing_iso

Modified src/algebra/category/Group.lean
- \+ *def* mul_equiv.to_Group_iso
- \+ *def* mul_equiv.to_CommGroup_iso
- \+ *def* Group_iso_to_mul_equiv
- \+ *def* CommGroup_iso_to_mul_equiv
- \+ *def* mul_equiv_iso_Group_iso
- \+ *def* mul_equiv_iso_CommGroup_iso
- \+ *def* iso_perm
- \+ *def* mul_equiv_perm

Modified src/algebra/category/Mon/basic.lean
- \+ *lemma* mul_equiv.to_Mon_iso_hom
- \+ *lemma* mul_equiv.to_Mon_iso_inv
- \+ *lemma* mul_equiv.to_CommMon_iso_hom
- \+ *lemma* mul_equiv.to_CommMon_iso_inv
- \+ *def* mul_equiv.to_Mon_iso
- \+ *def* mul_equiv.to_CommMon_iso
- \+ *def* Mon_iso_to_mul_equiv
- \+ *def* CommMon_iso_to_mul_equiv
- \+ *def* mul_equiv_iso_Mon_iso
- \+ *def* mul_equiv_iso_CommMon_iso

Modified src/algebra/group/to_additive.lean

Modified src/category_theory/concrete_category/basic.lean
- \+ *lemma* coe_hom_inv_id
- \+ *lemma* coe_inv_hom_id

Modified src/category_theory/conj.lean

Modified src/category_theory/endomorphism.lean
- \+ *def* units_End_equiv_Aut
- \- *def* units_End_eqv_Aut

Modified src/category_theory/single_obj.lean

Modified src/category_theory/types.lean
- \+ *lemma* equiv_equiv_iso_hom
- \+ *lemma* equiv_equiv_iso_inv
- \+ *def* equiv_iso_iso
- \+ *def* equiv_equiv_iso

Modified src/data/equiv/algebra.lean
- \+ *lemma* to_monoid_hom_apply_symm_to_monoid_hom_apply
- \+ *lemma* symm_to_monoid_hom_apply_to_monoid_hom_apply
- \+ *lemma* to_ring_hom_apply_symm_to_ring_hom_apply
- \+ *lemma* symm_to_ring_hom_apply_to_ring_hom_apply



## [2019-11-12 11:23:31](https://github.com/leanprover-community/mathlib/commit/2cbeed9)
style(*): use notation `𝓝` for `nhds` ([#1582](https://github.com/leanprover-community/mathlib/pull/1582))
* chore(*): notation for nhds
* Convert new uses of nhds
#### Estimated changes
Modified docs/contribute/style.md

Modified docs/theories/topology.md
- \+/\- *def* compact
- \+/\- *def* compact

Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_within_at_inter
- \+/\- *lemma* differentiable_within_at_inter
- \+/\- *lemma* fderiv_within_inter
- \+/\- *lemma* fderiv_congr_of_mem_nhds
- \+/\- *lemma* has_fderiv_within_at_inter
- \+/\- *lemma* differentiable_within_at_inter
- \+/\- *lemma* fderiv_within_inter
- \+/\- *lemma* fderiv_congr_of_mem_nhds
- \+/\- *theorem* has_fderiv_at.has_fderiv_at_filter
- \+/\- *theorem* has_fderiv_at.has_fderiv_at_filter

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_inter_nhds
- \+/\- *lemma* unique_diff_within_at_inter
- \+/\- *lemma* unique_diff_within_at.inter
- \+/\- *lemma* tangent_cone_inter_nhds
- \+/\- *lemma* unique_diff_within_at_inter
- \+/\- *lemma* unique_diff_within_at.inter

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* iterated_fderiv_within_inter
- \+/\- *lemma* iterated_fderiv_within_inter

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* tendsto_exp_zero_one
- \+/\- *lemma* tendsto_log_one_zero
- \+/\- *lemma* tendsto_exp_zero_one
- \+/\- *lemma* tendsto_log_one_zero

Modified src/analysis/normed_space/banach.lean

Modified src/analysis/normed_space/basic.lean

Modified src/analysis/normed_space/real_inner_product.lean

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_one_div_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_one_div_at_top_nhds_0_nat

Modified src/data/analysis/topology.lean

Modified src/data/padics/hensel.lean

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* lt_of_tendsto_zero_of_pos
- \+/\- *lemma* neg_lt_of_tendsto_zero_of_pos
- \+/\- *lemma* gt_of_tendsto_zero_of_neg
- \+/\- *lemma* lt_of_tendsto_zero_of_pos
- \+/\- *lemma* neg_lt_of_tendsto_zero_of_pos
- \+/\- *lemma* gt_of_tendsto_zero_of_neg
- \+/\- *theorem* is_st_of_tendsto
- \+/\- *theorem* is_st_of_tendsto

Modified src/measure_theory/decomposition.lean

Modified src/measure_theory/integration.lean

Modified src/measure_theory/measure_space.lean

Modified src/measure_theory/simple_func_dense.lean

Modified src/order/filter/pointwise.lean

Modified src/topology/algebra/group.lean
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* nhds_eq
- \+/\- *lemma* nhds_zero_eq_Z
- \+/\- *lemma* nhds_pointwise_mul
- \+/\- *lemma* nhds_is_mul_hom
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* nhds_eq
- \+/\- *lemma* nhds_zero_eq_Z
- \+/\- *lemma* nhds_pointwise_mul
- \+/\- *lemma* nhds_is_mul_hom

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* has_sum
- \+/\- *def* has_sum

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* tendsto_mul'
- \+/\- *lemma* tendsto_mul'

Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* mem_nhds_one
- \+/\- *lemma* mem_nhds_one

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* tendsto_max
- \+/\- *lemma* tendsto_min
- \+/\- *lemma* lt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* ge_mem_nhds
- \+/\- *lemma* mem_nhds_orderable_dest
- \+/\- *lemma* is_bounded_le_nhds
- \+/\- *lemma* is_cobounded_ge_nhds
- \+/\- *lemma* is_bounded_ge_nhds
- \+/\- *lemma* is_cobounded_le_nhds
- \+/\- *lemma* tendsto_max
- \+/\- *lemma* tendsto_min
- \+/\- *lemma* lt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* ge_mem_nhds
- \+/\- *lemma* mem_nhds_orderable_dest
- \+/\- *lemma* is_bounded_le_nhds
- \+/\- *lemma* is_cobounded_ge_nhds
- \+/\- *lemma* is_bounded_ge_nhds
- \+/\- *lemma* is_cobounded_le_nhds
- \+/\- *theorem* Limsup_nhds
- \+/\- *theorem* Liminf_nhds
- \+/\- *theorem* Liminf_eq_of_le_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds
- \+/\- *theorem* Limsup_nhds
- \+/\- *theorem* Liminf_nhds
- \+/\- *theorem* Liminf_eq_of_le_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds

Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniformity_eq_comap_nhds_zero
- \+/\- *lemma* uniformity_eq_comap_nhds_zero'
- \+/\- *lemma* is_Z_bilin.tendsto_zero_left
- \+/\- *lemma* is_Z_bilin.tendsto_zero_right
- \+/\- *lemma* uniformity_eq_comap_nhds_zero
- \+/\- *lemma* uniformity_eq_comap_nhds_zero'
- \+/\- *lemma* is_Z_bilin.tendsto_zero_left
- \+/\- *lemma* is_Z_bilin.tendsto_zero_right

Modified src/topology/bases.lean

Modified src/topology/basic.lean
- \+/\- *lemma* nhds_def
- \+/\- *lemma* le_nhds_iff
- \+/\- *lemma* nhds_le_of_le
- \+/\- *lemma* nhds_sets
- \+/\- *lemma* mem_of_nhds
- \+/\- *lemma* tendsto_const_nhds
- \+/\- *lemma* pure_le_nhds
- \+/\- *lemma* nhds_neq_bot
- \+/\- *lemma* interior_eq_nhds
- \+/\- *lemma* is_open_iff_nhds
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *lemma* closure_eq_nhds
- \+/\- *lemma* is_closed_iff_nhds
- \+/\- *lemma* lim_spec
- \+/\- *lemma* nhds_def
- \+/\- *lemma* le_nhds_iff
- \+/\- *lemma* nhds_le_of_le
- \+/\- *lemma* nhds_sets
- \+/\- *lemma* mem_of_nhds
- \+/\- *lemma* tendsto_const_nhds
- \+/\- *lemma* pure_le_nhds
- \+/\- *lemma* nhds_neq_bot
- \+/\- *lemma* interior_eq_nhds
- \+/\- *lemma* is_open_iff_nhds
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *lemma* closure_eq_nhds
- \+/\- *lemma* is_closed_iff_nhds
- \+/\- *lemma* lim_spec
- \+/\- *theorem* mem_closure_iff_nhds
- \+/\- *theorem* mem_closure_iff_nhds
- \+/\- *def* continuous_at
- \+/\- *def* continuous_at

Modified src/topology/bounded_continuous_function.lean

Modified src/topology/compact_open.lean

Modified src/topology/constructions.lean
- \+/\- *lemma* nhds_prod_eq
- \+/\- *lemma* nhds_swap
- \+/\- *lemma* map_nhds_subtype_val_eq
- \+/\- *lemma* nhds_prod_eq
- \+/\- *lemma* nhds_swap
- \+/\- *lemma* map_nhds_subtype_val_eq

Modified src/topology/continuous_on.lean
- \+/\- *lemma* mem_nhds_within_of_mem_nhds
- \+/\- *lemma* continuous_within_at_inter
- \+/\- *lemma* mem_nhds_within_of_mem_nhds
- \+/\- *lemma* continuous_within_at_inter
- \+/\- *theorem* nhds_within_univ
- \+/\- *theorem* inter_mem_nhds_within
- \+/\- *theorem* nhds_within_restrict'
- \+/\- *theorem* nhds_within_univ
- \+/\- *theorem* inter_mem_nhds_within
- \+/\- *theorem* nhds_within_restrict'
- \+/\- *def* nhds_within
- \+/\- *def* nhds_within

Modified src/topology/dense_embedding.lean
- \+/\- *lemma* tendsto_comap_nhds_nhds
- \+/\- *lemma* comap_nhds_neq_bot
- \+/\- *lemma* extend_eq
- \+/\- *lemma* tendsto_comap_nhds_nhds
- \+/\- *lemma* comap_nhds_neq_bot
- \+/\- *lemma* extend_eq

Modified src/topology/instances/complex.lean
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* tendsto_inv

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* coe_range_mem_nhds
- \+/\- *lemma* nhds_coe
- \+/\- *lemma* nhds_coe_coe
- \+/\- *lemma* tendsto_of_real
- \+/\- *lemma* nhds_top
- \+/\- *lemma* nhds_zero
- \+/\- *lemma* Icc_mem_nhds
- \+/\- *lemma* nhds_of_ne_top
- \+/\- *lemma* coe_range_mem_nhds
- \+/\- *lemma* nhds_coe
- \+/\- *lemma* nhds_coe_coe
- \+/\- *lemma* tendsto_of_real
- \+/\- *lemma* nhds_top
- \+/\- *lemma* nhds_zero
- \+/\- *lemma* Icc_mem_nhds
- \+/\- *lemma* nhds_of_ne_top

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* tendsto_of_real
- \+/\- *lemma* tendsto_of_real

Modified src/topology/instances/real.lean
- \+/\- *lemma* real.tendsto_inv
- \+/\- *lemma* real.tendsto_inv

Modified src/topology/list.lean
- \+/\- *lemma* nhds_list
- \+/\- *lemma* nhds_nil
- \+/\- *lemma* nhds_list
- \+/\- *lemma* nhds_nil

Modified src/topology/local_homeomorph.lean

Modified src/topology/maps.lean
- \+/\- *lemma* inducing.map_nhds_eq
- \+/\- *lemma* is_open_map_iff_nhds_le
- \+/\- *lemma* inducing.map_nhds_eq
- \+/\- *lemma* is_open_map_iff_nhds_le

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* nhds_comap_dist
- \+/\- *lemma* nhds_comap_dist
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds

Modified src/topology/metric_space/cau_seq_filter.lean
- \+/\- *lemma* half_pow_tendsto_zero
- \+/\- *lemma* B2_lim
- \+/\- *lemma* le_nhds_cau_filter_lim
- \+/\- *lemma* half_pow_tendsto_zero
- \+/\- *lemma* B2_lim
- \+/\- *lemma* le_nhds_cau_filter_lim

Modified src/topology/metric_space/closeds.lean

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds
- \+/\- *theorem* nhds_eq
- \+/\- *theorem* mem_nhds_iff
- \+/\- *theorem* ball_mem_nhds

Modified src/topology/metric_space/gromov_hausdorff.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/lipschitz.lean

Modified src/topology/order.lean
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* map_nhds_induced_eq

Modified src/topology/separation.lean
- \+/\- *lemma* compl_singleton_mem_nhds
- \+/\- *lemma* eq_of_nhds_neq_bot
- \+/\- *lemma* t2_iff_nhds
- \+/\- *lemma* nhds_eq_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff
- \+/\- *lemma* lim_eq
- \+/\- *lemma* lim_nhds_eq
- \+/\- *lemma* locally_compact_of_compact_nhds
- \+/\- *lemma* nhds_is_closed
- \+/\- *lemma* compl_singleton_mem_nhds
- \+/\- *lemma* eq_of_nhds_neq_bot
- \+/\- *lemma* t2_iff_nhds
- \+/\- *lemma* nhds_eq_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff
- \+/\- *lemma* lim_eq
- \+/\- *lemma* lim_nhds_eq
- \+/\- *lemma* locally_compact_of_compact_nhds
- \+/\- *lemma* nhds_is_closed

Modified src/topology/sequences.lean

Modified src/topology/stone_cech.lean
- \+/\- *lemma* ultrafilter_comap_pure_nhds
- \+/\- *lemma* convergent_eqv_pure
- \+/\- *lemma* ultrafilter_comap_pure_nhds
- \+/\- *lemma* convergent_eqv_pure

Modified src/topology/subset_properties.lean
- \+/\- *def* compact
- \+/\- *def* compact

Modified src/topology/topological_fiber_bundle.lean

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* nhds_eq_comap_uniformity
- \+/\- *lemma* nhds_eq_uniformity
- \+/\- *lemma* tendsto_right_nhds_uniformity
- \+/\- *lemma* tendsto_left_nhds_uniformity
- \+/\- *lemma* nhds_eq_comap_uniformity
- \+/\- *lemma* nhds_eq_uniformity
- \+/\- *lemma* tendsto_right_nhds_uniformity
- \+/\- *lemma* tendsto_left_nhds_uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_nhds
- \+/\- *lemma* cauchy_nhds
- \+/\- *def* is_complete
- \+/\- *def* is_complete

Modified src/topology/uniform_space/complete_separated.lean

Modified src/topology/uniform_space/completion.lean

Modified src/topology/uniform_space/pi.lean

Modified src/topology/uniform_space/separation.lean

Modified src/topology/uniform_space/uniform_embedding.lean



## [2019-11-12 07:05:03](https://github.com/leanprover-community/mathlib/commit/3cae70d)
feat(extensionality): generate ext_iff for structures ([#1656](https://github.com/leanprover-community/mathlib/pull/1656))
* feat(extensionality): generate ext_iff for structures
* fix
* core.lean [skip ci]
* Update ext.lean
* Update ext.lean
* Update tactics.md
* Update src/tactic/ext.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/ext.lean
- \+ *lemma* foo.ext
- \+ *lemma* foo.ext_iff

Modified test/tactics.lean



## [2019-11-12 05:02:30](https://github.com/leanprover-community/mathlib/commit/f58f340)
feat(order/lattice): add `monotone.le_map_sup` and `monotone.map_inf_le` ([#1673](https://github.com/leanprover-community/mathlib/pull/1673))
Use it to simplify some proofs in `data/rel`.
#### Estimated changes
Modified src/data/rel.lean
- \+ *lemma* image_subset
- \+/\- *lemma* image_mono
- \+ *lemma* core_subset
- \+/\- *lemma* core_mono
- \+/\- *lemma* core_union
- \+/\- *lemma* image_mono
- \+/\- *lemma* core_mono
- \+/\- *lemma* core_union

Modified src/order/lattice.lean
- \+ *lemma* le_map_sup
- \+ *lemma* map_inf_le



## [2019-11-12 03:02:15](https://github.com/leanprover-community/mathlib/commit/c28497f)
chore(*): use `iff.rfl` instead of `iff.refl _` ([#1675](https://github.com/leanprover-community/mathlib/pull/1675))
#### Estimated changes
Modified src/algebra/associated.lean

Modified src/algebra/order.lean
- \+/\- *lemma* ge_iff_le
- \+/\- *lemma* gt_iff_lt
- \+/\- *lemma* ge_iff_le
- \+/\- *lemma* gt_iff_lt

Modified src/data/equiv/basic.lean

Modified src/data/fin.lean
- \+/\- *lemma* lt_iff_val_lt_val
- \+/\- *lemma* le_iff_val_le_val
- \+/\- *lemma* lt_iff_val_lt_val
- \+/\- *lemma* le_iff_val_le_val

Modified src/data/finmap.lean

Modified src/data/opposite.lean
- \+/\- *lemma* op_inj_iff
- \+/\- *lemma* unop_inj_iff
- \+/\- *lemma* op_inj_iff
- \+/\- *lemma* unop_inj_iff

Modified src/data/pfun.lean

Modified src/data/rel.lean

Modified src/data/set/basic.lean
- \+/\- *lemma* set_of_app_iff
- \+/\- *lemma* set_of_app_iff

Modified src/data/set/lattice.lean

Modified src/group_theory/free_group.lean

Modified src/measure_theory/measurable_space.lean

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* mem_a_e_iff
- \+/\- *lemma* all_ae_iff
- \+/\- *lemma* mem_a_e_iff
- \+/\- *lemma* all_ae_iff

Modified src/order/filter/basic.lean

Modified src/order/filter/partial.lean

Modified src/set_theory/zfc.lean
- \+/\- *theorem* mem_hom_right
- \+/\- *theorem* subset_hom
- \+/\- *theorem* mem_hom_right
- \+/\- *theorem* subset_hom

Modified src/topology/instances/nnreal.lean

Modified src/topology/order.lean

Modified src/topology/uniform_space/basic.lean

Modified src/topology/uniform_space/cauchy.lean



## [2019-11-11 21:44:54](https://github.com/leanprover-community/mathlib/commit/d077887)
cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot` ([#1672](https://github.com/leanprover-community/mathlib/pull/1672))
* cleanup(data/equiv/basic): drop `quot_equiv_of_quot'`, rename `quot_equiv_of_quot`
* `quot_equiv_of_quot` was the same as `quot.congr`
* rename `quot_equiv_of_quot` to `quot.congr_left` to match
  `quot.congr` and `quot.congr_right`.
* Add docs
#### Estimated changes
Modified src/data/equiv/basic.lean
- \- *def* quot_equiv_of_quot'
- \- *def* quot_equiv_of_quot



## [2019-11-11 15:19:29](https://github.com/leanprover-community/mathlib/commit/a5b3af3)
fix(tactic/core): correct `of_int` doc string ([#1671](https://github.com/leanprover-community/mathlib/pull/1671))
#### Estimated changes
Modified src/tactic/core.lean



## [2019-11-11 02:02:13](https://github.com/leanprover-community/mathlib/commit/6ecdefc)
chore(analysis/calculus/deriv): rename to fderiv ([#1661](https://github.com/leanprover-community/mathlib/pull/1661))
#### Estimated changes
Renamed src/analysis/calculus/deriv.lean to src/analysis/calculus/fderiv.lean

Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/calculus/times_cont_diff.lean



## [2019-11-10 23:56:06](https://github.com/leanprover-community/mathlib/commit/886b15b)
doc(measure_theory/l1_space): add doc and some lemmas ([#1657](https://github.com/leanprover-community/mathlib/pull/1657))
* Add doc and lemmas
* Remove unnecessary assumption
* Fix integrable_neg
* Remove extra assumptions
* Wrong variable used
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_norm

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_const_mul_le
- \+ *lemma* lintegral_const_mul'

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_of_ae_eq
- \+ *lemma* integrable_iff_of_ae_eq
- \+ *lemma* lintegral_nnnorm_eq_lintegral_edist
- \+ *lemma* integrable_iff_lintegral_edist
- \+ *lemma* lintegral_edist_triangle
- \+ *lemma* lintegral_edist_lt_top
- \+/\- *lemma* lintegral_nnnorm_zero
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* integrable_add
- \+/\- *lemma* lintegral_nnnorm_neg
- \+/\- *lemma* integrable_neg
- \+ *lemma* integrable_sub
- \+ *lemma* integrable_norm
- \+/\- *lemma* integrable_smul
- \+/\- *lemma* integrable_mk
- \+ *lemma* integrable_to_fun
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* integrable_add
- \+/\- *lemma* integrable_neg
- \+ *lemma* integrable_sub
- \+/\- *lemma* integrable_smul
- \+ *lemma* mk_eq_mk
- \+ *lemma* ext_iff
- \+ *lemma* all_ae_mk_to_fun
- \+ *lemma* self_eq_mk
- \+/\- *lemma* zero_def
- \+ *lemma* zero_to_fun
- \+ *lemma* mk_zero
- \+/\- *lemma* add_def
- \+ *lemma* mk_add
- \+ *lemma* add_to_fun
- \+ *lemma* neg_mk
- \+ *lemma* neg_to_fun
- \+ *lemma* sub_to_fun
- \+/\- *lemma* dist_def
- \+ *lemma* dist_to_fun
- \+/\- *lemma* norm_def
- \+ *lemma* norm_mk
- \+ *lemma* norm_to_fun
- \+ *lemma* lintegral_edist_to_fun_lt_top
- \+/\- *lemma* smul_def
- \+ *lemma* smul_mk
- \+ *lemma* smul_to_fun
- \+/\- *lemma* lintegral_nnnorm_zero
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* integrable_add
- \+/\- *lemma* lintegral_nnnorm_neg
- \+/\- *lemma* integrable_neg
- \+/\- *lemma* integrable_smul
- \+/\- *lemma* integrable_mk
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* integrable_add
- \+/\- *lemma* integrable_neg
- \+/\- *lemma* integrable_smul
- \+/\- *lemma* dist_def
- \+/\- *lemma* zero_def
- \+/\- *lemma* add_def
- \+/\- *lemma* norm_def
- \+/\- *lemma* smul_def
- \+/\- *def* integrable
- \+/\- *def* integrable
- \+/\- *def* l1
- \+/\- *def* mk
- \+/\- *def* integrable
- \+/\- *def* integrable
- \+/\- *def* l1
- \+/\- *def* mk

Modified src/measure_theory/measure_space.lean
- \+ *lemma* all_ae_eq_refl
- \+ *lemma* all_ae_eq_symm
- \+ *lemma* all_ae_eq_trans



## [2019-11-10 21:49:19](https://github.com/leanprover-community/mathlib/commit/ce48727)
fix(order/conditionally_complete_lattice): fix 2 misleading names ([#1666](https://github.com/leanprover-community/mathlib/pull/1666))
* `cSup_upper_bounds_eq_cInf` → `cSup_lower_bounds_eq_cInf`;
* `cInf_lower_bounds_eq_cSup` → `cInf_upper_bounds_eq_cSup`.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cSup_lower_bounds_eq_cInf
- \+ *lemma* cInf_upper_bounds_eq_cSup
- \- *lemma* cSup_upper_bounds_eq_cInf
- \- *lemma* cInf_lower_bounds_eq_cSup

Modified src/order/liminf_limsup.lean



## [2019-11-10 19:42:35](https://github.com/leanprover-community/mathlib/commit/f738ec7)
refactor(data/zmod/quadratic_reciprocity): simplify proof of quadratic reciprocity and prove when 2 is a square ([#1609](https://github.com/leanprover-community/mathlib/pull/1609))
* feat(number_theory/sum_four_squares): every natural number is the sum of four square numbers
* gauss_lemma
* Johan's suggestions
* some better parity proofs
* refactor(data/finset): restate disjoint_filter
* fix build
* fix silly lemmas in finite_fields
* generalize a lemma
* work on add_sum_mul_div_eq_mul
* fix build
* Update src/number_theory/sum_four_squares.lean
* feat(data/multiset): map_eq_map_of_bij_of_nodup
* finish proof of quad_rec
* minor fix
* Add docs
* add docs in correct style
* Use Ico 1 p instead of (range p).erase 0
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_Ico_id_eq_fact
- \- *lemma* prod_range_id_eq_fact

Modified src/data/nat/parity.lean
- \+ *lemma* even_div
- \+ *theorem* neg_one_pow_eq_one_iff_even

Modified src/data/zmod/basic.lean
- \+ *lemma* cast_nat_abs_val_min_abs
- \+ *lemma* nat_abs_val_min_abs_neg
- \+ *lemma* val_eq_ite_val_min_abs
- \+ *lemma* neg_eq_self_mod_two
- \+ *lemma* nat_abs_mod_two
- \+ *lemma* cast_nat_abs_val_min_abs
- \+ *lemma* nat_abs_val_min_abs_neg
- \+ *lemma* val_eq_ite_val_min_abs

Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* prod_Ico_one_prime
- \+ *lemma* Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
- \+ *lemma* div_eq_filter_card
- \+/\- *lemma* legendre_sym_eq_pow
- \+ *lemma* gauss_lemma
- \+ *lemma* legendre_sym_eq_one_iff
- \+ *lemma* eisenstein_lemma
- \+ *lemma* legendre_sym_two
- \+ *lemma* exists_pow_two_eq_two_iff
- \- *lemma* prod_range_prime_erase_zero
- \- *lemma* filter_range_p_mul_q_div_two_eq
- \- *lemma* prod_filter_range_p_mul_q_div_two_eq
- \- *lemma* prod_filter_range_p_mul_q_div_two_mod_p_eq
- \- *lemma* prod_filter_range_p_mul_q_not_coprime_eq
- \- *lemma* prod_range_p_mul_q_filter_coprime_mod_p
- \- *lemma* card_range_p_mul_q_filter_not_coprime
- \- *lemma* prod_filter_range_p_mul_q_div_two_eq_prod_product
- \- *lemma* prod_range_div_two_erase_zero
- \- *lemma* range_p_product_range_q_div_two_prod
- \- *lemma* prod_range_p_mul_q_div_two_ite_eq
- \+/\- *lemma* legendre_sym_eq_pow
- \+/\- *theorem* quadratic_reciprocity
- \+/\- *theorem* quadratic_reciprocity



## [2019-11-10 17:58:18](https://github.com/leanprover-community/mathlib/commit/4e68129)
feat(data/finset): Ico.subset ([#1669](https://github.com/leanprover-community/mathlib/pull/1669))
Does not have the `m1 < n1` assumption required for `subset_iff`
#### Estimated changes
Modified src/data/finset.lean



## [2019-11-10 15:51:47](https://github.com/leanprover-community/mathlib/commit/2cd59b4)
feat(coinduction): add identifier list to `coinduction` tactic ([#1653](https://github.com/leanprover-community/mathlib/pull/1653))
* feat(coinduction): add identifier list to `coinduction` tactic
* Update coinductive_predicates.lean
* two doc strings [skip ci]
* Update coinductive_predicates.lean
* fix merge
* move definitions around
* move more stuff
* fix build
* move and document functions
#### Estimated changes
Modified src/meta/coinductive_predicates.lean
- \- *def* last_string

Modified src/meta/expr.lean
- \+ *def* last_string

Modified src/tactic/core.lean

Modified src/tactic/mk_iff_of_inductive_prop.lean

Modified test/examples.lean



## [2019-11-10 13:45:26](https://github.com/leanprover-community/mathlib/commit/209e039)
cleanup(tactic/core): removing unused tactics ([#1641](https://github.com/leanprover-community/mathlib/pull/1641))
* doc(tactic/core): begin to add docstrings
* a few more doc strings
* more additions
* more doc
* deal with an undocumented definition by removing it
* minor
* add doc string
* remove some unused core tactics
* Revert "remove some unused core tactics"
This reverts commit 52de333c0c3fd4294930b270eeac503425f0070f.
* document get_classes
* Revert "deal with an undocumented definition by removing it"
This reverts commit 07b56e7456911466a15f1c340d9964e08aab195e.
* more doc strings
* dead code
* revert changing `subobject_names` to private
* remaining doc strings
* cleanup(tactic/core): removing unused tactics
* remove file_simp_attribute_decl and simp_lemmas_from_file
* delete drop_binders
* fix merge, delete check_defn
#### Estimated changes
Modified src/tactic/core.lean



## [2019-11-10 11:28:40](https://github.com/leanprover-community/mathlib/commit/4ecc17b)
fix(scripts/mk_all): don't add `lint_mathlib` to `all.lean` [ci skip] ([#1667](https://github.com/leanprover-community/mathlib/pull/1667))
#### Estimated changes
Modified scripts/mk_all.sh



## [2019-11-09 22:41:00](https://github.com/leanprover-community/mathlib/commit/c497f96)
feat(tactic/norm_cast): add push_cast simp attribute ([#1647](https://github.com/leanprover-community/mathlib/pull/1647))
* feat(tactic/norm_cast): add push_cast simp attribute
* test and docs
#### Estimated changes
Modified docs/tactics.md

Modified src/tactic/norm_cast.lean

Modified test/norm_cast.lean



## [2019-11-09 19:14:09](https://github.com/leanprover-community/mathlib/commit/1236ced)
feat(data/nat/basic): succ_div ([#1664](https://github.com/leanprover-community/mathlib/pull/1664))
* feat(data/nat/basic): succ_div
Rather long proof, but it was the best I could do.
* Update basic.lean
* add the two lemmas for each case
* get rid of positivity assumption
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* succ_div
- \+ *lemma* succ_div_of_dvd
- \+ *lemma* succ_div_of_not_dvd



## [2019-11-09 14:11:28](https://github.com/leanprover-community/mathlib/commit/1c24f92)
feat(data/list/basic): nth_le_append_right ([#1662](https://github.com/leanprover-community/mathlib/pull/1662))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* nth_le_append_right_aux
- \+ *lemma* nth_le_append_right



## [2019-11-09 11:29:30](https://github.com/leanprover-community/mathlib/commit/b0c36df)
feat(measure_theory/integration) lemmas for calculating integral of simple functions ([#1659](https://github.com/leanprover-community/mathlib/pull/1659))
* lemmas for calculating integration on simple functions
* Updates
* `finsupp` changed to `fin_vol_supp`
* less conditions for `to_real_mul_to_real`
* `sum_lt_top` with more abstraction
* Fix extra arguments
* One tactic per line
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_lt_top
- \+ *lemma* sum_lt_top_iff

Modified src/data/real/ennreal.lean
- \+/\- *lemma* of_real_eq_coe_nnreal
- \+ *lemma* sum_lt_top
- \+ *lemma* sum_lt_top_iff
- \+ *lemma* to_nnreal_sum
- \+ *lemma* to_real_sum
- \+/\- *lemma* of_real_lt_iff_lt_to_real
- \+/\- *lemma* le_of_real_iff_to_real_le
- \+/\- *lemma* to_real_of_real_mul
- \+ *lemma* to_real_mul_top
- \+ *lemma* to_real_top_mul
- \+ *lemma* to_real_eq_to_real
- \+ *lemma* to_real_mul_to_real
- \+/\- *lemma* of_real_eq_coe_nnreal
- \+/\- *lemma* of_real_lt_iff_lt_to_real
- \+/\- *lemma* le_of_real_iff_to_real_le
- \+/\- *lemma* to_real_of_real_mul

Modified src/measure_theory/integration.lean
- \+ *lemma* preimage_eq_empty_iff
- \+ *lemma* map_preimage
- \+ *lemma* map_preimage_singleton
- \+ *lemma* pair_preimage
- \+ *lemma* pair_preimage_singleton
- \+ *lemma* smul_apply
- \+ *lemma* smul_eq_map
- \+/\- *lemma* approx_apply
- \+/\- *lemma* approx_comp
- \+/\- *lemma* ennreal_rat_embed_encode
- \+ *lemma* volume_bUnion_preimage
- \+/\- *lemma* integral_map
- \+ *lemma* fin_vol_supp_map
- \+ *lemma* fin_vol_supp_of_fin_vol_supp_map
- \+ *lemma* fin_vol_supp_pair
- \+ *lemma* integral_lt_top_of_fin_vol_supp
- \+ *lemma* fin_vol_supp_of_integral_lt_top
- \+ *lemma* integral_map_coe_lt_top
- \+ *lemma* lintegral_rw₁
- \+ *lemma* lintegral_rw₂
- \+ *lemma* simple_func.lintegral_map
- \+/\- *lemma* approx_apply
- \+/\- *lemma* approx_comp
- \+/\- *lemma* ennreal_rat_embed_encode
- \+/\- *lemma* integral_map

Modified src/measure_theory/simple_func_dense.lean



## [2019-11-08 14:09:26+01:00](https://github.com/leanprover-community/mathlib/commit/ca21616)
chore(scripts): add linter and update nolints
#### Estimated changes
Modified scripts/mk_nolint.lean

Modified scripts/nolints.txt



## [2019-11-08 13:57:15+01:00](https://github.com/leanprover-community/mathlib/commit/8afcc5a)
feat(scripts): add nolints.txt
#### Estimated changes
Created scripts/nolints.txt



## [2019-11-08 11:03:46](https://github.com/leanprover-community/mathlib/commit/3223ba7)
doc(linear_algebra): rename lin_equiv to linear_equiv ([#1660](https://github.com/leanprover-community/mathlib/pull/1660))
#### Estimated changes
Modified src/linear_algebra/basic.lean

Modified src/linear_algebra/matrix.lean
- \+ *def* linear_equiv_matrix'
- \+ *def* linear_equiv_matrix
- \- *def* lin_equiv_matrix'
- \- *def* lin_equiv_matrix



## [2019-11-07 23:25:38](https://github.com/leanprover-community/mathlib/commit/362acb5)
feat(tactic/lint, script/mk_nolint): generate list of failing declarations to be ignored ([#1636](https://github.com/leanprover-community/mathlib/pull/1636))
* feat(tactic/lint): return names of failing declarations
* feat(scripts/mk_nolint): produce sorted list of declarations failing lint tests
* fix copyright
* fix test
* Update scripts/mk_nolint.lean
#### Estimated changes
Created scripts/mk_nolint.lean

Modified src/tactic/lint.lean

Modified test/lint.lean



## [2019-11-07 03:43:41](https://github.com/leanprover-community/mathlib/commit/c718a22)
feat(extensionality): rename to `ext`; generate `ext` rules for structures ([#1645](https://github.com/leanprover-community/mathlib/pull/1645))
* Update core.lean
* Update tactics.lean
* integrate generation of extensionality lemma of structures into `ext`
* Update src/tactic/ext.lean [skip ci]
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/tactic/ext.lean [skip ci]
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/tactic/ext.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update ext.lean [skip ci]
* Update tactics.md [skip ci]
* fix build
* fix build
#### Estimated changes
Modified docs/tactics.md

Modified src/algebra/continued_fractions/basic.lean

Modified src/algebra/group/hom.lean

Modified src/algebra/group/units.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/algebra/module.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/algebra/ring.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/category/monad/basic.lean

Modified src/category/monad/cont.lean

Modified src/category/monad/writer.lean

Modified src/category_theory/comma.lean
- \+/\- *lemma* ext
- \+/\- *lemma* over_morphism.ext
- \+/\- *lemma* under_morphism.ext
- \+/\- *lemma* ext
- \+/\- *lemma* over_morphism.ext
- \+/\- *lemma* under_morphism.ext

Modified src/category_theory/endomorphism.lean

Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* cone_morphism.ext
- \+/\- *lemma* cocone_morphism.ext
- \+/\- *lemma* cone_morphism.ext
- \+/\- *lemma* cocone_morphism.ext
- \+/\- *def* ext
- \+/\- *def* ext
- \+/\- *def* ext
- \+/\- *def* ext

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.hom_ext
- \+/\- *lemma* colimit.hom_ext
- \+/\- *lemma* limit.hom_ext
- \+/\- *lemma* colimit.hom_ext

Modified src/category_theory/monad/algebra.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/category_theory/natural_transformation.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/data/buffer/basic.lean

Modified src/data/dfinsupp.lean

Modified src/data/equiv/algebra.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/data/equiv/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* perm.ext
- \+/\- *lemma* ext
- \+/\- *lemma* perm.ext

Modified src/data/equiv/local_equiv.lean

Modified src/data/finmap.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/data/finset.lean

Modified src/data/finsupp.lean

Modified src/data/list/alist.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/data/list/basic.lean

Modified src/data/matrix/basic.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/data/multiset.lean

Modified src/data/option/basic.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/data/pequiv.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/data/polynomial.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/data/seq/seq.lean

Modified src/data/set/basic.lean

Modified src/data/setoid.lean
- \+/\- *lemma* ext'
- \+/\- *lemma* ext'

Modified src/data/stream/basic.lean

Modified src/data/vector2.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/logic/embedding.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/measure_theory/integration.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_space.ext
- \+/\- *lemma* ext
- \+/\- *lemma* measurable_space.ext
- \+/\- *lemma* ext

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/measure_theory/probability_mass_function.lean

Modified src/order/filter/basic.lean

Modified src/ring_theory/algebra.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/ring_theory/ideals.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/ring_theory/power_series.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/tactic/ext.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/topology/algebra/module.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/topology/algebra/open_subgroup.lean

Modified src/topology/basic.lean

Modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/topology/local_homeomorph.lean

Modified src/topology/opens.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/topology/sheaves/presheaf_of_functions.lean

Modified src/topology/uniform_space/basic.lean

Modified test/ext.lean
- \+/\- *lemma* unit.ext
- \+/\- *lemma* df.ext
- \+/\- *lemma* unit.ext
- \+/\- *lemma* df.ext

Modified test/tactics.lean



## [2019-11-06 22:22:23](https://github.com/leanprover-community/mathlib/commit/17a7f69)
doc(measure_theory/ae_eq_fun): add documentations and some lemmas ([#1650](https://github.com/leanprover-community/mathlib/pull/1650))
* Add documentations. `to_fun`.
* More precise comments
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* ext
- \+ *lemma* self_eq_mk
- \+ *lemma* all_ae_mk_to_fun
- \+ *lemma* comp_mk
- \+ *lemma* comp_eq_mk_to_fun
- \+ *lemma* comp_to_fun
- \+ *lemma* comp₂_eq_mk_to_fun
- \+ *lemma* comp₂_to_fun
- \+ *lemma* lift_rel_iff_to_fun
- \+ *lemma* le_iff_to_fun_le
- \+ *lemma* const_to_fun
- \+ *lemma* zero_to_fun
- \+ *lemma* one_to_fun
- \+/\- *lemma* mk_add_mk
- \+ *lemma* add_to_fun
- \+ *lemma* neg_to_fun
- \+ *lemma* mk_sub_mk
- \+ *lemma* sub_to_fun
- \+ *lemma* smul_to_fun
- \+ *lemma* eintegral_to_fun
- \+ *lemma* comp_edist_to_fun
- \+ *lemma* edist_to_fun
- \+ *lemma* edist_zero_to_fun
- \+ *lemma* edist_to_fun'
- \+/\- *lemma* mk_add_mk



## [2019-11-06 07:01:00](https://github.com/leanprover-community/mathlib/commit/3c8bbdc)
chore(topology/subset_properties): simplify a proof ([#1652](https://github.com/leanprover-community/mathlib/pull/1652))
#### Estimated changes
Modified src/topology/subset_properties.lean



## [2019-11-05 23:56:57](https://github.com/leanprover-community/mathlib/commit/62815e3)
doc(tactic/core): docstrings on all definitions ([#1632](https://github.com/leanprover-community/mathlib/pull/1632))
* doc(tactic/core): begin to add docstrings
* a few more doc strings
* more additions
* more doc
* deal with an undocumented definition by removing it
* minor
* add doc string
* remove some unused core tactics
* Revert "remove some unused core tactics"
This reverts commit 52de333c0c3fd4294930b270eeac503425f0070f.
* document get_classes
* Revert "deal with an undocumented definition by removing it"
This reverts commit 07b56e7456911466a15f1c340d9964e08aab195e.
* more doc strings
* dead code
* revert changing `subobject_names` to private
* remaining doc strings
* Apply suggestions from code review
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* remove todo
#### Estimated changes
Modified src/meta/expr.lean

Modified src/tactic/core.lean



## [2019-11-05 21:26:42](https://github.com/leanprover-community/mathlib/commit/d9578a6)
docs(tactic/lint) add code fence around #print statement to avoid its args looking like html tags. ([#1651](https://github.com/leanprover-community/mathlib/pull/1651))
#### Estimated changes
Modified src/tactic/lint.lean



## [2019-11-05 15:37:42](https://github.com/leanprover-community/mathlib/commit/986e58c)
refactor(sum_two_square): extract lemmas about primes in Z[i] ([#1643](https://github.com/leanprover-community/mathlib/pull/1643))
* refactor(sum_two_square): extract lemmas about primes in Z[i]
* forgot to save
* docztring
* module docstrings
#### Estimated changes
Modified src/data/zsqrtd/gaussian_int.lean
- \+ *lemma* mod_four_eq_three_of_nat_prime_of_prime
- \+ *lemma* sum_two_squares_of_nat_prime_of_not_irreducible
- \+ *lemma* prime_of_nat_prime_of_mod_four_eq_three
- \+ *lemma* prime_iff_mod_four_eq_three_of_nat_prime

Modified src/number_theory/sum_two_squares.lean



## [2019-11-04 22:23:15](https://github.com/leanprover-community/mathlib/commit/f3f1fd8)
feat(floor): one more lemma ([#1646](https://github.com/leanprover-community/mathlib/pull/1646))
* feat(floor): one more lemma
and #lint fix
* Update src/algebra/floor.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/floor.lean
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+ *lemma* le_of_nat_ceil_le
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor



## [2019-11-04 20:13:48](https://github.com/leanprover-community/mathlib/commit/2dcc6c2)
fix(tactic/tfae,scc): change the strongly connected component algorithm ([#1600](https://github.com/leanprover-community/mathlib/pull/1600))
* fix(tactic/tfae,scc): change the strongly connected component algorithm
* add example
* fix scc algorithm and add documentation
* documentation [skip ci]
* Update scc.lean [skip ci]
* Update src/tactic/scc.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update scc.lean
* Update tactics.lean
* Update src/tactic/scc.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* rename mk_closure, add line breaks, grammar tweaks
* Update scc.lean
* add to `to_tactic_format` output and docstring, more minor fixes
#### Estimated changes
Modified src/tactic/scc.lean

Modified src/tactic/tfae.lean

Modified test/tactics.lean



## [2019-11-04 15:02:31](https://github.com/leanprover-community/mathlib/commit/ee5b38d)
feat(simps): allow the user to specify the projections ([#1630](https://github.com/leanprover-community/mathlib/pull/1630))
* feat(simps): allow the user to specify the projections
Also add option to shorten generated lemma names
Add the attribute to more places in the category_theory library
The projection lemmas of inl_ and inr_ are now called inl__obj and similar
* use simps partially in limits/cones and whiskering
* revert whiskering
* rename last_name to short_name
* Update src/category_theory/products/basic.lean
* Update src/category_theory/limits/cones.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/category_theory/products/associator.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/data/string/defs.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* clarify is_eta_expansion docstrings
#### Estimated changes
Modified docs/tactics.md

Modified src/category_theory/limits/cones.lean
- \- *lemma* cone_of_cocone_left_op_X
- \- *lemma* cocone_left_op_of_cone_X
- \- *lemma* cocone_of_cone_left_op_X
- \- *lemma* cone_left_op_of_cocone_X
- \+/\- *def* cone_of_cocone_left_op
- \+/\- *def* cocone_left_op_of_cone
- \+/\- *def* cocone_of_cone_left_op
- \+/\- *def* cone_left_op_of_cocone
- \+/\- *def* cone_of_cocone_left_op
- \+/\- *def* cocone_left_op_of_cone
- \+/\- *def* cocone_of_cone_left_op
- \+/\- *def* cone_left_op_of_cocone

Modified src/category_theory/products/associator.lean
- \- *lemma* associator_obj
- \- *lemma* associator_map
- \- *lemma* inverse_associator_obj
- \- *lemma* inverse_associator_map
- \+/\- *def* associator
- \+/\- *def* inverse_associator
- \+/\- *def* associator
- \+/\- *def* inverse_associator

Modified src/category_theory/products/basic.lean
- \- *lemma* inl_obj
- \- *lemma* inl_map
- \- *lemma* inr_obj
- \- *lemma* inr_map
- \- *lemma* fst_obj
- \- *lemma* fst_map
- \- *lemma* snd_obj
- \- *lemma* snd_map
- \- *lemma* swap_obj
- \- *lemma* swap_map
- \- *lemma* evaluation_obj_obj
- \- *lemma* evaluation_obj_map
- \- *lemma* evaluation_map_app
- \- *lemma* evaluation_uncurried_obj
- \- *lemma* evaluation_uncurried_map
- \- *lemma* prod_obj
- \- *lemma* prod_map
- \- *lemma* prod_app
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* swap
- \+/\- *def* symmetry
- \+/\- *def* evaluation
- \+/\- *def* evaluation_uncurried
- \+/\- *def* prod
- \+/\- *def* prod
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* swap
- \+/\- *def* symmetry
- \+/\- *def* evaluation
- \+/\- *def* evaluation_uncurried
- \+/\- *def* prod
- \+/\- *def* prod

Modified src/category_theory/sums/basic.lean
- \- *lemma* inl_obj
- \- *lemma* inl_map
- \- *lemma* inr_obj
- \- *lemma* inr_map
- \+/\- *def* inl_
- \+/\- *def* inr_
- \+/\- *def* inl_
- \+/\- *def* inr_

Modified src/data/list/defs.lean
- \+ *def* get_rest

Modified src/data/string/defs.lean
- \+ *def* get_rest

Modified src/meta/expr.lean

Modified src/tactic/core.lean

Modified src/tactic/simps.lean
- \- *lemma* {simp_lemma}.
- \- *lemma* {nm.append_suffix
- \- *lemma* {nm.append_suffix

Modified test/simps.lean
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify5_snd_snd.
- \+ *def* specify1
- \+ *def* specify2
- \+ *def* specify3
- \+ *def* specify4
- \+ *def* specify5
- \+ *def* short_name1



## [2019-11-03 15:40:43](https://github.com/leanprover-community/mathlib/commit/a6ace34)
feat(analysis/normed_space): Riesz's lemma ([#1642](https://github.com/leanprover-community/mathlib/pull/1642))
* fix(topology/metric_space/hausdorff_distance): fix typo
* feat(analysis/normed_space): Riesz's Lemma
* fix(analysis/normed_space): fix silly mistake in statement of riesz lemma
* style(analysis/normed_space/riesz_lemma): variable names & indent
* doc(analysis/normed_space/riesz_lemma): add attribution
* doc(analysis/normed_space/riesz_lemma): fix module docstring style
* style(analysis/normed_space/riesz_lemma): more style & documentation
- recall statement in module header comment
- typecast instead of unfold
#### Estimated changes
Created src/analysis/normed_space/riesz_lemma.lean
- \+ *lemma* riesz_lemma

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* mem_iff_inf_dist_zero_of_closed
- \- *lemma* mem_iff_ind_dist_zero_of_closed



## [2019-11-01 11:28:15](https://github.com/leanprover-community/mathlib/commit/9af7e5b)
refactor(linear_algebra/basic): use smul_right ([#1640](https://github.com/leanprover-community/mathlib/pull/1640))
* refactor(linear_algebra/basic): use smul_right
* Update src/linear_algebra/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/linear_algebra/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
#### Estimated changes
Modified src/analysis/calculus/deriv.lean

Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* smul_right_norm
- \- *lemma* scalar_prod_space_iso_norm
- \+/\- *theorem* bound
- \+/\- *theorem* bound

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* sum_apply
- \+/\- *lemma* sum_apply
- \- *def* scalar_prod_space_iso

Modified src/topology/algebra/module.lean
- \+ *def* smul_right
- \- *def* scalar_prod_space_iso



## [2019-11-01 03:25:06](https://github.com/leanprover-community/mathlib/commit/1710fd8)
feat(lint): add priority test for instances that always apply ([#1625](https://github.com/leanprover-community/mathlib/pull/1625))
* feat(lint): add priority test for instances that always apply
also move a defn from coinductive_predicates to expr
also slightly refactor incorrect_def_lemma
* update doc
* add priorities to linters
Now they are run in the order specified by the doc
* always run tests in the extra set
even when they are slow and  is false
* move some more declarations from coinductive_predicates to expr
remove coinductive_predicates as import from some (but not all) files
* reviewer comments
* remove unsafe prefixes
#### Estimated changes
Modified docs/tactics.md

Modified src/meta/coinductive_predicates.lean

Modified src/meta/expr.lean

Modified src/tactic/alias.lean

Modified src/tactic/core.lean

Modified src/tactic/explode.lean

Modified src/tactic/lint.lean



## [2019-11-01 01:22:43](https://github.com/leanprover-community/mathlib/commit/5f17abc)
fix(tactic/elide): was untested and buggy. Fixed a few issues ([#1638](https://github.com/leanprover-community/mathlib/pull/1638))
* fix(tactic/elide): was untested and buggy. Fixed a few issues
* Update tactics.lean
* add copyright header
* Update src/tactic/elide.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *def* hidden
- \+/\- *def* hidden

Modified src/tactic/elide.lean

Modified test/tactics.lean

