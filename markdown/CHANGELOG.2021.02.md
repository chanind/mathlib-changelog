## [2021-02-28 22:54:58](https://github.com/leanprover-community/mathlib/commit/13f30e5)
feat(geometry/manifold): `ext_chart_at` is smooth on its source ([#6473](https://github.com/leanprover-community/mathlib/pull/6473))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_within_at.congr'

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* ext_chart_at_coe
- \+/\- *lemma* ext_chart_at_coe_symm
- \+ *lemma* ext_chart_at_continuous_at'
- \+/\- *lemma* ext_chart_at_continuous_at
- \+ *lemma* ext_chart_at_map_nhds'
- \+ *lemma* ext_chart_at_map_nhds
- \+ *lemma* ext_chart_at_source_mem_nhds'
- \+ *lemma* ext_chart_at_target_subset_range
- \+ *lemma* ext_chart_continuous_at_symm''
- \+ *lemma* ext_chart_continuous_on_symm

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* times_cont_mdiff_at_ext_chart_at'
- \+ *lemma* times_cont_mdiff_at_ext_chart_at
- \+ *lemma* times_cont_mdiff_within_at_iff'



## [2021-02-28 22:54:57](https://github.com/leanprover-community/mathlib/commit/83bc663)
feat(category_theory/monoidal): skeleton of a monoidal category is a monoid ([#6444](https://github.com/leanprover-community/mathlib/pull/6444))
#### Estimated changes
Added src/category_theory/monoidal/skeleton.lean
- \+ *def* category_theory.comm_monoid_of_skeletal_braided
- \+ *def* category_theory.monoid_of_skeletal_monoidal



## [2021-02-28 22:54:56](https://github.com/leanprover-community/mathlib/commit/1e45472)
feat(analysis/calculus): Lagrange multipliers ([#6431](https://github.com/leanprover-community/mathlib/pull/6431))
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.to_add_monoid_hom_coe

Added src/analysis/calculus/lagrange_multipliers.lean
- \+ *lemma* is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at
- \+ *lemma* is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at
- \+ *lemma* is_local_extr_on.linear_dependent_of_has_strict_fderiv_at
- \+ *lemma* is_local_extr_on.range_ne_top_of_has_strict_fderiv_at

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.prod_option

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.pi_ring
- \+ *lemma* linear_equiv.pi_ring_apply
- \+ *lemma* linear_equiv.pi_ring_symm_apply

Modified src/order/filter/extr.lean
- \+ *lemma* is_max_filter.tendsto_principal_Iic
- \+ *lemma* is_min_filter.tendsto_principal_Ici

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.coe_sum'
- \+ *lemma* continuous_linear_map.coe_sum

Modified src/topology/continuous_on.lean




## [2021-02-28 20:56:20](https://github.com/leanprover-community/mathlib/commit/18804b2)
chore(category/equivalence): remove functor.fun_inv_id ([#6450](https://github.com/leanprover-community/mathlib/pull/6450))
`F.fun_inv_id` was just a confusing alternative way to write `F.as_equivalence.unit_iso.symm`, and meant that many lemmas couldn't fire.
Deletes the definitions `functor.fun_inv_id` and `functor.inv_hom_id`, and the lemmas `is_equivalence.functor_unit_comp` and `is_equivalence.inv_fun_id_inv_comp`.
#### Estimated changes
Modified src/category_theory/adjunction/lifting.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/equivalence.lean
- \- *def* category_theory.functor.fun_inv_id
- \- *def* category_theory.functor.inv_fun_id
- \- *lemma* category_theory.is_equivalence.functor_unit_comp
- \- *lemma* category_theory.is_equivalence.inv_fun_id_inv_comp



## [2021-02-28 20:56:19](https://github.com/leanprover-community/mathlib/commit/ac3c478)
feat(archive/100-theorems-list/9_area_of_a_circle): area of a disc ([#6374](https://github.com/leanprover-community/mathlib/pull/6374))
Freek № 9: The area of a disc with radius _r_ is _πr²_.
Also included are an `of_le` version of [FTC-2 for the open set](https://leanprover-community.github.io/mathlib_docs/find/interval_integral.integral_eq_sub_of_has_deriv_at') and the definition `nnreal.pi`.
Co-authored by @asouther4  and @jamesa9283.
#### Estimated changes
Modified .gitignore


Added archive/100-theorems-list/9_area_of_a_circle.lean
- \+ *theorem* area_disc
- \+ *def* disc
- \+ *lemma* disc_eq_region_between
- \+ *theorem* measurable_set_disc

Modified docs/100.yaml


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* nnreal.coe_real_pi
- \+ *lemma* nnreal.pi_ne_zero
- \+ *lemma* nnreal.pi_pos

Modified src/measure_theory/interval_integral.lean
- \+ *theorem* interval_integral.integral_eq_sub_of_has_deriv_at'_of_le



## [2021-02-28 17:40:43](https://github.com/leanprover-community/mathlib/commit/b181866)
feat(data/set): more lemmas ([#6474](https://github.com/leanprover-community/mathlib/pull/6474))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite_option
- \+ *lemma* set.subsingleton.finite

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Inter_const
- \+ *lemma* set.Inter_option
- \+/\- *theorem* set.Union_const
- \+ *lemma* set.Union_option
- \+ *theorem* set.disjoint_Union_left
- \+ *theorem* set.disjoint_Union_right

Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* disjoint_supr_iff
- \+ *theorem* inf_supr_eq
- \+ *theorem* infi_sup_eq
- \+ *theorem* sup_infi_eq
- \+ *lemma* supr_disjoint_iff
- \+ *theorem* supr_inf_eq

Modified src/order/complete_lattice.lean
- \+ *theorem* infi_option
- \+ *theorem* supr_option



## [2021-02-28 10:49:48](https://github.com/leanprover-community/mathlib/commit/ef5c1d5)
feat(analysis/special_functions/pow): smoothness of `complex.cpow` ([#6447](https://github.com/leanprover-community/mathlib/pull/6447))
* `x ^ y` is smooth in both variables at `(x, y)`, if `0 < re x` or
  `im x ≠ 0`;
* `x ^ y` is smooth in `y` if `x ≠ 0` or `y ≠ 0`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.cpow_def_of_ne_zero
- \+ *lemma* complex.cpow_sub
- \+ *lemma* complex.has_fderiv_at_cpow
- \+ *lemma* complex.has_strict_deriv_at_const_cpow
- \+ *lemma* complex.has_strict_deriv_at_cpow_const
- \+ *lemma* complex.has_strict_fderiv_at_cpow
- \+ *lemma* continuous.const_cpow
- \+ *lemma* continuous.cpow
- \+ *lemma* continuous_at.const_cpow
- \+ *lemma* continuous_at.cpow
- \+ *lemma* continuous_on.const_cpow
- \+ *lemma* continuous_on.cpow
- \+ *lemma* continuous_within_at.const_cpow
- \+ *lemma* continuous_within_at.cpow
- \+ *lemma* differentiable_at.const_cpow
- \+ *lemma* differentiable_at.cpow
- \+ *lemma* differentiable_within_at.const_cpow
- \+ *lemma* differentiable_within_at.cpow
- \+ *lemma* filter.tendsto.const_cpow
- \+ *lemma* filter.tendsto.cpow
- \+ *lemma* has_deriv_at.const_cpow
- \+ *lemma* has_deriv_at.cpow
- \+ *lemma* has_deriv_at.cpow_const
- \+ *lemma* has_deriv_within_at.const_cpow
- \+ *lemma* has_deriv_within_at.cpow
- \+ *lemma* has_deriv_within_at.cpow_const
- \+ *lemma* has_fderiv_at.const_cpow
- \+ *lemma* has_fderiv_at.cpow
- \+ *lemma* has_fderiv_within_at.const_cpow
- \+ *lemma* has_fderiv_within_at.cpow
- \+ *lemma* has_strict_deriv_at.const_cpow
- \+ *lemma* has_strict_deriv_at.cpow
- \+ *lemma* has_strict_deriv_at.cpow_const
- \+ *lemma* has_strict_fderiv_at.const_cpow
- \+ *lemma* has_strict_fderiv_at.cpow
- \+/\- *lemma* measurable.cpow

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.log_im_le_pi
- \+ *lemma* complex.neg_pi_lt_log_im
- \+ *lemma* real.cos_sub_pi



## [2021-02-28 07:50:15](https://github.com/leanprover-community/mathlib/commit/abb3121)
chore(*): more line lengths ([#6472](https://github.com/leanprover-community/mathlib/pull/6472))
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* is_bounded_bilinear_map.is_bounded_linear_map_right

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.bilinear_comp
- \+/\- *lemma* continuous_linear_map.to_span_singleton_homothety
- \+/\- *lemma* linear_map.mk_continuous_of_exists_bound_coe

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/computability/turing_machine.lean
- \+/\- *theorem* turing.blank_extends.refl

Modified src/control/basic.lean


Modified src/control/bitraversable/instances.lean


Modified src/control/equiv_functor.lean


Modified src/control/fix.lean


Modified src/control/fold.lean


Modified src/control/lawful_fix.lean
- \+/\- *lemma* pi.uncurry_curry_continuous

Modified src/control/monad/basic.lean
- \+/\- *lemma* map_eq_bind_pure_comp

Modified src/control/monad/cont.lean
- \+/\- *def* except_t.call_cc

Modified src/control/monad/writer.lean


Modified src/control/traversable/basic.lean


Modified src/control/traversable/derive.lean


Modified src/data/bitvec/core.lean


Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.of_real_smul

Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/finset/gcd.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/indicator_function.lean
- \+/\- *lemma* set.indicator_finset_sum

Modified src/data/multiset/nodup.lean
- \+/\- *theorem* multiset.nodup_add_of_nodup
- \+/\- *theorem* multiset.nodup_map
- \+/\- *theorem* multiset.nodup_union

Modified src/data/mv_polynomial/comm_ring.lean
- \+/\- *lemma* mv_polynomial.eval₂_sub

Modified src/data/mv_polynomial/counit.lean


Modified src/data/mv_polynomial/invertible.lean


Modified src/data/mv_polynomial/monad.lean


Modified src/data/mv_polynomial/variables.lean
- \+/\- *lemma* mv_polynomial.degrees_add_of_disjoint
- \+/\- *lemma* mv_polynomial.mem_support_not_mem_vars_zero

Modified src/data/nat/basic.lean


Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.to_with_top_coe'

Modified src/data/nat/gcd.lean
- \+/\- *theorem* nat.coprime.coprime_div_left
- \+/\- *theorem* nat.coprime.coprime_div_right

Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/padics/padic_norm.lean
- \+/\- *lemma* one_le_padic_val_nat_of_dvd
- \+/\- *lemma* padic_val_nat_primes
- \+/\- *lemma* padic_val_rat_of_nat

Modified src/data/padics/padic_numbers.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/pfunctor/multivariate/W.lean


Modified src/data/pfunctor/univariate/M.lean
- \+/\- *lemma* pfunctor.M.cases_on_mk'
- \+/\- *lemma* pfunctor.M.default_consistent
- \+/\- *lemma* pfunctor.M.isubtree_cons

Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/derivative.lean
- \+/\- *theorem* polynomial.nat_degree_eq_zero_of_derivative_eq_zero

Modified src/data/polynomial/integral_normalization.lean
- \+/\- *lemma* polynomial.integral_normalization_coeff_ne_nat_degree

Modified src/data/polynomial/iterated_deriv.lean
- \+/\- *lemma* polynomial.iterated_deriv_add
- \+/\- *lemma* polynomial.iterated_deriv_sub

Modified src/data/polynomial/ring_division.lean
- \+/\- *theorem* polynomial.nat_degree_le_of_dvd

Modified src/data/qpf/multivariate/basic.lean
- \+/\- *theorem* mvqpf.supp_eq

Modified src/data/qpf/multivariate/constructions/cofix.lean
- \+/\- *def* mvqpf.cofix.corec'

Modified src/data/qpf/multivariate/constructions/fix.lean
- \+/\- *def* mvqpf.fix.drec

Modified src/data/rat/basic.lean


Modified src/data/rat/sqrt.lean


Modified src/data/real/cardinality.lean


Modified src/data/set/countable.lean
- \+/\- *lemma* set.countable.bUnion
- \+/\- *lemma* set.countable.union

Modified src/data/set/function.lean
- \+/\- *theorem* set.left_inv_on.comp

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.sInter_insert
- \+/\- *theorem* set.sUnion_insert

Modified src/data/string/basic.lean


Modified src/data/sum.lean
- \+/\- *theorem* sum.lex_acc_inr

Modified src/data/vector2.lean
- \+/\- *lemma* vector.remove_nth_insert_nth

Modified src/data/zmod/basic.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean




## [2021-02-28 04:58:12](https://github.com/leanprover-community/mathlib/commit/f153a85)
chore(category_theory/*): fix long lines ([#6471](https://github.com/leanprover-community/mathlib/pull/6471))
#### Estimated changes
Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/adjunction/limits.lean
- \+/\- *def* category_theory.adjunction.functoriality_unit

Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/concrete_category/unbundled_hom.lean


Modified src/category_theory/conj.lean


Modified src/category_theory/const.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/functorial.lean


Modified src/category_theory/graded_object.lean
- \+/\- *lemma* category_theory.graded_object.comap_eq_symm

Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* category_theory.limits.evaluate_combined_cocones

Modified src/category_theory/limits/pi.lean
- \+/\- *def* category_theory.pi.cocone_of_cocone_eval_is_colimit

Modified src/category_theory/limits/shapes/finite_products.lean
- \+/\- *lemma* category_theory.limits.has_finite_coproducts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/regular_mono.lean
- \+/\- *def* category_theory.regular_of_is_pushout_fst_of_regular
- \+/\- *def* category_theory.regular_of_is_pushout_snd_of_regular

Modified src/category_theory/limits/shapes/types.lean
- \+/\- *lemma* category_theory.limits.types.pi_lift_π_apply

Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+/\- *def* category_theory.limits.wide_pullback_shape.wide_cospan

Modified src/category_theory/limits/types.lean
- \+/\- *lemma* category_theory.limits.types.is_limit_equiv_sections_apply
- \+/\- *lemma* category_theory.limits.types.is_limit_equiv_sections_symm_apply
- \+/\- *lemma* category_theory.limits.types.limit.π_mk

Modified src/category_theory/monad/limits.lean
- \+/\- *lemma* category_theory.monad.has_limit_of_comp_forget_has_limit

Modified src/category_theory/monoidal/CommMon_.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/internal/functor_category.lean


Modified src/category_theory/monoidal/natural_transformation.lean
- \+/\- *lemma* category_theory.monoidal_nat_iso.of_components.hom_app
- \+/\- *lemma* category_theory.monoidal_nat_iso.of_components.inv_app

Modified src/category_theory/monoidal/of_chosen_finite_products.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+/\- *def* category_theory.monoidal_of_has_finite_coproducts
- \+/\- *def* category_theory.monoidal_of_has_finite_products

Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/over.lean
- \+/\- *def* category_theory.over.iso_mk

Modified src/category_theory/products/basic.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/sums/associator.lean
- \+/\- *lemma* category_theory.sum.inverse_associator_obj_inl
- \+/\- *lemma* category_theory.sum.inverse_associator_obj_inr_inl
- \+/\- *lemma* category_theory.sum.inverse_associator_obj_inr_inr

Modified src/category_theory/whiskering.lean




## [2021-02-28 04:58:11](https://github.com/leanprover-community/mathlib/commit/c7a2d67)
refactor(analysis/calculus/specific_functions): add params to `smooth_bump_function` ([#6467](https://github.com/leanprover-community/mathlib/pull/6467))
In the construction of a partition of unity we need a smooth bump
function that vanishes outside of `ball x R` and equals one on
`closed_ball x r` with arbitrary `0 < r < R`.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean
- \+/\- *lemma* smooth_bump_function.eventually_eq_one
- \+ *lemma* smooth_bump_function.eventually_eq_one_of_mem_ball
- \- *lemma* smooth_bump_function.eventually_eq_one_of_norm_lt_one
- \+/\- *lemma* smooth_bump_function.le_one
- \+ *lemma* smooth_bump_function.lt_one_of_lt_dist
- \- *lemma* smooth_bump_function.lt_one_of_one_lt_norm
- \+/\- *lemma* smooth_bump_function.nonneg
- \+ *lemma* smooth_bump_function.one_of_mem_closed_ball
- \- *lemma* smooth_bump_function.one_of_norm_le_one
- \+ *lemma* smooth_bump_function.pos_of_mem_ball
- \- *lemma* smooth_bump_function.pos_of_norm_lt_two
- \+/\- *lemma* smooth_bump_function.support_eq
- \+ *lemma* smooth_bump_function.zero_of_le_dist
- \- *lemma* smooth_bump_function.zero_of_two_le_norm
- \+/\- *def* smooth_bump_function

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.map_nhds_eq
- \+ *lemma* continuous_linear_equiv.symm_map_nhds_eq

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.symm_map_nhds_eq

Modified src/topology/subset_properties.lean




## [2021-02-28 04:58:10](https://github.com/leanprover-community/mathlib/commit/cc3e2c7)
feat(linear_algebra/basic): f x ∈ submodule.span R (f '' s) ([#6453](https://github.com/leanprover-community/mathlib/pull/6453))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.apply_mem_span_image_of_mem_span
- \+ *lemma* submodule.not_mem_span_of_apply_not_mem_span_image



## [2021-02-28 01:58:42](https://github.com/leanprover-community/mathlib/commit/ee1947d)
chore(scripts): update nolints.txt ([#6468](https://github.com/leanprover-community/mathlib/pull/6468))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-28 01:58:42](https://github.com/leanprover-community/mathlib/commit/5b18369)
feat(ring_theory/power_series): coeff multiplication lemmas ([#6462](https://github.com/leanprover-community/mathlib/pull/6462))
Some lemmas used in combinatorics, from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.coeff_mul_of_lt_order
- \+ *lemma* power_series.coeff_mul_one_sub_of_lt_order
- \+ *lemma* power_series.coeff_mul_prod_one_sub_of_lt_order



## [2021-02-28 01:58:41](https://github.com/leanprover-community/mathlib/commit/11f1801)
feat(linear_algebra/quadratic_form): add associated_eq_self_apply ([#6458](https://github.com/leanprover-community/mathlib/pull/6458))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.associated_eq_self_apply



## [2021-02-28 01:58:40](https://github.com/leanprover-community/mathlib/commit/9668bdd)
feat(algebra/category/Mon/adjunctions): adjoin_unit adjunction from Semigroup ([#6440](https://github.com/leanprover-community/mathlib/pull/6440))
This PR provides the adjoin_unit-forgetful adjunction between `Semigroup` and `Mon` and additionally the second to last module doc in algebra, namely `algebra.group.with_one`.
#### Estimated changes
Added src/algebra/category/Mon/adjunctions.lean
- \+ *def* adjoin_one
- \+ *def* adjoin_one_adj

Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/group/with_one.lean
- \+ *lemma* with_one.map_comp
- \+ *lemma* with_one.map_id



## [2021-02-27 23:21:06](https://github.com/leanprover-community/mathlib/commit/09d572d)
feat(algebra/big_operators): additive versions of multiset lemmas ([#6463](https://github.com/leanprover-community/mathlib/pull/6463))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.sum_multiset_count
- \+ *lemma* finset.sum_multiset_map_count



## [2021-02-27 19:21:16](https://github.com/leanprover-community/mathlib/commit/aa0b274)
chore(*): split lines and move module doc `measure_theory/category/Meas` ([#6459](https://github.com/leanprover-community/mathlib/pull/6459))
#### Estimated changes
Modified src/deprecated/subgroup.lean


Modified src/deprecated/subring.lean


Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* finite_field.card_image_polynomial_eval

Modified src/field_theory/fixed.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/primitive_element.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *theorem* polynomial.factor_dvd_of_nat_degree_ne_zero

Modified src/field_theory/subfield.lean


Modified src/measure_theory/category/Meas.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/principal_ideal_domain.lean




## [2021-02-27 19:21:15](https://github.com/leanprover-community/mathlib/commit/d1b7a67)
feat(ring_theory/power_series/basic): coeff_zero_X_mul ([#6445](https://github.com/leanprover-community/mathlib/pull/6445))
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_power_series.coeff_zero_X_mul
- \+ *lemma* power_series.coeff_zero_X_mul



## [2021-02-27 16:06:18](https://github.com/leanprover-community/mathlib/commit/a19af60)
feat(data/option): add `option.forall` and `option.exists` ([#6419](https://github.com/leanprover-community/mathlib/pull/6419))
#### Estimated changes
Modified src/data/option/basic.lean


Modified src/data/seq/wseq.lean




## [2021-02-27 12:58:12](https://github.com/leanprover-community/mathlib/commit/4b02853)
feat(tactic/apply_fun): work on the goal as well ([#6439](https://github.com/leanprover-community/mathlib/pull/6439))
Extend the functionality of `apply_fun`, to "apply" functions to inequalities in the goal, as well.
```
Apply a function to an equality or inequality in either a local hypothesis or the goal.
* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.
```
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* ne_of_apply_ne

Modified src/tactic/apply_fun.lean


Modified test/apply_fun.lean




## [2021-02-27 09:13:13](https://github.com/leanprover-community/mathlib/commit/7256361)
chore(data/nat/choose): fix namespace of theorems ([#6451](https://github.com/leanprover-community/mathlib/pull/6451))
#### Estimated changes
Modified src/data/nat/choose/dvd.lean
- \+ *lemma* nat.choose_eq_factorial_div_factorial'
- \+ *lemma* nat.choose_mul
- \- *lemma* nat.prime.choose_eq_factorial_div_factorial'
- \- *lemma* nat.prime.choose_mul



## [2021-02-27 09:13:12](https://github.com/leanprover-community/mathlib/commit/5f68d0e)
feat(ring_theory/power_series/basic): rescale_inj ([#6446](https://github.com/leanprover-community/mathlib/pull/6446))
Authored-by Ashvni Narayanan
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.rescale_injective



## [2021-02-27 09:13:11](https://github.com/leanprover-community/mathlib/commit/f33418a)
feat(algebra/homology/chain_complex): pushforward of complex w.r.t. additive functor ([#6403](https://github.com/leanprover-community/mathlib/pull/6403))
This PR adds a definition for the pushforward of a homological complex with respect to an additive functor.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean
- \+ *def* category_theory.functor.map_homological_complex
- \+ *def* category_theory.functor.pushforward_homological_complex



## [2021-02-27 06:20:12](https://github.com/leanprover-community/mathlib/commit/7ce01bb)
feat(category_theory/skeletal): skeleton of a general category ([#6443](https://github.com/leanprover-community/mathlib/pull/6443))
Construct the skeleton of a category using choice.
#### Estimated changes
Modified src/category_theory/skeletal.lean
- \+ *def* category_theory.skeleton



## [2021-02-27 01:15:38](https://github.com/leanprover-community/mathlib/commit/1af882b)
chore(scripts): update nolints.txt ([#6449](https://github.com/leanprover-community/mathlib/pull/6449))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-26 23:38:23](https://github.com/leanprover-community/mathlib/commit/d38b5a5)
feat(category_theory/monoidal): construct the monoidal inverse to a functor ([#6442](https://github.com/leanprover-community/mathlib/pull/6442))
I worked out what was mentioned here: https://github.com/leanprover-community/mathlib/blob/20b49fbd453fc42c91c36ee30ecb512d70f48172/src/category_theory/monoidal/transport.lean#L283-L287
except for uniqueness, not sure how important that is
#### Estimated changes
Modified src/category_theory/monoidal/functor.lean
- \+ *def* category_theory.monoidal_adjoint
- \+ *def* category_theory.monoidal_inverse
- \+ *lemma* category_theory.monoidal_inverse_to_functor



## [2021-02-26 21:29:04](https://github.com/leanprover-community/mathlib/commit/a225e12)
feat(linear_algebra/basic): add is_scalar_tower instance for hom type ([#6331](https://github.com/leanprover-community/mathlib/pull/6331))
This instance tells Lean that if R is an S-algebra with R and S both commutative semirings, then the R-action on Hom_R(M,N) is compatible with the S-action.
`linear_map.is_scalar_tower_extend_scalars` is just a special case of this new instance with the `smul_comm_class` arguments populated with `is_scalar_tower.to_smul_comm_class` and `smul_comm_class_self`, so has been removed.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/linear_algebra/basic.lean




## [2021-02-26 20:32:43](https://github.com/leanprover-community/mathlib/commit/407615e)
feat(algebra/lie/solvable): images of solvable Lie algebras are solvable ([#6413](https://github.com/leanprover-community/mathlib/pull/6413))
Summary of changes:
New definition:
 - `lie_hom.range_restrict`
New lemmas:
 - `lie_ideal.derived_series_map_eq`
 - `function.surjective.lie_algebra_is_solvable`
 - `lie_algebra.solvable_iff_equiv_solvable`
 - `lie_hom.is_solvable_range`
 - `lie_hom.mem_range_self`
 - `lie_hom.range_restrict_apply`
 - `lie_hom.surjective_range_restrict`
Renamed lemmas:
 - `lie_algebra.is_solvable_of_injective` → `function.injective.lie_algebra_is_solvable`
 - `lie_ideal.derived_series_map_le_derived_series` → `lie_ideal.derived_series_map_le`
#### Estimated changes
Modified src/algebra/lie/solvable.lean
- \+ *lemma* function.injective.lie_algebra_is_solvable
- \+ *lemma* function.surjective.lie_algebra_is_solvable
- \- *lemma* lie_algebra.is_solvable_of_injective
- \+ *lemma* lie_algebra.solvable_iff_equiv_solvable
- \+ *lemma* lie_hom.is_solvable_range
- \+ *lemma* lie_ideal.derived_series_map_eq
- \+ *lemma* lie_ideal.derived_series_map_le
- \- *lemma* lie_ideal.derived_series_map_le_derived_series

Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_hom.mem_range_self
- \+ *def* lie_hom.range_restrict
- \+ *lemma* lie_hom.range_restrict_apply
- \+ *lemma* lie_hom.surjective_range_restrict



## [2021-02-26 19:47:44](https://github.com/leanprover-community/mathlib/commit/ddefd96)
feat(category_theory/subobject): kernels and images as subobjects ([#6301](https://github.com/leanprover-community/mathlib/pull/6301))
Further work on subobjects,  building on the initial definition in [#6278](https://github.com/leanprover-community/mathlib/pull/6278).
* Add noncomputable functions to obtain representatives of subobjects.
* Realise kernel/equalizer/image as subobjects.
#### Estimated changes
Modified src/category_theory/subobject.lean
- \+ *def* category_theory.limits.equalizer_subobject
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow'
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow_comp
- \+ *def* category_theory.limits.equalizer_subobject_iso
- \+ *def* category_theory.limits.factor_thru_image_subobject
- \+ *def* category_theory.limits.image_subobject
- \+ *lemma* category_theory.limits.image_subobject_arrow'
- \+ *lemma* category_theory.limits.image_subobject_arrow
- \+ *lemma* category_theory.limits.image_subobject_arrow_comp
- \+ *def* category_theory.limits.image_subobject_iso
- \+ *def* category_theory.limits.kernel_subobject
- \+ *lemma* category_theory.limits.kernel_subobject_arrow'
- \+ *lemma* category_theory.limits.kernel_subobject_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_arrow_comp
- \+ *def* category_theory.limits.kernel_subobject_iso
- \+/\- *lemma* category_theory.mono_over.bot_left
- \+/\- *lemma* category_theory.mono_over.forget_obj_left
- \+ *def* category_theory.mono_over.image_mono_over
- \+/\- *lemma* category_theory.mono_over.top_left
- \+ *def* category_theory.subobject.arrow
- \+ *def* category_theory.subobject.representative
- \+ *def* category_theory.subobject.representative_iso
- \+ *def* category_theory.subobject.underlying
- \+ *lemma* category_theory.subobject.underlying_arrow
- \+ *lemma* category_theory.subobject.underlying_as_coe
- \+ *def* category_theory.subobject.underlying_iso



## [2021-02-26 15:56:35](https://github.com/leanprover-community/mathlib/commit/11e1cc3)
feat(data/equiv/basic): Add `fin_succ_above_equiv` ([#5145](https://github.com/leanprover-community/mathlib/pull/5145))
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *def* fin_succ_equiv'
- \+ *lemma* fin_succ_equiv'_above
- \+ *lemma* fin_succ_equiv'_at
- \+ *lemma* fin_succ_equiv'_below
- \+ *lemma* fin_succ_equiv'_symm_none
- \+ *lemma* fin_succ_equiv'_zero
- \+/\- *def* fin_succ_equiv
- \+ *lemma* fin_succ_equiv_symm'_coe_above
- \+ *lemma* fin_succ_equiv_symm'_coe_below
- \+ *lemma* fin_succ_equiv_symm'_some_above
- \+ *lemma* fin_succ_equiv_symm'_some_below
- \+ *lemma* fin_succ_equiv_symm_coe

Modified src/data/fin.lean
- \+/\- *lemma* fin.cast_succ_pos
- \+ *lemma* fin.pred_above_above
- \+ *lemma* fin.pred_above_below
- \+ *lemma* fin.pred_above_last
- \+ *lemma* fin.pred_above_last_apply
- \+ *lemma* fin.pred_cast_succ_succ

Modified src/data/mv_polynomial/equiv.lean


Modified src/linear_algebra/linear_independent.lean




## [2021-02-26 13:13:36](https://github.com/leanprover-community/mathlib/commit/20b49fb)
feat(linear_algebra/tensor_product): allow different semirings in linear_map.flip ([#6414](https://github.com/leanprover-community/mathlib/pull/6414))
This also means the `map_*₂` lemmas are more generally applicable to linear_maps over different rings, such as `linear_map.prod_equiv.to_linear_map`.
To avoid breakage, this leaves `mk₂ R` for when R is commutative, and introduces `mk₂' R S` for when two different rings are wanted.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *theorem* linear_map.ext₂
- \+/\- *def* linear_map.flip
- \+/\- *theorem* linear_map.flip_apply
- \+/\- *theorem* linear_map.flip_inj
- \+/\- *def* linear_map.lflip
- \+/\- *theorem* linear_map.map_add₂
- \+/\- *theorem* linear_map.map_neg₂
- \+/\- *theorem* linear_map.map_smul₂
- \+/\- *theorem* linear_map.map_sub₂
- \+/\- *theorem* linear_map.map_zero₂
- \+ *def* linear_map.mk₂'
- \+ *theorem* linear_map.mk₂'_apply



## [2021-02-26 13:13:35](https://github.com/leanprover-community/mathlib/commit/47b62ea)
feat(algebra/big_operators): add lemmas about `sum` and `pi.single` ([#6390](https://github.com/leanprover-community/mathlib/pull/6390))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.sum_pi_single'
- \+ *lemma* finset.sum_pi_single

Modified src/algebra/big_operators/pi.lean
- \+/\- *lemma* ring_hom.functions_ext

Modified src/algebra/module/linear_map.lean
- \+ *theorem* linear_map.ext_ring_iff

Modified src/algebra/module/pi.lean
- \+/\- *lemma* pi.single_smul'
- \+/\- *lemma* pi.single_smul

Modified src/linear_algebra/pi.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.coe_pi'
- \+/\- *lemma* continuous_linear_map.coe_pi



## [2021-02-26 10:06:30](https://github.com/leanprover-community/mathlib/commit/aeda3fb)
feat(topology/instances/real, topology/metric_space/basic, algebra/floor): integers are a proper space ([#6437](https://github.com/leanprover-community/mathlib/pull/6437))
The metric space `ℤ` is a proper space.  Also, under the coercion from `ℤ` to `ℝ`, inverse images of compact sets are finite.
The key point for both facts is to express the inverse image of an `ℝ`-interval under the coercion as an appropriate `ℤ`-interval, using floor or ceiling of the endpoints -- I provide these facts as simp-lemmas.
Indirectly related discussion:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Finiteness.20of.20balls.20in.20the.20integers
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* int.preimage_Icc
- \+ *lemma* int.preimage_Ici
- \+ *lemma* int.preimage_Ico
- \+ *lemma* int.preimage_Iic
- \+ *lemma* int.preimage_Iio
- \+ *lemma* int.preimage_Ioc
- \+ *lemma* int.preimage_Ioi
- \+ *lemma* int.preimage_Ioo

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* int.tendsto_coe_cofinite



## [2021-02-26 10:06:29](https://github.com/leanprover-community/mathlib/commit/ff5fa52)
chore(data/finsupp/basic): add coe_{neg,sub,smul} lemmas to match coe_{zero,add,fn_sum} ([#6350](https://github.com/leanprover-community/mathlib/pull/6350))
This also:
* merges together `smul_apply'` and `smul_apply`, since the latter is just a special case of the former.
* changes the implicitness of arguments to all of the `finsupp.*_apply` lemmas so that all the variables and none of the types are explicit
The whitespace style here matches how `coe_add` is spaced.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.add_apply
- \+/\- *def* finsupp.apply_add_hom
- \+ *lemma* finsupp.coe_nat_sub
- \+ *lemma* finsupp.coe_neg
- \+ *lemma* finsupp.coe_smul
- \+ *lemma* finsupp.coe_sub
- \+/\- *lemma* finsupp.nat_sub_apply
- \+/\- *lemma* finsupp.neg_apply
- \- *lemma* finsupp.smul_apply'
- \+/\- *lemma* finsupp.smul_apply
- \+/\- *lemma* finsupp.sub_apply

Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/comm_ring.lean


Modified src/data/polynomial/coeff.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dual.lean
- \+/\- *def* is_basis.coord_fun
- \- *def* is_basis.eval_finsupp_at



## [2021-02-26 10:06:28](https://github.com/leanprover-community/mathlib/commit/dd5363b)
feat(algebraic_topology): introduce the simplex category ([#6173](https://github.com/leanprover-community/mathlib/pull/6173))
* introduce `simplex_category`, with objects `nat` and morphisms `n ⟶ m` order-preserving maps from `fin (n+1)` to `fin (m+1)`.
* prove the simplicial identities
* show the category is equivalent to `NonemptyFinLinOrd`
This is the start of simplicial sets, moving and completing some of the material from @jcommelin's `sset` branch. Dold-Kan is the obvious objective; apparently we're going to need it for `lean-liquid` at some point.
The proofs of the simplicial identities are bad and slow. They involve extravagant use of nonterminal simp (`simp?` doesn't seem to give good answers) and lots of `linarith` bashing. Help welcome, especially if you love playing with inequalities in `nat` involving lots of `-1`s.
#### Estimated changes
Added src/algebraic_topology/simplex_category.lean
- \+ *lemma* simplex_category.comp_apply
- \+ *lemma* simplex_category.id_apply
- \+ *def* simplex_category.is_skeleton_of
- \+ *def* simplex_category.mk
- \+ *lemma* simplex_category.skeletal
- \+ *def* simplex_category.skeletal_functor
- \+ *def* simplex_category.δ
- \+ *lemma* simplex_category.δ_comp_δ
- \+ *lemma* simplex_category.δ_comp_δ_self
- \+ *lemma* simplex_category.δ_comp_σ_of_gt
- \+ *lemma* simplex_category.δ_comp_σ_of_le
- \+ *lemma* simplex_category.δ_comp_σ_self
- \+ *lemma* simplex_category.δ_comp_σ_succ
- \+ *def* simplex_category.σ
- \+ *lemma* simplex_category.σ_comp_σ
- \+ *def* simplex_category

Modified src/data/fin.lean
- \+ *lemma* fin.pred_mk



## [2021-02-26 07:13:25](https://github.com/leanprover-community/mathlib/commit/2f1de3f)
feat(polynomial/eval): lemmas relating eval/map on numerals ([#6438](https://github.com/leanprover-community/mathlib/pull/6438))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_int_cast_map
- \+ *lemma* polynomial.eval_nat_cast_map
- \+ *lemma* polynomial.eval_one_map
- \+ *lemma* polynomial.eval_zero_map



## [2021-02-26 07:13:24](https://github.com/leanprover-community/mathlib/commit/300e81d)
feat(analysis/complex/basic): complex conjugation is a linear isometry ([#6436](https://github.com/leanprover-community/mathlib/pull/6436))
Complex conjugation is a linear isometry (and various corollaries, eg it is a continuous linear map).
Also rewrite the results that `re` and `im` are continuous linear maps, to deduce from explicit bounds rather than passing through `linear_map.continuous_of_finite_dimensional`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.continuous_conj
- \+ *def* complex.continuous_linear_map.conj
- \+ *lemma* complex.continuous_linear_map.conj_apply
- \+ *lemma* complex.continuous_linear_map.conj_coe
- \+ *lemma* complex.continuous_linear_map.conj_norm
- \+/\- *def* complex.continuous_linear_map.im
- \+/\- *def* complex.continuous_linear_map.re
- \+ *lemma* complex.isometry_conj
- \+ *def* complex.linear_isometry.conj

Modified src/data/complex/module.lean
- \+ *lemma* complex.linear_map.coe_conj
- \+ *def* complex.linear_map.conj



## [2021-02-26 07:13:23](https://github.com/leanprover-community/mathlib/commit/274042d)
feat(data/polynomial): basic lemmas ([#6434](https://github.com/leanprover-community/mathlib/pull/6434))
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.coeff_monomial_succ

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.int_cast_coeff_zero
- \+ *theorem* polynomial.int_cast_inj
- \+ *lemma* polynomial.nat_cast_coeff_zero
- \+ *theorem* polynomial.nat_cast_inj



## [2021-02-26 07:13:22](https://github.com/leanprover-community/mathlib/commit/cca22d7)
feat(data/polynomial/degree/trailing_degree): Trailing degree of multiplication by X^n ([#6425](https://github.com/leanprover-community/mathlib/pull/6425))
A lemma about the trailing degree of a shifted polynomial.
(this PR is part of the irreducibility saga)
#### Estimated changes
Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.nat_trailing_degree_mul_X_pow



## [2021-02-26 07:13:21](https://github.com/leanprover-community/mathlib/commit/24ed74a)
feat(algebra/category/Semigroup/basic): categories of magmas and semigroups ([#6387](https://github.com/leanprover-community/mathlib/pull/6387))
This PR introduces the category of magmas and the category of semigroups, together with their additive versions.
#### Estimated changes
Modified src/algebra/category/Mon/basic.lean
- \- *lemma* mul_equiv.to_CommMon_iso_hom
- \- *lemma* mul_equiv.to_CommMon_iso_inv
- \- *lemma* mul_equiv.to_Mon_iso_hom
- \- *lemma* mul_equiv.to_Mon_iso_inv

Added src/algebra/category/Semigroup/basic.lean
- \+ *lemma* Magma.coe_of
- \+ *def* Magma.of
- \+ *def* Magma
- \+ *lemma* Semigroup.coe_of
- \+ *def* Semigroup.of
- \+ *def* Semigroup
- \+ *def* category_theory.iso.Magma_iso_to_mul_equiv
- \+ *def* category_theory.iso.Semigroup_iso_to_mul_equiv
- \+ *def* mul_equiv.to_Magma_iso
- \+ *def* mul_equiv.to_Semigroup_iso
- \+ *def* mul_equiv_iso_Magma_iso
- \+ *def* mul_equiv_iso_Semigroup_iso

Added src/algebra/pempty_instances.lean




## [2021-02-26 07:13:20](https://github.com/leanprover-community/mathlib/commit/aafa5fe)
feat(ring_theory/flat): definition of flat module ([#6284](https://github.com/leanprover-community/mathlib/pull/6284))
#### Estimated changes
Added src/ring_theory/flat.lean
- \+ *def* module.flat



## [2021-02-26 07:13:19](https://github.com/leanprover-community/mathlib/commit/d451876)
doc(data/finset/basic): rewrite finset module doc ([#5893](https://github.com/leanprover-community/mathlib/pull/5893))
#### Estimated changes
Modified src/data/finset/basic.lean




## [2021-02-26 04:07:32](https://github.com/leanprover-community/mathlib/commit/07d6d3f)
feat(algebra/algebra/basic): smul_mul_smul ([#6423](https://github.com/leanprover-community/mathlib/pull/6423))
An identity for algebras.
(this PR is part of the irreducibility saga)
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.smul_mul_smul



## [2021-02-26 04:07:31](https://github.com/leanprover-community/mathlib/commit/0035e2d)
chore(*): upgrade to Lean 3.27.0c ([#6411](https://github.com/leanprover-community/mathlib/pull/6411))
#### Estimated changes
Modified leanpkg.toml


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/opposites.lean


Modified src/computability/language.lean


Modified src/computability/regular_expressions.lean


Modified src/computability/tm_computable.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/linear_algebra/dual.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/unfold_cases.lean


Modified src/topology/locally_constant/basic.lean


Modified src/topology/omega_complete_partial_order.lean


Modified test/qpf.lean




## [2021-02-26 04:07:31](https://github.com/leanprover-community/mathlib/commit/5fbebf6)
fix(logic/{function}/basic): remove simp lemmas `function.injective.eq_iff` and `imp_iff_right` ([#6402](https://github.com/leanprover-community/mathlib/pull/6402))
* `imp_iff_right` is a conditional simp lemma that matches a lot and should never successfully rewrite.
* `function.injective.eq_iff` is a conditional simp lemma that matches a lot and is rarely used. Since you almost always need to give the proof `hf : function.injective f` as an argument to `simp`, you can replace it with `hf.eq_iff`.
#### Estimated changes
Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/combinatorics/colex.lean


Modified src/combinatorics/hall.lean


Modified src/data/equiv/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/logic/basic.lean
- \+/\- *theorem* imp_iff_right

Modified src/logic/function/basic.lean
- \+/\- *theorem* function.injective.eq_iff

Modified src/order/rel_iso.lean




## [2021-02-26 03:21:37](https://github.com/leanprover-community/mathlib/commit/0938880)
chore(scripts): update nolints.txt ([#6432](https://github.com/leanprover-community/mathlib/pull/6432))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-26 00:42:52](https://github.com/leanprover-community/mathlib/commit/521b821)
feat(data/polynomial/basic): monomial_left_inj ([#6430](https://github.com/leanprover-community/mathlib/pull/6430))
A version of `finsupp.single_left_inj` for monomials, so that it works with `rw.`
(this PR is part of the irreducibility saga)
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.monomial_left_inj



## [2021-02-26 00:42:51](https://github.com/leanprover-community/mathlib/commit/84ca016)
feat(data/polynomial/coeff): Alternate form of coeff_mul_X_pow ([#6424](https://github.com/leanprover-community/mathlib/pull/6424))
An `ite`-version of `coeff_mul_X_pow` that sometimes works better with `rw`.
(this PR is part of the irreducibility saga)
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.coeff_mul_X_pow'



## [2021-02-26 00:42:50](https://github.com/leanprover-community/mathlib/commit/49d2191)
feat(data/polynomial/basic): monomial_neg ([#6422](https://github.com/leanprover-community/mathlib/pull/6422))
The monomial of a negation is the negation of the monomial.
(this PR is part of the irreducibility saga)
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.monomial_neg



## [2021-02-26 00:42:49](https://github.com/leanprover-community/mathlib/commit/f34fa5f)
feat(algebra/algebra/subalgebra): use opt_param for redundant axioms ([#6417](https://github.com/leanprover-community/mathlib/pull/6417))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean




## [2021-02-26 00:42:48](https://github.com/leanprover-community/mathlib/commit/9d5088a)
feat(linear_algebra/pi): add `linear_equiv.pi` ([#6415](https://github.com/leanprover-community/mathlib/pull/6415))
#### Estimated changes
Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.pi



## [2021-02-26 00:42:47](https://github.com/leanprover-community/mathlib/commit/61028ed)
chore(number_theory/bernoulli): use factorial notation ([#6412](https://github.com/leanprover-community/mathlib/pull/6412))
#### Estimated changes
Modified src/number_theory/bernoulli.lean




## [2021-02-26 00:42:46](https://github.com/leanprover-community/mathlib/commit/2755939)
feat(data/pnat/basic): add induction principle ([#6410](https://github.com/leanprover-community/mathlib/pull/6410))
An induction principle for `pnat`.  The proof is by Mario Carneiro.  If there are mistakes, I introduced them!
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/torsion.20free/near/227748865
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *def* pnat.rec_on
- \+ *theorem* pnat.rec_on_one
- \+ *theorem* pnat.rec_on_succ



## [2021-02-26 00:42:45](https://github.com/leanprover-community/mathlib/commit/6ed8b4b)
feat(linear_algebra/finite_dimensional): lemmas for zero dimensional vector spaces ([#6397](https://github.com/leanprover-community/mathlib/pull/6397))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_zero_iff
- \+ *lemma* is_basis_of_dim_eq_zero'
- \+ *lemma* is_basis_of_dim_eq_zero

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_zero_iff_forall_zero
- \+ *lemma* finite_dimensional.findim_zero_iff
- \+ *lemma* finite_dimensional.findim_zero_of_subsingleton
- \+ *lemma* is_basis_of_findim_zero'
- \+ *lemma* is_basis_of_findim_zero



## [2021-02-25 21:38:34](https://github.com/leanprover-community/mathlib/commit/d496676)
feat(geometry/manifold): manifold modelled on locally compact vector space is locally compact ([#6394](https://github.com/leanprover-community/mathlib/pull/6394))
Also connect `locally_compact_space` to `filter.has_basis`.
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* charted_space.locally_compact
- \- *def* charted_space_core.local_homeomorph
- \+ *lemma* mem_chart_target

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners.locally_compact

Modified src/order/filter/bases.lean


Modified src/topology/constructions.lean
- \+ *lemma* filter.has_basis.prod_nhds'

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.symm_map_nhds_eq

Modified src/topology/metric_space/basic.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* compact_basis_nhds
- \+ *lemma* locally_compact_space_of_has_basis

Modified src/topology/uniform_space/basic.lean




## [2021-02-25 21:38:33](https://github.com/leanprover-community/mathlib/commit/8770f5c)
refactor(topology/subset_properties): more properties of `compact_covering` ([#6328](https://github.com/leanprover-community/mathlib/pull/6328))
Modify the definition of `compact_covering α n` to ensure that it is monotone in `n`.
Also, in a locally compact space, prove the existence of a compact exhaustion, i.e. a sequence which satisfies the properties for `compact_covering` and in which, moreover, the interior of the next set includes the previous set.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.find_comp_succ

Modified src/topology/subset_properties.lean
- \+ *lemma* compact_accumulate
- \+ *lemma* compact_covering_subset
- \+ *lemma* compact_exhaustion.Union_eq
- \+ *lemma* compact_exhaustion.exists_mem
- \+ *lemma* compact_exhaustion.find_shiftr
- \+ *lemma* compact_exhaustion.mem_diff_shiftr_find
- \+ *lemma* compact_exhaustion.mem_find
- \+ *lemma* compact_exhaustion.mem_iff_find_le
- \+ *def* compact_exhaustion.shiftr
- \+ *lemma* compact_exhaustion.subset_interior
- \+ *lemma* compact_exhaustion.subset_interior_succ
- \+ *lemma* compact_exhaustion.subset_succ
- \+ *lemma* is_compact.elim_directed_cover



## [2021-02-25 15:43:34](https://github.com/leanprover-community/mathlib/commit/85b5d5c)
refactor(logic/basic): turn *_prop_of_* into congr lemma ([#6406](https://github.com/leanprover-community/mathlib/pull/6406))
Alternative solution to the exists part of [#6404](https://github.com/leanprover-community/mathlib/pull/6404).
#### Estimated changes
Modified src/category_theory/filtered.lean


Modified src/combinatorics/composition.lean


Modified src/data/multiset/pi.lean


Modified src/data/nat/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/vector2.lean


Modified src/logic/basic.lean
- \+ *lemma* exists_false_left
- \+ *lemma* exists_prop_congr'
- \+ *lemma* exists_prop_congr
- \+/\- *theorem* exists_prop_of_false
- \+/\- *theorem* exists_prop_of_true
- \+ *lemma* exists_true_left
- \+ *lemma* forall_false_left
- \+ *lemma* forall_prop_congr'
- \+ *lemma* forall_prop_congr
- \+/\- *theorem* forall_prop_of_false
- \+/\- *theorem* forall_prop_of_true
- \+ *lemma* forall_true_left

Modified src/measure_theory/outer_measure.lean


Modified src/testing/slim_check/gen.lean




## [2021-02-25 09:50:19](https://github.com/leanprover-community/mathlib/commit/e3ae6cd)
feat(data/equiv/basic): lemmas about images and preimages ([#6398](https://github.com/leanprover-community/mathlib/pull/6398))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.eq_preimage_iff_image_eq
- \+ *lemma* equiv.image_eq_iff_eq
- \+ *lemma* equiv.image_subset
- \+ *lemma* equiv.preimage_eq_iff_eq_image
- \+ *lemma* equiv.preimage_subset
- \+ *lemma* equiv.preimage_symm_preimage
- \+ *lemma* equiv.symm_preimage_preimage

Modified src/data/set/basic.lean
- \+ *lemma* set.eq_preimage_iff_image_eq
- \+ *lemma* set.preimage_eq_iff_eq_image



## [2021-02-25 07:29:30](https://github.com/leanprover-community/mathlib/commit/56f2c05)
chore(algebra/regular): rename lemma is_regular_of_cancel_monoid_with_zero to is_regular_of_ne_zero ([#6408](https://github.com/leanprover-community/mathlib/pull/6408))
Change the name of lemma is_regular_of_cancel_monoid_with_zero to the shorter is_regular_of_ne_zero.
Zulip reference:
https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics
#### Estimated changes
Modified src/algebra/regular.lean
- \- *lemma* is_regular_of_cancel_monoid_with_zero
- \+ *lemma* is_regular_of_ne_zero



## [2021-02-25 04:10:42](https://github.com/leanprover-community/mathlib/commit/4b6680a)
chore(scripts): update nolints.txt ([#6407](https://github.com/leanprover-community/mathlib/pull/6407))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-25 04:10:41](https://github.com/leanprover-community/mathlib/commit/caed841)
feat(order/complete_lattice): add complete_lattice.independent.disjoint{_Sup,} ([#6405](https://github.com/leanprover-community/mathlib/pull/6405))
#### Estimated changes
Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* Inf_sup_le_infi_sup
- \+ *lemma* complete_lattice.independent.disjoint
- \+ *lemma* complete_lattice.independent.disjoint_Sup
- \+/\- *theorem* complete_lattice.independent.mono
- \+/\- *def* complete_lattice.independent
- \+/\- *lemma* complete_lattice.independent_empty
- \+ *lemma* disjoint_Sup_left
- \+ *lemma* disjoint_Sup_right
- \+ *lemma* supr_inf_le_Sup_inf

Modified src/order/omega_complete_partial_order.lean




## [2021-02-25 04:10:40](https://github.com/leanprover-community/mathlib/commit/9d748f0)
feat(data/finset/basic): mem_map_equiv ([#6399](https://github.com/leanprover-community/mathlib/pull/6399))
This adds a version of `mem_map` specialized to equivs, which has a better simp-nf.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* equiv.finset_congr_refl
- \+ *lemma* equiv.finset_congr_symm
- \- *lemma* equiv.finset_congr_symm_apply
- \+ *lemma* equiv.finset_congr_trans
- \+ *theorem* finset.mem_map_equiv

Modified src/ring_theory/polynomial/symmetric.lean




## [2021-02-25 04:10:39](https://github.com/leanprover-community/mathlib/commit/eba9be5)
feat(ring_theory/power_series/basic): remove const coeff ([#6383](https://github.com/leanprover-community/mathlib/pull/6383))
This shows that we can factor out X when the constant coefficient is removed from a power series.
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.eq_X_mul_shift_add_const
- \+ *lemma* power_series.eq_shift_mul_X_add_const
- \+ *lemma* power_series.sub_const_eq_X_mul_shift
- \+ *lemma* power_series.sub_const_eq_shift_mul_X



## [2021-02-25 04:10:38](https://github.com/leanprover-community/mathlib/commit/a31d06a)
feat(data/zmod/basic): Explicitly state computable right_inverses instead of just surjectivity ([#5797](https://github.com/leanprover-community/mathlib/pull/5797))
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.int_cast_right_inverse
- \+ *lemma* zmod.nat_cast_right_inverse
- \+ *lemma* zmod.ring_hom_right_inverse
- \+/\- *lemma* zmod.ring_hom_surjective



## [2021-02-25 00:30:10](https://github.com/leanprover-community/mathlib/commit/a518fb8)
feat(data/list/basic): take_init, take_eq_nil ([#6380](https://github.com/leanprover-community/mathlib/pull/6380))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.init_eq_take
- \+ *lemma* list.init_take
- \+ *lemma* list.take_eq_nil_iff



## [2021-02-24 22:06:41](https://github.com/leanprover-community/mathlib/commit/e66e136)
feat(data/mv_polynomial/basic): add two equivs ([#6324](https://github.com/leanprover-community/mathlib/pull/6324))
Two small lemma about `mv_polynomial` as `R`-algebra.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *def* mv_polynomial.alg_equiv_congr
- \+ *def* mv_polynomial.alg_equiv_congr_left
- \+ *def* mv_polynomial.alg_equiv_congr_right
- \- *def* mv_polynomial.alg_equiv_of_equiv
- \+ *def* mv_polynomial.sum_alg_equiv

Modified src/ring_theory/finiteness.lean




## [2021-02-24 21:08:03](https://github.com/leanprover-community/mathlib/commit/ead4731)
feat(geometry/manifold): `model_with_corners` is a `closed_embedding` ([#6393](https://github.com/leanprover-community/mathlib/pull/6393))
#### Estimated changes
Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners.closed_range
- \+ *lemma* model_with_corners.image_mem_nhds_within
- \- *lemma* model_with_corners.left_inv'
- \+ *lemma* model_with_corners.map_nhds_eq
- \+ *lemma* model_with_corners.symm_comp_self
- \+ *lemma* model_with_corners.symm_map_nhds_within_range
- \- *lemma* model_with_corners.target
- \+ *lemma* model_with_corners.target_eq

Modified src/geometry/manifold/times_cont_mdiff.lean




## [2021-02-24 21:08:02](https://github.com/leanprover-community/mathlib/commit/27b6110)
feat(algebra/lie/cartan_subalgebra): define Cartan subalgebras ([#6385](https://github.com/leanprover-community/mathlib/pull/6385))
We do this via the normalizer of a Lie subalgebra, which is also defined here.
#### Estimated changes
Added src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_ideal.normalizer_eq_top
- \+ *lemma* lie_subalgebra.ideal_in_normalizer
- \+ *lemma* lie_subalgebra.le_normalizer
- \+ *lemma* lie_subalgebra.le_normalizer_of_ideal
- \+ *lemma* lie_subalgebra.mem_normalizer_iff
- \+ *def* lie_subalgebra.normalizer

Modified src/algebra/lie/semisimple.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/lie/submodule.lean
- \- *def* lie_algebra.top_equiv_self
- \- *lemma* lie_algebra.top_equiv_self_apply
- \+ *def* lie_ideal.top_equiv_self
- \+ *lemma* lie_ideal.top_equiv_self_apply
- \+ *def* lie_subalgebra.top_equiv_self
- \+ *lemma* lie_subalgebra.top_equiv_self_apply



## [2021-02-24 17:52:02](https://github.com/leanprover-community/mathlib/commit/25ea499)
feat(data/multiset/basic): subsingleton_equiv_apply' ([#6400](https://github.com/leanprover-community/mathlib/pull/6400))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.coe_subsingleton_equiv



## [2021-02-24 17:52:00](https://github.com/leanprover-community/mathlib/commit/6271fe5)
fix(tactic/delta_instance): beta reduce type of instance ([#6396](https://github.com/leanprover-community/mathlib/pull/6396))
The delta derive handler was creating instances that weren't beta reduced, which isn't a problem for type class inference but can be unexpected. @gebner fixed the line in doc-gen that assumed beta reduction, but we should also produce the expected instance in the first place.
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/doc-gen.20is.20failing
#### Estimated changes
Modified src/tactic/delta_instance.lean




## [2021-02-24 15:23:35](https://github.com/leanprover-community/mathlib/commit/3d9e790)
fix(topology/metric_space/cau_seq_filter): remove non-terminal simp ([#6401](https://github.com/leanprover-community/mathlib/pull/6401))
#### Estimated changes
Modified src/topology/metric_space/cau_seq_filter.lean




## [2021-02-24 11:31:20](https://github.com/leanprover-community/mathlib/commit/12afc98)
chore(data/matrix/basic): instances for unique, subsing, nontriv, coe ([#6296](https://github.com/leanprover-community/mathlib/pull/6296))
This adds a coercion to the underlying scalar if the matrix is 1 x 1.
#### Estimated changes
Modified src/data/matrix/basic.lean




## [2021-02-24 09:53:02](https://github.com/leanprover-community/mathlib/commit/85636f9)
feat(data/complex|matrix): instances of star_ordered_ring and star_ordered_algebra ([#4686](https://github.com/leanprover-community/mathlib/pull/4686))
#### Estimated changes
Modified src/analysis/quaternion.lean
- \- *lemma* quaternion.coe_complex_smul
- \+ *lemma* quaternion.coe_real_complex_mul

Modified src/data/complex/basic.lean
- \+ *def* complex.complex_star_ordered_ring

Modified src/data/complex/module.lean
- \+ *lemma* complex.complex_ordered_semimodule
- \- *lemma* complex.im_smul
- \- *lemma* complex.re_smul
- \+ *lemma* complex.smul_coe

Modified src/data/real/basic.lean




## [2021-02-24 06:44:15](https://github.com/leanprover-community/mathlib/commit/196c2a8)
feat(topology/separation): a cont. function with a cont. left inverse is a closed embedding ([#6329](https://github.com/leanprover-community/mathlib/pull/6329))
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+/\- *lemma* tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
- \+ *lemma* tendsto_nhds_within_range

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.image_mem_nhds

Modified src/topology/maps.lean


Modified src/topology/separation.lean
- \+ *lemma* function.left_inverse.closed_embedding
- \+ *lemma* function.left_inverse.closed_range



## [2021-02-24 03:38:57](https://github.com/leanprover-community/mathlib/commit/9bad59c)
chore(scripts): update nolints.txt ([#6389](https://github.com/leanprover-community/mathlib/pull/6389))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-24 03:38:56](https://github.com/leanprover-community/mathlib/commit/4a391c9)
fix(data/int/basic,category_theory/equivalence): use neg not minus in lemma names ([#6384](https://github.com/leanprover-community/mathlib/pull/6384))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/category_theory/equivalence.lean
- \- *lemma* category_theory.equivalence.pow_minus_one
- \+ *lemma* category_theory.equivalence.pow_neg_one

Modified src/data/int/basic.lean
- \- *lemma* int.add_minus_one
- \+ *lemma* int.add_neg_one

Modified src/data/num/lemmas.lean


Modified src/group_theory/free_group.lean




## [2021-02-24 03:38:55](https://github.com/leanprover-community/mathlib/commit/358fdf2)
feat(category_theory/abelian/additive_functor): Adds definition of additive functors ([#6367](https://github.com/leanprover-community/mathlib/pull/6367))
This PR adds the basic definition of an additive functor.
See associated [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20functors/near/227295322).
#### Estimated changes
Added src/category_theory/abelian/additive_functor.lean
- \+ *lemma* category_theory.functor.additive.map_neg
- \+ *lemma* category_theory.functor.additive.map_sub
- \+ *lemma* category_theory.functor.coe_map_add_hom
- \+ *def* category_theory.functor.map_add_hom



## [2021-02-24 00:38:48](https://github.com/leanprover-community/mathlib/commit/b4d2ce4)
chore(data/equiv/local_equiv,topology/local_homeomorph,data/set/function): review ([#6306](https://github.com/leanprover-community/mathlib/pull/6306))
## `data/equiv/local_equiv`:
* move `local_equiv.inj_on` lemmas closer to each other, add missing lemmas;
* rename `local_equiv.bij_on_source` to `local_equiv.bij_on`;
* rename `local_equiv.inv_image_target_eq_souce` to `local_equiv.symm_image_target_eq_souce`;
## `data/set/function`
* add `set.inj_on.mem_of_mem_image`, `set.inj_on.mem_image_iff`, `set.inj_on.preimage_image_inter`;
* add `set.left_inv_on.image_image'` and `set.left_inv_on.image_image`;
* add `function.left_inverse.right_inv_on_range`;
* move `set.inj_on.inv_fun_on_image` to golf the proof;
## `topology/local_homeomorph`
* add lemmas like `local_homeomorph.inj_on`;
* golf the definition of `open_embedding.to_local_homeomorph`, make `f` explicit.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \- *lemma* local_equiv.bij_on_source
- \+/\- *lemma* local_equiv.image_source_eq_target
- \- *lemma* local_equiv.inv_image_target_eq_source
- \+ *lemma* local_equiv.symm_image_target_eq_source

Modified src/data/set/function.lean
- \+ *lemma* function.left_inverse.right_inv_on_range
- \+ *lemma* set.inj_on.mem_image_iff
- \+ *lemma* set.inj_on.mem_of_mem_image
- \+ *lemma* set.inj_on.preimage_image_inter
- \+ *theorem* set.left_inv_on.image_image'
- \+ *theorem* set.left_inv_on.image_image

Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* local_homeomorph.to_open_embedding
- \- *lemma* open_embedding.continuous_inv_fun
- \- *lemma* open_embedding.open_target
- \+/\- *lemma* open_embedding.source
- \+/\- *lemma* open_embedding.target
- \- *lemma* open_embedding.to_local_equiv_coe
- \- *lemma* open_embedding.to_local_equiv_source
- \- *lemma* open_embedding.to_local_equiv_target
- \+/\- *lemma* open_embedding.to_local_homeomorph_coe



## [2021-02-23 21:11:54](https://github.com/leanprover-community/mathlib/commit/387db0d)
feat(data/real/sqrt): add continuity attributes ([#6388](https://github.com/leanprover-community/mathlib/pull/6388))
I add continuity attributes to `continuous_sqrt` and `continuous.sqrt`.
#### Estimated changes
Modified src/data/real/sqrt.lean




## [2021-02-23 21:11:53](https://github.com/leanprover-community/mathlib/commit/8cfada1)
doc(measure_theory/interval_integral): move comment ([#6386](https://github.com/leanprover-community/mathlib/pull/6386))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean




## [2021-02-23 21:11:52](https://github.com/leanprover-community/mathlib/commit/2d51a44)
feat(data/list/basic): nth_drop ([#6381](https://github.com/leanprover-community/mathlib/pull/6381))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.nth_drop



## [2021-02-23 21:11:50](https://github.com/leanprover-community/mathlib/commit/63e7535)
chore(group_theory/coset): right_coset additions and module doc ([#6371](https://github.com/leanprover-community/mathlib/pull/6371))
This PR dualises two results from left_coset to right_coset and adds a module doc.
#### Estimated changes
Modified src/group_theory/coset.lean
- \- *def* left_coset_equiv
- \- *lemma* left_coset_equiv_rel
- \+ *def* left_coset_equivalence
- \+ *lemma* left_coset_equivalence_rel
- \+ *def* quotient_group.right_rel
- \+ *def* right_coset_equivalence
- \+ *lemma* right_coset_equivalence_rel
- \+ *def* subgroup.right_coset_equiv_subgroup



## [2021-02-23 17:14:41](https://github.com/leanprover-community/mathlib/commit/750d117)
feat(logic/basic): subsingleton_iff_forall_eq ([#6379](https://github.com/leanprover-community/mathlib/pull/6379))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* subsingleton_iff_forall_eq



## [2021-02-23 17:14:40](https://github.com/leanprover-community/mathlib/commit/59bf982)
feat(algebra/lie/nilpotent): basic facts about nilpotent Lie algebras ([#6378](https://github.com/leanprover-community/mathlib/pull/6378))
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_ideal.map_bracket_eq

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* function.injective.lie_algebra_is_nilpotent
- \+ *lemma* function.surjective.lie_algebra_is_nilpotent
- \+ *lemma* lie_algebra.nilpotent_iff_equiv_nilpotent
- \+ *lemma* lie_ideal.lower_central_series_map_eq
- \+ *lemma* lie_ideal.lower_central_series_map_le

Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.sub_mem

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_hom.ideal_range_eq_top_of_surjective
- \+ *lemma* lie_hom.is_ideal_morphism_of_surjective
- \+ *lemma* lie_hom.range_coe_submodule
- \+ *lemma* lie_hom.range_eq_top
- \+ *lemma* lie_ideal.coe_map_of_surjective
- \+/\- *lemma* lie_ideal.map_sup_ker_eq_map
- \+ *lemma* lie_ideal.mem_map_of_surjective
- \+ *lemma* lie_ideal.top_coe_lie_subalgebra



## [2021-02-23 17:14:39](https://github.com/leanprover-community/mathlib/commit/4b22c39)
feat(ring_theory/power_series/well_known): sum of power of exponentials ([#6368](https://github.com/leanprover-community/mathlib/pull/6368))
#### Estimated changes
Modified src/ring_theory/power_series/well_known.lean
- \+ *theorem* power_series.exp_pow_sum



## [2021-02-23 17:14:38](https://github.com/leanprover-community/mathlib/commit/e3d6cf8)
feat(measure_theory/integration): add theorems about the product of independent random variables ([#6106](https://github.com/leanprover-community/mathlib/pull/6106))
Consider the integral of the product of two random variables. Two random variables are independent if the preimage of all measurable sets are independent variables. Alternatively, if there is a pair of independent measurable spaces (as sigma algebras are independent), then two random variables are independent if they are measurable with respect to them.
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* set.inter_indicator_mul

Modified src/probability_theory/independence.lean
- \+/\- *def* probability_theory.indep_set

Added src/probability_theory/integration.lean
- \+ *lemma* probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
- \+ *lemma* probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
- \+ *lemma* probability_theory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator



## [2021-02-23 14:09:45](https://github.com/leanprover-community/mathlib/commit/f84f5b2)
feat(category_theory/subobject): the semilattice_inf/sup of subobjects ([#6278](https://github.com/leanprover-community/mathlib/pull/6278))
# The lattice of subobjects
We define `subobject X` as the quotient (by isomorphisms) of
`mono_over X := {f : over X // mono f.hom}`.
Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.
We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : subobject Y ⥤ subobject X`
* `def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : subobject X ⥤ subobject Y`
(each first at the level of `mono_over`), and prove their basic properties and relationships.
We also provide the `semilattice_inf_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_inf (subobject X)` instance when `[has_images C] [has_finite_coproducts C]`.
## Notes
This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.
#### Estimated changes
Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/functor.lean
- \+ *lemma* category_theory.functor.monotone

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/over.lean
- \+ *def* category_theory.over.map_pullback_adj
- \+ *def* category_theory.over.pullback
- \+ *def* category_theory.over.pullback_comp
- \+ *def* category_theory.over.pullback_id
- \+ *def* category_theory.under.pushout

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.over.coprod
- \+ *def* category_theory.over.coprod_obj

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* category_theory.limits.pullback_cone.mono_of_is_limit_mk_id_id

Modified src/category_theory/over.lean
- \+/\- *lemma* category_theory.under.w

Modified src/category_theory/skeletal.lean
- \+/\- *lemma* category_theory.thin_skeleton.comp_to_thin_skeleton
- \+ *def* category_theory.thin_skeleton.lower_adjunction

Added src/category_theory/subobject.lean
- \+ *lemma* category_theory.mono_over.bot_arrow
- \+ *def* category_theory.mono_over.bot_le
- \+ *lemma* category_theory.mono_over.bot_left
- \+ *def* category_theory.mono_over.exists_iso_map
- \+ *def* category_theory.mono_over.exists_pullback_adj
- \+ *def* category_theory.mono_over.forget
- \+ *def* category_theory.mono_over.forget_image
- \+ *lemma* category_theory.mono_over.forget_obj_hom
- \+ *lemma* category_theory.mono_over.forget_obj_left
- \+ *def* category_theory.mono_over.image
- \+ *def* category_theory.mono_over.image_forget_adj
- \+ *def* category_theory.mono_over.inf
- \+ *def* category_theory.mono_over.inf_le_left
- \+ *def* category_theory.mono_over.inf_le_right
- \+ *def* category_theory.mono_over.iso_mk
- \+ *def* category_theory.mono_over.le_inf
- \+ *def* category_theory.mono_over.le_sup_left
- \+ *def* category_theory.mono_over.le_sup_right
- \+ *def* category_theory.mono_over.le_top
- \+ *def* category_theory.mono_over.lift
- \+ *lemma* category_theory.mono_over.lift_comm
- \+ *def* category_theory.mono_over.lift_comp
- \+ *def* category_theory.mono_over.lift_id
- \+ *def* category_theory.mono_over.lift_iso
- \+ *def* category_theory.mono_over.map
- \+ *def* category_theory.mono_over.map_bot
- \+ *def* category_theory.mono_over.map_comp
- \+ *def* category_theory.mono_over.map_id
- \+ *def* category_theory.mono_over.map_iso
- \+ *lemma* category_theory.mono_over.map_obj_arrow
- \+ *lemma* category_theory.mono_over.map_obj_left
- \+ *def* category_theory.mono_over.map_pullback_adj
- \+ *def* category_theory.mono_over.map_top
- \+ *def* category_theory.mono_over.mk'
- \+ *lemma* category_theory.mono_over.mk'_arrow
- \+ *def* category_theory.mono_over.pullback
- \+ *def* category_theory.mono_over.pullback_comp
- \+ *def* category_theory.mono_over.pullback_id
- \+ *def* category_theory.mono_over.pullback_map_self
- \+ *lemma* category_theory.mono_over.pullback_obj_arrow
- \+ *lemma* category_theory.mono_over.pullback_obj_left
- \+ *def* category_theory.mono_over.pullback_self
- \+ *def* category_theory.mono_over.pullback_top
- \+ *def* category_theory.mono_over.slice
- \+ *def* category_theory.mono_over.sup
- \+ *def* category_theory.mono_over.sup_le
- \+ *lemma* category_theory.mono_over.top_arrow
- \+ *def* category_theory.mono_over.top_le_pullback_self
- \+ *lemma* category_theory.mono_over.top_left
- \+ *lemma* category_theory.mono_over.w
- \+ *def* category_theory.mono_over.«exists»
- \+ *def* category_theory.mono_over
- \+ *lemma* category_theory.subobject.bot_eq_zero
- \+ *lemma* category_theory.subobject.exists_iso_map
- \+ *def* category_theory.subobject.exists_pullback_adj
- \+ *def* category_theory.subobject.functor
- \+ *def* category_theory.subobject.inf
- \+ *lemma* category_theory.subobject.inf_def
- \+ *lemma* category_theory.subobject.inf_eq_map_pullback'
- \+ *lemma* category_theory.subobject.inf_eq_map_pullback
- \+ *lemma* category_theory.subobject.inf_le_left
- \+ *lemma* category_theory.subobject.inf_le_right
- \+ *lemma* category_theory.subobject.inf_map
- \+ *lemma* category_theory.subobject.inf_pullback
- \+ *lemma* category_theory.subobject.le_inf
- \+ *def* category_theory.subobject.lower
- \+ *def* category_theory.subobject.lower_adjunction
- \+ *lemma* category_theory.subobject.lower_comm
- \+ *def* category_theory.subobject.lower_equivalence
- \+ *lemma* category_theory.subobject.lower_iso
- \+ *def* category_theory.subobject.lower₂
- \+ *def* category_theory.subobject.map
- \+ *lemma* category_theory.subobject.map_bot
- \+ *lemma* category_theory.subobject.map_comp
- \+ *lemma* category_theory.subobject.map_id
- \+ *def* category_theory.subobject.map_iso
- \+ *def* category_theory.subobject.map_iso_to_order_iso
- \+ *lemma* category_theory.subobject.map_iso_to_order_iso_apply
- \+ *lemma* category_theory.subobject.map_iso_to_order_iso_symm_apply
- \+ *lemma* category_theory.subobject.map_pullback
- \+ *def* category_theory.subobject.map_pullback_adj
- \+ *lemma* category_theory.subobject.map_top
- \+ *lemma* category_theory.subobject.prod_eq_inf
- \+ *def* category_theory.subobject.pullback
- \+ *lemma* category_theory.subobject.pullback_comp
- \+ *lemma* category_theory.subobject.pullback_id
- \+ *lemma* category_theory.subobject.pullback_map_self
- \+ *lemma* category_theory.subobject.pullback_self
- \+ *lemma* category_theory.subobject.pullback_top
- \+ *def* category_theory.subobject.sup
- \+ *lemma* category_theory.subobject.top_eq_id
- \+ *def* category_theory.subobject.«exists»
- \+ *def* category_theory.subobject



## [2021-02-23 14:09:44](https://github.com/leanprover-community/mathlib/commit/7f46c81)
feat(chain_complex): lemmas about eq_to_hom ([#6250](https://github.com/leanprover-community/mathlib/pull/6250))
Adds two lemmas relating `eq_to_hom` to differentials and chain maps. Useful in the ubiquitous circumstance of having to apply identities in the index of a chain complex.
Also add some `@[reassoc]` tags for convenience.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean
- \+ *lemma* homological_complex.eq_to_hom_d
- \+ *lemma* homological_complex.eq_to_hom_f



## [2021-02-23 14:09:43](https://github.com/leanprover-community/mathlib/commit/8d3efb7)
feat(data/buffer/basic): read and to_buffer lemmas ([#6048](https://github.com/leanprover-community/mathlib/pull/6048))
#### Estimated changes
Modified src/data/array/lemmas.lean
- \+ *lemma* array.read_push_back_left
- \+ *lemma* array.read_push_back_right

Modified src/data/buffer/basic.lean
- \+ *lemma* buffer.append_list_nil
- \+ *lemma* buffer.length_to_list
- \+ *lemma* buffer.read_append_list_left'
- \+ *lemma* buffer.read_append_list_left
- \+ *lemma* buffer.read_append_list_right
- \+ *lemma* buffer.read_push_back_left
- \+ *lemma* buffer.read_push_back_right
- \+ *lemma* buffer.read_singleton
- \+ *lemma* buffer.read_to_buffer'
- \+ *lemma* buffer.read_to_buffer
- \+ *lemma* buffer.size_append_list
- \+ *lemma* buffer.size_push_back
- \+ *lemma* buffer.size_singleton
- \+ *lemma* buffer.size_to_buffer
- \+ *lemma* buffer.to_buffer_cons
- \+ *lemma* buffer.to_buffer_to_list
- \+ *lemma* buffer.to_list_to_buffer



## [2021-02-23 10:52:40](https://github.com/leanprover-community/mathlib/commit/391c90a)
feat(logic/basic): subsingleton_of_forall_eq ([#6376](https://github.com/leanprover-community/mathlib/pull/6376))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* subsingleton_of_forall_eq

Modified src/logic/unique.lean




## [2021-02-23 10:52:39](https://github.com/leanprover-community/mathlib/commit/e6d23d2)
feat(ring_theory/power_series/basic): coeff_succ_X_mul ([#6370](https://github.com/leanprover-community/mathlib/pull/6370))
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.coeff_succ_X_mul



## [2021-02-23 09:46:58](https://github.com/leanprover-community/mathlib/commit/3ff9248)
feat({group,ring}_theory/free_*): make free_ring.lift and free_comm_ring.lift equivs ([#6364](https://github.com/leanprover-community/mathlib/pull/6364))
This also adds `free_ring.hom_ext` and `free_comm_ring.hom_ext`, and deduplicates the definitions of the two lifts by introducing `abelian_group.lift_monoid`.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *def* free_abelian_group.lift_monoid
- \+ *lemma* free_abelian_group.lift_monoid_coe
- \+ *lemma* free_abelian_group.lift_monoid_coe_add_monoid_hom
- \+ *lemma* free_abelian_group.lift_monoid_symm_coe
- \+/\- *lemma* free_abelian_group.mul_def
- \+/\- *lemma* free_abelian_group.of_mul
- \+ *def* free_abelian_group.of_mul_hom
- \+ *lemma* free_abelian_group.of_mul_hom_coe
- \+/\- *lemma* free_abelian_group.of_mul_of
- \+/\- *lemma* free_abelian_group.of_one
- \+/\- *lemma* free_abelian_group.one_def

Modified src/ring_theory/free_comm_ring.lean
- \+ *lemma* free_comm_ring.hom_ext
- \+/\- *def* free_comm_ring.lift

Modified src/ring_theory/free_ring.lean
- \+ *lemma* free_ring.hom_ext
- \+/\- *def* free_ring.lift



## [2021-02-23 06:48:15](https://github.com/leanprover-community/mathlib/commit/b7a7b3d)
feat(algebra/regular): lemmas for powers of regular elements ([#6356](https://github.com/leanprover-community/mathlib/pull/6356))
Prove that an element is (left/right-)regular iff a power of it is (left/right-)regular.
#### Estimated changes
Modified src/algebra/regular.lean
- \+ *lemma* is_left_regular.pow
- \+ *lemma* is_left_regular.pow_iff
- \+ *lemma* is_regular.pow
- \+ *lemma* is_regular.pow_iff
- \+ *lemma* is_right_regular.pow
- \+ *lemma* is_right_regular.pow_iff



## [2021-02-23 06:48:15](https://github.com/leanprover-community/mathlib/commit/ec36fc0)
fix(data/set/finite): add decidable assumptions ([#6264](https://github.com/leanprover-community/mathlib/pull/6264))
Yury's rule of thumb https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/classicalize/near/224871122 says that we should have decidable instances here, because the statements of the lemmas need them (rather than the proofs). I'm making this PR to see if anything breaks.
#### Estimated changes
Modified src/data/set/finite.lean
- \+/\- *lemma* set.card_ne_eq
- \+/\- *lemma* set.to_finset_compl
- \+/\- *lemma* set.to_finset_inter
- \+/\- *lemma* set.to_finset_ne_eq_erase
- \+/\- *lemma* set.to_finset_union



## [2021-02-23 06:48:14](https://github.com/leanprover-community/mathlib/commit/680e8ed)
feat(order/well_founded_set): defining `is_partially_well_ordered` to prove `is_wf.add` ([#6226](https://github.com/leanprover-community/mathlib/pull/6226))
Defines `set.is_partially_well_ordered s`, equivalent to any infinite sequence to `s` contains an infinite monotone subsequence
Provides a basic API for `set.is_partially_well_ordered`
Proves `is_wf.add` and `is_wf.mul`
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *theorem* finset.is_wf_support_mul_antidiagonal
- \+ *lemma* finset.mul_antidiagonal_mono_left
- \+ *lemma* finset.mul_antidiagonal_mono_right
- \+ *lemma* finset.support_mul_antidiagonal_subset_mul
- \+ *theorem* set.is_partially_well_ordered.exists_monotone_subseq
- \+ *theorem* set.is_partially_well_ordered.image_of_monotone
- \+ *lemma* set.is_partially_well_ordered.is_wf
- \+ *theorem* set.is_partially_well_ordered.mul
- \+ *lemma* set.is_partially_well_ordered.prod
- \+ *def* set.is_partially_well_ordered
- \+ *theorem* set.is_partially_well_ordered_iff_exists_monotone_subseq
- \+/\- *theorem* set.is_wf.insert
- \+ *theorem* set.is_wf.is_partially_well_ordered
- \+ *theorem* set.is_wf.mul
- \+ *theorem* set.is_wf_empty
- \+/\- *theorem* set.is_wf_singleton



## [2021-02-23 05:21:51](https://github.com/leanprover-community/mathlib/commit/5931c5c)
lint(set_theory/ordinal): fix def/lemma ([#6369](https://github.com/leanprover-community/mathlib/pull/6369))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *lemma* cardinal.ord_eq_min
- \- *def* cardinal.ord_eq_min



## [2021-02-23 01:14:10](https://github.com/leanprover-community/mathlib/commit/3c66fd1)
chore(scripts): update nolints.txt ([#6373](https://github.com/leanprover-community/mathlib/pull/6373))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-02-22 21:32:01](https://github.com/leanprover-community/mathlib/commit/7a91822)
feat(data/fintype/intervals): Add set.finite lemmas for integer intervals ([#6365](https://github.com/leanprover-community/mathlib/pull/6365))
#### Estimated changes
Modified src/data/fintype/intervals.lean
- \+ *lemma* set.Icc_ℤ_finite
- \+ *lemma* set.Ico_ℤ_finite
- \+ *lemma* set.Ioc_ℤ_finite
- \+ *lemma* set.Ioo_ℤ_finite



## [2021-02-22 21:32:00](https://github.com/leanprover-community/mathlib/commit/c038984)
chore(data/equiv/*): add missing coercion lemmas for equivs ([#6268](https://github.com/leanprover-community/mathlib/pull/6268))
This does not affect the simp-normal form.
This tries to make a lot of lemma names and statements more consistent:
* restates `linear_map.mk_apply` to be `linear_map.coe_mk` to match `monoid_hom.coe_mk`
* adds `linear_map.to_linear_map_eq_coe`
* adds the simp lemma `linear_map.coe_to_equiv`
* adds the simp lemma `linear_map.linear_map.coe_to_linear_map`
* adds the simp lemma `linear_map.to_fun_eq_coe`
* adds the missing `ancestor` attributes required to make `to_additive` work for things like `add_equiv.to_add_hom`
* restates `add_equiv.to_fun_apply` to be `add_equiv.to_fun_eq_coe`
* restates `add_equiv.to_equiv_apply` to be `add_equiv.coe_to_equiv`
* adds the simp lemma `add_equiv.coe_to_mul_hom`
* removes `add_equiv.to_add_monoid_hom_apply` since `add_equiv.coe_to_add_monoid_hom` is a shorter and more general statement
* restates `ring_equiv.to_fun_apply` to be `ring_equiv.to_fun_eq_coe`
* restates `ring_equiv.coe_mul_equiv` to be `ring_equiv.coe_to_mul_equiv`
* restates `ring_equiv.coe_add_equiv` to be `ring_equiv.coe_to_add_equiv`
* restates `ring_equiv.coe_ring_hom` to be `ring_equiv.coe_to_ring_hom`
* adds `ring_equiv.to_ring_hom_eq_coe`
* adds `ring_equiv.to_add_equiv_eq_coe`
* adds `ring_equiv.to_mul_equiv_eq_coe`
#### Estimated changes
Modified src/algebra/group/hom.lean


Modified src/algebra/lie/matrix.lean


Modified src/algebra/module/linear_map.lean
- \+/\- *theorem* linear_equiv.coe_coe
- \+ *lemma* linear_equiv.coe_mk
- \+/\- *lemma* linear_equiv.coe_to_equiv
- \+ *lemma* linear_equiv.coe_to_linear_map
- \- *lemma* linear_equiv.mk_apply
- \- *lemma* linear_equiv.to_fun_apply
- \+ *lemma* linear_equiv.to_fun_eq_coe
- \+ *lemma* linear_equiv.to_linear_map_eq_coe

Modified src/algebra/quandle.lean


Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.coe_to_equiv
- \+ *lemma* mul_equiv.coe_to_mul_hom
- \- *lemma* mul_equiv.to_equiv_apply
- \- *lemma* mul_equiv.to_fun_apply
- \+ *lemma* mul_equiv.to_fun_eq_coe
- \- *lemma* mul_equiv.to_monoid_hom_apply

Modified src/data/equiv/ring.lean
- \- *lemma* ring_equiv.coe_add_equiv
- \- *lemma* ring_equiv.coe_mul_equiv
- \- *lemma* ring_equiv.coe_ring_hom
- \+ *lemma* ring_equiv.coe_to_add_equiv
- \+ *lemma* ring_equiv.coe_to_mul_equiv
- \+ *lemma* ring_equiv.coe_to_ring_hom
- \+ *lemma* ring_equiv.to_add_equiv_eq_coe
- \+ *lemma* ring_equiv.to_fun_eq_coe
- \- *lemma* ring_equiv.to_fun_eq_coe_fun
- \+ *lemma* ring_equiv.to_mul_equiv_eq_coe
- \+ *lemma* ring_equiv.to_ring_hom_eq_coe

Modified src/data/mv_polynomial/equiv.lean


Modified src/group_theory/semidirect_product.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/witt_vector/is_poly.lean




## [2021-02-22 18:48:55](https://github.com/leanprover-community/mathlib/commit/283aaff)
feat(ring_theory/power_series/well_known): power of exponential ([#6330](https://github.com/leanprover-community/mathlib/pull/6330))
Co-authored by Fabian Kruse
#### Estimated changes
Modified src/ring_theory/power_series/well_known.lean
- \+ *theorem* power_series.exp_pow_eq_rescale_exp



## [2021-02-22 18:48:54](https://github.com/leanprover-community/mathlib/commit/0fb6ada)
chore(topology): move `exists_compact_superset`, drop assumption `t2_space` ([#6327](https://github.com/leanprover-community/mathlib/pull/6327))
Also golf the proof of `is_compact.elim_finite_subcover_image`
#### Estimated changes
Modified src/topology/separation.lean
- \- *lemma* exists_compact_superset

Modified src/topology/subset_properties.lean
- \+ *lemma* exists_compact_superset
- \+ *lemma* finset.compact_bUnion



## [2021-02-22 18:48:53](https://github.com/leanprover-community/mathlib/commit/db00ee4)
feat(ring_theory/polynomial/basic): add quotient_equiv_quotient_mv_polynomial ([#6287](https://github.com/leanprover-community/mathlib/pull/6287))
I've added `quotient_equiv_quotient_mv_polynomial` that says that `(R/I)[x_i] ≃+* (R[x_i])/I` where `I` is an ideal of `R`. I've included also a version for `R`-algebras. The proof is very similar to the case of (one variable) polynomials.
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* mv_polynomial.eval₂_C_mk_eq_zero
- \+ *lemma* mv_polynomial.mem_ideal_of_coeff_mem_ideal
- \+ *theorem* mv_polynomial.mem_map_C_iff
- \+ *def* mv_polynomial.quotient_alg_equiv_quotient_mv_polynomial
- \+ *def* mv_polynomial.quotient_equiv_quotient_mv_polynomial
- \+ *lemma* mv_polynomial.quotient_map_C_eq_zero



## [2021-02-22 18:48:52](https://github.com/leanprover-community/mathlib/commit/cc9d3ab)
feat(algebra/module,linear_algebra): generalize `smul_eq_zero` ([#6199](https://github.com/leanprover-community/mathlib/pull/6199))
Moves the theorem on division rings `smul_eq_zero` to a typeclass `no_zero_smul_divisors` with instances for the previously existing cases. The motivation for this change is that [#6178](https://github.com/leanprover-community/mathlib/pull/6178) added another `smul_eq_zero`, which could be captured neatly as an instance of the typeclass.
I didn't spend a lot of time yet on figuring out all the necessary instances, first let's see whether this compiles.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.no_zero_smul_divisors.of_algebra_map_injective

Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/module/basic.lean
- \+/\- *lemma* eq_zero_of_eq_neg
- \+/\- *lemma* eq_zero_of_smul_two_eq_zero
- \+ *lemma* nat.no_zero_smul_divisors
- \+/\- *lemma* ne_neg_of_ne_zero
- \+/\- *theorem* smul_eq_zero
- \- *lemma* smul_nat_eq_zero

Modified src/algebra/module/pi.lean


Modified src/algebra/module/prod.lean


Modified src/algebra/module/submodule.lean


Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/alternating.lean




## [2021-02-22 17:14:14](https://github.com/leanprover-community/mathlib/commit/7abfbc9)
doc(references.bib): add witt vector references and normalize ([#6366](https://github.com/leanprover-community/mathlib/pull/6366))
Now that we're actually displaying these bib links we should pay more attention to them.
Two commits: one adds references for the Witt vector files, the other normalizes the bib file. We can drop the second if people don't care.
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/witt_vector/basic.lean


Modified src/ring_theory/witt_vector/compare.lean


Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/identities.lean


Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/mul_p.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean


Modified src/ring_theory/witt_vector/teichmuller.lean


Modified src/ring_theory/witt_vector/truncated.lean


Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-02-22 17:14:13](https://github.com/leanprover-community/mathlib/commit/70d7114)
feat(nat/choose): lemmas regarding binomial coefficients ([#6362](https://github.com/leanprover-community/mathlib/pull/6362))
#### Estimated changes
Modified src/data/nat/choose/dvd.lean
- \+ *lemma* nat.prime.choose_eq_factorial_div_factorial'
- \+ *lemma* nat.prime.choose_mul



## [2021-02-22 17:14:10](https://github.com/leanprover-community/mathlib/commit/4daac66)
chore(field_theory/mv_polynomial): generalised to comm_ring and module doc ([#6341](https://github.com/leanprover-community/mathlib/pull/6341))
This PR generalises most of `field_theory/mv_polynomial` from polynomial rings over fields to polynomial rings over commutative rings. This is put into a separate file. 
Also renamed the field to K and did one tiny golf.
#### Estimated changes
Modified src/field_theory/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.dim_mv_polynomial
- \- *lemma* mv_polynomial.is_basis_monomials
- \- *lemma* mv_polynomial.map_range_eq_map
- \- *lemma* mv_polynomial.mem_restrict_degree
- \- *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \- *lemma* mv_polynomial.mem_restrict_total_degree
- \+/\- *lemma* mv_polynomial.quotient_mk_comp_C_injective
- \- *def* mv_polynomial.restrict_degree
- \- *def* mv_polynomial.restrict_total_degree

Added src/ring_theory/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.is_basis_monomials
- \+ *lemma* mv_polynomial.map_range_eq_map
- \+ *lemma* mv_polynomial.mem_restrict_degree
- \+ *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \+ *lemma* mv_polynomial.mem_restrict_total_degree
- \+ *def* mv_polynomial.restrict_degree
- \+ *def* mv_polynomial.restrict_total_degree



## [2021-02-22 14:12:42](https://github.com/leanprover-community/mathlib/commit/6d2726c)
feat(number_theory/bernoulli): definition and properties of Bernoulli numbers ([#6363](https://github.com/leanprover-community/mathlib/pull/6363))
#### Estimated changes
Modified src/number_theory/bernoulli.lean
- \+ *def* bernoulli'
- \+ *lemma* bernoulli'_def'
- \+ *lemma* bernoulli'_def
- \+ *lemma* bernoulli'_four
- \+ *theorem* bernoulli'_odd_eq_zero
- \+ *lemma* bernoulli'_one
- \+ *theorem* bernoulli'_power_series
- \+ *lemma* bernoulli'_spec'
- \+ *lemma* bernoulli'_spec
- \+ *lemma* bernoulli'_three
- \+ *lemma* bernoulli'_two
- \+ *lemma* bernoulli'_zero
- \+/\- *def* bernoulli
- \- *lemma* bernoulli_def'
- \- *lemma* bernoulli_def
- \+ *theorem* bernoulli_eq_bernoulli'
- \- *lemma* bernoulli_four
- \- *theorem* bernoulli_odd_eq_zero
- \+/\- *lemma* bernoulli_one
- \- *theorem* bernoulli_power_series
- \- *lemma* bernoulli_spec'
- \- *lemma* bernoulli_spec
- \- *lemma* bernoulli_three
- \- *lemma* bernoulli_two
- \+/\- *lemma* bernoulli_zero
- \+ *lemma* sum_bernoulli'
- \+ *theorem* sum_bernoulli
- \- *lemma* sum_bernoulli



## [2021-02-22 14:12:41](https://github.com/leanprover-community/mathlib/commit/46fb0d8)
feat(big_operators/intervals): lemma on dependent double sum ([#6361](https://github.com/leanprover-community/mathlib/pull/6361))
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+ *lemma* finset.sum_Ico_Ico_comm



## [2021-02-22 14:12:40](https://github.com/leanprover-community/mathlib/commit/12bb9ae)
chore(linear_algebra/*): split lines and doc `direct_sum/tensor_product` ([#6360](https://github.com/leanprover-community/mathlib/pull/6360))
This PR provides a short module doc to `direct_sum/tensor_product` (the file contains only one result). Furthermore, it splits lines in the `linear_algebra` folder.
#### Estimated changes
Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/char_poly/coeff.lean
- \+/\- *lemma* finite_field.trace_pow_card

Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/direct_sum/finsupp.lean


Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *theorem* linear_map.trace_eq_matrix_trace

Modified src/linear_algebra/special_linear_group.lean




## [2021-02-22 14:12:39](https://github.com/leanprover-community/mathlib/commit/a10c19d)
doc(group_theory/*): module docs for `quotient_group` and `presented_group` ([#6358](https://github.com/leanprover-community/mathlib/pull/6358))
#### Estimated changes
Modified src/group_theory/presented_group.lean
- \+/\- *theorem* presented_group.to_group.unique
- \+/\- *def* presented_group.to_group

Modified src/group_theory/quotient_group.lean




## [2021-02-22 14:12:38](https://github.com/leanprover-community/mathlib/commit/590442a)
feat(topology/subset_properties): locally finite family on a compact space is finite ([#6352](https://github.com/leanprover-community/mathlib/pull/6352))
#### Estimated changes
Modified src/data/set/finite.lean
- \- *def* set.fintype_of_univ_finite

Modified src/topology/basic.lean
- \- *lemma* locally_finite_of_finite
- \+ *lemma* locally_finite_of_fintype

Modified src/topology/subset_properties.lean
- \+ *lemma* finite_cover_nhds
- \+ *lemma* finite_cover_nhds_interior
- \+ *lemma* locally_finite.finite_nonempty_of_compact
- \+ *lemma* locally_finite.finite_of_compact



## [2021-02-22 14:12:37](https://github.com/leanprover-community/mathlib/commit/120feb1)
refactor(order/filter,topology): review API ([#6347](https://github.com/leanprover-community/mathlib/pull/6347))
### Filters
* move old `filter.map_comap` to `filter.map_comap_of_mem`;
* add a new `filter.map_comap` that doesn't assume `range m ∈ f` but
  gives `map m (comap m f) = f ⊓ 𝓟 (range m)` instead of
  `map m (comap m f) = f`;
* add `filter.comap_le_comap_iff`, use it to golf a couple of proofs;
* move some lemmas using `filter.map_comap`/`filter.map_comap_of_mem`
  closure to these lemmas;
* use `function.injective m` instead of `∀ x y, m x = m y → x = y` in
  some lemmas;
* drop `filter.le_map_comap_of_surjective'`,
  `filter.map_comap_of_surjective'`, and
  `filter.le_map_comap_of_surjective`: the inequalities easily follow
  from equalities, and `filter.map_comap_of_surjective'` is just
  `filter.map_comap_of_mem`+`filter.mem_sets_of_superset`;
### Topology
* add `closed_embedding_subtype_coe`, `ennreal.open_embedding_coe`;
* drop `inducing_open`, `inducing_is_closed`, `embedding_open`, and
  `embedding_is_closed` replace them with `inducing.is_open_map` and
  `inducing.is_closed_map`;
* move old `inducing.map_nhds_eq` to `inducing.map_nhds_of_mem`, the
  new `inducing.map_nhds_eq` says `map f (𝓝 a) = 𝓝[range f] (f a)`;
* add `inducing.is_closed_iff`;
* move old `embedding.map_nhds_eq` to `embedding.map_nhds_of_mem`, the
  new `embedding.map_nhds_eq` says `map f (𝓝 a) = 𝓝[range f] (f a)`;
* add `open_embedding.map_nhds_eq`;
* change signature of `is_closed_induced_iff` to match other similar
  lemmas;
* move old `map_nhds_induced_eq` to `map_nhds_induced_of_mem`, the new
  `map_nhds_induced_eq` give `𝓝[range f] (f a)` instead of `𝓝 (f a)`.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_le_comap_iff
- \- *theorem* filter.le_map_comap_of_surjective'
- \- *theorem* filter.le_map_comap_of_surjective
- \+/\- *lemma* filter.map_comap
- \+ *lemma* filter.map_comap_of_mem
- \- *theorem* filter.map_comap_of_surjective'
- \+/\- *lemma* filter.map_inj

Modified src/topology/algebra/ordered.lean


Modified src/topology/constructions.lean
- \+ *lemma* closed_embedding_subtype_coe

Modified src/topology/continuous_on.lean


Modified src/topology/homeomorph.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.nhds_coe_coe
- \+ *lemma* ennreal.open_embedding_coe
- \+/\- *lemma* ennreal.tendsto_to_nnreal
- \+/\- *lemma* ennreal.tendsto_to_real

Modified src/topology/maps.lean
- \+/\- *lemma* embedding.map_nhds_eq
- \+ *lemma* embedding.map_nhds_of_mem
- \- *lemma* embedding_is_closed
- \- *lemma* embedding_open
- \+ *lemma* inducing.is_closed_iff
- \+ *lemma* inducing.is_closed_map
- \+ *lemma* inducing.is_open_map
- \+/\- *lemma* inducing.map_nhds_eq
- \+ *lemma* inducing.map_nhds_of_mem
- \- *lemma* inducing_is_closed
- \- *lemma* inducing_open
- \+ *lemma* open_embedding.map_nhds_eq

Modified src/topology/order.lean
- \+/\- *lemma* map_nhds_induced_eq
- \+ *lemma* map_nhds_induced_of_mem

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-02-22 14:12:36](https://github.com/leanprover-community/mathlib/commit/26e6d4c)
feat(algebra/lie/{subalgebra,submodule}): grab bag of new lemmas ([#6342](https://github.com/leanprover-community/mathlib/pull/6342))
I'm splitting these off from other work to simplify subsequent reviews.
Cosmetic changes aside, the following summarises what I am proposing:
New definitions:
 - `lie_subalgebra.of_le`
Definition tweaks:
 - `lie_hom.range` [use coercion instead of `lie_hom.to_linear_map`]
 - `lie_ideal.map` [factor through `submodule.map` to avoid dropping all the way down to `set.image`]
New lemmas:
 - `lie_ideal.coe_to_lie_subalgebra_to_submodule`
 - `lie_ideal.incl_range`
 - `lie_hom.ideal_range_eq_lie_span_range`
 - `lie_hom.is_ideal_morphism_iff`
 - `lie_subalgebra.mem_range`
 - `lie_subalgebra.mem_map`
 - `lie_subalgebra.mem_of_le`
 - `lie_subalgebra.of_le_eq_comap_incl`
 - `lie_subalgebra.exists_lie_ideal_coe_eq_iff`
 - `lie_subalgebra.exists_nested_lie_ideal_coe_eq_iff`
 - `submodule.exists_lie_submodule_coe_eq_iff`
 - `lie_submodule.coe_lie_span_submodule_eq_iff`
Deleted lemma:
 - `lie_hom.range_bracket`
New simp attributes:
 - `lie_subalgebra.mem_top`
 - `lie_submodule.mem_top`
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_hom.mem_range
- \+/\- *def* lie_hom.range
- \- *lemma* lie_hom.range_bracket
- \+/\- *lemma* lie_hom.range_coe
- \+/\- *def* lie_subalgebra.comap
- \+ *lemma* lie_subalgebra.incl_range
- \+/\- *def* lie_subalgebra.map
- \+ *lemma* lie_subalgebra.mem_map
- \+/\- *lemma* lie_subalgebra.mem_map_submodule
- \+ *lemma* lie_subalgebra.mem_of_le
- \+/\- *lemma* lie_subalgebra.mem_top
- \+ *def* lie_subalgebra.of_le
- \+ *lemma* lie_subalgebra.of_le_eq_comap_incl
- \- *lemma* lie_subalgebra.range_incl

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_hom.ideal_range_eq_lie_span_range
- \+ *lemma* lie_hom.is_ideal_morphism_iff
- \+ *lemma* lie_ideal.coe_to_lie_subalgebra_to_submodule
- \+ *lemma* lie_ideal.incl_range
- \+/\- *def* lie_ideal.map
- \+ *lemma* lie_subalgebra.exists_lie_ideal_coe_eq_iff
- \+ *lemma* lie_subalgebra.exists_nested_lie_ideal_coe_eq_iff
- \+ *lemma* lie_submodule.coe_lie_span_submodule_eq_iff
- \+/\- *lemma* lie_submodule.mem_top
- \+ *lemma* submodule.exists_lie_submodule_coe_eq_iff



## [2021-02-22 14:12:35](https://github.com/leanprover-community/mathlib/commit/78eb83a)
feat(linear_algebra/pi): add `pi.lsum` ([#6335](https://github.com/leanprover-community/mathlib/pull/6335))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.coe_fn_sum

Modified src/linear_algebra/pi.lean
- \+ *lemma* linear_map.apply_single
- \+ *lemma* linear_map.coe_single
- \+ *def* linear_map.lsum
- \+ *lemma* linear_map.pi_ext'
- \+ *lemma* linear_map.pi_ext'_iff
- \+ *lemma* linear_map.pi_ext
- \+ *lemma* linear_map.pi_ext_iff

Modified src/linear_algebra/prod.lean
- \+ *theorem* linear_map.coprod_comp_prod

Modified src/linear_algebra/std_basis.lean
- \- *lemma* linear_map.pi_ext'
- \- *lemma* linear_map.pi_ext'_iff
- \- *lemma* linear_map.pi_ext
- \- *lemma* linear_map.pi_ext_iff



## [2021-02-22 14:12:34](https://github.com/leanprover-community/mathlib/commit/aa730c6)
feat(linear_algebra): a module has a unique submodule iff it has a unique element ([#6281](https://github.com/leanprover-community/mathlib/pull/6281))
Also strengthens the related lemmas about subgroup and submonoid
#### Estimated changes
Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/basic.lean


Modified src/linear_algebra/basic.lean
- \- *lemma* submodule.bot_ne_top
- \+ *lemma* submodule.bot_to_add_submonoid
- \- *lemma* submodule.eq_bot_of_zero_eq_one
- \+ *lemma* submodule.nontrivial_iff
- \+ *lemma* submodule.subsingleton_iff
- \+ *lemma* submodule.top_to_add_submonoid

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* is_basis_empty
- \- *lemma* is_basis_empty_bot

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/over.lean




## [2021-02-22 14:12:33](https://github.com/leanprover-community/mathlib/commit/ffb6a58)
feat(data/sigma/basic): add a more convenient ext lemma for equality of sigma types over subtypes ([#6257](https://github.com/leanprover-community/mathlib/pull/6257))
#### Estimated changes
Modified src/data/sigma/basic.lean
- \+ *lemma* psigma.subtype_ext
- \+ *lemma* psigma.subtype_ext_iff
- \+ *lemma* sigma.subtype_ext
- \+ *lemma* sigma.subtype_ext_iff



## [2021-02-22 14:12:32](https://github.com/leanprover-community/mathlib/commit/9d54837)
feat(data/polynomial/degree): lemmas on nat_degree and behaviour under multiplication by constants ([#6224](https://github.com/leanprover-community/mathlib/pull/6224))
These lemmas extend the API for nat_degree
I intend to use them to work with integrality statements
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.eq_C_of_nat_degree_eq_zero
- \+/\- *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \+/\- *lemma* polynomial.le_nat_degree_of_coe_le_degree
- \+ *lemma* polynomial.leading_coeff_ne_zero
- \+/\- *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \+/\- *lemma* polynomial.ne_zero_of_coe_le_degree

Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.eq_nat_degree_of_le_mem_support
- \+ *lemma* polynomial.nat_degree_C_mul_eq_of_mul_eq_one
- \+ *lemma* polynomial.nat_degree_C_mul_eq_of_mul_ne_zero
- \+ *lemma* polynomial.nat_degree_C_mul_eq_of_no_zero_divisors
- \+ *lemma* polynomial.nat_degree_C_mul_le
- \+ *lemma* polynomial.nat_degree_add_coeff_mul
- \+ *lemma* polynomial.nat_degree_le_iff_coeff_eq_zero
- \+ *lemma* polynomial.nat_degree_lt_coeff_mul
- \+ *lemma* polynomial.nat_degree_mul_C_eq_of_mul_eq_one
- \+ *lemma* polynomial.nat_degree_mul_C_eq_of_mul_ne_zero
- \+ *lemma* polynomial.nat_degree_mul_C_eq_of_no_zero_divisors
- \+ *lemma* polynomial.nat_degree_mul_C_le



## [2021-02-22 10:42:24](https://github.com/leanprover-community/mathlib/commit/87a021c)
feat(data/quot): `quotient.rec_on_subsingleton` with implicit setoid ([#6346](https://github.com/leanprover-community/mathlib/pull/6346))
#### Estimated changes
Modified src/data/quot.lean




## [2021-02-22 10:42:23](https://github.com/leanprover-community/mathlib/commit/69b93fc)
fix(data/finsupp/basic): delta-reduce the definition of coe_fn_injective ([#6344](https://github.com/leanprover-community/mathlib/pull/6344))
Without this, `apply coe_fn_injective` leaves a messy goal that usually has to be `dsimp`ed in order to make progress with `rw`.
With this change, `dsimp` now fails as the goal is already fully delta-reduced.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.coe_fn_injective



## [2021-02-22 08:31:25](https://github.com/leanprover-community/mathlib/commit/0e51976)
feat(data/polynomial/reverse): Trailing degree is multiplicative ([#6351](https://github.com/leanprover-community/mathlib/pull/6351))
Uses `polynomial.reverse` to prove that `nat_trailing_degree` behaves well under multiplication.
#### Estimated changes
Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.nat_trailing_degree_le_nat_degree

Modified src/data/polynomial/reverse.lean
- \+ *lemma* polynomial.coeff_reverse
- \+ *lemma* polynomial.nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree
- \+ *lemma* polynomial.reflect_neg
- \+ *lemma* polynomial.reflect_sub
- \+ *lemma* polynomial.reverse_eq_zero
- \+ *lemma* polynomial.reverse_leading_coeff
- \+ *lemma* polynomial.reverse_nat_degree
- \+ *lemma* polynomial.reverse_nat_degree_le
- \+ *lemma* polynomial.reverse_nat_trailing_degree
- \+ *lemma* polynomial.reverse_neg
- \+ *lemma* polynomial.reverse_trailing_coeff
- \+ *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.nat_trailing_degree_mul



## [2021-02-22 06:58:33](https://github.com/leanprover-community/mathlib/commit/a3d951b)
feat(data/nat/digits): digits injective at fixed base ([#6338](https://github.com/leanprover-community/mathlib/pull/6338))
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* nat.digits.injective
- \+ *lemma* nat.digits_inj_iff



## [2021-02-22 06:58:32](https://github.com/leanprover-community/mathlib/commit/2b6dec0)
feat(algebraic_geometry/prime_spectrum): specialization order ([#6286](https://github.com/leanprover-community/mathlib/pull/6286))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.as_ideal_le_as_ideal
- \+ *lemma* prime_spectrum.as_ideal_lt_as_ideal
- \+ *lemma* prime_spectrum.le_iff_mem_closure
- \+ *lemma* prime_spectrum.vanishing_ideal_singleton



## [2021-02-22 03:13:35](https://github.com/leanprover-community/mathlib/commit/dc78177)
chore(scripts): update nolints.txt ([#6354](https://github.com/leanprover-community/mathlib/pull/6354))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-22 03:13:34](https://github.com/leanprover-community/mathlib/commit/2134d0c)
feat(algebra/group_power/basic): `abs_lt_abs_of_sqr_lt_sqr` ([#6277](https://github.com/leanprover-community/mathlib/pull/6277))
These lemmas are (almost) the converses of some of the lemmas I added in [#5933](https://github.com/leanprover-community/mathlib/pull/5933).
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* abs_le_abs_of_sqr_le_sqr
- \+ *theorem* abs_le_of_sqr_le_sqr'
- \+ *theorem* abs_le_of_sqr_le_sqr
- \+ *theorem* abs_lt_abs_of_sqr_lt_sqr
- \+ *theorem* abs_lt_of_sqr_lt_sqr'
- \+ *theorem* abs_lt_of_sqr_lt_sqr
- \+/\- *theorem* abs_sqr
- \+/\- *theorem* sqr_abs



## [2021-02-22 00:01:15](https://github.com/leanprover-community/mathlib/commit/b8b8755)
feat(data/list/basic): repeat injectivity ([#6337](https://github.com/leanprover-community/mathlib/pull/6337))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.eq_of_mem_repeat
- \+ *theorem* list.mem_repeat
- \+ *lemma* list.repeat_left_inj'
- \+ *lemma* list.repeat_left_inj
- \+ *lemma* list.repeat_left_injective
- \+ *lemma* list.repeat_right_inj
- \+ *lemma* list.repeat_right_injective



## [2021-02-21 21:41:23](https://github.com/leanprover-community/mathlib/commit/87f8db2)
feat(data/dfinsupp): add coe lemmas ([#6343](https://github.com/leanprover-community/mathlib/pull/6343))
These lemmas already exist for `finsupp`, let's add them for `dfinsupp` too.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.add_apply
- \+ *lemma* dfinsupp.coe_add
- \+ *lemma* dfinsupp.coe_fn_injective
- \+ *lemma* dfinsupp.coe_neg
- \+ *lemma* dfinsupp.coe_smul
- \+ *lemma* dfinsupp.coe_sub
- \+/\- *lemma* dfinsupp.neg_apply
- \+/\- *lemma* dfinsupp.smul_apply
- \+/\- *lemma* dfinsupp.sub_apply



## [2021-02-21 21:41:22](https://github.com/leanprover-community/mathlib/commit/96ae2ad)
docs(undergrad.yaml): recent changes ([#6313](https://github.com/leanprover-community/mathlib/pull/6313))
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-02-21 18:45:11](https://github.com/leanprover-community/mathlib/commit/4355d17)
chore(topology/order): drop an unneeded argument ([#6345](https://github.com/leanprover-community/mathlib/pull/6345))
`closure_induced` doesn't need `f` to be injective.
#### Estimated changes
Modified src/topology/constructions.lean


Modified src/topology/maps.lean
- \+ *lemma* inducing.closure_eq_preimage_closure_image

Modified src/topology/order.lean
- \+/\- *lemma* closure_induced

Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-02-21 18:45:10](https://github.com/leanprover-community/mathlib/commit/ab03ebe)
feat(data/list/basic): drop_eq_nil_iff_le ([#6336](https://github.com/leanprover-community/mathlib/pull/6336))
The iff version of a recently added lemma.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.drop_eq_nil_iff_le



## [2021-02-21 15:22:22](https://github.com/leanprover-community/mathlib/commit/473bb7d)
feat(topology/locally_constant): basics on locally constant functions ([#6192](https://github.com/leanprover-community/mathlib/pull/6192))
From `lean-liquid`
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.not_nonempty_empty

Added src/topology/locally_constant/algebra.lean
- \+ *lemma* locally_constant.div_apply
- \+ *lemma* locally_constant.inv_apply
- \+ *lemma* locally_constant.mul_apply
- \+ *lemma* locally_constant.one_apply

Added src/topology/locally_constant/basic.lean
- \+ *lemma* is_locally_constant.apply_eq_of_is_preconnected
- \+ *lemma* is_locally_constant.comp
- \+ *lemma* is_locally_constant.comp_continuous
- \+ *lemma* is_locally_constant.comp₂
- \+ *lemma* is_locally_constant.const
- \+ *lemma* is_locally_constant.div
- \+ *lemma* is_locally_constant.exists_open
- \+ *lemma* is_locally_constant.iff_continuous
- \+ *lemma* is_locally_constant.iff_continuous_bot
- \+ *lemma* is_locally_constant.iff_eventually_eq
- \+ *lemma* is_locally_constant.iff_exists_open
- \+ *lemma* is_locally_constant.iff_is_const
- \+ *lemma* is_locally_constant.inv
- \+ *lemma* is_locally_constant.is_open_fiber
- \+ *lemma* is_locally_constant.mul
- \+ *lemma* is_locally_constant.of_constant
- \+ *lemma* is_locally_constant.of_discrete
- \+ *lemma* is_locally_constant.one
- \+ *lemma* is_locally_constant.prod_mk
- \+ *lemma* is_locally_constant.range_finite
- \+ *def* is_locally_constant
- \+ *lemma* locally_constant.apply_eq_of_is_preconnected
- \+ *lemma* locally_constant.apply_eq_of_preconnected_space
- \+ *lemma* locally_constant.coe_comap
- \+ *theorem* locally_constant.coe_inj
- \+ *theorem* locally_constant.coe_injective
- \+ *lemma* locally_constant.coe_mk
- \+ *def* locally_constant.comap
- \+ *lemma* locally_constant.comap_comp
- \+ *lemma* locally_constant.comap_const
- \+ *lemma* locally_constant.comap_id
- \+ *theorem* locally_constant.congr_arg
- \+ *theorem* locally_constant.congr_fun
- \+ *def* locally_constant.const
- \+ *lemma* locally_constant.eq_const
- \+ *lemma* locally_constant.exists_eq_const
- \+ *theorem* locally_constant.ext
- \+ *theorem* locally_constant.ext_iff
- \+ *def* locally_constant.map
- \+ *lemma* locally_constant.map_apply
- \+ *lemma* locally_constant.map_comp
- \+ *lemma* locally_constant.map_id
- \+ *lemma* locally_constant.range_finite
- \+ *lemma* locally_constant.to_fun_eq_coe



## [2021-02-21 06:06:38](https://github.com/leanprover-community/mathlib/commit/f470cc6)
feat(measure_theory/interval_integral): add simp attribute to `integral_const` ([#6334](https://github.com/leanprover-community/mathlib/pull/6334))
By adding a `simp` attribute to `interval_integral.integral_const`, the likes of the following become possible:
```
import measure_theory.interval_integral
example : ∫ x:ℝ in 5..19, (12:ℝ) = 168 := by norm_num
```
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_const



## [2021-02-21 01:15:37](https://github.com/leanprover-community/mathlib/commit/4d4c7bb)
chore(scripts): update nolints.txt ([#6332](https://github.com/leanprover-community/mathlib/pull/6332))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-20 21:10:00](https://github.com/leanprover-community/mathlib/commit/93d1760)
chore(topology/bases): golf a proof ([#6326](https://github.com/leanprover-community/mathlib/pull/6326))
Also add some supporting lemmas
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* topological_space.is_topological_basis.dense_iff
- \+ *lemma* topological_space.is_topological_basis.mem_closure_iff

Modified src/topology/basic.lean
- \+ *lemma* filter.has_basis.cluster_pt_iff
- \+ *theorem* mem_closure_iff_nhds_basis'



## [2021-02-20 21:09:59](https://github.com/leanprover-community/mathlib/commit/08ea23b)
refactor(group_theory/free_*): remove API duplicated by lift, promote lift functions to equivs ([#6311](https://github.com/leanprover-community/mathlib/pull/6311))
This removes:
* `free_group.to_group.to_fun` and `free_group.to_group`, as these are both subsumed by the stronger `lift`.
* `abelianization.hom_equiv` as this is now `abelianization.lift.symm`
* `free_abelian_group.hom_equiv` as this is now `free_abelian_group.lift.symm`
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/free_monoid.lean


Modified src/group_theory/abelianization.lean
- \- *def* abelianization.hom_equiv
- \+/\- *def* abelianization.lift

Modified src/group_theory/free_abelian_group.lean
- \- *def* free_abelian_group.hom_equiv
- \- *lemma* free_abelian_group.hom_equiv_apply
- \- *lemma* free_abelian_group.hom_equiv_symm_apply
- \+/\- *def* free_abelian_group.lift

Modified src/group_theory/free_group.lean
- \+ *def* free_group.lift.aux
- \+ *lemma* free_group.lift.mk
- \+ *lemma* free_group.lift.of
- \+ *theorem* free_group.lift.of_eq
- \+ *theorem* free_group.lift.range_eq_closure
- \+ *theorem* free_group.lift.range_subset
- \+ *theorem* free_group.lift.unique
- \+/\- *def* free_group.lift
- \+ *theorem* free_group.lift_eq_prod_map
- \+ *theorem* free_group.map_eq_lift
- \- *theorem* free_group.map_eq_to_group
- \+/\- *def* free_group.prod
- \+ *theorem* free_group.red.step.lift
- \- *theorem* free_group.red.step.to_group
- \- *def* free_group.to_group.aux
- \- *lemma* free_group.to_group.mk
- \- *lemma* free_group.to_group.of
- \- *theorem* free_group.to_group.of_eq
- \- *theorem* free_group.to_group.range_eq_closure
- \- *theorem* free_group.to_group.range_subset
- \- *def* free_group.to_group.to_fun
- \- *theorem* free_group.to_group.unique
- \- *def* free_group.to_group
- \- *theorem* free_group.to_group_eq_prod_map

Modified src/group_theory/presented_group.lean
- \+/\- *lemma* presented_group.to_group.of

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean




## [2021-02-20 17:42:12](https://github.com/leanprover-community/mathlib/commit/dccc542)
fix(algebra/group/pi): remove unnecessary add_monoid requirement from pi.single_zero ([#6325](https://github.com/leanprover-community/mathlib/pull/6325))
Follows on from [#6317](https://github.com/leanprover-community/mathlib/pull/6317)
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *lemma* pi.single_zero
- \+ *def* zero_hom.single



## [2021-02-20 17:42:11](https://github.com/leanprover-community/mathlib/commit/f0aad50)
feat(data/equiv/basic): injective iff injective after composing with equiv ([#6283](https://github.com/leanprover-community/mathlib/pull/6283))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.bijective_comp
- \+ *lemma* equiv.comp_bijective
- \+ *lemma* equiv.comp_injective
- \+ *lemma* equiv.comp_surjective
- \+ *lemma* equiv.injective_comp
- \+ *lemma* equiv.surjective_comp

Modified src/logic/function/basic.lean
- \+ *lemma* function.bijective.of_comp_iff'
- \+ *lemma* function.bijective.of_comp_iff
- \+ *lemma* function.injective.of_comp_iff'
- \+ *lemma* function.injective.of_comp_iff
- \+ *lemma* function.surjective.of_comp_iff'
- \+ *lemma* function.surjective.of_comp_iff



## [2021-02-20 17:42:10](https://github.com/leanprover-community/mathlib/commit/ee8708e)
feat(algebra/regular): define regular elements ([#6282](https://github.com/leanprover-community/mathlib/pull/6282))
The goal of this PR is to start the API for regular elements.  The final goal is to talk about non-zero-divisors.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/is_regular
#### Estimated changes
Added src/algebra/regular.lean
- \+ *lemma* is_left_regular.mul
- \+ *lemma* is_left_regular.of_mul
- \+ *lemma* is_left_regular.subsingleton
- \+ *def* is_left_regular
- \+ *lemma* is_left_regular_of_left_cancel_semigroup
- \+ *lemma* is_left_regular_of_mul_eq_one
- \+ *lemma* is_left_regular_zero_iff_subsingleton
- \+ *lemma* is_regular.and_of_mul_of_mul
- \+ *lemma* is_regular.subsingleton
- \+ *lemma* is_regular_iff_subsingleton
- \+ *lemma* is_regular_mul_and_mul_iff
- \+ *lemma* is_regular_mul_iff
- \+ *lemma* is_regular_of_cancel_monoid
- \+ *lemma* is_regular_of_cancel_monoid_with_zero
- \+ *lemma* is_regular_one
- \+ *lemma* is_right_regular.mul
- \+ *lemma* is_right_regular.of_mul
- \+ *lemma* is_right_regular.subsingleton
- \+ *def* is_right_regular
- \+ *lemma* is_right_regular_of_mul_eq_one
- \+ *lemma* is_right_regular_of_right_cancel_semigroup
- \+ *lemma* is_right_regular_zero_iff_subsingleton
- \+ *lemma* is_unit.is_regular
- \+ *lemma* mul_is_left_regular_iff
- \+ *lemma* mul_is_right_regular_iff
- \+ *lemma* not_is_left_regular_zero_iff
- \+ *lemma* not_is_right_regular_zero_iff
- \+ *lemma* units.is_regular



## [2021-02-20 15:00:59](https://github.com/leanprover-community/mathlib/commit/1855bd5)
chore(*): split lines ([#6323](https://github.com/leanprover-community/mathlib/pull/6323))
#### Estimated changes
Modified src/algebraic_geometry/sheafed_space.lean


Modified src/group_theory/eckmann_hilton.lean
- \+/\- *def* eckmann_hilton.comm_group

Modified src/group_theory/semidirect_product.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* subgroup.nontrivial_iff_exists_ne_one

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* submonoid.nontrivial_iff_exists_ne_one

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* exists_prime_spectrum_prod_le_and_ne_bot_of_domain
- \+/\- *lemma* finite_of_linear_independent

Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/subring.lean
- \+/\- *lemma* subring.Inf_to_submonoid

Modified src/ring_theory/tensor_product.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-02-20 11:52:21](https://github.com/leanprover-community/mathlib/commit/ed55502)
doc(algebraic_geometry/is_open_comap_C): add reference to Stacks project ([#6322](https://github.com/leanprover-community/mathlib/pull/6322))
Updated the doc-strings to reference the Stacks project.
Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/stacks.20tags
#### Estimated changes
Modified src/algebraic_geometry/is_open_comap_C.lean




## [2021-02-20 11:52:20](https://github.com/leanprover-community/mathlib/commit/52e2937)
feat(topology): the currying homeomorphism ([#6319](https://github.com/leanprover-community/mathlib/pull/6319))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.continuous_curry'
- \+ *lemma* continuous_map.continuous_curry
- \+ *lemma* continuous_map.continuous_of_continuous_uncurry
- \+ *lemma* continuous_map.continuous_uncurry
- \+ *lemma* continuous_map.continuous_uncurry_of_continuous
- \+ *def* continuous_map.curry'
- \+ *def* continuous_map.curry
- \+ *def* continuous_map.uncurry
- \+ *def* homeomorph.curry

Modified src/topology/subset_properties.lean




## [2021-02-20 11:52:19](https://github.com/leanprover-community/mathlib/commit/26d287c)
doc(ring_theory/*): two module docs ([#6318](https://github.com/leanprover-community/mathlib/pull/6318))
This PR provides module docs for `ring_theory.polynomial.scale_roots` as well as `ring_theory.multiplicity`. Furthermore, some lines are split in those two files.
#### Estimated changes
Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/scale_roots.lean




## [2021-02-20 11:52:19](https://github.com/leanprover-community/mathlib/commit/c7c40a7)
feat(*/pi): add lemmas about how `single` interacts with operators ([#6317](https://github.com/leanprover-community/mathlib/pull/6317))
This also adds a missing pi instances for `monoid_with_zero`.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *def* add_monoid_hom.single
- \+ *def* mul_hom.single
- \+ *lemma* pi.single_add
- \+ *lemma* pi.single_mul
- \+ *lemma* pi.single_neg
- \+ *lemma* pi.single_sub
- \+ *lemma* pi.single_zero

Modified src/algebra/module/pi.lean
- \+ *lemma* pi.single_smul'
- \+ *lemma* pi.single_smul

Modified src/data/pi.lean
- \+ *lemma* pi.apply_single
- \+ *lemma* pi.apply_single₂

Modified src/linear_algebra/pi.lean




## [2021-02-20 09:02:14](https://github.com/leanprover-community/mathlib/commit/4d2dcdb)
chore(*): fix broken Zulip archive links ([#6321](https://github.com/leanprover-community/mathlib/pull/6321))
#### Estimated changes
Modified src/data/tree.lean


Modified src/logic/basic.lean




## [2021-02-20 01:44:35](https://github.com/leanprover-community/mathlib/commit/3e381ad)
chore(ring_theory/*): split lines ([#6316](https://github.com/leanprover-community/mathlib/pull/6316))
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *theorem* free_comm_ring.exists_finite_support
- \+/\- *lemma* free_comm_ring.restriction_of

Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *theorem* ideal.mem_radical_of_pow_mem
- \+/\- *lemma* ideal.span_singleton_mul_span_singleton
- \+/\- *lemma* ring_hom.lift_of_surjective_comp

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean
- \+/\- *theorem* ideal.is_local.le_jacobson
- \+/\- *theorem* ideal.is_primary_of_is_maximal_radical

Modified src/ring_theory/localization.lean




## [2021-02-20 01:44:34](https://github.com/leanprover-community/mathlib/commit/32b9b21)
refactor(linear_algebra/pi): add `linear_map.single` to match `add_monoid_hom.single` ([#6315](https://github.com/leanprover-community/mathlib/pull/6315))
This changes the definition of `std_basis` to be exactly `linear_map.single`, but proves equality with the old definition.
In future, it might make sense to remove `std_basis` entirely.
#### Estimated changes
Modified src/linear_algebra/pi.lean
- \+ *def* linear_map.single

Modified src/linear_algebra/std_basis.lean
- \+/\- *def* linear_map.std_basis
- \+ *lemma* linear_map.std_basis_eq_pi_diag

Modified src/ring_theory/power_series/basic.lean




## [2021-02-20 01:44:33](https://github.com/leanprover-community/mathlib/commit/d483bc2)
chore(data/indicator_function): add a formula for the support of `indicator` ([#6314](https://github.com/leanprover-community/mathlib/pull/6314))
* rename `set.support_indicator` to `set.support_indicator_subset`;
* add a new `set.support_indicator`;
* add `function.support_comp_eq_preimage`.
#### Estimated changes
Modified src/data/indicator_function.lean
- \+/\- *lemma* set.support_indicator
- \+ *lemma* set.support_indicator_subset

Modified src/topology/algebra/infinite_sum.lean




## [2021-02-20 01:01:26](https://github.com/leanprover-community/mathlib/commit/3ab9818)
chore(scripts): update nolints.txt ([#6320](https://github.com/leanprover-community/mathlib/pull/6320))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-19 14:14:19](https://github.com/leanprover-community/mathlib/commit/845654a)
feat(analysis/calculus): define a smooth bump function ([#4458](https://github.com/leanprover-community/mathlib/pull/4458))
Define an infinitely smooth function which is `1` on the closed ball of radius `1` and is `0` outside of the open ball of radius `2`.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean
- \+ *lemma* exists_times_cont_diff_bump_function_of_mem_nhds
- \- *theorem* exp_neg_inv_glue.smooth
- \+ *lemma* smooth_bump_function.eventually_eq_one
- \+ *lemma* smooth_bump_function.eventually_eq_one_of_norm_lt_one
- \+ *lemma* smooth_bump_function.le_one
- \+ *lemma* smooth_bump_function.lt_one_of_one_lt_norm
- \+ *lemma* smooth_bump_function.nonneg
- \+ *lemma* smooth_bump_function.one_of_norm_le_one
- \+ *lemma* smooth_bump_function.pos_of_norm_lt_two
- \+ *lemma* smooth_bump_function.support_eq
- \+ *lemma* smooth_bump_function.zero_of_two_le_norm
- \+ *def* smooth_bump_function
- \+ *lemma* smooth_transition.le_one
- \+ *lemma* smooth_transition.lt_one_of_lt_one
- \+ *lemma* smooth_transition.nonneg
- \+ *lemma* smooth_transition.one_of_one_le
- \+ *lemma* smooth_transition.pos_denom
- \+ *lemma* smooth_transition.pos_of_pos
- \+ *lemma* smooth_transition.zero_of_nonpos
- \+ *def* smooth_transition

Modified src/data/support.lean
- \+ *lemma* function.support_comp_eq_preimage

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.image_closure



## [2021-02-19 12:23:04](https://github.com/leanprover-community/mathlib/commit/f6eef43)
doc(ring_theory): move some module docstring to correct place ([#6312](https://github.com/leanprover-community/mathlib/pull/6312))
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/tensor_product.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2021-02-19 12:23:03](https://github.com/leanprover-community/mathlib/commit/aaab837)
doc(ring_theory/witt_vector/witt_polynomial): move module docstring up ([#6310](https://github.com/leanprover-community/mathlib/pull/6310))
#### Estimated changes
Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-02-19 12:23:02](https://github.com/leanprover-community/mathlib/commit/0df1998)
doc(set_theory/*): more documentation about cardinals and ordinals ([#6247](https://github.com/leanprover-community/mathlib/pull/6247))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.le_def

Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/set_theory/ordinal_notation.lean




## [2021-02-19 12:23:01](https://github.com/leanprover-community/mathlib/commit/114f8ef)
chore(data/buffer/parser/numeral): derive mono for numeral ([#5463](https://github.com/leanprover-community/mathlib/pull/5463))
Thanks to Rob Lewis, using classes, instances, and the `delta_instance_handler`, transferring over instances becomes very easy.
#### Estimated changes
Modified src/data/buffer/parser/numeral.lean
- \+/\- *def* parser.numeral.char.of_fintype
- \+/\- *def* parser.numeral.char
- \+/\- *def* parser.numeral.from_one.of_fintype
- \+/\- *def* parser.numeral.from_one
- \+/\- *def* parser.numeral.of_fintype
- \+/\- *def* parser.numeral



## [2021-02-19 09:04:38](https://github.com/leanprover-community/mathlib/commit/e5c7789)
fix(lint/type_classes): fix instance_priority bug ([#6305](https://github.com/leanprover-community/mathlib/pull/6305))
The linter now doesn't fail if the type is a beta redex
#### Estimated changes
Modified src/tactic/lint/type_classes.lean


Modified test/lint.lean




## [2021-02-19 07:04:09](https://github.com/leanprover-community/mathlib/commit/a0e2b3c)
chore(topology/Profinite): reduce universe variables ([#6300](https://github.com/leanprover-community/mathlib/pull/6300))
See https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/universe.20issue
#### Estimated changes
Modified src/topology/category/Profinite.lean
- \+/\- *def* CompHaus.to_Profinite_obj
- \+/\- *def* Profinite.to_CompHaus_equivalence



## [2021-02-19 07:04:08](https://github.com/leanprover-community/mathlib/commit/64d86f7)
feat(topology/{subset_properties,separation}): closed subsets of compact t0 spaces contain a closed point ([#6273](https://github.com/leanprover-community/mathlib/pull/6273))
This adds two statements.  The first is that nonempty closed subsets of a compact space have a minimal nonempty closed subset, and the second is that when the space is additionally T0 then that minimal subset is a singleton.
(This PR does not do this, but one can go on to show that there is functor from compact T0 spaces to T1 spaces by taking the set of closed points, and it preserves nonemptiness.)
#### Estimated changes
Modified src/topology/separation.lean
- \+ *theorem* is_closed.exists_closed_singleton

Modified src/topology/subset_properties.lean
- \+ *theorem* is_closed.exists_minimal_nonempty_closed_subset



## [2021-02-19 04:14:30](https://github.com/leanprover-community/mathlib/commit/626a4b5)
chore(scripts): update nolints.txt ([#6303](https://github.com/leanprover-community/mathlib/pull/6303))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-19 04:14:29](https://github.com/leanprover-community/mathlib/commit/75149c3)
feat(data/list/basic): tail_drop, cons_nth_le_drop_succ ([#6265](https://github.com/leanprover-community/mathlib/pull/6265))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.cons_nth_le_drop_succ
- \+ *lemma* list.tail_drop



## [2021-02-19 00:43:42](https://github.com/leanprover-community/mathlib/commit/1fecd52)
fix(tactic/push_neg): fully simplify expressions not named `h` ([#6297](https://github.com/leanprover-community/mathlib/pull/6297))
A final pass of `push_neg` is intended to turn `¬ a = b` into `a ≠ b`.
Unfortunately, when you use `push_neg at ...`, this is applied to the hypothesis literally named `h`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60push_neg.60.20behaviour.20depends.20on.20variable.20name)
#### Estimated changes
Modified src/tactic/push_neg.lean


Modified test/push_neg.lean




## [2021-02-18 23:50:16](https://github.com/leanprover-community/mathlib/commit/3a8d976)
fix(archive/100/82): remove nonterminal simps ([#6299](https://github.com/leanprover-community/mathlib/pull/6299))
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean




## [2021-02-18 23:50:15](https://github.com/leanprover-community/mathlib/commit/8696990)
feat(category_theory/adjunction/reflective): show compositions of reflective are reflective ([#6298](https://github.com/leanprover-community/mathlib/pull/6298))
Show compositions of reflective are reflective.
#### Estimated changes
Modified src/category_theory/adjunction/reflective.lean




## [2021-02-18 20:23:11](https://github.com/leanprover-community/mathlib/commit/96f8933)
perf(tactic/lint/frontend): run linters in parallel ([#6293](https://github.com/leanprover-community/mathlib/pull/6293))
With this change it takes 5 minutes instead of 33 minutes to lint mathlib (on my machine...).
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/linting.20time
#### Estimated changes
Modified src/data/list/defs.lean


Modified src/tactic/lint/frontend.lean




## [2021-02-18 16:34:50](https://github.com/leanprover-community/mathlib/commit/619c1b0)
chore({algebra, algebraic_geometry}/*): move 1 module doc and split lines ([#6294](https://github.com/leanprover-community/mathlib/pull/6294))
This moves the module doc for `algebra/ordered_group` so that it gets recognised by the linter. Furthermore, several lines are split in the algebra and algebraic_geometry folder.
#### Estimated changes
Modified archive/miu_language/basic.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/continued_fractions/terminated_stable.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/module/submodule.lean


Modified src/algebra/ordered_group.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/stalks.lean




## [2021-02-18 11:09:39](https://github.com/leanprover-community/mathlib/commit/5b579a2)
feat(topology/category/profinite): show Profinite is reflective in CompHaus ([#6219](https://github.com/leanprover-community/mathlib/pull/6219))
Show Profinite is reflective in CompHaus.
#### Estimated changes
Modified src/topology/category/CompHaus.lean


Modified src/topology/category/Profinite.lean
- \+ *def* CompHaus.to_Profinite
- \+ *lemma* CompHaus.to_Profinite_obj'
- \+ *def* CompHaus.to_Profinite_obj
- \+ *def* Profinite.to_CompHaus
- \+ *def* Profinite.to_CompHaus_equivalence
- \+ *lemma* Profinite.to_CompHaus_to_Top
- \+ *def* Profinite.to_Profinite_adj_to_CompHaus
- \- *def* Profinite_to_CompHaus
- \- *lemma* Profinite_to_CompHaus_to_Top

Modified src/topology/connected.lean
- \+ *lemma* connected_component_nrel_iff
- \+ *def* connected_components
- \+ *lemma* connected_components_lift_unique'
- \+ *lemma* connected_components_preimage_image
- \+ *lemma* connected_components_preimage_singleton
- \+ *def* continuous.connected_components_lift
- \+ *lemma* continuous.connected_components_lift_continuous
- \+ *lemma* continuous.connected_components_lift_factors
- \+ *lemma* continuous.connected_components_lift_unique
- \+ *def* continuous.connected_components_map
- \+ *lemma* continuous.connected_components_map_continuous
- \- *def* continuous.pi0_lift
- \- *lemma* continuous.pi0_lift_continuous
- \- *lemma* continuous.pi0_lift_factors
- \- *lemma* continuous.pi0_lift_unique
- \- *def* continuous.pi0_map
- \+ *lemma* is_clopen.eq_union_connected_components
- \- *def* pi0
- \- *lemma* pi0_lift_unique'
- \- *lemma* pi0_preimage_image
- \- *lemma* pi0_preimage_singleton

Modified src/topology/separation.lean




## [2021-02-18 09:36:21](https://github.com/leanprover-community/mathlib/commit/5a59781)
fix(doc/references.bib): fix syntax ([#6290](https://github.com/leanprover-community/mathlib/pull/6290))
#### Estimated changes
Modified docs/references.bib




## [2021-02-18 08:05:51](https://github.com/leanprover-community/mathlib/commit/2a7eafa)
feat(order/pfilter): add preorder filters, dual to preorder ideals ([#5928](https://github.com/leanprover-community/mathlib/pull/5928))
Named `pfilter` to not conflict with the existing `order/filter`,
which is a much more developed theory of a special case of this.
#### Estimated changes
Added src/order/pfilter.lean
- \+ *lemma* pfilter.directed
- \+ *lemma* pfilter.ext
- \+ *lemma* pfilter.inf_mem
- \+ *lemma* pfilter.inf_mem_iff
- \+ *lemma* pfilter.mem_of_le
- \+ *lemma* pfilter.mem_of_mem_of_le
- \+ *lemma* pfilter.nonempty
- \+ *def* pfilter.principal
- \+ *lemma* pfilter.principal_le_iff
- \+ *lemma* pfilter.top_mem



## [2021-02-18 05:31:27](https://github.com/leanprover-community/mathlib/commit/017acae)
feat(linear_algebra/dual): adds dual annihilators ([#6078](https://github.com/leanprover-community/mathlib/pull/6078))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.dom_restrict'
- \+ *lemma* linear_map.dom_restrict'_apply

Modified src/linear_algebra/dual.lean
- \+ *def* submodule.dual_annihilator
- \+ *def* submodule.dual_restrict
- \+ *lemma* submodule.dual_restrict_apply
- \+ *lemma* submodule.dual_restrict_ker_eq_dual_annihilator
- \+ *lemma* submodule.mem_dual_annihilator
- \+ *lemma* subspace.dual_equiv_dual_apply
- \+ *lemma* subspace.dual_equiv_dual_def
- \+ *lemma* subspace.dual_lift_injective
- \+ *lemma* subspace.dual_lift_of_mem
- \+ *lemma* subspace.dual_lift_of_subtype
- \+ *lemma* subspace.dual_lift_right_inverse
- \+ *lemma* subspace.dual_restrict_comp_dual_lift
- \+ *lemma* subspace.dual_restrict_left_inverse
- \+ *lemma* subspace.dual_restrict_surjective

Modified src/linear_algebra/finite_dimensional.lean




## [2021-02-18 02:18:27](https://github.com/leanprover-community/mathlib/commit/7c267df)
chore(scripts): update nolints.txt ([#6289](https://github.com/leanprover-community/mathlib/pull/6289))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-17 23:53:33](https://github.com/leanprover-community/mathlib/commit/7592a8f)
chore(analysis/normed_space/finite_dimension,topology/metric_space): golf ([#6285](https://github.com/leanprover-community/mathlib/pull/6285))
* golf two proofs about `finite_dimension`;
* move `proper_image_of_proper` to `antilipschitz`, rename to
  `antilipschitz_with.proper_space`, golf.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.bounded_preimage

Modified src/topology/metric_space/basic.lean
- \- *lemma* metric.proper_image_of_proper



## [2021-02-17 23:53:32](https://github.com/leanprover-community/mathlib/commit/bc1c4f2)
feat(data/zmod/basic): add simp lemmas about coercions, tidy lemma names ([#6280](https://github.com/leanprover-community/mathlib/pull/6280))
Split from [#5797](https://github.com/leanprover-community/mathlib/pull/5797). This takes the new proofs without introducing the objectionable names.
This also renames a bunch of lemmas from `zmod.cast_*` to `zmod.nat_cast_*` and `zmod.int_cast_*`, in order to distinguish lemmas about `zmod.cast` from lemmas about `nat.cast` and `int.cast` applied with a zmod argument.
As an example, `zmod.cast_val` has been renamed to `zmod.nat_cast_zmod_val`, as the lemma statement is defeq to `(nat.cast : ℕ → zmod n) (zmod.val x) = x`, and `zmod.nat_cast_val` is already taken by `nat.cast (zmod.val x) = (x : R)`.
The full list of renames:
* `zmod.cast_val` → `zmod.nat_cast_zmod_val`
* `zmod.cast_self` → `zmod.nat_cast_self`
* `zmod.cast_self'` → `zmod.nat_cast_self'`
* `zmod.cast_mod_nat` → `zmod.nat_cast_mod`
* `zmod.cast_mod_int` → `zmod.int_cast_mod`
* `zmod.val_cast_nat` → `zmod.val_nat_cast`
* `zmod.coe_to_nat` → `zmod.nat_cast_to_nat`
* `zmod.cast_unit_of_coprime` → `coe_unit_of_coprime`
* `zmod.cast_nat_abs_val_min_abs` → `zmod.nat_cast_nat_abs_val_min_abs`
#### Estimated changes
Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_id'
- \- *lemma* zmod.cast_mod_int
- \- *lemma* zmod.cast_mod_nat
- \- *lemma* zmod.cast_nat_abs_val_min_abs
- \- *lemma* zmod.cast_self'
- \- *lemma* zmod.cast_self
- \- *lemma* zmod.cast_unit_of_coprime
- \- *lemma* zmod.cast_val
- \- *lemma* zmod.coe_to_nat
- \+ *lemma* zmod.coe_unit_of_coprime
- \+ *lemma* zmod.int_cast_cast
- \+ *lemma* zmod.int_cast_comp_cast
- \+ *lemma* zmod.int_cast_mod
- \+/\- *lemma* zmod.int_cast_surjective
- \+ *lemma* zmod.int_cast_zmod_cast
- \+ *lemma* zmod.nat_cast_comp_val
- \+ *lemma* zmod.nat_cast_mod
- \+ *lemma* zmod.nat_cast_nat_abs_val_min_abs
- \+ *lemma* zmod.nat_cast_self'
- \+ *lemma* zmod.nat_cast_self
- \- *lemma* zmod.nat_cast_surjective
- \+ *lemma* zmod.nat_cast_to_nat
- \+/\- *lemma* zmod.nat_cast_val
- \+ *lemma* zmod.nat_cast_zmod_surjective
- \+ *lemma* zmod.nat_cast_zmod_val
- \+ *lemma* zmod.ring_hom_map_cast
- \- *lemma* zmod.val_cast_nat
- \+ *lemma* zmod.val_nat_cast

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/dihedral.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/witt_vector/frobenius.lean




## [2021-02-17 20:29:45](https://github.com/leanprover-community/mathlib/commit/75f3346)
feat(analysis/normed_space/multilinear): generalized `curry` ([#6270](https://github.com/leanprover-community/mathlib/pull/6270))
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+ *def* continuous_multilinear_map.curry_fin_finset
- \+ *lemma* continuous_multilinear_map.curry_fin_finset_apply
- \+ *lemma* continuous_multilinear_map.curry_fin_finset_apply_const
- \+ *lemma* continuous_multilinear_map.curry_fin_finset_symm_apply
- \+ *lemma* continuous_multilinear_map.curry_fin_finset_symm_apply_const
- \+ *lemma* continuous_multilinear_map.curry_fin_finset_symm_apply_piecewise_const
- \+ *def* continuous_multilinear_map.curry_sum
- \+ *lemma* continuous_multilinear_map.curry_sum_apply
- \+ *def* continuous_multilinear_map.curry_sum_equiv
- \+ *def* continuous_multilinear_map.dom_dom_congr
- \+ *theorem* continuous_multilinear_map.le_of_op_norm_le
- \+ *def* continuous_multilinear_map.uncurry_sum
- \+ *lemma* continuous_multilinear_map.uncurry_sum_apply
- \+ *def* multilinear_map.mk_continuous_linear
- \+ *lemma* multilinear_map.mk_continuous_linear_norm_le'
- \+ *lemma* multilinear_map.mk_continuous_linear_norm_le
- \+ *def* multilinear_map.mk_continuous_multilinear
- \+ *lemma* multilinear_map.mk_continuous_multilinear_apply
- \+ *lemma* multilinear_map.mk_continuous_multilinear_norm_le'
- \+ *lemma* multilinear_map.mk_continuous_multilinear_norm_le
- \+ *lemma* multilinear_map.mk_continuous_norm_le'



## [2021-02-17 20:29:44](https://github.com/leanprover-community/mathlib/commit/152bf15)
feat(data/fin): pred_above_monotone ([#6170](https://github.com/leanprover-community/mathlib/pull/6170))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_pred_monotone
- \+ *lemma* fin.cast_succ_lt_cast_succ_iff
- \+ *lemma* fin.pred_above_left_monotone
- \+ *lemma* fin.pred_above_right_monotone

Modified src/order/preorder_hom.lean
- \+ *def* order_embedding.to_preorder_hom
- \+ *lemma* order_embedding.to_preorder_hom_coe



## [2021-02-17 15:49:57](https://github.com/leanprover-community/mathlib/commit/4bae1c4)
doc(tactic/algebra): document @[ancestor] ([#6272](https://github.com/leanprover-community/mathlib/pull/6272))
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/algebra.lean




## [2021-02-17 15:49:55](https://github.com/leanprover-community/mathlib/commit/07a1b8d)
feat(ring_theory/simple_module): introduce `is_semisimple_module` ([#6215](https://github.com/leanprover-community/mathlib/pull/6215))
Defines `is_semisimple_module` to mean that the lattice of submodules is complemented
Shows that this is equivalent to the module being the `Sup` of its simple submodules
#### Estimated changes
Modified src/order/compactly_generated.lean
- \+ *theorem* is_complemented_of_Sup_atoms_eq_top

Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.is_compl
- \+ *theorem* order_iso.is_compl_iff
- \+ *lemma* order_iso.is_complemented
- \+ *theorem* order_iso.is_complemented_iff

Modified src/representation_theory/maschke.lean
- \+ *theorem* monoid_algebra.is_semisimple_module

Modified src/ring_theory/simple_module.lean
- \+ *theorem* is_semisimple_iff_top_eq_Sup_simples
- \+ *theorem* is_semisimple_module.Sup_simples_eq_top
- \+ *theorem* is_semisimple_of_Sup_simples_eq_top
- \+ *lemma* is_simple_module.is_atom
- \+ *theorem* is_simple_module_iff_is_atom



## [2021-02-17 11:38:42](https://github.com/leanprover-community/mathlib/commit/f066eb1)
feat(algebra/lie/subalgebra): define lattice structure for Lie subalgebras ([#6279](https://github.com/leanprover-community/mathlib/pull/6279))
We already have the lattice structure for Lie submodules but not for subalgebras.
This is mostly a lightly-edited copy-paste of the corresponding subset of results
for Lie submodules that remain true for subalgebras.
The results which hold for Lie submodules but not for Lie subalgebras are:
  - `sup_coe_to_submodule` and `mem_sup`
  - `is_modular_lattice`
I have also made a few tweaks to bring the structure and naming of Lie
subalgebras a little closer to that of Lie submodules.
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.Inf_coe
- \+ *lemma* lie_subalgebra.Inf_coe_to_submodule
- \+ *lemma* lie_subalgebra.Inf_glb
- \+ *lemma* lie_subalgebra.add_eq_sup
- \+ *lemma* lie_subalgebra.bot_coe
- \+ *lemma* lie_subalgebra.bot_coe_submodule
- \+ *lemma* lie_subalgebra.coe_hom_of_le
- \+/\- *theorem* lie_subalgebra.coe_set_eq
- \+ *lemma* lie_subalgebra.coe_submodule_le_coe_submodule
- \+ *lemma* lie_subalgebra.coe_to_submodule
- \- *lemma* lie_subalgebra.coe_to_submodule_eq
- \+ *lemma* lie_subalgebra.coe_to_submodule_eq_iff
- \+ *lemma* lie_subalgebra.coe_to_submodule_mk
- \+ *def* lie_subalgebra.comap
- \+ *lemma* lie_subalgebra.eq_bot_iff
- \+ *lemma* lie_subalgebra.gc_map_comap
- \+ *def* lie_subalgebra.hom_of_le
- \+ *lemma* lie_subalgebra.hom_of_le_apply
- \+ *lemma* lie_subalgebra.hom_of_le_injective
- \+ *theorem* lie_subalgebra.inf_coe
- \+ *lemma* lie_subalgebra.inf_coe_to_submodule
- \+ *lemma* lie_subalgebra.le_def
- \+/\- *def* lie_subalgebra.map
- \+ *lemma* lie_subalgebra.map_le_iff_le_comap
- \+ *lemma* lie_subalgebra.mem_bot
- \+ *lemma* lie_subalgebra.mem_carrier
- \- *lemma* lie_subalgebra.mem_coe'
- \+/\- *lemma* lie_subalgebra.mem_coe
- \+ *lemma* lie_subalgebra.mem_coe_submodule
- \+ *lemma* lie_subalgebra.mem_inf
- \+/\- *lemma* lie_subalgebra.mem_map_submodule
- \+ *lemma* lie_subalgebra.mem_top
- \+/\- *lemma* lie_subalgebra.range_incl
- \+ *lemma* lie_subalgebra.subsingleton_of_bot
- \+ *lemma* lie_subalgebra.top_coe
- \+ *lemma* lie_subalgebra.top_coe_submodule
- \+ *lemma* lie_subalgebra.well_founded_of_noetherian



## [2021-02-17 11:38:41](https://github.com/leanprover-community/mathlib/commit/d43a3ba)
feat(analysis/normed_space/inner_product): norm is smooth at `x ≠ 0` ([#6275](https://github.com/leanprover-community/mathlib/pull/6275))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* differentiable.dist
- \+ *lemma* differentiable.norm
- \+ *lemma* differentiable_at.dist
- \+ *lemma* differentiable_at.norm
- \+ *lemma* differentiable_on.dist
- \+ *lemma* differentiable_on.norm
- \+ *lemma* differentiable_within_at.dist
- \+ *lemma* differentiable_within_at.norm
- \+ *lemma* times_cont_diff.dist
- \+ *lemma* times_cont_diff.norm
- \+ *lemma* times_cont_diff_at.dist
- \+ *lemma* times_cont_diff_at.norm
- \+ *lemma* times_cont_diff_at_norm
- \+ *lemma* times_cont_diff_on.dist
- \+ *lemma* times_cont_diff_on.norm
- \+ *lemma* times_cont_diff_within_at.dist
- \+ *lemma* times_cont_diff_within_at.norm



## [2021-02-17 11:38:40](https://github.com/leanprover-community/mathlib/commit/b190131)
feat(data/int/basic): lemmas about int and int.to_nat ([#6253](https://github.com/leanprover-community/mathlib/pull/6253))
Golfing welcome.
This adds a `@[simp]` lemma `int.add_minus_one : i + -1 = i - 1`, which I think is mostly helpful, but needs to be turned off in `data/num/lemmas.lean`, which is perhaps an argument against it.
I've also added a lemma
```
@[simp] lemma lt_self_iff_false [preorder α] (a : α) : a < a ↔ false :=
```
(not just for `int`), which I've often found useful (e.g. `simpa` works well when it can reduce a hypothesis to `false`). This lemma seems harmless, but I'm happy to hear objections if it is too general.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/data/int/basic.lean
- \+ *lemma* int.add_minus_one
- \+ *lemma* int.coe_pred_of_pos
- \+ *lemma* int.neg_succ_not_nonneg
- \+ *lemma* int.neg_succ_not_pos
- \+ *lemma* int.neg_succ_sub_one
- \+ *lemma* int.pred_to_nat
- \+ *lemma* int.succ_coe_nat_pos
- \+ *lemma* int.to_nat_pred_coe_of_pos

Modified src/data/num/lemmas.lean


Modified src/data/rat/basic.lean


Modified src/data/string/basic.lean


Modified src/group_theory/free_group.lean


Modified src/order/basic.lean
- \+ *lemma* lt_self_iff_false



## [2021-02-17 11:38:39](https://github.com/leanprover-community/mathlib/commit/8b8a5a2)
feat(category/eq_to_hom): lemmas to replace rewriting in objects with eq_to_hom ([#6252](https://github.com/leanprover-community/mathlib/pull/6252))
This adds two lemmas which replace expressions in which we've used `eq.mpr` to rewrite the source or target of a morphism, replacing the `eq.mpr` by composition with an `eq_to_hom`.
Possibly we just shouldn't add these
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.congr_arg_mpr_hom_left
- \+ *lemma* category_theory.congr_arg_mpr_hom_right

Modified src/logic/basic.lean
- \+ *lemma* congr_arg_refl
- \+ *lemma* congr_fun_congr_arg
- \+ *lemma* congr_fun_rfl
- \+ *lemma* congr_refl_left
- \+ *lemma* congr_refl_right



## [2021-02-17 11:38:38](https://github.com/leanprover-community/mathlib/commit/ea1cff4)
feat(linear_algebra/pi): ext lemma for `f : (Π i, M i) →ₗ[R] N` ([#6233](https://github.com/leanprover-community/mathlib/pull/6233))
#### Estimated changes
Modified src/algebra/big_operators/pi.lean
- \+ *lemma* add_monoid_hom.functions_ext'

Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/std_basis.lean
- \+ *lemma* linear_map.coe_std_basis
- \+ *lemma* linear_map.pi_ext'
- \+ *lemma* linear_map.pi_ext'_iff
- \+ *lemma* linear_map.pi_ext
- \+ *lemma* linear_map.pi_ext_iff



## [2021-02-17 11:38:37](https://github.com/leanprover-community/mathlib/commit/0c61fc4)
feat(group_theory): prove the 2nd isomorphism theorem for groups ([#6187](https://github.com/leanprover-community/mathlib/pull/6187))
Define an `inclusion` homomorphism from a subgroup `H` contained in `K` to `K`. Add instance of `subgroup.normal` to `H ∩ N` in `H` whenever `N` is normal and use it to prove the 2nd isomorphism theorem for groups.
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_group.equiv_quotient_of_eq

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.coe_inclusion
- \+ *lemma* subgroup.comap_subtype_inf_left
- \+ *lemma* subgroup.comap_subtype_inf_right
- \+ *def* subgroup.inclusion
- \+ *lemma* subgroup.subtype_comp_inclusion



## [2021-02-17 11:38:36](https://github.com/leanprover-community/mathlib/commit/9b3008e)
feat(algebra/ordered_monoid): inequalities involving mul/add ([#6171](https://github.com/leanprover-community/mathlib/pull/6171))
I couldn't find some statements about inequalities, so I'm adding them. I included all the useful variants I could think of.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+ *lemma* le_mul_of_le_mul_left
- \+ *lemma* le_mul_of_le_mul_right
- \+ *lemma* le_of_le_mul_of_le_one_left
- \+ *lemma* le_of_le_mul_of_le_one_right
- \+ *lemma* le_of_mul_le_of_one_le_left
- \+ *lemma* le_of_mul_le_of_one_le_right
- \+ *lemma* lt_mul_of_lt_mul_left
- \+ *lemma* lt_mul_of_lt_mul_right
- \+ *lemma* lt_of_lt_mul_of_le_one_left
- \+ *lemma* lt_of_lt_mul_of_le_one_right
- \+ *lemma* lt_of_mul_lt_of_one_le_left
- \+ *lemma* lt_of_mul_lt_of_one_le_right
- \+ *lemma* mul_le_of_le_one_left'
- \+ *lemma* mul_le_of_le_one_right'
- \+ *lemma* mul_le_of_mul_le_left
- \+ *lemma* mul_le_of_mul_le_right
- \+ *lemma* mul_lt_of_mul_lt_left
- \+ *lemma* mul_lt_of_mul_lt_right



## [2021-02-17 11:38:35](https://github.com/leanprover-community/mathlib/commit/3c15751)
feat(ring_theory/ideal/operations) : add lemma prod_eq_bot ([#5795](https://github.com/leanprover-community/mathlib/pull/5795))
Add lemma `prod_eq_bot` showing that a product of ideals in an integral domain is zero if and only if one of the terms
is zero.
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.prod_eq_bot

Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* prod_zero_iff_exists_zero



## [2021-02-17 07:54:59](https://github.com/leanprover-community/mathlib/commit/11f054b)
chore(topology/sheaves): speed up slow proofs by tidy ([#6274](https://github.com/leanprover-community/mathlib/pull/6274))
No changes, just making some proofs by tidy explicit, so the file is not quite as slow as previously. Now compiles with `-T40000`.
#### Estimated changes
Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2021-02-17 07:54:58](https://github.com/leanprover-community/mathlib/commit/5258de0)
feat(data/fin): refactor `pred_above` ([#6125](https://github.com/leanprover-community/mathlib/pull/6125))
Currently the signature of `pred_above` is
```lean
def pred_above (p : fin (n+1)) (i : fin (n+1)) (hi : i ≠ p) : fin n := ...
```
and its behaviour is "subtract one from `i` if it is greater than `p`".
There are two reasons I don't like this much:
1. It's not a total function.
2. Since `succ_above` is exactly a simplicial face map, I'd like `pred_above` to be a simplicial degeneracy map.
In this PR I propose replacing this with
```lean
def pred_above (p : fin n) (i : fin (n+1)) : fin n :=
```
again with the behaviour "subtract one from `i` if it is greater than `p`".
~~Unfortunately, it seems the current `pred_above` really is needed for the sake of `fin.insert_nth`, so this PR has ended up as a half-hearted attempt to replace `pred_above`
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.cast_pred
- \+ *theorem* fin.cast_pred_cast_succ
- \+ *lemma* fin.cast_pred_last
- \+ *lemma* fin.cast_pred_mk
- \+ *lemma* fin.cast_pred_zero
- \+ *lemma* fin.cast_succ_cast_pred
- \+/\- *lemma* fin.cast_succ_mk
- \+ *lemma* fin.coe_cast_pred_le_self
- \+ *lemma* fin.coe_cast_pred_lt_iff
- \+ *def* fin.insert_nth'
- \+/\- *def* fin.insert_nth
- \+ *lemma* fin.is_le
- \+ *lemma* fin.le_cast_succ_iff
- \+ *lemma* fin.lt_last_iff_coe_cast_pred
- \+ *lemma* fin.pos_iff_ne_zero
- \+/\- *def* fin.pred_above
- \+/\- *lemma* fin.pred_above_succ_above
- \+/\- *theorem* fin.pred_above_zero
- \+ *lemma* fin.range_succ_above
- \+/\- *lemma* fin.succ_above_pred_above

Modified src/data/fintype/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.compl_ne_eq_singleton

Modified src/data/vector2.lean
- \+ *lemma* vector.remove_nth_insert_nth'
- \- *lemma* vector.remove_nth_insert_nth_ne

Modified src/geometry/manifold/instances/real.lean


Modified src/linear_algebra/multilinear.lean




## [2021-02-17 03:54:44](https://github.com/leanprover-community/mathlib/commit/b2dbfd6)
chore(scripts): update nolints.txt ([#6276](https://github.com/leanprover-community/mathlib/pull/6276))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-17 03:54:43](https://github.com/leanprover-community/mathlib/commit/d4ef2e8)
feat(topology/category/Top): nonempty inverse limit of compact Hausdorff spaces ([#6271](https://github.com/leanprover-community/mathlib/pull/6271))
The limit of an inverse system of nonempty compact Hausdorff spaces is nonempty, and this can be seen as a generalization of Kőnig's lemma.  A future PR will address the weaker generalization that the limit of an inverse system of nonempty finite types is nonempty.
This result could be generalized more, to the inverse limit of nonempty compact T0 spaces where all the maps are closed, but I think it involves an essentially different method.
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/category/default.lean
- \+ *lemma* category_theory.hom_of_le_comp
- \+ *lemma* category_theory.hom_of_le_le_of_hom
- \+ *lemma* category_theory.hom_of_le_refl
- \+ *lemma* category_theory.le_of_hom_hom_of_le

Modified src/logic/basic.lean
- \+ *lemma* iff_mpr_iff_true_intro

Modified src/topology/category/Top/limits.lean
- \+ *lemma* Top.nonempty_limit_cone_of_compact_t2_inverse_system
- \+ *lemma* Top.partial_sections.closed
- \+ *lemma* Top.partial_sections.directed
- \+ *lemma* Top.partial_sections.nonempty
- \+ *def* Top.partial_sections



## [2021-02-17 03:54:42](https://github.com/leanprover-community/mathlib/commit/bf9ca8b)
feat(data/set/finite): complement of finite set is infinite ([#6266](https://github.com/leanprover-community/mathlib/pull/6266))
Add two missing lemmas. One-line proofs due to Yakov Pechersky.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite.infinite_compl
- \+ *lemma* set.infinite_of_finite_compl



## [2021-02-16 23:59:06](https://github.com/leanprover-community/mathlib/commit/7a7a559)
feat(option/basic): add join_eq_none ([#6269](https://github.com/leanprover-community/mathlib/pull/6269))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.join_eq_none



## [2021-02-16 23:59:05](https://github.com/leanprover-community/mathlib/commit/781cc63)
feat(data/real/liouville, ring_theory/algebraic): a Liouville number is transcendental! ([#6204](https://github.com/leanprover-community/mathlib/pull/6204))
This is an annotated proof.  It finishes the first half of the Liouville PR.
A taste of what is to come in a future PR: a proof that Liouville numbers actually exist!
#### Estimated changes
Modified src/data/real/liouville.lean
- \- *lemma* exists_one_le_pow_mul_dist
- \- *lemma* exists_pos_real_of_irrational_root
- \+ *lemma* liouville.exists_one_le_pow_mul_dist
- \+ *lemma* liouville.exists_pos_real_of_irrational_root
- \+/\- *lemma* liouville.irrational
- \+ *theorem* liouville.transcendental

Modified src/ring_theory/algebraic.lean
- \+ *def* transcendental



## [2021-02-16 23:59:04](https://github.com/leanprover-community/mathlib/commit/efa6877)
feat(algebra/category/Module): the free/forgetful adjunction for R-modules ([#6168](https://github.com/leanprover-community/mathlib/pull/6168))
#### Estimated changes
Added src/algebra/category/Module/adjunctions.lean
- \+ *def* Module.adj
- \+ *def* Module.free

Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.arrow_congr
- \+ *def* mul_equiv.monoid_hom_congr

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.induction_linear
- \+ *lemma* finsupp.sum_map_domain_index_add_monoid_hom

Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.ring_lmap_equiv_self

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.lift_apply
- \+ *lemma* finsupp.lift_symm_apply



## [2021-02-16 23:59:03](https://github.com/leanprover-community/mathlib/commit/3bf7241)
feat(algebra/algebra,linear_algebra): add *_equiv.of_left_inverse ([#6167](https://github.com/leanprover-community/mathlib/pull/6167))
The main purpose of this change is to add equivalences onto the range of a function with a left-inverse:
* `algebra_equiv.of_left_inverse`
* `linear_equiv.of_left_inverse`
* `ring_equiv.of_left_inverse`
* `ring_equiv.sof_left_inverse` (the sub***S***emiring version)
This also:
* Renames `alg_hom.alg_equiv.of_injective` to `alg_equiv.of_injective`
* Adds `subalgebra.mem_range_self` and `subsemiring.mem_srange_self` for consistency with `subring.mem_range_self`
* Replaces `subring.surjective_onto_range` with `subring.range_restrict_surjective`, which have defeq statements
These are computable versions of `*_equiv.of_injective`, with the benefit of having a known inverse, and in the case of `linear_equiv` working for `semiring` and not just `ring`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* alg_equiv.of_injective_apply
- \+ *def* alg_equiv.of_left_inverse
- \+ *lemma* alg_equiv.of_left_inverse_apply
- \+ *lemma* alg_equiv.of_left_inverse_symm_apply
- \- *lemma* alg_hom.alg_equiv.of_injective_apply
- \+ *lemma* alg_hom.coe_cod_restrict
- \+ *theorem* alg_hom.mem_range_self
- \+ *def* alg_hom.range_restrict
- \+ *lemma* alg_hom.val_comp_cod_restrict

Modified src/field_theory/normal.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/linear_algebra/basic.lean
- \+ *def* linear_equiv.of_left_inverse
- \+ *lemma* linear_equiv.of_left_inverse_apply
- \+ *lemma* linear_equiv.of_left_inverse_symm_apply

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/subring.lean
- \+ *def* ring_equiv.of_left_inverse
- \+ *lemma* ring_equiv.of_left_inverse_apply
- \+ *lemma* ring_equiv.of_left_inverse_symm_apply
- \+ *lemma* ring_hom.range_restrict_surjective
- \- *lemma* ring_hom.surjective_onto_range

Modified src/ring_theory/subsemiring.lean
- \+ *def* ring_equiv.sof_left_inverse
- \+ *lemma* ring_equiv.sof_left_inverse_apply
- \+ *lemma* ring_equiv.sof_left_inverse_symm_apply
- \+ *lemma* ring_hom.mem_srange_self
- \+ *lemma* ring_hom.srange_restrict_surjective



## [2021-02-16 21:22:44](https://github.com/leanprover-community/mathlib/commit/2289b18)
chore(topology/basic): add `continuous_at_congr` and `continuous_at.congr` ([#6267](https://github.com/leanprover-community/mathlib/pull/6267))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* continuous_at.congr
- \+ *lemma* continuous_at_congr



## [2021-02-16 18:36:50](https://github.com/leanprover-community/mathlib/commit/0b4823c)
doc(*): remove `\\` hack for latex backslashes in markdown ([#6263](https://github.com/leanprover-community/mathlib/pull/6263))
With leanprover-community/doc-gen[#110](https://github.com/leanprover-community/mathlib/pull/110), these should no longer be needed.
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/inverse.lean


Modified src/linear_algebra/basic.lean




## [2021-02-16 18:36:49](https://github.com/leanprover-community/mathlib/commit/16eb4af)
doc(algebraic_geometry/structure_sheaf): fix latex ([#6262](https://github.com/leanprover-community/mathlib/pull/6262))
This is broken regardless of the markdown processor: <https://leanprover-community.github.io/mathlib_docs/algebraic_geometry/structure_sheaf.html#algebraic_geometry.structure_sheaf.is_locally_fraction>
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean




## [2021-02-16 18:36:48](https://github.com/leanprover-community/mathlib/commit/7459c21)
feat(analysis/special_functions): strict differentiability of `real.exp` and `real.log` ([#6256](https://github.com/leanprover-community/mathlib/pull/6256))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* has_strict_deriv_at.exp
- \+ *lemma* has_strict_deriv_at.log
- \+ *lemma* has_strict_fderiv_at.exp
- \+ *lemma* has_strict_fderiv_at.log
- \- *lemma* real.has_deriv_at_log_of_pos
- \+ *lemma* real.has_strict_deriv_at_exp
- \+ *lemma* real.has_strict_deriv_at_log
- \+ *lemma* real.has_strict_deriv_at_log_of_pos
- \+/\- *lemma* real.times_cont_diff_at_log
- \+ *lemma* times_cont_diff.log
- \+ *lemma* times_cont_diff_at.log
- \+ *lemma* times_cont_diff_on.log
- \+ *lemma* times_cont_diff_within_at.log



## [2021-02-16 18:36:47](https://github.com/leanprover-community/mathlib/commit/b0071f3)
feat(analysis/special_functions): `sqrt` is infinitely smooth at `x ≠ 0` ([#6255](https://github.com/leanprover-community/mathlib/pull/6255))
Also move lemmas about differentiability of `sqrt` out from `special_functions/pow` to a new file.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at.pow
- \+ *lemma* times_cont_diff_on.pow
- \+ *lemma* times_cont_diff_within_at.pow

Modified src/analysis/special_functions/pow.lean
- \- *lemma* deriv_sqrt
- \- *lemma* deriv_within_sqrt
- \- *lemma* differentiable.sqrt
- \- *lemma* differentiable_at.sqrt
- \- *lemma* differentiable_on.sqrt
- \- *lemma* differentiable_within_at.sqrt
- \- *lemma* has_deriv_at.sqrt
- \- *lemma* has_deriv_within_at.sqrt

Added src/analysis/special_functions/sqrt.lean
- \+ *lemma* deriv_sqrt
- \+ *lemma* deriv_within_sqrt
- \+ *lemma* differentiable.sqrt
- \+ *lemma* differentiable_at.sqrt
- \+ *lemma* differentiable_on.sqrt
- \+ *lemma* differentiable_within_at.sqrt
- \+ *lemma* fderiv_sqrt
- \+ *lemma* fderiv_within_sqrt
- \+ *lemma* has_deriv_at.sqrt
- \+ *lemma* has_deriv_within_at.sqrt
- \+ *lemma* has_fderiv_at.sqrt
- \+ *lemma* has_fderiv_within_at.sqrt
- \+ *lemma* has_strict_deriv_at.sqrt
- \+ *lemma* has_strict_fderiv_at.sqrt
- \+ *lemma* measurable.sqrt
- \+ *lemma* real.deriv_sqrt_aux
- \+ *lemma* real.has_deriv_at_sqrt
- \+ *lemma* real.has_strict_deriv_at_sqrt
- \+ *lemma* real.times_cont_diff_at_sqrt
- \+ *lemma* times_cont_diff.sqrt
- \+ *lemma* times_cont_diff_at.sqrt
- \+ *lemma* times_cont_diff_on.sqrt
- \+ *lemma* times_cont_diff_within_at.sqrt



## [2021-02-16 18:36:46](https://github.com/leanprover-community/mathlib/commit/8a43163)
feat(topology/algebra/normed_group): completion of normed groups ([#6189](https://github.com/leanprover-community/mathlib/pull/6189))
From `lean-liquid`
#### Estimated changes
Added src/topology/algebra/normed_group.lean
- \+ *lemma* uniform_space.completion.norm_coe



## [2021-02-16 18:36:45](https://github.com/leanprover-community/mathlib/commit/35c070f)
chore(linear_algebra/dfinsupp): make lsum a linear_equiv ([#6185](https://github.com/leanprover-community/mathlib/pull/6185))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20inference.20can't.20fill.20in.20parameters/near/226019081) with a summary of the problem which required the nasty `semimodule_of_linear_map` present here.
#### Estimated changes
Modified src/linear_algebra/dfinsupp.lean
- \+/\- *def* dfinsupp.lsum

Modified src/linear_algebra/direct_sum_module.lean




## [2021-02-16 15:40:57](https://github.com/leanprover-community/mathlib/commit/2411d68)
doc(algebra/big_operators): fix formatting of library note ([#6261](https://github.com/leanprover-community/mathlib/pull/6261))
The name of a library note is already used as its title: <https://leanprover-community.github.io/mathlib_docs_demo/notes.html#operator%20precedence%20of%20big%20operators>
#### Estimated changes
Modified src/algebra/big_operators/basic.lean




## [2021-02-16 12:05:22](https://github.com/leanprover-community/mathlib/commit/362619e)
chore(data/equiv/basic): add lemmas about `equiv.cast` ([#6246](https://github.com/leanprover-community/mathlib/pull/6246))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.cast_eq_iff_heq
- \+ *theorem* equiv.cast_refl
- \+ *theorem* equiv.cast_symm
- \+ *theorem* equiv.cast_trans



## [2021-02-16 12:05:21](https://github.com/leanprover-community/mathlib/commit/841b007)
doc(control/fold): fix bad markdown ([#6245](https://github.com/leanprover-community/mathlib/pull/6245))
#### Estimated changes
Modified src/control/fold.lean




## [2021-02-16 12:05:20](https://github.com/leanprover-community/mathlib/commit/beee5d8)
doc(topology/category/*): 5 module docs ([#6240](https://github.com/leanprover-community/mathlib/pull/6240))
This PR provides module docs to `Top.basic`, `Top.limits`, `Top.adjuntions`, `Top.epi_mono` , `TopCommRing`.
Furthermore, a few lines are split to please the line length linter.
#### Estimated changes
Modified src/topology/category/Top/adjunctions.lean


Modified src/topology/category/Top/basic.lean


Modified src/topology/category/Top/epi_mono.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/category/UniformSpace.lean
- \+/\- *def* CpltSepUniformSpace.of



## [2021-02-16 12:05:19](https://github.com/leanprover-community/mathlib/commit/0716fa4)
feat(data/set/intervals/basic): not_mem of various intervals ([#6238](https://github.com/leanprover-community/mathlib/pull/6238))
`c` is not in a given open/closed/unordered interval if it is outside the bounds of that interval (or if it is not in a superset of that interval).
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.not_mem_subset

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Icc_union_Ici'
- \+/\- *lemma* set.Icc_union_Ici
- \+/\- *lemma* set.Ico_union_Ici'
- \+/\- *lemma* set.Ico_union_Ici
- \+/\- *lemma* set.Iic_union_Icc'
- \+/\- *lemma* set.Iic_union_Icc
- \+/\- *lemma* set.Iic_union_Ioc'
- \+/\- *lemma* set.Iic_union_Ioc
- \+/\- *lemma* set.Iio_union_Ico'
- \+/\- *lemma* set.Iio_union_Ico
- \+/\- *lemma* set.Iio_union_Ioo'
- \+/\- *lemma* set.Iio_union_Ioo
- \+/\- *lemma* set.Ioc_union_Ioi'
- \+/\- *lemma* set.Ioc_union_Ioi
- \+/\- *lemma* set.Ioo_union_Ioi'
- \+/\- *lemma* set.Ioo_union_Ioi
- \+ *lemma* set.not_mem_Icc_of_gt
- \+ *lemma* set.not_mem_Icc_of_lt
- \+ *lemma* set.not_mem_Ici
- \+ *lemma* set.not_mem_Ico_of_ge
- \+ *lemma* set.not_mem_Ico_of_lt
- \+ *lemma* set.not_mem_Iic
- \+ *lemma* set.not_mem_Iio
- \+ *lemma* set.not_mem_Ioc_of_gt
- \+ *lemma* set.not_mem_Ioc_of_le
- \+ *lemma* set.not_mem_Ioi
- \+ *lemma* set.not_mem_Ioo_of_ge
- \+ *lemma* set.not_mem_Ioo_of_le

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.not_mem_interval_of_gt
- \+ *lemma* set.not_mem_interval_of_lt



## [2021-02-16 12:05:17](https://github.com/leanprover-community/mathlib/commit/914517b)
feat(order/well_founded_set): finite antidiagonal of well-founded sets ([#6208](https://github.com/leanprover-community/mathlib/pull/6208))
Defines `set.add_antidiagonal s t a`, the set of pairs of an element from `s` and an element from `t` that add to `a`
If `s` and `t` are well-founded, then constructs a finset version, `finset.add_antidiagonal_of_is_wf`
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.infinite.nonempty

Modified src/order/order_iso_nat.lean
- \+ *theorem* exists_increasing_or_nonincreasing_subseq'
- \+ *theorem* exists_increasing_or_nonincreasing_subseq

Modified src/order/well_founded_set.lean
- \+ *lemma* finset.mem_mul_antidiagonal
- \+ *theorem* not_well_founded_swap_of_infinite_of_well_order
- \+ *lemma* set.mul_antidiagonal.eq_of_fst_eq_fst
- \+ *lemma* set.mul_antidiagonal.eq_of_snd_eq_snd
- \+ *theorem* set.mul_antidiagonal.finite_of_is_wf
- \+ *lemma* set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd
- \+ *def* set.mul_antidiagonal.fst_rel_embedding
- \+ *def* set.mul_antidiagonal.lt_left
- \+ *lemma* set.mul_antidiagonal.mem_mul_antidiagonal
- \+ *def* set.mul_antidiagonal.snd_rel_embedding
- \+ *def* set.mul_antidiagonal



## [2021-02-16 12:05:16](https://github.com/leanprover-community/mathlib/commit/1a43888)
feat(analysis/normed_space/operator_norm): bundle more arguments ([#6207](https://github.com/leanprover-community/mathlib/pull/6207))
* Drop `lmul_left` in favor of a partially applied `lmul`.
* Use `lmul_left_right` in `has_fderiv_at_ring_inverse` and related lemmas.
* Add bundled `compL`, `lmulₗᵢ`, `lsmul`.
* Make `𝕜` argument in `of_homothety` implicit.
* Add `deriv₂` and `bilinear_comp`.
#### Estimated changes
Modified src/analysis/analytic/linear.lean
- \+ *def* continuous_linear_map.fpower_series_bilinear
- \+ *lemma* continuous_linear_map.fpower_series_bilinear_radius
- \+ *def* continuous_linear_map.uncurry_bilinear
- \+ *lemma* continuous_linear_map.uncurry_bilinear_apply

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous_linear_map.is_bounded_bilinear_map

Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* continuous_linear_map.bilinear_comp
- \+ *lemma* continuous_linear_map.bilinear_comp_apply
- \+ *lemma* continuous_linear_map.coe_deriv₂
- \+ *lemma* continuous_linear_map.coe_lmul_rightₗᵢ
- \+ *lemma* continuous_linear_map.coe_lmulₗᵢ
- \+ *def* continuous_linear_map.compL
- \+ *lemma* continuous_linear_map.compL_apply
- \+ *def* continuous_linear_map.deriv₂
- \+ *lemma* continuous_linear_map.flip_apply
- \+ *def* continuous_linear_map.lmul
- \+ *lemma* continuous_linear_map.lmul_apply
- \- *def* continuous_linear_map.lmul_left
- \- *lemma* continuous_linear_map.lmul_left_apply
- \- *lemma* continuous_linear_map.lmul_left_norm
- \+/\- *def* continuous_linear_map.lmul_left_right
- \+/\- *lemma* continuous_linear_map.lmul_left_right_apply
- \- *lemma* continuous_linear_map.lmul_left_right_norm_le
- \+/\- *def* continuous_linear_map.lmul_right
- \- *lemma* continuous_linear_map.lmul_right_norm
- \+ *def* continuous_linear_map.lmul_rightₗᵢ
- \+ *def* continuous_linear_map.lmulₗᵢ
- \+ *def* continuous_linear_map.lsmul
- \+ *lemma* continuous_linear_map.map_add₂
- \+ *lemma* continuous_linear_map.op_norm_lmul
- \+ *lemma* continuous_linear_map.op_norm_lmul_apply
- \+ *lemma* continuous_linear_map.op_norm_lmul_left_right_apply_apply_le
- \+ *lemma* continuous_linear_map.op_norm_lmul_left_right_apply_le
- \+ *lemma* continuous_linear_map.op_norm_lmul_left_right_le
- \+ *lemma* continuous_linear_map.op_norm_lmul_right
- \+ *lemma* continuous_linear_map.op_norm_lmul_right_apply



## [2021-02-16 12:05:15](https://github.com/leanprover-community/mathlib/commit/8d9eb26)
chore(linear_algebra/finsupp): make lsum a linear_equiv ([#6183](https://github.com/leanprover-community/mathlib/pull/6183))
#### Estimated changes
Modified src/group_theory/group_action/defs.lean


Modified src/linear_algebra/direct_sum/finsupp.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* finsupp.coe_lsum
- \+/\- *def* finsupp.lsum
- \+/\- *theorem* finsupp.lsum_symm_apply

Modified src/linear_algebra/prod.lean




## [2021-02-16 12:05:14](https://github.com/leanprover-community/mathlib/commit/314f5ad)
feat(ring_theory/finiteness): add quotient of finitely presented ([#6098](https://github.com/leanprover-community/mathlib/pull/6098))
I've added `algebra.finitely_presented.quotient`: the quotient of a finitely presented algebra by a finitely generated ideal is finitely presented. To do so I had to prove some preliminary results about finitely generated modules.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* submodule.span_eq_restrict_scalars
- \+ *lemma* submodule.span_le_restrict_scalars

Modified src/ring_theory/finiteness.lean
- \+ *lemma* algebra.finitely_presented.of_surjective
- \+ *lemma* algebra.finitely_presented.quotient

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_ker_comp
- \+ *lemma* submodule.fg_ker_ring_hom_comp
- \+ *lemma* submodule.fg_restrict_scalars



## [2021-02-16 12:05:12](https://github.com/leanprover-community/mathlib/commit/3cec1cf)
feat(apply_fun): handle implicit arguments ([#6091](https://github.com/leanprover-community/mathlib/pull/6091))
I've modified the way `apply_fun` handles inequalities, by building an intermediate expression before calling `mono` to discharge the `monotone f` subgoal. This has the effect of sometimes filling in implicit arguments successfully, so that `mono` works.
In `tests/apply_fun.lean` I've added an example showing this in action
#### Estimated changes
Modified src/tactic/apply_fun.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified test/apply_fun.lean




## [2021-02-16 12:05:11](https://github.com/leanprover-community/mathlib/commit/d3c5667)
feat(number_theory/bernoulli): the odd Bernoulli numbers (greater than 1) are zero ([#6056](https://github.com/leanprover-community/mathlib/pull/6056))
The proof requires a ring homomorphism between power series to be defined, `eval_mul_hom` . This PR defines it and states some of its properties, along with the result that `e^(ax) * e^(bx) = e^((a + b) x)`, which is needed for the final result, `bernoulli_odd_eq_zero`.
#### Estimated changes
Modified src/number_theory/bernoulli.lean
- \+ *theorem* bernoulli_odd_eq_zero

Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.coeff_rescale
- \+ *lemma* power_series.eval_neg_hom_X
- \+ *lemma* power_series.rescale_neg_one_X
- \+ *lemma* power_series.rescale_one
- \+ *lemma* power_series.rescale_zero
- \+ *lemma* power_series.rescale_zero_apply

Modified src/ring_theory/power_series/well_known.lean
- \+ *theorem* power_series.exp_mul_exp_eq_exp_add
- \+ *theorem* power_series.exp_mul_exp_neg_eq_one



## [2021-02-16 12:05:10](https://github.com/leanprover-community/mathlib/commit/2da1ab4)
feat(data/equiv): Add lemmas to reduce `@finset.univ (perm (fin n.succ)) _` ([#5593](https://github.com/leanprover-community/mathlib/pull/5593))
The culmination of these lemmas is that `matrix.det` can now be reduced by a minimally steered simp:
```lean
import data.matrix.notation
import group_theory.perm.fin
import linear_algebra.determinant
open finset
example {α : Type} [comm_ring α] {a b c d : α} :
  matrix.det ![![a, b], ![c, d]] = a * d - b * c :=
begin
  simp [matrix.det, univ_perm_fin_succ, ←univ_product_univ, sum_product, fin.sum_univ_succ, fin.prod_univ_succ],
  ring
end
```
#### Estimated changes
Added src/data/equiv/option.lean
- \+ *lemma* equiv.option_symm_apply_none_iff
- \+ *def* equiv.remove_none
- \+ *lemma* equiv.remove_none_map_equiv
- \+ *lemma* equiv.remove_none_none
- \+ *lemma* equiv.remove_none_some
- \+ *lemma* equiv.remove_none_symm
- \+ *lemma* equiv.some_remove_none_iff

Modified src/data/matrix/notation.lean


Added src/group_theory/perm/fin.lean
- \+ *lemma* equiv.perm.decompose_fin.symm_sign
- \+ *def* equiv.perm.decompose_fin
- \+ *lemma* equiv.perm.decompose_fin_symm_apply_one
- \+ *lemma* equiv.perm.decompose_fin_symm_apply_succ
- \+ *lemma* equiv.perm.decompose_fin_symm_apply_zero
- \+ *lemma* equiv.perm.decompose_fin_symm_of_one
- \+ *lemma* equiv.perm.decompose_fin_symm_of_refl
- \+ *lemma* finset.univ_perm_fin_succ

Added src/group_theory/perm/option.lean
- \+ *def* equiv.perm.decompose_option
- \+ *lemma* equiv.perm.decompose_option_symm_of_none_apply
- \+ *lemma* equiv.perm.decompose_option_symm_sign
- \+ *lemma* equiv_functor.map_equiv_option_injective
- \+ *lemma* equiv_functor.option.map_none
- \+ *lemma* equiv_functor.option.sign
- \+ *lemma* finset.univ_perm_option
- \+ *lemma* map_equiv_option_one
- \+ *lemma* map_equiv_option_refl
- \+ *lemma* map_equiv_option_swap
- \+ *lemma* map_equiv_remove_none

Modified src/linear_algebra/determinant.lean


Modified test/matrix.lean




## [2021-02-16 09:30:21](https://github.com/leanprover-community/mathlib/commit/dc917df)
feat(category/limits/shapes/zero): lemmas about is_isomorphic 0 ([#6251](https://github.com/leanprover-community/mathlib/pull/6251))
#### Estimated changes
Modified src/category_theory/limits/shapes/zero.lean
- \+ *def* category_theory.limits.iso_of_is_isomorphic_zero
- \+ *lemma* category_theory.limits.zero_of_source_iso_zero'
- \+ *lemma* category_theory.limits.zero_of_target_iso_zero'



## [2021-02-16 09:30:20](https://github.com/leanprover-community/mathlib/commit/d7003c1)
feat(algebra/category/Module): allow writing (0 : Module R) ([#6249](https://github.com/leanprover-community/mathlib/pull/6249))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean




## [2021-02-16 09:30:19](https://github.com/leanprover-community/mathlib/commit/2961e79)
feat(topology/connected.lean): define pi_0 and prove basic properties ([#6188](https://github.com/leanprover-community/mathlib/pull/6188))
Define and prove basic properties of pi_0, the functor quotienting a space by its connected components. 
For dot notation convenience, this PR renames `subset_connected_component` to `is_preconnected.subset_connected_component` and also defines the weaker version `is_connected.subset_connected_component`.
#### Estimated changes
Modified src/topology/connected.lean
- \+ *lemma* connected_component_disjoint
- \+ *theorem* connected_component_eq
- \+ *lemma* connected_component_rel_iff
- \+ *def* connected_component_setoid
- \+ *lemma* continuous.image_connected_component_eq_singleton
- \+ *lemma* continuous.image_connected_component_subset
- \+ *lemma* continuous.image_eq_of_equiv
- \+ *def* continuous.pi0_lift
- \+ *lemma* continuous.pi0_lift_continuous
- \+ *lemma* continuous.pi0_lift_factors
- \+ *lemma* continuous.pi0_lift_unique
- \+ *def* continuous.pi0_map
- \+ *theorem* is_connected.subset_connected_component
- \+ *theorem* is_preconnected.subset_connected_component
- \+ *theorem* is_preconnected_connected_component
- \+ *def* pi0
- \+ *lemma* pi0_lift_unique'
- \+ *lemma* pi0_preimage_image
- \+ *lemma* pi0_preimage_singleton
- \+ *lemma* preimage_connected_component_connected
- \- *theorem* subset_connected_component
- \+ *lemma* totally_disconnected_space_iff_connected_component_singleton
- \+ *lemma* totally_disconnected_space_iff_connected_component_subsingleton

Modified src/topology/path_connected.lean


Modified src/topology/separation.lean




## [2021-02-16 08:09:48](https://github.com/leanprover-community/mathlib/commit/acf2b6d)
docs(algebraic_geometry/Scheme): fix typo in module docstring ([#6254](https://github.com/leanprover-community/mathlib/pull/6254))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean




## [2021-02-16 06:42:40](https://github.com/leanprover-community/mathlib/commit/dbe586c)
chore(scripts): update nolints.txt ([#6248](https://github.com/leanprover-community/mathlib/pull/6248))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-02-16 00:20:31](https://github.com/leanprover-community/mathlib/commit/97f7b52)
chore(data/logic/unique): there is a unique function with domain pempty ([#6243](https://github.com/leanprover-community/mathlib/pull/6243))
#### Estimated changes
Modified src/data/fin.lean


Modified src/logic/unique.lean




## [2021-02-15 21:04:25](https://github.com/leanprover-community/mathlib/commit/65fe78a)
feat(analysis/special_functions/trigonometric): add missing continuity attributes ([#6236](https://github.com/leanprover-community/mathlib/pull/6236))
I added continuity attributes to lemmas about the continuity of trigonometric functions, e.g. `continuous_sin`, `continuous_cos`, `continuous_tan`, etc. This came up in [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/What's.20new.20in.20Lean.20maths.3F/near/221511451)
I also added `real.continuous_tan`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.continuous_tan



## [2021-02-15 17:15:21](https://github.com/leanprover-community/mathlib/commit/0ed6f7c)
feat(data/real/liouville, topology/metric_space/basic): further preparations for Liouville ([#6201](https://github.com/leanprover-community/mathlib/pull/6201))
These lemmas are used to show that a Liouville number is transcendental.
The statement that Liouville numbers are transcendental is the next PR in this sequence!
#### Estimated changes
Modified src/data/real/liouville.lean
- \+ *lemma* exists_one_le_pow_mul_dist
- \+ *lemma* exists_pos_real_of_irrational_root
- \- *lemma* is_liouville.irrational
- \- *def* is_liouville
- \+ *lemma* liouville.irrational
- \+ *def* liouville

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.mem_Icc_iff_abs_le



## [2021-02-15 13:26:17](https://github.com/leanprover-community/mathlib/commit/26c6fb5)
chore(data/set/basic): set.union_univ and set.univ_union ([#6239](https://github.com/leanprover-community/mathlib/pull/6239))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.union_univ
- \+ *lemma* set.univ_union



## [2021-02-15 13:26:16](https://github.com/leanprover-community/mathlib/commit/d6db038)
refactor(analysis/normed_space/multilinear): use `≃ₗᵢ` for `curry` equivs ([#6232](https://github.com/leanprover-community/mathlib/pull/6232))
Also copy some `continuous_linear_equiv` API to `linear_isometry_equiv` (e.g., all API in `analysis.calculus.fderiv`).
#### Estimated changes
Modified src/analysis/analytic/inverse.lean


Modified src/analysis/analytic/linear.lean


Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* continuous_linear_equiv.comp_differentiable_at_iff
- \+/\- *lemma* continuous_linear_equiv.comp_differentiable_iff
- \+/\- *lemma* continuous_linear_equiv.comp_differentiable_on_iff
- \+/\- *lemma* continuous_linear_equiv.comp_differentiable_within_at_iff
- \+/\- *lemma* continuous_linear_equiv.comp_fderiv
- \+/\- *lemma* continuous_linear_equiv.comp_fderiv_within
- \+/\- *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff'
- \+/\- *lemma* continuous_linear_equiv.comp_has_fderiv_at_iff
- \+/\- *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff'
- \+/\- *lemma* continuous_linear_equiv.comp_has_fderiv_within_at_iff
- \+/\- *lemma* continuous_linear_equiv.comp_has_strict_fderiv_at_iff
- \+ *lemma* linear_isometry_equiv.comp_differentiable_at_iff
- \+ *lemma* linear_isometry_equiv.comp_differentiable_iff
- \+ *lemma* linear_isometry_equiv.comp_differentiable_on_iff
- \+ *lemma* linear_isometry_equiv.comp_differentiable_within_at_iff
- \+ *lemma* linear_isometry_equiv.comp_fderiv
- \+ *lemma* linear_isometry_equiv.comp_fderiv_within
- \+ *lemma* linear_isometry_equiv.comp_has_fderiv_at_iff'
- \+ *lemma* linear_isometry_equiv.comp_has_fderiv_at_iff
- \+ *lemma* linear_isometry_equiv.comp_has_fderiv_within_at_iff'
- \+ *lemma* linear_isometry_equiv.comp_has_fderiv_within_at_iff
- \+ *lemma* linear_isometry_equiv.comp_has_strict_fderiv_at_iff

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* continuous_linear_equiv.times_cont_diff
- \+ *lemma* linear_isometry_equiv.times_cont_diff
- \+ *lemma* linear_isometry_map.times_cont_diff

Modified src/analysis/normed_space/basic.lean
- \- *lemma* coe_norm
- \+ *lemma* submodule.norm_coe
- \+ *lemma* submodule.norm_mk

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_coe''
- \+ *lemma* linear_isometry_equiv.coe_coe'
- \+ *lemma* linear_isometry_equiv.coe_coe
- \- *lemma* linear_isometry_equiv.coe_symm_to_linear_equiv
- \+ *lemma* linear_isometry_equiv.coe_to_homeomorph
- \+ *lemma* linear_isometry_equiv.coe_to_isometric
- \+ *lemma* linear_isometry_equiv.comp_continuous_iff
- \+ *lemma* linear_isometry_equiv.comp_continuous_on_iff
- \+/\- *lemma* linear_isometry_equiv.diam_image
- \+/\- *lemma* linear_isometry_equiv.ediam_image
- \+/\- *lemma* linear_isometry_equiv.map_eq_iff
- \- *def* linear_isometry_equiv.to_continuous_linear_equiv
- \+ *def* linear_isometry_equiv.to_homeomorph
- \+ *lemma* linear_isometry_equiv.to_homeomorph_symm
- \+ *lemma* linear_isometry_equiv.to_isometric_symm
- \+ *lemma* linear_isometry_equiv.to_linear_equiv_symm

Modified src/analysis/normed_space/multilinear.lean
- \+/\- *def* continuous_multilinear_curry_fin0
- \- *lemma* continuous_multilinear_curry_fin0_apply_norm
- \- *def* continuous_multilinear_curry_fin0_aux
- \- *lemma* continuous_multilinear_curry_fin0_symm_apply_norm
- \+/\- *def* continuous_multilinear_curry_fin1
- \- *lemma* continuous_multilinear_curry_fin1_apply_norm
- \- *lemma* continuous_multilinear_curry_fin1_symm_apply_norm
- \- *def* continuous_multilinear_curry_left_equiv_aux
- \- *lemma* continuous_multilinear_curry_right_equiv_apply_norm
- \- *def* continuous_multilinear_curry_right_equiv_aux
- \- *lemma* continuous_multilinear_curry_right_equiv_symm_apply_norm
- \+/\- *lemma* continuous_multilinear_map.curry0_norm
- \+/\- *lemma* continuous_multilinear_map.uncurry0_norm

Modified src/geometry/manifold/instances/sphere.lean


Modified src/topology/algebra/module.lean
- \+/\- *def* continuous_linear_equiv.to_homeomorph

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry.comp_continuous_iff
- \+ *lemma* isometry.comp_continuous_on_iff



## [2021-02-15 13:26:15](https://github.com/leanprover-community/mathlib/commit/f5c55ae)
feat(analysis/normed_space/basic): uniform_continuous_norm ([#6162](https://github.com/leanprover-community/mathlib/pull/6162))
From `lean-liquid`
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* dist_zero_left
- \+ *lemma* lipschitz_with_one_norm
- \+/\- *lemma* real.norm_eq_abs
- \+ *lemma* uniform_continuous_nnnorm
- \+ *lemma* uniform_continuous_norm



## [2021-02-15 13:26:14](https://github.com/leanprover-community/mathlib/commit/0fa1312)
feat(linear_algebra/unitary_group): add unitary/orthogonal groups ([#5702](https://github.com/leanprover-community/mathlib/pull/5702))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.star_mul

Added src/linear_algebra/unitary_group.lean
- \+ *lemma* matrix.unitary_group.coe_to_GL
- \+ *def* matrix.unitary_group.embedding_GL
- \+ *lemma* matrix.unitary_group.ext
- \+ *lemma* matrix.unitary_group.ext_iff
- \+ *lemma* matrix.unitary_group.inv_apply
- \+ *lemma* matrix.unitary_group.inv_val
- \+ *lemma* matrix.unitary_group.mul_apply
- \+ *lemma* matrix.unitary_group.mul_val
- \+ *lemma* matrix.unitary_group.one_apply
- \+ *lemma* matrix.unitary_group.one_val
- \+ *lemma* matrix.unitary_group.star_mul_self
- \+ *def* matrix.unitary_group.to_GL
- \+ *lemma* matrix.unitary_group.to_GL_mul
- \+ *lemma* matrix.unitary_group.to_GL_one
- \+ *def* matrix.unitary_group.to_lin'
- \+ *lemma* matrix.unitary_group.to_lin'_mul
- \+ *lemma* matrix.unitary_group.to_lin'_one
- \+ *def* matrix.unitary_group.to_linear_equiv
- \+ *def* matrix.unitary_group
- \+ *lemma* matrix.unitary_submonoid.star_mem
- \+ *lemma* matrix.unitary_submonoid.star_mem_iff
- \+ *def* unitary_submonoid



## [2021-02-15 10:01:44](https://github.com/leanprover-community/mathlib/commit/9f0687c)
feat(order/liminf_limsup): liminf_nat_add and liminf_le_of_frequently_le' ([#6220](https://github.com/leanprover-community/mathlib/pull/6220))
Add `liminf_nat_add (f : ℕ → α) (k : ℕ) : at_top.liminf f = at_top.liminf (λ i, f (i + k))`. Same for `limsup`.
Add `liminf_le_of_frequently_le'`, variant of `liminf_le_of_frequently_le` in which the lattice is complete but there is no linear order. Same for `limsup`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* monotone.supr_nat_add
- \+ *lemma* supr_infi_ge_nat_add

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.le_limsup_of_frequently_le'
- \+ *lemma* filter.liminf_le_of_frequently_le'
- \+ *lemma* filter.liminf_nat_add
- \+ *lemma* filter.limsup_nat_add



## [2021-02-15 03:01:16](https://github.com/leanprover-community/mathlib/commit/1f0bf33)
chore(scripts): update nolints.txt ([#6234](https://github.com/leanprover-community/mathlib/pull/6234))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-15 03:01:15](https://github.com/leanprover-community/mathlib/commit/0469268)
doc(topology/subset_properties): minor change to docstring of `is_compact` ([#6231](https://github.com/leanprover-community/mathlib/pull/6231))
I'm learning (for the first time) about how to do topology with filters, and this docstring confused me for a second. If there are linguistic reasons for leaving it as it is then fair enough, but it wasn't clear to me on first reading that `a` was independent of the set in the filter.
#### Estimated changes
Modified src/topology/subset_properties.lean




## [2021-02-15 03:01:14](https://github.com/leanprover-community/mathlib/commit/5a6c893)
feat(topology/algebra/module): 2 new ext lemmas ([#6211](https://github.com/leanprover-community/mathlib/pull/6211))
Add ext lemmas for maps `f : M × M₂ →L[R] M₃` and `f : R →L[R] M`.
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/linear_algebra/prod.lean
- \+/\- *def* linear_map.inl
- \+/\- *def* linear_map.inr
- \+ *theorem* linear_map.prod_ext_iff

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.coe_inl
- \+ *lemma* continuous_linear_map.coe_inr
- \+ *theorem* continuous_linear_map.ext_ring
- \+ *theorem* continuous_linear_map.ext_ring_iff
- \+ *def* continuous_linear_map.inl
- \+ *lemma* continuous_linear_map.inl_apply
- \+ *def* continuous_linear_map.inr
- \+ *lemma* continuous_linear_map.inr_apply
- \+ *def* continuous_linear_map.prod_equiv
- \+ *lemma* continuous_linear_map.prod_ext
- \+ *lemma* continuous_linear_map.prod_ext_iff
- \+/\- *def* continuous_linear_map.prodₗ



## [2021-02-15 03:01:13](https://github.com/leanprover-community/mathlib/commit/c94577a)
feat(group_theory/free_abelian_group): add module doc and some equivs ([#6062](https://github.com/leanprover-community/mathlib/pull/6062))
Also add some API for `free_abelian_group.map`.
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *def* free_abelian_group.equiv_of_equiv
- \+ *lemma* free_abelian_group.map_comp
- \+ *lemma* free_abelian_group.map_comp_apply
- \+ *lemma* free_abelian_group.map_id
- \+ *lemma* free_abelian_group.map_id_apply
- \+ *lemma* free_abelian_group.map_of_apply
- \+ *def* free_abelian_group.punit_equiv



## [2021-02-14 23:17:58](https://github.com/leanprover-community/mathlib/commit/6f99407)
feat(analysis/calculus/inverse): a function with onto strict derivative is locally onto ([#6229](https://github.com/leanprover-community/mathlib/pull/6229))
Removes a useless assumption in `map_nhds_eq_of_complemented` (no need to have a completemented subspace).
The proof of the local inverse theorem breaks into two parts, local injectivity and local surjectivity. We refactor the local surjectivity part, assuming in the proof only that the derivative is onto. The result is stronger, but the proof is less streamlined since there is no contracting map any more: we give a naive proof from first principles instead of reducing to the fixed point theorem for contracting maps.
#### Estimated changes
Modified src/analysis/calculus/implicit.lean
- \- *lemma* has_strict_fderiv_at.map_nhds_eq
- \- *lemma* has_strict_fderiv_at.map_nhds_eq_of_complemented

Modified src/analysis/calculus/inverse.lean
- \+ *lemma* approximates_linear_on.image_mem_nhds
- \- *def* approximates_linear_on.inverse_approx_map
- \- *lemma* approximates_linear_on.inverse_approx_map_contracts_on
- \- *lemma* approximates_linear_on.inverse_approx_map_dist_self
- \- *lemma* approximates_linear_on.inverse_approx_map_dist_self_le
- \- *lemma* approximates_linear_on.inverse_approx_map_fixed_iff
- \- *lemma* approximates_linear_on.inverse_approx_map_maps_to
- \- *lemma* approximates_linear_on.inverse_approx_map_sub
- \+ *lemma* approximates_linear_on.map_nhds_eq
- \+ *lemma* approximates_linear_on.open_image
- \- *theorem* approximates_linear_on.surj_on_closed_ball
- \+ *theorem* approximates_linear_on.surj_on_closed_ball_of_nonlinear_right_inverse
- \+ *lemma* has_strict_fderiv_at.map_nhds_eq_of_surj

Modified src/analysis/normed_space/banach.lean
- \+ *lemma* continuous_linear_map.exists_nonlinear_right_inverse_of_surjective
- \+ *lemma* continuous_linear_map.nonlinear_right_inverse.bound
- \+ *lemma* continuous_linear_map.nonlinear_right_inverse.right_inv
- \+ *lemma* continuous_linear_map.nonlinear_right_inverse_of_surjective_nnnorm_pos

Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.subsingleton_iff



## [2021-02-14 19:41:17](https://github.com/leanprover-community/mathlib/commit/22b26d3)
chore(algebra/group/basic): remove three redundant lemmas ([#6197](https://github.com/leanprover-community/mathlib/pull/6197))
The following lemmas are changed in this PR (long list because of the additive versions:
* `mul_eq_left_iff` for `left_cancel_monoid` is renamed to `mul_right_eq_self` which previously was stated for `group`
* `add_eq_left_iff` the additive version is automatically renamed to `add_right_eq_self`
* `mul_eq_right_iff` for `right_cancel_monoid` is renamed to `mul_left_eq_self` which previously was stated for `group`
* `add_eq_right_iff` the additive version is automatically renamed to `add_left_eq_self`
* `left_eq_mul_iff` is renamed to `self_eq_mul_right` to fit the convention above
* `left_eq_add_iff` is renamed to `self_eq_add_right` to fit the convention above
* `right_eq_mul_iff` is renamed to `self_eq_mul_left` to fit the convention above
* `right_eq_add_iff` is renamed to `self_eq_add_left` to fit the convention above
* the duplicate `mul_left_eq_self` and `add_left_eq_self` for groups are removed
* the duplicate `mul_right_eq_self` and `add_right_eq_self` for groups are removed
* `mul_self_iff_eq_one` and `add_self_iff_eq_zero` deal only with the special case `a=b` of the other lemmas. It is therefore removed and the few instances in the library are replaced by one of the above. 
While I was at it, I provided a module doc for this file.
#### Estimated changes
Modified src/algebra/char_zero.lean


Modified src/algebra/group/basic.lean
- \- *lemma* left_eq_mul_iff
- \- *lemma* mul_eq_left_iff
- \- *lemma* mul_eq_right_iff
- \+/\- *lemma* mul_left_eq_self
- \+/\- *lemma* mul_right_eq_self
- \- *theorem* mul_self_iff_eq_one
- \- *lemma* right_eq_mul_iff
- \+ *lemma* self_eq_mul_left
- \+ *lemma* self_eq_mul_right

Modified src/algebra/group/hom.lean


Modified src/data/nat/parity.lean


Modified src/deprecated/group.lean


Modified src/ring_theory/derivation.lean


Modified src/topology/algebra/uniform_group.lean




## [2021-02-14 16:06:00](https://github.com/leanprover-community/mathlib/commit/c35672b)
feat(analysis/special_functions): strict differentiability of some functions ([#6228](https://github.com/leanprover-community/mathlib/pull/6228))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_strict_deriv_at.const_mul
- \+ *theorem* has_strict_deriv_at.const_sub
- \+ *lemma* has_strict_deriv_at.div
- \+ *theorem* has_strict_deriv_at.mul_const
- \+ *lemma* has_strict_deriv_at_iff_has_strict_fderiv_at

Modified src/analysis/complex/real_deriv.lean
- \+ *theorem* has_strict_deriv_at.real_of_complex

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* has_strict_deriv_at.cexp
- \+ *lemma* has_strict_fderiv_at.cexp

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.has_strict_deriv_at_cos
- \+ *lemma* complex.has_strict_deriv_at_cosh
- \+ *lemma* complex.has_strict_deriv_at_sin
- \+ *lemma* complex.has_strict_deriv_at_sinh
- \+ *lemma* complex.has_strict_deriv_at_tan
- \+ *lemma* has_strict_deriv_at.arctan
- \+ *lemma* has_strict_deriv_at.ccos
- \+ *lemma* has_strict_deriv_at.ccosh
- \+ *lemma* has_strict_deriv_at.cos
- \+ *lemma* has_strict_deriv_at.cosh
- \+ *lemma* has_strict_deriv_at.csin
- \+ *lemma* has_strict_deriv_at.csinh
- \+ *lemma* has_strict_deriv_at.sin
- \+ *lemma* has_strict_deriv_at.sinh
- \+ *lemma* has_strict_fderiv_at.arctan
- \+ *lemma* has_strict_fderiv_at.ccos
- \+ *lemma* has_strict_fderiv_at.ccosh
- \+ *lemma* has_strict_fderiv_at.cos
- \+ *lemma* has_strict_fderiv_at.cosh
- \+ *lemma* has_strict_fderiv_at.csin
- \+ *lemma* has_strict_fderiv_at.csinh
- \+ *lemma* has_strict_fderiv_at.sin
- \+ *lemma* has_strict_fderiv_at.sinh
- \+ *lemma* real.has_strict_deriv_at_arccos
- \+ *lemma* real.has_strict_deriv_at_arcsin
- \+ *lemma* real.has_strict_deriv_at_arctan
- \+ *lemma* real.has_strict_deriv_at_cos
- \+ *lemma* real.has_strict_deriv_at_cosh
- \+ *lemma* real.has_strict_deriv_at_sin
- \+ *lemma* real.has_strict_deriv_at_sinh
- \+ *lemma* real.has_strict_deriv_at_tan



## [2021-02-14 16:05:59](https://github.com/leanprover-community/mathlib/commit/713432f)
chore(.github/PULL_REQUEST_TEMPLATE.md): clarify instructions ([#6222](https://github.com/leanprover-community/mathlib/pull/6222))
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2021-02-14 14:16:51](https://github.com/leanprover-community/mathlib/commit/b9af22d)
fix(*): arsinh and complex.basic had module docs at the wrong position ([#6230](https://github.com/leanprover-community/mathlib/pull/6230))
This is fixed and the module doc for `complex.basic` is expanded slightly.
#### Estimated changes
Modified src/analysis/special_functions/arsinh.lean


Modified src/data/complex/basic.lean




## [2021-02-14 03:41:08](https://github.com/leanprover-community/mathlib/commit/c54a8d0)
chore(scripts): update nolints.txt ([#6227](https://github.com/leanprover-community/mathlib/pull/6227))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-14 01:28:45](https://github.com/leanprover-community/mathlib/commit/86e8a5d)
fix(data/real/basic): remove `decidable_le` field in `real.conditionally_complete_linear_order` ([#6223](https://github.com/leanprover-community/mathlib/pull/6223))
Because of this field, `@conditionally_complete_linear_order.to_linear_order ℝ real.conditionally_complete_linear_order` and `real.linear_order` were not defeq
See : https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Different.20linear.20orders.20on.20reals/near/226257434
Co-authored by @urkud
#### Estimated changes
Modified src/data/real/basic.lean




## [2021-02-13 22:35:47](https://github.com/leanprover-community/mathlib/commit/b0aae27)
feat(algebra/category/Group/adjunctions): free_group-forgetful adjunction ([#6190](https://github.com/leanprover-community/mathlib/pull/6190))
Furthermore, a module doc for `group_theory/free_group` is provided and a few lines in this file are split.
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean
- \+ *def* Group.adj
- \+ *def* Group.free

Modified src/group_theory/free_group.lean
- \+/\- *def* free_group.free_group_unit_equiv_int
- \+ *def* free_group.lift
- \+/\- *lemma* free_group.mul_bind
- \+/\- *theorem* free_group.reduce.not



## [2021-02-13 22:35:46](https://github.com/leanprover-community/mathlib/commit/07600ee)
feat(computability/epsilon_nfa): epsilon-NFA definition ([#6108](https://github.com/leanprover-community/mathlib/pull/6108))
#### Estimated changes
Added src/computability/epsilon_NFA.lean
- \+ *def* NFA.to_ε_NFA
- \+ *lemma* NFA.to_ε_NFA_correct
- \+ *lemma* NFA.to_ε_NFA_eval_from_match
- \+ *lemma* NFA.to_ε_NFA_ε_closure
- \+ *def* ε_NFA.accepts
- \+ *def* ε_NFA.eval
- \+ *def* ε_NFA.eval_from
- \+ *lemma* ε_NFA.pumping_lemma
- \+ *def* ε_NFA.step_set
- \+ *def* ε_NFA.to_NFA
- \+ *lemma* ε_NFA.to_NFA_correct
- \+ *lemma* ε_NFA.to_NFA_eval_from_match



## [2021-02-13 19:32:58](https://github.com/leanprover-community/mathlib/commit/ac19b4a)
refactor(measure_theory/l1_space): remove one of the two definitions of L1 space ([#6058](https://github.com/leanprover-community/mathlib/pull/6058))
Currently, we have two independent versions of the `L^1` space in mathlib: one coming from the general family of `L^p` spaces, the other one is an ad hoc construction based on the `integrable` predicate used in the construction of the Bochner integral.
We remove the second construction, and use instead the `L^1` space coming from the family of `L^p` spaces to construct the Bochner integral. Still, we keep the `integrable` predicate as it is generally useful, and show that it coincides with the `mem_Lp 1` predicate.
#### Estimated changes
Modified docs/overview.yaml


Modified src/analysis/convex/integral.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* coe_norm_subgroup

Modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* measure_theory.ae_eq_fun.ext_iff

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.L1.continuous_integral
- \+ *def* measure_theory.L1.integral
- \+ *lemma* measure_theory.L1.integral_add
- \+ *def* measure_theory.L1.integral_clm
- \+ *lemma* measure_theory.L1.integral_eq
- \+ *lemma* measure_theory.L1.integral_eq_integral
- \+ *lemma* measure_theory.L1.integral_eq_norm_pos_part_sub
- \+ *lemma* measure_theory.L1.integral_neg
- \+ *lemma* measure_theory.L1.integral_of_fun_eq_integral
- \+ *lemma* measure_theory.L1.integral_smul
- \+ *lemma* measure_theory.L1.integral_sub
- \+ *lemma* measure_theory.L1.integral_zero
- \+ *lemma* measure_theory.L1.norm_Integral_le_one
- \+ *lemma* measure_theory.L1.norm_eq_integral_norm
- \+ *lemma* measure_theory.L1.norm_integral_le
- \+ *lemma* measure_theory.L1.norm_of_fun_eq_integral_norm
- \+ *lemma* measure_theory.L1.simple_func.add_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.coe_add
- \+ *lemma* measure_theory.L1.simple_func.coe_coe
- \+ *lemma* measure_theory.L1.simple_func.coe_neg
- \+ *lemma* measure_theory.L1.simple_func.coe_neg_part
- \+ *lemma* measure_theory.L1.simple_func.coe_pos_part
- \+ *lemma* measure_theory.L1.simple_func.coe_smul
- \+ *lemma* measure_theory.L1.simple_func.coe_sub
- \+ *def* measure_theory.L1.simple_func.coe_to_L1
- \+ *lemma* measure_theory.L1.simple_func.coe_zero
- \+ *lemma* measure_theory.L1.simple_func.dist_eq
- \+ *lemma* measure_theory.L1.simple_func.dist_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.edist_eq
- \+ *def* measure_theory.L1.simple_func.integral
- \+ *lemma* measure_theory.L1.simple_func.integral_L1_eq_integral
- \+ *lemma* measure_theory.L1.simple_func.integral_add
- \+ *def* measure_theory.L1.simple_func.integral_clm
- \+ *lemma* measure_theory.L1.simple_func.integral_congr
- \+ *lemma* measure_theory.L1.simple_func.integral_eq_integral
- \+ *lemma* measure_theory.L1.simple_func.integral_eq_lintegral
- \+ *lemma* measure_theory.L1.simple_func.integral_eq_norm_pos_part_sub
- \+ *lemma* measure_theory.L1.simple_func.integral_smul
- \+ *lemma* measure_theory.L1.simple_func.lintegral_edist_to_simple_func_lt_top
- \+ *def* measure_theory.L1.simple_func.neg_part
- \+ *lemma* measure_theory.L1.simple_func.neg_part_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.neg_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.norm_Integral_le_one
- \+ *lemma* measure_theory.L1.simple_func.norm_eq
- \+ *lemma* measure_theory.L1.simple_func.norm_eq_integral
- \+ *lemma* measure_theory.L1.simple_func.norm_integral_le_norm
- \+ *lemma* measure_theory.L1.simple_func.norm_to_L1
- \+ *lemma* measure_theory.L1.simple_func.norm_to_simple_func
- \+ *def* measure_theory.L1.simple_func.pos_part
- \+ *lemma* measure_theory.L1.simple_func.pos_part_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.smul_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.sub_to_simple_func
- \+ *def* measure_theory.L1.simple_func.to_L1
- \+ *lemma* measure_theory.L1.simple_func.to_L1_add
- \+ *lemma* measure_theory.L1.simple_func.to_L1_eq_mk
- \+ *lemma* measure_theory.L1.simple_func.to_L1_eq_to_L1
- \+ *lemma* measure_theory.L1.simple_func.to_L1_neg
- \+ *lemma* measure_theory.L1.simple_func.to_L1_smul
- \+ *lemma* measure_theory.L1.simple_func.to_L1_sub
- \+ *lemma* measure_theory.L1.simple_func.to_L1_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.to_L1_zero
- \+ *def* measure_theory.L1.simple_func.to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.to_simple_func_eq_to_fun
- \+ *lemma* measure_theory.L1.simple_func.to_simple_func_to_L1
- \+ *lemma* measure_theory.L1.simple_func.zero_to_simple_func
- \+ *def* measure_theory.L1.simple_func
- \- *lemma* measure_theory.l1.continuous_integral
- \- *def* measure_theory.l1.integral
- \- *lemma* measure_theory.l1.integral_add
- \- *def* measure_theory.l1.integral_clm
- \- *lemma* measure_theory.l1.integral_eq
- \- *lemma* measure_theory.l1.integral_eq_integral
- \- *lemma* measure_theory.l1.integral_eq_norm_pos_part_sub
- \- *lemma* measure_theory.l1.integral_neg
- \- *lemma* measure_theory.l1.integral_of_fun_eq_integral
- \- *lemma* measure_theory.l1.integral_smul
- \- *lemma* measure_theory.l1.integral_sub
- \- *lemma* measure_theory.l1.integral_zero
- \- *lemma* measure_theory.l1.norm_Integral_le_one
- \- *lemma* measure_theory.l1.norm_eq_integral_norm
- \- *lemma* measure_theory.l1.norm_integral_le
- \- *lemma* measure_theory.l1.norm_of_fun_eq_integral_norm
- \- *lemma* measure_theory.l1.simple_func.add_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.coe_add
- \- *lemma* measure_theory.l1.simple_func.coe_coe
- \- *lemma* measure_theory.l1.simple_func.coe_neg
- \- *lemma* measure_theory.l1.simple_func.coe_neg_part
- \- *lemma* measure_theory.l1.simple_func.coe_pos_part
- \- *lemma* measure_theory.l1.simple_func.coe_smul
- \- *lemma* measure_theory.l1.simple_func.coe_sub
- \- *def* measure_theory.l1.simple_func.coe_to_l1
- \- *lemma* measure_theory.l1.simple_func.coe_zero
- \- *lemma* measure_theory.l1.simple_func.dist_eq
- \- *lemma* measure_theory.l1.simple_func.dist_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.edist_eq
- \- *def* measure_theory.l1.simple_func.integral
- \- *lemma* measure_theory.l1.simple_func.integral_add
- \- *def* measure_theory.l1.simple_func.integral_clm
- \- *lemma* measure_theory.l1.simple_func.integral_congr
- \- *lemma* measure_theory.l1.simple_func.integral_eq_integral
- \- *lemma* measure_theory.l1.simple_func.integral_eq_lintegral
- \- *lemma* measure_theory.l1.simple_func.integral_eq_norm_pos_part_sub
- \- *lemma* measure_theory.l1.simple_func.integral_l1_eq_integral
- \- *lemma* measure_theory.l1.simple_func.integral_smul
- \- *lemma* measure_theory.l1.simple_func.lintegral_edist_to_simple_func_lt_top
- \- *def* measure_theory.l1.simple_func.neg_part
- \- *lemma* measure_theory.l1.simple_func.neg_part_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.neg_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.norm_Integral_le_one
- \- *lemma* measure_theory.l1.simple_func.norm_eq'
- \- *lemma* measure_theory.l1.simple_func.norm_eq
- \- *lemma* measure_theory.l1.simple_func.norm_eq_integral
- \- *lemma* measure_theory.l1.simple_func.norm_integral_le_norm
- \- *lemma* measure_theory.l1.simple_func.norm_of_simple_func
- \- *lemma* measure_theory.l1.simple_func.norm_to_simple_func
- \- *def* measure_theory.l1.simple_func.of_simple_func
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_add
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_eq_mk
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_eq_of_fun
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_neg
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_smul
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_sub
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.of_simple_func_zero
- \- *def* measure_theory.l1.simple_func.pos_part
- \- *lemma* measure_theory.l1.simple_func.pos_part_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.smul_to_simple_func
- \- *lemma* measure_theory.l1.simple_func.sub_to_simple_func
- \- *def* measure_theory.l1.simple_func.to_simple_func
- \- *lemma* measure_theory.l1.simple_func.to_simple_func_eq_to_fun
- \- *lemma* measure_theory.l1.simple_func.to_simple_func_of_simple_func
- \- *lemma* measure_theory.l1.simple_func.zero_to_simple_func
- \- *def* measure_theory.l1.simple_func
- \+ *lemma* measure_theory.tendsto_integral_of_L1
- \- *lemma* measure_theory.tendsto_integral_of_l1

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.L1.ae_measurable_coe_fn
- \+ *lemma* measure_theory.L1.dist_def
- \+ *lemma* measure_theory.L1.edist_def
- \+ *lemma* measure_theory.L1.has_finite_integral_coe_fn
- \+ *lemma* measure_theory.L1.integrable_coe_fn
- \+ *lemma* measure_theory.L1.measurable_coe_fn
- \+ *lemma* measure_theory.L1.norm_def
- \+ *lemma* measure_theory.L1.norm_sub_eq_lintegral
- \+ *lemma* measure_theory.L1.of_real_norm_eq_lintegral
- \+ *lemma* measure_theory.L1.of_real_norm_sub_eq_lintegral
- \+/\- *def* measure_theory.ae_eq_fun.integrable
- \+ *lemma* measure_theory.ae_eq_fun.integrable_iff_mem_L1
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable_zero
- \+ *lemma* measure_theory.integrable.coe_fn_to_L1
- \+ *lemma* measure_theory.integrable.edist_to_L1_to_L1
- \+ *lemma* measure_theory.integrable.edist_to_L1_zero
- \+ *lemma* measure_theory.integrable.norm_to_L1
- \+ *lemma* measure_theory.integrable.norm_to_L1_eq_lintegral_norm
- \+ *def* measure_theory.integrable.to_L1
- \+ *lemma* measure_theory.integrable.to_L1_add
- \+ *lemma* measure_theory.integrable.to_L1_coe_fn
- \+ *lemma* measure_theory.integrable.to_L1_eq_mk
- \+ *lemma* measure_theory.integrable.to_L1_eq_to_L1_iff
- \+ *lemma* measure_theory.integrable.to_L1_neg
- \+ *lemma* measure_theory.integrable.to_L1_smul
- \+ *lemma* measure_theory.integrable.to_L1_sub
- \+ *lemma* measure_theory.integrable.to_L1_zero
- \- *lemma* measure_theory.l1.add_to_fun
- \- *lemma* measure_theory.l1.coe_add
- \- *lemma* measure_theory.l1.coe_coe
- \- *lemma* measure_theory.l1.coe_neg
- \- *lemma* measure_theory.l1.coe_pos_part
- \- *lemma* measure_theory.l1.coe_smul
- \- *lemma* measure_theory.l1.coe_sub
- \- *lemma* measure_theory.l1.coe_zero
- \- *lemma* measure_theory.l1.continuous_neg_part
- \- *lemma* measure_theory.l1.continuous_pos_part
- \- *lemma* measure_theory.l1.dist_eq
- \- *lemma* measure_theory.l1.dist_to_fun
- \- *lemma* measure_theory.l1.edist_eq
- \- *lemma* measure_theory.l1.integrable_norm
- \- *lemma* measure_theory.l1.lintegral_edist_to_fun_lt_top
- \- *lemma* measure_theory.l1.measurable_norm
- \- *lemma* measure_theory.l1.mk_to_fun
- \- *def* measure_theory.l1.neg_part
- \- *lemma* measure_theory.l1.neg_part_to_fun_eq_max
- \- *lemma* measure_theory.l1.neg_part_to_fun_eq_min
- \- *lemma* measure_theory.l1.neg_to_fun
- \- *lemma* measure_theory.l1.norm_eq
- \- *lemma* measure_theory.l1.norm_eq_lintegral
- \- *lemma* measure_theory.l1.norm_eq_nnnorm_to_fun
- \- *lemma* measure_theory.l1.norm_eq_norm_to_fun
- \- *lemma* measure_theory.l1.norm_le_norm_of_ae_le
- \- *lemma* measure_theory.l1.norm_of_fun
- \- *lemma* measure_theory.l1.norm_of_fun_eq_lintegral_norm
- \- *lemma* measure_theory.l1.norm_sub_eq_lintegral
- \- *def* measure_theory.l1.of_fun
- \- *lemma* measure_theory.l1.of_fun_add
- \- *lemma* measure_theory.l1.of_fun_eq_mk
- \- *lemma* measure_theory.l1.of_fun_eq_of_fun
- \- *lemma* measure_theory.l1.of_fun_neg
- \- *lemma* measure_theory.l1.of_fun_smul
- \- *lemma* measure_theory.l1.of_fun_sub
- \- *lemma* measure_theory.l1.of_fun_to_fun
- \- *lemma* measure_theory.l1.of_fun_zero
- \- *lemma* measure_theory.l1.of_real_norm_eq_lintegral
- \- *lemma* measure_theory.l1.of_real_norm_sub_eq_lintegral
- \- *def* measure_theory.l1.pos_part
- \- *lemma* measure_theory.l1.pos_part_to_fun
- \- *lemma* measure_theory.l1.smul_to_fun
- \- *lemma* measure_theory.l1.sub_to_fun
- \- *lemma* measure_theory.l1.to_fun_of_fun
- \- *lemma* measure_theory.l1.zero_to_fun
- \- *def* measure_theory.l1
- \+ *lemma* measure_theory.mem_ℒp.integrable
- \+ *lemma* measure_theory.mem_ℒp_one_iff_integrable

Modified src/measure_theory/prod.lean


Modified src/measure_theory/set_integral.lean
- \- *def* continuous_linear_map.comp_l1
- \- *def* continuous_linear_map.comp_l1L
- \- *lemma* continuous_linear_map.comp_l1_apply
- \- *def* continuous_linear_map.comp_l1ₗ
- \+ *lemma* continuous_linear_map.continuous_integral_comp_L1
- \- *lemma* continuous_linear_map.continuous_integral_comp_l1
- \- *lemma* continuous_linear_map.integrable_comp_l1
- \+ *lemma* continuous_linear_map.integral_comp_L1_comm
- \+ *lemma* continuous_linear_map.integral_comp_Lp
- \- *lemma* continuous_linear_map.integral_comp_l1
- \- *lemma* continuous_linear_map.integral_comp_l1_comm
- \- *lemma* continuous_linear_map.measurable_comp_l1
- \- *lemma* continuous_linear_map.norm_comp_l1_apply_le
- \- *lemma* continuous_linear_map.norm_comp_l1_le
- \- *lemma* continuous_linear_map.norm_compl1L_le

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_L1_edist
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_l1_edist
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_edist
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1_edist

Modified src/order/galois_connection.lean




## [2021-02-13 17:23:27](https://github.com/leanprover-community/mathlib/commit/ad5a81d)
chore(measure_theory/measure_space): add some `simp`/`mono` tags ([#6221](https://github.com/leanprover-community/mathlib/pull/6221))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.ae_eq_empty
- \+/\- *lemma* measure_theory.measure_mono_ae
- \+/\- *lemma* measure_theory.union_ae_eq_right



## [2021-02-13 14:34:16](https://github.com/leanprover-community/mathlib/commit/3cfaa0b)
feat(measure_theory/measure_space): add ae_imp_iff ([#6218](https://github.com/leanprover-community/mathlib/pull/6218))
This is `filter.eventually_imp_distrib_left` specialized to the measure.ae filter.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_imp_iff
- \+/\- *lemma* measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict



## [2021-02-13 12:18:12](https://github.com/leanprover-community/mathlib/commit/d0456d3)
feat(measure_theory/borel_space): add ae_measurable versions of finset.measurable_prod and measurable.ennreal_tsum ([#6217](https://github.com/leanprover-community/mathlib/pull/6217))
Also add an ae_measurable version of `ae_lt_top`.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.ennreal_tsum
- \+ *lemma* finset.ae_measurable_prod

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.ae_lt_top'



## [2021-02-13 12:18:11](https://github.com/leanprover-community/mathlib/commit/42bb0c4)
feat(ring_theory/ideal/operations): add first isomorphism theorem for rings and algebras ([#6166](https://github.com/leanprover-community/mathlib/pull/6166))
The first isomorphism theorem for commutative rings `quotient_ker_equiv_of_surjective` and algebras `quotient_ker_alg_equiv_of_surjective`.
#### Estimated changes
Modified docs/overview.yaml


Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.ker_lift.map_smul
- \+ *def* ideal.ker_lift_alg
- \+ *lemma* ideal.ker_lift_alg_injective
- \+ *lemma* ideal.ker_lift_alg_mk
- \+ *lemma* ideal.ker_lift_alg_to_ring_hom
- \+ *lemma* ideal.quotient_ker_alg_equiv_of_right_inverse.apply
- \+ *def* ideal.quotient_ker_alg_equiv_of_right_inverse
- \+ *lemma* ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply
- \+ *def* ring_hom.ker_lift
- \+ *lemma* ring_hom.ker_lift_injective
- \+ *lemma* ring_hom.ker_lift_mk
- \+ *lemma* ring_hom.quotient_ker_equiv_of_right_inverse.apply
- \+ *lemma* ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply
- \+ *def* ring_hom.quotient_ker_equiv_of_right_inverse



## [2021-02-13 12:18:10](https://github.com/leanprover-community/mathlib/commit/8b59d97)
feat(linear_algebra/pi_tensor_product): tmul distributes over tprod ([#6126](https://github.com/leanprover-community/mathlib/pull/6126))
This adds the equivalence `(⨂[R] i : ι, M) ⊗[R] (⨂[R] i : ι₂, M) ≃ₗ[R] ⨂[R] i : ι ⊕ ι₂, M`.
Working with dependently-typed `M` here is more trouble than it's worth, as we don't have any typeclass structures on `sum.elim M N` right now,
This is one of the pieces needed to provide a ring structure on `⨁ n, ⨂[R] i : fin n, M`, but that's left for another time.
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean
- \+ *def* pi_tensor_product.tmul_equiv
- \+ *lemma* pi_tensor_product.tmul_equiv_apply
- \+ *lemma* pi_tensor_product.tmul_equiv_symm_apply



## [2021-02-13 09:47:57](https://github.com/leanprover-community/mathlib/commit/445e6fc)
refactor(topology/{basic,continuous_on}): review `continuous_if` etc ([#6182](https://github.com/leanprover-community/mathlib/pull/6182))
* move `continuous_if` to `topology/continuous_on`, use weaker assumptions;
* add `piecewise` versions of various `if` lemmas;
* add a specialized `continuous_if_le` version;
* use dot notation for `continuous_on.if` and `continuous_on.if'`;
* minor golfing here and there.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto.if
- \+ *lemma* filter.tendsto.piecewise
- \- *lemma* filter.tendsto_if

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.if_le
- \+ *lemma* continuous_if_le

Modified src/topology/basic.lean
- \- *lemma* continuous_if

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous.if
- \+ *lemma* continuous.piecewise
- \+/\- *lemma* continuous_if'
- \+ *lemma* continuous_if
- \+ *lemma* continuous_on.if'
- \+ *lemma* continuous_on.if
- \+ *lemma* continuous_on.piecewise'
- \+ *lemma* continuous_on.piecewise
- \- *lemma* continuous_on_if'
- \- *lemma* continuous_on_if
- \+ *lemma* continuous_piecewise
- \+ *theorem* filter.tendsto.if_nhds_within
- \+ *theorem* filter.tendsto.piecewise_nhds_within
- \+ *lemma* is_open_inter_union_inter_compl'
- \+ *lemma* is_open_inter_union_inter_compl
- \- *theorem* tendsto_if_nhds_within

Modified src/topology/order.lean
- \+ *lemma* is_open_iff_continuous_mem

Modified src/topology/path_connected.lean




## [2021-02-13 09:47:56](https://github.com/leanprover-community/mathlib/commit/5c22531)
doc(data/polynomial/denoms_clearable): fix typo in the doc-string ([#6174](https://github.com/leanprover-community/mathlib/pull/6174))
#### Estimated changes
Modified src/data/polynomial/denoms_clearable.lean




## [2021-02-13 07:17:57](https://github.com/leanprover-community/mathlib/commit/5bee826)
feat(data/int/gcd): some missing lemmas about int.gcd ([#6212](https://github.com/leanprover-community/mathlib/pull/6212))
As requested [on zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/different.20gcd's.3F/near/226203698).
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *def* int.gcd_a
- \+ *def* int.gcd_b
- \+ *theorem* int.gcd_eq_gcd_ab

Modified src/data/int/modeq.lean


Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.nat_abs_euclidean_domain_gcd



## [2021-02-13 07:17:56](https://github.com/leanprover-community/mathlib/commit/0544641)
chore(analysis/special_functions/pow): review lemmas about measurability of `cpow`/`rpow` ([#6209](https://github.com/leanprover-community/mathlib/pull/6209))
* prove that `complex.cpow` is measurable;
* deduce measurability of `real.rpow` from definition, not continuity.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* measurable.cpow
- \+/\- *lemma* measurable.ennreal_rpow
- \+/\- *lemma* measurable.ennreal_rpow_const
- \+/\- *lemma* measurable.nnreal_rpow
- \+/\- *lemma* measurable.nnreal_rpow_const
- \- *lemma* nnreal.measurable_rpow
- \- *lemma* nnreal.measurable_rpow_const
- \- *lemma* real.measurable_rpow

Modified src/analysis/special_functions/trigonometric.lean


Modified src/measure_theory/borel_space.lean




## [2021-02-13 07:17:55](https://github.com/leanprover-community/mathlib/commit/ee9197a)
chore(topology/algebra/module): review `coe` lemmas ([#6206](https://github.com/leanprover-community/mathlib/pull/6206))
* add `@[simp]` to `continuous_linear_equiv.coe_coe`, remove from `continuous_linear_equiv.coe_apply`;
* golf `continuous_linear_equiv.ext`;
* given `(e e' : M ≃L[R] M₂)`, simplify `(e : M →L[R] M₂) = e'` to `e = e'`;
* add `@[simp]` to `continuous_linear_equiv.symm_comp_self` and `continuous_linear_equiv.self_comp_symm`;
* drop `symm_comp_self'` and `self_comp_symm'`: now `coe_coe` simplifies LHS to `symm_comp_self`/`self_comp_symm`;
* `continuous_linear_equiv.coord` is no longer an `abbreviation`: without this change `coe_coe` prevents us from using lemmas about `coord`;
#### Estimated changes
Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.coe_to_span_nonzero_singleton_symm
- \+ *def* continuous_linear_equiv.coord
- \+/\- *lemma* continuous_linear_equiv.coord_norm
- \+/\- *lemma* continuous_linear_equiv.coord_self
- \+ *lemma* continuous_linear_equiv.coord_to_span_nonzero_singleton
- \+ *lemma* continuous_linear_equiv.to_span_nonzero_singleton_coord

Modified src/topology/algebra/module.lean
- \+/\- *theorem* continuous_linear_equiv.coe_apply
- \+/\- *lemma* continuous_linear_equiv.coe_coe
- \+ *lemma* continuous_linear_equiv.coe_inj
- \+ *lemma* continuous_linear_equiv.coe_injective
- \- *lemma* continuous_linear_equiv.self_comp_symm'
- \+/\- *lemma* continuous_linear_equiv.self_comp_symm
- \- *lemma* continuous_linear_equiv.symm_comp_self'
- \+/\- *lemma* continuous_linear_equiv.symm_comp_self
- \+ *lemma* continuous_linear_equiv.to_linear_equiv_injective



## [2021-02-13 07:17:54](https://github.com/leanprover-community/mathlib/commit/43bfd90)
chore(group_theory/free_group): clean up unnecessary lemmas ([#6200](https://github.com/leanprover-community/mathlib/pull/6200))
This removes:
* `free_abelian_group.lift.{add,sub,neg,zero}` as these exist already as `(free_abelian_group.lift _).map_{add,sub,neg,zero}` 
* `free_group.to_group.{mul,one,inv}` as these exist already as `(free_group.to_group _).map_{mul,one,inv}`
* `free_group.map.{mul,one,inv}` as these exist already as `(free_group.map _).map_{mul,one,inv}`
* `free_group.prod.{mul,one,inv}` as these exist already as `free_group.prod.map_{mul,one,inv}`
* `to_group.is_group_hom` as this is provided automatically for `monoid_hom`s
and renames
* `free_group.sum.{mul,one,inv}` to `free_group.sum.map_{mul,one,inv}`
These lemmas are already simp lemmas thanks to the functions they relate to being bundled homs.
While the new spelling is slightly longer, it makes it clear that the entire set of `monoid_hom` lemmas apply, not just the three that were copied across.
This also wraps some lines to make the linter happier about these files.
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean
- \- *lemma* free_group.map.inv
- \- *lemma* free_group.map.mul
- \- *lemma* free_group.map.one
- \+/\- *theorem* free_group.map.unique
- \- *lemma* free_group.prod.inv
- \- *lemma* free_group.prod.mul
- \- *lemma* free_group.prod.one
- \- *lemma* free_group.sum.inv
- \+ *lemma* free_group.sum.map_inv
- \+ *lemma* free_group.sum.map_mul
- \+ *lemma* free_group.sum.map_one
- \- *lemma* free_group.sum.mul
- \- *lemma* free_group.sum.one
- \- *lemma* free_group.to_group.inv
- \- *lemma* free_group.to_group.mul
- \- *lemma* free_group.to_group.one

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean




## [2021-02-13 05:21:53](https://github.com/leanprover-community/mathlib/commit/759ebc0)
chore(analysis/calculus/local_extr): minor golfing ([#6214](https://github.com/leanprover-community/mathlib/pull/6214))
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean




## [2021-02-13 03:56:07](https://github.com/leanprover-community/mathlib/commit/5869039)
chore(scripts): update nolints.txt ([#6213](https://github.com/leanprover-community/mathlib/pull/6213))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-13 00:49:42](https://github.com/leanprover-community/mathlib/commit/37459ee)
doc(docs/overview.yaml): Added Hall's theorem ([#6205](https://github.com/leanprover-community/mathlib/pull/6205))
Also fixed module documentation to use inline math mode (and removed the dreaded "any").
#### Estimated changes
Modified docs/overview.yaml


Modified src/combinatorics/hall.lean




## [2021-02-13 00:49:41](https://github.com/leanprover-community/mathlib/commit/06fdc08)
chore(algebra/group/pi): replace a lemma with @[simps] ([#6203](https://github.com/leanprover-community/mathlib/pull/6203))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *def* add_monoid_hom.single
- \- *lemma* add_monoid_hom.single_apply



## [2021-02-13 00:49:40](https://github.com/leanprover-community/mathlib/commit/e79bf05)
feat(number_theory/ADE_inequality): the inequality 1/p + 1/q + 1/r > 1 ([#6156](https://github.com/leanprover-community/mathlib/pull/6156))
#### Estimated changes
Added src/number_theory/ADE_inequality.lean
- \+ *def* ADE_inequality.A'
- \+ *def* ADE_inequality.A
- \+ *def* ADE_inequality.D'
- \+ *def* ADE_inequality.E'
- \+ *def* ADE_inequality.E6
- \+ *def* ADE_inequality.E7
- \+ *def* ADE_inequality.E8
- \+ *lemma* ADE_inequality.admissible.one_lt_sum_inv
- \+ *def* ADE_inequality.admissible
- \+ *lemma* ADE_inequality.admissible_A'
- \+ *lemma* ADE_inequality.admissible_D'
- \+ *lemma* ADE_inequality.admissible_E'3
- \+ *lemma* ADE_inequality.admissible_E'4
- \+ *lemma* ADE_inequality.admissible_E'5
- \+ *lemma* ADE_inequality.admissible_E6
- \+ *lemma* ADE_inequality.admissible_E7
- \+ *lemma* ADE_inequality.admissible_E8
- \+ *lemma* ADE_inequality.admissible_of_one_lt_sum_inv
- \+ *lemma* ADE_inequality.admissible_of_one_lt_sum_inv_aux'
- \+ *lemma* ADE_inequality.admissible_of_one_lt_sum_inv_aux
- \+ *lemma* ADE_inequality.classification
- \+ *lemma* ADE_inequality.lt_four
- \+ *lemma* ADE_inequality.lt_six
- \+ *lemma* ADE_inequality.lt_three
- \+ *def* ADE_inequality.sum_inv
- \+ *lemma* ADE_inequality.sum_inv_pqr



## [2021-02-13 00:49:38](https://github.com/leanprover-community/mathlib/commit/30c2c5b)
feat(data/fin): cast_succ_mk and other lemmas ([#6094](https://github.com/leanprover-community/mathlib/pull/6094))
* add lemmas for all the `fin.cast_*` functions which describe what happens to an "explicitly presented" term of `fin n`, built from the constructor
* fixes some errors in doc-strings
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/data/fin.lean
- \+ *lemma* fin.cast_add_mk
- \+ *lemma* fin.cast_le_mk
- \+ *lemma* fin.cast_lt_mk
- \+ *lemma* fin.cast_mk
- \+ *lemma* fin.cast_succ_mk
- \+ *lemma* fin.succ_mk



## [2021-02-13 00:49:36](https://github.com/leanprover-community/mathlib/commit/152ad1f)
feat(measure_theory/measure_space): add theorems about restrict and subtraction ([#5000](https://github.com/leanprover-community/mathlib/pull/5000))
This is the next tranche of theorems toward Lebesgue-Radon-Nikodym.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_apply_self
- \+ *lemma* measure_theory.measure.restrict_eq_self
- \+ *lemma* measure_theory.measure.restrict_sub_eq_restrict_sub_restrict
- \+ *lemma* measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict



## [2021-02-12 21:14:37](https://github.com/leanprover-community/mathlib/commit/dd13f00)
feat(data/set/intervals/basic): 24 lemmas about membership of arithmetic operations ([#6202](https://github.com/leanprover-community/mathlib/pull/6202))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.add_mem_Icc_iff_left
- \+ *lemma* set.add_mem_Icc_iff_right
- \+ *lemma* set.add_mem_Ico_iff_left
- \+ *lemma* set.add_mem_Ico_iff_right
- \+ *lemma* set.add_mem_Ioc_iff_left
- \+ *lemma* set.add_mem_Ioc_iff_right
- \+ *lemma* set.add_mem_Ioo_iff_left
- \+ *lemma* set.add_mem_Ioo_iff_right
- \+ *lemma* set.inv_mem_Icc_iff
- \+ *lemma* set.inv_mem_Ico_iff
- \+ *lemma* set.inv_mem_Ioc_iff
- \+ *lemma* set.inv_mem_Ioo_iff
- \+ *lemma* set.sub_mem_Icc_iff_left
- \+ *lemma* set.sub_mem_Icc_iff_right
- \+ *lemma* set.sub_mem_Ico_iff_left
- \+ *lemma* set.sub_mem_Ico_iff_right
- \+ *lemma* set.sub_mem_Ioc_iff_left
- \+ *lemma* set.sub_mem_Ioc_iff_right
- \+ *lemma* set.sub_mem_Ioo_iff_left
- \+ *lemma* set.sub_mem_Ioo_iff_right



## [2021-02-12 14:15:57](https://github.com/leanprover-community/mathlib/commit/254c3ee)
feat(analysis/special_functions/exp_log): added `log_div` ([#6196](https://github.com/leanprover-community/mathlib/pull/6196))
`∀ x y : ℝ, x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y`
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.log_div



## [2021-02-12 14:15:56](https://github.com/leanprover-community/mathlib/commit/a5ccba6)
feat(analysis/calculus): generalize `has_strict_fderiv_at.map_nhds_eq` ([#6193](https://github.com/leanprover-community/mathlib/pull/6193))
Generalize `has_strict_fderiv_at.map_nhds_eq` to a function that satisfies assumptions of the implicit function theorem.
#### Estimated changes
Modified src/analysis/calculus/implicit.lean
- \+ *lemma* has_strict_fderiv_at.implicit_function_apply_image
- \+ *lemma* has_strict_fderiv_at.implicit_function_of_complemented_apply_image
- \+ *lemma* has_strict_fderiv_at.map_nhds_eq
- \+ *lemma* has_strict_fderiv_at.map_nhds_eq_of_complemented
- \+ *lemma* has_strict_fderiv_at.tendsto_implicit_function
- \+ *lemma* implicit_function_data.map_nhds_eq

Modified src/analysis/calculus/inverse.lean
- \- *lemma* has_strict_fderiv_at.map_nhds_eq
- \+ *lemma* has_strict_fderiv_at.map_nhds_eq_of_equiv
- \- *lemma* open_map_of_strict_fderiv
- \+ *lemma* open_map_of_strict_fderiv_equiv



## [2021-02-12 12:44:07](https://github.com/leanprover-community/mathlib/commit/74d3270)
fix(topology/topological_fiber_bundle): fix definition, review ([#6184](https://github.com/leanprover-community/mathlib/pull/6184))
* fix definition of `is_topological_fiber_bundle`;
* add `is_trivial_topological_fiber_bundle`;
* more lemmas, golf here and there;
* define induced fiber bundle.
#### Estimated changes
Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.apply_symm_apply'
- \+ *lemma* bundle_trivialization.apply_symm_apply
- \+/\- *lemma* bundle_trivialization.coe_coe
- \+ *lemma* bundle_trivialization.coe_fst'
- \+ *lemma* bundle_trivialization.coe_fst_eventually_eq_proj'
- \+ *lemma* bundle_trivialization.coe_fst_eventually_eq_proj
- \+/\- *lemma* bundle_trivialization.coe_mk
- \+ *def* bundle_trivialization.comp_homeomorph
- \+ *lemma* bundle_trivialization.map_proj_nhds
- \+ *lemma* bundle_trivialization.mem_source
- \+ *lemma* bundle_trivialization.mem_target
- \+ *lemma* bundle_trivialization.proj_symm_apply'
- \+ *lemma* bundle_trivialization.proj_symm_apply
- \+ *lemma* bundle_trivialization.symm_apply_mk_proj
- \+ *lemma* is_topological_fiber_bundle.comap
- \+ *lemma* is_topological_fiber_bundle.comp_homeomorph
- \+/\- *def* is_topological_fiber_bundle
- \+ *lemma* is_trivial_topological_fiber_bundle.is_topological_fiber_bundle
- \+ *def* is_trivial_topological_fiber_bundle
- \+ *lemma* is_trivial_topological_fiber_bundle_fst
- \+ *lemma* is_trivial_topological_fiber_bundle_snd
- \- *theorem* topological_fiber_bundle_core.is_topological_fiber_bundle



## [2021-02-12 10:09:14](https://github.com/leanprover-community/mathlib/commit/2d70880)
feat(topology/subset_properties): compact discrete spaces are finite ([#6191](https://github.com/leanprover-community/mathlib/pull/6191))
From `lean-liquid`
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* finite_of_is_compact_of_discrete
- \+ *def* fintype_of_compact_of_discrete



## [2021-02-12 02:51:33](https://github.com/leanprover-community/mathlib/commit/159e807)
chore(scripts): update nolints.txt ([#6194](https://github.com/leanprover-community/mathlib/pull/6194))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-12 02:51:32](https://github.com/leanprover-community/mathlib/commit/72141fd)
feat(combinatorics/hall): Hall's marriage theorem ([#5695](https://github.com/leanprover-community/mathlib/pull/5695))
We state and prove Hall's marriage theorem with respect to fintypes and relations. 
Coauthor: @b-mehta @kmill
#### Estimated changes
Modified docs/references.bib


Added src/combinatorics/hall.lean
- \+ *theorem* finset.all_card_le_bUnion_card_iff_exists_injective
- \+ *theorem* fintype.all_card_le_filter_rel_iff_exists_injective
- \+ *theorem* fintype.all_card_le_rel_image_card_iff_exists_injective
- \+ *lemma* hall_marriage_theorem.hall_cond_of_compl
- \+ *lemma* hall_marriage_theorem.hall_cond_of_erase
- \+ *lemma* hall_marriage_theorem.hall_cond_of_restrict
- \+ *theorem* hall_marriage_theorem.hall_hard_inductive
- \+ *theorem* hall_marriage_theorem.hall_hard_inductive_step
- \+ *lemma* hall_marriage_theorem.hall_hard_inductive_step_A
- \+ *lemma* hall_marriage_theorem.hall_hard_inductive_step_B
- \+ *theorem* hall_marriage_theorem.hall_hard_inductive_zero

Modified src/data/set/finite.lean
- \+ *lemma* set.card_ne_eq
- \+ *lemma* set.to_finset_ne_eq_erase



## [2021-02-11 23:33:03](https://github.com/leanprover-community/mathlib/commit/db305fb)
feat(data/set/finite): fintype_of_univ_finite ([#6164](https://github.com/leanprover-community/mathlib/pull/6164))
From `lean-liquid`
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *def* set.fintype_of_univ_finite
- \+ *lemma* set.univ_finite_iff_nonempty_fintype



## [2021-02-11 23:33:02](https://github.com/leanprover-community/mathlib/commit/2f56620)
feat(data/real/irrational): define Liouville numbers ([#6158](https://github.com/leanprover-community/mathlib/pull/6158))
Prove that a Liouville number is irrational
#### Estimated changes
Added src/data/real/liouville.lean
- \+ *lemma* is_liouville.irrational
- \+ *def* is_liouville



## [2021-02-11 20:21:07](https://github.com/leanprover-community/mathlib/commit/64914d3)
chore(group_theory/perm, linear_algebra/alternating): add some helper lemmas for gh-5269 ([#6186](https://github.com/leanprover-community/mathlib/pull/6186))
#### Estimated changes
Modified src/group_theory/perm/subgroup.lean


Modified src/linear_algebra/alternating.lean
- \+ *lemma* multilinear_map.alternatization_coe



## [2021-02-11 20:21:06](https://github.com/leanprover-community/mathlib/commit/cee5ddf)
chore(topology/homeomorph): review, add `prod_punit`/`punit_prod` ([#6180](https://github.com/leanprover-community/mathlib/pull/6180))
* use `to_equiv := e` instead of `.. e` to have definitional equality
  `h.to_equiv = e`;
* add some `@[simp]` lemmas;
* add `homeomorph.prod_punit` and `homeomorph.punit_prod`;
* generalize `unit.topological_space` to `punit.topological_space`.
#### Estimated changes
Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.coe_prod_comm
- \+ *lemma* homeomorph.coe_prod_congr
- \+ *lemma* homeomorph.coe_prod_punit
- \+ *lemma* homeomorph.coe_punit_prod
- \+ *lemma* homeomorph.coe_refl
- \+ *lemma* homeomorph.prod_comm_symm
- \+ *lemma* homeomorph.prod_congr_symm
- \+ *def* homeomorph.prod_punit
- \+ *def* homeomorph.punit_prod
- \+ *lemma* homeomorph.refl_symm

Modified src/topology/order.lean


Modified src/topology/topological_fiber_bundle.lean




## [2021-02-11 20:21:05](https://github.com/leanprover-community/mathlib/commit/6c602c7)
feat(data/nat/bitwise): test bits of powers of two ([#6070](https://github.com/leanprover-community/mathlib/pull/6070))
#### Estimated changes
Modified src/data/nat/bitwise.lean
- \+ *lemma* nat.test_bit_two_pow
- \+ *lemma* nat.test_bit_two_pow_of_ne
- \+ *lemma* nat.test_bit_two_pow_self



## [2021-02-11 16:21:09](https://github.com/leanprover-community/mathlib/commit/1ad29d6)
refactor(algebra/lie/of_associative): remove `ring_commutator` namespace; use `ring` instead ([#6181](https://github.com/leanprover-community/mathlib/pull/6181))
The `old_structure_cmd` change to `lie_algebra.is_simple` is unrelated and is
included here only for convenience.
`ring_commutator.commutator` -> `ring.lie_def`
#### Estimated changes
Modified src/algebra/lie/of_associative.lean
- \+ *lemma* ring.lie_def
- \- *lemma* ring_commutator.commutator

Modified src/algebra/lie/semisimple.lean


Modified src/ring_theory/derivation.lean




## [2021-02-11 16:21:06](https://github.com/leanprover-community/mathlib/commit/abf72e6)
refactor(algebra/lie/*): rename `lie_algebra.morphism` --> `lie_hom`, `lie_algebra.equiv` --> `lie_equiv` ([#6179](https://github.com/leanprover-community/mathlib/pull/6179))
Also renaming the field `map_lie` to `map_lie'` in both `lie_algebra.morphism` and `lie_module_hom`
for consistency with the pattern elsewhere in Mathlib.
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/basic.lean
- \- *lemma* lie_algebra.coe_mk
- \- *lemma* lie_algebra.coe_to_linear_map
- \- *lemma* lie_algebra.equiv.apply_symm_apply
- \- *lemma* lie_algebra.equiv.bijective
- \- *lemma* lie_algebra.equiv.coe_to_lie_equiv
- \- *lemma* lie_algebra.equiv.coe_to_linear_equiv
- \- *lemma* lie_algebra.equiv.injective
- \- *lemma* lie_algebra.equiv.one_apply
- \- *def* lie_algebra.equiv.refl
- \- *lemma* lie_algebra.equiv.refl_apply
- \- *lemma* lie_algebra.equiv.surjective
- \- *def* lie_algebra.equiv.symm
- \- *lemma* lie_algebra.equiv.symm_apply_apply
- \- *lemma* lie_algebra.equiv.symm_symm
- \- *lemma* lie_algebra.equiv.symm_trans_apply
- \- *def* lie_algebra.equiv.trans
- \- *lemma* lie_algebra.equiv.trans_apply
- \- *lemma* lie_algebra.map_lie
- \- *lemma* lie_algebra.map_zero
- \- *lemma* lie_algebra.morphism.coe_injective
- \- *def* lie_algebra.morphism.comp
- \- *lemma* lie_algebra.morphism.comp_apply
- \- *lemma* lie_algebra.morphism.comp_coe
- \- *lemma* lie_algebra.morphism.ext
- \- *lemma* lie_algebra.morphism.ext_iff
- \- *def* lie_algebra.morphism.inverse
- \- *lemma* lie_algebra.morphism.map_add
- \- *lemma* lie_algebra.morphism.map_smul
- \+ *lemma* lie_equiv.apply_symm_apply
- \+ *lemma* lie_equiv.bijective
- \+ *lemma* lie_equiv.coe_to_lie_equiv
- \+ *lemma* lie_equiv.coe_to_linear_equiv
- \+ *lemma* lie_equiv.injective
- \+ *lemma* lie_equiv.one_apply
- \+ *def* lie_equiv.refl
- \+ *lemma* lie_equiv.refl_apply
- \+ *lemma* lie_equiv.surjective
- \+ *def* lie_equiv.symm
- \+ *lemma* lie_equiv.symm_apply_apply
- \+ *lemma* lie_equiv.symm_symm
- \+ *lemma* lie_equiv.symm_trans_apply
- \+ *def* lie_equiv.trans
- \+ *lemma* lie_equiv.trans_apply
- \+ *lemma* lie_hom.coe_injective
- \+ *lemma* lie_hom.coe_mk
- \+ *lemma* lie_hom.coe_to_linear_map
- \+ *def* lie_hom.comp
- \+ *lemma* lie_hom.comp_apply
- \+ *lemma* lie_hom.comp_coe
- \+ *lemma* lie_hom.ext
- \+ *lemma* lie_hom.ext_iff
- \+ *def* lie_hom.inverse
- \+ *lemma* lie_hom.map_add
- \+ *lemma* lie_hom.map_lie
- \+ *lemma* lie_hom.map_smul
- \+ *lemma* lie_hom.map_zero
- \- *lemma* lie_module_hom.map_lie'
- \+ *lemma* lie_module_hom.map_lie

Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/direct_sum.lean


Modified src/algebra/lie/ideal_operations.lean


Modified src/algebra/lie/matrix.lean


Modified src/algebra/lie/of_associative.lean


Modified src/algebra/lie/quotient.lean


Modified src/algebra/lie/skew_adjoint.lean


Modified src/algebra/lie/subalgebra.lean
- \- *def* lie_algebra.equiv.of_eq
- \- *lemma* lie_algebra.equiv.of_eq_apply
- \- *lemma* lie_algebra.equiv.of_injective_apply
- \- *def* lie_algebra.equiv.of_subalgebra
- \- *lemma* lie_algebra.equiv.of_subalgebra_apply
- \- *def* lie_algebra.equiv.of_subalgebras
- \- *lemma* lie_algebra.equiv.of_subalgebras_apply
- \- *lemma* lie_algebra.equiv.of_subalgebras_symm_apply
- \- *def* lie_algebra.morphism.range
- \- *lemma* lie_algebra.morphism.range_bracket
- \- *lemma* lie_algebra.morphism.range_coe
- \+ *def* lie_equiv.of_eq
- \+ *lemma* lie_equiv.of_eq_apply
- \+ *lemma* lie_equiv.of_injective_apply
- \+ *def* lie_equiv.of_subalgebra
- \+ *lemma* lie_equiv.of_subalgebra_apply
- \+ *def* lie_equiv.of_subalgebras
- \+ *lemma* lie_equiv.of_subalgebras_apply
- \+ *lemma* lie_equiv.of_subalgebras_symm_apply
- \+ *def* lie_hom.range
- \+ *lemma* lie_hom.range_bracket
- \+ *lemma* lie_hom.range_coe

Modified src/algebra/lie/submodule.lean
- \- *def* lie_algebra.morphism.ideal_range
- \- *def* lie_algebra.morphism.is_ideal_morphism
- \- *lemma* lie_algebra.morphism.is_ideal_morphism_def
- \- *def* lie_algebra.morphism.ker
- \- *lemma* lie_algebra.morphism.ker_coe_submodule
- \- *lemma* lie_algebra.morphism.ker_eq_bot
- \- *lemma* lie_algebra.morphism.ker_le_comap
- \- *lemma* lie_algebra.morphism.le_ker_iff
- \- *lemma* lie_algebra.morphism.map_bot_iff
- \- *lemma* lie_algebra.morphism.map_le_ideal_range
- \- *lemma* lie_algebra.morphism.mem_ideal_range
- \- *lemma* lie_algebra.morphism.mem_ideal_range_iff
- \- *lemma* lie_algebra.morphism.mem_ker
- \- *lemma* lie_algebra.morphism.range_subset_ideal_range
- \+ *def* lie_hom.ideal_range
- \+ *def* lie_hom.is_ideal_morphism
- \+ *lemma* lie_hom.is_ideal_morphism_def
- \+ *def* lie_hom.ker
- \+ *lemma* lie_hom.ker_coe_submodule
- \+ *lemma* lie_hom.ker_eq_bot
- \+ *lemma* lie_hom.ker_le_comap
- \+ *lemma* lie_hom.le_ker_iff
- \+ *lemma* lie_hom.map_bot_iff
- \+ *lemma* lie_hom.map_le_ideal_range
- \+ *lemma* lie_hom.mem_ideal_range
- \+ *lemma* lie_hom.mem_ideal_range_iff
- \+ *lemma* lie_hom.mem_ker
- \+ *lemma* lie_hom.range_subset_ideal_range

Modified src/algebra/lie/universal_enveloping.lean




## [2021-02-11 16:21:04](https://github.com/leanprover-community/mathlib/commit/b3347e5)
doc(algebra/field): added module doc ([#6177](https://github.com/leanprover-community/mathlib/pull/6177))
#### Estimated changes
Modified src/algebra/field.lean




## [2021-02-11 16:21:00](https://github.com/leanprover-community/mathlib/commit/af8b60b)
feat(algebra/lie/submodule): Lie submodules form a modular lattice ([#6176](https://github.com/leanprover-community/mathlib/pull/6176))
#### Estimated changes
Modified src/algebra/lie/submodule.lean




## [2021-02-11 16:20:58](https://github.com/leanprover-community/mathlib/commit/b9354dd)
feat(algebra/ordered_ring): a product is at least one if both factors are ([#6172](https://github.com/leanprover-community/mathlib/pull/6172))
Add single lemma one_le_mul_of_one_le_of_one_le
The lemma is stated for an `ordered_semiring`, but only multiplication is used.  There does not seem to be an `ordered_monoid` class where this lemma would fit.
Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/ordered_monoid.3F
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* one_le_mul_of_one_le_of_one_le



## [2021-02-11 16:20:56](https://github.com/leanprover-community/mathlib/commit/194ec66)
feat(group_theory/subgroup): prove relation between pointwise product of submonoids/subgroups and their join ([#6165](https://github.com/leanprover-community/mathlib/pull/6165))
If `H` and `K` are subgroups/submonoids then `H ⊔ K = closure (H * K)`, where `H * K` is the pointwise set product. When `H` or `K` is a normal subgroup, it is proved that `(↑(H ⊔ K) : set G) = H * K`.
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* submonoid.closure_mul_le
- \+ *lemma* submonoid.sup_eq_closure

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.closure_mul_le
- \+ *lemma* subgroup.mul_normal
- \+ *lemma* subgroup.normal_mul
- \+ *lemma* subgroup.sup_eq_closure



## [2021-02-11 16:20:55](https://github.com/leanprover-community/mathlib/commit/f151da2)
feat(field_theory/polynomial_galois_group): Restriction from splitting field of composition ([#6148](https://github.com/leanprover-community/mathlib/pull/6148))
Defines the surjective restriction map from the splitting field of a composition
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.mul_splits_in_splitting_field_of_mul
- \+ *def* polynomial.gal.restrict_comp
- \+ *lemma* polynomial.gal.restrict_comp_surjective
- \+ *lemma* polynomial.gal.splits_in_splitting_field_of_comp



## [2021-02-11 16:20:52](https://github.com/leanprover-community/mathlib/commit/7b4a9e5)
feat(order/well_founded_set) : Define when a set is well-founded with `set.is_wf` ([#6113](https://github.com/leanprover-community/mathlib/pull/6113))
Defines a predicate for when a set within an ordered type is well-founded (`set.is_wf`)
Proves basic lemmas about well-founded sets
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+ *def* nat.order_embedding_of_set
- \+ *lemma* nat.order_embedding_of_set_apply
- \+ *lemma* nat.order_embedding_of_set_range
- \+ *lemma* nat.subtype.order_iso_of_nat_apply
- \+/\- *def* rel_embedding.nat_gt
- \+/\- *def* rel_embedding.nat_lt
- \+ *lemma* rel_embedding.nat_lt_apply
- \+/\- *theorem* rel_embedding.well_founded_iff_no_descending_seq

Modified src/order/rel_iso.lean
- \+ *lemma* rel_embedding.order_embedding_of_lt_embedding_apply

Added src/order/well_founded_set.lean
- \+ *theorem* finset.is_wf
- \+ *theorem* set.finite.is_wf
- \+ *theorem* set.fintype.is_wf
- \+ *theorem* set.is_wf.insert
- \+ *theorem* set.is_wf.mono
- \+ *theorem* set.is_wf.union
- \+ *def* set.is_wf
- \+ *theorem* set.is_wf_iff_no_descending_seq
- \+ *theorem* set.is_wf_singleton
- \+ *def* set.well_founded_on
- \+ *lemma* set.well_founded_on_iff



## [2021-02-11 16:20:48](https://github.com/leanprover-community/mathlib/commit/a557f8b)
feat(data/complex): order structure ([#4684](https://github.com/leanprover-community/mathlib/pull/4684))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *def* complex.complex_order
- \+ *def* complex.complex_ordered_comm_ring
- \+ *lemma* complex.le_def
- \+ *lemma* complex.lt_def
- \+ *lemma* complex.norm_sq_eq_conj_mul_self
- \+/\- *lemma* complex.norm_sq_one
- \+/\- *lemma* complex.norm_sq_zero
- \+ *lemma* complex.real_le_real
- \+ *lemma* complex.real_lt_real
- \+ *lemma* complex.zero_le_real
- \+ *lemma* complex.zero_lt_real



## [2021-02-11 14:27:06](https://github.com/leanprover-community/mathlib/commit/39090c8)
doc(analysis/analytic/inverse): fix mathjax output ([#6175](https://github.com/leanprover-community/mathlib/pull/6175))
`\\` in source code is converted to `\` in the generated html file, so one should have `\\\\` to generate proper line break for mathjax.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/analytic/inverse.lean




## [2021-02-11 11:51:02](https://github.com/leanprover-community/mathlib/commit/58632ac)
feat(topology/order): discrete_topology_bot ([#6163](https://github.com/leanprover-community/mathlib/pull/6163))
From `lean-liquid`
#### Estimated changes
Modified src/topology/order.lean




## [2021-02-11 11:50:59](https://github.com/leanprover-community/mathlib/commit/fdace95)
feat(linear_algebra/matrix): generalize some `is_basis.to_matrix` results ([#6127](https://github.com/leanprover-community/mathlib/pull/6127))
This PR contains some changes to the lemmas involving `is_basis.to_matrix`, allowing the bases involved to differ in their index type. Although you can prove there exists an `equiv` between those types, it's easier to not have to transport along that equiv.
The PR also generalizes `linear_map.to_matrix_id` to a form with two different bases, `linear_map.to_matrix_id_eq_basis_to_matrix`. Marking the second as `simp` means the first can be proved automatically, hence the removal of `simp` on that one.
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+ *lemma* is_basis.to_matrix_mul_to_matrix
- \+ *lemma* linear_map.to_matrix_id_eq_basis_to_matrix



## [2021-02-11 09:21:58](https://github.com/leanprover-community/mathlib/commit/d405c5e)
chore(scripts): update nolints.txt ([#6169](https://github.com/leanprover-community/mathlib/pull/6169))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-11 09:21:57](https://github.com/leanprover-community/mathlib/commit/59daf53)
refactor(topology/subset_properties.lean): split the subset_properties.lean file ([#6161](https://github.com/leanprover-community/mathlib/pull/6161))
split the file subset_properties.lean into another file called connected.lean which contains the properties that relate to connectivity. This is in preparation for a future PR proving properties about the quotient of a space by its connected components and it would add roughly 300 lines.
#### Estimated changes
Added src/topology/connected.lean
- \+ *def* connected_component
- \+ *def* connected_component_in
- \+ *lemma* connected_component_subset_Inter_clopen
- \+ *lemma* connected_space_iff_connected_component
- \+ *lemma* eq_univ_of_nonempty_clopen
- \+ *theorem* irreducible_component_subset_connected_component
- \+ *theorem* is_clopen_iff
- \+ *theorem* is_closed_connected_component
- \+ *theorem* is_connected.closure
- \+ *theorem* is_connected.image
- \+ *lemma* is_connected.is_preconnected
- \+ *lemma* is_connected.nonempty
- \+ *theorem* is_connected.union
- \+ *def* is_connected
- \+ *theorem* is_connected_connected_component
- \+ *lemma* is_connected_iff_connected_space
- \+ *lemma* is_connected_iff_sUnion_disjoint_open
- \+ *lemma* is_connected_range
- \+ *theorem* is_connected_singleton
- \+ *theorem* is_irreducible.is_connected
- \+ *theorem* is_preconnected.closure
- \+ *theorem* is_preconnected.image
- \+ *theorem* is_preconnected.union
- \+ *def* is_preconnected
- \+ *theorem* is_preconnected_closed_iff
- \+ *theorem* is_preconnected_empty
- \+ *lemma* is_preconnected_iff_preconnected_space
- \+ *lemma* is_preconnected_iff_subset_of_disjoint
- \+ *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \+ *theorem* is_preconnected_iff_subset_of_fully_disjoint_closed
- \+ *theorem* is_preconnected_of_forall
- \+ *theorem* is_preconnected_of_forall_pair
- \+ *theorem* is_preconnected_sUnion
- \+ *theorem* is_preirreducible.is_preconnected
- \+ *def* is_totally_disconnected
- \+ *theorem* is_totally_disconnected_empty
- \+ *theorem* is_totally_disconnected_of_is_totally_separated
- \+ *theorem* is_totally_disconnected_singleton
- \+ *def* is_totally_separated
- \+ *theorem* is_totally_separated_empty
- \+ *theorem* is_totally_separated_singleton
- \+ *theorem* mem_connected_component
- \+ *theorem* nonempty_inter
- \+ *theorem* subset_connected_component
- \+ *theorem* subset_or_disjoint_of_clopen
- \+ *lemma* subtype.connected_space
- \+ *lemma* subtype.preconnected_space

Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \- *def* connected_component
- \- *def* connected_component_in
- \- *lemma* connected_component_subset_Inter_clopen
- \- *lemma* connected_space_iff_connected_component
- \- *lemma* eq_univ_of_nonempty_clopen
- \- *theorem* irreducible_component_subset_connected_component
- \- *theorem* is_clopen_iff
- \- *theorem* is_closed_connected_component
- \- *theorem* is_connected.closure
- \- *theorem* is_connected.image
- \- *lemma* is_connected.is_preconnected
- \- *lemma* is_connected.nonempty
- \- *theorem* is_connected.union
- \- *def* is_connected
- \- *theorem* is_connected_connected_component
- \- *lemma* is_connected_iff_connected_space
- \- *lemma* is_connected_iff_sUnion_disjoint_open
- \- *lemma* is_connected_range
- \- *theorem* is_connected_singleton
- \- *theorem* is_irreducible.is_connected
- \- *theorem* is_preconnected.closure
- \- *theorem* is_preconnected.image
- \- *theorem* is_preconnected.union
- \- *def* is_preconnected
- \- *theorem* is_preconnected_closed_iff
- \- *theorem* is_preconnected_empty
- \- *lemma* is_preconnected_iff_preconnected_space
- \- *lemma* is_preconnected_iff_subset_of_disjoint
- \- *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \- *theorem* is_preconnected_iff_subset_of_fully_disjoint_closed
- \- *theorem* is_preconnected_of_forall
- \- *theorem* is_preconnected_of_forall_pair
- \- *theorem* is_preconnected_sUnion
- \- *theorem* is_preirreducible.is_preconnected
- \- *def* is_totally_disconnected
- \- *theorem* is_totally_disconnected_empty
- \- *theorem* is_totally_disconnected_of_is_totally_separated
- \- *theorem* is_totally_disconnected_singleton
- \- *def* is_totally_separated
- \- *theorem* is_totally_separated_empty
- \- *theorem* is_totally_separated_singleton
- \- *theorem* mem_connected_component
- \- *theorem* nonempty_inter
- \- *theorem* subset_connected_component
- \- *theorem* subset_or_disjoint_of_clopen
- \- *lemma* subtype.connected_space
- \- *lemma* subtype.preconnected_space



## [2021-02-11 09:21:55](https://github.com/leanprover-community/mathlib/commit/97a56e6)
refactor(algebra/lie/basic): split giant file into pieces ([#6141](https://github.com/leanprover-community/mathlib/pull/6141))
#### Estimated changes
Added src/algebra/lie/abelian.lean
- \+ *lemma* commutative_ring_iff_abelian_lie_ring
- \+ *lemma* function.injective.is_lie_abelian
- \+ *lemma* function.surjective.is_lie_abelian
- \+ *lemma* lie_abelian_iff_equiv_lie_abelian
- \+ *lemma* lie_algebra.abelian_of_le_center
- \+ *lemma* lie_algebra.center_eq_adjoint_kernel
- \+ *lemma* lie_algebra.is_lie_abelian_bot
- \+ *lemma* lie_algebra.is_lie_abelian_iff_center_eq_top
- \+ *lemma* lie_module.is_trivial_iff_maximal_trivial_eq_top
- \+ *def* lie_module.maximal_trivial_submodule
- \+ *lemma* lie_module.mem_maximal_trivial_submodule
- \+ *lemma* lie_module.trivial_iff_le_maximal_trivial
- \+ *lemma* lie_submodule.lie_abelian_iff_lie_self_eq_bot
- \+ *lemma* lie_submodule.trivial_lie_oper_zero
- \+ *lemma* trivial_lie_zero

Modified src/algebra/lie/basic.lean
- \- *def* alg_equiv.to_lie_equiv
- \- *lemma* alg_equiv.to_lie_equiv_apply
- \- *lemma* alg_equiv.to_lie_equiv_symm_apply
- \- *lemma* commutative_ring_iff_abelian_lie_ring
- \- *lemma* function.injective.is_lie_abelian
- \- *lemma* function.surjective.is_lie_abelian
- \- *lemma* lie_abelian_iff_equiv_lie_abelian
- \- *lemma* lie_algebra.abelian_derived_abelian_of_ideal
- \- *lemma* lie_algebra.abelian_iff_derived_one_eq_bot
- \- *lemma* lie_algebra.abelian_iff_derived_succ_eq_bot
- \- *lemma* lie_algebra.abelian_of_le_center
- \- *lemma* lie_algebra.abelian_of_solvable_ideal_eq_bot_iff
- \- *lemma* lie_algebra.abelian_radical_iff_solvable_is_abelian
- \- *lemma* lie_algebra.abelian_radical_of_semisimple
- \- *def* lie_algebra.ad
- \- *lemma* lie_algebra.ad_apply
- \- *lemma* lie_algebra.center_eq_adjoint_kernel
- \- *lemma* lie_algebra.center_eq_bot_of_semisimple
- \- *lemma* lie_algebra.center_le_radical
- \- *lemma* lie_algebra.derived_length_eq_derived_length_of_ideal
- \- *lemma* lie_algebra.derived_length_zero
- \- *lemma* lie_algebra.derived_series_def
- \- *lemma* lie_algebra.derived_series_of_bot_eq_bot
- \- *lemma* lie_algebra.derived_series_of_derived_length_succ
- \- *def* lie_algebra.derived_series_of_ideal
- \- *lemma* lie_algebra.derived_series_of_ideal_add
- \- *lemma* lie_algebra.derived_series_of_ideal_add_le_add
- \- *lemma* lie_algebra.derived_series_of_ideal_antimono
- \- *lemma* lie_algebra.derived_series_of_ideal_le
- \- *lemma* lie_algebra.derived_series_of_ideal_le_self
- \- *lemma* lie_algebra.derived_series_of_ideal_mono
- \- *lemma* lie_algebra.derived_series_of_ideal_succ
- \- *lemma* lie_algebra.derived_series_of_ideal_succ_le
- \- *lemma* lie_algebra.derived_series_of_ideal_zero
- \- *def* lie_algebra.equiv.of_eq
- \- *lemma* lie_algebra.equiv.of_eq_apply
- \- *lemma* lie_algebra.equiv.of_injective_apply
- \- *def* lie_algebra.equiv.of_subalgebra
- \- *lemma* lie_algebra.equiv.of_subalgebra_apply
- \- *def* lie_algebra.equiv.of_subalgebras
- \- *lemma* lie_algebra.equiv.of_subalgebras_apply
- \- *lemma* lie_algebra.equiv.of_subalgebras_symm_apply
- \- *lemma* lie_algebra.is_lie_abelian_bot
- \- *lemma* lie_algebra.is_lie_abelian_iff_center_eq_top
- \- *lemma* lie_algebra.is_semisimple_iff_no_abelian_ideals
- \- *lemma* lie_algebra.is_semisimple_iff_no_solvable_ideals
- \- *lemma* lie_algebra.is_solvable_of_injective
- \- *lemma* lie_algebra.le_solvable_ideal_solvable
- \- *lemma* lie_algebra.lie_ideal.solvable_iff_le_radical
- \- *def* lie_algebra.morphism.ideal_range
- \- *def* lie_algebra.morphism.is_ideal_morphism
- \- *lemma* lie_algebra.morphism.is_ideal_morphism_def
- \- *def* lie_algebra.morphism.ker
- \- *lemma* lie_algebra.morphism.ker_coe_submodule
- \- *lemma* lie_algebra.morphism.ker_eq_bot
- \- *lemma* lie_algebra.morphism.ker_le_comap
- \- *lemma* lie_algebra.morphism.le_ker_iff
- \- *lemma* lie_algebra.morphism.map_bot_iff
- \- *lemma* lie_algebra.morphism.map_le_ideal_range
- \- *lemma* lie_algebra.morphism.mem_ideal_range
- \- *lemma* lie_algebra.morphism.mem_ideal_range_iff
- \- *lemma* lie_algebra.morphism.mem_ker
- \- *def* lie_algebra.morphism.range
- \- *lemma* lie_algebra.morphism.range_bracket
- \- *lemma* lie_algebra.morphism.range_coe
- \- *lemma* lie_algebra.morphism.range_subset_ideal_range
- \- *def* lie_algebra.of_associative_algebra_hom
- \- *lemma* lie_algebra.of_associative_algebra_hom_apply
- \- *lemma* lie_algebra.of_associative_algebra_hom_comp
- \- *lemma* lie_algebra.of_associative_algebra_hom_id
- \- *def* lie_algebra.radical
- \- *lemma* lie_algebra.subsingleton_of_semisimple_lie_abelian
- \- *def* lie_algebra.top_equiv_self
- \- *lemma* lie_algebra.top_equiv_self_apply
- \- *def* lie_equiv_matrix'
- \- *lemma* lie_equiv_matrix'_apply
- \- *lemma* lie_equiv_matrix'_symm_apply
- \- *lemma* lie_ideal.bot_of_map_eq_bot
- \- *lemma* lie_ideal.coe_hom_of_le
- \- *lemma* lie_ideal.coe_to_subalgebra
- \- *def* lie_ideal.comap
- \- *lemma* lie_ideal.comap_bracket_eq
- \- *lemma* lie_ideal.comap_bracket_incl
- \- *lemma* lie_ideal.comap_bracket_incl_of_le
- \- *lemma* lie_ideal.comap_bracket_le
- \- *lemma* lie_ideal.comap_coe_submodule
- \- *lemma* lie_ideal.comap_incl_self
- \- *lemma* lie_ideal.comap_map_eq
- \- *lemma* lie_ideal.comap_map_le
- \- *lemma* lie_ideal.comap_mono
- \- *lemma* lie_ideal.derived_series_add_eq_bot
- \- *lemma* lie_ideal.derived_series_eq_bot_iff
- \- *lemma* lie_ideal.derived_series_eq_derived_series_of_ideal_comap
- \- *lemma* lie_ideal.derived_series_eq_derived_series_of_ideal_map
- \- *lemma* lie_ideal.derived_series_map_le_derived_series
- \- *lemma* lie_ideal.gc_map_comap
- \- *def* lie_ideal.hom_of_le
- \- *lemma* lie_ideal.hom_of_le_apply
- \- *lemma* lie_ideal.hom_of_le_injective
- \- *def* lie_ideal.incl
- \- *lemma* lie_ideal.incl_apply
- \- *lemma* lie_ideal.incl_coe
- \- *lemma* lie_ideal.incl_ideal_range
- \- *lemma* lie_ideal.incl_is_ideal_morphism
- \- *lemma* lie_ideal.ker_incl
- \- *def* lie_ideal.map
- \- *lemma* lie_ideal.map_bracket_le
- \- *lemma* lie_ideal.map_coe_submodule
- \- *lemma* lie_ideal.map_comap_bracket_eq
- \- *lemma* lie_ideal.map_comap_eq
- \- *lemma* lie_ideal.map_comap_incl
- \- *lemma* lie_ideal.map_comap_le
- \- *lemma* lie_ideal.map_le
- \- *lemma* lie_ideal.map_le_iff_le_comap
- \- *lemma* lie_ideal.map_mono
- \- *lemma* lie_ideal.map_of_image
- \- *lemma* lie_ideal.map_sup_ker_eq_map
- \- *lemma* lie_ideal.mem_comap
- \- *lemma* lie_ideal.mem_map
- \- *lemma* lie_ideal.subsingleton_of_bot
- \- *def* lie_ideal_subalgebra
- \- *lemma* lie_mem_left
- \- *lemma* lie_mem_right
- \- *lemma* lie_module.derived_series_le_lower_central_series
- \- *lemma* lie_module.is_trivial_iff_maximal_trivial_eq_top
- \- *def* lie_module.lower_central_series
- \- *lemma* lie_module.lower_central_series_succ
- \- *lemma* lie_module.lower_central_series_zero
- \- *def* lie_module.maximal_trivial_submodule
- \- *lemma* lie_module.mem_maximal_trivial_submodule
- \- *def* lie_module.to_endomorphism
- \- *lemma* lie_module.trivial_iff_le_maximal_trivial
- \- *lemma* lie_module.trivial_iff_lower_central_eq_bot
- \- *lemma* lie_ring.of_associative_ring_bracket
- \- *lemma* lie_subalgebra.add_mem
- \- *lemma* lie_subalgebra.coe_bracket
- \- *lemma* lie_subalgebra.coe_injective
- \- *theorem* lie_subalgebra.coe_set_eq
- \- *lemma* lie_subalgebra.coe_to_submodule_eq
- \- *lemma* lie_subalgebra.coe_zero_iff_zero
- \- *lemma* lie_subalgebra.ext
- \- *lemma* lie_subalgebra.ext_iff'
- \- *lemma* lie_subalgebra.ext_iff
- \- *def* lie_subalgebra.incl
- \- *lemma* lie_subalgebra.lie_mem
- \- *def* lie_subalgebra.map
- \- *lemma* lie_subalgebra.mem_coe'
- \- *lemma* lie_subalgebra.mem_coe
- \- *lemma* lie_subalgebra.mem_map_submodule
- \- *lemma* lie_subalgebra.mk_coe
- \- *lemma* lie_subalgebra.range_incl
- \- *lemma* lie_subalgebra.smul_mem
- \- *lemma* lie_subalgebra.to_submodule_injective
- \- *lemma* lie_subalgebra.zero_mem
- \- *def* lie_subalgebra_of_subalgebra
- \- *lemma* lie_submodule.Inf_coe
- \- *lemma* lie_submodule.Inf_coe_to_submodule
- \- *lemma* lie_submodule.Inf_glb
- \- *lemma* lie_submodule.add_eq_sup
- \- *lemma* lie_submodule.bot_coe
- \- *lemma* lie_submodule.bot_coe_submodule
- \- *lemma* lie_submodule.bot_lie
- \- *lemma* lie_submodule.coe_hom_of_le
- \- *lemma* lie_submodule.coe_injective
- \- *lemma* lie_submodule.coe_submodule_injective
- \- *lemma* lie_submodule.coe_submodule_le_coe_submodule
- \- *lemma* lie_submodule.coe_to_set_mk
- \- *lemma* lie_submodule.coe_to_submodule
- \- *lemma* lie_submodule.coe_to_submodule_eq_iff
- \- *lemma* lie_submodule.coe_to_submodule_mk
- \- *def* lie_submodule.comap
- \- *lemma* lie_submodule.eq_bot_iff
- \- *lemma* lie_submodule.ext
- \- *lemma* lie_submodule.gc_map_comap
- \- *def* lie_submodule.hom_of_le
- \- *lemma* lie_submodule.hom_of_le_apply
- \- *lemma* lie_submodule.hom_of_le_injective
- \- *def* lie_submodule.incl
- \- *lemma* lie_submodule.incl_apply
- \- *lemma* lie_submodule.incl_eq_val
- \- *theorem* lie_submodule.inf_coe
- \- *lemma* lie_submodule.inf_coe_to_submodule
- \- *lemma* lie_submodule.inf_lie
- \- *lemma* lie_submodule.le_def
- \- *lemma* lie_submodule.lie_abelian_iff_lie_self_eq_bot
- \- *lemma* lie_submodule.lie_bot
- \- *lemma* lie_submodule.lie_comm
- \- *lemma* lie_submodule.lie_ideal_oper_eq_linear_span
- \- *lemma* lie_submodule.lie_ideal_oper_eq_span
- \- *lemma* lie_submodule.lie_inf
- \- *lemma* lie_submodule.lie_le_inf
- \- *lemma* lie_submodule.lie_le_left
- \- *lemma* lie_submodule.lie_le_right
- \- *lemma* lie_submodule.lie_mem_lie
- \- *def* lie_submodule.lie_span
- \- *lemma* lie_submodule.lie_span_eq
- \- *lemma* lie_submodule.lie_span_le
- \- *lemma* lie_submodule.lie_span_mono
- \- *lemma* lie_submodule.lie_sup
- \- *def* lie_submodule.map
- \- *lemma* lie_submodule.map_le_iff_le_comap
- \- *lemma* lie_submodule.mem_bot
- \- *lemma* lie_submodule.mem_carrier
- \- *lemma* lie_submodule.mem_coe
- \- *lemma* lie_submodule.mem_coe_submodule
- \- *lemma* lie_submodule.mem_inf
- \- *lemma* lie_submodule.mem_lie_span
- \- *lemma* lie_submodule.mem_sup
- \- *lemma* lie_submodule.mem_top
- \- *lemma* lie_submodule.mono_lie
- \- *lemma* lie_submodule.mono_lie_left
- \- *lemma* lie_submodule.mono_lie_right
- \- *def* lie_submodule.quotient.action_as_endo_map
- \- *def* lie_submodule.quotient.action_as_endo_map_bracket
- \- *lemma* lie_submodule.quotient.is_quotient_mk
- \- *def* lie_submodule.quotient.lie_submodule_invariant
- \- *lemma* lie_submodule.quotient.mk_bracket
- \- *lemma* lie_submodule.submodule_span_le_lie_span
- \- *lemma* lie_submodule.subset_lie_span
- \- *lemma* lie_submodule.subsingleton_of_bot
- \- *lemma* lie_submodule.sup_coe_to_submodule
- \- *lemma* lie_submodule.sup_lie
- \- *lemma* lie_submodule.top_coe
- \- *lemma* lie_submodule.top_coe_submodule
- \- *lemma* lie_submodule.trivial_lie_oper_zero
- \- *lemma* lie_submodule.well_founded_of_noetherian
- \- *lemma* lie_submodule.zero_mem
- \- *def* linear_equiv.lie_conj
- \- *lemma* linear_equiv.lie_conj_apply
- \- *lemma* linear_equiv.lie_conj_symm
- \- *lemma* matrix.lie_conj_apply
- \- *lemma* matrix.lie_conj_symm_apply
- \- *def* matrix.reindex_lie_equiv
- \- *lemma* matrix.reindex_lie_equiv_apply
- \- *lemma* matrix.reindex_lie_equiv_symm_apply
- \- *lemma* ring_commutator.commutator
- \- *lemma* trivial_lie_zero

Modified src/algebra/lie/classical.lean


Added src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_ideal.comap_bracket_eq
- \+ *lemma* lie_ideal.comap_bracket_incl
- \+ *lemma* lie_ideal.comap_bracket_incl_of_le
- \+ *lemma* lie_ideal.comap_bracket_le
- \+ *lemma* lie_ideal.map_bracket_le
- \+ *lemma* lie_ideal.map_comap_bracket_eq
- \+ *lemma* lie_ideal.map_comap_incl
- \+ *lemma* lie_submodule.bot_lie
- \+ *lemma* lie_submodule.inf_lie
- \+ *lemma* lie_submodule.lie_bot
- \+ *lemma* lie_submodule.lie_comm
- \+ *lemma* lie_submodule.lie_ideal_oper_eq_linear_span
- \+ *lemma* lie_submodule.lie_ideal_oper_eq_span
- \+ *lemma* lie_submodule.lie_inf
- \+ *lemma* lie_submodule.lie_le_inf
- \+ *lemma* lie_submodule.lie_le_left
- \+ *lemma* lie_submodule.lie_le_right
- \+ *lemma* lie_submodule.lie_mem_lie
- \+ *lemma* lie_submodule.lie_sup
- \+ *lemma* lie_submodule.mono_lie
- \+ *lemma* lie_submodule.mono_lie_left
- \+ *lemma* lie_submodule.mono_lie_right
- \+ *lemma* lie_submodule.sup_lie

Added src/algebra/lie/matrix.lean
- \+ *def* lie_equiv_matrix'
- \+ *lemma* lie_equiv_matrix'_apply
- \+ *lemma* lie_equiv_matrix'_symm_apply
- \+ *lemma* matrix.lie_conj_apply
- \+ *lemma* matrix.lie_conj_symm_apply
- \+ *def* matrix.reindex_lie_equiv
- \+ *lemma* matrix.reindex_lie_equiv_apply
- \+ *lemma* matrix.reindex_lie_equiv_symm_apply

Added src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_module.derived_series_le_lower_central_series
- \+ *def* lie_module.lower_central_series
- \+ *lemma* lie_module.lower_central_series_succ
- \+ *lemma* lie_module.lower_central_series_zero
- \+ *lemma* lie_module.trivial_iff_lower_central_eq_bot

Added src/algebra/lie/of_associative.lean
- \+ *def* alg_equiv.to_lie_equiv
- \+ *lemma* alg_equiv.to_lie_equiv_apply
- \+ *lemma* alg_equiv.to_lie_equiv_symm_apply
- \+ *def* lie_algebra.ad
- \+ *lemma* lie_algebra.ad_apply
- \+ *def* lie_algebra.of_associative_algebra_hom
- \+ *lemma* lie_algebra.of_associative_algebra_hom_apply
- \+ *lemma* lie_algebra.of_associative_algebra_hom_comp
- \+ *lemma* lie_algebra.of_associative_algebra_hom_id
- \+ *def* lie_module.to_endomorphism
- \+ *lemma* lie_ring.of_associative_ring_bracket
- \+ *def* lie_subalgebra_of_subalgebra
- \+ *def* linear_equiv.lie_conj
- \+ *lemma* linear_equiv.lie_conj_apply
- \+ *lemma* linear_equiv.lie_conj_symm
- \+ *lemma* ring_commutator.commutator

Added src/algebra/lie/quotient.lean
- \+ *def* lie_submodule.quotient.action_as_endo_map
- \+ *def* lie_submodule.quotient.action_as_endo_map_bracket
- \+ *lemma* lie_submodule.quotient.is_quotient_mk
- \+ *def* lie_submodule.quotient.lie_submodule_invariant
- \+ *lemma* lie_submodule.quotient.mk_bracket

Added src/algebra/lie/semisimple.lean
- \+ *lemma* lie_algebra.abelian_radical_iff_solvable_is_abelian
- \+ *lemma* lie_algebra.abelian_radical_of_semisimple
- \+ *lemma* lie_algebra.center_eq_bot_of_semisimple
- \+ *lemma* lie_algebra.is_semisimple_iff_no_abelian_ideals
- \+ *lemma* lie_algebra.is_semisimple_iff_no_solvable_ideals
- \+ *lemma* lie_algebra.subsingleton_of_semisimple_lie_abelian

Modified src/algebra/lie/skew_adjoint.lean


Added src/algebra/lie/solvable.lean
- \+ *lemma* lie_algebra.abelian_derived_abelian_of_ideal
- \+ *lemma* lie_algebra.abelian_iff_derived_one_eq_bot
- \+ *lemma* lie_algebra.abelian_iff_derived_succ_eq_bot
- \+ *lemma* lie_algebra.abelian_of_solvable_ideal_eq_bot_iff
- \+ *lemma* lie_algebra.center_le_radical
- \+ *lemma* lie_algebra.derived_length_eq_derived_length_of_ideal
- \+ *lemma* lie_algebra.derived_length_zero
- \+ *lemma* lie_algebra.derived_series_def
- \+ *lemma* lie_algebra.derived_series_of_bot_eq_bot
- \+ *lemma* lie_algebra.derived_series_of_derived_length_succ
- \+ *def* lie_algebra.derived_series_of_ideal
- \+ *lemma* lie_algebra.derived_series_of_ideal_add
- \+ *lemma* lie_algebra.derived_series_of_ideal_add_le_add
- \+ *lemma* lie_algebra.derived_series_of_ideal_antimono
- \+ *lemma* lie_algebra.derived_series_of_ideal_le
- \+ *lemma* lie_algebra.derived_series_of_ideal_le_self
- \+ *lemma* lie_algebra.derived_series_of_ideal_mono
- \+ *lemma* lie_algebra.derived_series_of_ideal_succ
- \+ *lemma* lie_algebra.derived_series_of_ideal_succ_le
- \+ *lemma* lie_algebra.derived_series_of_ideal_zero
- \+ *lemma* lie_algebra.is_solvable_of_injective
- \+ *lemma* lie_algebra.le_solvable_ideal_solvable
- \+ *lemma* lie_algebra.lie_ideal.solvable_iff_le_radical
- \+ *def* lie_algebra.radical
- \+ *lemma* lie_ideal.derived_series_add_eq_bot
- \+ *lemma* lie_ideal.derived_series_eq_bot_iff
- \+ *lemma* lie_ideal.derived_series_eq_derived_series_of_ideal_comap
- \+ *lemma* lie_ideal.derived_series_eq_derived_series_of_ideal_map
- \+ *lemma* lie_ideal.derived_series_map_le_derived_series

Added src/algebra/lie/subalgebra.lean
- \+ *def* lie_algebra.equiv.of_eq
- \+ *lemma* lie_algebra.equiv.of_eq_apply
- \+ *lemma* lie_algebra.equiv.of_injective_apply
- \+ *def* lie_algebra.equiv.of_subalgebra
- \+ *lemma* lie_algebra.equiv.of_subalgebra_apply
- \+ *def* lie_algebra.equiv.of_subalgebras
- \+ *lemma* lie_algebra.equiv.of_subalgebras_apply
- \+ *lemma* lie_algebra.equiv.of_subalgebras_symm_apply
- \+ *def* lie_algebra.morphism.range
- \+ *lemma* lie_algebra.morphism.range_bracket
- \+ *lemma* lie_algebra.morphism.range_coe
- \+ *lemma* lie_subalgebra.add_mem
- \+ *lemma* lie_subalgebra.coe_bracket
- \+ *lemma* lie_subalgebra.coe_injective
- \+ *theorem* lie_subalgebra.coe_set_eq
- \+ *lemma* lie_subalgebra.coe_to_submodule_eq
- \+ *lemma* lie_subalgebra.coe_zero_iff_zero
- \+ *lemma* lie_subalgebra.ext
- \+ *lemma* lie_subalgebra.ext_iff'
- \+ *lemma* lie_subalgebra.ext_iff
- \+ *def* lie_subalgebra.incl
- \+ *lemma* lie_subalgebra.lie_mem
- \+ *def* lie_subalgebra.map
- \+ *lemma* lie_subalgebra.mem_coe'
- \+ *lemma* lie_subalgebra.mem_coe
- \+ *lemma* lie_subalgebra.mem_map_submodule
- \+ *lemma* lie_subalgebra.mk_coe
- \+ *lemma* lie_subalgebra.range_incl
- \+ *lemma* lie_subalgebra.smul_mem
- \+ *lemma* lie_subalgebra.to_submodule_injective
- \+ *lemma* lie_subalgebra.zero_mem

Added src/algebra/lie/submodule.lean
- \+ *def* lie_algebra.morphism.ideal_range
- \+ *def* lie_algebra.morphism.is_ideal_morphism
- \+ *lemma* lie_algebra.morphism.is_ideal_morphism_def
- \+ *def* lie_algebra.morphism.ker
- \+ *lemma* lie_algebra.morphism.ker_coe_submodule
- \+ *lemma* lie_algebra.morphism.ker_eq_bot
- \+ *lemma* lie_algebra.morphism.ker_le_comap
- \+ *lemma* lie_algebra.morphism.le_ker_iff
- \+ *lemma* lie_algebra.morphism.map_bot_iff
- \+ *lemma* lie_algebra.morphism.map_le_ideal_range
- \+ *lemma* lie_algebra.morphism.mem_ideal_range
- \+ *lemma* lie_algebra.morphism.mem_ideal_range_iff
- \+ *lemma* lie_algebra.morphism.mem_ker
- \+ *lemma* lie_algebra.morphism.range_subset_ideal_range
- \+ *def* lie_algebra.top_equiv_self
- \+ *lemma* lie_algebra.top_equiv_self_apply
- \+ *lemma* lie_ideal.bot_of_map_eq_bot
- \+ *lemma* lie_ideal.coe_hom_of_le
- \+ *lemma* lie_ideal.coe_to_subalgebra
- \+ *def* lie_ideal.comap
- \+ *lemma* lie_ideal.comap_coe_submodule
- \+ *lemma* lie_ideal.comap_incl_self
- \+ *lemma* lie_ideal.comap_map_eq
- \+ *lemma* lie_ideal.comap_map_le
- \+ *lemma* lie_ideal.comap_mono
- \+ *lemma* lie_ideal.gc_map_comap
- \+ *def* lie_ideal.hom_of_le
- \+ *lemma* lie_ideal.hom_of_le_apply
- \+ *lemma* lie_ideal.hom_of_le_injective
- \+ *def* lie_ideal.incl
- \+ *lemma* lie_ideal.incl_apply
- \+ *lemma* lie_ideal.incl_coe
- \+ *lemma* lie_ideal.incl_ideal_range
- \+ *lemma* lie_ideal.incl_is_ideal_morphism
- \+ *lemma* lie_ideal.ker_incl
- \+ *def* lie_ideal.map
- \+ *lemma* lie_ideal.map_coe_submodule
- \+ *lemma* lie_ideal.map_comap_eq
- \+ *lemma* lie_ideal.map_comap_le
- \+ *lemma* lie_ideal.map_le
- \+ *lemma* lie_ideal.map_le_iff_le_comap
- \+ *lemma* lie_ideal.map_mono
- \+ *lemma* lie_ideal.map_of_image
- \+ *lemma* lie_ideal.map_sup_ker_eq_map
- \+ *lemma* lie_ideal.mem_comap
- \+ *lemma* lie_ideal.mem_map
- \+ *lemma* lie_ideal.subsingleton_of_bot
- \+ *def* lie_ideal_subalgebra
- \+ *lemma* lie_mem_left
- \+ *lemma* lie_mem_right
- \+ *lemma* lie_submodule.Inf_coe
- \+ *lemma* lie_submodule.Inf_coe_to_submodule
- \+ *lemma* lie_submodule.Inf_glb
- \+ *lemma* lie_submodule.add_eq_sup
- \+ *lemma* lie_submodule.bot_coe
- \+ *lemma* lie_submodule.bot_coe_submodule
- \+ *lemma* lie_submodule.coe_hom_of_le
- \+ *lemma* lie_submodule.coe_injective
- \+ *lemma* lie_submodule.coe_submodule_injective
- \+ *lemma* lie_submodule.coe_submodule_le_coe_submodule
- \+ *lemma* lie_submodule.coe_to_set_mk
- \+ *lemma* lie_submodule.coe_to_submodule
- \+ *lemma* lie_submodule.coe_to_submodule_eq_iff
- \+ *lemma* lie_submodule.coe_to_submodule_mk
- \+ *def* lie_submodule.comap
- \+ *lemma* lie_submodule.eq_bot_iff
- \+ *lemma* lie_submodule.ext
- \+ *lemma* lie_submodule.gc_map_comap
- \+ *def* lie_submodule.hom_of_le
- \+ *lemma* lie_submodule.hom_of_le_apply
- \+ *lemma* lie_submodule.hom_of_le_injective
- \+ *def* lie_submodule.incl
- \+ *lemma* lie_submodule.incl_apply
- \+ *lemma* lie_submodule.incl_eq_val
- \+ *theorem* lie_submodule.inf_coe
- \+ *lemma* lie_submodule.inf_coe_to_submodule
- \+ *lemma* lie_submodule.le_def
- \+ *def* lie_submodule.lie_span
- \+ *lemma* lie_submodule.lie_span_eq
- \+ *lemma* lie_submodule.lie_span_le
- \+ *lemma* lie_submodule.lie_span_mono
- \+ *def* lie_submodule.map
- \+ *lemma* lie_submodule.map_le_iff_le_comap
- \+ *lemma* lie_submodule.mem_bot
- \+ *lemma* lie_submodule.mem_carrier
- \+ *lemma* lie_submodule.mem_coe
- \+ *lemma* lie_submodule.mem_coe_submodule
- \+ *lemma* lie_submodule.mem_inf
- \+ *lemma* lie_submodule.mem_lie_span
- \+ *lemma* lie_submodule.mem_sup
- \+ *lemma* lie_submodule.mem_top
- \+ *lemma* lie_submodule.submodule_span_le_lie_span
- \+ *lemma* lie_submodule.subset_lie_span
- \+ *lemma* lie_submodule.subsingleton_of_bot
- \+ *lemma* lie_submodule.sup_coe_to_submodule
- \+ *lemma* lie_submodule.top_coe
- \+ *lemma* lie_submodule.top_coe_submodule
- \+ *lemma* lie_submodule.well_founded_of_noetherian
- \+ *lemma* lie_submodule.zero_mem

Modified src/algebra/lie/universal_enveloping.lean


Modified src/ring_theory/derivation.lean




## [2021-02-11 06:02:45](https://github.com/leanprover-community/mathlib/commit/97f89af)
doc(algebra/euclidean_domain): module doc ([#6107](https://github.com/leanprover-community/mathlib/pull/6107))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/euclidean_domain.lean




## [2021-02-11 06:02:43](https://github.com/leanprover-community/mathlib/commit/906e03d)
chore(field_theory,ring_theory): reduce dependencies of `power_basis.lean` ([#6104](https://github.com/leanprover-community/mathlib/pull/6104))
I was having trouble with circular imports related to `power_basis.lean`, so I decided to reshuffle some definitions to make `power_basis.lean` have less dependencies. That way, something depending on `power_basis` doesn't also need to depend on `intermediate_field.adjoin`.
The following (main) declarations are moved:
 - `algebra.adjoin`: from `ring_theory/adjoin.lean` to `ring_theory/adjoin/basic.lean` (renamed file)
 - `algebra.adjoin.power_basis`: from `ring_theory/power_basis.lean` to `ring_theory/adjoin/power_basis.lean` (new file)
 - `adjoin_root.power_basis`: from `ring_theory/power_basis.lean` to `ring_theory/adjoin_root.lean`
 - `intermediate_field.adjoin.power_basis`: from `ring_theory/power_basis.lean` to `field_theory/adjoin.lean`
 - `is_scalar_tower.polynomial`: from `ring_theory/algebra_tower.lean` to `ring_theory/polynomial/tower.lean` (new file)
The following results are new:
 - `is_integral.linear_independent_pow` and `is_integral.mem_span_pow`: generalize `algebra.adjoin.linear_independent_power_basis` and `algebra.adjoin.mem_span_power_basis`.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* intermediate_field.adjoin.findim
- \+ *lemma* intermediate_field.adjoin.finite_dimensional
- \+ *lemma* intermediate_field.adjoin.power_basis.gen_eq
- \+ *lemma* intermediate_field.power_basis_is_basis
- \+ *lemma* power_basis.equiv_adjoin_simple_aeval
- \+ *lemma* power_basis.equiv_adjoin_simple_gen
- \+ *lemma* power_basis.equiv_adjoin_simple_symm_aeval
- \+ *lemma* power_basis.equiv_adjoin_simple_symm_gen

Modified src/field_theory/minpoly.lean


Modified src/field_theory/normal.lean


Renamed src/ring_theory/adjoin.lean to src/ring_theory/adjoin/basic.lean


Added src/ring_theory/adjoin/default.lean


Added src/ring_theory/adjoin/power_basis.lean
- \+ *lemma* algebra.power_basis_is_basis

Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* adjoin_root.power_basis_is_basis

Modified src/ring_theory/algebra_tower.lean
- \- *theorem* is_scalar_tower.aeval_apply
- \- *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \- *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field
- \- *lemma* is_scalar_tower.algebra_map_aeval
- \- *lemma* subalgebra.aeval_coe

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Added src/ring_theory/polynomial/tower.lean
- \+ *theorem* is_scalar_tower.aeval_apply
- \+ *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+ *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field
- \+ *lemma* is_scalar_tower.algebra_map_aeval
- \+ *lemma* subalgebra.aeval_coe

Modified src/ring_theory/power_basis.lean
- \- *lemma* adjoin_root.power_basis_is_basis
- \- *lemma* algebra.linear_independent_power_basis
- \- *lemma* algebra.mem_span_power_basis
- \- *lemma* algebra.power_basis_is_basis
- \- *lemma* intermediate_field.adjoin.findim
- \- *lemma* intermediate_field.adjoin.finite_dimensional
- \- *lemma* intermediate_field.adjoin.power_basis.gen_eq
- \- *lemma* intermediate_field.power_basis_is_basis
- \+ *lemma* is_integral.linear_independent_pow
- \+ *lemma* is_integral.mem_span_pow
- \- *lemma* power_basis.equiv_adjoin_simple_aeval
- \- *lemma* power_basis.equiv_adjoin_simple_gen
- \- *lemma* power_basis.equiv_adjoin_simple_symm_aeval
- \- *lemma* power_basis.equiv_adjoin_simple_symm_gen



## [2021-02-11 06:02:41](https://github.com/leanprover-community/mathlib/commit/330129d)
feat(data/finset/lattice): `inf` and `sup` on complete_linear_orders produce an element of the set ([#6103](https://github.com/leanprover-community/mathlib/pull/6103))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.exists_mem_eq_inf
- \+ *lemma* finset.exists_mem_eq_sup



## [2021-02-11 06:02:39](https://github.com/leanprover-community/mathlib/commit/3959a8b)
perf(ring_theory/{noetherian,ideal/basic}): Simplify proofs of Krull's theorem and related theorems ([#6082](https://github.com/leanprover-community/mathlib/pull/6082))
Move `submodule.singleton_span_is_compact_element` and `submodule.is_compactly_generated` to more appropriate locations. Add trivial order isomorphisms and order-iso lemmas. Show that `is_atomic` and `is_coatomic` are respected by order isomorphisms. Greatly simplify `is_noetherian_iff_well_founded`. Provide an `is_coatomic` instance on the ideal lattice of a ring and simplify `ideal.exists_le_maximal`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.singleton_span_is_compact_element

Modified src/order/atoms.lean
- \+ *lemma* order_iso.is_atomic_iff
- \+ *lemma* order_iso.is_coatomic_iff

Modified src/order/compactly_generated.lean
- \+ *lemma* complete_lattice.coatomic_of_top_compact

Modified src/order/rel_iso.lean
- \+ *def* order_iso.Ici_bot
- \+ *def* order_iso.Iic_top
- \+ *lemma* order_iso.apply_eq_iff_eq_symm_apply

Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/noetherian.lean
- \- *lemma* submodule.singleton_span_is_compact_element



## [2021-02-11 00:37:06](https://github.com/leanprover-community/mathlib/commit/030107f)
feat(order/compactly_generated): A compactly-generated modular lattice is complemented iff atomistic ([#6071](https://github.com/leanprover-community/mathlib/pull/6071))
Shows that a compactly-generated modular lattice is complemented iff it is atomistic
Proves extra lemmas about atomistic or compactly-generated lattices
Proves extra lemmas about `complete_lattice.independent`
Fix the name of `is_modular_lattice.sup_inf_sup_assoc`
#### Estimated changes
Modified docs/references.bib


Modified src/order/atoms.lean
- \+ *theorem* Sup_atoms_eq_top
- \+ *theorem* Sup_atoms_le_eq
- \+ *theorem* le_iff_atom_le_imp

Modified src/order/compactly_generated.lean
- \+ *theorem* Sup_compact_eq_top
- \+ *lemma* complete_lattice.independent_Union_of_directed
- \+ *lemma* complete_lattice.independent_sUnion_of_directed
- \+ *theorem* is_complemented_iff_is_atomistic
- \+ *theorem* is_complemented_of_is_atomistic

Modified src/order/complete_lattice.lean
- \+ *lemma* Sup_sUnion
- \+ *lemma* complete_lattice.independent_empty

Modified src/order/modular_lattice.lean
- \+ *theorem* disjoint.disjoint_sup_right_of_disjoint_sup_left
- \+ *theorem* is_modular_lattice.inf_sup_inf_assoc
- \+ *theorem* is_modular_lattice_iff_inf_sup_inf_assoc
- \- *theorem* is_modular_lattice_iff_sup_inf_sup_assoc



## [2021-02-11 00:37:04](https://github.com/leanprover-community/mathlib/commit/7fb7fb3)
feat(ring_theory/polynomial/chebyshev/dickson): Introduce generalised Dickson polynomials ([#5869](https://github.com/leanprover-community/mathlib/pull/5869))
and replace lambdashev with dickson 1 1.
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/polynomial/chebyshev/basic.lean
- \+ *lemma* polynomial.chebyshev₁_eq_dickson_one_one
- \- *lemma* polynomial.chebyshev₁_eq_lambdashev
- \+ *lemma* polynomial.dickson_one_one_char_p
- \+ *lemma* polynomial.dickson_one_one_comp_comm
- \+ *lemma* polynomial.dickson_one_one_eq_chebyshev₁
- \+ *lemma* polynomial.dickson_one_one_eval_add_inv
- \+ *lemma* polynomial.dickson_one_one_mul
- \+ *lemma* polynomial.dickson_one_one_zmod_p
- \- *lemma* polynomial.lambdashev_char_p
- \- *lemma* polynomial.lambdashev_comp_comm
- \- *lemma* polynomial.lambdashev_eq_chebyshev₁
- \- *lemma* polynomial.lambdashev_eval_add_inv
- \- *lemma* polynomial.lambdashev_mul
- \- *lemma* polynomial.lambdashev_zmod_p

Modified src/ring_theory/polynomial/chebyshev/defs.lean
- \- *lemma* polynomial.lambdashev_add_two
- \- *lemma* polynomial.lambdashev_eq_two_le
- \- *lemma* polynomial.lambdashev_one
- \- *lemma* polynomial.lambdashev_two
- \- *lemma* polynomial.lambdashev_zero
- \- *lemma* polynomial.map_lambdashev

Added src/ring_theory/polynomial/chebyshev/dickson.lean
- \+ *lemma* polynomial.dickson_add_two
- \+ *lemma* polynomial.dickson_of_two_le
- \+ *lemma* polynomial.dickson_one
- \+ *lemma* polynomial.dickson_two
- \+ *lemma* polynomial.dickson_two_zero
- \+ *lemma* polynomial.dickson_zero
- \+ *lemma* polynomial.map_dickson



## [2021-02-11 00:37:02](https://github.com/leanprover-community/mathlib/commit/c70feeb)
feat(analysis/analytic/inverse): convergence of the inverse of a power series ([#5854](https://github.com/leanprover-community/mathlib/pull/5854))
If a formal multilinear series has a positive radius of convergence, then its inverse also does.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/geom_sum.lean
- \+ *theorem* geom_sum_Ico'

Modified src/analysis/analytic/basic.lean
- \+ *lemma* formal_multilinear_series.le_mul_pow_of_radius_pos

Modified src/analysis/analytic/composition.lean


Modified src/analysis/analytic/inverse.lean
- \+ *theorem* formal_multilinear_series.radius_right_inv_pos_of_radius_pos
- \+ *lemma* formal_multilinear_series.radius_right_inv_pos_of_radius_pos_aux1
- \+ *lemma* formal_multilinear_series.radius_right_inv_pos_of_radius_pos_aux2

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_linear_map.norm_comp_continuous_multilinear_map_le
- \+ *lemma* continuous_multilinear_curry_fin0_apply_norm
- \+ *lemma* continuous_multilinear_curry_fin0_symm_apply_norm
- \+ *lemma* continuous_multilinear_curry_fin1_apply_norm
- \+ *lemma* continuous_multilinear_curry_fin1_symm_apply_norm
- \+ *lemma* continuous_multilinear_curry_right_equiv_apply_norm
- \+ *lemma* continuous_multilinear_curry_right_equiv_symm_apply_norm



## [2021-02-11 00:37:00](https://github.com/leanprover-community/mathlib/commit/19f24ce)
feat(algebra/subalgebra): Trivial subalgebra has trivial automorphism group ([#5672](https://github.com/leanprover-community/mathlib/pull/5672))
Adds a lemma stating that if top=bot in the subalgebra type then top=bot in the subgroup type.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.alg_equiv.subsingleton_left
- \+ *lemma* subalgebra.alg_equiv.subsingleton_right
- \+ *lemma* subalgebra.alg_hom.subsingleton
- \+ *lemma* subalgebra.subsingleton_of_subsingleton

Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-02-11 00:36:58](https://github.com/leanprover-community/mathlib/commit/983cb90)
feat(archive/imo): formalize 1987Q1 ([#4731](https://github.com/leanprover-community/mathlib/pull/4731))
#### Estimated changes
Added archive/imo/imo1987_q1.lean
- \+ *theorem* imo_1987_q1.card_fixed_points
- \+ *def* imo_1987_q1.fiber
- \+ *def* imo_1987_q1.fixed_points_equiv'
- \+ *def* imo_1987_q1.fixed_points_equiv
- \+ *theorem* imo_1987_q1.main
- \+ *theorem* imo_1987_q1.main_fintype
- \+ *theorem* imo_1987_q1.main₀
- \+ *lemma* imo_1987_q1.mem_fiber
- \+ *def* imo_1987_q1.p



## [2021-02-10 21:01:42](https://github.com/leanprover-community/mathlib/commit/13c9ed3)
refactor(data/finset/basic): simplify proof ([#6160](https://github.com/leanprover-community/mathlib/pull/6160))
... of `bUnion_filter_eq_of_maps_to`
looks nicer, slightly faster elaboration, 13% smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/finset/basic.lean




## [2021-02-10 21:01:40](https://github.com/leanprover-community/mathlib/commit/0bc7fc1)
refactor(ring_theory/perfection): faster proof of `coeff_frobenius` ([#6159](https://github.com/leanprover-community/mathlib/pull/6159))
4X smaller proof term, elaboration 800ms -> 50ms
Co-authors: `lean-gptf`, Stanislas Polu
Note: supplying `coeff_pow_p f n` also works but takes 500ms to
elaborate
#### Estimated changes
Modified src/ring_theory/perfection.lean




## [2021-02-10 21:01:38](https://github.com/leanprover-community/mathlib/commit/6e52dfe)
feat(algebra/category/Group/adjunctions): adjunction of abelianization and forgetful functor ([#6154](https://github.com/leanprover-community/mathlib/pull/6154))
Abelianization has been defined in `group_theory/abelianization` without realising it in category theory. This PR adds this feature. Furthermore, a module doc for abelianization is added and the one for adjunctions is expanded.
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean
- \+ *def* abelianize
- \+ *def* abelianize_adj

Modified src/group_theory/abelianization.lean
- \+ *def* abelianization.hom_equiv



## [2021-02-10 21:01:36](https://github.com/leanprover-community/mathlib/commit/bce1cb3)
feat(linear_algebra/matrix): lemmas for `reindex({_linear,_alg}_equiv)?` ([#6153](https://github.com/leanprover-community/mathlib/pull/6153))
This PR contains a couple of `simp` lemmas for `reindex` and its bundled equivs. Namely, it adds `reindex_refl` (reindexing along the identity map is the identity), and `reindex_apply` (the same as `coe_reindex`, but no `λ i j` on the RHS, which makes it more useful for `rw`'ing.) The previous `reindex_apply` is renamed `coe_reindex` for disambiguation.
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.coe_reindex_alg_equiv
- \+ *lemma* matrix.coe_reindex_alg_equiv_symm
- \+ *lemma* matrix.coe_reindex_linear_equiv
- \+ *lemma* matrix.coe_reindex_linear_equiv_symm
- \+ *lemma* matrix.reindex_alg_equiv_refl
- \+/\- *lemma* matrix.reindex_linear_equiv_apply
- \+ *lemma* matrix.reindex_linear_equiv_refl_refl
- \+/\- *lemma* matrix.reindex_linear_equiv_symm_apply
- \+ *lemma* matrix.reindex_refl_refl



## [2021-02-10 21:01:35](https://github.com/leanprover-community/mathlib/commit/eca4f38)
feat(data/int/basic): an integer of absolute value less than one is zero ([#6151](https://github.com/leanprover-community/mathlib/pull/6151))
lemma eq_zero_iff_abs_lt_one
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.eq_zero_iff_abs_lt_one



## [2021-02-10 21:01:33](https://github.com/leanprover-community/mathlib/commit/14a1fd7)
feat(data/nat/basic): le_of_add_le_* ([#6145](https://github.com/leanprover-community/mathlib/pull/6145))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_of_add_le_left
- \+ *lemma* nat.le_of_add_le_right

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.le_of_add_le_left
- \+ *lemma* nnreal.le_of_add_le_right



## [2021-02-10 21:01:31](https://github.com/leanprover-community/mathlib/commit/dbbac3b)
chore(algebra/module/pi): add missing smul_comm_class instances ([#6139](https://github.com/leanprover-community/mathlib/pull/6139))
There are three families of these for consistency with how we have three families of `is_scalar_tower` instances.
#### Estimated changes
Modified src/algebra/module/pi.lean




## [2021-02-10 21:01:30](https://github.com/leanprover-community/mathlib/commit/56fde49)
feat(data/polynomial/denoms_clearable): add lemma about clearing denominators in evaluating a polynomial ([#6122](https://github.com/leanprover-community/mathlib/pull/6122))
Evaluating a polynomial with integer coefficients at a rational number and clearing denominators, yields a number greater than or equal to one.  The target can be any `linear_ordered_field K`.
The assumption on `K` could be weakened to `linear_ordered_comm_ring` assuming that the
image of the denominator is invertible in `K`.
Reference: Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).
#### Estimated changes
Modified src/data/polynomial/denoms_clearable.lean
- \+ *lemma* one_le_pow_mul_abs_eval_div



## [2021-02-10 21:01:28](https://github.com/leanprover-community/mathlib/commit/db0fa61)
feat(category_theory/differential_object): the shift functor ([#6111](https://github.com/leanprover-community/mathlib/pull/6111))
Requested by @jcommelin.
#### Estimated changes
Modified src/category_theory/differential_object.lean
- \+ *def* category_theory.differential_object.shift_counit
- \+ *def* category_theory.differential_object.shift_counit_inv
- \+ *def* category_theory.differential_object.shift_counit_iso
- \+ *def* category_theory.differential_object.shift_functor
- \+ *def* category_theory.differential_object.shift_inverse
- \+ *def* category_theory.differential_object.shift_inverse_obj
- \+ *def* category_theory.differential_object.shift_unit
- \+ *def* category_theory.differential_object.shift_unit_inv
- \+ *def* category_theory.differential_object.shift_unit_iso



## [2021-02-10 17:50:05](https://github.com/leanprover-community/mathlib/commit/f0413da)
refactor(combinatorics/simple_graph/basic): change statement of mem_decidable to more general version ([#6157](https://github.com/leanprover-community/mathlib/pull/6157))
Change statement of `mem_decidable` to more general version.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-02-10 17:50:03](https://github.com/leanprover-community/mathlib/commit/83118da)
feat(data/nat/basic): prove an inequality of natural numbers ([#6155](https://github.com/leanprover-community/mathlib/pull/6155))
Add lemma mul_lt_mul_pow_succ, proving the inequality `n * q < a * q ^ (n + 1)`.
Reference: Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.mul_lt_mul_pow_succ



## [2021-02-10 17:50:01](https://github.com/leanprover-community/mathlib/commit/ca8e009)
feat(data/polynomial/ring_division): comp_eq_zero_iff ([#6147](https://github.com/leanprover-community/mathlib/pull/6147))
Condition for a composition of polynomials to be zero (assuming that the ring is an integral domain).
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.comp_eq_zero_iff



## [2021-02-10 17:49:59](https://github.com/leanprover-community/mathlib/commit/41530ae)
feat(field_theory/splitting_field): splits_of_nat_degree_le_one ([#6146](https://github.com/leanprover-community/mathlib/pull/6146))
Adds the analogs of `splits_of_degree_eq_one` and `splits_of_degree_le_one` for `nat_degree`
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.splits_of_nat_degree_eq_one
- \+ *lemma* polynomial.splits_of_nat_degree_le_one



## [2021-02-10 17:49:57](https://github.com/leanprover-community/mathlib/commit/3fae96c)
feat(algebra/ordered_monoid): min_*_distrib ([#6144](https://github.com/leanprover-community/mathlib/pull/6144))
Also provide a `canonically_linear_ordered_add_monoid` instances for `nat`, `nnreal`, `cardinal` and `with_top`.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+ *lemma* min_mul_distrib'
- \+ *lemma* min_mul_distrib

Modified src/data/nat/basic.lean


Modified src/data/real/nnreal.lean


Modified src/set_theory/cardinal.lean




## [2021-02-10 17:49:55](https://github.com/leanprover-community/mathlib/commit/3cc398b)
feat(linear_algebra/prod): add an ext lemma that recurses into products ([#6124](https://github.com/leanprover-community/mathlib/pull/6124))
Combined with [#6105](https://github.com/leanprover-community/mathlib/pull/6105), this means that applying `ext` when faced with an equality between `A × (B ⊗[R] C) →ₗ[R] D`s now expands to two goals, the first taking `a : A` and the second taking `b : B` and `c : C`.
Again, this comes at the expense of sometimes needing to `simp [prod.mk_fst, linear_map.inr_apply]` after using `ext`, but those are all covered by `dsimp` anyway.
#### Estimated changes
Modified src/linear_algebra/prod.lean
- \+ *theorem* linear_map.prod_ext



## [2021-02-10 15:17:41](https://github.com/leanprover-community/mathlib/commit/0854536)
feat(topology/constructions): add `map_fst_nhds` and `map_snd_nhds` ([#6142](https://github.com/leanprover-community/mathlib/pull/6142))
* Move the definition of `nhds_within` to `topology/basic`. The theory is still in `continuous_on`.
* Add `filter.map_inf_principal_preimage`.
* Add `map_fst_nhds_within`, `map_fst_nhds`, `map_snd_nhds_within`, and `map_snd_nhds`.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.map_inf_principal_preimage

Modified src/topology/basic.lean
- \+ *def* nhds_within

Modified src/topology/constructions.lean
- \+ *lemma* map_fst_nhds
- \+ *lemma* map_fst_nhds_within
- \+ *lemma* map_snd_nhds
- \+ *lemma* map_snd_nhds_within

Modified src/topology/continuous_on.lean
- \- *def* nhds_within



## [2021-02-10 15:17:39](https://github.com/leanprover-community/mathlib/commit/7fd4dcf)
feat(analysis/normed_space/operator_norm): bundle more arguments ([#6140](https://github.com/leanprover-community/mathlib/pull/6140))
* bundle the first argument of `continuous_linear_map.smul_rightL`;
* add `continuous_linear_map.flip` and `continuous_linear_map.flipₗᵢ`;
* use `flip` to redefine `apply`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.apply
- \+ *lemma* continuous_linear_map.coe_flipₗᵢ
- \+ *def* continuous_linear_map.flip
- \+ *lemma* continuous_linear_map.flip_add
- \+ *lemma* continuous_linear_map.flip_flip
- \+ *lemma* continuous_linear_map.flip_smul
- \+ *def* continuous_linear_map.flipₗᵢ
- \+ *lemma* continuous_linear_map.flipₗᵢ_symm
- \+ *lemma* continuous_linear_map.op_norm_flip
- \+/\- *def* continuous_linear_map.smul_rightL



## [2021-02-10 15:17:37](https://github.com/leanprover-community/mathlib/commit/d5e2029)
refactor(linear_algebra/basic): extract definitions about pi types to a new file ([#6130](https://github.com/leanprover-community/mathlib/pull/6130))
This makes it consistent with how the `prod` definitions are in their own file.
With each in its own file, it should be easier to unify the APIs between them.
This does not do anything other than copy across the definitions.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/basic.lean
- \- *def* linear_map.diag
- \- *lemma* linear_map.infi_ker_proj
- \- *def* linear_map.infi_ker_proj_equiv
- \- *lemma* linear_map.ker_pi
- \- *def* linear_map.pi
- \- *lemma* linear_map.pi_apply
- \- *lemma* linear_map.pi_comp
- \- *lemma* linear_map.pi_eq_zero
- \- *lemma* linear_map.pi_zero
- \- *def* linear_map.proj
- \- *lemma* linear_map.proj_apply
- \- *lemma* linear_map.proj_pi
- \- *lemma* linear_map.update_apply

Added src/linear_algebra/pi.lean
- \+ *def* linear_map.diag
- \+ *lemma* linear_map.infi_ker_proj
- \+ *def* linear_map.infi_ker_proj_equiv
- \+ *lemma* linear_map.ker_pi
- \+ *def* linear_map.pi
- \+ *lemma* linear_map.pi_apply
- \+ *lemma* linear_map.pi_comp
- \+ *lemma* linear_map.pi_eq_zero
- \+ *lemma* linear_map.pi_zero
- \+ *def* linear_map.proj
- \+ *lemma* linear_map.proj_apply
- \+ *lemma* linear_map.proj_pi
- \+ *lemma* linear_map.update_apply

Modified src/linear_algebra/std_basis.lean


Modified src/topology/algebra/module.lean




## [2021-02-10 11:14:03](https://github.com/leanprover-community/mathlib/commit/7a51c0f)
refactor(data/set/intervals/basic): simpler proof of `Iio_union_Ioo'` ([#6132](https://github.com/leanprover-community/mathlib/pull/6132))
proof term 2577 -> 1587 chars
elaboration time 130ms -> 75ms
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/data/set/intervals/basic.lean




## [2021-02-10 05:02:51](https://github.com/leanprover-community/mathlib/commit/5a2eac6)
refactor(order/closure): golf `closure_inter_le` ([#6138](https://github.com/leanprover-community/mathlib/pull/6138))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/order/closure.lean




## [2021-02-10 03:37:24](https://github.com/leanprover-community/mathlib/commit/0731a70)
chore(scripts): update nolints.txt ([#6143](https://github.com/leanprover-community/mathlib/pull/6143))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-10 00:03:36](https://github.com/leanprover-community/mathlib/commit/922ecb0)
chore(group_theory/perm/sign): speed up sign_aux_swap_zero_one proof ([#6128](https://github.com/leanprover-community/mathlib/pull/6128))
#### Estimated changes
Modified src/group_theory/perm/sign.lean




## [2021-02-10 00:03:34](https://github.com/leanprover-community/mathlib/commit/18b378d)
chore(data/fin): reorder file to group declarations ([#6109](https://github.com/leanprover-community/mathlib/pull/6109))
The `data/fin` file has a lot of definitions and lemmas. This reordering groups declarations and places ones that do not rely on `fin` operations first, like order. No definitions or lemma statements have been changed. A minimal amount of proofs have been rephrased. No reformatting of style has been done. Section titles have been added.
This is useful in preparation for redefining `fin` operations (lean[#527](https://github.com/leanprover-community/mathlib/pull/527)). Additionally, it allows for better organization for other refactors like making `pred` and `pred_above` total.
#### Estimated changes
Modified src/algebra/linear_recurrence.lean


Modified src/analysis/analytic/composition.lean


Modified src/data/fin.lean
- \+/\- *lemma* fin.mk_coe



## [2021-02-10 00:03:32](https://github.com/leanprover-community/mathlib/commit/4c1c11c)
feat(data/equiv/mul_add): monoids/rings with one element are isomorphic ([#6079](https://github.com/leanprover-community/mathlib/pull/6079))
Monoids (resp. add_monoids, semirings) with one element are isomorphic.
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.mul_equiv_of_unique_of_unique

Modified src/data/equiv/ring.lean
- \+ *def* ring_equiv.ring_equiv_of_unique_of_unique



## [2021-02-10 00:03:30](https://github.com/leanprover-community/mathlib/commit/b34da00)
feat(algebra/geom_sum): adds further variants ([#6077](https://github.com/leanprover-community/mathlib/pull/6077))
This adds further variants for the value of `geom_series\2`. Additionally, a docstring is provided.
Thanks to Patrick Massot for help with the reindexing of sums.
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *lemma* commute.mul_geom_sum₂
- \+ *lemma* commute.mul_neg_geom_sum₂
- \+ *theorem* geom_sum₂_Ico
- \- *theorem* geom_sum₂_mul_comm
- \+ *theorem* geom₂_sum
- \+ *theorem* mul_geom_sum₂_Ico
- \+ *lemma* op_geom_series₂

Modified src/algebra/opposites.lean
- \+ *lemma* opposite.commute.op
- \+ *lemma* opposite.commute.unop
- \+ *lemma* opposite.commute_op
- \+ *lemma* opposite.commute_unop
- \+ *lemma* opposite.semiconj_by.op
- \+ *lemma* opposite.semiconj_by.unop
- \+ *lemma* opposite.semiconj_by_op
- \+ *lemma* opposite.semiconj_by_unop



## [2021-02-10 00:03:28](https://github.com/leanprover-community/mathlib/commit/49e50ee)
feat(measure_theory/lp_space): add more API on Lp spaces ([#6042](https://github.com/leanprover-community/mathlib/pull/6042))
Flesh out the file on `L^p` spaces, notably adding facts on the composition with Lipschitz functions. This makes it possible to define in one go the positive part of an `L^p` function, and its image under a continuous linear map.
The file `ae_eq_fun.lean` is split into two, to solve a temporary issue: this file defines a global emetric space instance (of `L^1` type) on the space of function classes. This passes to subtypes, and clashes with the topology on `L^p` coming from the distance. This did not show up before as there were not enough topological statements on `L^p`, but I have been bitten by this when adding new results. For now, we move this part of `ae_eq_fun.lean` to another file which is not imported by `lp_space.lean`, to avoid the clash. This will be solved in a subsequent PR in which I will remove the global instance, and construct the integral based on the specialization of `L^p` to `p = 1` instead of the ad hoc construction we have now (note that, currently, we have two different `L^1` spaces in mathlib, denoted `Lp E 1 μ` and `α →₁[μ] E` -- I will remove the second one in a later PR).
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnreal.nnnorm_eq
- \+ *lemma* nnreal.norm_eq
- \- *lemma* real.nnnorm_coe_eq_self
- \- *lemma* real.nnreal.norm_eq

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/ess_sup.lean
- \+/\- *lemma* ennreal.ess_sup_eq_zero_iff

Modified src/measure_theory/lp_space.lean
- \+ *lemma* continuous_linear_map.coe_fn_comp_Lp
- \+ *def* continuous_linear_map.comp_Lp
- \+ *def* continuous_linear_map.comp_LpL
- \+ *def* continuous_linear_map.comp_Lpₗ
- \+ *lemma* continuous_linear_map.norm_compLpL_le
- \+ *lemma* continuous_linear_map.norm_comp_Lp_le
- \+ *lemma* fact_one_le_one_ennreal
- \+ *lemma* fact_one_le_top_ennreal
- \+ *lemma* fact_one_le_two_ennreal
- \+ *lemma* lipschitz_with.coe_fn_comp_Lp
- \+ *def* lipschitz_with.comp_Lp
- \+ *lemma* lipschitz_with.comp_Lp_zero
- \+ *lemma* lipschitz_with.continuous_comp_Lp
- \+ *lemma* lipschitz_with.lipschitz_with_comp_Lp
- \+ *lemma* lipschitz_with.norm_comp_Lp_le
- \+ *lemma* lipschitz_with.norm_comp_Lp_sub_le
- \- *lemma* measure_theory.Lp.ae_measurable
- \+/\- *lemma* measure_theory.Lp.coe_fn_add
- \+/\- *lemma* measure_theory.Lp.coe_fn_mk
- \+/\- *lemma* measure_theory.Lp.coe_fn_neg
- \+ *lemma* measure_theory.Lp.coe_fn_neg_part
- \+ *lemma* measure_theory.Lp.coe_fn_neg_part_eq_max
- \+ *lemma* measure_theory.Lp.coe_fn_pos_part
- \+/\- *lemma* measure_theory.Lp.coe_fn_smul
- \+/\- *lemma* measure_theory.Lp.coe_fn_sub
- \+ *lemma* measure_theory.Lp.coe_mk
- \+ *lemma* measure_theory.Lp.coe_pos_part
- \+ *lemma* measure_theory.Lp.continuous_neg_part
- \+ *lemma* measure_theory.Lp.continuous_pos_part
- \+ *lemma* measure_theory.Lp.dist_def
- \+ *lemma* measure_theory.Lp.edist_def
- \+ *lemma* measure_theory.Lp.edist_to_Lp_to_Lp
- \+ *lemma* measure_theory.Lp.edist_to_Lp_zero
- \+ *lemma* measure_theory.Lp.eq_zero_iff_ae_eq_zero
- \+ *lemma* measure_theory.Lp.ext
- \+ *lemma* measure_theory.Lp.ext_iff
- \+ *lemma* measure_theory.Lp.lipschitz_with_pos_part
- \- *lemma* measure_theory.Lp.measurable
- \+ *lemma* measure_theory.Lp.mem_Lp_iff_mem_ℒp
- \+ *lemma* measure_theory.Lp.mem_Lp_of_ae_le
- \+ *lemma* measure_theory.Lp.mem_Lp_of_ae_le_mul
- \- *lemma* measure_theory.Lp.mem_ℒp
- \+ *def* measure_theory.Lp.neg_part
- \+ *lemma* measure_theory.Lp.norm_le_mul_norm_of_ae_le_mul
- \+ *lemma* measure_theory.Lp.norm_le_norm_of_ae_le
- \+ *lemma* measure_theory.Lp.norm_to_Lp
- \+ *def* measure_theory.Lp.pos_part
- \+ *lemma* measure_theory.Lp.to_Lp_coe_fn
- \+/\- *lemma* measure_theory.ae_eq_zero_of_snorm'_eq_zero
- \+/\- *lemma* measure_theory.lintegral_rpow_nnnorm_eq_rpow_snorm'
- \+/\- *lemma* measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
- \+/\- *lemma* measure_theory.mem_ℒp.add
- \+/\- *lemma* measure_theory.mem_ℒp.ae_eq
- \+ *lemma* measure_theory.mem_ℒp.ae_measurable
- \+/\- *lemma* measure_theory.mem_ℒp.coe_fn_to_Lp
- \+ *lemma* measure_theory.mem_ℒp.const_mul
- \+/\- *lemma* measure_theory.mem_ℒp.const_smul
- \- *lemma* measure_theory.mem_ℒp.integrable
- \+/\- *lemma* measure_theory.mem_ℒp.neg
- \+ *lemma* measure_theory.mem_ℒp.norm
- \+ *lemma* measure_theory.mem_ℒp.of_le
- \+ *lemma* measure_theory.mem_ℒp.of_le_mul
- \+/\- *lemma* measure_theory.mem_ℒp.snorm_lt_top
- \+/\- *lemma* measure_theory.mem_ℒp.snorm_ne_top
- \+/\- *lemma* measure_theory.mem_ℒp.sub
- \+/\- *def* measure_theory.mem_ℒp.to_Lp
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_add
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_const_smul
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_eq_to_Lp_iff
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_neg
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_sub
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_zero
- \+/\- *lemma* measure_theory.mem_ℒp_congr_ae
- \+/\- *lemma* measure_theory.mem_ℒp_const
- \- *lemma* measure_theory.mem_ℒp_one_iff_integrable
- \+/\- *def* measure_theory.snorm'
- \+/\- *lemma* measure_theory.snorm'_add_le
- \+/\- *lemma* measure_theory.snorm'_congr_ae
- \+ *lemma* measure_theory.snorm'_congr_norm_ae
- \+/\- *lemma* measure_theory.snorm'_const'
- \+/\- *lemma* measure_theory.snorm'_const
- \+/\- *lemma* measure_theory.snorm'_const_of_probability_measure
- \+/\- *lemma* measure_theory.snorm'_const_smul
- \+/\- *lemma* measure_theory.snorm'_eq_zero_iff
- \+/\- *lemma* measure_theory.snorm'_eq_zero_of_ae_zero'
- \+/\- *lemma* measure_theory.snorm'_eq_zero_of_ae_zero
- \+/\- *lemma* measure_theory.snorm'_le_snorm_ess_sup
- \+/\- *lemma* measure_theory.snorm'_le_snorm_ess_sup_mul_rpow_measure_univ
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_neg
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_pos
- \+ *lemma* measure_theory.snorm'_mono_ae
- \+/\- *lemma* measure_theory.snorm'_neg
- \+/\- *lemma* measure_theory.snorm'_zero'
- \+/\- *lemma* measure_theory.snorm'_zero
- \+/\- *def* measure_theory.snorm
- \+/\- *lemma* measure_theory.snorm_add_le
- \+/\- *lemma* measure_theory.snorm_add_lt_top
- \+/\- *lemma* measure_theory.snorm_add_lt_top_of_one_le
- \+/\- *lemma* measure_theory.snorm_congr_ae
- \+ *lemma* measure_theory.snorm_congr_norm_ae
- \+/\- *lemma* measure_theory.snorm_const'
- \+/\- *lemma* measure_theory.snorm_const
- \+/\- *lemma* measure_theory.snorm_eq_snorm'
- \+/\- *lemma* measure_theory.snorm_eq_zero_iff
- \+/\- *lemma* measure_theory.snorm_ess_sup_eq_zero_iff
- \+ *lemma* measure_theory.snorm_le_mul_snorm_aux_of_neg
- \+ *lemma* measure_theory.snorm_le_mul_snorm_aux_of_nonneg
- \+ *lemma* measure_theory.snorm_le_mul_snorm_of_ae_le_mul
- \+/\- *lemma* measure_theory.snorm_measure_zero
- \+ *lemma* measure_theory.snorm_mono_ae
- \+/\- *lemma* measure_theory.snorm_neg
- \+ *lemma* measure_theory.snorm_norm
- \+/\- *lemma* measure_theory.snorm_zero
- \+/\- *lemma* measure_theory.zero_mem_ℒp



## [2021-02-10 00:03:26](https://github.com/leanprover-community/mathlib/commit/7c77279)
feat(category_theory/monad): use bundled monads everywhere ([#5889](https://github.com/leanprover-community/mathlib/pull/5889))
This PR makes bundled monads the default (adapting definitions by @adamtopaz). The main motivation for this is that the category of algebras for a monad is currently not "hygienic" in that isomorphic monads don't have equivalent Eilenberg-Moore categories, but further that the notion of monad isomorphism is tricky to express, in particular this makes the definition of a monadic functor not preserved by isos either despite not explicitly having monads or algebras in the type.
We can now say:
```
@[simps]
def algebra_equiv_of_iso_monads {T₁ T₂ : monad C} (h : T₁ ≅ T₂) :
  algebra T₁ ≌ algebra T₂ :=
```
Other than this new data, virtually everything in this PR is just refactoring - in particular there's quite a bit of golfing and generalisation possible, but to keep the diff here minimal I'll do those in later PRs
#### Estimated changes
Modified src/category_theory/adjunction/lifting.lean


Modified src/category_theory/monad/adjunction.lean
- \+ *def* category_theory.adjunction.to_comonad
- \+ *def* category_theory.adjunction.to_monad
- \+/\- *def* category_theory.comonad.comparison
- \- *def* category_theory.comonad.comparison_forget
- \+ *def* category_theory.comparison_forget
- \+/\- *def* category_theory.monad.comparison
- \+/\- *def* category_theory.monad.comparison_forget

Modified src/category_theory/monad/algebra.lean
- \+/\- *def* category_theory.monad.adj
- \+ *def* category_theory.monad.algebra_equiv_of_iso_monads
- \+ *lemma* category_theory.monad.algebra_equiv_of_iso_monads_comp_forget
- \+ *def* category_theory.monad.algebra_functor_of_monad_hom
- \+ *def* category_theory.monad.algebra_functor_of_monad_hom_comp
- \+ *def* category_theory.monad.algebra_functor_of_monad_hom_eq
- \+ *def* category_theory.monad.algebra_functor_of_monad_hom_id

Modified src/category_theory/monad/basic.lean
- \+ *lemma* category_theory.comonad.coassoc
- \+ *def* category_theory.comonad.id
- \+ *lemma* category_theory.comonad.left_counit
- \+ *lemma* category_theory.comonad.right_counit
- \+ *def* category_theory.comonad.simps.to_functor
- \+ *def* category_theory.comonad.simps.δ'
- \+ *def* category_theory.comonad.simps.ε'
- \+ *def* category_theory.comonad.δ
- \+ *def* category_theory.comonad.ε
- \- *lemma* category_theory.comonad_hom.assoc
- \- *def* category_theory.comonad_hom.comp
- \- *lemma* category_theory.comonad_hom.comp_id
- \- *theorem* category_theory.comonad_hom.ext
- \- *def* category_theory.comonad_hom.id
- \- *lemma* category_theory.comonad_hom.id_comp
- \+ *lemma* category_theory.comonad_hom.id_to_nat_trans
- \+ *def* category_theory.comonad_iso.to_nat_iso
- \+ *def* category_theory.comonad_to_functor
- \+ *lemma* category_theory.comonad_to_functor_eq_coe
- \+ *lemma* category_theory.comp_to_nat_trans
- \+ *lemma* category_theory.monad.assoc
- \+ *def* category_theory.monad.id
- \+ *lemma* category_theory.monad.left_unit
- \+ *lemma* category_theory.monad.right_unit
- \+ *def* category_theory.monad.simps.to_functor
- \+ *def* category_theory.monad.simps.η'
- \+ *def* category_theory.monad.simps.μ'
- \+ *def* category_theory.monad.η
- \+ *def* category_theory.monad.μ
- \- *lemma* category_theory.monad_hom.assoc
- \- *def* category_theory.monad_hom.comp
- \- *lemma* category_theory.monad_hom.comp_id
- \+ *lemma* category_theory.monad_hom.comp_to_nat_trans
- \- *theorem* category_theory.monad_hom.ext
- \- *def* category_theory.monad_hom.id
- \- *lemma* category_theory.monad_hom.id_comp
- \+ *lemma* category_theory.monad_hom.id_to_nat_trans
- \+ *def* category_theory.monad_iso.to_nat_iso
- \+ *def* category_theory.monad_to_functor
- \+ *lemma* category_theory.monad_to_functor_eq_coe

Modified src/category_theory/monad/bundled.lean
- \- *lemma* category_theory.Comonad.coassoc_func_app
- \- *lemma* category_theory.Comonad.comp_to_nat_trans
- \- *def* category_theory.Comonad.forget
- \- *def* category_theory.Comonad.hom
- \- *def* category_theory.Comonad.terminal
- \- *lemma* category_theory.Monad.assoc_func_app
- \- *lemma* category_theory.Monad.comp_to_nat_trans
- \- *def* category_theory.Monad.forget
- \- *def* category_theory.Monad.hom
- \- *def* category_theory.Monad.initial

Modified src/category_theory/monad/coequalizer.lean
- \+/\- *def* category_theory.monad.beck_cofork
- \+/\- *def* category_theory.monad.beck_split_coequalizer

Modified src/category_theory/monad/equiv_mon.lean
- \+/\- *def* category_theory.Monad.Mon_to_Monad
- \+/\- *def* category_theory.Monad.Monad_Mon_equiv
- \+/\- *def* category_theory.Monad.Monad_to_Mon
- \+/\- *def* category_theory.Monad.of_Mon
- \+/\- *def* category_theory.Monad.to_Mon

Modified src/category_theory/monad/kleisli.lean
- \+/\- *def* category_theory.kleisli

Modified src/category_theory/monad/limits.lean
- \+/\- *def* category_theory.monad.forget_creates_colimits.lambda
- \+/\- *def* category_theory.monad.forget_creates_colimits.new_cocone
- \+/\- *def* category_theory.monad.forget_creates_colimits.γ
- \+/\- *def* category_theory.monad.forget_creates_limits.γ

Modified src/category_theory/monad/monadicity.lean
- \+/\- *def* category_theory.monad.monadicity_internal.comparison_left_adjoint_hom_equiv
- \+/\- *def* category_theory.monad.monadicity_internal.unit_cofork

Modified src/category_theory/monad/products.lean
- \+ *def* category_theory.coprod_monad
- \+ *def* category_theory.prod_comonad

Modified src/category_theory/monad/types.lean
- \+/\- *def* category_theory.eq
- \+ *def* category_theory.of_type_monad

Modified src/category_theory/monoidal/End.lean


Modified src/measure_theory/category/Meas.lean
- \+ *def* Meas.Giry
- \+/\- *def* Meas.Integral

Modified src/topology/category/Compactum.lean
- \+/\- *def* Compactum.incl
- \+/\- *def* Compactum.join



## [2021-02-09 20:17:00](https://github.com/leanprover-community/mathlib/commit/ba9e06e)
refactor(algebra/lie/basic): rm extraneous rewrite hypothesis ([#6137](https://github.com/leanprover-community/mathlib/pull/6137))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/algebra/lie/basic.lean




## [2021-02-09 20:16:58](https://github.com/leanprover-community/mathlib/commit/456bdb7)
refactor(measure_theory/measure_space): simplify proof ([#6136](https://github.com/leanprover-community/mathlib/pull/6136))
2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/measure_theory/measure_space.lean




## [2021-02-09 20:16:56](https://github.com/leanprover-community/mathlib/commit/c377e68)
refactor(ring_theory/polynomial/symmetric): simplify proof ([#6135](https://github.com/leanprover-community/mathlib/pull/6135))
... of `mv_polynomial.is_symmetric.sub`
2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/ring_theory/polynomial/symmetric.lean




## [2021-02-09 20:16:55](https://github.com/leanprover-community/mathlib/commit/eb2dcba)
refactor(*): remove uses of omega in the library ([#6129](https://github.com/leanprover-community/mathlib/pull/6129))
The transition to Lean 4 will be easier if we don't have to port omega.
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/lie/basic.lean


Modified src/algebra/linear_recurrence.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/combinatorics/composition.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/computability/regular_expressions.lean


Modified src/data/nat/choose/sum.lean


Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/ring_division.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/multilinear.lean


Modified src/number_theory/pell.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/cardinal_ordinal.lean




## [2021-02-09 20:16:52](https://github.com/leanprover-community/mathlib/commit/296899e)
refactor(data/string/basic): simplify proof of `to_list_nonempty` ([#6117](https://github.com/leanprover-community/mathlib/pull/6117))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/data/string/basic.lean
- \+/\- *lemma* string.to_list_nonempty



## [2021-02-09 20:16:49](https://github.com/leanprover-community/mathlib/commit/d9d56eb)
feat(analysis/special_functions/trigonometric): `complex.log` is smooth away from `(-∞, 0]` ([#6041](https://github.com/leanprover-community/mathlib/pull/6041))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_strict_deriv_at.comp_has_strict_fderiv_at
- \+ *lemma* local_homeomorph.has_strict_deriv_at_symm

Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.continuous_im
- \+/\- *lemma* complex.continuous_of_real
- \+ *lemma* complex.continuous_re

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.measurable_im
- \+ *lemma* complex.measurable_of_real
- \+ *lemma* complex.measurable_re

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.arg_eq_pi_iff
- \+ *def* complex.exp_local_homeomorph
- \+ *lemma* complex.has_strict_deriv_at_log
- \+ *lemma* complex.measurable_arg
- \+ *lemma* complex.measurable_log
- \+ *lemma* complex.times_cont_diff_at_log
- \+ *lemma* continuous.clog
- \+ *lemma* continuous_at.clog
- \+ *lemma* continuous_on.clog
- \+ *lemma* continuous_within_at.clog
- \+ *lemma* differentiable.clog
- \+ *lemma* differentiable_at.clog
- \+ *lemma* differentiable_on.clog
- \+ *lemma* differentiable_within_at.clog
- \+ *lemma* filter.tendsto.clog
- \+ *lemma* has_deriv_at.clog
- \+ *lemma* has_deriv_within_at.clog
- \+ *lemma* has_fderiv_at.clog
- \+ *lemma* has_fderiv_within_at.clog
- \+ *lemma* has_strict_deriv_at.clog
- \+ *lemma* has_strict_fderiv_at.clog
- \+ *lemma* measurable.carg
- \+ *lemma* measurable.clog

Modified src/data/complex/basic.lean
- \+ *lemma* complex.of_real_def

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.exp_im
- \+ *lemma* complex.exp_re

Modified src/data/equiv/local_equiv.lean


Modified src/data/set/function.lean
- \+ *lemma* set.image_restrict
- \+ *theorem* set.left_inv_on.image_inter'
- \+ *theorem* set.left_inv_on.image_inter

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable.const_mul
- \+ *lemma* measurable.div
- \+/\- *lemma* measurable.mul_const
- \+ *lemma* measurable.sub_const

Modified src/topology/continuous_on.lean


Modified src/topology/local_homeomorph.lean
- \+/\- *def* homeomorph.to_local_homeomorph
- \+ *def* local_homeomorph.of_continuous_open
- \+ *def* local_homeomorph.of_continuous_open_restrict



## [2021-02-09 16:47:39](https://github.com/leanprover-community/mathlib/commit/e8f383c)
refactor(analysis/special_functions/trigonometric): simpler proof ([#6133](https://github.com/leanprover-community/mathlib/pull/6133))
... of `complex.tan_int_mul_pi`
3X faster elaboration, 2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean




## [2021-02-09 16:47:37](https://github.com/leanprover-community/mathlib/commit/bf1465c)
refactor(data/fintype/basic): golf `card_eq_one_of_forall_eq` ([#6131](https://github.com/leanprover-community/mathlib/pull/6131))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2021-02-09 16:47:34](https://github.com/leanprover-community/mathlib/commit/fdbd4bf)
feat(archive/imo): formalize solution to IMO 2013 problem Q1 ([#6110](https://github.com/leanprover-community/mathlib/pull/6110))
#### Estimated changes
Added archive/imo/imo2013_q1.lean
- \+ *lemma* arith_lemma
- \+ *theorem* imo2013_q1
- \+ *lemma* prod_lemma



## [2021-02-09 14:41:24](https://github.com/leanprover-community/mathlib/commit/aa9e2b8)
feat(analysis/normed_space/operator_norm): lemmas about `E →L[𝕜] F →L[𝕜] G` ([#6102](https://github.com/leanprover-community/mathlib/pull/6102))
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* continuous_linear_map.le_op_norm₂
- \+ *theorem* continuous_linear_map.op_norm_le_bound₂
- \+/\- *lemma* linear_isometry.norm_to_continuous_linear_map
- \+/\- *lemma* linear_isometry.norm_to_continuous_linear_map_le
- \+ *lemma* linear_map.mk_continuous_norm_le'
- \+/\- *lemma* linear_map.mk_continuous_norm_le
- \+ *def* linear_map.mk_continuous₂
- \+ *lemma* linear_map.mk_continuous₂_apply
- \+ *lemma* linear_map.mk_continuous₂_norm_le'
- \+ *lemma* linear_map.mk_continuous₂_norm_le



## [2021-02-09 14:41:22](https://github.com/leanprover-community/mathlib/commit/766146b)
fix(topology/algebra/infinite_sum): remove hard-coding of ℕ and ℝ ([#6096](https://github.com/leanprover-community/mathlib/pull/6096))
It may be possible to make these assumptions stricter, but they're weak enough to still cover the original use case.
Hopefully that can be handled by @alexjbest's upcoming linter to relax assumptions.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.update
- \+ *lemma* has_sum_lt
- \+ *lemma* has_sum_mono
- \+ *lemma* has_sum_strict_mono
- \+ *lemma* summable.update
- \+/\- *lemma* tsum_lt_tsum
- \+ *lemma* tsum_mono
- \+ *lemma* tsum_strict_mono



## [2021-02-09 11:14:56](https://github.com/leanprover-community/mathlib/commit/2d50cce)
refactor(geometry/euclidean): shorten proof ([#6121](https://github.com/leanprover-community/mathlib/pull/6121))
... of `eq_reflection_of_eq_subspace`
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean




## [2021-02-09 11:14:54](https://github.com/leanprover-community/mathlib/commit/aaab113)
refactor(linear_algebra/prod): split out prod and coprod defs and lemmas  ([#6059](https://github.com/leanprover-community/mathlib/pull/6059))
Lemmas are moved without modification.
I expect this will take a few builds of adding missing imports.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/basic.lean
- \- *lemma* linear_equiv.coe_prod
- \- *lemma* linear_equiv.prod_apply
- \- *lemma* linear_equiv.prod_symm
- \- *lemma* linear_equiv.skew_prod_apply
- \- *lemma* linear_equiv.skew_prod_symm_apply
- \- *theorem* linear_map.comap_prod_prod
- \- *theorem* linear_map.comp_coprod
- \- *def* linear_map.coprod
- \- *theorem* linear_map.coprod_apply
- \- *def* linear_map.coprod_equiv
- \- *theorem* linear_map.coprod_inl
- \- *theorem* linear_map.coprod_inl_inr
- \- *theorem* linear_map.coprod_inr
- \- *lemma* linear_map.disjoint_inl_inr
- \- *def* linear_map.fst
- \- *theorem* linear_map.fst_apply
- \- *theorem* linear_map.fst_eq_coprod
- \- *theorem* linear_map.fst_prod
- \- *def* linear_map.inl
- \- *theorem* linear_map.inl_apply
- \- *theorem* linear_map.inl_eq_prod
- \- *theorem* linear_map.inl_injective
- \- *def* linear_map.inr
- \- *theorem* linear_map.inr_apply
- \- *theorem* linear_map.inr_eq_prod
- \- *theorem* linear_map.inr_injective
- \- *lemma* linear_map.is_compl_range_inl_inr
- \- *lemma* linear_map.ker_prod
- \- *theorem* linear_map.map_coprod_prod
- \- *theorem* linear_map.pair_fst_snd
- \- *def* linear_map.prod
- \- *theorem* linear_map.prod_eq_inf_comap
- \- *theorem* linear_map.prod_eq_sup_map
- \- *def* linear_map.prod_equiv
- \- *def* linear_map.prod_map
- \- *theorem* linear_map.prod_map_apply
- \- *lemma* linear_map.range_coprod
- \- *lemma* linear_map.range_prod_eq
- \- *lemma* linear_map.range_prod_le
- \- *def* linear_map.snd
- \- *theorem* linear_map.snd_apply
- \- *theorem* linear_map.snd_eq_coprod
- \- *theorem* linear_map.snd_prod
- \- *lemma* linear_map.span_inl_union_inr
- \- *lemma* linear_map.sup_range_inl_inr
- \- *theorem* submodule.comap_fst
- \- *theorem* submodule.comap_snd
- \- *theorem* submodule.ker_inl
- \- *theorem* submodule.ker_inr
- \- *theorem* submodule.map_inl
- \- *theorem* submodule.map_inr
- \- *theorem* submodule.prod_comap_inl
- \- *theorem* submodule.prod_comap_inr
- \- *theorem* submodule.prod_map_fst
- \- *theorem* submodule.prod_map_snd
- \- *theorem* submodule.range_fst
- \- *theorem* submodule.range_snd
- \- *lemma* submodule.sup_eq_range

Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/linear_pmap.lean


Added src/linear_algebra/prod.lean
- \+ *lemma* linear_equiv.coe_prod
- \+ *lemma* linear_equiv.prod_apply
- \+ *lemma* linear_equiv.prod_symm
- \+ *lemma* linear_equiv.skew_prod_apply
- \+ *lemma* linear_equiv.skew_prod_symm_apply
- \+ *theorem* linear_map.comap_prod_prod
- \+ *theorem* linear_map.comp_coprod
- \+ *def* linear_map.coprod
- \+ *theorem* linear_map.coprod_apply
- \+ *def* linear_map.coprod_equiv
- \+ *theorem* linear_map.coprod_inl
- \+ *theorem* linear_map.coprod_inl_inr
- \+ *theorem* linear_map.coprod_inr
- \+ *lemma* linear_map.disjoint_inl_inr
- \+ *def* linear_map.fst
- \+ *theorem* linear_map.fst_apply
- \+ *theorem* linear_map.fst_eq_coprod
- \+ *theorem* linear_map.fst_prod
- \+ *def* linear_map.inl
- \+ *theorem* linear_map.inl_apply
- \+ *theorem* linear_map.inl_eq_prod
- \+ *theorem* linear_map.inl_injective
- \+ *def* linear_map.inr
- \+ *theorem* linear_map.inr_apply
- \+ *theorem* linear_map.inr_eq_prod
- \+ *theorem* linear_map.inr_injective
- \+ *lemma* linear_map.is_compl_range_inl_inr
- \+ *lemma* linear_map.ker_prod
- \+ *theorem* linear_map.map_coprod_prod
- \+ *theorem* linear_map.pair_fst_snd
- \+ *def* linear_map.prod
- \+ *theorem* linear_map.prod_eq_inf_comap
- \+ *theorem* linear_map.prod_eq_sup_map
- \+ *def* linear_map.prod_equiv
- \+ *def* linear_map.prod_map
- \+ *theorem* linear_map.prod_map_apply
- \+ *lemma* linear_map.range_coprod
- \+ *lemma* linear_map.range_prod_eq
- \+ *lemma* linear_map.range_prod_le
- \+ *def* linear_map.snd
- \+ *theorem* linear_map.snd_apply
- \+ *theorem* linear_map.snd_eq_coprod
- \+ *theorem* linear_map.snd_prod
- \+ *lemma* linear_map.span_inl_union_inr
- \+ *lemma* linear_map.sup_range_inl_inr
- \+ *theorem* submodule.comap_fst
- \+ *theorem* submodule.comap_snd
- \+ *theorem* submodule.ker_inl
- \+ *theorem* submodule.ker_inr
- \+ *theorem* submodule.map_inl
- \+ *theorem* submodule.map_inr
- \+ *theorem* submodule.prod_comap_inl
- \+ *theorem* submodule.prod_comap_inr
- \+ *theorem* submodule.prod_map_fst
- \+ *theorem* submodule.prod_map_snd
- \+ *theorem* submodule.range_fst
- \+ *theorem* submodule.range_snd
- \+ *lemma* submodule.sup_eq_range

Modified src/linear_algebra/projection.lean




## [2021-02-09 11:14:52](https://github.com/leanprover-community/mathlib/commit/17448c6)
feat(group_theory/perm/sign): induced permutation on a subtype that is a fintype ([#5706](https://github.com/leanprover-community/mathlib/pull/5706))
If a permutation on a type maps a subtype into itself and the subtype is a fintype, then we get a permutation on the subtype. Similar to the subtype_perm definition in the same file.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.subtype_perm_apply

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.perm_inv_maps_to_iff_maps_to
- \+ *lemma* equiv.perm.perm_inv_maps_to_of_maps_to
- \+ *lemma* equiv.perm.perm_inv_on_of_perm_on_finset
- \+ *lemma* equiv.perm.perm_inv_on_of_perm_on_fintype
- \+ *lemma* equiv.perm.subtype_perm_of_fintype_apply
- \+ *lemma* equiv.perm.subtype_perm_of_fintype_one



## [2021-02-09 07:26:19](https://github.com/leanprover-community/mathlib/commit/342bccf)
refactor(group_theory/solvable): `simp` -> assumption ([#6120](https://github.com/leanprover-community/mathlib/pull/6120))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/group_theory/solvable.lean




## [2021-02-09 07:26:17](https://github.com/leanprover-community/mathlib/commit/ec8f2ac)
refactor(data/ordmap/ordset): simpler proof of `not_le_delta` ([#6119](https://github.com/leanprover-community/mathlib/pull/6119))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/data/ordmap/ordset.lean




## [2021-02-09 07:26:15](https://github.com/leanprover-community/mathlib/commit/7e5ff2f)
refactor(computability/partrec): simpler proof of `subtype_mk` ([#6118](https://github.com/leanprover-community/mathlib/pull/6118))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/computability/partrec.lean




## [2021-02-09 07:26:13](https://github.com/leanprover-community/mathlib/commit/183f4fc)
refactor(category_theory/adjunction/mates): faster proof ([#6116](https://github.com/leanprover-community/mathlib/pull/6116))
Co-authors: `lean-gptf`, Stanislas Polu
elaboration 750ms -> 350ms
5X smaller proof term
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/category_theory/adjunction/mates.lean




## [2021-02-09 07:26:11](https://github.com/leanprover-community/mathlib/commit/1611b30)
refactor(combinatorics/simple_graph): simplify proofs ([#6115](https://github.com/leanprover-community/mathlib/pull/6115))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-02-09 07:26:10](https://github.com/leanprover-community/mathlib/commit/d06b11a)
refactor(algebra/lie/basic): golf `lie_algebra.morphism.map_bot_iff` ([#6114](https://github.com/leanprover-community/mathlib/pull/6114))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.
#### Estimated changes
Modified src/algebra/lie/basic.lean




## [2021-02-09 07:26:06](https://github.com/leanprover-community/mathlib/commit/6b65c37)
refactor(linear_algebra/tensor_product): Use a more powerful lemma for ext ([#6105](https://github.com/leanprover-community/mathlib/pull/6105))
This means that the `ext` tactic can recurse into both the left and the right of the tensor product.
The downside is that `compr₂_apply, mk_apply` needs to be added to some `simp only`s.
Notably this makes `ext` able to prove `tensor_product.ext_fourfold` (which is still needed to cut down elaboration time for the `pentagon` proof), and enables `ext` to be used on things like tensor products of a tensor_algebra and a free_algebra.
#### Estimated changes
Modified src/category_theory/monoidal/internal/Module.lean


Modified src/linear_algebra/tensor_product.lean




## [2021-02-09 07:26:04](https://github.com/leanprover-community/mathlib/commit/7b1945e)
feat(logic/basic): dite_eq_ite ([#6095](https://github.com/leanprover-community/mathlib/pull/6095))
Simplify `dite` to `ite` when possible.
#### Estimated changes
Modified src/data/real/golden_ratio.lean


Modified src/group_theory/perm/sign.lean


Modified src/logic/basic.lean
- \+ *lemma* dite_eq_ite



## [2021-02-09 05:58:46](https://github.com/leanprover-community/mathlib/commit/8fd8636)
feat(field_theory/minpoly): add `minpoly.nat_degree_pos` ([#6100](https://github.com/leanprover-community/mathlib/pull/6100))
I needed this lemma and noticed that `minpoly.lean` actually uses this result more than `minpoly.degree_pos` (including in the proof of `degree_pos` itself). So I took the opportunity to golf a couple of proofs.
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.degree_pos
- \+ *lemma* minpoly.nat_degree_pos



## [2021-02-09 03:30:54](https://github.com/leanprover-community/mathlib/commit/69bf484)
chore(scripts): update nolints.txt ([#6112](https://github.com/leanprover-community/mathlib/pull/6112))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-09 00:54:24](https://github.com/leanprover-community/mathlib/commit/117e729)
chore(linear_algebra/basic, analysis/normed_space/operator_norm): bundle another argument into the homs ([#5899](https://github.com/leanprover-community/mathlib/pull/5899))
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.apply
- \- *def* continuous_linear_map.applyₗ
- \- *lemma* continuous_linear_map.continuous_applyₗ

Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_map.applyₗ'
- \+/\- *def* linear_map.applyₗ



## [2021-02-08 21:41:41](https://github.com/leanprover-community/mathlib/commit/7f11d72)
feat(analysis/normed_space): `continuous_linear_map.prod` as a `linear_isometry_equiv` ([#6099](https://github.com/leanprover-community/mathlib/pull/6099))
* add lemma `continuous_linear_map.op_norm_prod`;
* add `continuous_linear_map.prodₗ` and `continuous_linear_map.prodₗᵢ`;
* add `prod.topological_semimodule`;
* drop unused `is_bounded_linear_map_prod_iso`.
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* is_bounded_linear_map_prod_iso

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_norm_prod
- \+ *def* continuous_linear_map.prodₗᵢ

Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_map.prodₗ



## [2021-02-08 21:41:39](https://github.com/leanprover-community/mathlib/commit/03074b1)
doc(algebra/{field_power, punit_instances}): module docs ([#6097](https://github.com/leanprover-community/mathlib/pull/6097))
Additionally `ordered_field` is aligned with the style guidelines.
#### Estimated changes
Modified src/algebra/field_power.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/punit_instances.lean




## [2021-02-08 19:30:23](https://github.com/leanprover-community/mathlib/commit/d62d793)
feat(differential_object/iso_app): extract the isomorphism of underlying objects ([#6083](https://github.com/leanprover-community/mathlib/pull/6083))
From `lean-liquid`.
#### Estimated changes
Modified src/category_theory/differential_object.lean
- \+ *def* category_theory.differential_object.iso_app
- \+ *lemma* category_theory.differential_object.iso_app_refl
- \+ *lemma* category_theory.differential_object.iso_app_symm
- \+ *lemma* category_theory.differential_object.iso_app_trans



## [2021-02-08 19:30:20](https://github.com/leanprover-community/mathlib/commit/0c6fa28)
feat(linear_algebra/basis): if `(p : submodule K V) < ⊤`, then there exists `f : V →ₗ[K] K`, `p ≤ ker f` ([#6074](https://github.com/leanprover-community/mathlib/pull/6074))
#### Estimated changes
Modified src/analysis/convex/cone.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_map.exists_extend
- \+ *lemma* submodule.exists_le_ker_of_lt_top

Modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* linear_pmap.domain_sup_span_singleton
- \+ *lemma* linear_pmap.sup_span_singleton_apply_mk



## [2021-02-08 19:30:18](https://github.com/leanprover-community/mathlib/commit/4e9fbb9)
feat(measure_theory/probability_mass_function): Add definitions for filtering pmfs on a predicate ([#6033](https://github.com/leanprover-community/mathlib/pull/6033))
#### Estimated changes
Modified src/measure_theory/probability_mass_function.lean
- \+ *def* pmf.filter
- \+ *lemma* pmf.filter_apply
- \+ *lemma* pmf.filter_apply_eq_zero_iff
- \+ *lemma* pmf.filter_apply_eq_zero_of_not_mem
- \+ *lemma* pmf.filter_apply_ne_zero_iff
- \+ *lemma* pmf.mem_support_iff
- \+ *def* pmf.normalize
- \+ *lemma* pmf.normalize_apply

Modified src/topology/instances/ennreal.lean
- \+ *lemma* nnreal.indicator_summable
- \+ *lemma* nnreal.tsum_indicator_ne_zero



## [2021-02-08 19:30:16](https://github.com/leanprover-community/mathlib/commit/f6504f1)
feat(computability/DFA): the pumping lemma ([#5925](https://github.com/leanprover-community/mathlib/pull/5925))
#### Estimated changes
Modified src/computability/DFA.lean
- \+ *lemma* DFA.eval_from_of_append
- \+ *lemma* DFA.eval_from_of_pow
- \+ *lemma* DFA.eval_from_split
- \+ *lemma* DFA.mem_accepts
- \+ *lemma* DFA.pumping_lemma

Modified src/computability/NFA.lean
- \+ *lemma* NFA.pumping_lemma



## [2021-02-08 16:17:44](https://github.com/leanprover-community/mathlib/commit/1d49f87)
chore(data/finset): golf some proofs ([#6101](https://github.com/leanprover-community/mathlib/pull/6101))
* prove that `finset.min'` and `finset.max'` are `is_least` and
  `is_greatest` elements of the corresponding sets;
* use this fact to golf some proofs;
  generalize `min'_lt_max'` to `is_glb_lt_is_lub_of_ne`;
* add `finset.card_le_one` and `finset.one_lt_card`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_le_one
- \+ *theorem* finset.one_lt_card

Modified src/data/finset/lattice.lean
- \+ *theorem* finset.is_greatest_max'
- \+ *theorem* finset.is_least_min'
- \+ *lemma* finset.le_min'_iff
- \+ *lemma* finset.max'_le_iff

Modified src/order/bounds.lean
- \+ *lemma* is_glb_lt_is_lub_of_ne
- \+ *lemma* le_of_is_lub_le_is_glb
- \+ *lemma* set.subsingleton_of_is_lub_le_is_glb



## [2021-02-08 16:17:43](https://github.com/leanprover-community/mathlib/commit/1a0f84c)
feat(linear_algebra/basic): bundle prod and coprod into linear_equivs ([#5992](https://github.com/leanprover-community/mathlib/pull/5992))
In order to do this, this has to reorder some definitions to make the semimodule structure on linear maps available earlier.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_map.comp_coprod
- \+/\- *theorem* linear_map.coprod_apply
- \+ *def* linear_map.coprod_equiv
- \+/\- *theorem* linear_map.fst_eq_coprod
- \- *lemma* linear_map.is_linear_map_prod_iso
- \+/\- *def* linear_map.prod
- \- *theorem* linear_map.prod_apply
- \+ *def* linear_map.prod_equiv
- \+/\- *theorem* linear_map.snd_eq_coprod



## [2021-02-08 14:15:50](https://github.com/leanprover-community/mathlib/commit/8a23aa3)
feat(topology/instances/{nnreal,ennreal}): add tendsto_cofinite_zero_of_summable ([#6093](https://github.com/leanprover-community/mathlib/pull/6093))
For `f : a -> nnreal`, `summable f` implies `tendsto f cofinite (nhds 0)`.
For `f : a -> ennreal`, `tsum f < \top` implies `tendsto f cofinite (nhds 0)`.
Add versions of these lemmas with `at_top` instead of `cofinite` when `a = N`.
Also add `ennreal.tendsto_at_top_zero`, a simpler statement for a particular case of `ennreal.tendsto_at_top`.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.tendsto_at_top_zero

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_at_top_zero_of_tsum_lt_top
- \+ *lemma* ennreal.tendsto_cofinite_zero_of_tsum_lt_top

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.tendsto_at_top_zero_of_summable
- \+ *lemma* nnreal.tendsto_cofinite_zero_of_summable



## [2021-02-08 14:15:49](https://github.com/leanprover-community/mathlib/commit/8e3e79a)
feat(category_theory/pi): extract components of isomorphisms of indexed objects ([#6086](https://github.com/leanprover-community/mathlib/pull/6086))
From `lean-liquid`.
#### Estimated changes
Modified src/category_theory/pi/basic.lean
- \+ *def* category_theory.pi.iso_app
- \+ *lemma* category_theory.pi.iso_app_refl
- \+ *lemma* category_theory.pi.iso_app_symm
- \+ *lemma* category_theory.pi.iso_app_trans



## [2021-02-08 14:15:47](https://github.com/leanprover-community/mathlib/commit/f075a69)
feat(category_theory/differential_object): lifting a functor ([#6084](https://github.com/leanprover-community/mathlib/pull/6084))
From `lean-liquid`.
#### Estimated changes
Modified src/category_theory/differential_object.lean
- \+ *def* category_theory.functor.map_differential_object



## [2021-02-08 14:15:44](https://github.com/leanprover-community/mathlib/commit/6561639)
feat(topology/local_extr): not locally surjective at a local extr ([#6076](https://github.com/leanprover-community/mathlib/pull/6076))
#### Estimated changes
Modified src/topology/local_extr.lean
- \+ *lemma* is_local_extr_on.not_nhds_le_map
- \+ *lemma* is_local_max_on.not_nhds_le_map
- \+ *lemma* is_local_min_on.not_nhds_le_map



## [2021-02-08 14:15:42](https://github.com/leanprover-community/mathlib/commit/054b467)
feat(analysis/calculus): derivatives of `f : E → Π i, F i` ([#6075](https://github.com/leanprover-community/mathlib/pull/6075))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_O_iff_eventually
- \+ *lemma* asymptotics.is_O_iff_eventually_is_O_with
- \+ *theorem* asymptotics.is_O_pi
- \+ *theorem* asymptotics.is_O_with_pi
- \+ *theorem* asymptotics.is_o_pi

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_pi
- \+ *lemma* deriv_within_pi
- \+ *lemma* has_deriv_at_filter_pi
- \+ *lemma* has_deriv_at_pi
- \+ *lemma* has_deriv_within_at_pi
- \+ *lemma* has_strict_deriv_at_pi

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_at_pi
- \+ *lemma* differentiable_on_pi
- \+ *lemma* differentiable_pi
- \+ *lemma* differentiable_within_at_pi
- \+ *lemma* fderiv_pi
- \+ *lemma* fderiv_within_pi
- \+ *lemma* has_fderiv_at_filter_pi'
- \+ *lemma* has_fderiv_at_filter_pi
- \+ *lemma* has_fderiv_at_pi'
- \+ *lemma* has_fderiv_at_pi
- \+ *lemma* has_fderiv_within_at_pi'
- \+ *lemma* has_fderiv_within_at_pi
- \+ *lemma* has_strict_fderiv_at_pi'
- \+ *lemma* has_strict_fderiv_at_pi

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.coe_pi
- \+/\- *lemma* continuous_linear_map.pi_apply
- \+/\- *lemma* continuous_linear_map.pi_zero



## [2021-02-08 14:15:40](https://github.com/leanprover-community/mathlib/commit/dc48a84)
feat(linear_algebra/pi_tensor_product): add reindex and pempty_equiv ([#6069](https://github.com/leanprover-community/mathlib/pull/6069))
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean
- \+ *lemma* pi_tensor_product.lift_comp_reindex
- \+ *lemma* pi_tensor_product.lift_reindex
- \+ *theorem* pi_tensor_product.lift_symm
- \+ *def* pi_tensor_product.pempty_equiv
- \+ *def* pi_tensor_product.reindex
- \+ *lemma* pi_tensor_product.reindex_comp_tprod
- \+ *lemma* pi_tensor_product.reindex_refl
- \+ *lemma* pi_tensor_product.reindex_symm
- \+ *lemma* pi_tensor_product.reindex_tprod
- \+ *lemma* pi_tensor_product.reindex_trans



## [2021-02-08 10:21:58](https://github.com/leanprover-community/mathlib/commit/d7a4f72)
feat(norm_cast): dite_cast to match ite_cast ([#6092](https://github.com/leanprover-community/mathlib/pull/6092))
There's already an `ite_cast` lemma, for pushing a cast inside an `ite`. This adds the analogous `dite_cast`.
#### Estimated changes
Modified src/tactic/norm_cast.lean
- \+ *lemma* dite_cast



## [2021-02-08 10:21:56](https://github.com/leanprover-community/mathlib/commit/b338240)
feat(topology/constructions): a finite product of discrete spaces is discrete ([#6088](https://github.com/leanprover-community/mathlib/pull/6088))
From `lean-liquid`.
#### Estimated changes
Modified src/topology/constructions.lean




## [2021-02-08 10:21:55](https://github.com/leanprover-community/mathlib/commit/e4369fe)
chore(algebra/module/prod): add missing instances ([#6055](https://github.com/leanprover-community/mathlib/pull/6055))
This adds the following instances for `prod`:
* `is_scalar_tower`
* `smul_comm_class`
* `mul_action`
* `distrib_mul_action`
It also renames the type variables to match the usual convention for modules
#### Estimated changes
Modified src/algebra/module/prod.lean
- \+/\- *theorem* prod.smul_fst
- \+/\- *theorem* prod.smul_mk
- \+/\- *theorem* prod.smul_snd



## [2021-02-08 08:08:37](https://github.com/leanprover-community/mathlib/commit/90702a0)
feat(topology/continuous_map): missing coe_mk lemma ([#6087](https://github.com/leanprover-community/mathlib/pull/6087))
#### Estimated changes
Modified src/topology/continuous_map.lean
- \+ *lemma* continuous_map.coe_mk



## [2021-02-08 05:08:19](https://github.com/leanprover-community/mathlib/commit/a6fc6bd)
feat(finset/lattice): max'_insert ([#6089](https://github.com/leanprover-community/mathlib/pull/6089))
From `lean-liquid`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.max'_insert
- \+ *lemma* finset.max'_subset
- \+ *lemma* finset.min'_insert
- \+ *lemma* finset.min'_subset



## [2021-02-08 02:16:50](https://github.com/leanprover-community/mathlib/commit/6b83e72)
chore(scripts): update nolints.txt ([#6090](https://github.com/leanprover-community/mathlib/pull/6090))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-08 02:16:48](https://github.com/leanprover-community/mathlib/commit/5bf92e1)
chore(analysis/calculus/local_extr): review ([#6085](https://github.com/leanprover-community/mathlib/pull/6085))
* golf 2 proofs;
* don't use explicit section `variables`;
* add 2 docstrings.
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean
- \+/\- *lemma* exists_Ioo_extr_on_Icc
- \+/\- *lemma* exists_deriv_eq_zero'
- \+/\- *lemma* exists_deriv_eq_zero
- \+/\- *lemma* exists_has_deriv_at_eq_zero'
- \+/\- *lemma* exists_has_deriv_at_eq_zero
- \+/\- *lemma* exists_local_extr_Ioo
- \+ *lemma* mem_pos_tangent_cone_at_of_segment_subset'



## [2021-02-07 23:41:53](https://github.com/leanprover-community/mathlib/commit/45f9544)
feat(topology/separation): an injective map on a compact space is an embedding ([#6057](https://github.com/leanprover-community/mathlib/pull/6057))
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* continuous.closed_embedding
- \+ *lemma* continuous.is_closed_map



## [2021-02-07 23:41:49](https://github.com/leanprover-community/mathlib/commit/9411b00)
feat(algebra/lie/basic): define the center of a Lie algebra and prove some related results ([#6013](https://github.com/leanprover-community/mathlib/pull/6013))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_algebra.abelian_of_le_center
- \+ *lemma* lie_algebra.abelian_radical_iff_solvable_is_abelian
- \+ *lemma* lie_algebra.abelian_radical_of_semisimple
- \+/\- *def* lie_algebra.ad
- \+ *lemma* lie_algebra.center_eq_adjoint_kernel
- \+ *lemma* lie_algebra.center_eq_bot_of_semisimple
- \+ *lemma* lie_algebra.center_le_radical
- \+ *lemma* lie_algebra.is_lie_abelian_iff_center_eq_top
- \- *lemma* lie_algebra.of_abelian_is_solvable
- \+ *lemma* lie_algebra.subsingleton_of_semisimple_lie_abelian
- \- *lemma* lie_ideal.of_bot_eq_bot
- \+ *lemma* lie_ideal.subsingleton_of_bot
- \- *lemma* lie_ideal.unique_of_bot
- \+ *lemma* lie_module.is_trivial_iff_maximal_trivial_eq_top
- \+ *def* lie_module.maximal_trivial_submodule
- \+ *lemma* lie_module.mem_maximal_trivial_submodule
- \- *def* lie_module.to_endo_morphism
- \+ *def* lie_module.to_endomorphism
- \+ *lemma* lie_module.trivial_iff_le_maximal_trivial
- \- *lemma* lie_submodule.of_bot_eq_bot
- \+ *lemma* lie_submodule.subsingleton_of_bot
- \- *lemma* lie_submodule.unique_of_bot



## [2021-02-07 23:41:48](https://github.com/leanprover-community/mathlib/commit/d989ff4)
feat(measure_theory/lebesgue_measure): integral as volume between graphs ([#5932](https://github.com/leanprover-community/mathlib/pull/5932))
I show that the integral can compute the volume between two real-valued functions. I start with the definition `region_between`, I prove that the region between two functions is a `measurable_set`, and then I prove two integral theorems. 
Help from @hrmacbeth and @benjamindavidson.
#### Estimated changes
Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* measurable_set_region_between
- \+ *def* region_between
- \+ *lemma* region_between_subset
- \+ *theorem* volume_region_between_eq_integral'
- \+ *theorem* volume_region_between_eq_integral
- \+ *theorem* volume_region_between_eq_lintegral'
- \+ *theorem* volume_region_between_eq_lintegral

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_apply'
- \+ *lemma* measure_theory.measure.restrict_eq_self_of_measurable_subset
- \+ *lemma* measure_theory.measure.restrict_eq_self_of_subset_of_measurable

Modified src/measure_theory/prod.lean
- \+ *lemma* measure_theory.measure.restrict_prod_eq_prod_univ



## [2021-02-07 21:13:03](https://github.com/leanprover-community/mathlib/commit/f3b0295)
chore(measure_theory): use `∞` notation for `(⊤ : ℝ≥0∞)` ([#6080](https://github.com/leanprover-community/mathlib/pull/6080))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_to_real

Modified src/measure_theory/borel_space.lean
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal

Modified src/measure_theory/content.lean
- \+/\- *lemma* measure_theory.outer_measure.of_content_exists_compact
- \+/\- *lemma* measure_theory.outer_measure.of_content_exists_open

Modified src/measure_theory/decomposition.lean
- \+/\- *lemma* measure_theory.hahn_decomposition

Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.ae_lt_top
- \+/\- *lemma* measure_theory.exists_pos_set_lintegral_lt_of_measure_lt
- \+/\- *lemma* measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos
- \+/\- *lemma* measure_theory.lintegral_const_mul'
- \+/\- *lemma* measure_theory.lintegral_mul_const'
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.of_lintegral_lt_top
- \+/\- *lemma* measure_theory.tendsto_set_lintegral_zero

Modified src/measure_theory/l1_space.lean
- \+/\- *def* measure_theory.ae_eq_fun.integrable
- \+/\- *lemma* measure_theory.integrable.smul_measure
- \+/\- *lemma* measure_theory.integrable_const_iff
- \+/\- *lemma* measure_theory.l1.lintegral_edist_to_fun_lt_top

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.Lp.coe_fn_mk
- \+/\- *lemma* measure_theory.Lp.mem_Lp_iff_snorm_lt_top
- \+/\- *lemma* measure_theory.Lp.snorm_lt_top
- \+/\- *lemma* measure_theory.Lp.snorm_ne_top
- \+/\- *lemma* measure_theory.mem_ℒp.snorm_lt_top
- \+/\- *lemma* measure_theory.mem_ℒp.snorm_ne_top
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_neg
- \+/\- *lemma* measure_theory.snorm_const'
- \+/\- *lemma* measure_theory.snorm_eq_snorm'
- \+/\- *lemma* measure_theory.snorm_exponent_top

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* is_compact.finite_measure
- \+/\- *lemma* measure_theory.measure.compl_mem_cofinite
- \+/\- *lemma* measure_theory.measure.count_apply_eq_top
- \+/\- *lemma* measure_theory.measure.count_apply_infinite
- \+/\- *lemma* measure_theory.measure.count_apply_lt_top
- \+/\- *lemma* measure_theory.measure.eventually_cofinite
- \+/\- *def* measure_theory.measure.finite_at_filter
- \+/\- *lemma* measure_theory.measure.finite_at_principal
- \+/\- *lemma* measure_theory.measure.mem_cofinite
- \+/\- *lemma* measure_theory.measure_compl
- \+/\- *lemma* measure_theory.measure_lt_top
- \+/\- *lemma* measure_theory.measure_mono_top
- \+/\- *lemma* measure_theory.measure_ne_top

Modified src/measure_theory/outer_measure.lean
- \+/\- *theorem* measure_theory.outer_measure.top_apply

Modified src/measure_theory/prod.lean


Modified src/measure_theory/prod_group.lean


Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* measure_theory.integrable_on_const
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const'
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae''
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae'
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae

Modified src/measure_theory/simple_func_dense.lean




## [2021-02-07 21:13:00](https://github.com/leanprover-community/mathlib/commit/5d4d815)
feat(analysis): prove that a polynomial function is equivalent to its leading term along at_top, and consequences ([#5354](https://github.com/leanprover-community/mathlib/pull/5354))
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coeff `a`, the corresponding polynomial
function is equivalent to `a * x^n` as `x` goes to +∞.
We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coeffs of the considered polynomials.
#### Estimated changes
Renamed src/analysis/asymptotic_equivalent.lean to src/analysis/asymptotics/asymptotic_equivalent.lean
- \+ *lemma* asymptotics.is_equivalent.add_is_o
- \+ *lemma* asymptotics.is_equivalent.congr_left
- \+ *lemma* asymptotics.is_equivalent.congr_right
- \+ *lemma* asymptotics.is_equivalent.neg
- \+ *lemma* asymptotics.is_equivalent.tendsto_at_bot
- \+ *lemma* asymptotics.is_equivalent.tendsto_at_bot_iff
- \+ *lemma* asymptotics.is_o.is_equivalent
- \+ *lemma* filter.eventually_eq.is_equivalent

Renamed src/analysis/asymptotics.lean to src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_o.tendsto_zero_of_tendsto

Added src/analysis/asymptotics/specific_asymptotics.lean
- \+ *lemma* asymptotics.is_O.trans_tendsto_norm_at_top
- \+ *lemma* asymptotics.is_o_pow_pow_at_top_of_lt
- \+ *lemma* pow_div_pow_eventually_eq_at_bot
- \+ *lemma* pow_div_pow_eventually_eq_at_top
- \+ *lemma* tendsto_fpow_at_top_at_top
- \+ *lemma* tendsto_pow_div_pow_at_top_at_top
- \+ *lemma* tendsto_pow_div_pow_at_top_zero

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/ordered.lean
- \- *lemma* is_o_pow_pow_at_top_of_lt
- \- *lemma* tendsto_pow_div_pow_at_top_of_lt

Modified src/analysis/normed_space/units.lean


Added src/analysis/special_functions/polynomials.lean
- \+ *lemma* polynomial.abs_tendsto_at_top
- \+ *lemma* polynomial.div_tendsto_at_bot_of_degree_gt'
- \+ *lemma* polynomial.div_tendsto_at_bot_of_degree_gt
- \+ *lemma* polynomial.div_tendsto_at_top_of_degree_gt'
- \+ *lemma* polynomial.div_tendsto_at_top_of_degree_gt
- \+ *lemma* polynomial.div_tendsto_leading_coeff_div_of_degree_eq
- \+ *lemma* polynomial.div_tendsto_zero_of_degree_lt
- \+ *lemma* polynomial.eval_div_tendsto_at_top_of_degree_gt
- \+ *lemma* polynomial.is_equivalent_at_top_div
- \+ *lemma* polynomial.is_equivalent_at_top_lead
- \+ *lemma* polynomial.tendsto_at_bot_of_leading_coeff_nonpos
- \+ *lemma* polynomial.tendsto_at_top_of_leading_coeff_nonneg

Modified src/analysis/specific_limits.lean


Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_lt_degree
- \+ *lemma* polynomial.le_nat_degree_of_coe_le_degree
- \+ *lemma* polynomial.nat_degree_lt_nat_degree_iff
- \+ *lemma* polynomial.ne_zero_of_coe_le_degree
- \+ *lemma* polynomial.ne_zero_of_nat_degree_gt

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_eq_finset_sum'
- \+ *lemma* polynomial.eval_eq_finset_sum

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.tendsto_const_mul_pow_at_top
- \+ *lemma* filter.tendsto_neg_const_mul_pow_at_top

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.div'
- \+ *lemma* filter.eventually_eq.sub_eq
- \+ *lemma* filter.eventually_eq_iff_sub

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_fpow_at_top_zero



## [2021-02-07 19:35:43](https://github.com/leanprover-community/mathlib/commit/99fe12a)
refactor(measure_theory/ae_eq_fun): move emetric to `ae_eq_fun_metric` ([#6081](https://github.com/leanprover-community/mathlib/pull/6081))
Cherry-picked from [#6042](https://github.com/leanprover-community/mathlib/pull/6042)
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean
- \- *lemma* measure_theory.ae_eq_fun.coe_fn_edist
- \- *lemma* measure_theory.ae_eq_fun.edist_add_right
- \- *lemma* measure_theory.ae_eq_fun.edist_eq_coe'
- \- *lemma* measure_theory.ae_eq_fun.edist_eq_coe
- \- *lemma* measure_theory.ae_eq_fun.edist_mk_mk'
- \- *lemma* measure_theory.ae_eq_fun.edist_mk_mk
- \- *lemma* measure_theory.ae_eq_fun.edist_smul
- \- *lemma* measure_theory.ae_eq_fun.edist_zero_eq_coe

Added src/measure_theory/ae_eq_fun_metric.lean
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_edist
- \+ *lemma* measure_theory.ae_eq_fun.edist_add_right
- \+ *lemma* measure_theory.ae_eq_fun.edist_eq_coe'
- \+ *lemma* measure_theory.ae_eq_fun.edist_eq_coe
- \+ *lemma* measure_theory.ae_eq_fun.edist_mk_mk'
- \+ *lemma* measure_theory.ae_eq_fun.edist_mk_mk
- \+ *lemma* measure_theory.ae_eq_fun.edist_smul
- \+ *lemma* measure_theory.ae_eq_fun.edist_zero_eq_coe

Modified src/measure_theory/l1_space.lean




## [2021-02-07 19:35:41](https://github.com/leanprover-community/mathlib/commit/5a25827)
chore(measure_theory/measure_space): move definition of `measure.ae` up ([#6051](https://github.com/leanprover-community/mathlib/pull/6051))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+/\- *def* measure_theory.measure.ae



## [2021-02-07 19:35:39](https://github.com/leanprover-community/mathlib/commit/132b0fe)
fix(scripts): make lint-style.* work on macos and windows ([#6047](https://github.com/leanprover-community/mathlib/pull/6047))
Make lint-style.sh use a POSIX-portable way of checking for executable bits, and make it always open files as UTF-8.
Also makes CI run the sanity checks across all 3 OSes to ensure this stays working.
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/lint-style.py


Modified scripts/lint-style.sh


Modified scripts/lint_style_sanity_test.py




## [2021-02-07 15:56:24](https://github.com/leanprover-community/mathlib/commit/288cc2e)
feat(logic/function/basic): add lemma stating that dite of two injective functions is injective if images are disjoint ([#5866](https://github.com/leanprover-community/mathlib/pull/5866))
Add lemma stating that dite of two injective functions is injective if their images are disjoint. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's Marriage Theorem.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.injective.dite



## [2021-02-07 13:33:58](https://github.com/leanprover-community/mathlib/commit/c25dad9)
refactor(analysis/calculus/mean_value): use `is_R_or_C` in more lemmas ([#6022](https://github.com/leanprover-community/mathlib/pull/6022))
* use `is_R_or_C` in `convex.norm_image_sub_le*` lemmas;
* replace `strict_fderiv_of_cont_diff` with
  `has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at` and
  `has_strict_deriv_at_of_has_deriv_at_of_continuous_at`, slightly change assumptions;
* add `has_ftaylor_series_up_to_on.has_fderiv_at`,
  `has_ftaylor_series_up_to_on.eventually_has_fderiv_at`,
  `has_ftaylor_series_up_to_on.differentiable_at`;
* add `times_cont_diff_at.has_strict_deriv_at` and
  `times_cont_diff_at.has_strict_deriv_at'`;
* prove that `complex.exp` is strictly differentiable and is an open map;
* add `simp` lemma `interior_mem_nhds`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* convex.is_const_of_fderiv_within_eq_zero
- \+/\- *theorem* convex.lipschitz_on_with_of_norm_fderiv_le
- \+/\- *theorem* convex.lipschitz_on_with_of_norm_fderiv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le'
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le'
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le
- \+ *lemma* has_strict_deriv_at_of_has_deriv_at_of_continuous_at
- \+ *lemma* has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at
- \- *theorem* is_R_or_C.norm_image_sub_le_of_norm_has_fderiv_within_le'
- \+/\- *theorem* is_const_of_fderiv_eq_zero
- \- *lemma* strict_fderiv_of_cont_diff

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.differentiable_at
- \+ *lemma* has_ftaylor_series_up_to_on.eventually_has_fderiv_at
- \+ *lemma* has_ftaylor_series_up_to_on.has_fderiv_at
- \+ *lemma* times_cont_diff.has_strict_deriv_at
- \+ *lemma* times_cont_diff_at.has_strict_deriv_at'
- \+ *lemma* times_cont_diff_at.has_strict_deriv_at

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.has_strict_deriv_at_exp
- \+ *lemma* complex.is_open_map_exp

Modified src/topology/basic.lean
- \+ *lemma* interior_mem_nhds



## [2021-02-07 06:54:51](https://github.com/leanprover-community/mathlib/commit/8b1f323)
feat(ring_theory/polynomial): Almost Vieta's formula on products of (X + r) ([#5696](https://github.com/leanprover-community/mathlib/pull/5696))
The main result is `prod_X_add_C_eq_sum_esymm`, which proves that a product of linear terms is equal to a linear combination of symmetric polynomials. Evaluating the variables of the symmetric polynomials gives Vieta's Formula.
#### Estimated changes
Modified src/algebra/big_operators/ring.lean
- \+ *lemma* finset.prod_powerset
- \+ *lemma* finset.sum_powerset

Modified src/data/finset/powerset.lean
- \+ *lemma* finset.powerset_card_bUnion
- \+ *theorem* finset.powerset_len_empty
- \+/\- *lemma* finset.powerset_len_zero

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_X_add_C

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.coeff_C_ne_zero

Modified src/ring_theory/polynomial/symmetric.lean


Added src/ring_theory/polynomial/vieta.lean
- \+ *lemma* mv_polynomial.esymm_to_sum
- \+ *lemma* mv_polynomial.prod_X_add_C_coeff
- \+ *lemma* mv_polynomial.prod_X_add_C_eq_sum_esymm
- \+ *lemma* mv_polynomial.prod_X_add_C_eval



## [2021-02-07 04:02:36](https://github.com/leanprover-community/mathlib/commit/4b035fc)
refactor(analysis/normed_space): upgrade `linear_map.to_continuous_linear_map` to `linear_equiv` ([#6072](https://github.com/leanprover-community/mathlib/pull/6072))
This way Lean will simplify, e.g., `f.to_continuous_linear_map = 0` to
`f = 0`.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* linear_map.coe_to_continuous_linear_map'
- \+ *lemma* linear_map.coe_to_continuous_linear_map
- \+ *lemma* linear_map.coe_to_continuous_linear_map_symm
- \+/\- *def* linear_map.to_continuous_linear_map



## [2021-02-07 02:14:17](https://github.com/leanprover-community/mathlib/commit/736929e)
chore(scripts): update nolints.txt ([#6073](https://github.com/leanprover-community/mathlib/pull/6073))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-06 22:54:57](https://github.com/leanprover-community/mathlib/commit/7f467fa)
feat(algebra/group/hom): add inv_comp and comp_inv ([#6046](https://github.com/leanprover-community/mathlib/pull/6046))
Two missing lemmas. Used in the Liquid Tensor Experiment.
Inversion for monoid hom is (correctly) only defined when the target is a comm_group; this explains the choice of typeclasses. I follow `inv_apply` and use `{}` rather than `[]`, but this is certainly not my area of expertise.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.comp_inv
- \+ *lemma* monoid_hom.inv_comp



## [2021-02-06 22:54:56](https://github.com/leanprover-community/mathlib/commit/7c53a16)
feat(algebra/ordered_ring): add lemma ([#6031](https://github.com/leanprover-community/mathlib/pull/6031))
Add a lemma in algebra.ordered_ring proving the inequality `a + (2 + b) ≤ a * (2 + b)`.
This is again part of the Liouville PR.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* add_le_mul_two_add



## [2021-02-06 21:31:25](https://github.com/leanprover-community/mathlib/commit/7ec4fcc)
feat(category_theory): connected components of a category ([#5425](https://github.com/leanprover-community/mathlib/pull/5425))
#### Estimated changes
Added src/category_theory/connected_components.lean
- \+ *def* category_theory.component.ι
- \+ *def* category_theory.component
- \+ *def* category_theory.connected_components
- \+ *def* category_theory.decomposed_equiv
- \+ *def* category_theory.decomposed_to
- \+ *lemma* category_theory.inclusion_comp_decomposed_to



## [2021-02-06 20:09:52](https://github.com/leanprover-community/mathlib/commit/a1ebf54)
refactor(data/buffer/parser/basic): make valid a class and rename to mono ([#6015](https://github.com/leanprover-community/mathlib/pull/6015))
#### Estimated changes
Modified src/data/buffer/parser/basic.lean
- \+ *lemma* parser.foldl_eq_fail_iff_mono_at_end
- \+ *lemma* parser.foldr_eq_fail_iff_mono_at_end
- \- *lemma* parser.foldr_eq_fail_of_valid_at_end
- \+ *lemma* parser.mono.fix
- \+ *lemma* parser.mono.fix_core
- \+ *lemma* parser.mono.le
- \+ *lemma* parser.mono.of_done
- \+ *lemma* parser.mono.of_fail
- \- *lemma* parser.orelse_eq_fail_invalid_lt
- \+ *lemma* parser.orelse_eq_fail_not_mono_lt
- \+ *lemma* parser.orelse_eq_fail_of_mono_ne
- \- *lemma* parser.orelse_eq_fail_of_valid_ne
- \- *lemma* parser.valid.and_then
- \- *lemma* parser.valid.any_char
- \- *lemma* parser.valid.bind
- \- *lemma* parser.valid.ch
- \- *lemma* parser.valid.char_buf
- \- *lemma* parser.valid.decorate_error
- \- *lemma* parser.valid.decorate_errors
- \- *lemma* parser.valid.digit
- \- *lemma* parser.valid.eof
- \- *lemma* parser.valid.eps
- \- *lemma* parser.valid.failure
- \- *lemma* parser.valid.fix
- \- *lemma* parser.valid.fix_core
- \- *lemma* parser.valid.foldl
- \- *lemma* parser.valid.foldl_core
- \- *lemma* parser.valid.foldl_core_zero
- \- *lemma* parser.valid.foldr
- \- *lemma* parser.valid.foldr_core
- \- *lemma* parser.valid.foldr_core_zero
- \- *lemma* parser.valid.guard
- \- *lemma* parser.valid.many'
- \- *lemma* parser.valid.many1
- \- *lemma* parser.valid.many
- \- *lemma* parser.valid.many_char1
- \- *lemma* parser.valid.many_char
- \- *lemma* parser.valid.map
- \- *lemma* parser.valid.mmap'
- \- *lemma* parser.valid.mmap
- \- *lemma* parser.valid.mono_done
- \- *lemma* parser.valid.mono_fail
- \- *lemma* parser.valid.nat
- \- *lemma* parser.valid.one_of'
- \- *lemma* parser.valid.one_of
- \- *lemma* parser.valid.orelse
- \- *lemma* parser.valid.pure
- \- *lemma* parser.valid.remaining
- \- *lemma* parser.valid.sat
- \- *lemma* parser.valid.sep_by1
- \- *lemma* parser.valid.sep_by
- \- *lemma* parser.valid.seq
- \- *lemma* parser.valid.str
- \- *def* parser.valid



## [2021-02-06 15:06:18](https://github.com/leanprover-community/mathlib/commit/dbf038d)
feat(topology/category): constructor for compact hausdorff spaces ([#6068](https://github.com/leanprover-community/mathlib/pull/6068))
`CompHaus.of` constructor. From the lean-liquid project.
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *lemma* CompHaus.coe_of
- \+ *def* CompHaus.of
- \+/\- *def* StoneCech_obj



## [2021-02-06 12:13:41](https://github.com/leanprover-community/mathlib/commit/767e6ae)
refactor(topology): make two definitions irreducible from the start ([#6060](https://github.com/leanprover-community/mathlib/pull/6060))
#### Estimated changes
Modified src/topology/basic.lean
- \+/\- *def* nhds
- \+/\- *lemma* nhds_def

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *def* emetric.Hausdorff_edist



## [2021-02-06 08:37:26](https://github.com/leanprover-community/mathlib/commit/2bdeda9)
doc(number_theory/*): provide docstrings for basic and dioph ([#6063](https://github.com/leanprover-community/mathlib/pull/6063))
The main purpose of this PR is to provide docstrings for the two remaining files without docstring in number_theory, basic and dioph. Furthermore, lines are split in other files, so that there should be no number_theory entries in the style_exceptions file.
#### Estimated changes
Modified src/number_theory/basic.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/pell.lean
- \+/\- *theorem* pell.eq_of_xn_modeq'

Modified src/number_theory/primorial.lean


Modified src/number_theory/pythagorean_triples.lean
- \+/\- *lemma* pythagorean_triple.is_classified_of_normalize_is_primitive_classified

Modified src/number_theory/quadratic_reciprocity.lean




## [2021-02-06 05:00:08](https://github.com/leanprover-community/mathlib/commit/d951b2b)
feat(data/nat): division of powers ([#6067](https://github.com/leanprover-community/mathlib/pull/6067))
A small missing lemma.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.pow_div



## [2021-02-06 01:48:21](https://github.com/leanprover-community/mathlib/commit/b8a6f81)
chore(scripts): update nolints.txt ([#6066](https://github.com/leanprover-community/mathlib/pull/6066))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-02-06 01:48:19](https://github.com/leanprover-community/mathlib/commit/b6b90e2)
fix(ring_theory/power_series/basic): fix algebra arguments ([#6065](https://github.com/leanprover-community/mathlib/pull/6065))
`power_series` is just an alias for `mv_power_series` over `unit`, yet it did not correctly inherit the algebra instance
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean




## [2021-02-06 01:48:17](https://github.com/leanprover-community/mathlib/commit/94033d8)
feat(data/list/basic): simp iffs about *fix nil ([#6064](https://github.com/leanprover-community/mathlib/pull/6064))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.eq_nil_iff_infix_nil
- \+ *theorem* list.eq_nil_iff_prefix_nil
- \+ *theorem* list.eq_nil_iff_suffix_nil



## [2021-02-05 22:20:21](https://github.com/leanprover-community/mathlib/commit/0926e67)
feat(algebra/star): star_ordered_ring ([#4685](https://github.com/leanprover-community/mathlib/pull/4685))
#### Estimated changes
Modified src/algebra/ordered_ring.lean


Modified src/algebra/star/basic.lean
- \+ *lemma* star_mul_self_nonneg



## [2021-02-05 15:46:37](https://github.com/leanprover-community/mathlib/commit/bd38c5f)
chore(linear_algebra): move `is_basis_std_basis` to `std_basis.lean` ([#6054](https://github.com/leanprover-community/mathlib/pull/6054))
This is a follow-up to [#6020](https://github.com/leanprover-community/mathlib/pull/6020) which moved `std_basis` to a new file: now move results from `basis.lean` to that same file.
CC @eric-wieser
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \- *lemma* pi.is_basis_fun
- \- *lemma* pi.is_basis_fun_repr
- \- *lemma* pi.is_basis_fun₀
- \- *lemma* pi.is_basis_std_basis
- \- *lemma* pi.linear_independent_std_basis

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/std_basis.lean
- \+ *lemma* pi.is_basis_fun
- \+ *lemma* pi.is_basis_fun_repr
- \+ *lemma* pi.is_basis_fun₀
- \+ *lemma* pi.is_basis_std_basis
- \+ *lemma* pi.linear_independent_std_basis

Modified src/ring_theory/power_series/basic.lean




## [2021-02-05 15:46:35](https://github.com/leanprover-community/mathlib/commit/b5c23ce)
feat(data/nat/factorial): non-strict inequality on factorial ([#6052](https://github.com/leanprover-community/mathlib/pull/6052))
Add lemmas add_factorial_le_factorial_add and  add_factorial_le_factorial_add'.  These are still used in the Liouville PR.
I should have added them to the previous PR on factorials, but they got lost on the way!
#### Estimated changes
Modified src/data/nat/factorial.lean
- \+ *lemma* nat.add_factorial_le_factorial_add
- \- *lemma* nat.add_factorial_lt_factorial_add'
- \+/\- *lemma* nat.add_factorial_lt_factorial_add
- \+ *lemma* nat.add_factorial_succ_le_factorial_add_succ
- \+ *lemma* nat.add_factorial_succ_lt_factorial_add_succ



## [2021-02-05 15:46:33](https://github.com/leanprover-community/mathlib/commit/1ab7cf6)
feat(algebra/ordered_ring): proof that `a + b ≤ a * b` ([#6043](https://github.com/leanprover-community/mathlib/pull/6043))
This is Johan's proof of the fact above.  If you are curious about the assumptions, there is an extensive discussion on
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* add_le_mul'
- \+ *lemma* add_le_mul
- \+ *lemma* add_le_mul_of_left_le_right
- \+ *lemma* add_le_mul_of_right_le_left



## [2021-02-05 15:46:31](https://github.com/leanprover-community/mathlib/commit/fa9bf62)
feat(algebra/char_zero): add char_zero lemma for ordered_semirings ([#6038](https://github.com/leanprover-community/mathlib/pull/6038))
Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* ordered_semiring.to_char_zero



## [2021-02-05 15:46:28](https://github.com/leanprover-community/mathlib/commit/c2c686e)
feat(linear_algebra/multilinear): add more `curry` equivs ([#6012](https://github.com/leanprover-community/mathlib/pull/6012))
* `multilinear_map (λ i : ι ⊕ ι', E) F` is equivalent to
  `multilinear_map (λ i : ι, E) (multilinear_map (λ i : ι', E) F)`;
* given `s : finset (fin n)`, `s.card = k`, and `sᶜ.card = l`,
  `multilinear_map (λ i : fin n, E) F` is equivalent to
  `multilinear_map (λ i : fin k, E) (multilinear_map (λ i : fin l, E) F)`.
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.coe_curr_sum_equiv_symm
- \+ *lemma* multilinear_map.coe_curry_sum_equiv
- \+ *def* multilinear_map.curry_fin_finset
- \+ *lemma* multilinear_map.curry_fin_finset_apply
- \+ *lemma* multilinear_map.curry_fin_finset_apply_const
- \+ *lemma* multilinear_map.curry_fin_finset_symm_apply
- \+ *lemma* multilinear_map.curry_fin_finset_symm_apply_const
- \+ *lemma* multilinear_map.curry_fin_finset_symm_apply_piecewise_const
- \+ *def* multilinear_map.curry_sum
- \+ *lemma* multilinear_map.curry_sum_apply
- \+ *def* multilinear_map.curry_sum_equiv
- \+ *def* multilinear_map.dom_dom_congr_linear_equiv
- \+ *def* multilinear_map.uncurry_sum
- \+ *lemma* multilinear_map.uncurry_sum_aux_apply



## [2021-02-05 15:46:26](https://github.com/leanprover-community/mathlib/commit/dc98547)
feat(linear_algebra/projection): Extending maps from complement submodules to the entire module ([#5981](https://github.com/leanprover-community/mathlib/pull/5981))
Given two linear maps from complement submodules, `of_is_comp` is the linear map extended to the entire module. 
This is useful whenever we would like to extend a linear map from a submodule to a map on the entire module.
#### Estimated changes
Modified src/linear_algebra/projection.lean
- \+ *def* linear_map.of_is_compl
- \+ *lemma* linear_map.of_is_compl_add
- \+ *lemma* linear_map.of_is_compl_eq'
- \+ *lemma* linear_map.of_is_compl_eq
- \+ *lemma* linear_map.of_is_compl_left_apply
- \+ *def* linear_map.of_is_compl_prod
- \+ *lemma* linear_map.of_is_compl_prod_apply
- \+ *def* linear_map.of_is_compl_prod_equiv
- \+ *lemma* linear_map.of_is_compl_right_apply
- \+ *lemma* linear_map.of_is_compl_smul
- \+ *lemma* linear_map.of_is_compl_zero
- \+ *lemma* submodule.exists_unique_add_of_is_compl
- \+ *lemma* submodule.exists_unique_add_of_is_compl_prod



## [2021-02-05 12:11:35](https://github.com/leanprover-community/mathlib/commit/34e366c)
refactor(*): remove uses of @[class] def  ([#6028](https://github.com/leanprover-community/mathlib/pull/6028))
Preparation for lean 4, which does not support this idiom.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *def* irreducible
- \+ *lemma* irreducible_iff

Modified src/algebra/gcd_monoid.lean


Modified src/algebra/squarefree.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/computability/turing_machine.lean


Modified src/data/list/forall2.lean
- \+ *lemma* list.left_unique_forall₂'
- \+/\- *lemma* list.left_unique_forall₂
- \+ *lemma* list.right_unique_forall₂'
- \+/\- *lemma* list.right_unique_forall₂

Modified src/data/list/perm.lean


Modified src/data/option/basic.lean
- \+ *theorem* option.mem.left_unique

Modified src/data/pfun.lean
- \+ *theorem* roption.mem.left_unique
- \+/\- *theorem* roption.mem_unique

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/seq/computation.lean
- \+ *theorem* computation.mem.left_unique
- \+/\- *theorem* computation.mem_unique
- \- *def* computation.terminates
- \+ *theorem* computation.terminates_iff
- \+/\- *theorem* computation.terminates_of_mem

Modified src/data/seq/parallel.lean


Modified src/data/seq/wseq.lean
- \- *def* wseq.is_finite
- \- *def* wseq.productive
- \+ *theorem* wseq.productive_iff

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/algebraic_closure.lean
- \- *def* is_alg_closure
- \+ *theorem* is_alg_closure_iff

Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean
- \+/\- *lemma* is_galois.integral
- \- *lemma* is_galois.normal
- \+/\- *lemma* is_galois.separable
- \+ *lemma* is_galois.splits
- \- *def* is_galois
- \+ *theorem* is_galois_iff

Modified src/field_theory/normal.lean
- \+/\- *theorem* normal.exists_is_splitting_field
- \+/\- *theorem* normal.is_integral
- \+ *theorem* normal.out
- \+/\- *theorem* normal.splits
- \- *def* normal
- \+ *theorem* normal_iff

Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean
- \+ *theorem* is_separable.is_integral
- \+ *theorem* is_separable.separable
- \- *def* is_separable
- \+ *theorem* is_separable_iff

Modified src/linear_algebra/adic_completion.lean
- \+ *theorem* is_Hausdorff.haus
- \- *def* is_Hausdorff
- \+ *theorem* is_Hausdorff_iff
- \- *def* is_adic_complete
- \+ *theorem* is_precomplete.prec
- \- *def* is_precomplete
- \+ *theorem* is_precomplete_iff

Modified src/logic/relation.lean


Modified src/logic/relator.lean
- \- *def* relator.bi_total
- \- *def* relator.bi_unique
- \- *def* relator.left_total
- \+ *lemma* relator.left_unique.unique
- \- *def* relator.left_unique
- \+/\- *lemma* relator.left_unique_flip
- \+/\- *lemma* relator.left_unique_of_rel_eq
- \+/\- *lemma* relator.rel_exists_of_left_total
- \+/\- *lemma* relator.rel_exists_of_total
- \+/\- *lemma* relator.rel_forall_of_right_total
- \+/\- *lemma* relator.rel_forall_of_total
- \- *def* relator.right_total
- \+ *lemma* relator.right_unique.unique
- \- *def* relator.right_unique

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/ess_sup.lean


Modified src/measure_theory/measure_space.lean
- \+ *theorem* measure_theory.measure.is_complete.out
- \- *def* measure_theory.measure.is_complete
- \+ *theorem* measure_theory.measure.is_complete_iff
- \+ *theorem* measure_theory.sigma_finite.out
- \- *def* measure_theory.sigma_finite
- \+ *theorem* measure_theory.sigma_finite_iff

Modified src/measure_theory/prod.lean


Modified src/order/filter/bases.lean
- \+ *lemma* filter.not_mem_iff_inf_principal_compl

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually_const
- \+/\- *lemma* filter.ne_bot.ne
- \- *def* filter.ne_bot
- \+ *lemma* filter.ne_bot_iff

Modified src/order/filter/cofinite.lean


Modified src/order/filter/ultrafilter.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.is_maximal.ne_top
- \- *def* ideal.is_maximal
- \+ *theorem* ideal.is_maximal_def
- \+ *theorem* ideal.is_prime.ne_top
- \- *def* ideal.is_prime
- \+ *theorem* ideal.is_prime_iff

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/jacobson.lean
- \+ *theorem* ideal.is_jacobson.out
- \- *def* ideal.is_jacobson
- \+ *theorem* ideal.is_jacobson_iff

Modified src/ring_theory/jacobson_ideal.lean
- \- *def* ideal.is_local
- \+ *theorem* ideal.is_local_iff

Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean
- \- *def* is_noetherian_ring
- \+ *theorem* is_noetherian_ring_iff

Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/is_poly.lean
- \- *def* witt_vector.is_poly
- \- *def* witt_vector.is_poly₂

Modified src/ring_theory/witt_vector/mul_p.lean


Modified src/set_theory/game/impartial.lean
- \- *def* pgame.impartial
- \+ *def* pgame.impartial_aux
- \+ *lemma* pgame.impartial_aux_def
- \+/\- *lemma* pgame.impartial_def
- \+ *lemma* pgame.impartial_iff_aux

Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+ *lemma* mem_closure_iff_nhds_ne_bot

Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean
- \- *def* separated_space
- \+ *theorem* separated_space_iff

Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-02-05 12:11:33](https://github.com/leanprover-community/mathlib/commit/c6c7eaf)
refactor(topology/algebra/module,analysis/*): merge some `smul` lemmas and defs ([#5987](https://github.com/leanprover-community/mathlib/pull/5987))
Generalize some definitions and lemmas about `smul`  and `f : E →L[k] F` so that now they allow scalars from an algebra over `k`. This way we can get rid of `smul_algebra` definitions and lemmas.
In particular, now `continuous_linear_map.smul_right` accepts functions with values in an algebra over `k`, so `smul_right 1 f` now needs a type annotation on `1`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean
- \- *lemma* differentiable.const_smul_algebra
- \- *lemma* differentiable.smul_algebra
- \- *lemma* differentiable.smul_algebra_const
- \- *lemma* differentiable_at.const_smul_algebra
- \- *lemma* differentiable_at.smul_algebra
- \- *lemma* differentiable_at.smul_algebra_const
- \- *lemma* differentiable_on.const_smul_algebra
- \- *lemma* differentiable_on.smul_algebra
- \- *lemma* differentiable_on.smul_algebra_const
- \- *lemma* differentiable_within_at.const_smul_algebra
- \- *lemma* differentiable_within_at.smul_algebra
- \- *lemma* differentiable_within_at.smul_algebra_const
- \- *lemma* fderiv_const_smul_algebra
- \- *lemma* fderiv_smul_algebra
- \- *lemma* fderiv_smul_algebra_const
- \- *lemma* fderiv_within_const_smul_algebra
- \- *lemma* fderiv_within_smul_algebra
- \- *lemma* fderiv_within_smul_algebra_const
- \- *theorem* has_fderiv_at.const_smul_algebra
- \- *theorem* has_fderiv_at.smul_algebra
- \- *theorem* has_fderiv_at.smul_algebra_const
- \- *theorem* has_fderiv_at_filter.const_smul_algebra
- \- *theorem* has_fderiv_within_at.const_smul_algebra
- \- *theorem* has_fderiv_within_at.smul_algebra
- \- *theorem* has_fderiv_within_at.smul_algebra_const
- \- *theorem* has_strict_fderiv_at.const_smul_algebra
- \- *theorem* has_strict_fderiv_at.smul_algebra
- \- *theorem* has_strict_fderiv_at.smul_algebra_const

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* is_bounded_bilinear_map_smul
- \- *lemma* is_bounded_bilinear_map_smul_algebra

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* submodule.coe_subtypeL'
- \+ *lemma* submodule.coe_subtypeL
- \+ *lemma* submodule.coe_subtypeₗᵢ
- \+ *def* submodule.subtypeL
- \+ *def* submodule.subtypeₗᵢ
- \+ *lemma* submodule.subtypeₗᵢ_to_linear_map

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.coe_restrict_scalarsL'
- \+ *lemma* continuous_linear_map.coe_restrict_scalarsL
- \+ *lemma* continuous_linear_map.coe_restrict_scalars_isometry
- \+ *lemma* continuous_linear_map.norm_restrict_scalars
- \+/\- *lemma* continuous_linear_map.op_norm_neg
- \+/\- *lemma* continuous_linear_map.op_norm_smul_le
- \- *def* continuous_linear_map.restrict_scalars
- \+ *def* continuous_linear_map.restrict_scalarsL
- \- *lemma* continuous_linear_map.restrict_scalars_coe_eq_coe'
- \- *lemma* continuous_linear_map.restrict_scalars_coe_eq_coe
- \+ *def* continuous_linear_map.restrict_scalars_isometry
- \+ *lemma* continuous_linear_map.restrict_scalars_isometry_to_linear_map
- \- *def* continuous_linear_map.smul_algebra_right
- \- *theorem* continuous_linear_map.smul_algebra_right_apply
- \+/\- *lemma* linear_isometry.norm_to_continuous_linear_map
- \+ *lemma* linear_isometry.norm_to_continuous_linear_map_le
- \+ *lemma* submodule.norm_subtypeL
- \+ *lemma* submodule.norm_subtypeL_le
- \- *def* submodule.subtype_continuous
- \- *lemma* submodule.subtype_continuous_apply

Modified src/geometry/manifold/instances/sphere.lean


Modified src/topology/algebra/module.lean
- \- *lemma* continuous_linear_map.coe_apply'
- \- *lemma* continuous_linear_map.coe_apply
- \+ *lemma* continuous_linear_map.coe_eq_id
- \+ *lemma* continuous_linear_map.coe_inj
- \+ *lemma* continuous_linear_map.coe_restrict_scalars'
- \+ *lemma* continuous_linear_map.coe_restrict_scalars
- \+ *lemma* continuous_linear_map.coe_restrict_scalarsₗ
- \+ *lemma* continuous_linear_map.coe_smul'
- \+ *lemma* continuous_linear_map.coe_smul
- \+ *lemma* continuous_linear_map.coe_smul_rightₗ
- \+/\- *lemma* continuous_linear_map.comp_smul
- \+ *lemma* continuous_linear_map.fst_comp_prod
- \+ *lemma* continuous_linear_map.map_smul_of_tower
- \+ *def* continuous_linear_map.restrict_scalars
- \+ *lemma* continuous_linear_map.restrict_scalars_add
- \+ *lemma* continuous_linear_map.restrict_scalars_neg
- \+ *lemma* continuous_linear_map.restrict_scalars_smul
- \+ *lemma* continuous_linear_map.restrict_scalars_zero
- \+ *def* continuous_linear_map.restrict_scalarsₗ
- \+/\- *lemma* continuous_linear_map.smul_apply
- \+/\- *def* continuous_linear_map.smul_right
- \+/\- *lemma* continuous_linear_map.smul_right_apply
- \+/\- *lemma* continuous_linear_map.smul_right_one_one
- \+/\- *def* continuous_linear_map.smul_rightₗ
- \+ *lemma* continuous_linear_map.snd_comp_prod



## [2021-02-05 12:11:32](https://github.com/leanprover-community/mathlib/commit/392ebec)
chore(algebra/algebra/basic): show that the ℚ-algebra structure is unique ([#5980](https://github.com/leanprover-community/mathlib/pull/5980))
Note that we already have similar lemmas showing that ℕ and ℤ modules are unique.
The name is based on `rat.algebra_rat`, which provides a canonical instance.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* rat.algebra_rat_subsingleton



## [2021-02-05 12:11:29](https://github.com/leanprover-community/mathlib/commit/915bff4)
feat(field_theory/polynomial_galois_group): Restriction is surjective ([#5961](https://github.com/leanprover-community/mathlib/pull/5961))
Proves surjectivity of `restrict` and `restrict_dvd`.
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.restrict_dvd_surjective
- \+ *lemma* polynomial.gal.restrict_surjective



## [2021-02-05 12:11:27](https://github.com/leanprover-community/mathlib/commit/e1db909)
feat(order/filter): add lattice instance to order.ideal ([#5937](https://github.com/leanprover-community/mathlib/pull/5937))
Add lattice instance to `order.ideal P` when the preorder `P` is
actually a `semilattice_sup_bot` (that is, when `P` is a partial
order with all finite suprema).
#### Estimated changes
Modified src/order/ideal.lean
- \+ *def* order.ideal.inf
- \+ *lemma* order.ideal.mem_inf
- \+ *lemma* order.ideal.mem_sup
- \+ *def* order.ideal.sup
- \+ *lemma* order.ideal.sup_le



## [2021-02-05 12:11:25](https://github.com/leanprover-community/mathlib/commit/70269f3)
feat(order/*): introduces complemented lattices ([#5747](https://github.com/leanprover-community/mathlib/pull/5747))
Defines `is_complemented` on bounded lattices
Proves facts about complemented modular lattices
Provides two instances of `is_complemented` on submodule lattices
#### Estimated changes
Modified src/linear_algebra/basis.lean


Modified src/order/atoms.lean
- \+ *theorem* is_atomic_iff_is_coatomic
- \+ *lemma* is_atomic_of_is_coatomic_of_is_complemented_of_is_modular
- \+ *lemma* is_coatomic_of_is_atomic_of_is_complemented_of_is_modular

Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_is_compl_top
- \+ *lemma* eq_bot_of_top_is_compl
- \+ *lemma* eq_top_of_bot_is_compl
- \+ *lemma* eq_top_of_is_compl_bot

Modified src/order/modular_lattice.lean


Modified src/representation_theory/maschke.lean
- \+/\- *lemma* monoid_algebra.exists_left_inverse_of_injective
- \+/\- *lemma* monoid_algebra.submodule.exists_is_compl
- \+ *theorem* monoid_algebra.submodule.is_complemented



## [2021-02-05 08:47:31](https://github.com/leanprover-community/mathlib/commit/5391433)
feat(algebra/group_power/basic): `pow_add_pow_le` ([#6037](https://github.com/leanprover-community/mathlib/pull/6037))
For natural `n ≠ 0` and nonnegative `x, y` in an `ordered_semiring`, `x ^ n + y ^ n ≤ (x + y) ^ n`.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* pow_add_pow_le



## [2021-02-05 04:22:35](https://github.com/leanprover-community/mathlib/commit/5cb2865)
chore(scripts): update nolints.txt ([#6049](https://github.com/leanprover-community/mathlib/pull/6049))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-02-05 00:51:27](https://github.com/leanprover-community/mathlib/commit/80c7ac1)
feat(algebra/big_operators/order): add fintype.sum_mono and fintype.sum_strict_mono ([#6040](https://github.com/leanprover-community/mathlib/pull/6040))
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* fintype.sum_mono
- \+ *lemma* fintype.sum_strict_mono



## [2021-02-05 00:51:25](https://github.com/leanprover-community/mathlib/commit/a101788)
fix(tactic/congr): fix trivial congr/convert ([#6011](https://github.com/leanprover-community/mathlib/pull/6011))
Now `convert` will prove reflexivity goals even at the top level, before
applying any congruence rules. Under the interpretation of the depth
argument as the number of nested congruence rules applied, we allow
proofs by assumption or reflexivity to work even at depth 0.
Also fixes a bug where
```lean
example {α} (a b : α) : a = b := by congr'
```
would succeed, because `apply proof_irrel` will unify the universe
metavariable in the type of `α` to `Prop`, causing surprising behavior.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified archive/imo/imo2019_q4.lean


Modified src/algebra/category/Group/images.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/computability/turing_machine.lean


Modified src/data/list/chain.lean


Modified src/data/matrix/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basis.lean


Modified src/measure_theory/interval_integral.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/tactic/congr.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/module.lean


Modified test/congr.lean


Modified test/convert.lean




## [2021-02-05 00:51:23](https://github.com/leanprover-community/mathlib/commit/59cfa02)
chore(data/quot): rename `lift_on_beta` to `lift_on_mk` ([#5921](https://github.com/leanprover-community/mathlib/pull/5921))
This also renames some other `lift_*_beta` lemmas to match their statement.
The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/quotient.20.22on_beta.22.20vs.20.22on_mk.22) was unanimously in favor of this rename.
#### Estimated changes
Modified src/algebra/ring_quot.lean


Modified src/data/dfinsupp.lean


Modified src/data/multiset/functor.lean
- \- *lemma* multiset.lift_beta
- \+ *lemma* multiset.lift_coe

Modified src/data/quot.lean
- \+ *lemma* quot.lift_mk
- \+ *lemma* quot.lift_on_mk
- \+/\- *lemma* quot.lift_on₂_mk
- \+/\- *lemma* quot.lift₂_mk
- \- *lemma* quotient.lift_beta
- \+ *lemma* quotient.lift_mk
- \- *lemma* quotient.lift_on_beta
- \- *theorem* quotient.lift_on_beta₂
- \+ *lemma* quotient.lift_on_mk
- \+ *theorem* quotient.lift_on₂_mk

Modified src/data/setoid/basic.lean


Modified src/group_theory/congruence.lean


Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/valuation/basic.lean




## [2021-02-04 21:33:38](https://github.com/leanprover-community/mathlib/commit/b9e559b)
feat(data/real/ennreal): use notation for ennreal ([#6044](https://github.com/leanprover-community/mathlib/pull/6044))
The notation for `ennreal` is `ℝ≥0∞` and it is localized to `ennreal` (though I guess it doesn't have to be?).
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20ennreal
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *theorem* formal_multilinear_series.change_origin_eval
- \+/\- *lemma* formal_multilinear_series.change_origin_has_sum
- \+/\- *lemma* formal_multilinear_series.change_origin_summable_aux1
- \+/\- *lemma* formal_multilinear_series.change_origin_summable_aux2
- \+/\- *lemma* formal_multilinear_series.change_origin_summable_aux3
- \+/\- *def* formal_multilinear_series.radius

Modified src/analysis/analytic/composition.lean


Modified src/analysis/analytic/radius_liminf.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/mean_inequalities.lean
- \+/\- *lemma* ennreal.add_rpow_le_rpow_add
- \+/\- *lemma* ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero
- \+/\- *lemma* ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm
- \+/\- *def* ennreal.fun_mul_inv_snorm
- \+/\- *lemma* ennreal.fun_mul_inv_snorm_rpow
- \+/\- *theorem* ennreal.lintegral_Lp_add_le
- \+/\- *lemma* ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one
- \+/\- *lemma* ennreal.rpow_add_le_add_rpow
- \+/\- *theorem* ennreal.rpow_add_rpow_le
- \+/\- *lemma* ennreal.rpow_add_rpow_le_add
- \+/\- *theorem* ennreal.rpow_arith_mean_le_arith_mean2_rpow
- \+/\- *theorem* ennreal.rpow_arith_mean_le_arith_mean_rpow
- \+/\- *theorem* ennreal.young_inequality

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* mem_emetric_ball_0_iff
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* real.ennnorm_eq_of_real

Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* ae_measurable.ennreal_rpow_const
- \+/\- *lemma* ennreal.div_rpow_of_nonneg
- \+/\- *lemma* ennreal.inv_rpow_of_pos
- \+/\- *lemma* ennreal.le_rpow_one_div_iff
- \+/\- *lemma* ennreal.le_rpow_self_of_one_le
- \+/\- *lemma* ennreal.lt_rpow_one_div_iff
- \+/\- *lemma* ennreal.measurable_rpow
- \+/\- *lemma* ennreal.measurable_rpow_const
- \+/\- *lemma* ennreal.mul_rpow_of_ne_top
- \+/\- *lemma* ennreal.mul_rpow_of_ne_zero
- \+/\- *lemma* ennreal.mul_rpow_of_nonneg
- \+/\- *lemma* ennreal.one_le_rpow
- \+/\- *lemma* ennreal.one_le_rpow_of_pos_of_le_one_of_neg
- \+/\- *lemma* ennreal.one_lt_rpow
- \+/\- *lemma* ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg
- \+/\- *lemma* ennreal.one_rpow
- \+/\- *lemma* ennreal.rpow_add
- \+/\- *lemma* ennreal.rpow_eq_pow
- \+/\- *lemma* ennreal.rpow_eq_top_iff
- \+/\- *lemma* ennreal.rpow_eq_top_iff_of_pos
- \+/\- *lemma* ennreal.rpow_eq_top_of_nonneg
- \+/\- *lemma* ennreal.rpow_eq_zero_iff
- \+/\- *lemma* ennreal.rpow_le_one
- \+/\- *lemma* ennreal.rpow_le_one_of_one_le_of_neg
- \+/\- *lemma* ennreal.rpow_le_rpow
- \+/\- *lemma* ennreal.rpow_le_rpow_iff
- \+/\- *lemma* ennreal.rpow_le_rpow_of_exponent_ge
- \+/\- *lemma* ennreal.rpow_le_rpow_of_exponent_le
- \+/\- *lemma* ennreal.rpow_le_self_of_le_one
- \+/\- *lemma* ennreal.rpow_left_monotone_of_nonneg
- \+/\- *lemma* ennreal.rpow_left_strict_mono_of_pos
- \+/\- *lemma* ennreal.rpow_lt_one
- \+/\- *lemma* ennreal.rpow_lt_one_of_one_lt_of_neg
- \+/\- *lemma* ennreal.rpow_lt_rpow
- \+/\- *lemma* ennreal.rpow_lt_rpow_iff
- \+/\- *lemma* ennreal.rpow_lt_rpow_of_exponent_gt
- \+/\- *lemma* ennreal.rpow_lt_rpow_of_exponent_lt
- \+/\- *lemma* ennreal.rpow_lt_top_of_nonneg
- \+/\- *lemma* ennreal.rpow_mul
- \+/\- *lemma* ennreal.rpow_nat_cast
- \+/\- *lemma* ennreal.rpow_ne_top_of_nonneg
- \+/\- *lemma* ennreal.rpow_neg
- \+/\- *lemma* ennreal.rpow_neg_one
- \+/\- *lemma* ennreal.rpow_one
- \+/\- *lemma* ennreal.rpow_pos
- \+/\- *lemma* ennreal.rpow_pos_of_nonneg
- \+/\- *lemma* ennreal.rpow_zero
- \+/\- *lemma* ennreal.to_nnreal_rpow
- \+/\- *lemma* ennreal.to_real_rpow
- \+/\- *lemma* ennreal.top_rpow_def
- \+/\- *lemma* ennreal.top_rpow_of_neg
- \+/\- *lemma* ennreal.top_rpow_of_pos
- \+/\- *lemma* ennreal.zero_rpow_def
- \+/\- *lemma* ennreal.zero_rpow_of_neg
- \+/\- *lemma* ennreal.zero_rpow_of_pos
- \+/\- *lemma* measurable.ennreal_rpow
- \+/\- *lemma* measurable.ennreal_rpow_const

Modified src/analysis/specific_limits.lean
- \+/\- *theorem* ennreal.exists_pos_sum_of_encodable
- \+/\- *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+/\- *lemma* ennreal.tsum_geometric

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.Inf_add
- \+/\- *lemma* ennreal.add_halves
- \+/\- *lemma* ennreal.add_infi
- \+/\- *lemma* ennreal.add_sub_self
- \+/\- *lemma* ennreal.bot_eq_zero
- \+/\- *lemma* ennreal.cinfi_ne_top
- \+/\- *lemma* ennreal.coe_Inf
- \+/\- *lemma* ennreal.coe_Sup
- \+/\- *lemma* ennreal.coe_add
- \+/\- *lemma* ennreal.coe_bit0
- \+/\- *lemma* ennreal.coe_bit1
- \+/\- *lemma* ennreal.coe_div
- \+/\- *lemma* ennreal.coe_eq_coe
- \+/\- *lemma* ennreal.coe_eq_one
- \+/\- *lemma* ennreal.coe_eq_zero
- \+/\- *lemma* ennreal.coe_inv
- \+/\- *lemma* ennreal.coe_inv_le
- \+/\- *lemma* ennreal.coe_inv_two
- \+/\- *lemma* ennreal.coe_le_coe
- \+/\- *lemma* ennreal.coe_le_one_iff
- \+/\- *lemma* ennreal.coe_lt_coe
- \+/\- *lemma* ennreal.coe_lt_coe_nat
- \+/\- *lemma* ennreal.coe_lt_one_iff
- \+/\- *lemma* ennreal.coe_max
- \+/\- *lemma* ennreal.coe_min
- \+/\- *lemma* ennreal.coe_mono
- \+/\- *lemma* ennreal.coe_mul
- \+/\- *lemma* ennreal.coe_nat
- \+/\- *lemma* ennreal.coe_nat_le_coe_nat
- \+/\- *lemma* ennreal.coe_nat_lt_coe
- \+/\- *lemma* ennreal.coe_nat_lt_coe_nat
- \+/\- *lemma* ennreal.coe_nat_mono
- \+/\- *lemma* ennreal.coe_nat_ne_top
- \+/\- *lemma* ennreal.coe_ne_top
- \+/\- *lemma* ennreal.coe_nnreal_eq
- \+/\- *lemma* ennreal.coe_nonneg
- \+/\- *lemma* ennreal.coe_one
- \+/\- *lemma* ennreal.coe_pos
- \+/\- *lemma* ennreal.coe_pow
- \+/\- *lemma* ennreal.coe_sub
- \+/\- *lemma* ennreal.coe_to_nnreal
- \+/\- *lemma* ennreal.coe_to_nnreal_le_self
- \+/\- *lemma* ennreal.coe_to_real
- \+/\- *lemma* ennreal.coe_two
- \+/\- *lemma* ennreal.coe_zero
- \+/\- *lemma* ennreal.csupr_ne_top
- \+/\- *lemma* ennreal.div_add_div_same
- \+/\- *lemma* ennreal.div_lt_top
- \+/\- *lemma* ennreal.div_one
- \+/\- *lemma* ennreal.eq_top_of_forall_nnreal_le
- \+/\- *lemma* ennreal.exists_inv_nat_lt
- \+/\- *lemma* ennreal.exists_ne_top
- \+/\- *lemma* ennreal.forall_ennreal
- \+/\- *lemma* ennreal.forall_ne_top
- \+/\- *lemma* ennreal.half_lt_self
- \+/\- *lemma* ennreal.half_pos
- \+/\- *lemma* ennreal.infi_ennreal
- \+/\- *lemma* ennreal.infi_mul
- \+/\- *lemma* ennreal.infi_ne_top
- \+/\- *lemma* ennreal.infi_sum
- \+/\- *lemma* ennreal.inv_bijective
- \+/\- *lemma* ennreal.inv_involutive
- \+/\- *lemma* ennreal.inv_lt_top
- \+/\- *lemma* ennreal.inv_one
- \+/\- *lemma* ennreal.inv_two_add_inv_two
- \+/\- *lemma* ennreal.inv_zero
- \+/\- *lemma* ennreal.le_of_add_le_add_left
- \+/\- *lemma* ennreal.le_of_forall_nnreal_lt
- \+/\- *lemma* ennreal.le_of_forall_pos_le_add
- \+/\- *lemma* ennreal.le_of_real_iff_to_real_le
- \+/\- *lemma* ennreal.le_of_top_imp_top_of_to_nnreal_le
- \+/\- *lemma* ennreal.lt_of_real_iff_to_real_lt
- \+/\- *lemma* ennreal.mul_infi
- \+/\- *lemma* ennreal.mul_le_iff_le_inv
- \+/\- *lemma* ennreal.mul_lt_top_iff
- \+ *lemma* ennreal.mul_self_lt_top_iff
- \+/\- *lemma* ennreal.nat_ne_top
- \+/\- *lemma* ennreal.none_eq_top
- \+/\- *lemma* ennreal.not_lt_top
- \+/\- *def* ennreal.of_nnreal_hom
- \+/\- *lemma* ennreal.of_real_le_iff_le_to_real
- \+/\- *lemma* ennreal.of_real_le_of_le_to_real
- \+/\- *lemma* ennreal.of_real_lt_iff_lt_to_real
- \+/\- *lemma* ennreal.of_real_one
- \+/\- *lemma* ennreal.of_real_to_real
- \+/\- *lemma* ennreal.of_real_to_real_le
- \+/\- *lemma* ennreal.one_eq_coe
- \+/\- *lemma* ennreal.one_half_lt_one
- \+/\- *lemma* ennreal.one_le_coe_iff
- \+/\- *lemma* ennreal.one_lt_coe_iff
- \+/\- *lemma* ennreal.one_lt_two
- \+/\- *lemma* ennreal.one_sub_inv_two
- \+/\- *lemma* ennreal.one_to_nnreal
- \+/\- *lemma* ennreal.one_to_real
- \+/\- *lemma* ennreal.prod_lt_top
- \+/\- *lemma* ennreal.some_eq_coe
- \+/\- *lemma* ennreal.sub_add_cancel_of_le
- \+/\- *lemma* ennreal.sub_le_self
- \+/\- *lemma* ennreal.sub_right_inj
- \+/\- *lemma* ennreal.sum_eq_top_iff
- \+/\- *lemma* ennreal.sum_lt_top
- \+/\- *lemma* ennreal.sum_lt_top_iff
- \+/\- *lemma* ennreal.supr_coe_nat
- \+/\- *lemma* ennreal.supr_ennreal
- \+/\- *lemma* ennreal.supr_ne_top
- \+/\- *lemma* ennreal.to_nnreal_add
- \+/\- *lemma* ennreal.to_nnreal_coe
- \+/\- *lemma* ennreal.to_nnreal_eq_zero_iff
- \+/\- *def* ennreal.to_nnreal_hom
- \+/\- *lemma* ennreal.to_nnreal_mul
- \+/\- *lemma* ennreal.to_nnreal_mul_top
- \+/\- *lemma* ennreal.to_nnreal_pow
- \+/\- *lemma* ennreal.to_nnreal_prod
- \+/\- *lemma* ennreal.to_nnreal_sum
- \+/\- *lemma* ennreal.to_nnreal_top_mul
- \+/\- *lemma* ennreal.to_real_eq_zero_iff
- \+/\- *def* ennreal.to_real_hom
- \+/\- *lemma* ennreal.to_real_le_of_le_of_real
- \+/\- *lemma* ennreal.to_real_mul_top
- \+/\- *lemma* ennreal.to_real_nonneg
- \+/\- *lemma* ennreal.to_real_of_real_mul
- \+/\- *lemma* ennreal.to_real_pow
- \+/\- *lemma* ennreal.to_real_prod
- \+/\- *lemma* ennreal.to_real_sum
- \+/\- *lemma* ennreal.to_real_top_mul
- \+/\- *lemma* ennreal.top_mem_upper_bounds
- \+/\- *lemma* ennreal.top_ne_coe
- \+/\- *lemma* ennreal.two_ne_top
- \+/\- *lemma* ennreal.two_ne_zero
- \+/\- *lemma* ennreal.zero_eq_coe
- \+/\- *lemma* ennreal.zero_lt_coe_iff
- \+/\- *lemma* ennreal.zero_lt_two
- \+/\- *lemma* ennreal.zero_to_nnreal
- \+/\- *lemma* ennreal.zero_to_real

Modified src/data/real/ereal.lean


Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *def* measure_theory.ae_eq_fun.lintegral
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_add
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_coe_fn
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_eq_zero_iff
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_mono
- \+/\- *lemma* measure_theory.ae_eq_fun.lintegral_zero

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_smul_measure
- \+/\- *lemma* measure_theory.integral_to_real
- \+/\- *lemma* measure_theory.simple_func.integral_eq_lintegral'

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* ae_measurable.ennreal_mul
- \+/\- *lemma* ae_measurable.to_real
- \+/\- *def* ennreal.ennreal_equiv_sum
- \+/\- *lemma* ennreal.measurable_coe
- \+/\- *lemma* ennreal.measurable_div
- \+/\- *lemma* ennreal.measurable_inv
- \+/\- *lemma* ennreal.measurable_mul
- \+/\- *lemma* ennreal.measurable_of_measurable_nnreal
- \+/\- *lemma* ennreal.measurable_sub
- \+/\- *lemma* measurable.ennreal_div
- \+/\- *lemma* measurable.ennreal_inv
- \+/\- *lemma* measurable.ennreal_mul
- \+/\- *lemma* measurable.ennreal_sub
- \+/\- *lemma* measurable.ennreal_tsum
- \+/\- *lemma* measurable.to_nnreal
- \+/\- *lemma* measurable.to_real
- \+/\- *lemma* measurable_ennnorm
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/content.lean
- \+/\- *def* measure_theory.inner_content
- \+/\- *lemma* measure_theory.inner_content_Sup_nat
- \+/\- *lemma* measure_theory.inner_content_Union_nat
- \+/\- *lemma* measure_theory.inner_content_comap
- \+/\- *lemma* measure_theory.inner_content_empty
- \+/\- *lemma* measure_theory.inner_content_exists_compact
- \+/\- *lemma* measure_theory.inner_content_le
- \+/\- *lemma* measure_theory.inner_content_mono'
- \+/\- *lemma* measure_theory.inner_content_mono
- \+/\- *lemma* measure_theory.inner_content_of_is_compact
- \+/\- *lemma* measure_theory.is_mul_left_invariant_inner_content
- \+/\- *lemma* measure_theory.le_inner_content
- \+/\- *def* measure_theory.outer_measure.of_content

Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/ess_sup.lean
- \+/\- *lemma* ennreal.ae_le_ess_sup
- \+/\- *lemma* ennreal.ess_sup_add_le
- \+/\- *lemma* ennreal.ess_sup_const_mul
- \+/\- *lemma* ennreal.ess_sup_eq_zero_iff

Modified src/measure_theory/giry_monad.lean
- \+/\- *lemma* measure_theory.measure.lintegral_bind
- \+/\- *lemma* measure_theory.measure.lintegral_join
- \+/\- *lemma* measure_theory.measure.measurable_lintegral

Modified src/measure_theory/group.lean
- \+/\- *def* measure_theory.is_mul_left_invariant
- \+/\- *def* measure_theory.is_mul_right_invariant

Modified src/measure_theory/haar_measure.lean
- \+/\- *def* measure_theory.measure.haar.echaar

Modified src/measure_theory/integration.lean
- \+/\- *theorem* measurable.ennreal_induction
- \+/\- *lemma* measure_theory.ae_lt_top
- \+/\- *lemma* measure_theory.exists_pos_set_lintegral_lt_of_measure_lt
- \+/\- *lemma* measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos
- \+/\- *theorem* measure_theory.le_infi2_lintegral
- \+/\- *theorem* measure_theory.le_infi_lintegral
- \+/\- *lemma* measure_theory.limsup_lintegral_le
- \+/\- *def* measure_theory.lintegral
- \+/\- *lemma* measure_theory.lintegral_Union_le
- \+/\- *lemma* measure_theory.lintegral_add'
- \+/\- *lemma* measure_theory.lintegral_add
- \+/\- *lemma* measure_theory.lintegral_add_measure
- \+/\- *lemma* measure_theory.lintegral_comp
- \+/\- *lemma* measure_theory.lintegral_congr
- \+/\- *lemma* measure_theory.lintegral_congr_ae
- \+/\- *lemma* measure_theory.lintegral_const
- \+/\- *lemma* measure_theory.lintegral_const_mul''
- \+/\- *lemma* measure_theory.lintegral_const_mul'
- \+/\- *lemma* measure_theory.lintegral_const_mul
- \+/\- *lemma* measure_theory.lintegral_const_mul_le
- \+/\- *lemma* measure_theory.lintegral_count'
- \+/\- *lemma* measure_theory.lintegral_count
- \+/\- *lemma* measure_theory.lintegral_dirac'
- \+/\- *lemma* measure_theory.lintegral_dirac
- \+/\- *lemma* measure_theory.lintegral_eq_nnreal
- \+/\- *lemma* measure_theory.lintegral_eq_supr_eapprox_lintegral
- \+/\- *lemma* measure_theory.lintegral_eq_zero_iff'
- \+/\- *lemma* measure_theory.lintegral_eq_zero_iff
- \+/\- *lemma* measure_theory.lintegral_finset_sum
- \+/\- *lemma* measure_theory.lintegral_indicator
- \+/\- *lemma* measure_theory.lintegral_liminf_le'
- \+/\- *lemma* measure_theory.lintegral_liminf_le
- \+/\- *lemma* measure_theory.lintegral_map'
- \+/\- *lemma* measure_theory.lintegral_map
- \+/\- *lemma* measure_theory.lintegral_mono'
- \+/\- *lemma* measure_theory.lintegral_mono
- \+/\- *lemma* measure_theory.lintegral_mono_ae
- \+/\- *lemma* measure_theory.lintegral_mul_const''
- \+/\- *lemma* measure_theory.lintegral_mul_const'
- \+/\- *lemma* measure_theory.lintegral_mul_const
- \+/\- *lemma* measure_theory.lintegral_mul_const_le
- \+/\- *lemma* measure_theory.lintegral_one
- \+/\- *lemma* measure_theory.lintegral_pos_iff_support
- \+/\- *lemma* measure_theory.lintegral_rw₁
- \+/\- *lemma* measure_theory.lintegral_smul_measure
- \+/\- *lemma* measure_theory.lintegral_sub
- \+/\- *lemma* measure_theory.lintegral_sum_measure
- \+/\- *theorem* measure_theory.lintegral_supr'
- \+/\- *lemma* measure_theory.lintegral_supr_ae
- \+/\- *theorem* measure_theory.lintegral_supr_directed
- \+/\- *lemma* measure_theory.lintegral_tsum
- \+/\- *lemma* measure_theory.lintegral_zero_fun
- \+/\- *lemma* measure_theory.lintegral_zero_measure
- \+/\- *lemma* measure_theory.meas_ge_le_lintegral_div
- \+/\- *def* measure_theory.measure.with_density
- \+/\- *lemma* measure_theory.mul_meas_ge_le_lintegral
- \+/\- *lemma* measure_theory.set_lintegral_congr
- \+/\- *lemma* measure_theory.set_lintegral_const
- \+/\- *lemma* measure_theory.set_lintegral_map
- \+/\- *lemma* measure_theory.simple_func.add_lintegral
- \+/\- *lemma* measure_theory.simple_func.const_lintegral
- \+/\- *lemma* measure_theory.simple_func.const_lintegral_restrict
- \+/\- *lemma* measure_theory.simple_func.const_mul_lintegral
- \+/\- *def* measure_theory.simple_func.eapprox
- \+/\- *lemma* measure_theory.simple_func.eapprox_comp
- \+/\- *def* measure_theory.simple_func.ennreal_rat_embed
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.of_lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.le_sup_lintegral
- \+/\- *def* measure_theory.simple_func.lintegral
- \+/\- *lemma* measure_theory.simple_func.lintegral_add
- \+/\- *lemma* measure_theory.simple_func.lintegral_congr
- \+/\- *theorem* measure_theory.simple_func.lintegral_eq_lintegral
- \+/\- *lemma* measure_theory.simple_func.lintegral_eq_of_measure_preimage
- \+/\- *lemma* measure_theory.simple_func.lintegral_eq_of_subset
- \+/\- *lemma* measure_theory.simple_func.lintegral_map
- \+/\- *lemma* measure_theory.simple_func.lintegral_mono
- \+/\- *lemma* measure_theory.simple_func.lintegral_restrict
- \+/\- *lemma* measure_theory.simple_func.lintegral_smul
- \+/\- *lemma* measure_theory.simple_func.lintegral_sum
- \+/\- *lemma* measure_theory.simple_func.lintegral_zero
- \+/\- *def* measure_theory.simple_func.lintegralₗ
- \+/\- *lemma* measure_theory.simple_func.map_lintegral
- \+/\- *lemma* measure_theory.simple_func.monotone_eapprox
- \+/\- *lemma* measure_theory.simple_func.restrict_const_lintegral
- \+/\- *lemma* measure_theory.simple_func.restrict_lintegral
- \+/\- *lemma* measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict
- \+/\- *lemma* measure_theory.simple_func.supr_eapprox_apply
- \+/\- *lemma* measure_theory.simple_func.zero_lintegral
- \+/\- *theorem* measure_theory.supr2_lintegral_le
- \+/\- *theorem* measure_theory.supr_lintegral_le
- \+/\- *lemma* measure_theory.tendsto_set_lintegral_zero
- \+/\- *lemma* measure_theory.with_density_apply

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_smul_measure

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.has_finite_integral.smul_measure
- \+/\- *lemma* measure_theory.integrable.smul_measure
- \+/\- *lemma* measure_theory.l1.norm_eq_lintegral

Modified src/measure_theory/lebesgue_measure.lean
- \+/\- *def* measure_theory.lebesgue_length

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.Lp.antimono
- \+/\- *lemma* measure_theory.mem_ℒp.mem_ℒp_of_exponent_le
- \+/\- *def* measure_theory.mem_ℒp
- \+/\- *def* measure_theory.snorm'
- \+/\- *def* measure_theory.snorm
- \+/\- *def* measure_theory.snorm_ess_sup
- \+/\- *lemma* measure_theory.snorm_le_snorm_of_exponent_le

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ae_measurable.smul_measure
- \+/\- *lemma* ae_measurable_smul_measure_iff
- \+/\- *lemma* measure_theory.ae_smul_measure
- \+/\- *lemma* measure_theory.ae_smul_measure_iff
- \+/\- *theorem* measure_theory.measure.coe_smul
- \+/\- *def* measure_theory.measure.comap
- \+/\- *lemma* measure_theory.measure.le_count_apply
- \+/\- *lemma* measure_theory.measure.le_lift_linear_apply
- \+/\- *def* measure_theory.measure.lift_linear
- \+/\- *lemma* measure_theory.measure.lift_linear_apply
- \+/\- *def* measure_theory.measure.map
- \+/\- *def* measure_theory.measure.of_measurable
- \+/\- *lemma* measure_theory.measure.of_measurable_apply
- \+/\- *lemma* measure_theory.measure.restrict_smul
- \+/\- *def* measure_theory.measure.restrictₗ
- \+/\- *theorem* measure_theory.measure.smul_apply
- \+/\- *theorem* measure_theory.measure.smul_to_outer_measure

Modified src/measure_theory/outer_measure.lean
- \+/\- *def* measure_theory.extend
- \+/\- *def* measure_theory.outer_measure.Inf_gen
- \+/\- *lemma* measure_theory.outer_measure.bounded_by_caratheodory
- \+/\- *lemma* measure_theory.outer_measure.coe_smul
- \+/\- *def* measure_theory.outer_measure.comap
- \+/\- *theorem* measure_theory.outer_measure.le_smul_caratheodory
- \+/\- *def* measure_theory.outer_measure.map
- \+/\- *lemma* measure_theory.outer_measure.of_function_caratheodory
- \+/\- *def* measure_theory.outer_measure.restrict
- \+/\- *lemma* measure_theory.outer_measure.smul_apply
- \+/\- *theorem* measure_theory.outer_measure.smul_dirac_apply
- \+/\- *theorem* measure_theory.outer_measure.trim_smul

Modified src/measure_theory/pi.lean
- \+/\- *def* measure_theory.pi_premeasure

Modified src/measure_theory/probability_mass_function.lean


Modified src/measure_theory/prod.lean
- \+/\- *lemma* measurable.lintegral_prod_left'
- \+/\- *lemma* measurable.lintegral_prod_left
- \+/\- *lemma* measurable.lintegral_prod_right
- \+/\- *lemma* measure_theory.lintegral_lintegral
- \+/\- *lemma* measure_theory.lintegral_lintegral_swap
- \+/\- *lemma* measure_theory.lintegral_lintegral_symm
- \+/\- *lemma* measure_theory.lintegral_prod
- \+/\- *lemma* measure_theory.lintegral_prod_mul
- \+/\- *lemma* measure_theory.lintegral_prod_swap
- \+/\- *lemma* measure_theory.lintegral_prod_symm'
- \+/\- *lemma* measure_theory.lintegral_prod_symm

Modified src/measure_theory/prod_group.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/filter/ennreal.lean
- \+/\- *lemma* ennreal.eventually_le_limsup
- \+/\- *lemma* ennreal.limsup_add_le
- \+/\- *lemma* ennreal.limsup_const_mul
- \+/\- *lemma* ennreal.limsup_const_mul_of_ne_top
- \+/\- *lemma* ennreal.limsup_eq_zero_iff

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* cauchy_seq_of_edist_le_of_tsum_ne_top
- \+/\- *lemma* continuous_of_le_add_edist
- \+/\- *lemma* edist_le_tsum_of_edist_le_of_tendsto
- \+/\- *lemma* edist_le_tsum_of_edist_le_of_tendsto₀
- \+/\- *lemma* edist_ne_top_of_mem_ball
- \+/\- *lemma* emetric.is_closed_ball
- \+/\- *lemma* ennreal.Sup_add
- \+/\- *lemma* ennreal.add_supr
- \+/\- *lemma* ennreal.bsupr_add
- \+/\- *lemma* ennreal.coe_range_mem_nhds
- \+/\- *lemma* ennreal.continuous_coe
- \+/\- *lemma* ennreal.embedding_coe
- \+/\- *lemma* ennreal.finset_sum_supr_nat
- \+/\- *lemma* ennreal.has_sum_iff_tendsto_nat
- \+/\- *lemma* ennreal.infi_mul_left
- \+/\- *lemma* ennreal.infi_mul_right
- \+/\- *lemma* ennreal.is_open_ne_top
- \+/\- *lemma* ennreal.le_of_forall_lt_one_mul_le
- \+/\- *lemma* ennreal.mul_Sup
- \+/\- *lemma* ennreal.mul_supr
- \+/\- *lemma* ennreal.nhds_coe
- \+/\- *lemma* ennreal.nhds_coe_coe
- \+/\- *lemma* ennreal.nhds_within_Ioi_coe_ne_bot
- \+/\- *lemma* ennreal.nhds_within_Ioi_zero_ne_bot
- \+/\- *lemma* ennreal.nhds_zero
- \+/\- *lemma* ennreal.sub_supr
- \+/\- *lemma* ennreal.summable_to_nnreal_of_tsum_ne_top
- \+/\- *lemma* ennreal.supr_add
- \+/\- *lemma* ennreal.supr_add_supr
- \+/\- *lemma* ennreal.supr_eq_zero
- \+/\- *lemma* ennreal.supr_mul
- \+/\- *lemma* ennreal.tendsto_nhds_top
- \+/\- *lemma* ennreal.tendsto_nhds_top_iff_nat
- \+/\- *lemma* ennreal.tendsto_nhds_top_iff_nnreal
- \+/\- *lemma* ennreal.tendsto_sum_nat_add
- \+/\- *lemma* ennreal.tendsto_to_nnreal
- \+/\- *lemma* ennreal.tendsto_to_real
- \+/\- *lemma* ennreal.to_nnreal_apply_of_tsum_ne_top
- \+/\- *lemma* ennreal.tsum_sub
- \+/\- *lemma* ennreal.tsum_supr_eq
- \+/\- *def* metric_space_emetric_ball
- \+/\- *lemma* nhds_eq_nhds_emetric_ball

Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean
- \+/\- *lemma* contracting_with.one_sub_K_ne_top
- \+/\- *lemma* contracting_with.one_sub_K_ne_zero
- \+/\- *lemma* contracting_with.one_sub_K_pos'

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* edist_mem_uniformity
- \+/\- *def* emetric.ball
- \+/\- *theorem* emetric.ball_mem_nhds
- \+/\- *theorem* emetric.ball_prod_same
- \+/\- *def* emetric.closed_ball
- \+/\- *theorem* emetric.closed_ball_prod_same
- \+/\- *theorem* emetric.complete_of_convergent_controlled_sequences
- \+/\- *lemma* emetric.diam_ball
- \+/\- *lemma* emetric.diam_closed_ball
- \+/\- *lemma* emetric.diam_le_iff_forall_edist_le
- \+/\- *lemma* emetric.diam_le_of_forall_edist_le
- \+/\- *theorem* emetric.nhds_basis_closed_eball
- \+/\- *theorem* emetric.nhds_basis_eball
- \+/\- *theorem* uniformity_basis_edist'
- \+/\- *theorem* uniformity_basis_edist_le'

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *def* emetric.Hausdorff_edist
- \+/\- *lemma* emetric.Hausdorff_edist_le_of_inf_edist
- \+/\- *lemma* emetric.Hausdorff_edist_le_of_mem_edist
- \+/\- *lemma* emetric.exists_edist_lt_of_Hausdorff_edist_lt
- \+/\- *lemma* emetric.exists_edist_lt_of_inf_edist_lt
- \+/\- *def* emetric.inf_edist

Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/metric_space/pi_Lp.lean


Modified test/norm_cast.lean
- \+/\- *lemma* ennreal.half_lt_self_bis



## [2021-02-04 21:33:36](https://github.com/leanprover-community/mathlib/commit/7734d38)
refactor(data/real/basic): make ℝ a structure ([#6024](https://github.com/leanprover-community/mathlib/pull/6024))
Preparation for :four_leaf_clover:, which doesn't have irreducible.
#### Estimated changes
Modified src/analysis/specific_limits.lean


Modified src/data/real/basic.lean
- \+ *lemma* real.add_cauchy
- \- *def* real.comm_ring_aux
- \+ *def* real.equiv_Cauchy
- \+ *lemma* real.ext_cauchy
- \+ *lemma* real.ext_cauchy_iff
- \+ *lemma* real.inv_cauchy
- \+ *lemma* real.lt_cauchy
- \+/\- *def* real.mk
- \+ *lemma* real.mk_add
- \+/\- *theorem* real.mk_eq
- \- *theorem* real.mk_eq_mk
- \+/\- *theorem* real.mk_le_of_forall_le
- \+/\- *theorem* real.mk_lt
- \+ *lemma* real.mk_mul
- \+ *lemma* real.mk_neg
- \+ *lemma* real.mk_one
- \+ *lemma* real.mk_zero
- \+ *lemma* real.mul_cauchy
- \+ *lemma* real.neg_cauchy
- \+/\- *def* real.of_rat
- \+ *lemma* real.of_rat_apply
- \+/\- *theorem* real.of_rat_lt
- \- *theorem* real.of_rat_sub
- \+ *lemma* real.one_cauchy
- \- *theorem* real.quotient_mk_eq_mk
- \+ *lemma* real.zero_cauchy
- \- *def* real

Modified src/data/real/cardinality.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* equiv.cardinal_eq

Modified src/topology/path_connected.lean




## [2021-02-04 21:33:34](https://github.com/leanprover-community/mathlib/commit/d293822)
feat(topology/algebra/infinite_sum, topology/instances/ennreal): extend tsum API ([#6017](https://github.com/leanprover-community/mathlib/pull/6017))
Lemma `tsum_lt_of_nonneg` shows that if a sequence `f` with non-negative terms is dominated by a sequence `g` with summable series and at least one term of `f` is strictly smaller than the corresponding term in `g`, then the series of `f` is strictly smaller than the series of `g`.
Besides this lemma, I also added the relevant API in topology.algebra.infinite_sum.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_congr
- \+ *lemma* tsum_ite_eq_extract
- \+ *lemma* tsum_lt_tsum

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_lt_tsum_of_nonneg



## [2021-02-04 21:33:32](https://github.com/leanprover-community/mathlib/commit/1ee00c8)
feat(number_theory/bernoulli): Results regarding Bernoulli numbers as a generating function ([#5957](https://github.com/leanprover-community/mathlib/pull/5957))
We prove that the Bernoulli numbers are generating functions for t/(e^t - 1). Most of the results are proved by @kbuzzard.
#### Estimated changes
Modified src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* finset.nat.prod_antidiagonal_eq_prod_range_succ_mk

Modified src/data/nat/choose/basic.lean
- \+ *lemma* nat.add_choose
- \+ *lemma* nat.factorial_mul_factorial_dvd_factorial_add

Modified src/number_theory/bernoulli.lean
- \+ *theorem* bernoulli_power_series
- \+ *lemma* bernoulli_spec'
- \+ *lemma* bernoulli_spec

Modified src/ring_theory/power_series/well_known.lean
- \+ *lemma* power_series.constant_coeff_exp



## [2021-02-04 18:03:59](https://github.com/leanprover-community/mathlib/commit/49cf0be)
refactor(real): protect real.pi ([#6039](https://github.com/leanprover-community/mathlib/pull/6039))
Currently, `real.pi` is not protected. This can conflict with `set.pi`. Since it is most often used as `π` through the `real` locale, let's protect it.
#### Estimated changes
Modified src/analysis/complex/roots_of_unity.lean
- \+/\- *lemma* complex.is_primitive_root_exp

Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* real.cos_pi_div_eight
- \+/\- *lemma* real.cos_pi_div_four
- \+/\- *lemma* real.cos_pi_div_sixteen
- \+/\- *lemma* real.cos_pi_div_thirty_two
- \+/\- *lemma* real.cos_pi_over_two_pow
- \+/\- *lemma* real.sin_pi_div_eight
- \+/\- *lemma* real.sin_pi_div_four
- \+/\- *lemma* real.sin_pi_div_sixteen
- \+/\- *lemma* real.sin_pi_div_thirty_two

Modified src/data/real/pi.lean
- \+/\- *lemma* real.pi_gt_3141592
- \+/\- *lemma* real.pi_gt_31415
- \+/\- *lemma* real.pi_gt_314
- \+/\- *lemma* real.pi_gt_sqrt_two_add_series
- \+/\- *lemma* real.pi_gt_three
- \+/\- *lemma* real.pi_lt_3141593
- \+/\- *lemma* real.pi_lt_31416
- \+/\- *lemma* real.pi_lt_315



## [2021-02-04 18:03:58](https://github.com/leanprover-community/mathlib/commit/1a7fb7e)
feat(data/list/sort): add sorted.rel_of_mem_take_of_mem_drop ([#6027](https://github.com/leanprover-community/mathlib/pull/6027))
Also renames the existing lemmas to enable dot notation
#### Estimated changes
Modified src/data/finset/sort.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/list/sort.lean
- \- *lemma* list.nth_le_of_sorted_of_le
- \+ *lemma* list.sorted.rel_nth_le_of_le
- \+ *lemma* list.sorted.rel_nth_le_of_lt
- \+ *lemma* list.sorted.rel_of_mem_take_of_mem_drop



## [2021-02-04 18:03:56](https://github.com/leanprover-community/mathlib/commit/b98b5f6)
chore(data/dfinsupp): add simp lemmas about sum_add_hom, remove commutativity requirement ([#5939](https://github.com/leanprover-community/mathlib/pull/5939))
Note that `dfinsupp.sum_add_hom` and `dfinsupp.sum` are not defeq, so its valuable to repeat these lemmas.
The former is often easier to work with because there are no decidability requirements to juggle on equality with zero.
`dfinsupp.single_eq_of_sigma_eq` was a handy lemma for constructing a term-mode proof of `dfinsupp.single` equality.
A lot of the lemmas about `lift_add_hom` have to be repeated for `sum_add_hom` because the former simplifies to the latter before its lemmas get a chance to apply. At least the proofs can be reused.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* add_monoid_hom.coe_dfinsupp_sum_add_hom
- \+ *lemma* add_monoid_hom.dfinsupp_sum_add_hom_apply
- \+ *lemma* add_monoid_hom.map_dfinsupp_sum_add_hom
- \+/\- *lemma* dfinsupp.comp_lift_add_hom
- \+ *lemma* dfinsupp.comp_sum_add_hom
- \+/\- *lemma* dfinsupp.lift_add_hom_apply_single
- \+/\- *lemma* dfinsupp.lift_add_hom_comp_single
- \+ *lemma* dfinsupp.single_eq_of_sigma_eq
- \+ *lemma* dfinsupp.sum_add_hom_add
- \+ *lemma* dfinsupp.sum_add_hom_comm
- \+/\- *lemma* dfinsupp.sum_add_hom_comp_single
- \+ *lemma* dfinsupp.sum_add_hom_single_add_hom
- \+ *lemma* dfinsupp.sum_add_hom_zero
- \+/\- *lemma* dfinsupp.sum_sub_index



## [2021-02-04 18:03:54](https://github.com/leanprover-community/mathlib/commit/6d153f1)
feat(data/equiv/basic): perm.subtype_congr ([#5875](https://github.com/leanprover-community/mathlib/pull/5875))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.perm.subtype_congr.apply
- \+ *lemma* equiv.perm.subtype_congr.left_apply
- \+ *lemma* equiv.perm.subtype_congr.left_apply_subtype
- \+ *lemma* equiv.perm.subtype_congr.refl
- \+ *lemma* equiv.perm.subtype_congr.right_apply
- \+ *lemma* equiv.perm.subtype_congr.right_apply_subtype
- \+ *lemma* equiv.perm.subtype_congr.symm
- \+ *lemma* equiv.perm.subtype_congr.trans
- \+ *def* equiv.perm.subtype_congr

Modified src/group_theory/perm/basic.lean
- \+ *def* equiv.perm.subtype_congr_hom
- \+ *lemma* equiv.perm.subtype_congr_hom_injective

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.sign_subtype_congr

Modified src/group_theory/perm/subgroup.lean
- \+ *lemma* equiv.perm.subtype_congr_hom.card_range



## [2021-02-04 18:03:51](https://github.com/leanprover-community/mathlib/commit/bbf9774)
feat(data/fintype/basic): inv of inj on deceq ([#5872](https://github.com/leanprover-community/mathlib/pull/5872))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* function.embedding.inv_fun_restrict
- \+ *def* function.embedding.inv_of_mem_range
- \+ *lemma* function.embedding.inv_of_mem_range_surjective
- \+ *lemma* function.embedding.left_inv_of_inv_of_mem_range
- \+ *lemma* function.embedding.right_inv_of_inv_of_mem_range
- \+ *lemma* function.injective.inv_fun_restrict
- \+ *def* function.injective.inv_of_mem_range
- \+ *lemma* function.injective.inv_of_mem_range_surjective
- \+ *lemma* function.injective.left_inv_of_inv_of_mem_range
- \+ *lemma* function.injective.right_inv_of_inv_of_mem_range

Modified src/data/set/basic.lean
- \+ *lemma* function.injective.exists_unique_of_mem_range
- \+ *lemma* function.injective.mem_range_iff_exists_unique

Modified src/logic/function/basic.lean




## [2021-02-04 18:03:49](https://github.com/leanprover-community/mathlib/commit/9993a50)
feat(tactic/norm_swap): simplify numeral swaps ([#5637](https://github.com/leanprover-community/mathlib/pull/5637))
Explicitly applied swap equalities over `nat` can be proven to be true using `dec_trivial`. However, if occurring in the middle of a larger expression, a separate specialized hypothesis would be necessary to reduce them down. This is an initial attempt at a `norm_num` extension which seeks to reduce down expressions of the `swap X Y Z` form. Handles `nat`, `int`, `rat`, and `fin` swaps.
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/norm_num.lean


Added src/tactic/norm_swap.lean


Added test/norm_swap.lean




## [2021-02-04 14:28:12](https://github.com/leanprover-community/mathlib/commit/4d26028)
chore(order/basic): add a lemma expanding `le` on pi types ([#6023](https://github.com/leanprover-community/mathlib/pull/6023))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* pi.lt_def
- \+ *lemma* update_le_update_iff



## [2021-02-04 14:28:10](https://github.com/leanprover-community/mathlib/commit/e61db52)
chore(linear_algebra/quadratic_form): add polar_self, polar_zero_left, and polar_zero_right simp lemmas ([#6003](https://github.com/leanprover-community/mathlib/pull/6003))
This also reorders the existing lemmas to keep the polar ones separate from the non-polar ones
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.polar_self
- \+ *lemma* quadratic_form.polar_zero_left
- \+ *lemma* quadratic_form.polar_zero_right



## [2021-02-04 12:05:37](https://github.com/leanprover-community/mathlib/commit/1a2eb0b)
feat(analysis/special_functions/trigonometric): add mistakenly omitted lemma ([#6036](https://github.com/leanprover-community/mathlib/pull/6036))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.arcsin_eq_arctan



## [2021-02-04 12:05:35](https://github.com/leanprover-community/mathlib/commit/16be8e3)
refactor(analysis/normed_space): simpler proof of `norm_sub_pow_two` ([#6035](https://github.com/leanprover-community/mathlib/pull/6035))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean




## [2021-02-04 12:05:34](https://github.com/leanprover-community/mathlib/commit/894ff7a)
doc(number_theory/{pell, sum_of_four_squares}): docstring to pell  ([#6030](https://github.com/leanprover-community/mathlib/pull/6030))
and additionally fixing the syntax for the docstring of sum_of_four_squares.
#### Estimated changes
Modified docs/references.bib


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean




## [2021-02-04 12:05:32](https://github.com/leanprover-community/mathlib/commit/0aed8b1)
refactor(analysis/asymptotics): make definitions immediately irreducible ([#6021](https://github.com/leanprover-community/mathlib/pull/6021))
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* asymptotics.is_O.add
- \+ *lemma* asymptotics.is_O.bound
- \+ *lemma* asymptotics.is_O.is_O_with
- \+/\- *lemma* asymptotics.is_O_top
- \+/\- *theorem* asymptotics.is_O_with.is_O
- \- *lemma* asymptotics.is_O_with.of_bound
- \+/\- *theorem* asymptotics.is_O_with_bot
- \+/\- *lemma* asymptotics.is_O_with_top
- \+/\- *theorem* asymptotics.is_O_zero
- \+/\- *theorem* asymptotics.is_o.is_O_with
- \+/\- *theorem* asymptotics.is_o_bot



## [2021-02-04 12:05:30](https://github.com/leanprover-community/mathlib/commit/97781b9)
chore(linear_algebra/std_basis): move std_basis to a new file ([#6020](https://github.com/leanprover-community/mathlib/pull/6020))
linear_algebra/basic is _very_ long. This reduces its length by about 5%.
Authorship of the std_basis stuff seems to come almost entirely from 10a586b1d82098af32e13c8d8448696022132f17.
None of the lemmas have changed, and the variables are kept in exactly the same order as before.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \- *lemma* linear_map.disjoint_std_basis_std_basis
- \- *lemma* linear_map.infi_ker_proj_le_supr_range_std_basis
- \- *lemma* linear_map.ker_std_basis
- \- *lemma* linear_map.proj_comp_std_basis
- \- *lemma* linear_map.proj_std_basis_ne
- \- *lemma* linear_map.proj_std_basis_same
- \- *def* linear_map.std_basis
- \- *lemma* linear_map.std_basis_apply
- \- *lemma* linear_map.std_basis_eq_single
- \- *lemma* linear_map.std_basis_ne
- \- *lemma* linear_map.std_basis_same
- \- *lemma* linear_map.supr_range_std_basis
- \- *lemma* linear_map.supr_range_std_basis_eq_infi_ker_proj
- \- *lemma* linear_map.supr_range_std_basis_le_infi_ker_proj

Modified src/linear_algebra/basis.lean


Added src/linear_algebra/std_basis.lean
- \+ *lemma* linear_map.disjoint_std_basis_std_basis
- \+ *lemma* linear_map.infi_ker_proj_le_supr_range_std_basis
- \+ *lemma* linear_map.ker_std_basis
- \+ *lemma* linear_map.proj_comp_std_basis
- \+ *lemma* linear_map.proj_std_basis_ne
- \+ *lemma* linear_map.proj_std_basis_same
- \+ *def* linear_map.std_basis
- \+ *lemma* linear_map.std_basis_apply
- \+ *lemma* linear_map.std_basis_eq_single
- \+ *lemma* linear_map.std_basis_ne
- \+ *lemma* linear_map.std_basis_same
- \+ *lemma* linear_map.supr_range_std_basis
- \+ *lemma* linear_map.supr_range_std_basis_eq_infi_ker_proj
- \+ *lemma* linear_map.supr_range_std_basis_le_infi_ker_proj



## [2021-02-04 07:48:51](https://github.com/leanprover-community/mathlib/commit/6df1501)
feat(algebra/ordered_ring): weaken hypotheses for one_le_two ([#6034](https://github.com/leanprover-community/mathlib/pull/6034))
Adjust `one_le_two` to not require nontriviality.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* one_le_two



## [2021-02-04 03:30:09](https://github.com/leanprover-community/mathlib/commit/3309490)
chore(scripts): update nolints.txt ([#6032](https://github.com/leanprover-community/mathlib/pull/6032))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-04 03:30:08](https://github.com/leanprover-community/mathlib/commit/7812afa)
feat(data/list/basic): drop_eq_nil_of_le ([#6029](https://github.com/leanprover-community/mathlib/pull/6029))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.drop_eq_nil_of_le
- \+/\- *theorem* list.drop_nil



## [2021-02-04 03:30:06](https://github.com/leanprover-community/mathlib/commit/cbd67cf)
feat(order/(complete_lattice, compactly_generated)): independent sets in a complete lattice ([#5971](https://github.com/leanprover-community/mathlib/pull/5971))
Defines `complete_lattice.independent`
Shows that this notion of independence is finitary in compactly generated lattices
#### Estimated changes
Modified src/order/compactly_generated.lean
- \+ *lemma* Sup_compact_le_eq
- \+ *theorem* complete_lattice.independent_iff_finite
- \+ *theorem* inf_Sup_eq_of_directed_on
- \+ *theorem* inf_Sup_eq_supr_inf_sup_finset
- \+ *theorem* le_iff_compact_le_imp

Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+ *theorem* complete_lattice.independent.mono
- \+ *def* complete_lattice.independent
- \+ *lemma* sup_Inf_le_infi_sup
- \+ *lemma* supr_inf_le_inf_Sup



## [2021-02-04 03:30:04](https://github.com/leanprover-community/mathlib/commit/5f328b6)
feat(linear_algebra/free_algebra): Show that free_monoid forms a basis over free_algebra ([#5868](https://github.com/leanprover-community/mathlib/pull/5868))
#### Estimated changes
Added src/linear_algebra/free_algebra.lean
- \+ *lemma* free_algebra.dim_eq
- \+ *lemma* free_algebra.is_basis_free_monoid



## [2021-02-03 23:29:31](https://github.com/leanprover-community/mathlib/commit/36b3510)
feat(data/nat/factorial): additional inequalities ([#6026](https://github.com/leanprover-community/mathlib/pull/6026))
I added two lemmas about factorials.  I use them in the Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).
#### Estimated changes
Modified src/data/nat/factorial.lean
- \+ *lemma* nat.add_factorial_lt_factorial_add'
- \+ *lemma* nat.add_factorial_lt_factorial_add
- \+ *lemma* nat.lt_factorial_self



## [2021-02-03 17:44:44](https://github.com/leanprover-community/mathlib/commit/360fa07)
feat(data/real/sqrt): added some missing sqrt lemmas ([#5933](https://github.com/leanprover-community/mathlib/pull/5933))
I noticed that some facts about `sqrt` and `abs` are missing, so I am adding them.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \- *lemma* abs_sq_eq
- \+ *theorem* abs_sqr
- \+ *theorem* sqr_abs
- \+ *theorem* sqr_le_sqr'
- \+ *theorem* sqr_le_sqr
- \+ *theorem* sqr_lt_sqr'
- \+ *theorem* sqr_lt_sqr

Modified src/algebra/ordered_group.lean
- \+ *lemma* abs_le'
- \- *theorem* abs_le'
- \+ *lemma* abs_le
- \- *theorem* abs_le
- \+/\- *lemma* abs_lt
- \+ *lemma* le_abs
- \+ *lemma* le_of_abs_le
- \+/\- *lemma* lt_abs
- \+ *lemma* lt_of_abs_lt
- \+ *lemma* neg_le_of_abs_le
- \+ *lemma* neg_lt_of_abs_lt

Modified src/data/real/sqrt.lean
- \+ *theorem* real.abs_le_sqrt
- \+ *theorem* real.div_sqrt
- \+ *theorem* real.le_sqrt'
- \- *lemma* real.le_sqrt'
- \+ *theorem* real.le_sqrt
- \- *lemma* real.le_sqrt
- \+ *theorem* real.le_sqrt_of_sqr_le
- \- *lemma* real.le_sqrt_of_sqr_le
- \+ *theorem* real.lt_sqrt
- \+ *theorem* real.lt_sqrt_of_sqr_lt
- \+ *theorem* real.neg_sqrt_le_of_sqr_le
- \+ *theorem* real.neg_sqrt_lt_of_sqr_lt
- \+ *theorem* real.sqr_le
- \+ *theorem* real.sqr_lt
- \+ *theorem* real.sqrt_le_iff
- \- *lemma* real.sqrt_le_iff
- \+ *theorem* real.sqrt_le_left
- \- *lemma* real.sqrt_le_left
- \+ *theorem* real.sqrt_le_sqrt
- \- *lemma* real.sqrt_le_sqrt
- \+ *theorem* real.sqrt_ne_zero'
- \+ *theorem* real.sqrt_ne_zero

Modified src/geometry/manifold/instances/sphere.lean




## [2021-02-03 16:02:37](https://github.com/leanprover-community/mathlib/commit/bb15b1c)
chore(analysis/calculus): rename `has_f?deriv_at_unique` to `has_f?deriv_at.unique` ([#6019](https://github.com/leanprover-community/mathlib/pull/6019))
Also make some lemmas `protected`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \- *lemma* continuous_linear_map.deriv
- \- *lemma* continuous_linear_map.deriv_within
- \- *lemma* continuous_linear_map.has_deriv_at
- \- *lemma* continuous_linear_map.has_deriv_at_filter
- \- *lemma* continuous_linear_map.has_deriv_within_at
- \- *lemma* continuous_linear_map.has_strict_deriv_at
- \+ *theorem* has_deriv_at.unique
- \- *theorem* has_deriv_at_unique
- \- *lemma* has_fpower_series_at.deriv
- \- *lemma* has_fpower_series_at.has_deriv_at
- \- *lemma* has_fpower_series_at.has_strict_deriv_at
- \- *lemma* linear_map.deriv
- \- *lemma* linear_map.deriv_within
- \- *lemma* linear_map.has_deriv_at
- \- *lemma* linear_map.has_deriv_at_filter
- \- *lemma* linear_map.has_deriv_within_at
- \- *lemma* linear_map.has_strict_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_fderiv_at.unique
- \- *theorem* has_fderiv_at_unique

Modified src/analysis/calculus/times_cont_diff.lean




## [2021-02-03 12:26:39](https://github.com/leanprover-community/mathlib/commit/235a7c4)
doc(lint/simp): typesetting issues in simp_nf library note ([#6018](https://github.com/leanprover-community/mathlib/pull/6018))
#### Estimated changes
Modified src/tactic/lint/simp.lean




## [2021-02-03 12:26:38](https://github.com/leanprover-community/mathlib/commit/9a0d2b2)
chore(data/nat/parity): rename type variable ([#6016](https://github.com/leanprover-community/mathlib/pull/6016))
#### Estimated changes
Modified src/data/nat/parity.lean
- \+/\- *theorem* nat.even.add_even
- \+/\- *theorem* nat.even.add_odd
- \+/\- *theorem* nat.even.sub_even
- \+/\- *theorem* nat.even.sub_odd
- \+/\- *theorem* nat.even_add'
- \+/\- *theorem* nat.even_add
- \+/\- *lemma* nat.even_div
- \+/\- *theorem* nat.even_iff
- \+/\- *lemma* nat.even_iff_not_odd
- \+/\- *theorem* nat.even_mul
- \+/\- *theorem* nat.even_pow
- \+/\- *theorem* nat.even_sub'
- \+/\- *theorem* nat.even_sub
- \+/\- *theorem* nat.even_succ
- \+/\- *theorem* nat.mod_two_ne_one
- \+/\- *theorem* nat.mod_two_ne_zero
- \+/\- *theorem* nat.neg_one_pow_eq_one_iff_even
- \+/\- *theorem* nat.neg_one_pow_of_even
- \+/\- *theorem* nat.neg_one_pow_of_odd
- \+/\- *theorem* nat.neg_one_pow_two
- \+/\- *lemma* nat.not_even_iff
- \+/\- *lemma* nat.not_odd_iff
- \+/\- *theorem* nat.odd.add_even
- \+/\- *theorem* nat.odd.add_odd
- \+/\- *theorem* nat.odd.sub_even
- \+/\- *theorem* nat.odd.sub_odd
- \+/\- *theorem* nat.odd_add'
- \+/\- *theorem* nat.odd_add
- \+/\- *lemma* nat.odd_gt_zero
- \+/\- *theorem* nat.odd_iff
- \+/\- *lemma* nat.odd_iff_not_even
- \+/\- *theorem* nat.odd_sub'
- \+/\- *theorem* nat.odd_sub
- \+/\- *lemma* nat.two_not_dvd_two_mul_sub_one



## [2021-02-03 12:26:36](https://github.com/leanprover-community/mathlib/commit/fa8df59)
feat(algebra/polynomial/big_operators): add degree_prod lemma ([#5979](https://github.com/leanprover-community/mathlib/pull/5979))
This PR adds a degree_prod lemma next to the nat_degree_prod lemma. This version of the lemma works for the interpretation of 'degree' which says the degree of the zero polynomial is \bot
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.degree_prod



## [2021-02-03 12:26:34](https://github.com/leanprover-community/mathlib/commit/5a9ca8d)
feat(linear_algebra/sesquilinear_form): add composition between sesquilinear forms and linear maps ([#5729](https://github.com/leanprover-community/mathlib/pull/5729))
Add composition lemmas for sesquilinear forms, that is, given a sesquilinear form and linear maps, a new sesquilinear form is induced by applying the arguments with the linear map.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.comp_injective

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *def* sesq_form.comp
- \+ *lemma* sesq_form.comp_apply
- \+ *lemma* sesq_form.comp_comp
- \+ *lemma* sesq_form.comp_injective
- \+ *def* sesq_form.comp_left
- \+ *lemma* sesq_form.comp_left_apply
- \+ *lemma* sesq_form.comp_left_comp_right
- \+ *def* sesq_form.comp_right
- \+ *lemma* sesq_form.comp_right_apply
- \+ *lemma* sesq_form.comp_right_comp_left



## [2021-02-03 09:45:38](https://github.com/leanprover-community/mathlib/commit/e1ca806)
doc(algebra/{archimedean, char_zero}): provide docstrings ([#6010](https://github.com/leanprover-community/mathlib/pull/6010))
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/char_zero.lean




## [2021-02-03 04:39:23](https://github.com/leanprover-community/mathlib/commit/e66ad5f)
chore(scripts): update nolints.txt ([#6014](https://github.com/leanprover-community/mathlib/pull/6014))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-03 04:39:21](https://github.com/leanprover-community/mathlib/commit/79ca6e2)
feat(order/compactly_generated): Show that the sublattice below a compact element is coatomic ([#5942](https://github.com/leanprover-community/mathlib/pull/5942))
Show that the sublattice below a compact element is coatomic. Introduce a lemma stating that any set lying strictly below a compact element has Sup strictly below that element.
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
#### Estimated changes
Modified src/order/compactly_generated.lean
- \+ *theorem* complete_lattice.Iic_coatomic_of_compact_element
- \+ *lemma* complete_lattice.is_compact_element.directed_Sup_lt_of_lt



## [2021-02-03 01:05:51](https://github.com/leanprover-community/mathlib/commit/fcad25f)
feat(algebra/ring): add mk_mul_self_of_two_ne_zero ([#5862](https://github.com/leanprover-community/mathlib/pull/5862))
Which allows us to make a ring homomorphism from an additive hom which maps squares to squares assuming a couple of  things, this is especially useful in ordered fields where it allows us to think only of positive elements.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* add_monoid_hom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero
- \+ *lemma* add_monoid_hom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero
- \+ *def* add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero



## [2021-02-02 23:11:29](https://github.com/leanprover-community/mathlib/commit/2153dc3)
feat(data/fintype/sort): add `fin_sum_equiv_of_finset` ([#6008](https://github.com/leanprover-community/mathlib/pull/6008))
#### Estimated changes
Modified src/data/fintype/sort.lean
- \+ *def* fin_sum_equiv_of_finset
- \+ *lemma* fin_sum_equiv_of_finset_inl
- \+ *lemma* fin_sum_equiv_of_finset_inr



## [2021-02-02 21:38:31](https://github.com/leanprover-community/mathlib/commit/1b1ad15)
refactor(measure_theory/*): rename `is_(null_)?measurable` to `(null_)?measurable_set` ([#6001](https://github.com/leanprover-community/mathlib/pull/6001))
Search & replace:
* `is_null_measurable` → `null_measurable`;
* `is_measurable` → `measurable_set'`;
* `measurable_set_set` → `measurable_set`;
* `measurable_set_spanning_sets` → `measurable_spanning_sets`;
* `measurable_set_superset` → `measurable_superset`.
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean
- \- *theorem* is_measurable_set_of_differentiable_at
- \- *theorem* is_measurable_set_of_differentiable_at_of_is_complete
- \+ *theorem* measurable_set_of_differentiable_at
- \+ *theorem* measurable_set_of_differentiable_at_of_is_complete

Modified src/analysis/special_functions/pow.lean


Modified src/measure_theory/ae_measurable_sequence.lean
- \- *lemma* ae_seq.ae_seq_set_is_measurable
- \+ *lemma* ae_seq.ae_seq_set_measurable_set

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean
- \- *lemma* is_Gδ.is_measurable
- \+ *lemma* is_Gδ.measurable_set
- \- *lemma* is_closed.is_measurable
- \+ *lemma* is_closed.measurable_set
- \- *lemma* is_compact.is_measurable
- \+ *lemma* is_compact.measurable_set
- \- *lemma* is_measurable.nhds_within_is_measurably_generated
- \- *lemma* is_measurable_Icc
- \- *lemma* is_measurable_Ici
- \- *lemma* is_measurable_Ico
- \- *lemma* is_measurable_Iic
- \- *lemma* is_measurable_Iio
- \- *lemma* is_measurable_Ioc
- \- *lemma* is_measurable_Ioi
- \- *lemma* is_measurable_Ioo
- \- *lemma* is_measurable_ball
- \- *lemma* is_measurable_closed_ball
- \- *lemma* is_measurable_closure
- \- *lemma* is_measurable_eball
- \- *lemma* is_measurable_interior
- \- *lemma* is_measurable_interval
- \- *lemma* is_measurable_le'
- \- *lemma* is_measurable_le
- \- *lemma* is_measurable_lt'
- \- *lemma* is_measurable_lt
- \- *lemma* is_measurable_set_of_continuous_at
- \- *lemma* is_open.is_measurable
- \+ *lemma* is_open.measurable_set
- \+/\- *lemma* measurable_of_Ici
- \+/\- *lemma* measurable_of_Iic
- \+/\- *lemma* measurable_of_Iio
- \+/\- *lemma* measurable_of_Ioi
- \+/\- *lemma* measurable_of_is_closed
- \+/\- *lemma* measurable_of_is_open
- \+ *lemma* measurable_set.nhds_within_is_measurably_generated
- \+ *lemma* measurable_set_Icc
- \+ *lemma* measurable_set_Ici
- \+ *lemma* measurable_set_Ico
- \+ *lemma* measurable_set_Iic
- \+ *lemma* measurable_set_Iio
- \+ *lemma* measurable_set_Ioc
- \+ *lemma* measurable_set_Ioi
- \+ *lemma* measurable_set_Ioo
- \+ *lemma* measurable_set_ball
- \+ *lemma* measurable_set_closed_ball
- \+ *lemma* measurable_set_closure
- \+ *lemma* measurable_set_eball
- \+ *lemma* measurable_set_interior
- \+ *lemma* measurable_set_interval
- \+ *lemma* measurable_set_le'
- \+ *lemma* measurable_set_le
- \+ *lemma* measurable_set_lt'
- \+ *lemma* measurable_set_lt
- \+ *lemma* measurable_set_of_continuous_at

Modified src/measure_theory/content.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/giry_monad.lean
- \+/\- *lemma* measure_theory.measure.measurable_coe

Modified src/measure_theory/group.lean
- \+/\- *lemma* measure_theory.measure.inv_apply

Modified src/measure_theory/haar_measure.lean
- \+/\- *lemma* measure_theory.measure.haar_measure_apply

Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.lintegral_Union
- \+/\- *lemma* measure_theory.lintegral_indicator
- \+/\- *theorem* measure_theory.simple_func.coe_piecewise
- \+/\- *theorem* measure_theory.simple_func.coe_restrict
- \- *lemma* measure_theory.simple_func.is_measurable_cut
- \- *lemma* measure_theory.simple_func.is_measurable_fiber
- \- *theorem* measure_theory.simple_func.is_measurable_preimage
- \+ *lemma* measure_theory.simple_func.measurable_set_cut
- \+ *lemma* measure_theory.simple_func.measurable_set_fiber
- \+ *theorem* measure_theory.simple_func.measurable_set_preimage
- \+/\- *lemma* measure_theory.simple_func.mem_restrict_range
- \+/\- *def* measure_theory.simple_func.piecewise
- \+/\- *theorem* measure_theory.simple_func.piecewise_apply
- \+/\- *lemma* measure_theory.simple_func.piecewise_compl
- \+/\- *lemma* measure_theory.simple_func.piecewise_empty
- \+/\- *lemma* measure_theory.simple_func.piecewise_univ
- \+/\- *theorem* measure_theory.simple_func.restrict_apply
- \+/\- *lemma* measure_theory.simple_func.restrict_const_lintegral
- \+/\- *lemma* measure_theory.simple_func.restrict_lintegral
- \+/\- *theorem* measure_theory.simple_func.restrict_preimage
- \+/\- *theorem* measure_theory.simple_func.restrict_preimage_singleton
- \+/\- *lemma* measure_theory.with_density_apply

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \- *lemma* finset.is_measurable_bInter
- \- *lemma* finset.is_measurable_bUnion
- \+ *lemma* finset.measurable_set_bInter
- \+ *lemma* finset.measurable_set_bUnion
- \- *lemma* is_countably_spanning_is_measurable
- \+ *lemma* is_countably_spanning_measurable_set
- \- *lemma* is_measurable.Inter
- \- *lemma* is_measurable.Inter_Prop
- \- *lemma* is_measurable.Inter_fintype
- \- *lemma* is_measurable.Union
- \- *lemma* is_measurable.Union_Prop
- \- *lemma* is_measurable.Union_fintype
- \- *lemma* is_measurable.bInter
- \- *lemma* is_measurable.bUnion
- \- *lemma* is_measurable.bUnion_decode2
- \- *lemma* is_measurable.compl
- \- *lemma* is_measurable.compl_iff
- \- *lemma* is_measurable.congr
- \- *lemma* is_measurable.const
- \- *lemma* is_measurable.diff
- \- *lemma* is_measurable.disjointed
- \- *lemma* is_measurable.empty
- \- *lemma* is_measurable.inl_image
- \- *lemma* is_measurable.insert
- \- *lemma* is_measurable.inter
- \- *lemma* is_measurable.of_compl
- \- *lemma* is_measurable.pi
- \- *lemma* is_measurable.pi_fintype
- \- *lemma* is_measurable.pi_univ
- \- *lemma* is_measurable.prod
- \- *lemma* is_measurable.sInter
- \- *lemma* is_measurable.sUnion
- \- *lemma* is_measurable.subtype_image
- \- *lemma* is_measurable.tprod
- \- *lemma* is_measurable.union
- \- *lemma* is_measurable.univ
- \- *def* is_measurable
- \- *lemma* is_measurable_eq
- \- *lemma* is_measurable_inr_image
- \- *lemma* is_measurable_insert
- \- *lemma* is_measurable_pi
- \- *lemma* is_measurable_pi_of_nonempty
- \- *lemma* is_measurable_prod
- \- *lemma* is_measurable_prod_of_nonempty
- \- *lemma* is_measurable_range_inl
- \- *lemma* is_measurable_range_inr
- \- *lemma* is_measurable_swap_iff
- \+/\- *lemma* measurable_find_greatest
- \+ *lemma* measurable_set.Inter
- \+ *lemma* measurable_set.Inter_Prop
- \+ *lemma* measurable_set.Inter_fintype
- \+ *lemma* measurable_set.Union
- \+ *lemma* measurable_set.Union_Prop
- \+ *lemma* measurable_set.Union_fintype
- \+ *lemma* measurable_set.bInter
- \+ *lemma* measurable_set.bUnion
- \+ *lemma* measurable_set.bUnion_decode2
- \+ *lemma* measurable_set.compl
- \+ *lemma* measurable_set.compl_iff
- \+ *lemma* measurable_set.congr
- \+ *lemma* measurable_set.const
- \+ *lemma* measurable_set.diff
- \+ *lemma* measurable_set.disjointed
- \+ *lemma* measurable_set.empty
- \+ *lemma* measurable_set.inl_image
- \+ *lemma* measurable_set.insert
- \+ *lemma* measurable_set.inter
- \+ *lemma* measurable_set.of_compl
- \+ *lemma* measurable_set.pi
- \+ *lemma* measurable_set.pi_fintype
- \+ *lemma* measurable_set.pi_univ
- \+ *lemma* measurable_set.prod
- \+ *lemma* measurable_set.sInter
- \+ *lemma* measurable_set.sUnion
- \+ *lemma* measurable_set.subtype_image
- \+ *lemma* measurable_set.tprod
- \+ *lemma* measurable_set.union
- \+ *lemma* measurable_set.univ
- \+ *def* measurable_set
- \+ *lemma* measurable_set_eq
- \+ *lemma* measurable_set_inr_image
- \+ *lemma* measurable_set_insert
- \+ *lemma* measurable_set_pi
- \+ *lemma* measurable_set_pi_of_nonempty
- \+ *lemma* measurable_set_prod
- \+ *lemma* measurable_set_prod_of_nonempty
- \+ *lemma* measurable_set_range_inl
- \+ *lemma* measurable_set_range_inr
- \+ *lemma* measurable_set_swap_iff
- \- *lemma* measurable_space.generate_from_is_measurable
- \+ *lemma* measurable_space.generate_from_measurable_set
- \+/\- *def* measurable_space.gi_generate_from
- \- *theorem* measurable_space.is_measurable_Inf
- \- *theorem* measurable_space.is_measurable_Sup
- \- *lemma* measurable_space.is_measurable_bot_iff
- \- *lemma* measurable_space.is_measurable_generate_from
- \- *theorem* measurable_space.is_measurable_inf
- \- *theorem* measurable_space.is_measurable_infi
- \- *theorem* measurable_space.is_measurable_sup
- \- *theorem* measurable_space.is_measurable_supr
- \- *theorem* measurable_space.is_measurable_top
- \- *lemma* measurable_space.is_pi_system_is_measurable
- \+ *lemma* measurable_space.is_pi_system_measurable_set
- \+ *theorem* measurable_space.measurable_set_Inf
- \+ *theorem* measurable_space.measurable_set_Sup
- \+ *lemma* measurable_space.measurable_set_bot_iff
- \+ *lemma* measurable_space.measurable_set_generate_from
- \+ *theorem* measurable_space.measurable_set_inf
- \+ *theorem* measurable_space.measurable_set_infi
- \+ *theorem* measurable_space.measurable_set_sup
- \+ *theorem* measurable_space.measurable_set_supr
- \+ *theorem* measurable_space.measurable_set_top
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_to_nat
- \+/\- *lemma* nonempty_measurable_superset
- \- *lemma* set.finite.is_measurable
- \- *lemma* set.finite.is_measurable_bInter
- \- *lemma* set.finite.is_measurable_bUnion
- \- *lemma* set.finite.is_measurable_sInter
- \- *lemma* set.finite.is_measurable_sUnion
- \+ *lemma* set.finite.measurable_set
- \+ *lemma* set.finite.measurable_set_bInter
- \+ *lemma* set.finite.measurable_set_bUnion
- \+ *lemma* set.finite.measurable_set_sInter
- \+ *lemma* set.finite.measurable_set_sUnion
- \- *lemma* subsingleton.is_measurable
- \+ *lemma* subsingleton.measurable_set

Modified src/measure_theory/measure_space.lean
- \- *lemma* ae_measurable.is_null_measurable
- \+ *lemma* ae_measurable.null_measurable_set
- \- *theorem* is_measurable.diff_null
- \- *theorem* is_measurable.is_null_measurable
- \- *theorem* is_null_measurable.Union_nat
- \- *theorem* is_null_measurable.compl
- \- *theorem* is_null_measurable.diff_null
- \- *theorem* is_null_measurable.union_null
- \- *def* is_null_measurable
- \- *theorem* is_null_measurable_iff
- \- *theorem* is_null_measurable_iff_ae
- \- *theorem* is_null_measurable_iff_sandwich
- \- *theorem* is_null_measurable_measure_eq
- \- *theorem* is_null_measurable_of_complete
- \+ *theorem* measurable_set.diff_null
- \+ *theorem* measurable_set.null_measurable_set
- \+/\- *lemma* measure_theory.ae_dirac_iff
- \+/\- *lemma* measure_theory.ae_eventually_not_mem
- \+/\- *lemma* measure_theory.ae_map_iff
- \+/\- *lemma* measure_theory.ae_restrict_eq
- \+/\- *lemma* measure_theory.ae_restrict_iff'
- \+/\- *lemma* measure_theory.ae_restrict_iff
- \- *lemma* measure_theory.exists_is_measurable_superset
- \- *lemma* measure_theory.exists_is_measurable_superset_iff_measure_eq_zero
- \- *lemma* measure_theory.exists_is_measurable_superset_of_null
- \+ *lemma* measure_theory.exists_measurable_superset
- \+ *lemma* measure_theory.exists_measurable_superset_iff_measure_eq_zero
- \+ *lemma* measure_theory.exists_measurable_superset_of_null
- \- *lemma* measure_theory.is_measurable_spanning_sets
- \- *lemma* measure_theory.is_measurable_to_measurable
- \+ *lemma* measure_theory.measurable_set_to_measurable
- \+ *lemma* measure_theory.measurable_spanning_sets
- \+/\- *lemma* measure_theory.measure.Inf_apply
- \+/\- *lemma* measure_theory.measure.Inf_caratheodory
- \+/\- *lemma* measure_theory.measure.absolutely_continuous.mk
- \+/\- *lemma* measure_theory.measure.count_apply
- \+/\- *lemma* measure_theory.measure.dirac_apply'
- \+/\- *lemma* measure_theory.measure.ext
- \+/\- *lemma* measure_theory.measure.ext_iff
- \+/\- *theorem* measure_theory.measure.le_iff
- \+/\- *theorem* measure_theory.measure.lt_iff
- \+/\- *theorem* measure_theory.measure.map_apply
- \+/\- *lemma* measure_theory.measure.map_comap_subtype_coe
- \+/\- *def* measure_theory.measure.of_measurable
- \+/\- *lemma* measure_theory.measure.of_measurable_apply
- \+/\- *lemma* measure_theory.measure.restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* measure_theory.measure.restrict_Union_congr
- \+/\- *lemma* measure_theory.measure.restrict_add_restrict_compl
- \+/\- *lemma* measure_theory.measure.restrict_apply
- \+/\- *lemma* measure_theory.measure.restrict_apply_eq_zero'
- \+/\- *lemma* measure_theory.measure.restrict_apply_eq_zero
- \+/\- *lemma* measure_theory.measure.restrict_compl_add_restrict
- \+/\- *lemma* measure_theory.measure.restrict_congr_meas
- \+/\- *lemma* measure_theory.measure.restrict_congr_mono
- \+/\- *lemma* measure_theory.measure.restrict_map
- \+/\- *lemma* measure_theory.measure.restrict_restrict
- \+/\- *lemma* measure_theory.measure.restrict_sUnion_congr
- \+/\- *lemma* measure_theory.measure.restrict_sum
- \+/\- *lemma* measure_theory.measure.restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* measure_theory.measure.restrict_union
- \+/\- *lemma* measure_theory.measure.restrict_union_add_inter
- \+/\- *lemma* measure_theory.measure.restrict_union_apply
- \+/\- *lemma* measure_theory.measure.restrict_union_congr
- \+/\- *lemma* measure_theory.measure.sub_apply
- \+/\- *lemma* measure_theory.measure.sum_apply
- \+/\- *lemma* measure_theory.measure.supr_restrict_spanning_sets
- \+/\- *lemma* measure_theory.measure_Union_eq_supr
- \+/\- *lemma* measure_theory.measure_compl
- \+/\- *lemma* measure_theory.measure_diff
- \+/\- *lemma* measure_theory.measure_eq_extend
- \+/\- *lemma* measure_theory.measure_eq_infi
- \+/\- *lemma* measure_theory.measure_eq_inter_diff
- \+/\- *lemma* measure_theory.measure_limsup_eq_zero
- \+/\- *lemma* measure_theory.measure_union
- \+/\- *lemma* measure_theory.measure_union_add_inter
- \+/\- *lemma* measure_theory.mem_ae_dirac_iff
- \+/\- *lemma* measure_theory.mem_ae_map_iff
- \+/\- *lemma* measure_theory.self_mem_ae_restrict
- \+/\- *lemma* measure_theory.sum_measure_le_measure_univ
- \+/\- *lemma* measure_theory.tendsto_measure_Union
- \+/\- *lemma* measure_theory.tsum_measure_le_measure_univ
- \- *theorem* null_is_null_measurable
- \+ *theorem* null_measurable_set.Union_nat
- \+ *theorem* null_measurable_set.compl
- \+ *theorem* null_measurable_set.diff_null
- \+ *theorem* null_measurable_set.union_null
- \+ *def* null_measurable_set
- \+ *theorem* null_measurable_set_iff
- \+ *theorem* null_measurable_set_iff_ae
- \+ *theorem* null_measurable_set_iff_sandwich
- \+ *theorem* null_measurable_set_measure_eq
- \+ *theorem* null_measurable_set_of_complete
- \+ *theorem* null_null_measurable_set
- \- *lemma* restrict_apply_of_is_null_measurable
- \+ *lemma* restrict_apply_of_null_measurable_set

Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* measure_theory.extend_mono
- \+/\- *lemma* measure_theory.induced_outer_measure_eq
- \+/\- *lemma* measure_theory.induced_outer_measure_eq_extend
- \- *lemma* measure_theory.outer_measure.exists_is_measurable_superset_eq_trim
- \- *lemma* measure_theory.outer_measure.exists_is_measurable_superset_of_trim_eq_zero
- \+ *lemma* measure_theory.outer_measure.exists_measurable_superset_eq_trim
- \+ *lemma* measure_theory.outer_measure.exists_measurable_superset_of_trim_eq_zero
- \+/\- *theorem* measure_theory.outer_measure.le_trim_iff
- \+/\- *lemma* measure_theory.outer_measure.restrict_trim
- \+/\- *theorem* measure_theory.outer_measure.trim_eq
- \+/\- *theorem* measure_theory.outer_measure.trim_eq_infi'
- \+/\- *theorem* measure_theory.outer_measure.trim_eq_infi

Modified src/measure_theory/pi.lean
- \+/\- *lemma* measure_theory.measure.pi_pi

Modified src/measure_theory/prod.lean
- \- *lemma* is_measurable_integrable
- \+ *lemma* measurable_set_integrable
- \+/\- *lemma* measure_theory.measure.ae_measure_lt_top
- \+/\- *lemma* measure_theory.measure.prod_apply
- \+/\- *lemma* measure_theory.measure.prod_apply_symm
- \+/\- *lemma* measure_theory.measure.prod_restrict

Modified src/measure_theory/prod_group.lean
- \+/\- *lemma* measure_theory.measurable_measure_mul_right
- \+/\- *lemma* measure_theory.measure_inv_null
- \+/\- *lemma* measure_theory.measure_mul_right_ne_zero
- \+/\- *lemma* measure_theory.measure_mul_right_null

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* indicator_ae_eq_restrict
- \+/\- *lemma* indicator_ae_eq_restrict_compl
- \+/\- *lemma* measure_theory.ae_measurable_indicator_iff
- \+/\- *lemma* measure_theory.integrable_indicator_iff
- \+/\- *lemma* measure_theory.integrable_on.indicator
- \+/\- *lemma* measure_theory.integral_add_compl
- \+/\- *lemma* measure_theory.integral_indicator
- \+/\- *lemma* measure_theory.integral_indicator_const
- \+/\- *lemma* measure_theory.integral_union
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const'
- \+/\- *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae''
- \+/\- *lemma* measure_theory.set_integral_congr
- \+/\- *lemma* measure_theory.set_integral_congr_ae
- \+/\- *lemma* piecewise_ae_eq_restrict
- \+/\- *lemma* piecewise_ae_eq_restrict_compl

Modified src/measure_theory/simple_func_dense.lean


Modified src/probability_theory/independence.lean




## [2021-02-02 18:29:12](https://github.com/leanprover-community/mathlib/commit/2b2edc9)
chore(analysis/normed_space/basic): use explicit arg `𝕜'` in lemmas about `normed_algebra` ([#6009](https://github.com/leanprover-community/mathlib/pull/6009))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* normed_algebra.norm_one

Modified src/analysis/normed_space/operator_norm.lean




## [2021-02-02 18:29:10](https://github.com/leanprover-community/mathlib/commit/4e78654)
fix(tactic/delta_instance): improve naming of instances with multiple arguments ([#6007](https://github.com/leanprover-community/mathlib/pull/6007))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/tactic/delta_instance.lean


Modified test/delta_instance.lean




## [2021-02-02 18:29:08](https://github.com/leanprover-community/mathlib/commit/fe9c021)
feat(geometry/manifold/instances): sphere is a smooth manifold ([#5607](https://github.com/leanprover-community/mathlib/pull/5607))
Put a smooth manifold structure on the sphere, and provide tools for constructing smooth maps to and from the sphere.
#### Estimated changes
Modified docs/overview.yaml


Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* findim_orthogonal_span_singleton

Modified src/geometry/manifold/instances/sphere.lean
- \+/\- *def* stereographic'
- \+/\- *lemma* stereographic'_source
- \+/\- *lemma* stereographic'_target
- \+ *lemma* times_cont_mdiff.cod_restrict_sphere
- \+ *lemma* times_cont_mdiff_coe_sphere
- \+ *lemma* times_cont_mdiff_neg_sphere

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.finite_dimensional_of_findim
- \+ *lemma* finite_dimensional.finite_dimensional_of_findim_eq_succ

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.coe_to_homeomorph
- \+ *lemma* continuous_linear_equiv.symm_to_homeomorph



## [2021-02-02 14:44:00](https://github.com/leanprover-community/mathlib/commit/dbb5ca1)
refactor(group_theory/perm): move perm.subtype_perm to basic ([#6005](https://github.com/leanprover-community/mathlib/pull/6005))
Both `perm.subtype_perm` and `perm.of_subtype` can be moved up the import hierarchy out of `group_theory/perm/sign` since they do not rely on any finiteness assumption.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.mem_iff_of_subtype_apply_mem
- \+ *def* equiv.perm.of_subtype
- \+ *lemma* equiv.perm.of_subtype_apply_of_not_mem
- \+ *lemma* equiv.perm.of_subtype_subtype_perm
- \+ *def* equiv.perm.subtype_perm
- \+ *lemma* equiv.perm.subtype_perm_of_subtype
- \+ *lemma* equiv.perm.subtype_perm_one

Modified src/group_theory/perm/sign.lean
- \- *lemma* equiv.perm.mem_iff_of_subtype_apply_mem
- \- *def* equiv.perm.of_subtype
- \- *lemma* equiv.perm.of_subtype_apply_of_not_mem
- \- *lemma* equiv.perm.of_subtype_subtype_perm
- \- *def* equiv.perm.subtype_perm
- \- *lemma* equiv.perm.subtype_perm_of_subtype
- \- *lemma* equiv.perm.subtype_perm_one



## [2021-02-02 14:43:58](https://github.com/leanprover-community/mathlib/commit/9b3dc41)
feat(nat/basic): more nat.find lemmas ([#6002](https://github.com/leanprover-community/mathlib/pull/6002))
also merge two sections on nat.find
#### Estimated changes
Modified src/data/nat/basic.lean
- \+/\- *lemma* nat.find_eq_iff
- \+/\- *lemma* nat.find_eq_zero
- \+/\- *theorem* nat.find_le
- \+ *lemma* nat.find_le_iff
- \+ *lemma* nat.find_lt_iff
- \+/\- *lemma* nat.find_pos
- \+ *lemma* nat.le_find_iff
- \+ *lemma* nat.lt_find_iff



## [2021-02-02 14:43:56](https://github.com/leanprover-community/mathlib/commit/6633a70)
feat(analysis/normed_space/inner_product): remove unnecessary `nonneg_im` field ([#5999](https://github.com/leanprover-community/mathlib/pull/5999))
The `nonneg_im` property already follows from `conj_sym`.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* inner_conj_sym
- \+/\- *lemma* inner_product_space.of_core.inner_self_im_zero
- \+/\- *lemma* inner_product_space.of_core.inner_self_nonneg_im
- \+/\- *lemma* inner_self_im_zero
- \+/\- *lemma* inner_self_nonneg_im

Modified src/analysis/quaternion.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.conj_I
- \+ *theorem* is_R_or_C.im_eq_conj_sub



## [2021-02-02 14:43:54](https://github.com/leanprover-community/mathlib/commit/508c265)
feat(logic/function/basic): add bijective.iff_exists_unique and projections ([#5995](https://github.com/leanprover-community/mathlib/pull/5995))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.bijective.exists_unique
- \+ *lemma* function.bijective_iff_exists_unique



## [2021-02-02 14:43:51](https://github.com/leanprover-community/mathlib/commit/3732fb9)
refactor(data/polynomial/eval): change eval_smul lemmas to use * instead of 2nd smul ([#5991](https://github.com/leanprover-community/mathlib/pull/5991))
#### Estimated changes
Modified src/data/polynomial/eval.lean


Modified src/ring_theory/localization.lean




## [2021-02-02 14:43:49](https://github.com/leanprover-community/mathlib/commit/ff05d3a)
feat(algebra/group_power/lemmas): sign of even/odd powers ([#5990](https://github.com/leanprover-community/mathlib/pull/5990))
Added theorems about the sign of even and odd natural powers.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_mul_sub_le_pow
- \+/\- *theorem* pow_bit1_neg_iff
- \+/\- *theorem* pow_bit1_nonneg_iff
- \+/\- *theorem* pow_bit1_nonpos_iff
- \+/\- *theorem* pow_bit1_pos_iff
- \+ *theorem* pow_even_nonneg
- \+ *theorem* pow_even_pos
- \+ *theorem* pow_odd_neg
- \+ *theorem* pow_odd_nonneg
- \+ *theorem* pow_odd_nonpos
- \+ *theorem* pow_odd_pos



## [2021-02-02 14:43:46](https://github.com/leanprover-community/mathlib/commit/25c34e0)
refactor(linear_algebra,algebra/algebra): generalize `linear_map.smul_right` ([#5967](https://github.com/leanprover-community/mathlib/pull/5967))
* the new `linear_map.smul_right` generalizes both the old
  `linear_map.smul_right` and the old `linear_map.smul_algebra_right`;
* add `smul_comm_class` for `linear_map`s.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* linear_map.smul_algebra_right
- \- *theorem* linear_map.smul_algebra_right_apply

Modified src/analysis/normed_space/operator_norm.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_map.smul_right
- \+/\- *theorem* linear_map.smul_right_apply

Modified src/linear_algebra/finsupp.lean




## [2021-02-02 14:43:44](https://github.com/leanprover-community/mathlib/commit/fc7daa3)
feat(data/nat/parity): addition/subtraction of even/odd nats ([#5934](https://github.com/leanprover-community/mathlib/pull/5934))
 Added various theorems pertaining to the addition and subtraction of even and odd natural numbers.
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean


Modified src/data/nat/parity.lean
- \- *theorem* nat.even.add
- \+ *theorem* nat.even.add_even
- \+ *theorem* nat.even.add_odd
- \- *theorem* nat.even.sub
- \+ *theorem* nat.even.sub_even
- \+ *theorem* nat.even.sub_odd
- \+ *theorem* nat.even_add'
- \+/\- *lemma* nat.even_div
- \+ *theorem* nat.even_sub'
- \+/\- *theorem* nat.neg_one_pow_eq_one_iff_even
- \+ *theorem* nat.odd.add_even
- \+ *theorem* nat.odd.add_odd
- \+ *theorem* nat.odd.sub_even
- \+ *theorem* nat.odd.sub_odd
- \+ *theorem* nat.odd_add'
- \+ *theorem* nat.odd_add
- \+ *theorem* nat.odd_sub'
- \+ *theorem* nat.odd_sub
- \+/\- *lemma* nat.two_not_dvd_two_mul_add_one
- \+/\- *lemma* nat.two_not_dvd_two_mul_sub_one



## [2021-02-02 14:43:42](https://github.com/leanprover-community/mathlib/commit/893ce8b)
feat(tactic/norm_fin): tactic for normalizing `fin n` expressions ([#5820](https://github.com/leanprover-community/mathlib/pull/5820))
This is based on [#5791](https://github.com/leanprover-community/mathlib/pull/5791), with a new implementation using the
`normalize_fin` function.
#### Estimated changes
Added src/tactic/norm_fin.lean
- \+ *theorem* tactic.norm_fin.normalize_fin.add
- \+ *theorem* tactic.norm_fin.normalize_fin.bit0
- \+ *theorem* tactic.norm_fin.normalize_fin.bit1
- \+ *theorem* tactic.norm_fin.normalize_fin.cast
- \+ *theorem* tactic.norm_fin.normalize_fin.eq
- \+ *theorem* tactic.norm_fin.normalize_fin.le
- \+ *theorem* tactic.norm_fin.normalize_fin.lt
- \+ *theorem* tactic.norm_fin.normalize_fin.mul
- \+ *theorem* tactic.norm_fin.normalize_fin.one
- \+ *theorem* tactic.norm_fin.normalize_fin.reduce
- \+ *theorem* tactic.norm_fin.normalize_fin.zero
- \+ *def* tactic.norm_fin.normalize_fin
- \+ *theorem* tactic.norm_fin.normalize_fin_iff
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.add_nat
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.cast
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.cast_add
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.cast_le
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.cast_lt
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.cast_succ
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.coe
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.lt
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.mk
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.nat_add
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.of
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.reduce
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.succ
- \+ *theorem* tactic.norm_fin.normalize_fin_lt.zero
- \+ *def* tactic.norm_fin.normalize_fin_lt

Modified src/tactic/norm_num.lean


Added test/norm_fin.lean




## [2021-02-02 11:46:18](https://github.com/leanprover-community/mathlib/commit/75a7ce9)
refactor(*): rename subtype_congr to subtype_equiv ([#6004](https://github.com/leanprover-community/mathlib/pull/6004))
This definition is closely related to `perm.subtype_perm`, so renaming will bring them closer in use. Also releavnt is [#5875](https://github.com/leanprover-community/mathlib/pull/5875) which defines a separate `perm.subtype_congr`.
#### Estimated changes
Modified src/category_theory/adjunction/lifting.lean


Modified src/category_theory/monad/monadicity.lean


Modified src/data/equiv/basic.lean
- \- *def* equiv.subtype_congr
- \- *lemma* equiv.subtype_congr_apply
- \- *def* equiv.subtype_congr_prop
- \- *def* equiv.subtype_congr_right
- \- *lemma* equiv.subtype_congr_symm_apply
- \+ *def* equiv.subtype_equiv
- \+ *lemma* equiv.subtype_equiv_apply
- \+ *def* equiv.subtype_equiv_prop
- \+ *def* equiv.subtype_equiv_right
- \+ *lemma* equiv.subtype_equiv_symm_apply

Modified src/data/fintype/card.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/ring_theory/polynomial/symmetric.lean




## [2021-02-02 07:14:15](https://github.com/leanprover-community/mathlib/commit/fec8ee4)
chore(topology/bases): rewrite 2 proofs using tactic mode ([#5996](https://github.com/leanprover-community/mathlib/pull/5996))
IMHO they're more readable that way
#### Estimated changes
Modified src/topology/bases.lean
- \+/\- *lemma* topological_space.first_countable_topology.tendsto_subseq



## [2021-02-02 04:14:06](https://github.com/leanprover-community/mathlib/commit/0c26bb0)
feat(data/finset/basic): add lemmas about bUnion and images of functions on finsets ([#5887](https://github.com/leanprover-community/mathlib/pull/5887))
Add lemmas about bUnion and images of functions on finsets. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's marriage theorem.
Coauthors: @kmill @b-mehta
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_bUnion
- \+ *lemma* finset.nonempty.image_iff



## [2021-02-02 02:06:24](https://github.com/leanprover-community/mathlib/commit/2c62c0b)
chore(scripts): update nolints.txt ([#6006](https://github.com/leanprover-community/mathlib/pull/6006))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-02-02 02:06:21](https://github.com/leanprover-community/mathlib/commit/a301ef7)
feat(order/compactly_generated, ring_theory/noetherian): the lattice of submodules is compactly generated ([#5944](https://github.com/leanprover-community/mathlib/pull/5944))
Redefines `is_compactly_generated` as a class
Provides an instance of `is_compactly_generated` on `submodule R M`
#### Estimated changes
Modified src/order/compactly_generated.lean
- \- *def* complete_lattice.is_compactly_generated

Modified src/ring_theory/noetherian.lean




## [2021-02-01 22:55:52](https://github.com/leanprover-community/mathlib/commit/4d3b26f)
feat(combinatorics/simple_graph/basic): add decidable instance for adjacency of complement ([#6000](https://github.com/leanprover-community/mathlib/pull/6000))
Add instance that states that, if the adjacency relation for a simple graph is decidable, the adjacency relation for its complement is also decidable.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-02-01 22:55:50](https://github.com/leanprover-community/mathlib/commit/1706e55)
feat(data/list/basic) add update_nth_comm ([#5989](https://github.com/leanprover-community/mathlib/pull/5989))
As requested on Zulip at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_nth_comm/near/223007424
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.update_nth_comm
- \+ *lemma* list.update_nth_nil
- \+ *lemma* list.update_nth_succ



## [2021-02-01 22:55:48](https://github.com/leanprover-community/mathlib/commit/9b779f4)
refactor(ring_theory/ideal/*, ring_theory/jacobson): use `comm_semiring` instead of `comm_ring` for ideals ([#5954](https://github.com/leanprover-community/mathlib/pull/5954))
This is the second pass at refactoring the definition of `ideal`.  I have changed a `comm_ring` assumption to a `comm_semiring` assumption on many of the lemmas in `ring_theory/ideal/basic`.  Most implied changes were very simple, with the usual exception of `jacobson`.
I also moved out of `jacobson` the lemmas that were left-over from the previous refactor in this sequence.
Besides changing such assumptions on other files, many of the lemmas in `ring_theory/ideal/basic` still using `comm_ring` and without explicit subtractions, deal with quotients.
#### Estimated changes
Modified src/algebra/ring_quot.lean


Modified src/ring_theory/ideal/basic.lean
- \+/\- *theorem* coe_subset_nonunits
- \+/\- *lemma* exists_max_ideal_of_mem_nonunits
- \- *lemma* ideal.exists_mem_ne_zero_iff_ne_bot
- \- *lemma* ideal.exists_mem_ne_zero_of_ne_bot
- \+/\- *lemma* ideal.maximal_of_no_maximal
- \- *lemma* ideal.quotient.lift_comp_mk
- \- *lemma* ideal.quotient.lift_surjective

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/over.lean
- \+ *lemma* ideal.exists_nonzero_mem_of_ne_bot
- \+ *lemma* ideal.injective_quotient_le_comap_map
- \+ *lemma* ideal.quotient_mk_maps_eq

Modified src/ring_theory/jacobson.lean
- \- *lemma* ideal.injective_quotient_le_comap_map
- \- *lemma* ideal.quotient_mk_maps_eq

Modified src/ring_theory/jacobson_ideal.lean




## [2021-02-01 19:15:19](https://github.com/leanprover-community/mathlib/commit/829c1a5)
chore(group_theory/coset): rename lemmas to follow naming conventions ([#5998](https://github.com/leanprover-community/mathlib/pull/5998))
Rename `normal_of_eq_cosets` and `eq_cosets_of_normal` to follow naming conventions. Conclusion should be stated before the `of`.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+/\- *theorem* eq_cosets_of_normal
- \+/\- *theorem* normal_of_eq_cosets



## [2021-02-01 19:15:16](https://github.com/leanprover-community/mathlib/commit/684f4f5)
chore(*): split some long lines ([#5997](https://github.com/leanprover-community/mathlib/pull/5997))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* nat.cast_le_pow_sub_div_sub
- \+/\- *lemma* semiconj_by.cast_nat_mul_right

Modified src/algebra/group_with_zero/power.lean
- \+/\- *theorem* commute.fpow_fpow_self

Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/analysis/convex/extrema.lean


Modified src/category_theory/adjunction/limits.lean
- \+/\- *def* category_theory.adjunction.functoriality_counit'
- \+/\- *def* category_theory.adjunction.functoriality_counit
- \+/\- *def* category_theory.adjunction.functoriality_unit'

Modified src/category_theory/limits/shapes/zero.lean


Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.cast_dvd

Modified src/data/qpf/multivariate/constructions/cofix.lean
- \+/\- *lemma* mvqpf.cofix.ext_mk

Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/deprecated/subgroup.lean
- \+/\- *lemma* is_add_subgroup.gsmul_mem
- \+/\- *lemma* is_subgroup.coe_gpow

Modified src/field_theory/algebraic_closure.lean
- \+/\- *lemma* is_alg_closed.degree_eq_one_of_irreducible

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *theorem* findim_eq_zero
- \+/\- *theorem* finite_dimensional.span_of_finite

Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/number_theory/pell.lean
- \+/\- *theorem* pell.eq_of_xn_modeq
- \+/\- *theorem* pell.eq_of_xn_modeq_le

Modified src/order/omega_complete_partial_order.lean
- \+/\- *lemma* omega_complete_partial_order.continuous_hom.comp_assoc

Modified src/tactic/interval_cases.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/squeeze.lean




## [2021-02-01 19:15:14](https://github.com/leanprover-community/mathlib/commit/acabfa6)
fix(archive/imo/*): fixed syntax for docstrings ([#5994](https://github.com/leanprover-community/mathlib/pull/5994))
#### Estimated changes
Modified archive/imo/imo1959_q1.lean


Modified archive/imo/imo1972_b2.lean


Modified archive/imo/imo1988_q6.lean




## [2021-02-01 19:15:11](https://github.com/leanprover-community/mathlib/commit/a84a80d)
fix(topology/algebra/infinite_sum): add missing decidable arguments ([#5993](https://github.com/leanprover-community/mathlib/pull/5993))
These decidable instances were being inferred as classical instances, which meant these lemmas would not match other instances.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum_ite_eq
- \+/\- *lemma* tsum_ite_eq



## [2021-02-01 19:15:09](https://github.com/leanprover-community/mathlib/commit/64283ce)
feat(list/{zip,indexes}): Add `zip_with` and `map_with_index` lemmas ([#5974](https://github.com/leanprover-community/mathlib/pull/5974))
All proofs are due to @pechersky.
#### Estimated changes
Modified src/data/list/indexes.lean
- \+ *lemma* list.map_with_index_core_eq
- \+ *lemma* list.map_with_index_eq_enum_map

Modified src/data/list/zip.lean
- \+ *lemma* list.map_uncurry_zip_eq_zip_with
- \+ *lemma* list.zip_with_map
- \+ *lemma* list.zip_with_map_left
- \+ *lemma* list.zip_with_map_right



## [2021-02-01 15:46:19](https://github.com/leanprover-community/mathlib/commit/cbd88d6)
chore(*) add mod_add_div' and div_add_mod' and golf proofs ([#5962](https://github.com/leanprover-community/mathlib/pull/5962))
Resolves issue [#1534](https://github.com/leanprover-community/mathlib/pull/1534).
Name of nat.mod_add_div shouldn't be changed as this is in core. Better name suggestions for mod_add_div' and div_add_mod' welcome.
#### Estimated changes
Modified archive/imo/imo1962_q1.lean


Modified archive/imo/imo1964_q1.lean


Modified src/algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.div_add_mod'
- \+ *lemma* euclidean_domain.mod_add_div'

Modified src/data/int/basic.lean
- \+ *lemma* int.div_add_mod'
- \+ *lemma* int.mod_add_div'

Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_add_mod'
- \+ *lemma* nat.div_add_mod
- \+ *lemma* nat.mod_add_div'

Modified src/data/nat/fib.lean


Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.div_add_mod'
- \+ *lemma* pnat.mod_add_div'

Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/set_theory/ordinal_arithmetic.lean




## [2021-02-01 12:31:43](https://github.com/leanprover-community/mathlib/commit/866e4fd)
chore(linear_algebra/quadratic_form): add two missing simp lemmas about subtraction ([#5985](https://github.com/leanprover-community/mathlib/pull/5985))
This also reorders the instance definitions to keep the lemmas about subtraction near the ones about negation, and uses the `add := (+)` pattern to make definitions unfold more nicely, even though it probably doesn't make any difference.
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.coe_fn_sub
- \+ *lemma* quadratic_form.sub_apply



## [2021-02-01 12:31:41](https://github.com/leanprover-community/mathlib/commit/f2c84aa)
doc(algebra/category/*): provide two short docstrings and shorten lines ([#5984](https://github.com/leanprover-community/mathlib/pull/5984))
also fixed one minor typo.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Module/monoidal.lean
- \+/\- *def* Module.monoidal_category.tensor_hom

Modified src/algebra/category/Mon/colimits.lean
- \+/\- *lemma* Mon.colimits.quot_mul



## [2021-02-01 12:31:39](https://github.com/leanprover-community/mathlib/commit/b1ab310)
chore(analysis/normed_space/inner_product): add {bilin,sesq}_form_of_inner_apply simp lemmas ([#5982](https://github.com/leanprover-community/mathlib/pull/5982))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean




## [2021-02-01 12:31:37](https://github.com/leanprover-community/mathlib/commit/398e7ad)
feat(data/pnat/basic) pnat can_lift instances ([#5977](https://github.com/leanprover-community/mathlib/pull/5977))
Add can_lift instances for pnat from nat and int
#### Estimated changes
Modified src/data/pnat/basic.lean




## [2021-02-01 12:31:35](https://github.com/leanprover-community/mathlib/commit/89c7963)
feat(category_theory/nat_iso): dsimp lemma for natural isomorphisms ([#5973](https://github.com/leanprover-community/mathlib/pull/5973))
a little simp lemma
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.is_iso_inv_app



## [2021-02-01 12:31:33](https://github.com/leanprover-community/mathlib/commit/8273588)
chore(category_theory/monad): generate simp lemmas ([#5972](https://github.com/leanprover-community/mathlib/pull/5972))
Adds a missing simps command to generate simp lemmas for the functor.
#### Estimated changes
Modified src/category_theory/monad/products.lean




## [2021-02-01 12:31:31](https://github.com/leanprover-community/mathlib/commit/3f9b035)
chore(category_theory/adjunction): reflective lemmas ([#5968](https://github.com/leanprover-community/mathlib/pull/5968))
Improves the docstring and changes the name to be more appropriate (the lemma has nothing to do with essential images).
#### Estimated changes
Modified src/category_theory/adjunction/reflective.lean




## [2021-02-01 09:10:42](https://github.com/leanprover-community/mathlib/commit/c5e0d10)
chore(*): split some long lines ([#5988](https://github.com/leanprover-community/mathlib/pull/5988))
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified docs/tutorial/category_theory/intro.lean


Modified src/algebra/algebra/subalgebra.lean
- \+/\- *theorem* algebra.bijective_algebra_map_iff

Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/divisibility.lean


Modified src/algebra/group/prod.lean
- \+/\- *lemma* mul_equiv.coe_prod_comm

Modified src/algebra/quandle.lean


Modified src/algebra/ring_quot.lean
- \+/\- *lemma* ring_quot.lift_alg_hom_mk_alg_hom_apply
- \+/\- *theorem* ring_quot.rel.neg

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/category_theory/hom_functor.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/creates.lean
- \+/\- *def* category_theory.lift_colimit

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.ι_map
- \+/\- *lemma* category_theory.limits.colimit.ι_post
- \+/\- *lemma* category_theory.limits.colimit.ι_pre
- \+/\- *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_hom_desc
- \+/\- *lemma* category_theory.limits.has_colimit.of_cocones_iso
- \+/\- *lemma* category_theory.limits.has_limit.of_cones_iso
- \+/\- *def* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso
- \+/\- *lemma* category_theory.limits.limit.pre_π

Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* category_theory.limits.coprod.associator_naturality
- \+/\- *lemma* category_theory.limits.coprod.desc_comp
- \+/\- *lemma* category_theory.limits.coprod.map_codiag
- \+/\- *lemma* category_theory.limits.coprod.map_inl_inr_codiag
- \+/\- *lemma* category_theory.limits.coprod.map_swap
- \+/\- *lemma* category_theory.limits.prod.diag_map_fst_snd
- \+/\- *lemma* category_theory.limits.prod.lift_fst_comp_snd_comp
- \+/\- *lemma* category_theory.limits.prod.lift_map
- \+/\- *lemma* category_theory.limits.prod.map_swap

Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* category_theory.limits.biproduct.is_colimit
- \+/\- *lemma* category_theory.limits.has_binary_biproduct.mk

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+/\- *lemma* category_theory.limits.has_finite_wide_pullbacks_of_has_finite_limits
- \+/\- *lemma* category_theory.limits.has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/images.lean
- \+/\- *def* category_theory.limits.image.iso_strong_epi_mono
- \+/\- *lemma* category_theory.limits.image.iso_strong_epi_mono_hom_comp_ι
- \+/\- *lemma* category_theory.limits.image.iso_strong_epi_mono_inv_comp_mono

Modified src/category_theory/limits/shapes/kernel_pair.lean
- \+/\- *def* category_theory.is_kernel_pair.cancel_right
- \+/\- *def* category_theory.is_kernel_pair.cancel_right_of_mono

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+/\- *def* category_theory.regular_of_is_pullback_fst_of_regular
- \+/\- *def* category_theory.regular_of_is_pullback_snd_of_regular

Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monoidal/of_chosen_finite_products.lean


Modified src/category_theory/skeletal.lean


Modified src/data/lazy_list/basic.lean
- \+/\- *lemma* lazy_list.append_assoc
- \+/\- *lemma* lazy_list.mem_cons
- \+/\- *def* lazy_list.pmap

Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.mul_vec_cons

Modified src/data/multiset/fold.lean
- \+/\- *theorem* multiset.fold_add
- \+/\- *theorem* multiset.fold_eq_foldl
- \+/\- *theorem* multiset.fold_eq_foldr
- \+/\- *theorem* multiset.fold_erase_dup_idem

Modified src/data/mv_polynomial/equiv.lean
- \+/\- *def* mv_polynomial.ring_equiv_congr

Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.generate_eq_generate_inter

Modified src/order/filter/basic.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/tactic/linarith/datatypes.lean


Modified src/topology/algebra/multilinear.lean
- \+ *def* continuous_multilinear_map.apply_add_hom

Modified src/topology/category/Top/adjunctions.lean


Modified src/topology/list.lean


Modified src/topology/local_extr.lean
- \+/\- *lemma* is_local_extr_on.comp_continuous_on
- \+/\- *lemma* is_local_extr_on.is_local_extr
- \+/\- *lemma* is_local_max_on.comp_continuous_on
- \+/\- *lemma* is_local_min_on.comp_continuous_on

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/lipschitz.lean


Modified test/finish2.lean


Modified test/finish4.lean




## [2021-02-01 03:11:45](https://github.com/leanprover-community/mathlib/commit/f060e09)
chore(*): golf some proofs ([#5983](https://github.com/leanprover-community/mathlib/pull/5983))
API changes:
* new lemmas `finset.card_filter_le`, `finset.compl_filter`, `finset.card_lt_univ_of_not_mem`, `fintype.card_le_of_embedding`, `fintype.card_lt_of_injective_not_surjective`;
* rename `finset.card_le_of_inj_on` → `finset.le_card_of_inj_on_range`;
* rename `card_lt_of_injective_of_not_mem` to `fintype.card_lt_of_injective_of_not_mem`;
* generalize `card_units_lt` to a `monoid_with_zero`.
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean


Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_filter_le
- \- *lemma* finset.card_le_of_inj_on
- \+ *lemma* finset.le_card_of_inj_on_range

Modified src/data/fintype/basic.lean
- \- *lemma* card_lt_card_of_injective_of_not_mem
- \+ *lemma* finset.card_lt_univ_of_not_mem
- \+ *lemma* finset.compl_filter
- \+ *lemma* fintype.card_le_of_embedding
- \+ *lemma* fintype.card_lt_of_injective_not_surjective
- \+ *lemma* fintype.card_lt_of_injective_of_not_mem

Modified src/data/nat/totient.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* set.range_inclusion

Modified src/data/set/finite.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycles.lean


Modified src/measure_theory/haar_measure.lean


Modified src/ring_theory/fintype.lean
- \+/\- *lemma* card_units_lt

Modified src/set_theory/cardinal.lean




## [2021-02-01 01:50:40](https://github.com/leanprover-community/mathlib/commit/609f5f7)
chore(scripts): update nolints.txt ([#5986](https://github.com/leanprover-community/mathlib/pull/5986))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt


