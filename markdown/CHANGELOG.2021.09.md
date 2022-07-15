## [2021-09-30 22:39:03](https://github.com/leanprover-community/mathlib/commit/a24b496)
feat(analysis/normed_space/add_torsor_bases): add lemma `exists_subset_affine_independent_span_eq_top_of_open` ([#9418](https://github.com/leanprover-community/mathlib/pull/9418))
Also some supporting lemmas about affine span, affine independence.
#### Estimated changes
Added src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* exists_subset_affine_independent_span_eq_top_of_open

Modified src/data/finset/basic.lean
- \+ *lemma* finset.sdiff_singleton_not_mem_eq_self

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* affine_span_eq_affine_span_line_map_units
- \+ *lemma* finset.weighted_vsub_of_point_eq_of_weights_eq
- \+/\- *lemma* finset.weighted_vsub_of_point_insert
- \+ *lemma* mem_affine_span_iff_eq_weighted_vsub_of_point_vadd

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent.units_line_map



## [2021-09-30 22:39:00](https://github.com/leanprover-community/mathlib/commit/931cd6d)
feat(data/set/equitable): Equitable functions ([#8509](https://github.com/leanprover-community/mathlib/pull/8509))
Equitable functions are functions whose maximum is at most one more than their minimum. Equivalently, in an additive successor order (`a < b ↔ a +1 ≤ b`), this means that the function takes only values `a` and `a + 1` for some `a`.
From Szemerédi's regularity lemma. Co-authored by @b-mehta
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_and_le_add_one_iff

Added src/data/set/equitable.lean
- \+ *lemma* finset.equitable_on_iff
- \+ *lemma* finset.equitable_on_iff_le_le_add_one
- \+ *def* set.equitable_on
- \+ *lemma* set.equitable_on_empty
- \+ *lemma* set.equitable_on_iff_exists_eq_eq_add_one
- \+ *lemma* set.equitable_on_iff_exists_image_subset_Icc
- \+ *lemma* set.equitable_on_iff_exists_le_le_add_one



## [2021-09-30 20:25:20](https://github.com/leanprover-community/mathlib/commit/a52a54b)
chore(analysis/convex/basic): instance cleanup ([#9466](https://github.com/leanprover-community/mathlib/pull/9466))
Some lemmas were about `f : whatever → 𝕜`. They are now about `f : whatever → β` + a scalar instance between `𝕜` and `β`.
Some `add_comm_monoid` assumptions are actually promotable to `add_comm_group` directly thanks to [`module.add_comm_monoid_to_add_comm_group`](https://leanprover-community.github.io/mathlib_docs/algebra/module/basic.html#module.add_comm_monoid_to_add_comm_group). [Related Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Convexity.20refactor/near/255268131).
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.add
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex.combo_self
- \+/\- *lemma* convex.linear_image
- \+/\- *def* convex
- \+/\- *lemma* convex_Icc
- \+/\- *lemma* convex_Ici
- \+/\- *lemma* convex_Ico
- \+/\- *lemma* convex_Iic
- \+/\- *lemma* convex_Iio
- \+/\- *lemma* convex_Ioc
- \+/\- *lemma* convex_Ioi
- \+/\- *lemma* convex_Ioo
- \+/\- *lemma* convex_halfspace_ge
- \+/\- *lemma* convex_halfspace_gt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_lt
- \+/\- *lemma* convex_hyperplane
- \+/\- *lemma* convex_interval
- \+/\- *lemma* convex_segment
- \+/\- *lemma* convex_std_simplex
- \+/\- *lemma* directed.convex_Union
- \+/\- *lemma* directed_on.convex_sUnion
- \+/\- *lemma* ite_eq_mem_std_simplex
- \+/\- *def* open_segment
- \+/\- *def* segment
- \+/\- *lemma* set.ord_connected.convex
- \+/\- *lemma* set.ord_connected.convex_of_chain
- \+/\- *def* std_simplex

Modified src/analysis/convex/combination.lean
- \+/\- *lemma* mem_Icc_of_mem_std_simplex

Modified src/analysis/convex/topology.lean
- \+/\- *lemma* bounded_std_simplex
- \+/\- *lemma* compact_std_simplex
- \+/\- *lemma* is_closed_std_simplex



## [2021-09-30 20:25:18](https://github.com/leanprover-community/mathlib/commit/97036e7)
feat(measure_theory/constructions/pi): volume on `α × α` as a map of volume on `fin 2 → α` ([#9432](https://github.com/leanprover-community/mathlib/pull/9432))
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *def* fin_two_arrow_equiv
- \+ *def* order_iso.fin_two_arrow_iso
- \+ *def* order_iso.pi_fin_two_iso
- \+ *def* pi_fin_two_equiv
- \+ *def* prod_equiv_pi_fin_two

Modified src/data/fin.lean
- \+ *lemma* fin.exists_fin_one
- \+ *lemma* fin.exists_fin_two
- \+ *lemma* fin.forall_fin_one
- \+ *lemma* fin.forall_fin_two
- \+ *lemma* fin.insert_nth_apply_above
- \+ *lemma* fin.insert_nth_apply_below
- \+ *lemma* fin.zero_lt_one

Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.vec_cons_const
- \+ *lemma* matrix.vec_single_eq_const

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.integral_fin_two_arrow'
- \+ *lemma* measure_theory.integral_fin_two_arrow
- \+ *lemma* measure_theory.integral_fin_two_arrow_pi'
- \+ *lemma* measure_theory.integral_fin_two_arrow_pi
- \+ *lemma* measure_theory.measure.prod_eq_map_fin_two_arrow
- \+ *lemma* measure_theory.measure.prod_eq_map_fin_two_arrow_same
- \+ *lemma* measure_theory.measure.{u}
- \+ *lemma* measure_theory.set_integral_fin_two_arrow'
- \+ *lemma* measure_theory.set_integral_fin_two_arrow
- \+ *lemma* measure_theory.set_integral_fin_two_arrow_pi'
- \+ *lemma* measure_theory.set_integral_fin_two_arrow_pi

Modified src/measure_theory/measurable_space.lean
- \+ *def* measurable_equiv.fin_two_arrow
- \+ *def* measurable_equiv.pi_fin_two



## [2021-09-30 20:25:17](https://github.com/leanprover-community/mathlib/commit/64bcb38)
feat(order/succ_pred): define successor orders ([#9397](https://github.com/leanprover-community/mathlib/pull/9397))
A successor order is an order in which every (non maximal) element has a least greater element. A predecessor order is an order in which every (non minimal) element has a greatest smaller element. Typical examples are `ℕ`, `ℕ+`, `ℤ`, `fin n`, `ordinal`. Anytime you want to turn `a < b + 1` into `a ≤ b` or `a < b` into `a + 1 ≤ b`, you want a `succ_order`.
#### Estimated changes
Added src/order/succ_pred.lean
- \+ *lemma* pred_order.le_pred_iff
- \+ *lemma* pred_order.le_pred_iff_eq_bot
- \+ *lemma* pred_order.le_pred_iff_lt_or_eq
- \+ *lemma* pred_order.pred_bot
- \+ *lemma* pred_order.pred_eq_pred_iff
- \+ *lemma* pred_order.pred_eq_supr
- \+ *lemma* pred_order.pred_injective
- \+ *lemma* pred_order.pred_le_le_iff
- \+ *lemma* pred_order.pred_le_pred
- \+ *lemma* pred_order.pred_le_pred_iff
- \+ *lemma* pred_order.pred_lt
- \+ *lemma* pred_order.pred_lt_iff
- \+ *lemma* pred_order.pred_lt_iff_lt_or_eq
- \+ *lemma* pred_order.pred_lt_iff_ne_bot
- \+ *lemma* pred_order.pred_lt_of_not_minimal
- \+ *lemma* pred_order.pred_lt_pred_iff
- \+ *lemma* pred_order.pred_lt_top
- \+ *lemma* pred_order.pred_mono
- \+ *lemma* pred_order.pred_ne_pred_iff
- \+ *lemma* pred_order.pred_ne_top
- \+ *def* pred_order.pred_order_of_le_pred_iff
- \+ *def* pred_order.pred_order_of_le_pred_iff_of_pred_le_pred
- \+ *lemma* pred_order.pred_strict_mono
- \+ *lemma* succ_order.bot_lt_succ
- \+ *lemma* succ_order.le_le_succ_iff
- \+ *lemma* succ_order.le_succ_iff_lt_or_eq
- \+ *lemma* succ_order.lt_succ
- \+ *lemma* succ_order.lt_succ_iff
- \+ *lemma* succ_order.lt_succ_iff_lt_or_eq
- \+ *lemma* succ_order.lt_succ_iff_ne_top
- \+ *lemma* succ_order.lt_succ_of_not_maximal
- \+ *lemma* succ_order.succ_eq_infi
- \+ *lemma* succ_order.succ_eq_succ_iff
- \+ *lemma* succ_order.succ_injective
- \+ *lemma* succ_order.succ_le_iff
- \+ *lemma* succ_order.succ_le_iff_eq_top
- \+ *lemma* succ_order.succ_le_succ
- \+ *lemma* succ_order.succ_le_succ_iff
- \+ *lemma* succ_order.succ_lt_succ_iff
- \+ *lemma* succ_order.succ_mono
- \+ *lemma* succ_order.succ_ne_bot
- \+ *lemma* succ_order.succ_ne_succ_iff
- \+ *def* succ_order.succ_order_of_succ_le_iff
- \+ *def* succ_order.succ_order_of_succ_le_iff_of_le_lt_succ
- \+ *lemma* succ_order.succ_strict_mono
- \+ *lemma* succ_order.succ_top



## [2021-09-30 20:25:16](https://github.com/leanprover-community/mathlib/commit/f7795d1)
feat(monoid_algebra/grading): `add_monoid_algebra`s permit an internal grading ([#8927](https://github.com/leanprover-community/mathlib/pull/8927))
#### Estimated changes
Added src/algebra/monoid_algebra/grading.lean
- \+ *def* add_monoid_algebra.equiv_grades
- \+ *lemma* add_monoid_algebra.grade.is_internal
- \+ *def* add_monoid_algebra.of_grades
- \+ *lemma* add_monoid_algebra.of_grades_comp_to_grades
- \+ *lemma* add_monoid_algebra.of_grades_of
- \+ *lemma* add_monoid_algebra.of_grades_to_grades
- \+ *def* add_monoid_algebra.to_grades
- \+ *lemma* add_monoid_algebra.to_grades_coe
- \+ *lemma* add_monoid_algebra.to_grades_comp_of_grades
- \+ *lemma* add_monoid_algebra.to_grades_of_grades
- \+ *lemma* add_monoid_algebra.to_grades_single



## [2021-09-30 18:34:36](https://github.com/leanprover-community/mathlib/commit/b18eedb)
feat(linear_algebra/affine_space/combination): add lemma `finset.map_affine_combination` ([#9453](https://github.com/leanprover-community/mathlib/pull/9453))
The other included lemmas `affine_map.coe_sub`,  `affine_map.coe_neg` are unrelated but are included to reduce PR overhead.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.coe_neg
- \+ *lemma* affine_map.coe_sub

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.map_affine_combination



## [2021-09-30 18:34:34](https://github.com/leanprover-community/mathlib/commit/6e6fe1f)
move(category_theory/category/default): rename to `category_theory.basic` ([#9412](https://github.com/leanprover-community/mathlib/pull/9412))
#### Estimated changes
Modified src/category_theory/category/Kleisli.lean


Modified src/category_theory/category/Rel.lean


Renamed src/category_theory/category/default.lean to src/category_theory/category/basic.lean


Modified src/category_theory/category/preorder.lean


Modified src/category_theory/category/ulift.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/control/equiv_functor.lean


Modified src/control/fold.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/slice.lean




## [2021-09-30 18:34:33](https://github.com/leanprover-community/mathlib/commit/4091f72)
refactor(linear_algebra/free_module): split in two files ([#9407](https://github.com/leanprover-community/mathlib/pull/9407))
We split `linear_algebra/free_module` in `linear_algebra/free_module/basic` and `linear_algebra/free_module/finite`, so one can work with free modules without having to import all the theory of dimension.
#### Estimated changes
Modified src/algebra/module/projective.lean


Modified src/linear_algebra/charpoly.lean


Renamed src/linear_algebra/free_module.lean to src/linear_algebra/free_module/basic.lean
- \- *lemma* module.finite.of_basis

Added src/linear_algebra/free_module/finite.lean
- \+ *lemma* module.finite.of_basis



## [2021-09-30 18:34:32](https://github.com/leanprover-community/mathlib/commit/6210d98)
feat(*): Clean up some misstated lemmas about analysis/manifolds ([#9395](https://github.com/leanprover-community/mathlib/pull/9395))
A few lemmas whose statement doesn't match the name / docstring about analytical things, all of these are duplicates of other lemmas, so look like copy paste errors.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* complex.differentiable_at_cosh

Modified src/geometry/manifold/mfderiv.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/topology/algebra/group_with_zero.lean
- \+/\- *lemma* continuous_at.div_const



## [2021-09-30 16:11:19](https://github.com/leanprover-community/mathlib/commit/118e809)
refactor(algebra/module/linear_map): Move elementwise structure from linear_algebra/basic ([#9331](https://github.com/leanprover-community/mathlib/pull/9331))
This helps reduce the size of linear_algebra/basic, and by virtue of being a smaller file makes it easier to spot typeclasses which can be relaxed.
As an example, `linear_map.endomorphism_ring` now requires only `semiring R` not `ring R`.
Having instances available as early as possible is generally good, as otherwise it is hard to even state things elsewhere.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.add_apply
- \+ *lemma* linear_map.add_comp
- \+ *lemma* linear_map.coe_mul
- \+ *lemma* linear_map.coe_one
- \+ *lemma* linear_map.comp_add
- \+ *lemma* linear_map.comp_neg
- \+ *theorem* linear_map.comp_smul
- \+ *lemma* linear_map.comp_sub
- \+ *theorem* linear_map.comp_zero
- \+ *lemma* linear_map.default_def
- \+ *lemma* linear_map.mul_apply
- \+ *lemma* linear_map.mul_eq_comp
- \+ *lemma* linear_map.neg_apply
- \+ *lemma* linear_map.neg_comp
- \+ *lemma* linear_map.one_apply
- \+ *lemma* linear_map.one_eq_id
- \+ *lemma* linear_map.smul_apply
- \+ *theorem* linear_map.smul_comp
- \+ *lemma* linear_map.sub_apply
- \+ *lemma* linear_map.sub_comp
- \+ *lemma* linear_map.zero_apply
- \+ *theorem* linear_map.zero_comp

Modified src/linear_algebra/basic.lean
- \- *lemma* linear_map.add_apply
- \- *lemma* linear_map.add_comp
- \- *lemma* linear_map.coe_mul
- \- *lemma* linear_map.coe_one
- \- *lemma* linear_map.comp_add
- \- *lemma* linear_map.comp_neg
- \- *theorem* linear_map.comp_smul
- \- *lemma* linear_map.comp_sub
- \- *theorem* linear_map.comp_zero
- \- *lemma* linear_map.default_def
- \- *lemma* linear_map.mul_apply
- \- *lemma* linear_map.mul_eq_comp
- \- *lemma* linear_map.neg_apply
- \- *lemma* linear_map.neg_comp
- \- *lemma* linear_map.one_apply
- \- *lemma* linear_map.one_eq_id
- \- *lemma* linear_map.smul_apply
- \- *theorem* linear_map.smul_comp
- \- *lemma* linear_map.sub_apply
- \- *lemma* linear_map.sub_comp
- \- *lemma* linear_map.zero_apply
- \- *theorem* linear_map.zero_comp



## [2021-09-30 16:11:18](https://github.com/leanprover-community/mathlib/commit/0dca20a)
feat(data/(d)finsupp): update_eq_sub_add_single ([#9184](https://github.com/leanprover-community/mathlib/pull/9184))
Also with `erase_eq_sub_single`.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.update_eq_sub_add_single

Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.erase_eq_sub_single
- \+ *lemma* dfinsupp.update_eq_erase_add_single
- \+ *lemma* dfinsupp.update_eq_single_add_erase
- \+ *lemma* dfinsupp.update_eq_sub_add_single

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.erase_eq_sub_single
- \+ *lemma* finsupp.update_eq_erase_add_single
- \+ *lemma* finsupp.update_eq_single_add_erase
- \+ *lemma* finsupp.update_eq_sub_add_single



## [2021-09-30 16:11:16](https://github.com/leanprover-community/mathlib/commit/8ec7fcf)
feat(ring_theory/henselian): Henselian local rings ([#8986](https://github.com/leanprover-community/mathlib/pull/8986))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring.inverse_mul_cancel
- \+ *lemma* ring.inverse_mul_cancel_left
- \+ *lemma* ring.inverse_mul_cancel_right
- \+ *lemma* ring.mul_inverse_cancel
- \+ *lemma* ring.mul_inverse_cancel_left
- \+ *lemma* ring.mul_inverse_cancel_right

Added src/ring_theory/henselian.lean
- \+ *lemma* henselian_local_ring.tfae
- \+ *lemma* is_local_ring_hom_of_le_jacobson_bot



## [2021-09-30 13:44:22](https://github.com/leanprover-community/mathlib/commit/f184dd7)
feat(group_theory/perm/concrete_cycle): perm.to_list ([#9178](https://github.com/leanprover-community/mathlib/pull/9178))
The conceptual inverse to `list.form_perm`.
#### Estimated changes
Modified src/group_theory/perm/concrete_cycle.lean
- \+ *lemma* equiv.perm.form_perm_to_list
- \+ *lemma* equiv.perm.is_cycle.exists_unique_cycle
- \+ *lemma* equiv.perm.is_cycle.exists_unique_cycle_subtype
- \+ *lemma* equiv.perm.length_to_list
- \+ *lemma* equiv.perm.length_to_list_pos_of_mem_support
- \+ *lemma* equiv.perm.mem_to_list_iff
- \+ *lemma* equiv.perm.next_to_list_eq_apply
- \+ *lemma* equiv.perm.nodup_to_list
- \+ *lemma* equiv.perm.nth_le_to_list
- \+ *lemma* equiv.perm.pow_apply_mem_to_list_iff_mem_support
- \+ *lemma* equiv.perm.same_cycle.to_list_is_rotated
- \+ *def* equiv.perm.to_list
- \+ *lemma* equiv.perm.to_list_eq_nil_iff
- \+ *lemma* equiv.perm.to_list_form_perm_is_rotated_self
- \+ *lemma* equiv.perm.to_list_form_perm_nil
- \+ *lemma* equiv.perm.to_list_form_perm_nontrivial
- \+ *lemma* equiv.perm.to_list_form_perm_singleton
- \+ *lemma* equiv.perm.to_list_ne_singleton
- \+ *lemma* equiv.perm.to_list_nth_le_zero
- \+ *lemma* equiv.perm.to_list_one
- \+ *lemma* equiv.perm.to_list_pow_apply_eq_rotate
- \+ *lemma* equiv.perm.two_le_length_to_list_iff_mem_support



## [2021-09-30 13:44:21](https://github.com/leanprover-community/mathlib/commit/3daae2c)
refactor(algebra/abs): add has_abs class ([#9172](https://github.com/leanprover-community/mathlib/pull/9172))
The notion of an "absolute value" occurs both in algebra (e.g. lattice ordered groups) and analysis (e.g. GM and GL-spaces). I introduced a `has_abs` notation class in https://github.com/leanprover-community/mathlib/pull/8673 for lattice ordered groups, along with the notation `|.|` and was asked by @eric-wieser and @jcommelin to add it in a separate PR and retro fit `has_abs` and the notation to mathlib.
I tried to introduce both the `has_abs` class and the `|.|` notation in [#8891](https://github.com/leanprover-community/mathlib/pull/8891) . However, I'm finding such a large and wide-ranging PR unwieldy to work with, so I'm now opening this PR which just replaces the previous definitions of `abs : α → α` in the following locations:
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/algebra/ordered_group.lean#L984
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/topology/continuous_function/basic.lean#L113
Out of scope are the following `abs : α → β`:
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/complex/is_R_or_C.lean#L439
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/complex/basic.lean#L406
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/real/nnreal.lean#L762
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/num/basic.lean#L315
Replacing the `abs` notation with `|.|` can be considered in a subsequent PR.
#### Estimated changes
Added src/algebra/abs.lean


Modified src/algebra/lattice_ordered_group.lean


Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_eq_max_neg
- \- *def* mabs

Modified src/analysis/complex/basic.lean
- \+/\- *lemma* complex.norm_int
- \+/\- *lemma* complex.norm_rat

Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.is_cau_abs_exp

Modified src/data/complex/exponential_bounds.lean


Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.abs_to_real

Modified src/measure_theory/function/l1_space.lean


Modified src/number_theory/zsqrtd/gaussian_int.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.inf_eq
- \+/\- *lemma* continuous_map.sup_eq

Modified src/topology/continuous_function/basic.lean
- \+/\- *lemma* continuous_map.abs_apply

Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-09-30 11:12:34](https://github.com/leanprover-community/mathlib/commit/2fd713a)
chore(order/basic): rename monotonicity concepts ([#9383](https://github.com/leanprover-community/mathlib/pull/9383))
This:
* Renames various mono lemmas either to enable dot notation (in some cases for types that don't exist yet) or to reflect they indicate monotonicity within a particular domain.
* Renames `strict_mono.top_preimage_top'` to `strict_mono.maximal_preimage_top'`
* Sorts some imports
* Replaces some `rcases` with `obtain`
#### Estimated changes
Modified src/algebra/lie/solvable.lean
- \+/\- *lemma* lie_algebra.derived_series_of_ideal_le

Modified src/algebra/order/field.lean


Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* antitone.concave_on_univ
- \+/\- *theorem* antitone_of_deriv_nonpos
- \- *theorem* concave_on_univ_of_deriv_antitone
- \- *theorem* convex.antitone_of_deriv_nonpos
- \- *theorem* convex.mono_of_deriv_nonneg
- \+ *theorem* convex.monotone_on_of_deriv_nonneg
- \+ *theorem* convex.strict_anti_of_deriv_neg
- \- *theorem* convex.strict_antitone_of_deriv_neg
- \- *theorem* mono_of_deriv_nonneg
- \+ *theorem* monotone_on_of_deriv_nonneg
- \+ *theorem* strict_anti_of_deriv_neg
- \- *theorem* strict_antitone_of_deriv_neg

Modified src/analysis/special_functions/integrals.lean
- \- *lemma* integral_sin_pow_antitone
- \+ *lemma* integral_sin_pow_succ_le

Modified src/data/real/pi/wallis.lean


Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* measurable_of_antitone
- \- *lemma* measurable_of_monotone

Modified src/measure_theory/function/lp_space.lean
- \- *lemma* measure_theory.Lp.antitone

Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* antitone.integrable_on_compact
- \+ *lemma* antitone_on.integrable_on_compact
- \- *lemma* integrable_on_compact_of_antitone
- \- *lemma* integrable_on_compact_of_antitone_on
- \- *lemma* integrable_on_compact_of_monotone
- \- *lemma* integrable_on_compact_of_monotone_on
- \+ *lemma* monotone.integrable_on_compact
- \+ *lemma* monotone_on.integrable_on_compact

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* antitone.interval_integrable
- \+ *lemma* antitone_on.interval_integrable
- \- *lemma* interval_integrable_of_antitone
- \- *lemma* interval_integrable_of_antitone_on
- \- *lemma* interval_integrable_of_monotone
- \- *lemma* interval_integrable_of_monotone_on
- \+ *lemma* monotone.interval_integrable
- \+ *lemma* monotone_on.interval_integrable

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* antitone.tendsto_set_integral
- \- *lemma* measure_theory.tendsto_set_integral_of_antitone

Modified src/order/basic.lean
- \+ *lemma* monotone.strict_mono_of_injective
- \- *lemma* strict_mono.bot_preimage_bot
- \+ *lemma* strict_mono.maximal_preimage_top
- \+ *lemma* strict_mono.minimal_preimage_bot
- \- *lemma* strict_mono.top_preimage_top
- \- *lemma* strict_mono_of_monotone_of_injective

Modified src/order/bounded_lattice.lean
- \- *lemma* is_compl.antitone
- \- *lemma* strict_mono.bot_preimage_bot'
- \+ *lemma* strict_mono.maximal_preimage_top'
- \+ *lemma* strict_mono.minimal_preimage_bot'
- \- *lemma* strict_mono.top_preimage_top'

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* csupr_mem_Inter_Icc_of_antitone_Icc_nat
- \- *lemma* csupr_mem_Inter_Icc_of_monotone_of_antitone
- \+ *lemma* monotone.csupr_mem_Inter_Icc_of_antitone

Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/ennreal.lean


Modified src/order/filter/indicator_function.lean
- \+ *lemma* antitone.tendsto_indicator
- \+ *lemma* monotone.tendsto_indicator
- \- *lemma* tendsto_indicator_of_antitone
- \- *lemma* tendsto_indicator_of_monotone

Modified src/order/lattice.lean
- \- *theorem* forall_le_of_monotone_of_antitone
- \+ *theorem* monotone.forall_le_of_antitone

Modified src/ring_theory/valuation/basic.lean


Modified src/topology/G_delta.lean


Modified src/topology/uniform_space/cauchy.lean




## [2021-09-30 11:12:33](https://github.com/leanprover-community/mathlib/commit/09506e6)
feat(ring_theory/finiteness): add finiteness of restrict_scalars ([#9363](https://github.com/leanprover-community/mathlib/pull/9363))
We add `module.finitte.of_restrict_scalars_finite` and related lemmas: if `A` is an `R`-algebra and `M` is an `A`-module that is finite as `R`-module, then it is finite as `A`-module (similarly for `finite_type`).
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* alg_hom.finite.of_comp_finite
- \+ *lemma* alg_hom.finite_type.of_comp_finite_type
- \+ *lemma* algebra.finite_type.of_restrict_scalars_finite_type
- \+ *lemma* module.finite.of_restrict_scalars_finite
- \+ *lemma* ring_hom.finite.of_comp_finite
- \+ *lemma* ring_hom.finite_type.of_comp_finite_type



## [2021-09-30 11:12:32](https://github.com/leanprover-community/mathlib/commit/3b48f7a)
docs(category_theory): provide missing module docs ([#9352](https://github.com/leanprover-community/mathlib/pull/9352))
#### Estimated changes
Modified src/category_theory/endomorphism.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/whiskering.lean




## [2021-09-30 08:02:28](https://github.com/leanprover-community/mathlib/commit/6d12b2e)
feat(group_theory/complement): Top is complement to every singleton subset ([#9460](https://github.com/leanprover-community/mathlib/pull/9460))
The top subset of G is complement to every singleton subset of G.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement_singleton_top
- \+ *lemma* subgroup.is_complement_top_singleton



## [2021-09-30 08:02:27](https://github.com/leanprover-community/mathlib/commit/f31758a)
chore(linear_algebra/quadratic_form): add missing lemmas, lift instance, and tweak argument implicitness ([#9458](https://github.com/leanprover-community/mathlib/pull/9458))
This adds `{quadratic,bilin}_form.{ext_iff,congr_fun}`, and a `can_lift` instance to promote `bilin_form`s to `quadratic_form`s.
The `associated_*` lemmas should have `Q` and `S` explicit as they are not inferable from the arguments. In particular, with `S` implicit, rewriting any of them backwards introduces a lot of noisy subgoals.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.congr_fun
- \+ *lemma* bilin_form.ext_iff
- \+ *lemma* bilin_form.nondegenerate.ne_zero
- \+ *lemma* bilin_form.not_nondegenerate_zero

Modified src/linear_algebra/quadratic_form.lean
- \+/\- *lemma* quadratic_form.associated_right_inverse
- \+ *lemma* quadratic_form.congr_fun
- \+ *lemma* quadratic_form.ext_iff
- \+ *lemma* quadratic_form.to_quadratic_form_associated



## [2021-09-30 08:02:25](https://github.com/leanprover-community/mathlib/commit/f6d2434)
feat(set_theory/cardinal_ordinal): there is no injective function from ordinals to types in the same universe ([#9452](https://github.com/leanprover-community/mathlib/pull/9452))
Contributed by @rwbarton at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Transfinite.20recursion/near/253614140
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* not_injective_of_ordinal
- \+ *lemma* not_injective_of_ordinal_of_small



## [2021-09-30 08:02:23](https://github.com/leanprover-community/mathlib/commit/089614b)
feat(algebra/star): If `R` is a `star_monoid`/`star_ring` then so is `Rᵒᵖ` ([#9446](https://github.com/leanprover-community/mathlib/pull/9446))
The definition is simply that `op (star r) = star (op r)`
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* op_star
- \+ *def* star_monoid_of_comm
- \+ *lemma* unop_star



## [2021-09-30 08:02:22](https://github.com/leanprover-community/mathlib/commit/d1f78e2)
feat(order/filter/{basic, cofinite}, topology/subset_properties): filter lemmas, prereqs for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9419](https://github.com/leanprover-community/mathlib/pull/9419))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto.of_tendsto_comp

Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.tendsto.exists_within_forall_ge
- \+ *lemma* filter.tendsto.exists_within_forall_le
- \+ *lemma* function.injective.tendsto_cofinite

Modified src/topology/subset_properties.lean
- \+ *lemma* filter.comap_cocompact



## [2021-09-30 08:02:21](https://github.com/leanprover-community/mathlib/commit/f76d019)
chore({field,ring}_theory): generalize `fraction_ring` and `is_separable` to rings ([#9415](https://github.com/leanprover-community/mathlib/pull/9415))
These used to be defined only for `integral_domain`s resp. `field`s, however the construction makes sense even for `comm_ring`s. So we can just do the generalization for free, and moreover it makes certain proof terms in their definition a lot smaller. Together with [#9414](https://github.com/leanprover-community/mathlib/pull/9414), this helps against [timeouts when combining `localization` and `polynomial`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60variables.60.20doesn't.20time.20out.20but.20inline.20params.20do), although the full test case is still quite slow (going from >40sec to approx 11 sec).
#### Estimated changes
Modified src/field_theory/separable.lean
- \+/\- *theorem* is_separable.is_integral
- \+/\- *theorem* is_separable.separable
- \+/\- *theorem* is_separable_iff

Modified src/ring_theory/localization.lean
- \+/\- *def* fraction_ring



## [2021-09-30 08:02:19](https://github.com/leanprover-community/mathlib/commit/92526c8)
chore(ring_theory/localization): speed up `localization` a bit ([#9414](https://github.com/leanprover-community/mathlib/pull/9414))
Now `nsmul` and `gsmul` are irreducible on `localization`. This helps against [timeouts when combining `localization` and `polynomial`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60variables.60.20doesn't.20time.20out.20but.20inline.20params.20do), although the full test case is still quite slow (going from >40sec to approx 11 sec).
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* localization.add_mk_self
- \+ *lemma* localization.smul_mk



## [2021-09-30 06:24:50](https://github.com/leanprover-community/mathlib/commit/8b238eb)
refactor(data/mv_polynomial/equiv): simplify option_equiv_left ([#9427](https://github.com/leanprover-community/mathlib/pull/9427))
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+/\- *def* mv_polynomial.option_equiv_left



## [2021-09-30 05:32:29](https://github.com/leanprover-community/mathlib/commit/c7dd27d)
split(analysis/convex/jensen): split Jensen's inequalities off `analysis.convex.function` ([#9445](https://github.com/leanprover-community/mathlib/pull/9445))
#### Estimated changes
Modified src/analysis/convex/function.lean
- \- *lemma* concave_on.exists_le_of_center_mass
- \- *lemma* concave_on.exists_le_of_mem_convex_hull
- \- *lemma* concave_on.le_map_center_mass
- \- *lemma* concave_on.le_map_sum
- \- *lemma* convex_on.exists_ge_of_center_mass
- \- *lemma* convex_on.exists_ge_of_mem_convex_hull
- \- *lemma* convex_on.map_center_mass_le
- \- *lemma* convex_on.map_sum_le

Added src/analysis/convex/jensen.lean
- \+ *lemma* concave_on.exists_le_of_center_mass
- \+ *lemma* concave_on.exists_le_of_mem_convex_hull
- \+ *lemma* concave_on.le_map_center_mass
- \+ *lemma* concave_on.le_map_sum
- \+ *lemma* convex_on.exists_ge_of_center_mass
- \+ *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+ *lemma* convex_on.map_center_mass_le
- \+ *lemma* convex_on.map_sum_le

Modified src/analysis/convex/topology.lean




## [2021-09-30 02:54:54](https://github.com/leanprover-community/mathlib/commit/d9ed073)
chore(scripts): update nolints.txt ([#9459](https://github.com/leanprover-community/mathlib/pull/9459))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-30 02:06:41](https://github.com/leanprover-community/mathlib/commit/f254c2f)
refactor(analysis/normed_space/{dual, pi_Lp}): split out inner product space parts ([#9388](https://github.com/leanprover-community/mathlib/pull/9388))
This is just moving code, no math changes.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20folder.20analysis.2Finner_product_space
#### Estimated changes
Added src/analysis/inner_product_space/dual.lean
- \+ *def* inner_product_space.isometric.to_dual
- \+ *lemma* inner_product_space.ker_to_dual_map
- \+ *lemma* inner_product_space.norm_to_dual'_apply
- \+ *lemma* inner_product_space.norm_to_dual_apply
- \+ *lemma* inner_product_space.norm_to_dual_map_apply
- \+ *lemma* inner_product_space.norm_to_dual_symm_apply
- \+ *lemma* inner_product_space.range_to_dual_map
- \+ *def* inner_product_space.to_dual'
- \+ *lemma* inner_product_space.to_dual'_apply
- \+ *lemma* inner_product_space.to_dual'_isometry
- \+ *lemma* inner_product_space.to_dual'_surjective
- \+ *def* inner_product_space.to_dual
- \+ *lemma* inner_product_space.to_dual_apply
- \+ *lemma* inner_product_space.to_dual_eq_iff_eq'
- \+ *lemma* inner_product_space.to_dual_eq_iff_eq
- \+ *def* inner_product_space.to_dual_map
- \+ *lemma* inner_product_space.to_dual_map_apply
- \+ *lemma* inner_product_space.to_dual_map_eq_iff_eq
- \+ *lemma* inner_product_space.to_dual_map_injective
- \+ *lemma* inner_product_space.to_dual_map_isometry

Modified src/analysis/inner_product_space/euclidean_dist.lean


Added src/analysis/inner_product_space/pi_L2.lean
- \+ *def* basis.isometry_euclidean_of_orthonormal
- \+ *def* complex.isometry_euclidean
- \+ *lemma* complex.isometry_euclidean_apply_one
- \+ *lemma* complex.isometry_euclidean_apply_zero
- \+ *lemma* complex.isometry_euclidean_proj_eq_self
- \+ *lemma* complex.isometry_euclidean_symm_apply
- \+ *lemma* euclidean_space.norm_eq
- \+ *def* euclidean_space
- \+ *lemma* finrank_euclidean_space
- \+ *lemma* finrank_euclidean_space_fin
- \+ *def* linear_isometry_equiv.from_orthogonal_span_singleton
- \+ *def* linear_isometry_equiv.of_inner_product_space
- \+ *lemma* pi_Lp.inner_apply
- \+ *lemma* pi_Lp.norm_eq_of_L2

Modified src/analysis/normed_space/dual.lean
- \- *def* inner_product_space.isometric.to_dual
- \- *lemma* inner_product_space.ker_to_dual_map
- \- *lemma* inner_product_space.norm_to_dual'_apply
- \- *lemma* inner_product_space.norm_to_dual_apply
- \- *lemma* inner_product_space.norm_to_dual_map_apply
- \- *lemma* inner_product_space.norm_to_dual_symm_apply
- \- *lemma* inner_product_space.range_to_dual_map
- \- *def* inner_product_space.to_dual'
- \- *lemma* inner_product_space.to_dual'_apply
- \- *lemma* inner_product_space.to_dual'_isometry
- \- *lemma* inner_product_space.to_dual'_surjective
- \- *def* inner_product_space.to_dual
- \- *lemma* inner_product_space.to_dual_apply
- \- *lemma* inner_product_space.to_dual_eq_iff_eq'
- \- *lemma* inner_product_space.to_dual_eq_iff_eq
- \- *def* inner_product_space.to_dual_map
- \- *lemma* inner_product_space.to_dual_map_apply
- \- *lemma* inner_product_space.to_dual_map_eq_iff_eq
- \- *lemma* inner_product_space.to_dual_map_injective
- \- *lemma* inner_product_space.to_dual_map_isometry

Modified src/analysis/normed_space/pi_Lp.lean
- \- *def* basis.isometry_euclidean_of_orthonormal
- \- *def* complex.isometry_euclidean
- \- *lemma* complex.isometry_euclidean_apply_one
- \- *lemma* complex.isometry_euclidean_apply_zero
- \- *lemma* complex.isometry_euclidean_proj_eq_self
- \- *lemma* complex.isometry_euclidean_symm_apply
- \- *lemma* euclidean_space.norm_eq
- \- *def* euclidean_space
- \- *lemma* finrank_euclidean_space
- \- *lemma* finrank_euclidean_space_fin
- \- *def* linear_isometry_equiv.from_orthogonal_span_singleton
- \- *def* linear_isometry_equiv.of_inner_product_space
- \- *lemma* pi_Lp.inner_apply
- \- *lemma* pi_Lp.norm_eq_of_L2

Modified src/geometry/manifold/instances/real.lean


Modified src/measure_theory/function/conditional_expectation.lean




## [2021-09-29 21:38:23](https://github.com/leanprover-community/mathlib/commit/519ab35)
feat(topology/metric_space/basic): nonempty intersections of balls ([#9448](https://github.com/leanprover-community/mathlib/pull/9448))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.not_disjoint_iff_nonempty_inter

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.ball_subset_ball'
- \+ *lemma* metric.closed_ball_subset_closed_ball'
- \+ *lemma* metric.dist_le_add_of_nonempty_closed_ball_inter_closed_ball
- \+ *lemma* metric.dist_lt_add_of_nonempty_ball_inter_ball
- \+ *lemma* metric.dist_lt_add_of_nonempty_ball_inter_closed_ball
- \+ *lemma* metric.dist_lt_add_of_nonempty_closed_ball_inter_ball



## [2021-09-29 21:38:22](https://github.com/leanprover-community/mathlib/commit/acced82)
chore(*): linting ([#9343](https://github.com/leanprover-community/mathlib/pull/9343))
#### Estimated changes
Modified src/data/mllist.lean


Modified src/data/multiset/basic.lean


Modified src/data/polynomial/identities.lean


Modified src/number_theory/pell.lean




## [2021-09-29 20:27:33](https://github.com/leanprover-community/mathlib/commit/3681b5a)
split(analysis/convex/slope): split slope results off `analysis.convex.function` ([#9444](https://github.com/leanprover-community/mathlib/pull/9444))
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/convex/function.lean
- \- *lemma* concave_on.slope_mono_adjacent
- \- *lemma* concave_on_iff_slope_mono_adjacent
- \- *lemma* concave_on_of_slope_mono_adjacent
- \- *lemma* convex_on.slope_mono_adjacent
- \- *lemma* convex_on_iff_slope_mono_adjacent
- \- *lemma* convex_on_of_slope_mono_adjacent

Added src/analysis/convex/slope.lean
- \+ *lemma* concave_on.slope_anti_adjacent
- \+ *lemma* concave_on_iff_slope_anti_adjacent
- \+ *lemma* concave_on_of_slope_anti_adjacent
- \+ *lemma* convex_on.slope_mono_adjacent
- \+ *lemma* convex_on_iff_slope_mono_adjacent
- \+ *lemma* convex_on_of_slope_mono_adjacent



## [2021-09-29 18:44:41](https://github.com/leanprover-community/mathlib/commit/eca3fd9)
feat(data/real/ennreal): composition of coercion of natural numbers in ennreal ([#9447](https://github.com/leanprover-community/mathlib/pull/9447))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_nnreal_nat
- \+ *lemma* ennreal.to_real_nat



## [2021-09-29 16:34:59](https://github.com/leanprover-community/mathlib/commit/88e613e)
feat(data/mv_polynomial/cardinal): cardinalities of polynomial rings ([#9384](https://github.com/leanprover-community/mathlib/pull/9384))
#### Estimated changes
Added src/data/mv_polynomial/cardinal.lean
- \+ *lemma* mv_polynomial.cardinal_mk_le_max

Added src/data/polynomial/cardinal.lean
- \+ *lemma* polynomial.cardinal_mk_le_max



## [2021-09-29 16:34:57](https://github.com/leanprover-community/mathlib/commit/2cd1d04)
feat(group_theory/sylow): Sylow's theorems for infinite groups ([#9288](https://github.com/leanprover-community/mathlib/pull/9288))
This PR contains all three of Sylow's theorems for infinite groups, building off the work of @ChrisHughes24 in the `ch_sylow2` branch of mathlib.
Later, I'll PR some consequences (e.g., index of normalizer stuff, maybe a golf of the original sylow stuff using the new results, Frattini's argument, ...).
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* card_sylow_modeq_one
- \+ *lemma* is_p_group.exists_le_sylow
- \+ *lemma* is_p_group.inf_normalizer_sylow
- \+ *lemma* is_p_group.sylow_mem_fixed_points_iff
- \+ *lemma* subgroup.sylow_mem_fixed_points_iff
- \+ *lemma* sylow.coe_smul
- \+ *lemma* sylow.coe_subgroup_smul
- \+ *lemma* sylow.ext
- \+ *lemma* sylow.ext_iff
- \+ *lemma* sylow.smul_eq_iff_mem_normalizer
- \+ *lemma* sylow.to_subgroup_eq_coe



## [2021-09-29 14:22:40](https://github.com/leanprover-community/mathlib/commit/9535c08)
feat(linear_algebra/affine_space/combination, analysis/convex/combination): basic lemmas about affine combinations, center of mass, centroid ([#9103](https://github.com/leanprover-community/mathlib/pull/9103))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_comp
- \+/\- *lemma* finset.sum_comp

Modified src/analysis/convex/combination.lean
- \+ *lemma* affine_combination_eq_center_mass
- \+ *lemma* finset.center_mass_id_mem_convex_hull
- \+ *lemma* finset.centroid_eq_center_mass
- \+ *lemma* finset.centroid_mem_convex_hull

Modified src/data/finset/basic.lean
- \+ *lemma* finset.attach_image_coe
- \+/\- *lemma* finset.attach_image_val

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.affine_combination_eq_linear_combination
- \+ *lemma* finset.attach_affine_combination_coe
- \+ *lemma* finset.attach_affine_combination_of_injective
- \+ *lemma* finset.centroid_univ



## [2021-09-29 13:14:50](https://github.com/leanprover-community/mathlib/commit/9e91b70)
feat(analysis/convex/function): define strictly convex/concave functions ([#9439](https://github.com/leanprover-community/mathlib/pull/9439))
#### Estimated changes
Modified src/analysis/convex/function.lean
- \+/\- *def* concave_on
- \+/\- *def* convex_on
- \+ *def* strict_concave_on
- \+ *def* strict_convex_on



## [2021-09-29 11:22:48](https://github.com/leanprover-community/mathlib/commit/6f609ba)
feat(data/mv_polynomial/basic): aeval_tower ([#9429](https://github.com/leanprover-community/mathlib/pull/9429))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *def* mv_polynomial.aeval_tower
- \+ *lemma* mv_polynomial.aeval_tower_C
- \+ *lemma* mv_polynomial.aeval_tower_X
- \+ *lemma* mv_polynomial.aeval_tower_algebra_map
- \+ *lemma* mv_polynomial.aeval_tower_comp_C
- \+ *lemma* mv_polynomial.aeval_tower_comp_algebra_map
- \+ *lemma* mv_polynomial.aeval_tower_comp_to_alg_hom
- \+ *lemma* mv_polynomial.aeval_tower_id
- \+ *lemma* mv_polynomial.aeval_tower_of_id
- \+ *lemma* mv_polynomial.aeval_tower_to_alg_hom
- \+ *lemma* mv_polynomial.alg_hom_ext'



## [2021-09-29 11:22:47](https://github.com/leanprover-community/mathlib/commit/43c1ab2)
fix(linear_algebra/basic): generalize `linear_map.add_comm_group` to semilinear maps ([#9402](https://github.com/leanprover-community/mathlib/pull/9402))
Also generalizes `coe_mk` and golfs some proofs.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.coe_mk

Modified src/linear_algebra/basic.lean




## [2021-09-29 10:20:15](https://github.com/leanprover-community/mathlib/commit/d2463aa)
feat(ring_theory/algebraic): is_algebraic_of_larger_base_of_injective ([#9433](https://github.com/leanprover-community/mathlib/pull/9433))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_algebraic_of_larger_base_of_injective
- \+/\- *lemma* is_algebraic_iff_not_injective



## [2021-09-29 09:37:26](https://github.com/leanprover-community/mathlib/commit/e150668)
chore(topology/sheaves): fix timeout by splitting proof ([#9436](https://github.com/leanprover-community/mathlib/pull/9436))
In [#7033](https://github.com/leanprover-community/mathlib/pull/7033) we were getting a timeout in `app_surjective_of_stalk_functor_map_bijective`. Since the proof looks like it has two rather natural components, I split out the first half into its own lemma. This is a separate PR since I don't really understand the topology/sheaf library, so I might be doing something very weird.
Timings:
 * original (master): 4.42s
 * original (master + [#7033](https://github.com/leanprover-community/mathlib/pull/7033)): 5.93s
 * new (master + this PR): 4.24s + 316ms
 * new (master + [#7033](https://github.com/leanprover-community/mathlib/pull/7033) + this PR): 5.48s + 212ms
#### Estimated changes
Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.app_surjective_of_injective_of_locally_surjective



## [2021-09-29 09:37:24](https://github.com/leanprover-community/mathlib/commit/0de5432)
feat(data/W/cardinal): results about cardinality of W-types ([#9210](https://github.com/leanprover-community/mathlib/pull/9210))
#### Estimated changes
Modified archive/examples/prop_encodable.lean


Renamed src/data/W.lean to src/data/W/basic.lean
- \+ *def* W_type.elim
- \+ *lemma* W_type.elim_injective
- \+ *def* W_type.equiv_sigma
- \+ *lemma* W_type.infinite_of_nonempty_of_is_empty
- \+ *def* W_type.of_sigma
- \+ *lemma* W_type.of_sigma_to_sigma
- \+ *def* W_type.to_sigma
- \+ *lemma* W_type.to_sigma_of_sigma

Added src/data/W/cardinal.lean
- \+ *lemma* W_type.cardinal_mk_eq_sum
- \+ *lemma* W_type.cardinal_mk_le_max_omega_of_fintype
- \+ *lemma* W_type.cardinal_mk_le_of_le

Modified src/data/pfunctor/univariate/basic.lean




## [2021-09-29 08:41:05](https://github.com/leanprover-community/mathlib/commit/c758cec)
chore(analysis/convex/function): change `add_comm_monoid` to `add_comm_group` when carrier type is module of scalars containing -1 ([#9442](https://github.com/leanprover-community/mathlib/pull/9442))
Related [Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Convexity.20refactor/near/255268131)
#### Estimated changes
Modified src/analysis/convex/combination.lean


Modified src/analysis/convex/function.lean




## [2021-09-29 04:03:07](https://github.com/leanprover-community/mathlib/commit/d7abdff)
chore(analysis/normed_space/*): prereqs for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9379](https://github.com/leanprover-community/mathlib/pull/9379))
The functions `abs` and `norm_sq` on `ℂ` are proper.
A matrix with entries in a {seminormed group, normed group, normed space} is itself a {seminormed group, normed group, normed space}.
An injective linear map with finite-dimensional domain is a closed embedding.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.tendsto_abs_cocompact_at_top
- \+ *lemma* complex.tendsto_norm_sq_cocompact_at_top

Modified src/analysis/normed_space/basic.lean
- \+ *def* matrix.normed_group
- \+ *def* matrix.normed_space
- \+ *def* matrix.semi_normed_group
- \+ *lemma* semi_norm_matrix_le_iff

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* linear_equiv.closed_embedding_of_injective



## [2021-09-29 04:03:06](https://github.com/leanprover-community/mathlib/commit/8bd75b2)
feat(measure_theory/measure/haar_lebesgue): properties of Haar measure on real vector spaces ([#9325](https://github.com/leanprover-community/mathlib/pull/9325))
We show that any additive Haar measure on a finite-dimensional real vector space is rescaled by a linear map through its determinant, and we compute the measure of balls and spheres.
#### Estimated changes
Modified src/linear_algebra/matrix/transvection.lean


Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* measure_theory.add_haar_measure_eq_volume
- \+ *lemma* measure_theory.add_haar_measure_eq_volume_pi
- \- *lemma* measure_theory.haar_measure_eq_lebesgue_measure
- \+ *lemma* measure_theory.is_add_left_invariant_real_volume_pi
- \+ *lemma* measure_theory.measure.add_haar_ball
- \+ *lemma* measure_theory.measure.add_haar_ball_center
- \+ *lemma* measure_theory.measure.add_haar_ball_lt_top
- \+ *lemma* measure_theory.measure.add_haar_ball_of_pos
- \+ *lemma* measure_theory.measure.add_haar_ball_pos
- \+ *lemma* measure_theory.measure.add_haar_closed_ball'
- \+ *lemma* measure_theory.measure.add_haar_closed_ball
- \+ *lemma* measure_theory.measure.add_haar_closed_ball_center
- \+ *lemma* measure_theory.measure.add_haar_closed_ball_lt_top
- \+ *lemma* measure_theory.measure.add_haar_closed_ball_pos
- \+ *lemma* measure_theory.measure.add_haar_closed_unit_ball_eq_add_haar_unit_ball
- \+ *lemma* measure_theory.measure.add_haar_preimage_smul
- \+ *lemma* measure_theory.measure.add_haar_smul
- \+ *lemma* measure_theory.measure.add_haar_sphere
- \+ *lemma* measure_theory.measure.add_haar_sphere_of_ne_zero
- \+ *lemma* measure_theory.measure.haar_preimage_linear_map
- \+ *lemma* measure_theory.measure.map_add_haar_smul
- \+ *lemma* measure_theory.measure.map_linear_map_add_haar_eq_smul_add_haar
- \+ *lemma* measure_theory.measure.map_linear_map_add_haar_pi_eq_smul_add_haar
- \+ *def* topological_space.positive_compacts.pi_Icc01

Modified src/measure_theory/measure/lebesgue.lean




## [2021-09-29 04:03:04](https://github.com/leanprover-community/mathlib/commit/861d3bc)
chore(order/preorder_hom): more homs, golf a few proofs ([#9256](https://github.com/leanprover-community/mathlib/pull/9256))
### New `preorder_hom`s
* `preorder_hom.curry`: an order isomorphism between `α × β →ₘ γ` and `α →ₘ β →ₘ γ`;
* `preorder_hom.compₘ`: a fully bundled version of `preorder_hom.comp`;
* `preorder_hom.prodₘ`: a fully bundled version of `preorder_hom.prod`;
* `preorder_hom.prod_iso`: Order isomorphism between the space of
  monotone maps to `β × γ` and the product of the spaces +of monotone
  maps to `β` and `γ`;
* `preorder_hom.pi`: construct a bundled monotone map `α →ₘ Π i, π i`
  from a family of monotone maps +`f i : α →ₘ π i`;
* `preorder_hom.pi_iso`: same thing, as an `order_iso`;
* `preorder_hom.dual`: interpret `f : α →ₘ β` as `order_dual α →ₘ order_dual β`;
* `preorder_hom.dual_iso`: same as an `order_iso` (with one more
  `order_dual` to get a monotone map, not an antitone map);
### Renamed/moved `preorder_hom`s
The following `preorder_hom`s were renamed and/or moved from
`order.omega_complete_partial_order` to `order.preorder_hom`.
* `preorder_hom.const` : moved, bundle as `β →ₘ α →ₘ β`;
* `preorder_hom.prod.diag` : `preorder_hom.diag`;
* `preorder_hom.prod.map` : `preorder_hom.prod_map`;
* `preorder_hom.prod.fst` : `preorder_hom.fst`;
* `preorder_hom.prod.snd` : `preorder_hom.snd`;
* `preorder_hom.prod.zip` : `preorder_hom.prod`;
* `pi.monotone_apply` : `pi.eval_preorder_hom`;
* `preorder_hom.monotone_apply` : `preorder_hom.apply`;
* `preorder_hom.to_fun_hom` : moved.
### Other changes
* add an instance `can_lift (α → β) (α →ₘ β)`;
- rename `omega_complete_partial_order.continuous.to_monotone` to
  `omega_complete_partial_order.continuous'.to_monotone` to enable dot
  notation, same with
  `omega_complete_partial_order.continuous.to_bundled`;
* use `order_dual` to get some proofs;
* golf some proofs;
* redefine `has_Inf.Inf` and `has_Sup.Sup` using `infi`/`supr`;
* generalize some `mono` lemmas;
* use notation `→ₘ`.
#### Estimated changes
Modified src/control/lawful_fix.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/order/closure.lean


Modified src/order/omega_complete_partial_order.lean
- \+/\- *theorem* complete_lattice.Sup_continuous'
- \+ *lemma* complete_lattice.supr_continuous
- \+ *lemma* omega_complete_partial_order.continuous'.to_bundled
- \+ *lemma* omega_complete_partial_order.continuous'.to_monotone
- \+ *lemma* omega_complete_partial_order.continuous'_coe
- \- *lemma* omega_complete_partial_order.continuous.to_bundled
- \- *lemma* omega_complete_partial_order.continuous.to_monotone
- \+ *lemma* omega_complete_partial_order.continuous_const
- \+ *lemma* omega_complete_partial_order.continuous_hom.apply_mono
- \+/\- *def* omega_complete_partial_order.continuous_hom.const
- \- *lemma* omega_complete_partial_order.continuous_hom.monotone
- \- *def* omega_complete_partial_order.preorder_hom.monotone_apply
- \- *def* omega_complete_partial_order.preorder_hom.to_fun_hom
- \- *def* pi.monotone_apply
- \- *def* preorder_hom.const
- \- *def* preorder_hom.prod.diag
- \- *def* preorder_hom.prod.fst
- \- *def* preorder_hom.prod.map
- \- *def* preorder_hom.prod.snd
- \- *def* preorder_hom.prod.zip

Modified src/order/preorder_hom.lean
- \+ *def* pi.eval_preorder_hom
- \+ *lemma* preorder_hom.Inf_apply
- \+ *lemma* preorder_hom.Sup_apply
- \+ *def* preorder_hom.apply
- \+ *lemma* preorder_hom.apply_mono
- \+ *def* preorder_hom.coe_fn_hom
- \+ *lemma* preorder_hom.coe_infi
- \+ *lemma* preorder_hom.coe_le_coe
- \+ *lemma* preorder_hom.coe_supr
- \+/\- *def* preorder_hom.comp
- \+ *lemma* preorder_hom.comp_const
- \+/\- *lemma* preorder_hom.comp_id
- \+ *lemma* preorder_hom.comp_mono
- \+ *lemma* preorder_hom.comp_prod_comp_same
- \+ *def* preorder_hom.compₘ
- \+ *def* preorder_hom.const
- \+ *lemma* preorder_hom.const_comp
- \+ *def* preorder_hom.curry
- \+ *lemma* preorder_hom.curry_apply
- \+ *lemma* preorder_hom.curry_symm_apply
- \+ *def* preorder_hom.diag
- \+ *def* preorder_hom.dual_iso
- \+/\- *lemma* preorder_hom.ext
- \+ *def* preorder_hom.fst
- \+ *lemma* preorder_hom.fst_comp_prod
- \+ *lemma* preorder_hom.fst_prod_snd
- \+/\- *def* preorder_hom.id
- \+/\- *lemma* preorder_hom.id_comp
- \+ *lemma* preorder_hom.infi_apply
- \+ *lemma* preorder_hom.le_def
- \+ *lemma* preorder_hom.mk_le_mk
- \- *lemma* preorder_hom.monotone
- \+ *def* preorder_hom.on_diag
- \+ *def* preorder_hom.pi
- \+ *def* preorder_hom.pi_iso
- \+ *def* preorder_hom.prod_iso
- \+ *def* preorder_hom.prod_map
- \+ *lemma* preorder_hom.prod_mono
- \+ *def* preorder_hom.prodₘ
- \+ *def* preorder_hom.snd
- \+ *lemma* preorder_hom.snd_comp_prod
- \+ *lemma* preorder_hom.supr_apply

Modified src/topology/omega_complete_partial_order.lean
- \+ *lemma* Scott.is_ωSup_iff_is_lub



## [2021-09-29 03:09:45](https://github.com/leanprover-community/mathlib/commit/49805e6)
chore(scripts): update nolints.txt ([#9441](https://github.com/leanprover-community/mathlib/pull/9441))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-09-28 23:13:37](https://github.com/leanprover-community/mathlib/commit/73afb6c)
chore(data/fintype/basic): add `fintype.card_set` ([#9434](https://github.com/leanprover-community/mathlib/pull/9434))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_set



## [2021-09-28 20:09:13](https://github.com/leanprover-community/mathlib/commit/e2cb9e1)
feat(data/mv_polynomial/supported): subalgebra of polynomials supported by a set of variables ([#9183](https://github.com/leanprover-community/mathlib/pull/9183))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.symm_trans_apply

Added src/data/mv_polynomial/supported.lean
- \+ *lemma* mv_polynomial.X_mem_supported
- \+ *lemma* mv_polynomial.mem_supported
- \+ *lemma* mv_polynomial.mem_supported_vars
- \+ *lemma* mv_polynomial.supported_empty
- \+ *lemma* mv_polynomial.supported_eq_adjoin_X
- \+ *lemma* mv_polynomial.supported_eq_range_rename
- \+ *lemma* mv_polynomial.supported_eq_vars_subset
- \+ *lemma* mv_polynomial.supported_equiv_mv_polynomial_symm_C
- \+ *lemma* mv_polynomial.supported_equiv_mv_polynomial_symm_X
- \+ *lemma* mv_polynomial.supported_le_supported_iff
- \+ *lemma* mv_polynomial.supported_mono
- \+ *lemma* mv_polynomial.supported_strict_mono
- \+ *lemma* mv_polynomial.supported_univ

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.exists_rename_eq_of_vars_subset_range
- \+ *lemma* mv_polynomial.hom_congr_vars



## [2021-09-28 16:57:32](https://github.com/leanprover-community/mathlib/commit/e18b9ca)
feat(set_theory/continuum): define `cardinal.continuum := 2 ^ ω` ([#9354](https://github.com/leanprover-community/mathlib/pull/9354))
#### Estimated changes
Modified src/data/real/cardinality.lean
- \+/\- *lemma* cardinal.mk_Icc_real
- \+/\- *lemma* cardinal.mk_Ici_real
- \+/\- *lemma* cardinal.mk_Ico_real
- \+/\- *lemma* cardinal.mk_Iic_real
- \+/\- *lemma* cardinal.mk_Iio_real
- \+/\- *lemma* cardinal.mk_Ioc_real
- \+/\- *lemma* cardinal.mk_Ioi_real
- \+/\- *lemma* cardinal.mk_Ioo_real
- \+/\- *lemma* cardinal.mk_real
- \+/\- *lemma* cardinal.mk_univ_real

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.mk_nat
- \+/\- *theorem* cardinal.nat_cast_inj

Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* cardinal.bit0_ne_zero
- \+ *lemma* cardinal.nat_power_eq

Added src/set_theory/continuum.lean
- \+ *def* cardinal.continuum
- \+ *lemma* cardinal.continuum_add_nat
- \+ *lemma* cardinal.continuum_add_omega
- \+ *lemma* cardinal.continuum_add_self
- \+ *lemma* cardinal.continuum_mul_nat
- \+ *lemma* cardinal.continuum_mul_omega
- \+ *lemma* cardinal.continuum_mul_self
- \+ *lemma* cardinal.continuum_ne_zero
- \+ *lemma* cardinal.continuum_pos
- \+ *lemma* cardinal.continuum_power_omega
- \+ *lemma* cardinal.lift_continuum
- \+ *lemma* cardinal.mk_set_nat
- \+ *lemma* cardinal.nat_add_continuum
- \+ *lemma* cardinal.nat_lt_continuum
- \+ *lemma* cardinal.nat_mul_continuum
- \+ *lemma* cardinal.nat_power_omega
- \+ *lemma* cardinal.omega_add_continuum
- \+ *lemma* cardinal.omega_le_continuum
- \+ *lemma* cardinal.omega_lt_continuum
- \+ *lemma* cardinal.omega_mul_continuum
- \+ *lemma* cardinal.omega_power_omega
- \+ *lemma* cardinal.two_power_omega



## [2021-09-28 14:01:07](https://github.com/leanprover-community/mathlib/commit/15f15a6)
chore(order/*): replace `mono_incr` and `mono_decr` in lemma names wih `monotone` and `antitone` ([#9428](https://github.com/leanprover-community/mathlib/pull/9428))
This change was performed as a find-and-replace. No occurrences of `incr` or `decr` appear as tokens in lemma names after this change.
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.pow_antitone_exp
- \- *lemma* nnreal.pow_mono_decr_exp

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_mem_Inter_Icc_of_antitone_Icc
- \+ *lemma* csupr_mem_Inter_Icc_of_antitone_Icc_nat
- \- *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc
- \- *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc_nat
- \- *lemma* csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr
- \+ *lemma* csupr_mem_Inter_Icc_of_monotone_of_antitone

Modified src/order/lattice.lean
- \+ *theorem* forall_le_of_monotone_of_antitone
- \- *theorem* forall_le_of_monotone_of_mono_decr

Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* continuous_at_left_of_mono_incr_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_left_of_mono_incr_on_of_exists_between
- \- *lemma* continuous_at_left_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_left_of_monotone_on_of_image_mem_nhds_within
- \- *lemma* continuous_at_of_mono_incr_on_of_closure_image_mem_nhds
- \- *lemma* continuous_at_of_mono_incr_on_of_exists_between
- \- *lemma* continuous_at_of_mono_incr_on_of_image_mem_nhds
- \+ *lemma* continuous_at_of_monotone_on_of_closure_image_mem_nhds
- \+ *lemma* continuous_at_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_of_monotone_on_of_image_mem_nhds
- \- *lemma* continuous_at_right_of_mono_incr_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_right_of_mono_incr_on_of_exists_between
- \- *lemma* continuous_at_right_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_right_of_monotone_on_of_image_mem_nhds_within



## [2021-09-28 14:01:05](https://github.com/leanprover-community/mathlib/commit/2d5fd65)
fix(algebra/opposites): add a missing `comm_semiring` instance ([#9425](https://github.com/leanprover-community/mathlib/pull/9425))
#### Estimated changes
Modified src/algebra/opposites.lean




## [2021-09-28 14:01:04](https://github.com/leanprover-community/mathlib/commit/84bbb00)
feat(data/set/intervals): add `order_iso.image_Ixx` lemmas ([#9404](https://github.com/leanprover-community/mathlib/pull/9404))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* order_iso.image_Icc
- \+ *lemma* order_iso.image_Ici
- \+ *lemma* order_iso.image_Ico
- \+ *lemma* order_iso.image_Iic
- \+ *lemma* order_iso.image_Iio
- \+ *lemma* order_iso.image_Ioc
- \+ *lemma* order_iso.image_Ioi
- \+ *lemma* order_iso.image_Ioo



## [2021-09-28 11:33:36](https://github.com/leanprover-community/mathlib/commit/4a02fd3)
refactor(algebra/order/ring,data/complex): redefine `ordered_comm_ring` and complex order ([#9420](https://github.com/leanprover-community/mathlib/pull/9420))
* `ordered_comm_ring` no longer extends `ordered_comm_semiring`.
  We add an instance `ordered_comm_ring.to_ordered_comm_semiring` instead.
* redefine complex order in terms of `re` and `im` instead of existence of a nonnegative real number.
* simplify `has_star.star` on `complex` to `conj`;
* rename `complex.complex_partial_order` etc to `complex.partial_order` etc, make them protected.
#### Estimated changes
Modified src/algebra/order/ring.lean


Modified src/data/complex/basic.lean
- \- *def* complex.complex_order
- \- *def* complex.complex_ordered_comm_ring
- \- *def* complex.complex_star_ordered_ring
- \+/\- *lemma* complex.le_def
- \+/\- *lemma* complex.lt_def
- \+ *lemma* complex.not_le_iff
- \+ *lemma* complex.not_le_zero_iff
- \+/\- *lemma* complex.real_le_real
- \+/\- *lemma* complex.real_lt_real
- \+ *lemma* complex.star_def

Modified src/data/complex/module.lean
- \- *lemma* complex.complex_ordered_smul



## [2021-09-28 11:33:35](https://github.com/leanprover-community/mathlib/commit/06610c7)
feat(data/list/basic): lemmas about tail ([#9259](https://github.com/leanprover-community/mathlib/pull/9259))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.mem_of_mem_tail
- \+ *lemma* list.nth_le_tail



## [2021-09-28 11:33:33](https://github.com/leanprover-community/mathlib/commit/c0dbe14)
feat(linear_algebra/matrix/fpow): integer powers of matrices ([#8683](https://github.com/leanprover-community/mathlib/pull/8683))
Since we have an inverse defined for matrices via `nonsing_inv`, we provide a `div_inv_monoid` instance for matrices.
The instance provides the ability to refer to integer power of matrices via the auto-generated `gpow`.
This is done in a new file to allow selective use.
Many API lemmas are provided to facilitate usage of the new `gpow`, many copied in form/content from
`algebra/group_with_zero/power.lean`, which provides a similar API.
#### Estimated changes
Added src/linear_algebra/matrix/fpow.lean
- \+ *lemma* is_unit.det_fpow
- \+ *theorem* matrix.commute.fpow_fpow
- \+ *theorem* matrix.commute.fpow_fpow_self
- \+ *theorem* matrix.commute.fpow_left
- \+ *theorem* matrix.commute.fpow_right
- \+ *theorem* matrix.commute.fpow_self
- \+ *lemma* matrix.commute.mul_fpow
- \+ *theorem* matrix.commute.self_fpow
- \+ *lemma* matrix.fpow_add
- \+ *lemma* matrix.fpow_add_of_nonneg
- \+ *lemma* matrix.fpow_add_of_nonpos
- \+ *lemma* matrix.fpow_add_one
- \+ *lemma* matrix.fpow_add_one_of_ne_neg_one
- \+ *theorem* matrix.fpow_bit0'
- \+ *theorem* matrix.fpow_bit0
- \+ *theorem* matrix.fpow_bit1'
- \+ *theorem* matrix.fpow_bit1
- \+ *theorem* matrix.fpow_coe_nat
- \+ *theorem* matrix.fpow_mul'
- \+ *theorem* matrix.fpow_mul
- \+ *lemma* matrix.fpow_ne_zero_of_is_unit_det
- \+ *theorem* matrix.fpow_neg
- \+ *theorem* matrix.fpow_neg_coe_nat
- \+ *theorem* matrix.fpow_neg_mul_fpow_self
- \+ *lemma* matrix.fpow_neg_one
- \+ *theorem* matrix.fpow_one_add
- \+ *lemma* matrix.fpow_sub
- \+ *lemma* matrix.fpow_sub_one
- \+ *lemma* matrix.inv_fpow'
- \+ *theorem* matrix.inv_fpow
- \+ *theorem* matrix.inv_pow'
- \+ *lemma* matrix.is_unit_det_fpow_iff
- \+ *theorem* matrix.one_div_fpow
- \+ *theorem* matrix.one_div_pow
- \+ *theorem* matrix.one_fpow
- \+ *theorem* matrix.pow_inv_comm'
- \+ *theorem* matrix.pow_sub'
- \+ *theorem* matrix.semiconj_by.fpow_right
- \+ *lemma* matrix.units.coe_fpow
- \+ *lemma* matrix.units.coe_inv''
- \+ *lemma* matrix.zero_fpow
- \+ *lemma* matrix.zero_fpow_eq

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.nonsing_inv_cancel_or_zero



## [2021-09-28 07:29:17](https://github.com/leanprover-community/mathlib/commit/01adfd6)
chore(analysis/special_functions): add some `@[simp]` attrs ([#9423](https://github.com/leanprover-community/mathlib/pull/9423))
Add `@[simp]` attrs to `real.sin_add_pi` and similar lemmas.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* real.cos_add_int_mul_two_pi
- \+/\- *lemma* real.cos_add_nat_mul_two_pi
- \+/\- *lemma* real.cos_add_pi
- \+/\- *lemma* real.cos_add_two_pi
- \+/\- *lemma* real.cos_int_mul_two_pi
- \+/\- *lemma* real.cos_int_mul_two_pi_add_pi
- \+/\- *lemma* real.cos_int_mul_two_pi_sub
- \+/\- *lemma* real.cos_int_mul_two_pi_sub_pi
- \+/\- *lemma* real.cos_nat_mul_two_pi
- \+/\- *lemma* real.cos_nat_mul_two_pi_add_pi
- \+/\- *lemma* real.cos_nat_mul_two_pi_sub
- \+/\- *lemma* real.cos_nat_mul_two_pi_sub_pi
- \+/\- *lemma* real.cos_pi_sub
- \+/\- *lemma* real.cos_sub_int_mul_two_pi
- \+/\- *lemma* real.cos_sub_nat_mul_two_pi
- \+/\- *lemma* real.cos_sub_pi
- \+/\- *lemma* real.cos_sub_two_pi
- \+/\- *lemma* real.cos_two_pi_sub
- \+/\- *lemma* real.sin_add_int_mul_two_pi
- \+/\- *lemma* real.sin_add_nat_mul_two_pi
- \+/\- *lemma* real.sin_add_pi
- \+/\- *lemma* real.sin_add_two_pi
- \+/\- *lemma* real.sin_int_mul_pi
- \+/\- *lemma* real.sin_int_mul_two_pi_sub
- \+/\- *lemma* real.sin_nat_mul_pi
- \+/\- *lemma* real.sin_nat_mul_two_pi_sub
- \+/\- *lemma* real.sin_pi_sub
- \+/\- *lemma* real.sin_sub_int_mul_two_pi
- \+/\- *lemma* real.sin_sub_nat_mul_two_pi
- \+/\- *lemma* real.sin_sub_pi
- \+/\- *lemma* real.sin_sub_two_pi
- \+/\- *lemma* real.sin_two_pi_sub



## [2021-09-28 07:29:16](https://github.com/leanprover-community/mathlib/commit/6108616)
doc(*): remove docstrings from copyright headers ([#9411](https://github.com/leanprover-community/mathlib/pull/9411))
This moves/removes the docs from the copyright header that are enough to make for the missing module docstring/redundant with the module docstring.
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean


Modified src/algebra/direct_sum/module.lean


Modified src/category_theory/category/Kleisli.lean


Modified src/data/lazy_list/basic.lean


Modified src/data/list/sigma.lean


Modified src/data/matrix/notation.lean


Modified src/data/nat/prime.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/order/preorder_hom.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/scc.lean


Modified src/tactic/simp_rw.lean


Modified src/tactic/tfae.lean


Modified src/topology/algebra/localization.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/compact_open.lean


Modified test/conv/conv.lean


Modified test/finish1.lean


Modified test/finish2.lean


Modified test/finish3.lean


Modified test/norm_num.lean


Modified test/norm_num_ext.lean


Modified test/simp_rw.lean




## [2021-09-28 07:29:14](https://github.com/leanprover-community/mathlib/commit/36c09f7)
doc(order/*): use "monotone" / "antitone" in place of "monotonically increasing" / "monotonically decreasing" ([#9408](https://github.com/leanprover-community/mathlib/pull/9408))
This PR cleans up the references to monotone and antitone function in lemmas and docstrings.
It doesn't touch anything beyond the docstrings.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/p_series.lean


Modified src/data/ordmap/ordnode.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/directed.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/extr.lean


Modified src/order/lattice.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/order_iso_nat.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/metric_space/holder.lean


Modified src/topology/uniform_space/cauchy.lean




## [2021-09-28 07:29:13](https://github.com/leanprover-community/mathlib/commit/22f2409)
chore(measure_theory/integral/interval_integral): change of variables for normed-space target ([#9350](https://github.com/leanprover-community/mathlib/pull/9350))
Re-state change of variables for `interval_integral` for a function with target a real normed space `E`, rather than just `ℝ`.  The proofs are exactly the same.
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+ *theorem* interval_integral.integral_comp_smul_deriv''
- \+ *theorem* interval_integral.integral_comp_smul_deriv'
- \+ *theorem* interval_integral.integral_comp_smul_deriv
- \+ *theorem* interval_integral.integral_deriv_comp_smul_deriv'
- \+ *theorem* interval_integral.integral_deriv_comp_smul_deriv



## [2021-09-28 06:33:23](https://github.com/leanprover-community/mathlib/commit/1db626e)
feat(analysis/normed_space/is_bounded_bilinear_map): direct proof of continuity ([#9390](https://github.com/leanprover-community/mathlib/pull/9390))
Previously `is_bounded_bilinear_map.continuous`, the continuity of a bounded bilinear map, was deduced from its differentiability and lived in `analysis.calculus.fderiv`.  This PR gives a direct proof so it can live in `analysis.normed_space.bounded_linear_maps`.
Two consequences of this lemma are also moved earlier in the hierarchy:
- `continuous_linear_equiv.is_open`, the openness of the set of continuous linear equivalences in the space of continuous linear maps, moves from `analysis.calculus.fderiv` to `analysis.normed_space.bounded_linear_maps`
- `continuous_inner`, the continuity of the inner product, moves from `analysis.inner_product_space.calculus` to `analysis.inner_product_space.basic`.
Previously discussed at
https://github.com/leanprover-community/mathlib/pull/4407#pullrequestreview-506198222
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \- *lemma* is_bounded_bilinear_map.continuous
- \- *lemma* is_bounded_bilinear_map.continuous_left
- \- *lemma* is_bounded_bilinear_map.continuous_right

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* continuous.inner
- \+ *lemma* continuous_at.inner
- \+ *lemma* continuous_inner
- \+ *lemma* continuous_on.inner
- \+ *lemma* continuous_within_at.inner
- \+ *lemma* filter.tendsto.inner
- \+ *lemma* is_bounded_bilinear_map_inner

Modified src/analysis/inner_product_space/calculus.lean
- \- *lemma* continuous.inner
- \- *lemma* continuous_at.inner
- \- *lemma* continuous_inner
- \- *lemma* continuous_on.inner
- \- *lemma* continuous_within_at.inner
- \- *lemma* filter.tendsto.inner
- \- *lemma* is_bounded_bilinear_map_inner

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map.continuous
- \+ *lemma* is_bounded_bilinear_map.continuous_left
- \+ *lemma* is_bounded_bilinear_map.continuous_right



## [2021-09-28 03:23:06](https://github.com/leanprover-community/mathlib/commit/4b5bf56)
feat(measure_theory/integral/interval_integral): one more FTC-2 ([#9409](https://github.com/leanprover-community/mathlib/pull/9409))
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_eq_integral_of_support_subset
- \+ *theorem* interval_integral.integral_eq_sub_of_has_deriv_at_of_tendsto

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at_update_same
- \+ *lemma* filter.eventually_eq.congr_continuous_within_at

Modified src/topology/separation.lean
- \+ *lemma* continuous_on_update_iff
- \+ *lemma* continuous_within_at_update_of_ne
- \+ *lemma* ne.nhds_within_compl_singleton



## [2021-09-28 01:02:53](https://github.com/leanprover-community/mathlib/commit/8c5d93b)
feat(analysis/special_functions/complex/log): `exp ⁻¹' s` is countable ([#9410](https://github.com/leanprover-community/mathlib/pull/9410))
Also prove that the preimage of a countable set under an injective map
is countable.
#### Estimated changes
Modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* complex.countable_preimage_exp
- \+/\- *lemma* complex.range_exp

Modified src/data/set/countable.lean
- \+ *lemma* set.countable.preimage_of_inj_on
- \+ *lemma* set.maps_to.countable_of_inj_on

Modified src/data/set/function.lean
- \+ *lemma* set.injective_cod_restrict



## [2021-09-28 01:02:52](https://github.com/leanprover-community/mathlib/commit/b21bc97)
feat(analysis/special_functions): limits of `arg` and `log` at a real negative ([#9406](https://github.com/leanprover-community/mathlib/pull/9406))
Also add a `can_lift ℂ ℝ` instance.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.continuous_within_at_arg_of_re_neg_of_im_zero
- \+ *lemma* complex.tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero
- \+ *lemma* complex.tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero

Modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* complex.continuous_within_at_log_of_re_neg_of_im_zero
- \+ *lemma* complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero
- \+ *lemma* complex.tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero

Modified src/data/complex/basic.lean




## [2021-09-27 22:35:23](https://github.com/leanprover-community/mathlib/commit/8279510)
feat(*): Clean up some misstated lemmas about algebra ([#9417](https://github.com/leanprover-community/mathlib/pull/9417))
Similar to [#9395](https://github.com/leanprover-community/mathlib/pull/9395) clean up a few lemmas whose statement doesn't match the name / docstring about algebraic things, all of these are duplicates of other lemmas, so look like copy paste errors.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+/\- *lemma* mul_hom.cancel_left

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Modified src/data/int/parity.lean
- \+/\- *lemma* int.is_compl_even_odd

Modified src/linear_algebra/matrix/symmetric.lean




## [2021-09-27 20:53:13](https://github.com/leanprover-community/mathlib/commit/0d37fd6)
feat(data/polynomial/algebra_map): aeval_tower ([#9250](https://github.com/leanprover-community/mathlib/pull/9250))
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \- *lemma* alg_hom.commutes_of_tower
- \+ *lemma* alg_hom.map_algebra_map

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* polynomial.C_eq_algebra_map
- \+ *def* polynomial.aeval_tower
- \+ *lemma* polynomial.aeval_tower_C
- \+ *lemma* polynomial.aeval_tower_X
- \+ *lemma* polynomial.aeval_tower_algebra_map
- \+ *lemma* polynomial.aeval_tower_comp_C
- \+ *lemma* polynomial.aeval_tower_comp_algebra_map
- \+ *lemma* polynomial.aeval_tower_comp_to_alg_hom
- \+ *lemma* polynomial.aeval_tower_id
- \+ *lemma* polynomial.aeval_tower_of_id
- \+ *lemma* polynomial.aeval_tower_to_alg_hom
- \+ *lemma* polynomial.alg_hom_ext'



## [2021-09-27 17:49:20](https://github.com/leanprover-community/mathlib/commit/f181d81)
chore(analysis/special_functions/exp_log): add some missing dot notation lemmas ([#9405](https://github.com/leanprover-community/mathlib/pull/9405))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* continuous.cexp
- \+ *lemma* continuous_at.cexp
- \+ *lemma* continuous_on.cexp
- \+ *lemma* continuous_within_at.cexp
- \+ *lemma* filter.tendsto.cexp



## [2021-09-27 17:49:19](https://github.com/leanprover-community/mathlib/commit/9175158)
refactor(analysis/convex/function): generalize lemmas about convexity/concavity of functions, prove concave Jensen ([#9356](https://github.com/leanprover-community/mathlib/pull/9356))
`convex_on` and `concave_on` are currently only defined for real vector spaces. This generalizes ℝ to an arbitrary `ordered_semiring`. As a result, we now have the concave Jensen inequality for free.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.combo_self

Modified src/analysis/convex/combination.lean


Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on.add
- \+/\- *lemma* concave_on.comp_affine_map
- \+/\- *lemma* concave_on.comp_linear_map
- \+ *lemma* concave_on.concave_ge
- \- *lemma* concave_on.concave_le
- \+/\- *lemma* concave_on.convex_hypograph
- \+/\- *lemma* concave_on.convex_lt
- \+ *lemma* concave_on.exists_le_of_center_mass
- \+ *lemma* concave_on.exists_le_of_mem_convex_hull
- \+/\- *lemma* concave_on.inf
- \+ *lemma* concave_on.le_map_center_mass
- \+ *lemma* concave_on.le_map_sum
- \+/\- *lemma* concave_on.le_on_segment'
- \+/\- *lemma* concave_on.le_on_segment
- \+/\- *lemma* concave_on.le_right_of_left_le'
- \+/\- *lemma* concave_on.le_right_of_left_le
- \+/\- *lemma* concave_on.left_le_of_le_right'
- \+/\- *lemma* concave_on.left_le_of_le_right
- \+/\- *lemma* concave_on.slope_mono_adjacent
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* concave_on.subset
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* concave_on.translate_right
- \+/\- *def* concave_on
- \+/\- *lemma* concave_on_const
- \+/\- *lemma* concave_on_id
- \+/\- *lemma* concave_on_iff_convex_hypograph
- \+ *lemma* concave_on_iff_slope_mono_adjacent
- \+ *lemma* concave_on_of_slope_mono_adjacent
- \- *lemma* concave_on_real_iff_slope_mono_adjacent
- \- *lemma* concave_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.comp_affine_map
- \+/\- *lemma* convex_on.comp_linear_map
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* convex_on.exists_ge_of_center_mass
- \+/\- *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+/\- *lemma* convex_on.le_left_of_right_le'
- \+/\- *lemma* convex_on.le_left_of_right_le
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.le_right_of_left_le'
- \+/\- *lemma* convex_on.le_right_of_left_le
- \+/\- *lemma* convex_on.map_center_mass_le
- \+/\- *lemma* convex_on.map_sum_le
- \+/\- *lemma* convex_on.slope_mono_adjacent
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.sup
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+/\- *def* convex_on
- \+/\- *lemma* convex_on_const
- \+/\- *lemma* convex_on_id
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+ *lemma* convex_on_iff_slope_mono_adjacent
- \+ *lemma* convex_on_of_slope_mono_adjacent
- \- *lemma* convex_on_real_iff_slope_mono_adjacent
- \- *lemma* convex_on_real_of_slope_mono_adjacent
- \+/\- *lemma* linear_map.concave_on
- \+/\- *lemma* linear_map.convex_on
- \+/\- *lemma* linear_order.concave_on_of_lt
- \+/\- *lemma* linear_order.convex_on_of_lt
- \+/\- *lemma* neg_concave_on_iff
- \+/\- *lemma* neg_convex_on_iff

Modified src/analysis/convex/integral.lean




## [2021-09-27 13:07:20](https://github.com/leanprover-community/mathlib/commit/5dfb76f)
feat(analysis/calculus/fderiv): generalize `const_smul` lemmas ([#9399](https://github.com/leanprover-community/mathlib/pull/9399))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable.const_smul
- \+/\- *lemma* differentiable_at.const_smul
- \+/\- *lemma* differentiable_on.const_smul
- \+/\- *lemma* differentiable_within_at.const_smul
- \+/\- *lemma* fderiv_const_smul
- \+/\- *theorem* has_fderiv_at.const_smul
- \+/\- *theorem* has_fderiv_at_filter.const_smul
- \+/\- *theorem* has_fderiv_within_at.const_smul
- \+/\- *theorem* has_strict_fderiv_at.const_smul



## [2021-09-27 13:07:18](https://github.com/leanprover-community/mathlib/commit/954896a)
feat(data/nat/choose/cast): Cast of binomial coefficients equals a Pochhammer polynomial ([#9394](https://github.com/leanprover-community/mathlib/pull/9394))
This adds some glue between `nat.factorial`/`nat.asc_factorial`/`nat.desc_factorial` and `pochhammer` to provide some API to calculate binomial coefficients in a semiring. For example, `n.choose 2` as a real is `n * (n - 1)/2`.
I also move files as such:
* create `data.nat.choose.cast`
* create `data.nat.factorial.cast`
* rename `data.nat.factorial` to `data.nat.factorial.basic`
#### Estimated changes
Modified src/data/nat/choose/basic.lean


Added src/data/nat/choose/cast.lean
- \+ *lemma* nat.cast_add_choose
- \+ *lemma* nat.cast_choose
- \+ *lemma* nat.cast_choose_eq_pochhammer_div
- \+ *lemma* nat.cast_choose_two

Modified src/data/nat/choose/default.lean


Modified src/data/nat/choose/dvd.lean
- \- *lemma* nat.cast_add_choose
- \- *lemma* nat.cast_choose

Renamed src/data/nat/factorial.lean to src/data/nat/factorial/basic.lean
- \+ *theorem* nat.factorial_two

Added src/data/nat/factorial/cast.lean
- \+ *lemma* nat.cast_asc_factorial
- \+ *lemma* nat.cast_desc_factorial
- \+ *lemma* nat.cast_desc_factorial_two
- \+ *lemma* nat.cast_factorial

Modified src/data/polynomial/hasse_deriv.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_nat_eq_desc_factorial
- \+ *lemma* pochhammer_succ_eval



## [2021-09-27 13:07:17](https://github.com/leanprover-community/mathlib/commit/9a30f8c)
refactor(data/fin): drop `fin.cast_add_right` ([#9371](https://github.com/leanprover-community/mathlib/pull/9371))
This was a duplicate of `fin.nat_add`. Also simplify some definitions of equivalences.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *lemma* fin_add_flip_apply_cast_add
- \- *lemma* fin_add_flip_apply_left
- \+ *lemma* fin_add_flip_apply_mk_left
- \+ *lemma* fin_add_flip_apply_mk_right
- \+ *lemma* fin_add_flip_apply_nat_add
- \- *lemma* fin_add_flip_apply_right
- \+ *lemma* fin_succ_equiv'_succ_above
- \+ *lemma* fin_succ_equiv'_symm_some
- \+/\- *lemma* fin_sum_fin_equiv_symm_apply_cast_add
- \- *lemma* fin_sum_fin_equiv_symm_apply_cast_add_right
- \- *lemma* fin_sum_fin_equiv_symm_apply_left
- \+ *lemma* fin_sum_fin_equiv_symm_apply_nat_add
- \- *lemma* fin_sum_fin_equiv_symm_apply_right

Modified src/data/fin.lean
- \+/\- *def* fin.add_cases
- \+ *lemma* fin.add_nat_mk
- \+ *lemma* fin.add_nat_sub_nat
- \+ *lemma* fin.cast_add_cast_lt
- \+ *lemma* fin.cast_add_nat
- \- *def* fin.cast_add_right
- \+ *lemma* fin.cast_lt_cast_add
- \+ *lemma* fin.cast_nat_add
- \- *lemma* fin.coe_cast_add_right
- \- *lemma* fin.le_cast_add_right
- \+ *lemma* fin.le_coe_add_nat
- \+ *lemma* fin.le_coe_nat_add
- \+ *lemma* fin.nat_add_mk
- \+ *lemma* fin.nat_add_sub_nat_cast
- \+ *lemma* fin.sub_nat_add_nat
- \+ *lemma* fin.sub_nat_mk



## [2021-09-27 10:29:19](https://github.com/leanprover-community/mathlib/commit/850784c)
chore(order/*): rename `strict_mono_{incr,decr}_on` to `strict_{mono,anti}_on` ([#9401](https://github.com/leanprover-community/mathlib/pull/9401))
This was done as a direct find and replace
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/algebra/group_power/order.lean
- \- *theorem* strict_mono_incr_on_pow
- \+ *theorem* strict_mono_on_pow

Modified src/algebra/order/field.lean
- \+ *lemma* one_div_strict_anti_on
- \- *lemma* one_div_strict_mono_decr_on

Modified src/algebra/order/ring.lean
- \- *lemma* strict_mono_incr_on_mul_self
- \+ *lemma* strict_mono_on_mul_self

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.strict_anti_on_log
- \- *lemma* real.strict_mono_decr_on_log
- \- *lemma* real.strict_mono_incr_on_log
- \+ *lemma* real.strict_mono_on_log

Modified src/analysis/special_functions/trigonometric/arctan.lean


Modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* real.inj_on_cos
- \+ *lemma* real.strict_anti_on_cos
- \- *lemma* real.strict_mono_decr_on_cos
- \- *lemma* real.strict_mono_incr_on_sin
- \- *lemma* real.strict_mono_incr_on_tan
- \+ *lemma* real.strict_mono_on_sin
- \+ *lemma* real.strict_mono_on_tan

Modified src/analysis/special_functions/trigonometric/inverse.lean
- \+/\- *lemma* real.arccos_inj_on
- \+/\- *lemma* real.inj_on_arcsin
- \+ *lemma* real.strict_anti_on_arccos
- \- *lemma* real.strict_mono_decr_on_arccos
- \- *lemma* real.strict_mono_incr_on_arcsin
- \+ *lemma* real.strict_mono_on_arcsin

Modified src/data/set/function.lean
- \+ *lemma* strict_anti_on.inj_on
- \- *lemma* strict_mono.comp_strict_mono_incr_on
- \+ *lemma* strict_mono.comp_strict_mono_on
- \- *lemma* strict_mono_decr_on.inj_on
- \- *lemma* strict_mono_incr_on.comp
- \- *lemma* strict_mono_incr_on.inj_on
- \+ *lemma* strict_mono_on.comp
- \+ *lemma* strict_mono_on.inj_on

Modified src/data/set/intervals/proj_Icc.lean
- \- *lemma* set.strict_mono_incr_on_proj_Icc
- \+ *lemma* set.strict_mono_on_proj_Icc
- \- *lemma* strict_mono.strict_mono_incr_on_Icc_extend
- \+ *lemma* strict_mono.strict_mono_on_Icc_extend

Modified src/order/basic.lean
- \+ *lemma* strict_anti_on.le_iff_le
- \+ *lemma* strict_anti_on.lt_iff_lt
- \+ *def* strict_anti_on
- \- *lemma* strict_mono_decr_on.le_iff_le
- \- *lemma* strict_mono_decr_on.lt_iff_lt
- \- *def* strict_mono_decr_on
- \- *lemma* strict_mono_incr_on.le_iff_le
- \- *lemma* strict_mono_incr_on.lt_iff_lt
- \- *def* strict_mono_incr_on
- \+ *lemma* strict_mono_on.le_iff_le
- \+ *lemma* strict_mono_on.lt_iff_lt
- \+ *def* strict_mono_on

Modified src/order/rel_iso.lean


Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* strict_mono_incr_on.continuous_at_left_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_incr_on.continuous_at_left_of_exists_between
- \- *lemma* strict_mono_incr_on.continuous_at_left_of_image_mem_nhds_within
- \- *lemma* strict_mono_incr_on.continuous_at_left_of_surj_on
- \- *lemma* strict_mono_incr_on.continuous_at_of_closure_image_mem_nhds
- \- *lemma* strict_mono_incr_on.continuous_at_of_exists_between
- \- *lemma* strict_mono_incr_on.continuous_at_of_image_mem_nhds
- \- *lemma* strict_mono_incr_on.continuous_at_right_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_incr_on.continuous_at_right_of_exists_between
- \- *lemma* strict_mono_incr_on.continuous_at_right_of_image_mem_nhds_within
- \- *lemma* strict_mono_incr_on.continuous_at_right_of_surj_on
- \+ *lemma* strict_mono_on.continuous_at_left_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_left_of_exists_between
- \+ *lemma* strict_mono_on.continuous_at_left_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_left_of_surj_on
- \+ *lemma* strict_mono_on.continuous_at_of_closure_image_mem_nhds
- \+ *lemma* strict_mono_on.continuous_at_of_exists_between
- \+ *lemma* strict_mono_on.continuous_at_of_image_mem_nhds
- \+ *lemma* strict_mono_on.continuous_at_right_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_right_of_exists_between
- \+ *lemma* strict_mono_on.continuous_at_right_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_right_of_surj_on



## [2021-09-27 10:29:16](https://github.com/leanprover-community/mathlib/commit/1472799)
chore(order): globally replace "antimono" with "antitone" ([#9400](https://github.com/leanprover-community/mathlib/pull/9400))
This was done with the regex `(?<=\b|_)antimono(?=\b|_)`
#### Estimated changes
Modified src/algebra/lie/solvable.lean
- \- *lemma* lie_algebra.derived_series_of_ideal_antimono
- \+ *lemma* lie_algebra.derived_series_of_ideal_antitone

Modified src/analysis/calculus/mean_value.lean
- \- *theorem* antimono_of_deriv_nonpos
- \+ *theorem* antitone_of_deriv_nonpos
- \- *theorem* concave_on_of_deriv_antimono
- \+ *theorem* concave_on_of_deriv_antitone
- \- *theorem* concave_on_univ_of_deriv_antimono
- \+ *theorem* concave_on_univ_of_deriv_antitone
- \- *theorem* convex.antimono_of_deriv_nonpos
- \+ *theorem* convex.antitone_of_deriv_nonpos
- \- *theorem* convex.strict_antimono_of_deriv_neg
- \+ *theorem* convex.strict_antitone_of_deriv_neg
- \- *theorem* strict_antimono_of_deriv_neg
- \+ *theorem* strict_antitone_of_deriv_neg

Modified src/analysis/special_functions/integrals.lean
- \- *lemma* integral_sin_pow_antimono
- \+ *lemma* integral_sin_pow_antitone

Modified src/data/real/pi/wallis.lean


Modified src/group_theory/nilpotent.lean
- \- *lemma* lower_central_series_antimono
- \+ *lemma* lower_central_series_antitone

Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* ae_measurable_restrict_of_antimono_on
- \+ *lemma* ae_measurable_restrict_of_antitone_on
- \- *lemma* measurable_of_antimono
- \+ *lemma* measurable_of_antitone

Modified src/measure_theory/function/ess_sup.lean
- \- *lemma* ess_inf_antimono_measure
- \+ *lemma* ess_inf_antitone_measure

Modified src/measure_theory/function/lp_space.lean
- \- *lemma* measure_theory.Lp.antimono
- \+ *lemma* measure_theory.Lp.antitone

Modified src/measure_theory/integral/integrable_on.lean
- \- *lemma* integrable_on_compact_of_antimono
- \- *lemma* integrable_on_compact_of_antimono_on
- \+ *lemma* integrable_on_compact_of_antitone
- \+ *lemma* integrable_on_compact_of_antitone_on

Modified src/measure_theory/integral/interval_integral.lean
- \- *lemma* interval_integrable_of_antimono
- \- *lemma* interval_integrable_of_antimono_on
- \+ *lemma* interval_integrable_of_antitone
- \+ *lemma* interval_integrable_of_antitone_on

Modified src/measure_theory/integral/set_integral.lean
- \- *lemma* measure_theory.tendsto_set_integral_of_antimono
- \+ *lemma* measure_theory.tendsto_set_integral_of_antitone

Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \- *lemma* is_compl.antimono
- \+ *lemma* is_compl.antitone

Modified src/order/filter/at_top_bot.lean
- \- *lemma* filter.has_antimono_basis.tendsto
- \+ *lemma* filter.has_antitone_basis.tendsto

Modified src/order/filter/bases.lean
- \- *lemma* filter.antimono_seq_of_seq
- \+ *lemma* filter.antitone_seq_of_seq
- \- *lemma* filter.is_countably_generated.exists_antimono_basis
- \- *lemma* filter.is_countably_generated.exists_antimono_seq'
- \- *lemma* filter.is_countably_generated.exists_antimono_subbasis
- \+ *lemma* filter.is_countably_generated.exists_antitone_basis
- \+ *lemma* filter.is_countably_generated.exists_antitone_seq'
- \+ *lemma* filter.is_countably_generated.exists_antitone_subbasis
- \- *lemma* filter.is_countably_generated_iff_exists_antimono_basis
- \+ *lemma* filter.is_countably_generated_iff_exists_antitone_basis

Modified src/order/filter/extr.lean
- \- *lemma* is_extr_filter.comp_antimono
- \+ *lemma* is_extr_filter.comp_antitone
- \- *lemma* is_extr_on.comp_antimono
- \+ *lemma* is_extr_on.comp_antitone
- \- *lemma* is_max_filter.comp_antimono
- \+ *lemma* is_max_filter.comp_antitone
- \- *lemma* is_max_on.comp_antimono
- \+ *lemma* is_max_on.comp_antitone
- \- *lemma* is_min_filter.comp_antimono
- \+ *lemma* is_min_filter.comp_antitone
- \- *lemma* is_min_on.comp_antimono
- \+ *lemma* is_min_on.comp_antitone

Modified src/order/filter/indicator_function.lean
- \- *lemma* tendsto_indicator_of_antimono
- \+ *lemma* tendsto_indicator_of_antitone

Modified src/topology/G_delta.lean


Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* exists_seq_strict_antimono_tendsto'
- \- *lemma* exists_seq_strict_antimono_tendsto
- \+ *lemma* exists_seq_strict_antitone_tendsto'
- \+ *lemma* exists_seq_strict_antitone_tendsto

Modified src/topology/local_extr.lean
- \- *lemma* is_local_extr.comp_antimono
- \+ *lemma* is_local_extr.comp_antitone
- \- *lemma* is_local_extr_on.comp_antimono
- \+ *lemma* is_local_extr_on.comp_antitone
- \- *lemma* is_local_max.comp_antimono
- \+ *lemma* is_local_max.comp_antitone
- \- *lemma* is_local_max_on.comp_antimono
- \+ *lemma* is_local_max_on.comp_antitone
- \- *lemma* is_local_min.comp_antimono
- \+ *lemma* is_local_min.comp_antitone
- \- *lemma* is_local_min_on.comp_antimono
- \+ *lemma* is_local_min_on.comp_antitone

Modified src/topology/semicontinuous.lean
- \- *lemma* continuous.comp_lower_semicontinuous_antimono
- \+ *lemma* continuous.comp_lower_semicontinuous_antitone
- \- *lemma* continuous.comp_lower_semicontinuous_on_antimono
- \+ *lemma* continuous.comp_lower_semicontinuous_on_antitone
- \- *lemma* continuous.comp_upper_semicontinuous_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous_antitone
- \- *lemma* continuous.comp_upper_semicontinuous_on_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous_on_antitone
- \- *lemma* continuous_at.comp_lower_semicontinuous_at_antimono
- \+ *lemma* continuous_at.comp_lower_semicontinuous_at_antitone
- \- *lemma* continuous_at.comp_lower_semicontinuous_within_at_antimono
- \+ *lemma* continuous_at.comp_lower_semicontinuous_within_at_antitone
- \- *lemma* continuous_at.comp_upper_semicontinuous_at_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_at_antitone
- \- *lemma* continuous_at.comp_upper_semicontinuous_within_at_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_within_at_antitone

Modified src/topology/sequences.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean




## [2021-09-27 10:29:14](https://github.com/leanprover-community/mathlib/commit/d1c68ef)
docs(docker): adjust readme to reflect that the PR was merged ([#9303](https://github.com/leanprover-community/mathlib/pull/9303))
#### Estimated changes
Modified .docker/README.md




## [2021-09-27 09:34:51](https://github.com/leanprover-community/mathlib/commit/cafd6fb)
chore(measure_theory/decomposition/lebesgue): rename `radon_nikodym_deriv` to `rn_deriv` ([#9386](https://github.com/leanprover-community/mathlib/pull/9386))
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean
- \- *theorem* measure_theory.measure.eq_radon_nikodym_deriv
- \+ *theorem* measure_theory.measure.eq_rn_deriv
- \- *lemma* measure_theory.measure.lintegral_radon_nikodym_deriv_lt_top
- \+ *lemma* measure_theory.measure.lintegral_rn_deriv_lt_top
- \- *lemma* measure_theory.measure.measurable_radon_nikodym_deriv
- \+ *lemma* measure_theory.measure.measurable_rn_deriv
- \- *def* measure_theory.measure.radon_nikodym_deriv
- \+ *def* measure_theory.measure.rn_deriv
- \- *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_le
- \+ *lemma* measure_theory.measure.with_density_rn_deriv_le
- \- *theorem* measure_theory.signed_measure.eq_radon_nikodym_deriv
- \+ *theorem* measure_theory.signed_measure.eq_rn_deriv
- \- *lemma* measure_theory.signed_measure.integrable_radon_nikodym_deriv
- \+ *lemma* measure_theory.signed_measure.integrable_rn_deriv
- \- *lemma* measure_theory.signed_measure.measurable_radon_nikodym_deriv
- \+ *lemma* measure_theory.signed_measure.measurable_rn_deriv
- \- *def* measure_theory.signed_measure.radon_nikodym_deriv
- \- *lemma* measure_theory.signed_measure.radon_nikodym_deriv_add
- \- *lemma* measure_theory.signed_measure.radon_nikodym_deriv_neg
- \- *lemma* measure_theory.signed_measure.radon_nikodym_deriv_smul
- \- *lemma* measure_theory.signed_measure.radon_nikodym_deriv_sub
- \+ *def* measure_theory.signed_measure.rn_deriv
- \+ *lemma* measure_theory.signed_measure.rn_deriv_add
- \+ *lemma* measure_theory.signed_measure.rn_deriv_neg
- \+ *lemma* measure_theory.signed_measure.rn_deriv_smul
- \+ *lemma* measure_theory.signed_measure.rn_deriv_sub
- \- *theorem* measure_theory.signed_measure.singular_part_add_with_density_radon_nikodym_deriv_eq
- \+ *theorem* measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq

Modified src/measure_theory/decomposition/radon_nikodym.lean
- \- *theorem* measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
- \+ *theorem* measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq
- \- *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_eq
- \- *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_to_real_eq
- \+ *lemma* measure_theory.measure.with_density_rn_deriv_eq
- \+ *lemma* measure_theory.measure.with_density_rn_deriv_to_real_eq
- \- *theorem* measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_radon_nikodym_deriv_eq
- \+ *theorem* measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq
- \- *theorem* measure_theory.signed_measure.with_densityᵥ_radon_nikodym_deriv_eq
- \+ *theorem* measure_theory.signed_measure.with_densityᵥ_rn_deriv_eq



## [2021-09-27 04:20:23](https://github.com/leanprover-community/mathlib/commit/a4b92a3)
refactor(analysis/special_functions/trigonometric): split file ([#9340](https://github.com/leanprover-community/mathlib/pull/9340))
Another mammoth file, cut into several pieces.
#### Estimated changes
Modified archive/100-theorems-list/57_herons_formula.lean


Modified archive/imo/imo1962_q4.lean


Modified src/analysis/complex/roots_of_unity.lean


Modified src/analysis/special_functions/arsinh.lean


Added src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_I
- \+ *lemma* complex.arg_cos_add_sin_mul_I
- \+ *lemma* complex.arg_eq_arg_iff
- \+ *lemma* complex.arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \+ *lemma* complex.arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \+ *lemma* complex.arg_eq_pi_iff
- \+ *lemma* complex.arg_le_pi
- \+ *lemma* complex.arg_neg_I
- \+ *lemma* complex.arg_neg_one
- \+ *lemma* complex.arg_of_real_of_neg
- \+ *lemma* complex.arg_of_real_of_nonneg
- \+ *lemma* complex.arg_one
- \+ *lemma* complex.arg_real_mul
- \+ *lemma* complex.arg_zero
- \+ *lemma* complex.cos_arg
- \+ *lemma* complex.ext_abs_arg
- \+ *lemma* complex.neg_pi_lt_arg
- \+ *lemma* complex.sin_arg
- \+ *lemma* complex.tan_arg

Added src/analysis/special_functions/complex/log.lean
- \+ *lemma* complex.exists_eq_mul_self
- \+ *lemma* complex.exists_pow_nat_eq
- \+ *lemma* complex.exp_eq_exp_iff_exists_int
- \+ *lemma* complex.exp_eq_exp_iff_exp_sub_eq_one
- \+ *lemma* complex.exp_eq_one_iff
- \+ *lemma* complex.exp_inj_of_neg_pi_lt_of_le_pi
- \+ *def* complex.exp_local_homeomorph
- \+ *lemma* complex.exp_log
- \+ *lemma* complex.has_strict_deriv_at_log
- \+ *lemma* complex.log_I
- \+ *lemma* complex.log_exp
- \+ *lemma* complex.log_im
- \+ *lemma* complex.log_im_le_pi
- \+ *lemma* complex.log_neg_I
- \+ *lemma* complex.log_neg_one
- \+ *lemma* complex.log_of_real_re
- \+ *lemma* complex.log_one
- \+ *lemma* complex.log_re
- \+ *lemma* complex.log_zero
- \+ *lemma* complex.neg_pi_lt_log_im
- \+ *lemma* complex.of_real_log
- \+ *lemma* complex.range_exp
- \+ *lemma* complex.times_cont_diff_at_log
- \+ *lemma* complex.two_pi_I_ne_zero
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

Modified src/analysis/special_functions/pow.lean


Added src/analysis/special_functions/trigonometric/arctan.lean
- \+ *lemma* deriv_arctan
- \+ *lemma* deriv_within_arctan
- \+ *lemma* differentiable.arctan
- \+ *lemma* differentiable_at.arctan
- \+ *lemma* differentiable_on.arctan
- \+ *lemma* differentiable_within_at.arctan
- \+ *lemma* fderiv_arctan
- \+ *lemma* fderiv_within_arctan
- \+ *lemma* has_deriv_at.arctan
- \+ *lemma* has_deriv_within_at.arctan
- \+ *lemma* has_fderiv_at.arctan
- \+ *lemma* has_fderiv_within_at.arctan
- \+ *lemma* has_strict_deriv_at.arctan
- \+ *lemma* has_strict_fderiv_at.arctan
- \+ *lemma* real.arcsin_eq_arctan
- \+ *lemma* real.arctan_eq_arcsin
- \+ *lemma* real.arctan_eq_of_tan_eq
- \+ *lemma* real.arctan_lt_pi_div_two
- \+ *lemma* real.arctan_mem_Ioo
- \+ *lemma* real.arctan_neg
- \+ *lemma* real.arctan_one
- \+ *lemma* real.arctan_tan
- \+ *lemma* real.arctan_zero
- \+ *lemma* real.coe_tan_local_homeomorph
- \+ *lemma* real.coe_tan_local_homeomorph_symm
- \+ *lemma* real.continuous_arctan
- \+ *lemma* real.continuous_at_arctan
- \+ *lemma* real.continuous_at_tan
- \+ *lemma* real.continuous_on_tan
- \+ *lemma* real.continuous_on_tan_Ioo
- \+ *lemma* real.continuous_tan
- \+ *lemma* real.cos_arctan
- \+ *lemma* real.cos_arctan_pos
- \+ *lemma* real.cos_sq_arctan
- \+ *lemma* real.deriv_arctan
- \+ *lemma* real.deriv_tan
- \+ *lemma* real.differentiable_arctan
- \+ *lemma* real.differentiable_at_arctan
- \+ *lemma* real.differentiable_at_tan
- \+ *lemma* real.differentiable_at_tan_of_mem_Ioo
- \+ *lemma* real.has_deriv_at_arctan
- \+ *lemma* real.has_deriv_at_tan
- \+ *lemma* real.has_deriv_at_tan_of_mem_Ioo
- \+ *lemma* real.has_strict_deriv_at_arctan
- \+ *lemma* real.has_strict_deriv_at_tan
- \+ *lemma* real.image_tan_Ioo
- \+ *lemma* real.neg_pi_div_two_lt_arctan
- \+ *lemma* real.sin_arctan
- \+ *lemma* real.surj_on_tan
- \+ *lemma* real.tan_add'
- \+ *lemma* real.tan_add
- \+ *lemma* real.tan_arctan
- \+ *lemma* real.tan_eq_zero_iff
- \+ *lemma* real.tan_int_mul_pi_div_two
- \+ *def* real.tan_local_homeomorph
- \+ *lemma* real.tan_ne_zero_iff
- \+ *def* real.tan_order_iso
- \+ *lemma* real.tan_surjective
- \+ *lemma* real.tan_two_mul
- \+ *lemma* real.tendsto_abs_tan_at_top
- \+ *lemma* real.tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* real.times_cont_diff_arctan
- \+ *lemma* real.times_cont_diff_at_tan
- \+ *lemma* times_cont_diff.arctan
- \+ *lemma* times_cont_diff_at.arctan
- \+ *lemma* times_cont_diff_on.arctan
- \+ *lemma* times_cont_diff_within_at.arctan

Renamed src/analysis/special_functions/trigonometric.lean to src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* complex.arg_I
- \- *lemma* complex.arg_cos_add_sin_mul_I
- \- *lemma* complex.arg_eq_arg_iff
- \- *lemma* complex.arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \- *lemma* complex.arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \- *lemma* complex.arg_eq_pi_iff
- \- *lemma* complex.arg_le_pi
- \- *lemma* complex.arg_neg_I
- \- *lemma* complex.arg_neg_one
- \- *lemma* complex.arg_of_real_of_neg
- \- *lemma* complex.arg_of_real_of_nonneg
- \- *lemma* complex.arg_one
- \- *lemma* complex.arg_real_mul
- \- *lemma* complex.arg_zero
- \- *lemma* complex.continuous_at_tan
- \- *lemma* complex.continuous_on_tan
- \- *lemma* complex.continuous_tan
- \- *lemma* complex.cos_arg
- \- *lemma* complex.cos_eq_cos_iff
- \- *lemma* complex.cos_eq_iff_quadratic
- \- *theorem* complex.cos_eq_zero_iff
- \- *theorem* complex.cos_ne_zero_iff
- \- *lemma* complex.cos_surjective
- \- *lemma* complex.deriv_tan
- \- *lemma* complex.differentiable_at_tan
- \- *lemma* complex.exists_eq_mul_self
- \- *lemma* complex.exists_pow_nat_eq
- \- *lemma* complex.exp_eq_exp_iff_exists_int
- \- *lemma* complex.exp_eq_exp_iff_exp_sub_eq_one
- \- *lemma* complex.exp_eq_one_iff
- \- *lemma* complex.exp_inj_of_neg_pi_lt_of_le_pi
- \- *def* complex.exp_local_homeomorph
- \- *lemma* complex.exp_log
- \- *lemma* complex.ext_abs_arg
- \- *lemma* complex.has_deriv_at_tan
- \- *lemma* complex.has_strict_deriv_at_log
- \- *lemma* complex.has_strict_deriv_at_tan
- \- *lemma* complex.log_I
- \- *lemma* complex.log_exp
- \- *lemma* complex.log_im
- \- *lemma* complex.log_im_le_pi
- \- *lemma* complex.log_neg_I
- \- *lemma* complex.log_neg_one
- \- *lemma* complex.log_of_real_re
- \- *lemma* complex.log_one
- \- *lemma* complex.log_re
- \- *lemma* complex.log_zero
- \- *lemma* complex.neg_pi_lt_arg
- \- *lemma* complex.neg_pi_lt_log_im
- \- *lemma* complex.of_real_log
- \- *lemma* complex.range_cos
- \- *lemma* complex.range_exp
- \- *lemma* complex.range_sin
- \- *lemma* complex.sin_arg
- \- *lemma* complex.sin_eq_sin_iff
- \- *theorem* complex.sin_eq_zero_iff
- \- *theorem* complex.sin_ne_zero_iff
- \- *lemma* complex.sin_surjective
- \- *lemma* complex.tan_add'
- \- *lemma* complex.tan_add
- \- *lemma* complex.tan_add_mul_I
- \- *lemma* complex.tan_arg
- \- *lemma* complex.tan_eq
- \- *lemma* complex.tan_eq_zero_iff
- \- *lemma* complex.tan_int_mul_pi_div_two
- \- *lemma* complex.tan_ne_zero_iff
- \- *lemma* complex.tan_two_mul
- \- *lemma* complex.tendsto_abs_tan_at_top
- \- *lemma* complex.tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* complex.times_cont_diff_at_log
- \- *lemma* complex.times_cont_diff_at_tan
- \- *lemma* complex.two_pi_I_ne_zero
- \- *lemma* continuous.clog
- \- *lemma* continuous_at.clog
- \- *lemma* continuous_on.clog
- \- *lemma* continuous_within_at.clog
- \- *lemma* deriv_arctan
- \- *lemma* deriv_within_arctan
- \- *lemma* differentiable.arctan
- \- *lemma* differentiable.clog
- \- *lemma* differentiable_at.arctan
- \- *lemma* differentiable_at.clog
- \- *lemma* differentiable_on.arctan
- \- *lemma* differentiable_on.clog
- \- *lemma* differentiable_within_at.arctan
- \- *lemma* differentiable_within_at.clog
- \- *lemma* fderiv_arctan
- \- *lemma* fderiv_within_arctan
- \- *lemma* filter.tendsto.clog
- \- *lemma* has_deriv_at.arctan
- \- *lemma* has_deriv_at.clog
- \- *lemma* has_deriv_within_at.arctan
- \- *lemma* has_deriv_within_at.clog
- \- *lemma* has_fderiv_at.arctan
- \- *lemma* has_fderiv_at.clog
- \- *lemma* has_fderiv_within_at.arctan
- \- *lemma* has_fderiv_within_at.clog
- \- *lemma* has_strict_deriv_at.arctan
- \- *lemma* has_strict_deriv_at.clog
- \- *lemma* has_strict_fderiv_at.arctan
- \- *lemma* has_strict_fderiv_at.clog
- \- *lemma* polynomial.chebyshev.T_complex_cos
- \- *lemma* polynomial.chebyshev.U_complex_cos
- \- *lemma* polynomial.chebyshev.cos_nat_mul
- \- *lemma* polynomial.chebyshev.sin_nat_succ_mul
- \- *lemma* real.arccos_cos
- \- *lemma* real.arccos_eq_pi
- \- *lemma* real.arccos_eq_pi_div_two
- \- *lemma* real.arccos_eq_pi_div_two_sub_arcsin
- \- *lemma* real.arccos_eq_zero
- \- *lemma* real.arccos_inj
- \- *lemma* real.arccos_inj_on
- \- *lemma* real.arccos_le_pi
- \- *lemma* real.arccos_neg
- \- *lemma* real.arccos_neg_one
- \- *lemma* real.arccos_nonneg
- \- *lemma* real.arccos_one
- \- *lemma* real.arccos_zero
- \- *lemma* real.arcsin_eq_arctan
- \- *lemma* real.arcsin_eq_iff_eq_sin
- \- *lemma* real.arcsin_eq_neg_pi_div_two
- \- *lemma* real.arcsin_eq_of_sin_eq
- \- *lemma* real.arcsin_eq_pi_div_two
- \- *lemma* real.arcsin_eq_pi_div_two_sub_arccos
- \- *lemma* real.arcsin_eq_zero_iff
- \- *lemma* real.arcsin_inj
- \- *lemma* real.arcsin_le_iff_le_sin'
- \- *lemma* real.arcsin_le_iff_le_sin
- \- *lemma* real.arcsin_le_neg_pi_div_two
- \- *lemma* real.arcsin_le_pi_div_two
- \- *lemma* real.arcsin_lt_iff_lt_sin'
- \- *lemma* real.arcsin_lt_iff_lt_sin
- \- *lemma* real.arcsin_lt_pi_div_two
- \- *lemma* real.arcsin_lt_zero
- \- *lemma* real.arcsin_mem_Icc
- \- *lemma* real.arcsin_neg
- \- *lemma* real.arcsin_neg_one
- \- *lemma* real.arcsin_nonneg
- \- *lemma* real.arcsin_nonpos
- \- *lemma* real.arcsin_of_le_neg_one
- \- *lemma* real.arcsin_of_one_le
- \- *lemma* real.arcsin_one
- \- *lemma* real.arcsin_pos
- \- *lemma* real.arcsin_proj_Icc
- \- *lemma* real.arcsin_sin'
- \- *lemma* real.arcsin_sin
- \- *lemma* real.arcsin_zero
- \- *lemma* real.arctan_eq_arcsin
- \- *lemma* real.arctan_eq_of_tan_eq
- \- *lemma* real.arctan_lt_pi_div_two
- \- *lemma* real.arctan_mem_Ioo
- \- *lemma* real.arctan_neg
- \- *lemma* real.arctan_one
- \- *lemma* real.arctan_tan
- \- *lemma* real.arctan_zero
- \- *lemma* real.coe_tan_local_homeomorph
- \- *lemma* real.coe_tan_local_homeomorph_symm
- \- *lemma* real.continuous_arccos
- \- *lemma* real.continuous_arcsin
- \- *lemma* real.continuous_arctan
- \- *lemma* real.continuous_at_arcsin
- \- *lemma* real.continuous_at_arctan
- \- *lemma* real.continuous_at_tan
- \- *lemma* real.continuous_on_tan
- \- *lemma* real.continuous_on_tan_Ioo
- \- *lemma* real.continuous_tan
- \- *lemma* real.cos_arccos
- \- *lemma* real.cos_arcsin
- \- *lemma* real.cos_arcsin_nonneg
- \- *lemma* real.cos_arctan
- \- *lemma* real.cos_arctan_pos
- \- *lemma* real.cos_eq_cos_iff
- \- *theorem* real.cos_eq_zero_iff
- \- *theorem* real.cos_ne_zero_iff
- \- *lemma* real.cos_sq_arctan
- \- *lemma* real.deriv_arccos
- \- *lemma* real.deriv_arcsin
- \- *lemma* real.deriv_arcsin_aux
- \- *lemma* real.deriv_arctan
- \- *lemma* real.deriv_tan
- \- *lemma* real.differentiable_arctan
- \- *lemma* real.differentiable_at_arccos
- \- *lemma* real.differentiable_at_arcsin
- \- *lemma* real.differentiable_at_arctan
- \- *lemma* real.differentiable_at_tan
- \- *lemma* real.differentiable_at_tan_of_mem_Ioo
- \- *lemma* real.differentiable_on_arccos
- \- *lemma* real.differentiable_on_arcsin
- \- *lemma* real.differentiable_within_at_arccos_Ici
- \- *lemma* real.differentiable_within_at_arccos_Iic
- \- *lemma* real.differentiable_within_at_arcsin_Ici
- \- *lemma* real.differentiable_within_at_arcsin_Iic
- \- *lemma* real.has_deriv_at_arccos
- \- *lemma* real.has_deriv_at_arcsin
- \- *lemma* real.has_deriv_at_arctan
- \- *lemma* real.has_deriv_at_tan
- \- *lemma* real.has_deriv_at_tan_of_mem_Ioo
- \- *lemma* real.has_deriv_within_at_arccos_Ici
- \- *lemma* real.has_deriv_within_at_arccos_Iic
- \- *lemma* real.has_deriv_within_at_arcsin_Ici
- \- *lemma* real.has_deriv_within_at_arcsin_Iic
- \- *lemma* real.has_strict_deriv_at_arccos
- \- *lemma* real.has_strict_deriv_at_arcsin
- \- *lemma* real.has_strict_deriv_at_arctan
- \- *lemma* real.has_strict_deriv_at_tan
- \- *lemma* real.image_tan_Ioo
- \- *lemma* real.inj_on_arcsin
- \- *lemma* real.le_arcsin_iff_sin_le'
- \- *lemma* real.le_arcsin_iff_sin_le
- \- *lemma* real.lt_arcsin_iff_sin_lt'
- \- *lemma* real.lt_arcsin_iff_sin_lt
- \- *lemma* real.maps_to_sin_Ioo
- \- *lemma* real.monotone_arcsin
- \- *lemma* real.neg_pi_div_two_eq_arcsin
- \- *lemma* real.neg_pi_div_two_le_arcsin
- \- *lemma* real.neg_pi_div_two_lt_arcsin
- \- *lemma* real.neg_pi_div_two_lt_arctan
- \- *lemma* real.pi_div_two_eq_arcsin
- \- *lemma* real.pi_div_two_le_arcsin
- \- *lemma* real.range_arcsin
- \- *lemma* real.sin_arccos
- \- *lemma* real.sin_arcsin'
- \- *lemma* real.sin_arcsin
- \- *lemma* real.sin_arctan
- \- *lemma* real.sin_eq_sin_iff
- \- *def* real.sin_local_homeomorph
- \- *lemma* real.strict_mono_decr_on_arccos
- \- *lemma* real.strict_mono_incr_on_arcsin
- \- *lemma* real.surj_on_tan
- \- *lemma* real.tan_add'
- \- *lemma* real.tan_add
- \- *lemma* real.tan_arctan
- \- *lemma* real.tan_eq_zero_iff
- \- *lemma* real.tan_int_mul_pi_div_two
- \- *def* real.tan_local_homeomorph
- \- *lemma* real.tan_ne_zero_iff
- \- *def* real.tan_order_iso
- \- *lemma* real.tan_surjective
- \- *lemma* real.tan_two_mul
- \- *lemma* real.tendsto_abs_tan_at_top
- \- *lemma* real.tendsto_abs_tan_of_cos_eq_zero
- \- *lemma* real.times_cont_diff_arctan
- \- *lemma* real.times_cont_diff_at_arccos
- \- *lemma* real.times_cont_diff_at_arccos_iff
- \- *lemma* real.times_cont_diff_at_arcsin
- \- *lemma* real.times_cont_diff_at_arcsin_iff
- \- *lemma* real.times_cont_diff_at_tan
- \- *lemma* real.times_cont_diff_on_arccos
- \- *lemma* real.times_cont_diff_on_arcsin
- \- *lemma* real.zero_eq_arcsin_iff
- \- *lemma* times_cont_diff.arctan
- \- *lemma* times_cont_diff_at.arctan
- \- *lemma* times_cont_diff_on.arctan
- \- *lemma* times_cont_diff_within_at.arctan

Added src/analysis/special_functions/trigonometric/chebyshev.lean
- \+ *lemma* polynomial.chebyshev.T_complex_cos
- \+ *lemma* polynomial.chebyshev.U_complex_cos
- \+ *lemma* polynomial.chebyshev.cos_nat_mul
- \+ *lemma* polynomial.chebyshev.sin_nat_succ_mul

Added src/analysis/special_functions/trigonometric/complex.lean
- \+ *lemma* complex.continuous_at_tan
- \+ *lemma* complex.continuous_on_tan
- \+ *lemma* complex.continuous_tan
- \+ *lemma* complex.cos_eq_cos_iff
- \+ *lemma* complex.cos_eq_iff_quadratic
- \+ *theorem* complex.cos_eq_zero_iff
- \+ *theorem* complex.cos_ne_zero_iff
- \+ *lemma* complex.cos_surjective
- \+ *lemma* complex.deriv_tan
- \+ *lemma* complex.differentiable_at_tan
- \+ *lemma* complex.has_deriv_at_tan
- \+ *lemma* complex.has_strict_deriv_at_tan
- \+ *lemma* complex.range_cos
- \+ *lemma* complex.range_sin
- \+ *lemma* complex.sin_eq_sin_iff
- \+ *theorem* complex.sin_eq_zero_iff
- \+ *theorem* complex.sin_ne_zero_iff
- \+ *lemma* complex.sin_surjective
- \+ *lemma* complex.tan_add'
- \+ *lemma* complex.tan_add
- \+ *lemma* complex.tan_add_mul_I
- \+ *lemma* complex.tan_eq
- \+ *lemma* complex.tan_eq_zero_iff
- \+ *lemma* complex.tan_int_mul_pi_div_two
- \+ *lemma* complex.tan_ne_zero_iff
- \+ *lemma* complex.tan_two_mul
- \+ *lemma* complex.tendsto_abs_tan_at_top
- \+ *lemma* complex.tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* complex.times_cont_diff_at_tan
- \+ *lemma* real.cos_eq_cos_iff
- \+ *theorem* real.cos_eq_zero_iff
- \+ *theorem* real.cos_ne_zero_iff
- \+ *lemma* real.sin_eq_sin_iff

Added src/analysis/special_functions/trigonometric/inverse.lean
- \+ *lemma* real.arccos_cos
- \+ *lemma* real.arccos_eq_pi
- \+ *lemma* real.arccos_eq_pi_div_two
- \+ *lemma* real.arccos_eq_pi_div_two_sub_arcsin
- \+ *lemma* real.arccos_eq_zero
- \+ *lemma* real.arccos_inj
- \+ *lemma* real.arccos_inj_on
- \+ *lemma* real.arccos_le_pi
- \+ *lemma* real.arccos_neg
- \+ *lemma* real.arccos_neg_one
- \+ *lemma* real.arccos_nonneg
- \+ *lemma* real.arccos_one
- \+ *lemma* real.arccos_zero
- \+ *lemma* real.arcsin_eq_iff_eq_sin
- \+ *lemma* real.arcsin_eq_neg_pi_div_two
- \+ *lemma* real.arcsin_eq_of_sin_eq
- \+ *lemma* real.arcsin_eq_pi_div_two
- \+ *lemma* real.arcsin_eq_pi_div_two_sub_arccos
- \+ *lemma* real.arcsin_eq_zero_iff
- \+ *lemma* real.arcsin_inj
- \+ *lemma* real.arcsin_le_iff_le_sin'
- \+ *lemma* real.arcsin_le_iff_le_sin
- \+ *lemma* real.arcsin_le_neg_pi_div_two
- \+ *lemma* real.arcsin_le_pi_div_two
- \+ *lemma* real.arcsin_lt_iff_lt_sin'
- \+ *lemma* real.arcsin_lt_iff_lt_sin
- \+ *lemma* real.arcsin_lt_pi_div_two
- \+ *lemma* real.arcsin_lt_zero
- \+ *lemma* real.arcsin_mem_Icc
- \+ *lemma* real.arcsin_neg
- \+ *lemma* real.arcsin_neg_one
- \+ *lemma* real.arcsin_nonneg
- \+ *lemma* real.arcsin_nonpos
- \+ *lemma* real.arcsin_of_le_neg_one
- \+ *lemma* real.arcsin_of_one_le
- \+ *lemma* real.arcsin_one
- \+ *lemma* real.arcsin_pos
- \+ *lemma* real.arcsin_proj_Icc
- \+ *lemma* real.arcsin_sin'
- \+ *lemma* real.arcsin_sin
- \+ *lemma* real.arcsin_zero
- \+ *lemma* real.continuous_arccos
- \+ *lemma* real.continuous_arcsin
- \+ *lemma* real.continuous_at_arcsin
- \+ *lemma* real.cos_arccos
- \+ *lemma* real.cos_arcsin
- \+ *lemma* real.cos_arcsin_nonneg
- \+ *lemma* real.deriv_arccos
- \+ *lemma* real.deriv_arcsin
- \+ *lemma* real.deriv_arcsin_aux
- \+ *lemma* real.differentiable_at_arccos
- \+ *lemma* real.differentiable_at_arcsin
- \+ *lemma* real.differentiable_on_arccos
- \+ *lemma* real.differentiable_on_arcsin
- \+ *lemma* real.differentiable_within_at_arccos_Ici
- \+ *lemma* real.differentiable_within_at_arccos_Iic
- \+ *lemma* real.differentiable_within_at_arcsin_Ici
- \+ *lemma* real.differentiable_within_at_arcsin_Iic
- \+ *lemma* real.has_deriv_at_arccos
- \+ *lemma* real.has_deriv_at_arcsin
- \+ *lemma* real.has_deriv_within_at_arccos_Ici
- \+ *lemma* real.has_deriv_within_at_arccos_Iic
- \+ *lemma* real.has_deriv_within_at_arcsin_Ici
- \+ *lemma* real.has_deriv_within_at_arcsin_Iic
- \+ *lemma* real.has_strict_deriv_at_arccos
- \+ *lemma* real.has_strict_deriv_at_arcsin
- \+ *lemma* real.inj_on_arcsin
- \+ *lemma* real.le_arcsin_iff_sin_le'
- \+ *lemma* real.le_arcsin_iff_sin_le
- \+ *lemma* real.lt_arcsin_iff_sin_lt'
- \+ *lemma* real.lt_arcsin_iff_sin_lt
- \+ *lemma* real.maps_to_sin_Ioo
- \+ *lemma* real.monotone_arcsin
- \+ *lemma* real.neg_pi_div_two_eq_arcsin
- \+ *lemma* real.neg_pi_div_two_le_arcsin
- \+ *lemma* real.neg_pi_div_two_lt_arcsin
- \+ *lemma* real.pi_div_two_eq_arcsin
- \+ *lemma* real.pi_div_two_le_arcsin
- \+ *lemma* real.range_arcsin
- \+ *lemma* real.sin_arccos
- \+ *lemma* real.sin_arcsin'
- \+ *lemma* real.sin_arcsin
- \+ *def* real.sin_local_homeomorph
- \+ *lemma* real.strict_mono_decr_on_arccos
- \+ *lemma* real.strict_mono_incr_on_arcsin
- \+ *lemma* real.times_cont_diff_at_arccos
- \+ *lemma* real.times_cont_diff_at_arccos_iff
- \+ *lemma* real.times_cont_diff_at_arcsin
- \+ *lemma* real.times_cont_diff_at_arcsin_iff
- \+ *lemma* real.times_cont_diff_on_arccos
- \+ *lemma* real.times_cont_diff_on_arcsin
- \+ *lemma* real.zero_eq_arcsin_iff

Modified src/data/real/pi/bounds.lean


Modified src/data/real/pi/leibniz.lean


Modified src/geometry/euclidean/basic.lean


Modified src/measure_theory/function/special_functions.lean


Modified test/continuity.lean


Modified test/differentiable.lean


Modified test/simp_command.lean




## [2021-09-26 22:22:00](https://github.com/leanprover-community/mathlib/commit/62abfe5)
refactor(measure_theory/measure/hausdorff): move `dimH` to a new file, redefine ([#9391](https://github.com/leanprover-community/mathlib/pull/9391))
* move definition of the Hausdorff dimension to a new file
  `topology.metric_space.hausdorff_dimension`;
* move `dimH` and related lemmas to the root namespace;
* rewrite the definition so that it no longer requires
  `[measurable_space X] [borel_space X]`; use `rw dimH_def` to get a
  version using `[measurable_space X]` from the environment;
* add `dimH_le`, `set.finite.dimH_zero` and `finset.dimH_zero`;
* make `dimH` irreducible.
#### Estimated changes
Modified docs/overview.yaml


Modified src/measure_theory/measure/hausdorff.lean
- \- *lemma* antilipschitz_with.dimH_preimage_le
- \- *lemma* antilipschitz_with.le_dimH_image
- \- *lemma* continuous_linear_equiv.dimH_image
- \- *lemma* continuous_linear_equiv.dimH_preimage
- \- *lemma* continuous_linear_equiv.dimH_univ
- \- *theorem* dense_compl_of_dimH_lt_finrank
- \- *lemma* dimH_image_le_of_locally_holder_on
- \- *lemma* dimH_image_le_of_locally_lipschitz_on
- \- *lemma* dimH_range_le_of_locally_holder_on
- \- *lemma* dimH_range_le_of_locally_lipschitz_on
- \- *lemma* holder_on_with.dimH_image_le
- \- *lemma* holder_with.dimH_image_le
- \- *lemma* holder_with.dimH_range_le
- \- *lemma* isometric.dimH_image
- \- *lemma* isometric.dimH_preimage
- \- *lemma* isometric.dimH_univ
- \- *lemma* isometry.dimH_image
- \- *lemma* lipschitz_on_with.dimH_image_le
- \- *lemma* lipschitz_with.dimH_image_le
- \- *lemma* lipschitz_with.dimH_range_le
- \- *def* measure_theory.dimH
- \- *lemma* measure_theory.dimH_Union
- \- *lemma* measure_theory.dimH_bUnion
- \- *lemma* measure_theory.dimH_countable
- \- *lemma* measure_theory.dimH_empty
- \- *lemma* measure_theory.dimH_le_of_hausdorff_measure_ne_top
- \- *lemma* measure_theory.dimH_mono
- \- *lemma* measure_theory.dimH_of_hausdorff_measure_ne_zero_ne_top
- \- *lemma* measure_theory.dimH_sUnion
- \- *lemma* measure_theory.dimH_singleton
- \- *lemma* measure_theory.dimH_subsingleton
- \- *lemma* measure_theory.dimH_union
- \- *lemma* measure_theory.hausdorff_measure_of_dimH_lt
- \- *lemma* measure_theory.hausdorff_measure_of_lt_dimH
- \- *lemma* measure_theory.le_dimH_of_hausdorff_measure_eq_top
- \- *lemma* measure_theory.le_dimH_of_hausdorff_measure_ne_zero
- \- *lemma* measure_theory.measure_zero_of_dimH_lt
- \- *theorem* real.dimH_ball_pi
- \- *theorem* real.dimH_ball_pi_fin
- \- *theorem* real.dimH_of_mem_nhds
- \- *theorem* real.dimH_of_nonempty_interior
- \- *theorem* real.dimH_univ
- \- *theorem* real.dimH_univ_eq_finrank
- \- *theorem* real.dimH_univ_pi
- \- *theorem* real.dimH_univ_pi_fin
- \- *lemma* times_cont_diff.dense_compl_range_of_finrank_lt_finrank
- \- *lemma* times_cont_diff.dimH_range_le
- \- *lemma* times_cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \- *lemma* times_cont_diff_on.dimH_image_le

Added src/topology/metric_space/hausdorff_dimension.lean
- \+ *lemma* antilipschitz_with.dimH_preimage_le
- \+ *lemma* antilipschitz_with.le_dimH_image
- \+ *lemma* continuous_linear_equiv.dimH_image
- \+ *lemma* continuous_linear_equiv.dimH_preimage
- \+ *lemma* continuous_linear_equiv.dimH_univ
- \+ *theorem* dense_compl_of_dimH_lt_finrank
- \+ *lemma* dimH_Union
- \+ *lemma* dimH_bUnion
- \+ *lemma* dimH_coe_finset
- \+ *lemma* dimH_countable
- \+ *lemma* dimH_def
- \+ *lemma* dimH_empty
- \+ *lemma* dimH_finite
- \+ *lemma* dimH_image_le_of_locally_holder_on
- \+ *lemma* dimH_image_le_of_locally_lipschitz_on
- \+ *lemma* dimH_le
- \+ *lemma* dimH_le_of_hausdorff_measure_ne_top
- \+ *lemma* dimH_mono
- \+ *lemma* dimH_of_hausdorff_measure_ne_zero_ne_top
- \+ *lemma* dimH_range_le_of_locally_holder_on
- \+ *lemma* dimH_range_le_of_locally_lipschitz_on
- \+ *lemma* dimH_sUnion
- \+ *lemma* dimH_singleton
- \+ *lemma* dimH_subsingleton
- \+ *lemma* dimH_union
- \+ *lemma* hausdorff_measure_of_dimH_lt
- \+ *lemma* hausdorff_measure_of_lt_dimH
- \+ *lemma* holder_on_with.dimH_image_le
- \+ *lemma* holder_with.dimH_image_le
- \+ *lemma* holder_with.dimH_range_le
- \+ *lemma* isometric.dimH_image
- \+ *lemma* isometric.dimH_preimage
- \+ *lemma* isometric.dimH_univ
- \+ *lemma* isometry.dimH_image
- \+ *lemma* le_dimH_of_hausdorff_measure_eq_top
- \+ *lemma* le_dimH_of_hausdorff_measure_ne_zero
- \+ *lemma* lipschitz_on_with.dimH_image_le
- \+ *lemma* lipschitz_with.dimH_image_le
- \+ *lemma* lipschitz_with.dimH_range_le
- \+ *lemma* measure_zero_of_dimH_lt
- \+ *theorem* real.dimH_ball_pi
- \+ *theorem* real.dimH_ball_pi_fin
- \+ *theorem* real.dimH_of_mem_nhds
- \+ *theorem* real.dimH_of_nonempty_interior
- \+ *theorem* real.dimH_univ
- \+ *theorem* real.dimH_univ_eq_finrank
- \+ *theorem* real.dimH_univ_pi
- \+ *theorem* real.dimH_univ_pi_fin
- \+ *lemma* times_cont_diff.dense_compl_range_of_finrank_lt_finrank
- \+ *lemma* times_cont_diff.dimH_range_le
- \+ *lemma* times_cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \+ *lemma* times_cont_diff_on.dimH_image_le



## [2021-09-26 22:21:59](https://github.com/leanprover-community/mathlib/commit/432271f)
feat(algebra/pointwise): add smul_set_inter ([#9374](https://github.com/leanprover-community/mathlib/pull/9374))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819) .
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.smul_set_inter'
- \+ *lemma* set.smul_set_inter
- \+ *lemma* set.smul_set_inter_subset



## [2021-09-26 21:40:02](https://github.com/leanprover-community/mathlib/commit/996783c)
feat(topology/sheaves/stalks): Generalize from Type to algebraic categories ([#9357](https://github.com/leanprover-community/mathlib/pull/9357))
Previously, basic lemmas about stalks like `germ_exist` and `section_ext` were only available for `Type`-valued (pre)sheaves. This PR generalizes these to (pre)sheaves valued in any concrete category where the forgetful functor preserves filtered colimits, which includes most algebraic categories like `Group` and `CommRing`. For the statements about stalks maps, we additionally assume that the forgetful functor reflects isomorphisms and preserves limits.
#### Estimated changes
Modified src/topology/sheaves/sheafify.lean


Modified src/topology/sheaves/stalks.lean
- \+/\- *lemma* Top.presheaf.app_bijective_of_stalk_functor_map_bijective
- \+/\- *lemma* Top.presheaf.app_injective_iff_stalk_functor_map_injective
- \+/\- *lemma* Top.presheaf.app_injective_of_stalk_functor_map_injective
- \+/\- *lemma* Top.presheaf.app_surjective_of_stalk_functor_map_bijective
- \+/\- *lemma* Top.presheaf.germ_eq
- \+/\- *lemma* Top.presheaf.germ_exist
- \+/\- *lemma* Top.presheaf.germ_ext
- \+/\- *lemma* Top.presheaf.germ_res
- \- *lemma* Top.presheaf.germ_res_apply'
- \- *lemma* Top.presheaf.germ_res_apply
- \+/\- *lemma* Top.presheaf.is_iso_iff_stalk_functor_map_iso
- \+/\- *lemma* Top.presheaf.is_iso_of_stalk_functor_map_iso
- \+/\- *lemma* Top.presheaf.section_ext
- \+/\- *lemma* Top.presheaf.stalk_functor_map_germ
- \- *lemma* Top.presheaf.stalk_functor_map_germ_apply
- \+/\- *lemma* Top.presheaf.stalk_functor_map_injective_of_app_injective
- \+/\- *def* Top.presheaf.stalk_pushforward



## [2021-09-26 12:40:21](https://github.com/leanprover-community/mathlib/commit/865ad47)
feat(algebra/module/pointwise_pi): add a file with lemmas on smul_pi ([#9369](https://github.com/leanprover-community/mathlib/pull/9369))
Make a new file rather than add an import to either of `algebra.pointwise` or `algebra.module.pi`.
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Added src/algebra/module/pointwise_pi.lean
- \+ *lemma* smul_pi'
- \+ *lemma* smul_pi
- \+ *lemma* smul_pi_subset
- \+ *lemma* smul_univ_pi



## [2021-09-26 10:39:54](https://github.com/leanprover-community/mathlib/commit/b3ca07f)
docs(undergrad): Add trigonometric Weierstrass ([#9393](https://github.com/leanprover-community/mathlib/pull/9393))
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-09-26 10:39:53](https://github.com/leanprover-community/mathlib/commit/4ae46db)
feat(field_theory/is_alg_closed): more isomorphisms of algebraic closures ([#9376](https://github.com/leanprover-community/mathlib/pull/9376))
#### Estimated changes
Modified src/field_theory/is_alg_closed/basic.lean
- \+ *lemma* is_alg_closure.equiv_of_equiv_algebra_map
- \+ *lemma* is_alg_closure.equiv_of_equiv_comp_algebra_map
- \+ *lemma* is_alg_closure.equiv_of_equiv_symm_algebra_map
- \+ *lemma* is_alg_closure.equiv_of_equiv_symm_comp_algebra_map



## [2021-09-26 10:39:52](https://github.com/leanprover-community/mathlib/commit/453f218)
refactor(linear_algebra/charpoly): move linear_algebra/charpoly to linear_algebra/matrix/charpoly ([#9368](https://github.com/leanprover-community/mathlib/pull/9368))
We move `linear_algebra/charpoly`to `linear_algebra/matrix/charpoly`, since the results there are for matrices. We also rename some lemmas in `linear_algebra/matrix/charpoly/coeff` to have the namespace `matrix`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified docs/100.yaml


Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/linear_algebra/charpoly.lean


Renamed src/linear_algebra/charpoly/basic.lean to src/linear_algebra/matrix/charpoly/basic.lean
- \- *theorem* aeval_self_charpoly
- \+ *theorem* matrix.aeval_self_charpoly

Renamed src/linear_algebra/charpoly/coeff.lean to src/linear_algebra/matrix/charpoly/coeff.lean
- \- *lemma* charpoly_coeff_eq_prod_coeff_of_le
- \- *theorem* charpoly_degree_eq_dim
- \- *lemma* charpoly_monic
- \- *theorem* charpoly_nat_degree_eq_dim
- \- *lemma* charpoly_sub_diagonal_degree_lt
- \- *theorem* det_eq_sign_charpoly_coeff
- \- *lemma* det_of_card_zero
- \- *lemma* eval_det
- \- *lemma* finite_field.charpoly_pow_card
- \+ *lemma* finite_field.matrix.charpoly_pow_card
- \- *lemma* mat_poly_equiv_eval
- \+ *lemma* matrix.charpoly_coeff_eq_prod_coeff_of_le
- \+ *theorem* matrix.charpoly_degree_eq_dim
- \+ *lemma* matrix.charpoly_monic
- \+ *theorem* matrix.charpoly_nat_degree_eq_dim
- \+ *lemma* matrix.charpoly_sub_diagonal_degree_lt
- \+ *theorem* matrix.det_eq_sign_charpoly_coeff
- \+ *lemma* matrix.det_of_card_zero
- \+ *lemma* matrix.eval_det
- \+ *lemma* matrix.mat_poly_equiv_eval
- \+ *theorem* matrix.trace_eq_neg_charpoly_coeff
- \- *theorem* trace_eq_neg_charpoly_coeff

Modified src/ring_theory/norm.lean


Modified src/ring_theory/trace.lean




## [2021-09-26 10:39:51](https://github.com/leanprover-community/mathlib/commit/a2517af)
refactor(data/fin,*): redefine `insert_nth`, add lemmas ([#9349](https://github.com/leanprover-community/mathlib/pull/9349))
### `data/fin`
* add `fin.succ_above_cast_lt`, `fin.succ_above_pred`,
  `fin.cast_lt_succ_above`, `fin.pred_succ_above`;
* add `fin.exists_succ_above_eq` and `fin.exists_succ_above_eq_iff`,
  use the latter to prove `fin.range_succ_above`;
* add `@[simp]` to `fin.succ_above_left_inj`;
* add `fin.cases_succ_above` induction principle, redefine
  `fin.insert_nth` to be `fin.cases_succ_above`;
* add lemmas about `fin.insert_nth` and some algebraic operations.
### `data/fintype/basic`
* add `finset.insert_compl_self`;
* add `fin.image_succ_above_univ`, `fin.image_succ_univ`,
  `fin.image_cast_succ` and use them to prove `fin.univ_succ`,
  `fin.univ_cast_succ`, and `fin.univ_succ_above` using `by simp`;
### `data/fintype/card`
* slightly golf the proof of `fin.prod_univ_succ_above`;
* use `@[to_additive]` to generate some proofs.
### `topology/*`
* prove continuity of `fin.insert_nth` in both arguments and add all
  the standard dot-notation `*.fin_insert_nth` lemmas (`*` is one of
  `filter.tendsto`, `continuous_at`, `continuous_within_at`,
  `continuous_on`, `continuous`).
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_lt_succ_above
- \+ *lemma* fin.exists_succ_above_eq
- \+ *lemma* fin.exists_succ_above_eq_iff
- \- *def* fin.insert_nth'
- \+/\- *def* fin.insert_nth
- \+ *lemma* fin.insert_nth_add
- \+ *lemma* fin.insert_nth_binop
- \+ *lemma* fin.insert_nth_div
- \+ *lemma* fin.insert_nth_mul
- \+ *lemma* fin.insert_nth_sub
- \+ *lemma* fin.insert_nth_sub_same
- \+ *lemma* fin.insert_nth_zero_right
- \+ *lemma* fin.pred_succ_above
- \+/\- *lemma* fin.range_succ_above
- \+ *def* fin.succ_above_cases
- \+ *lemma* fin.succ_above_cases_eq_insert_nth
- \+ *lemma* fin.succ_above_cast_lt
- \+/\- *lemma* fin.succ_above_left_inj
- \+ *lemma* fin.succ_above_pred

Modified src/data/fintype/basic.lean
- \+ *lemma* fin.image_cast_succ
- \+ *lemma* fin.image_succ_above_univ
- \+ *lemma* fin.image_succ_univ
- \+ *theorem* finset.insert_compl_self

Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.prod_univ_succ_above
- \- *theorem* fin.sum_univ_cast_succ
- \- *theorem* fin.sum_univ_succ
- \- *theorem* fin.sum_univ_succ_above

Modified src/topology/constructions.lean
- \+ *lemma* continuous.fin_insert_nth
- \+ *lemma* continuous_at.fin_insert_nth
- \+ *lemma* filter.tendsto.fin_insert_nth

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.fin_insert_nth
- \+ *lemma* continuous_within_at.fin_insert_nth



## [2021-09-26 08:35:17](https://github.com/leanprover-community/mathlib/commit/83470af)
feat(algebra/order/ring): add odd_neg, odd_abs, generalize dvd/abs lemmas ([#9362](https://github.com/leanprover-community/mathlib/pull/9362))
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* odd_abs

Modified src/algebra/ring/basic.lean
- \+ *lemma* odd.neg
- \+ *lemma* odd_neg



## [2021-09-26 07:23:13](https://github.com/leanprover-community/mathlib/commit/def1c02)
refactor(analysis/convex/function): generalize definition of `convex_on`/`concave_on` to allow any (ordered) scalars ([#9389](https://github.com/leanprover-community/mathlib/pull/9389))
`convex_on` and `concave_on` are currently only defined for real vector spaces. This generalizes ℝ to an arbitrary `ordered_semiring` in the definition.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/convex/basic.lean
- \+/\- *def* convex

Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on.add
- \+/\- *lemma* concave_on.comp_linear_map
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* concave_on.inf
- \+/\- *lemma* concave_on.le_on_segment'
- \+/\- *lemma* concave_on.le_on_segment
- \+/\- *lemma* concave_on.le_right_of_left_le'
- \+/\- *lemma* concave_on.le_right_of_left_le
- \+/\- *lemma* concave_on.left_le_of_le_right'
- \+/\- *lemma* concave_on.left_le_of_le_right
- \+/\- *lemma* concave_on.slope_mono_adjacent
- \+/\- *lemma* concave_on.subset
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* concave_on.translate_right
- \+/\- *def* concave_on
- \+/\- *lemma* concave_on_const
- \+/\- *lemma* concave_on_id
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.comp_linear_map
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.exists_ge_of_center_mass
- \+/\- *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+/\- *lemma* convex_on.le_left_of_right_le'
- \+/\- *lemma* convex_on.le_left_of_right_le
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.le_right_of_left_le'
- \+/\- *lemma* convex_on.le_right_of_left_le
- \+/\- *lemma* convex_on.map_center_mass_le
- \+/\- *lemma* convex_on.map_sum_le
- \+/\- *lemma* convex_on.slope_mono_adjacent
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.sup
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+/\- *def* convex_on
- \+/\- *lemma* convex_on_const
- \+/\- *lemma* convex_on_id
- \+/\- *lemma* linear_map.concave_on
- \+/\- *lemma* linear_map.convex_on

Modified src/analysis/convex/integral.lean


Modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* concave_on_log_Iio
- \+/\- *lemma* concave_on_log_Ioi
- \+/\- *lemma* convex_on_exp
- \+/\- *lemma* convex_on_fpow
- \+/\- *lemma* convex_on_pow
- \+/\- *lemma* convex_on_pow_of_even
- \+/\- *lemma* convex_on_rpow

Modified src/analysis/convex/topology.lean




## [2021-09-26 02:41:05](https://github.com/leanprover-community/mathlib/commit/793a598)
chore(scripts): update nolints.txt ([#9392](https://github.com/leanprover-community/mathlib/pull/9392))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-25 17:07:10](https://github.com/leanprover-community/mathlib/commit/9866526)
feat(data/multiset/basic): add lemma that `multiset.map f` preserves `count` under certain assumptions on `f` ([#9117](https://github.com/leanprover-community/mathlib/pull/9117))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.count_map_eq_count



## [2021-09-25 16:04:00](https://github.com/leanprover-community/mathlib/commit/168806c)
feat(measure_theory/integral/lebesgue): lintegral is strictly monotone under some conditions ([#9373](https://github.com/leanprover-community/mathlib/pull/9373))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_strict_mono
- \+ *lemma* measure_theory.lintegral_strict_mono_of_ae_le_of_ae_lt_on
- \+ *lemma* measure_theory.lintegral_sub_le
- \+ *lemma* measure_theory.set_lintegral_strict_mono

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.ae_le_of_ae_lt



## [2021-09-25 15:05:39](https://github.com/leanprover-community/mathlib/commit/eba2b2e)
feat(measure_theory/function/l1_space): add integrability lemma for `measure.with_density` ([#9367](https://github.com/leanprover-community/mathlib/pull/9367))
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable_with_density_iff
- \+ *lemma* measure_theory.of_real_to_real_ae_eq



## [2021-09-25 09:01:16](https://github.com/leanprover-community/mathlib/commit/6ea8168)
refactor(topology/compact_open): use bundled continuous maps ([#9351](https://github.com/leanprover-community/mathlib/pull/9351))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.continuous_comp
- \- *lemma* continuous_map.continuous_induced
- \- *def* continuous_map.induced



## [2021-09-25 06:48:09](https://github.com/leanprover-community/mathlib/commit/51ad06e)
refactor(analysis/inner_product_space/*): split big file ([#9382](https://github.com/leanprover-community/mathlib/pull/9382))
This PR makes a new folder `analysis/inner_product_space/*` comprising several files splitting the old `analysis/normed_space/inner_product` (which had reached 2900 lines!).
https://leanprover.zulipchat.com/#narrow/stream/116395-maths
#### Estimated changes
Modified src/analysis/calculus/conformal/inner_product.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/convex/cone.lean


Renamed src/analysis/normed_space/inner_product.lean to src/analysis/inner_product_space/basic.lean
- \- *lemma* coe_orthonormal_basis
- \- *lemma* continuous.inner
- \- *lemma* continuous_at.inner
- \- *lemma* continuous_inner
- \- *lemma* continuous_on.inner
- \- *lemma* continuous_within_at.inner
- \- *lemma* deriv_inner_apply
- \- *lemma* differentiable.dist
- \- *lemma* differentiable.inner
- \- *lemma* differentiable.norm
- \- *lemma* differentiable.norm_sq
- \- *lemma* differentiable_at.dist
- \- *lemma* differentiable_at.inner
- \- *lemma* differentiable_at.norm
- \- *lemma* differentiable_at.norm_sq
- \- *lemma* differentiable_inner
- \- *lemma* differentiable_on.dist
- \- *lemma* differentiable_on.inner
- \- *lemma* differentiable_on.norm
- \- *lemma* differentiable_on.norm_sq
- \- *lemma* differentiable_within_at.dist
- \- *lemma* differentiable_within_at.inner
- \- *lemma* differentiable_within_at.norm
- \- *lemma* differentiable_within_at.norm_sq
- \- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \- *lemma* eq_orthogonal_projection_of_eq_submodule
- \- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \- *lemma* eq_orthogonal_projection_of_mem_orthogonal'
- \- *lemma* eq_orthogonal_projection_of_mem_orthogonal
- \- *lemma* eq_sum_orthogonal_projection_self_orthogonal_complement
- \- *lemma* exists_is_orthonormal_dense_span
- \- *theorem* exists_norm_eq_infi_of_complete_convex
- \- *theorem* exists_norm_eq_infi_of_complete_subspace
- \- *lemma* exists_subset_is_orthonormal_basis
- \- *lemma* exists_subset_is_orthonormal_dense_span
- \- *lemma* fderiv_inner_apply
- \- *def* fderiv_inner_clm
- \- *lemma* fderiv_inner_clm_apply
- \- *lemma* filter.tendsto.inner
- \- *def* fin_orthonormal_basis
- \- *lemma* fin_orthonormal_basis_orthonormal
- \- *lemma* finrank_orthogonal_span_singleton
- \- *lemma* has_deriv_at.inner
- \- *lemma* has_deriv_within_at.inner
- \- *lemma* has_fderiv_at.inner
- \- *lemma* has_fderiv_within_at.inner
- \- *lemma* id_eq_sum_orthogonal_projection_self_orthogonal_complement
- \- *lemma* inner_orthogonal_projection_left_eq_right
- \- *lemma* is_bounded_bilinear_map_inner
- \- *lemma* maximal_orthonormal_iff_basis_of_finite_dimensional
- \- *lemma* maximal_orthonormal_iff_dense_span
- \- *lemma* maximal_orthonormal_iff_orthogonal_complement_eq_bot
- \- *theorem* norm_eq_infi_iff_inner_eq_zero
- \- *theorem* norm_eq_infi_iff_real_inner_eq_zero
- \- *theorem* norm_eq_infi_iff_real_inner_le_zero
- \- *def* orthogonal_projection
- \- *lemma* orthogonal_projection_bot
- \- *lemma* orthogonal_projection_eq_self_iff
- \- *def* orthogonal_projection_fn
- \- *lemma* orthogonal_projection_fn_eq
- \- *lemma* orthogonal_projection_fn_inner_eq_zero
- \- *lemma* orthogonal_projection_fn_mem
- \- *lemma* orthogonal_projection_fn_norm_sq
- \- *lemma* orthogonal_projection_inner_eq_zero
- \- *lemma* orthogonal_projection_map_apply
- \- *lemma* orthogonal_projection_mem_subspace_eq_self
- \- *lemma* orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
- \- *lemma* orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
- \- *lemma* orthogonal_projection_norm_le
- \- *lemma* orthogonal_projection_orthogonal_complement_singleton_eq_zero
- \- *lemma* orthogonal_projection_singleton
- \- *lemma* orthogonal_projection_unit_singleton
- \- *def* orthonormal_basis
- \- *def* orthonormal_basis_index
- \- *lemma* orthonormal_basis_orthonormal
- \- *def* reflection
- \- *lemma* reflection_apply
- \- *lemma* reflection_bot
- \- *lemma* reflection_eq_self_iff
- \- *lemma* reflection_involutive
- \- *lemma* reflection_map
- \- *lemma* reflection_map_apply
- \- *lemma* reflection_mem_subspace_eq_self
- \- *lemma* reflection_mem_subspace_orthogonal_complement_eq_neg
- \- *lemma* reflection_mem_subspace_orthogonal_precomplement_eq_neg
- \- *lemma* reflection_orthogonal_complement_singleton_eq_neg
- \- *lemma* reflection_reflection
- \- *lemma* reflection_symm
- \- *lemma* smul_orthogonal_projection_singleton
- \- *lemma* submodule.exists_sum_mem_mem_orthogonal
- \- *lemma* submodule.finrank_add_finrank_orthogonal'
- \- *lemma* submodule.finrank_add_finrank_orthogonal
- \- *lemma* submodule.finrank_add_inf_finrank_orthogonal'
- \- *lemma* submodule.finrank_add_inf_finrank_orthogonal
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \- *lemma* submodule.orthogonal_eq_bot_iff
- \- *lemma* submodule.orthogonal_orthogonal
- \- *lemma* submodule.orthogonal_orthogonal_eq_closure
- \- *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \- *lemma* submodule.sup_orthogonal_of_complete_space
- \- *lemma* submodule.sup_orthogonal_of_is_complete
- \- *lemma* times_cont_diff.dist
- \- *lemma* times_cont_diff.inner
- \- *lemma* times_cont_diff.norm
- \- *lemma* times_cont_diff.norm_sq
- \- *lemma* times_cont_diff_at.dist
- \- *lemma* times_cont_diff_at.inner
- \- *lemma* times_cont_diff_at.norm
- \- *lemma* times_cont_diff_at.norm_sq
- \- *lemma* times_cont_diff_at_inner
- \- *lemma* times_cont_diff_at_norm
- \- *lemma* times_cont_diff_inner
- \- *lemma* times_cont_diff_norm_sq
- \- *lemma* times_cont_diff_on.dist
- \- *lemma* times_cont_diff_on.inner
- \- *lemma* times_cont_diff_on.norm
- \- *lemma* times_cont_diff_on.norm_sq
- \- *lemma* times_cont_diff_within_at.dist
- \- *lemma* times_cont_diff_within_at.inner
- \- *lemma* times_cont_diff_within_at.norm
- \- *lemma* times_cont_diff_within_at.norm_sq

Added src/analysis/inner_product_space/calculus.lean
- \+ *lemma* continuous.inner
- \+ *lemma* continuous_at.inner
- \+ *lemma* continuous_inner
- \+ *lemma* continuous_on.inner
- \+ *lemma* continuous_within_at.inner
- \+ *lemma* deriv_inner_apply
- \+ *lemma* differentiable.dist
- \+ *lemma* differentiable.inner
- \+ *lemma* differentiable.norm
- \+ *lemma* differentiable.norm_sq
- \+ *lemma* differentiable_at.dist
- \+ *lemma* differentiable_at.inner
- \+ *lemma* differentiable_at.norm
- \+ *lemma* differentiable_at.norm_sq
- \+ *lemma* differentiable_inner
- \+ *lemma* differentiable_on.dist
- \+ *lemma* differentiable_on.inner
- \+ *lemma* differentiable_on.norm
- \+ *lemma* differentiable_on.norm_sq
- \+ *lemma* differentiable_within_at.dist
- \+ *lemma* differentiable_within_at.inner
- \+ *lemma* differentiable_within_at.norm
- \+ *lemma* differentiable_within_at.norm_sq
- \+ *lemma* fderiv_inner_apply
- \+ *def* fderiv_inner_clm
- \+ *lemma* fderiv_inner_clm_apply
- \+ *lemma* filter.tendsto.inner
- \+ *lemma* has_deriv_at.inner
- \+ *lemma* has_deriv_within_at.inner
- \+ *lemma* has_fderiv_at.inner
- \+ *lemma* has_fderiv_within_at.inner
- \+ *lemma* is_bounded_bilinear_map_inner
- \+ *lemma* times_cont_diff.dist
- \+ *lemma* times_cont_diff.inner
- \+ *lemma* times_cont_diff.norm
- \+ *lemma* times_cont_diff.norm_sq
- \+ *lemma* times_cont_diff_at.dist
- \+ *lemma* times_cont_diff_at.inner
- \+ *lemma* times_cont_diff_at.norm
- \+ *lemma* times_cont_diff_at.norm_sq
- \+ *lemma* times_cont_diff_at_inner
- \+ *lemma* times_cont_diff_at_norm
- \+ *lemma* times_cont_diff_inner
- \+ *lemma* times_cont_diff_norm_sq
- \+ *lemma* times_cont_diff_on.dist
- \+ *lemma* times_cont_diff_on.inner
- \+ *lemma* times_cont_diff_on.norm
- \+ *lemma* times_cont_diff_on.norm_sq
- \+ *lemma* times_cont_diff_within_at.dist
- \+ *lemma* times_cont_diff_within_at.inner
- \+ *lemma* times_cont_diff_within_at.norm
- \+ *lemma* times_cont_diff_within_at.norm_sq

Renamed src/analysis/normed_space/conformal_linear_map/inner_product.lean to src/analysis/inner_product_space/conformal_linear_map.lean


Renamed src/analysis/normed_space/euclidean_dist.lean to src/analysis/inner_product_space/euclidean_dist.lean


Added src/analysis/inner_product_space/projection.lean
- \+ *lemma* coe_orthonormal_basis
- \+ *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_eq_submodule
- \+ *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_mem_orthogonal'
- \+ *lemma* eq_orthogonal_projection_of_mem_orthogonal
- \+ *lemma* eq_sum_orthogonal_projection_self_orthogonal_complement
- \+ *lemma* exists_is_orthonormal_dense_span
- \+ *theorem* exists_norm_eq_infi_of_complete_convex
- \+ *theorem* exists_norm_eq_infi_of_complete_subspace
- \+ *lemma* exists_subset_is_orthonormal_basis
- \+ *lemma* exists_subset_is_orthonormal_dense_span
- \+ *def* fin_orthonormal_basis
- \+ *lemma* fin_orthonormal_basis_orthonormal
- \+ *lemma* finrank_orthogonal_span_singleton
- \+ *lemma* id_eq_sum_orthogonal_projection_self_orthogonal_complement
- \+ *lemma* inner_orthogonal_projection_left_eq_right
- \+ *lemma* maximal_orthonormal_iff_basis_of_finite_dimensional
- \+ *lemma* maximal_orthonormal_iff_dense_span
- \+ *lemma* maximal_orthonormal_iff_orthogonal_complement_eq_bot
- \+ *theorem* norm_eq_infi_iff_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_real_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_real_inner_le_zero
- \+ *def* orthogonal_projection
- \+ *lemma* orthogonal_projection_bot
- \+ *lemma* orthogonal_projection_eq_self_iff
- \+ *def* orthogonal_projection_fn
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* orthogonal_projection_fn_inner_eq_zero
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* orthogonal_projection_fn_norm_sq
- \+ *lemma* orthogonal_projection_inner_eq_zero
- \+ *lemma* orthogonal_projection_map_apply
- \+ *lemma* orthogonal_projection_mem_subspace_eq_self
- \+ *lemma* orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
- \+ *lemma* orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
- \+ *lemma* orthogonal_projection_norm_le
- \+ *lemma* orthogonal_projection_orthogonal_complement_singleton_eq_zero
- \+ *lemma* orthogonal_projection_singleton
- \+ *lemma* orthogonal_projection_unit_singleton
- \+ *def* orthonormal_basis
- \+ *def* orthonormal_basis_index
- \+ *lemma* orthonormal_basis_orthonormal
- \+ *def* reflection
- \+ *lemma* reflection_apply
- \+ *lemma* reflection_bot
- \+ *lemma* reflection_eq_self_iff
- \+ *lemma* reflection_involutive
- \+ *lemma* reflection_map
- \+ *lemma* reflection_map_apply
- \+ *lemma* reflection_mem_subspace_eq_self
- \+ *lemma* reflection_mem_subspace_orthogonal_complement_eq_neg
- \+ *lemma* reflection_mem_subspace_orthogonal_precomplement_eq_neg
- \+ *lemma* reflection_orthogonal_complement_singleton_eq_neg
- \+ *lemma* reflection_reflection
- \+ *lemma* reflection_symm
- \+ *lemma* smul_orthogonal_projection_singleton
- \+ *lemma* submodule.exists_sum_mem_mem_orthogonal
- \+ *lemma* submodule.finrank_add_finrank_orthogonal'
- \+ *lemma* submodule.finrank_add_finrank_orthogonal
- \+ *lemma* submodule.finrank_add_inf_finrank_orthogonal'
- \+ *lemma* submodule.finrank_add_inf_finrank_orthogonal
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+ *lemma* submodule.orthogonal_eq_bot_iff
- \+ *lemma* submodule.orthogonal_orthogonal
- \+ *lemma* submodule.orthogonal_orthogonal_eq_closure
- \+ *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \+ *lemma* submodule.sup_orthogonal_of_complete_space
- \+ *lemma* submodule.sup_orthogonal_of_is_complete

Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/pi_Lp.lean


Modified src/analysis/quaternion.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/special_functions.lean




## [2021-09-25 06:48:08](https://github.com/leanprover-community/mathlib/commit/55d8cd0)
chore(scripts): update nolints.txt ([#9381](https://github.com/leanprover-community/mathlib/pull/9381))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-25 06:48:07](https://github.com/leanprover-community/mathlib/commit/42d8243)
feat(data/polynomial/eval): map_equiv ([#9375](https://github.com/leanprover-community/mathlib/pull/9375))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *def* polynomial.map_equiv



## [2021-09-25 04:13:25](https://github.com/leanprover-community/mathlib/commit/59b9ebb)
feat(algebra/group/to_additive): customize the relevant argument ([#9138](https://github.com/leanprover-community/mathlib/pull/9138))
`@[to_additive]` now automatically checks for each declaration what the first argument is with a multiplicative structure on it. 
This is now the argument that is tested when executing later occurrences of `@[to_additive]` for a fixed type to decide whether this declaration should be translated or not.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/meta/expr.lean


Modified src/tactic/transform_decl.lean


Modified test/to_additive.lean
- \+ *def* foo_mul
- \+ *def* nat_pi_has_one
- \+ *def* pi_nat_has_one



## [2021-09-25 01:43:26](https://github.com/leanprover-community/mathlib/commit/64b794a)
chore(analysis/complex/basic): rename `complex/normed_space` ([#9366](https://github.com/leanprover-community/mathlib/pull/9366))
This matches `module.complex_to_real`
#### Estimated changes
Modified src/analysis/complex/basic.lean




## [2021-09-24 21:40:17](https://github.com/leanprover-community/mathlib/commit/b0cd1f9)
chore(algebra/group): move is_unit.inv lemmas ([#9364](https://github.com/leanprover-community/mathlib/pull/9364))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.coe_inv_mul
- \+ *lemma* is_unit.mul_coe_inv

Modified src/group_theory/group_action/units.lean
- \+ *lemma* is_unit.inv_smul

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \- *lemma* is_unit.coe_inv_mul
- \- *lemma* is_unit.inv_smul
- \- *lemma* is_unit.mul_coe_inv



## [2021-09-24 21:40:16](https://github.com/leanprover-community/mathlib/commit/c42aaa3)
chore(data/pi): add missing `pi.{inv,neg}_def` ([#9361](https://github.com/leanprover-community/mathlib/pull/9361))
#### Estimated changes
Modified src/data/pi.lean
- \+ *lemma* pi.inv_def



## [2021-09-24 21:40:15](https://github.com/leanprover-community/mathlib/commit/8ff756c)
feat(group_theory/*/pointwise): Copy set lemmas about pointwise actions to subgroups and submonoids ([#9359](https://github.com/leanprover-community/mathlib/pull/9359))
This is pretty much just a copy-and-paste job. At least the proofs themselves don't need copying. The set lemmas being copied here are:
https://github.com/leanprover-community/mathlib/blob/a9cd8c259d59b0bdbe931a6f8e6084f800bd7162/src/algebra/pointwise.lean#L607-L680
I skipped the `preimage_smul` lemma for now because I couldn't think of a useful statement using `map`.
#### Estimated changes
Modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* add_subgroup.le_pointwise_smul_iff'
- \+ *lemma* add_subgroup.le_pointwise_smul_iff
- \+ *lemma* add_subgroup.mem_inv_pointwise_smul_iff'
- \+ *lemma* add_subgroup.mem_inv_pointwise_smul_iff
- \+ *lemma* add_subgroup.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* add_subgroup.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* add_subgroup.pointwise_smul_le_iff'
- \+ *lemma* add_subgroup.pointwise_smul_le_iff
- \+ *lemma* add_subgroup.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* add_subgroup.pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* add_subgroup.smul_mem_pointwise_smul_iff'
- \+ *lemma* add_subgroup.smul_mem_pointwise_smul_iff
- \+ *lemma* subgroup.le_pointwise_smul_iff'
- \+ *lemma* subgroup.mem_inv_pointwise_smul_iff'
- \+ *lemma* subgroup.mem_inv_pointwise_smul_iff
- \+ *lemma* subgroup.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* subgroup.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* subgroup.pointwise_smul_le_iff'
- \+ *lemma* subgroup.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* subgroup.pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* subgroup.pointwise_smul_subset_iff
- \+ *lemma* subgroup.smul_mem_pointwise_smul_iff'
- \+ *lemma* subgroup.smul_mem_pointwise_smul_iff
- \+ *lemma* subgroup.subset_pointwise_smul_iff

Modified src/group_theory/submonoid/pointwise.lean
- \+/\- *lemma* add_submonoid.coe_pointwise_smul
- \+ *lemma* add_submonoid.le_pointwise_smul_iff'
- \+ *lemma* add_submonoid.le_pointwise_smul_iff
- \+ *lemma* add_submonoid.mem_inv_pointwise_smul_iff'
- \+ *lemma* add_submonoid.mem_inv_pointwise_smul_iff
- \+ *lemma* add_submonoid.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* add_submonoid.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* add_submonoid.pointwise_smul_le_iff'
- \+ *lemma* add_submonoid.pointwise_smul_le_iff
- \+ *lemma* add_submonoid.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* add_submonoid.pointwise_smul_le_pointwise_smul_iff
- \+/\- *lemma* add_submonoid.smul_mem_pointwise_smul
- \+ *lemma* add_submonoid.smul_mem_pointwise_smul_iff'
- \+ *lemma* add_submonoid.smul_mem_pointwise_smul_iff
- \+/\- *lemma* submonoid.coe_pointwise_smul
- \+ *lemma* submonoid.le_pointwise_smul_iff'
- \+ *lemma* submonoid.mem_inv_pointwise_smul_iff'
- \+ *lemma* submonoid.mem_inv_pointwise_smul_iff
- \+ *lemma* submonoid.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* submonoid.mem_pointwise_smul_iff_inv_smul_mem
- \+ *lemma* submonoid.pointwise_smul_le_iff'
- \+ *lemma* submonoid.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* submonoid.pointwise_smul_le_pointwise_smul_iff
- \+ *lemma* submonoid.pointwise_smul_subset_iff
- \+/\- *lemma* submonoid.smul_mem_pointwise_smul
- \+ *lemma* submonoid.smul_mem_pointwise_smul_iff'
- \+ *lemma* submonoid.smul_mem_pointwise_smul_iff
- \+ *lemma* submonoid.subset_pointwise_smul_iff



## [2021-09-24 19:49:10](https://github.com/leanprover-community/mathlib/commit/18f06ec)
chore(measure_theory/integral/interval_integral): generalize `integral_smul` ([#9355](https://github.com/leanprover-community/mathlib/pull/9355))
Make sure that it works for scalar multiplication by a complex number.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_smul



## [2021-09-24 19:49:09](https://github.com/leanprover-community/mathlib/commit/7cb7246)
chore(linear_algebra/basic): add `linear_map.neg_comp`, generalize `linear_map.{sub,smul}_comp` ([#9335](https://github.com/leanprover-community/mathlib/pull/9335))
`sub_comp` had unnecessary requirements that the codomain of the right map be an additive group, while `smul_comp` did not support compatible actions.
This also golfs the proofs of all the `comp_*` lemmas to eliminate `simp`.
`smul_comp` and `comp_smul` are also both promoted to instances.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.add_comp
- \+/\- *lemma* linear_map.comp_add
- \+/\- *lemma* linear_map.comp_neg
- \+/\- *theorem* linear_map.comp_smul
- \+/\- *lemma* linear_map.comp_sub
- \+/\- *lemma* linear_map.neg_apply
- \+ *lemma* linear_map.neg_comp
- \+/\- *lemma* linear_map.sub_apply
- \+/\- *lemma* linear_map.sub_comp

Modified src/linear_algebra/eigenspace.lean




## [2021-09-24 19:49:07](https://github.com/leanprover-community/mathlib/commit/c794c5c)
chore(linear_algebra/basic): split out quotients and isomorphism theorems ([#9332](https://github.com/leanprover-community/mathlib/pull/9332))
`linear_algebra.basic` had become a very large file; I think too unwieldy to even be able to edit.
Fortunately there are some natural splits on content. I moved everything about quotients out to `linear_algebra.quotient`. Happily many files in `linear_algebra/` don't even need this, so we also get some significant import reductions.
I've also moved Noether's three isomorphism theorems for submodules to their own file.
#### Estimated changes
Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/epi_mono.lean


Modified src/linear_algebra/basic.lean
- \- *lemma* linear_map.coe_quotient_inf_to_sup_quotient
- \- *lemma* linear_map.ker_le_range_iff
- \- *lemma* linear_map.quot_ker_equiv_range_apply_mk
- \- *lemma* linear_map.quot_ker_equiv_range_symm_apply_image
- \- *lemma* linear_map.quotient_inf_equiv_sup_quotient_apply_mk
- \- *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff
- \- *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left
- \- *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right
- \- *def* linear_map.quotient_inf_to_sup_quotient
- \- *lemma* linear_map.range_eq_top_of_cancel
- \- *lemma* linear_map.range_mkq_comp
- \- *lemma* submodule.coe_quot_equiv_of_eq_bot_symm
- \- *theorem* submodule.comap_liftq
- \- *theorem* submodule.comap_map_mkq
- \- *def* submodule.comap_mkq.order_embedding
- \- *def* submodule.comap_mkq.rel_iso
- \- *lemma* submodule.comap_mkq_embedding_eq
- \- *theorem* submodule.ker_liftq
- \- *theorem* submodule.ker_liftq_eq_bot
- \- *theorem* submodule.ker_mkq
- \- *lemma* submodule.le_comap_mkq
- \- *def* submodule.liftq
- \- *theorem* submodule.liftq_apply
- \- *theorem* submodule.liftq_mkq
- \- *lemma* submodule.linear_map_qext
- \- *theorem* submodule.map_liftq
- \- *theorem* submodule.map_mkq_eq_top
- \- *def* submodule.mapq
- \- *theorem* submodule.mapq_apply
- \- *def* submodule.mapq_linear
- \- *theorem* submodule.mapq_mkq
- \- *def* submodule.mkq
- \- *theorem* submodule.mkq_apply
- \- *theorem* submodule.mkq_map_self
- \- *def* submodule.quot_equiv_of_eq
- \- *def* submodule.quot_equiv_of_eq_bot
- \- *lemma* submodule.quot_equiv_of_eq_bot_apply_mk
- \- *lemma* submodule.quot_equiv_of_eq_bot_symm_apply
- \- *lemma* submodule.quot_equiv_of_eq_mk
- \- *lemma* submodule.quot_hom_ext
- \- *theorem* submodule.quotient.mk'_eq_mk
- \- *def* submodule.quotient.mk
- \- *theorem* submodule.quotient.mk_add
- \- *theorem* submodule.quotient.mk_eq_mk
- \- *theorem* submodule.quotient.mk_eq_zero
- \- *theorem* submodule.quotient.mk_neg
- \- *theorem* submodule.quotient.mk_nsmul
- \- *theorem* submodule.quotient.mk_smul
- \- *theorem* submodule.quotient.mk_sub
- \- *lemma* submodule.quotient.mk_surjective
- \- *theorem* submodule.quotient.mk_zero
- \- *lemma* submodule.quotient.nontrivial_of_lt_top
- \- *theorem* submodule.quotient.quot_mk_eq_mk
- \- *def* submodule.quotient
- \- *def* submodule.quotient_quotient_equiv_quotient
- \- *def* submodule.quotient_quotient_equiv_quotient_aux
- \- *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk
- \- *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk_mk
- \- *def* submodule.quotient_rel
- \- *theorem* submodule.range_liftq
- \- *theorem* submodule.range_mkq
- \- *lemma* submodule.span_preimage_eq

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp.lean


Added src/linear_algebra/isomorphisms.lean
- \+ *lemma* linear_map.coe_quotient_inf_to_sup_quotient
- \+ *lemma* linear_map.quot_ker_equiv_range_apply_mk
- \+ *lemma* linear_map.quot_ker_equiv_range_symm_apply_image
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_apply_mk
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right
- \+ *def* linear_map.quotient_inf_to_sup_quotient
- \+ *def* submodule.quotient_quotient_equiv_quotient
- \+ *def* submodule.quotient_quotient_equiv_quotient_aux
- \+ *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk
- \+ *lemma* submodule.quotient_quotient_equiv_quotient_aux_mk_mk

Modified src/linear_algebra/projection.lean


Added src/linear_algebra/quotient.lean
- \+ *lemma* linear_map.ker_le_range_iff
- \+ *lemma* linear_map.range_eq_top_of_cancel
- \+ *lemma* linear_map.range_mkq_comp
- \+ *lemma* submodule.coe_quot_equiv_of_eq_bot_symm
- \+ *theorem* submodule.comap_liftq
- \+ *theorem* submodule.comap_map_mkq
- \+ *def* submodule.comap_mkq.order_embedding
- \+ *def* submodule.comap_mkq.rel_iso
- \+ *lemma* submodule.comap_mkq_embedding_eq
- \+ *theorem* submodule.ker_liftq
- \+ *theorem* submodule.ker_liftq_eq_bot
- \+ *theorem* submodule.ker_mkq
- \+ *lemma* submodule.le_comap_mkq
- \+ *def* submodule.liftq
- \+ *theorem* submodule.liftq_apply
- \+ *theorem* submodule.liftq_mkq
- \+ *lemma* submodule.linear_map_qext
- \+ *theorem* submodule.map_liftq
- \+ *theorem* submodule.map_mkq_eq_top
- \+ *def* submodule.mapq
- \+ *theorem* submodule.mapq_apply
- \+ *def* submodule.mapq_linear
- \+ *theorem* submodule.mapq_mkq
- \+ *def* submodule.mkq
- \+ *theorem* submodule.mkq_apply
- \+ *theorem* submodule.mkq_map_self
- \+ *def* submodule.quot_equiv_of_eq
- \+ *def* submodule.quot_equiv_of_eq_bot
- \+ *lemma* submodule.quot_equiv_of_eq_bot_apply_mk
- \+ *lemma* submodule.quot_equiv_of_eq_bot_symm_apply
- \+ *lemma* submodule.quot_equiv_of_eq_mk
- \+ *lemma* submodule.quot_hom_ext
- \+ *theorem* submodule.quotient.mk'_eq_mk
- \+ *def* submodule.quotient.mk
- \+ *theorem* submodule.quotient.mk_add
- \+ *theorem* submodule.quotient.mk_eq_mk
- \+ *theorem* submodule.quotient.mk_eq_zero
- \+ *theorem* submodule.quotient.mk_neg
- \+ *theorem* submodule.quotient.mk_nsmul
- \+ *theorem* submodule.quotient.mk_smul
- \+ *theorem* submodule.quotient.mk_sub
- \+ *lemma* submodule.quotient.mk_surjective
- \+ *theorem* submodule.quotient.mk_zero
- \+ *lemma* submodule.quotient.nontrivial_of_lt_top
- \+ *theorem* submodule.quotient.quot_mk_eq_mk
- \+ *def* submodule.quotient
- \+ *def* submodule.quotient_rel
- \+ *theorem* submodule.range_liftq
- \+ *theorem* submodule.range_mkq
- \+ *lemma* submodule.span_preimage_eq

Modified src/linear_algebra/std_basis.lean


Modified src/ring_theory/ideal/basic.lean




## [2021-09-24 19:49:06](https://github.com/leanprover-community/mathlib/commit/6f2d1ba)
feat(data/dfinsupp): add submodule.bsupr_eq_range_dfinsupp_lsum ([#9202](https://github.com/leanprover-community/mathlib/pull/9202))
Also a version for `add_submonoid`. Unfortunately the proofs are almost identical, but that's consistent with the surrounding bits of the file anyway.
The key result is a dfinsupp version of the lemma in [#8246](https://github.com/leanprover-community/mathlib/pull/8246),
```lean
x ∈ (⨆ i (H : p i), f i) ↔ ∃ v : ι →₀ M, (∀ i, v i ∈ f i) ∧ ∑ i in v.support, v i = x ∧ (∀ i, ¬ p i → v i = 0) :=
```
as
```lean
x ∈ (⨆ i (h : p i), S i) ↔ ∃ f : Π₀ i, S i, dfinsupp.lsum ℕ (λ i, (S i).subtype) (f.filter p) = x
```
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom
- \+ *lemma* add_submonoid.mem_bsupr_iff_exists_dfinsupp

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* submodule.bsupr_eq_range_dfinsupp_lsum
- \+ *lemma* submodule.mem_bsupr_iff_exists_dfinsupp



## [2021-09-24 13:55:52](https://github.com/leanprover-community/mathlib/commit/981f8ba)
chore(*): remove some `assume`s ([#9365](https://github.com/leanprover-community/mathlib/pull/9365))
#### Estimated changes
Modified src/data/nat/basic.lean


Modified src/data/set/finite.lean




## [2021-09-24 12:53:07](https://github.com/leanprover-community/mathlib/commit/e14cf58)
feat(measure_theory/function/conditional_expectation): define the conditional expectation of a function, prove the equality of integrals ([#9114](https://github.com/leanprover-community/mathlib/pull/9114))
This PR puts together the generalized Bochner integral construction of [#8939](https://github.com/leanprover-community/mathlib/pull/8939) and the set function `condexp_ind` of [#8920](https://github.com/leanprover-community/mathlib/pull/8920) to define the conditional expectation of a function.
The equality of integrals that defines the conditional expectation is proven in `set_integral_condexp`.
#### Estimated changes
Modified src/measure_theory/decomposition/radon_nikodym.lean


Modified src/measure_theory/function/conditional_expectation.lean
- \+ *def* measure_theory.Lp_meas_to_Lp_trim
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_ae_eq
- \+ *def* measure_theory.Lp_meas_to_Lp_trim_lie
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_lie_symm_indicator
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_smul
- \+ *def* measure_theory.Lp_trim_to_Lp_meas
- \+ *lemma* measure_theory.Lp_trim_to_Lp_meas_ae_eq
- \+ *lemma* measure_theory.ae_eq_condexp_of_forall_set_integral_eq
- \+ *lemma* measure_theory.ae_measurable'_condexp_L1
- \+ *lemma* measure_theory.ae_measurable'_condexp_L1_clm
- \+ *def* measure_theory.condexp
- \+ *def* measure_theory.condexp_L1
- \+ *lemma* measure_theory.condexp_L1_add
- \+ *def* measure_theory.condexp_L1_clm
- \+ *lemma* measure_theory.condexp_L1_clm_Lp_meas
- \+ *lemma* measure_theory.condexp_L1_clm_indicator_const
- \+ *lemma* measure_theory.condexp_L1_clm_indicator_const_Lp
- \+ *lemma* measure_theory.condexp_L1_clm_of_ae_measurable'
- \+ *lemma* measure_theory.condexp_L1_clm_smul
- \+ *lemma* measure_theory.condexp_L1_eq
- \+ *lemma* measure_theory.condexp_L1_neg
- \+ *lemma* measure_theory.condexp_L1_of_ae_measurable'
- \+ *lemma* measure_theory.condexp_L1_smul
- \+ *lemma* measure_theory.condexp_L1_sub
- \+ *lemma* measure_theory.condexp_L1_undef
- \+ *lemma* measure_theory.condexp_L1_zero
- \+ *lemma* measure_theory.condexp_add
- \+ *lemma* measure_theory.condexp_ae_eq_condexp_L1
- \+ *lemma* measure_theory.condexp_ae_eq_condexp_L1_clm
- \+ *lemma* measure_theory.condexp_const
- \+ *lemma* measure_theory.condexp_ind_of_measurable
- \+ *lemma* measure_theory.condexp_neg
- \+ *lemma* measure_theory.condexp_of_measurable
- \+ *lemma* measure_theory.condexp_smul
- \+ *lemma* measure_theory.condexp_sub
- \+ *lemma* measure_theory.condexp_undef
- \+ *lemma* measure_theory.condexp_zero
- \+ *lemma* measure_theory.dominated_fin_meas_additive_condexp_ind
- \+ *lemma* measure_theory.integrable_condexp
- \+ *lemma* measure_theory.integrable_condexp_L1
- \+ *lemma* measure_theory.integral_condexp
- \+ *lemma* measure_theory.measurable_condexp
- \+ *lemma* measure_theory.set_integral_condexp
- \+ *lemma* measure_theory.set_integral_condexp_L1
- \+ *lemma* measure_theory.set_integral_condexp_L1_clm
- \+ *lemma* measure_theory.set_integral_condexp_L1_clm_of_measure_ne_top
- \+ *lemma* measure_theory.set_integral_condexp_ind
- \+ *lemma* measure_theory.set_integral_condexp_ind_smul

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_indicator_const_Lp
- \+ *lemma* measure_theory.set_integral_indicator_const_Lp



## [2021-09-24 11:04:41](https://github.com/leanprover-community/mathlib/commit/0db6caf)
feat(linear_algebra/affine_space/affine_map): add missing simp lemma `affine_map.homothety_apply_same` ([#9360](https://github.com/leanprover-community/mathlib/pull/9360))
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.homothety_apply_same



## [2021-09-24 11:04:40](https://github.com/leanprover-community/mathlib/commit/48883dc)
chore(algebra/basic): split out facts about lmul ([#9300](https://github.com/leanprover-community/mathlib/pull/9300))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* algebra.commute_lmul_left_right
- \- *def* algebra.lmul'
- \- *lemma* algebra.lmul'_apply
- \- *def* algebra.lmul
- \- *lemma* algebra.lmul_apply
- \- *lemma* algebra.lmul_injective
- \- *def* algebra.lmul_left
- \- *lemma* algebra.lmul_left_apply
- \- *lemma* algebra.lmul_left_eq_zero_iff
- \- *lemma* algebra.lmul_left_injective
- \- *lemma* algebra.lmul_left_mul
- \- *lemma* algebra.lmul_left_one
- \- *def* algebra.lmul_left_right
- \- *lemma* algebra.lmul_left_right_apply
- \- *lemma* algebra.lmul_left_zero_eq_zero
- \- *def* algebra.lmul_right
- \- *lemma* algebra.lmul_right_apply
- \- *lemma* algebra.lmul_right_eq_zero_iff
- \- *lemma* algebra.lmul_right_injective
- \- *lemma* algebra.lmul_right_mul
- \- *lemma* algebra.lmul_right_one
- \- *lemma* algebra.lmul_right_zero_eq_zero
- \- *lemma* algebra.pow_lmul_left
- \- *lemma* algebra.pow_lmul_right

Added src/algebra/algebra/bilinear.lean
- \+ *lemma* algebra.commute_lmul_left_right
- \+ *def* algebra.lmul'
- \+ *lemma* algebra.lmul'_apply
- \+ *def* algebra.lmul
- \+ *lemma* algebra.lmul_apply
- \+ *lemma* algebra.lmul_injective
- \+ *def* algebra.lmul_left
- \+ *lemma* algebra.lmul_left_apply
- \+ *lemma* algebra.lmul_left_eq_zero_iff
- \+ *lemma* algebra.lmul_left_injective
- \+ *lemma* algebra.lmul_left_mul
- \+ *lemma* algebra.lmul_left_one
- \+ *def* algebra.lmul_left_right
- \+ *lemma* algebra.lmul_left_right_apply
- \+ *lemma* algebra.lmul_left_zero_eq_zero
- \+ *def* algebra.lmul_right
- \+ *lemma* algebra.lmul_right_apply
- \+ *lemma* algebra.lmul_right_eq_zero_iff
- \+ *lemma* algebra.lmul_right_injective
- \+ *lemma* algebra.lmul_right_mul
- \+ *lemma* algebra.lmul_right_one
- \+ *lemma* algebra.lmul_right_zero_eq_zero
- \+ *lemma* algebra.pow_lmul_left
- \+ *lemma* algebra.pow_lmul_right

Modified src/algebra/algebra/operations.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/determinant.lean


Renamed src/linear_algebra/multilinear.lean to src/linear_algebra/multilinear/basic.lean
- \- *def* multilinear_map.dom_coprod'
- \- *lemma* multilinear_map.dom_coprod'_apply
- \- *def* multilinear_map.dom_coprod
- \- *lemma* multilinear_map.dom_coprod_dom_dom_congr_sum_congr

Added src/linear_algebra/multilinear/tensor_product.lean
- \+ *def* multilinear_map.dom_coprod'
- \+ *lemma* multilinear_map.dom_coprod'_apply
- \+ *def* multilinear_map.dom_coprod
- \+ *lemma* multilinear_map.dom_coprod_dom_dom_congr_sum_congr

Modified src/linear_algebra/pi_tensor_product.lean


Modified src/ring_theory/nilpotent.lean


Modified src/topology/algebra/multilinear.lean




## [2021-09-24 11:04:39](https://github.com/leanprover-community/mathlib/commit/854e5c6)
refactor(measure_theory/measure/regular): add `inner_regular`, `outer_regular`, generalize ([#9283](https://github.com/leanprover-community/mathlib/pull/9283))
### Regular measures
* add a non-class predicate `inner_regular` to prove some lemmas once, not twice;
* add TC `outer_regular`, drop primed lemmas;
* consistently use `≠ ∞`, `≠ 0` in the assumptions;
* drop some typeclass requirements.
### Other changes
* add a few lemmas about subtraction to `data.real.ennreal`;
* add `ennreal.add_lt_add_left`, `ennreal.add_lt_add_right`, and use them;
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.add_lt_add_left
- \+ *lemma* ennreal.add_lt_add_right
- \+ *lemma* ennreal.half_le_self
- \+ *lemma* ennreal.lt_div_iff_mul_lt
- \+ *lemma* ennreal.lt_sub_comm
- \+ *lemma* ennreal.mul_lt_of_lt_div'

Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* is_compact.exists_open_superset_measure_lt_top'
- \+ *lemma* is_compact.exists_open_superset_measure_lt_top
- \+ *theorem* measurable_set.induction_on_open
- \+ *def* measure_theory.measure.finite_spanning_sets_in_compact
- \+ *def* measure_theory.measure.finite_spanning_sets_in_open

Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measure/content.lean
- \- *def* measure_theory.content.measure

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.le_measure_diff
- \+ *lemma* measure_theory.measure_compl_le_add_iff
- \+ *lemma* measure_theory.measure_compl_le_add_of_le_add
- \+ *lemma* measure_theory.measure_diff_lt_of_lt_add

Modified src/measure_theory/measure/regular.lean
- \+ *lemma* is_open.exists_lt_is_closed
- \- *lemma* is_open.exists_lt_is_closed_of_gt
- \+ *lemma* measurable_set.exists_is_closed_diff_lt
- \+ *lemma* measurable_set.exists_is_closed_lt_add
- \+ *lemma* measurable_set.exists_is_compact_diff_lt
- \+ *lemma* measurable_set.exists_is_compact_lt_add
- \+ *lemma* measurable_set.exists_is_open_diff_lt
- \- *lemma* measurable_set.exists_is_open_lt_of_lt'
- \- *lemma* measurable_set.exists_is_open_lt_of_lt
- \- *lemma* measurable_set.exists_lt_is_closed_of_lt_top
- \- *lemma* measurable_set.exists_lt_is_closed_of_lt_top_of_pos
- \+ *lemma* measurable_set.exists_lt_is_closed_of_ne_top
- \- *lemma* measurable_set.exists_lt_is_compact_of_lt_top
- \- *lemma* measurable_set.exists_lt_is_compact_of_lt_top_of_pos
- \+ *lemma* measurable_set.exists_lt_is_compact_of_ne_top
- \- *lemma* measurable_set.measure_eq_infi_is_open'
- \- *lemma* measurable_set.measure_eq_infi_is_open
- \- *lemma* measurable_set.measure_eq_supr_is_closed_of_is_finite_measure
- \- *lemma* measurable_set.measure_eq_supr_is_closed_of_lt_top
- \+ *lemma* measurable_set.measure_eq_supr_is_closed_of_ne_top
- \- *lemma* measurable_set.measure_eq_supr_is_compact_of_lt_top
- \+ *lemma* measurable_set.measure_eq_supr_is_compact_of_ne_top
- \+ *lemma* measure_theory.measure.inner_regular.exists_subset_lt_add
- \+ *lemma* measure_theory.measure.inner_regular.is_compact_is_closed
- \+ *lemma* measure_theory.measure.inner_regular.map
- \+ *lemma* measure_theory.measure.inner_regular.measurable_set_of_open
- \+ *lemma* measure_theory.measure.inner_regular.measure_eq_supr
- \+ *lemma* measure_theory.measure.inner_regular.of_pseudo_emetric_space
- \+ *lemma* measure_theory.measure.inner_regular.smul
- \+ *lemma* measure_theory.measure.inner_regular.trans
- \+ *lemma* measure_theory.measure.inner_regular.weakly_regular_of_finite
- \+ *def* measure_theory.measure.inner_regular
- \+ *lemma* measure_theory.measure.regular.inner_regular_measurable
- \- *lemma* measure_theory.measure.weakly_regular.exists_closed_subset_self_subset_open_of_pos
- \- *lemma* measure_theory.measure.weakly_regular.exists_subset_is_open_measure_lt_top
- \+ *lemma* measure_theory.measure.weakly_regular.inner_regular_measurable
- \- *lemma* measure_theory.measure.weakly_regular.inner_regular_of_pseudo_emetric_space
- \- *lemma* measure_theory.measure.weakly_regular.restrict_of_is_open
- \+/\- *lemma* measure_theory.measure.weakly_regular.restrict_of_measurable_set
- \- *theorem* measure_theory.measure.weakly_regular.weakly_regular_of_inner_regular_of_is_finite_measure
- \+ *lemma* set.exists_is_open_lt_add
- \+ *lemma* set.exists_is_open_lt_of_lt
- \+ *lemma* set.measure_eq_infi_is_open

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/emetric_space.lean




## [2021-09-24 11:04:38](https://github.com/leanprover-community/mathlib/commit/a512db1)
feat(linear_algebra/free_modules): add instances ([#9223](https://github.com/leanprover-community/mathlib/pull/9223))
We add the instances `module.finite` and `module.free` on `(M →+ N)`, for `M` and `N` finite and free abelian groups.
We already have the more general version over any ring, for `(M →ₗ[R] N)`. (They are mathematically more general, but not for Lean.)
#### Estimated changes
Modified src/linear_algebra/free_module.lean




## [2021-09-24 08:36:36](https://github.com/leanprover-community/mathlib/commit/6a9ba18)
feat(measure_theory): `ι → α ≃ᵐ α` if `[unique ι]` ([#9353](https://github.com/leanprover-community/mathlib/pull/9353))
* define versions of `equiv.fun_unique` for `order_iso` and
  `measurable_equiv`;
* use the latter to relate integrals over (sets in) `ι → α` and `α`,
  where `ι` is a type with an unique element.
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.integral_fun_unique'
- \+ *lemma* measure_theory.integral_fun_unique
- \+ *lemma* measure_theory.integral_fun_unique_pi'
- \+ *lemma* measure_theory.integral_fun_unique_pi
- \+ *lemma* measure_theory.measure.map_fun_unique
- \+ *lemma* measure_theory.measure.pi_unique_eq_map
- \+ *lemma* measure_theory.set_integral_fun_unique'
- \+ *lemma* measure_theory.set_integral_fun_unique
- \+ *lemma* measure_theory.set_integral_fun_unique_pi'
- \+ *lemma* measure_theory.set_integral_fun_unique_pi

Modified src/measure_theory/measurable_space.lean
- \+ *def* measurable_equiv.fun_unique

Modified src/order/rel_iso.lean
- \+ *def* order_iso.fun_unique
- \+ *lemma* order_iso.fun_unique_symm_apply



## [2021-09-24 08:36:35](https://github.com/leanprover-community/mathlib/commit/9e59e29)
feat(category_theory/opposites): Add is_iso_op ([#9319](https://github.com/leanprover-community/mathlib/pull/9319))
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.op_inv



## [2021-09-24 08:36:34](https://github.com/leanprover-community/mathlib/commit/9618d73)
feat(algebra,group_theory): smul_(g)pow ([#9311](https://github.com/leanprover-community/mathlib/pull/9311))
Rename `smul_pow` to `smul_pow'` to match `smul_mul'`. Instead provide the distributing lemma `smul_pow` where the power distributes onto the scalar as well. Provide the group action `smul_gpow` as well.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* smul_pow'
- \+ *lemma* smul_pow

Modified src/algebra/polynomial/group_ring_action.lean


Modified src/field_theory/fixed.lean


Modified src/group_theory/group_action/basic.lean
- \- *lemma* smul_pow

Modified src/group_theory/group_action/group.lean
- \+ *lemma* smul_gpow



## [2021-09-24 06:10:23](https://github.com/leanprover-community/mathlib/commit/a9cd8c2)
feat(linear_algebra): redefine `linear_map` and `linear_equiv` to be semilinear ([#9272](https://github.com/leanprover-community/mathlib/pull/9272))
This PR redefines `linear_map` and `linear_equiv` to be semilinear maps/equivs.
A semilinear map `f` is a map from an `R`-module to an `S`-module with a ring homomorphism `σ` between `R` and `S`, such that `f (c • x) = (σ c) • (f x)`. If we plug in the identity into `σ`, we get regular linear maps, and if we plug in the complex conjugate, we get conjugate linear maps. There are also other examples (e.g. Frobenius-linear maps) where this is useful which are covered by this general formulation. This was discussed on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps), and a few preliminaries for this have already been merged.
The main issue that we had to overcome involved composition of semilinear maps, and `symm` for linear equivalences: having things like `σ₂₃.comp σ₁₂` in the types of semilinear maps creates major problems. For example, we want the composition of two conjugate-linear maps to be a regular linear map, not a `conj.comp conj`-linear map. To solve this issue, following a discussion from back in January, we created two typeclasses to make Lean infer the right ring hom. The first one is `[ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]` which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`, and the second one is `[ring_hom_inv_pair σ₁₂ σ₂₁]` which states that `σ₁₂` and `σ₂₁` are inverses of each other. There is also `[ring_hom_surjective σ]`, which is a necessary assumption to generalize some basic lemmas (such as `submodule.map`). Note that we have introduced notation to ensure that regular linear maps can still be used as before, i.e. `M →ₗ[R] N` still works as before to mean a regular linear map.
The main changes are in `algebra/module/linear_map.lean`, `data/equiv/module.lean` and `linear_algebra/basic.lean` (and `algebra/ring/basic.lean` for the `ring_hom` typeclasses). The changes in other files fall into the following categories:
1. When defining a regular linear map directly using the structure (i.e. when specifying `to_fun`, `map_smul'` and so on), there is a `ring_hom.id` that shows up in `map_smul'`. This mostly involves dsimping it away.
2. Elaboration seems slightly more brittle, and it fails a little bit more often than before. For example, when `f` is a linear map and `g` is something that can be coerced to a linear map (say a linear equiv), one has to write `↑g` to make `f.comp ↑g` work, or sometimes even to add a type annotation. This also occurs when using `trans` twice (i.e. `e₁.trans (e₂.trans e₃)`). In those places, we use the notation defined in [#8857](https://github.com/leanprover-community/mathlib/pull/8857) `∘ₗ` and `≪≫ₗ`. 
3. It seems to exacerbate the bug discussed [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/odd.20repeated.20type.20class.20search) for reasons that we don't understand all that well right now. It manifests itself in very slow calls to the tactic `ext`, and the quick fix is to manually use the right ext lemma.
4. The PR triggered a few timeouts in proofs that were already close to the edge. Those were sped up.
5. A few random other issues that didn't arise often enough to see a pattern.
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/direct_sum.lean


Modified src/algebra/lie/submodule.lean
- \+/\- *lemma* lie_ideal.comap_coe_submodule

Modified src/algebra/lie/tensor_product.lean


Modified src/algebra/lie/weights.lean


Modified src/algebra/module/linear_map.lean
- \+/\- *def* distrib_mul_action_hom.to_linear_map
- \+/\- *lemma* linear_map.coe_comp
- \+/\- *theorem* linear_map.coe_injective
- \+/\- *def* linear_map.comp
- \+/\- *lemma* linear_map.comp_apply
- \+/\- *theorem* linear_map.ext_ring
- \+/\- *theorem* linear_map.ext_ring_iff
- \+/\- *def* linear_map.inverse
- \+/\- *theorem* linear_map.is_linear
- \+/\- *lemma* linear_map.map_smul
- \+ *lemma* linear_map.map_smul_inv
- \+ *lemma* linear_map.map_smulₛₗ
- \+/\- *lemma* linear_map.mk_coe
- \+/\- *def* linear_map.restrict_scalars
- \+/\- *lemma* linear_map.restrict_scalars_inj
- \+/\- *def* linear_map.to_add_monoid_hom

Modified src/algebra/module/submodule_pointwise.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/ring/basic.lean


Added src/algebra/ring/comp_typeclasses.lean
- \+ *lemma* ring_hom.is_surjective
- \+ *lemma* ring_hom_comp_triple.comp_apply
- \+ *lemma* ring_hom_inv_pair.comp_apply_eq
- \+ *lemma* ring_hom_inv_pair.comp_apply_eq₂
- \+ *lemma* ring_hom_surjective.comp

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/isometry.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/data/equiv/module.lean
- \+/\- *theorem* linear_equiv.coe_coe
- \+/\- *lemma* linear_equiv.coe_of_involutive
- \+/\- *theorem* linear_equiv.map_smul
- \+ *theorem* linear_equiv.map_smulₛₗ
- \+/\- *lemma* linear_equiv.mk_coe'
- \+/\- *def* linear_equiv.of_involutive
- \+/\- *def* linear_equiv.simps.symm_apply
- \+/\- *def* linear_equiv.symm
- \+/\- *lemma* linear_equiv.symm_bijective
- \+/\- *theorem* linear_equiv.symm_symm
- \+/\- *lemma* linear_equiv.symm_trans_apply
- \+/\- *def* linear_equiv.to_equiv
- \+/\- *lemma* linear_equiv.to_equiv_inj
- \+/\- *lemma* linear_equiv.to_equiv_injective
- \+/\- *lemma* linear_equiv.to_linear_map_eq_coe
- \+/\- *lemma* linear_equiv.to_linear_map_inj
- \+/\- *lemma* linear_equiv.to_linear_map_injective
- \+/\- *def* linear_equiv.trans
- \+/\- *theorem* linear_equiv.trans_apply
- \+/\- *lemma* linear_equiv.trans_refl

Modified src/data/mv_polynomial/pderiv.lean


Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/taylor.lean


Modified src/geometry/manifold/derivation_bundle.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* finsupp.smul_sum
- \+/\- *lemma* finsupp.sum_smul_index_linear_map'
- \+/\- *lemma* linear_equiv.coe_zero
- \+/\- *lemma* linear_equiv.eq_bot_of_equiv
- \+/\- *theorem* linear_equiv.ker_comp
- \+/\- *lemma* linear_equiv.map_dfinsupp_sum_add_hom
- \+/\- *lemma* linear_equiv.map_eq_comap
- \+/\- *lemma* linear_equiv.map_finsupp_sum
- \+/\- *theorem* linear_equiv.of_bijective_apply
- \+/\- *theorem* linear_equiv.of_injective_apply
- \+/\- *def* linear_equiv.of_left_inverse
- \+/\- *lemma* linear_equiv.of_left_inverse_apply
- \+/\- *lemma* linear_equiv.of_left_inverse_symm_apply
- \+/\- *def* linear_equiv.of_linear
- \+/\- *theorem* linear_equiv.of_linear_symm_apply
- \+/\- *def* linear_equiv.of_submodule'
- \+/\- *lemma* linear_equiv.of_submodule'_apply
- \+/\- *lemma* linear_equiv.of_submodule'_symm_apply
- \+/\- *lemma* linear_equiv.of_submodule'_to_linear_map
- \+/\- *def* linear_equiv.of_submodule
- \+/\- *lemma* linear_equiv.of_submodule_symm_apply
- \+/\- *def* linear_equiv.of_submodules
- \+/\- *lemma* linear_equiv.of_submodules_apply
- \+/\- *lemma* linear_equiv.of_submodules_symm_apply
- \+/\- *theorem* linear_equiv.range_comp
- \+/\- *lemma* linear_equiv.zero_apply
- \+/\- *lemma* linear_equiv.zero_symm
- \+/\- *lemma* linear_map.add_apply
- \+/\- *lemma* linear_map.add_comp
- \+/\- *def* linear_map.cod_restrict
- \+/\- *theorem* linear_map.cod_restrict_apply
- \+/\- *lemma* linear_map.coe_dfinsupp_sum
- \+/\- *lemma* linear_map.coe_finsupp_sum
- \+/\- *lemma* linear_map.coe_fn_sum
- \+/\- *theorem* linear_map.coe_smul_right
- \+/\- *theorem* linear_map.comap_cod_restrict
- \+/\- *theorem* linear_map.comap_injective
- \+/\- *theorem* linear_map.comap_le_comap_iff
- \+/\- *lemma* linear_map.comp_add
- \+/\- *theorem* linear_map.comp_assoc
- \+/\- *lemma* linear_map.comp_cod_restrict
- \+/\- *lemma* linear_map.comp_ker_subtype
- \+/\- *lemma* linear_map.comp_neg
- \+/\- *lemma* linear_map.comp_sub
- \+/\- *theorem* linear_map.comp_zero
- \+/\- *lemma* linear_map.default_def
- \+/\- *lemma* linear_map.dfinsupp_sum_apply
- \+/\- *theorem* linear_map.disjoint_ker
- \+/\- *def* linear_map.dom_restrict
- \+/\- *lemma* linear_map.dom_restrict_apply
- \+/\- *lemma* linear_map.eq_on_span'
- \+/\- *lemma* linear_map.eq_on_span
- \+/\- *def* linear_map.eval_add_monoid_hom
- \+/\- *lemma* linear_map.ext_on
- \+/\- *lemma* linear_map.ext_on_range
- \+/\- *lemma* linear_map.finsupp_sum_apply
- \+/\- *def* linear_map.ker
- \+/\- *lemma* linear_map.ker_cod_restrict
- \+/\- *theorem* linear_map.ker_comp
- \+/\- *lemma* linear_map.ker_comp_of_ker_eq_bot
- \+/\- *theorem* linear_map.ker_eq_bot'
- \+/\- *lemma* linear_map.ker_eq_bot_of_cancel
- \+/\- *theorem* linear_map.ker_eq_bot_of_injective
- \+/\- *theorem* linear_map.ker_eq_bot_of_inverse
- \+/\- *theorem* linear_map.ker_eq_top
- \+/\- *lemma* linear_map.ker_le_iff
- \+/\- *theorem* linear_map.ker_le_ker_comp
- \+/\- *lemma* linear_map.ker_le_range_iff
- \+/\- *theorem* linear_map.ker_zero
- \+/\- *lemma* linear_map.le_ker_iff_map
- \+/\- *theorem* linear_map.map_cod_restrict
- \+/\- *theorem* linear_map.map_coe_ker
- \+/\- *lemma* linear_map.map_dfinsupp_sum
- \+/\- *lemma* linear_map.map_dfinsupp_sum_add_hom
- \+/\- *theorem* linear_map.map_eq_top_iff
- \+/\- *lemma* linear_map.map_finsupp_sum
- \+/\- *theorem* linear_map.map_injective
- \+/\- *theorem* linear_map.map_le_map_iff'
- \+/\- *theorem* linear_map.map_le_map_iff
- \+/\- *lemma* linear_map.map_le_range
- \+/\- *theorem* linear_map.mem_ker
- \+/\- *theorem* linear_map.mem_range
- \+/\- *theorem* linear_map.mem_range_self
- \+/\- *def* linear_map.range
- \+/\- *lemma* linear_map.range_cod_restrict
- \+/\- *theorem* linear_map.range_coe
- \+/\- *theorem* linear_map.range_comp
- \+/\- *theorem* linear_map.range_comp_le_range
- \+/\- *lemma* linear_map.range_comp_of_range_eq_top
- \+/\- *theorem* linear_map.range_eq_bot
- \+/\- *lemma* linear_map.range_eq_map
- \+/\- *theorem* linear_map.range_eq_top
- \+/\- *lemma* linear_map.range_eq_top_of_cancel
- \+/\- *lemma* linear_map.range_le_bot_iff
- \+/\- *lemma* linear_map.range_le_iff_comap
- \+/\- *lemma* linear_map.range_le_ker_iff
- \+/\- *lemma* linear_map.range_mkq_comp
- \+/\- *def* linear_map.range_restrict
- \+/\- *theorem* linear_map.range_zero
- \+/\- *def* linear_map.smul_right
- \+/\- *theorem* linear_map.smul_right_apply
- \+/\- *lemma* linear_map.sub_comp
- \+/\- *lemma* linear_map.subtype_comp_cod_restrict
- \+/\- *lemma* linear_map.sum_apply
- \+/\- *def* linear_map.to_add_monoid_hom'
- \+/\- *lemma* linear_map.zero_apply
- \+/\- *theorem* linear_map.zero_comp
- \+/\- *lemma* pi_eq_sum_univ
- \+/\- *lemma* submodule.apply_coe_mem_map
- \+/\- *lemma* submodule.coe_equiv_map_of_injective_apply
- \+/\- *def* submodule.comap
- \+/\- *theorem* submodule.comap_bot
- \+/\- *lemma* submodule.comap_coe
- \+/\- *lemma* submodule.comap_comp
- \+/\- *lemma* submodule.comap_equiv_eq_map_symm
- \+/\- *lemma* submodule.comap_inf
- \+/\- *lemma* submodule.comap_infi
- \+/\- *lemma* submodule.comap_le_comap_iff_of_surjective
- \+/\- *lemma* submodule.comap_le_comap_smul
- \+/\- *theorem* submodule.comap_liftq
- \+/\- *lemma* submodule.comap_map_eq
- \+/\- *lemma* submodule.comap_map_eq_self
- \+/\- *lemma* submodule.comap_mono
- \+/\- *lemma* submodule.comap_top
- \+/\- *lemma* submodule.comap_zero
- \+/\- *def* submodule.compatible_maps
- \+/\- *lemma* submodule.gc_map_comap
- \+/\- *lemma* submodule.inf_comap_le_comap_add
- \+/\- *theorem* submodule.ker_liftq
- \+/\- *theorem* submodule.ker_liftq_eq_bot
- \+/\- *lemma* submodule.le_comap_map
- \+/\- *def* submodule.liftq
- \+/\- *theorem* submodule.liftq_apply
- \+/\- *theorem* submodule.liftq_mkq
- \+/\- *lemma* submodule.linear_map_qext
- \+/\- *def* submodule.map
- \+/\- *lemma* submodule.map_add_le
- \+/\- *lemma* submodule.map_bot
- \+/\- *lemma* submodule.map_coe
- \+/\- *lemma* submodule.map_comap_eq
- \+/\- *lemma* submodule.map_comap_eq_of_surjective
- \+/\- *lemma* submodule.map_comap_eq_self
- \+/\- *lemma* submodule.map_comap_le
- \+/\- *lemma* submodule.map_comp
- \+/\- *lemma* submodule.map_equiv_eq_comap_symm
- \+/\- *lemma* submodule.map_id
- \+/\- *lemma* submodule.map_inf_comap_of_surjective
- \+/\- *lemma* submodule.map_inf_eq_map_inf_comap
- \+/\- *lemma* submodule.map_infi_comap_of_surjective
- \+/\- *lemma* submodule.map_le_iff_le_comap
- \+/\- *theorem* submodule.map_liftq
- \+/\- *lemma* submodule.map_mono
- \+/\- *lemma* submodule.map_span
- \+/\- *lemma* submodule.map_sup
- \+/\- *lemma* submodule.map_sup_comap_of_surjective
- \+/\- *lemma* submodule.map_supr
- \+/\- *lemma* submodule.map_supr_comap_of_sujective
- \+/\- *theorem* submodule.map_top
- \+/\- *lemma* submodule.map_zero
- \+/\- *def* submodule.mapq
- \+/\- *theorem* submodule.mapq_apply
- \+/\- *def* submodule.mapq_linear
- \+/\- *theorem* submodule.mapq_mkq
- \+/\- *lemma* submodule.mem_comap
- \+/\- *lemma* submodule.mem_map
- \+/\- *lemma* submodule.mem_map_equiv
- \+/\- *theorem* submodule.mem_map_of_mem
- \+/\- *lemma* submodule.mem_prod
- \+/\- *lemma* submodule.mem_supr
- \+/\- *lemma* submodule.mem_supr_of_chain
- \+/\- *def* submodule.prod
- \+/\- *lemma* submodule.prod_bot
- \+/\- *lemma* submodule.prod_inf_prod
- \+/\- *lemma* submodule.prod_mono
- \+/\- *lemma* submodule.prod_sup_prod
- \+/\- *lemma* submodule.prod_top
- \+/\- *theorem* submodule.range_liftq
- \+/\- *lemma* submodule.span_image
- \+/\- *lemma* submodule.span_preimage_eq
- \+/\- *lemma* submodule.span_preimage_le
- \+/\- *lemma* submodule.span_prod_le
- \+/\- *lemma* submodule.supr_eq_span

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean
- \+ *def* bilin_form.to_lin_hom_aux₁
- \+ *def* bilin_form.to_lin_hom_aux₂
- \+/\- *lemma* bilin_form.to_matrix'_comp_left
- \+/\- *lemma* bilin_form.to_matrix'_comp_right

Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/clifford_algebra/conjugation.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/matrix/diagonal.lean


Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/pi.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/prod.lean


Modified src/linear_algebra/projection.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/std_basis.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/number_theory/class_number/finite.lean


Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/tensor_product.lean


Modified src/topology/algebra/module.lean


Modified src/topology/continuous_function/bounded.lean




## [2021-09-24 04:51:04](https://github.com/leanprover-community/mathlib/commit/a7a9c91)
feat(ring_theory/localization): Localizing at units is isomorphic to the ring ([#9324](https://github.com/leanprover-community/mathlib/pull/9324))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *def* is_localization.at_one
- \+ *def* is_localization.at_unit
- \+ *def* is_localization.at_units



## [2021-09-24 02:10:32](https://github.com/leanprover-community/mathlib/commit/4a8fb6a)
chore(linear_algebra): rename endomorphism multiplicative structures for consistency ([#9336](https://github.com/leanprover-community/mathlib/pull/9336))
This renames:
* `module.endomorphism_semiring` → `module.End.semiring`
* `module.endomorphism_ring` → `module.End.ring`
* `module.endomorphism_algebra` → `module.End.algebra`
* `linear_map.module.End.division_ring` → `module.End.division_ring`
This brings the name in line with the names for `add_monoid.End`.
Since `module.End` is an abbreviation, it does not matter that the instances now use this instead of `M →ₗ[R] M`.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/linear_map.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/simple_module.lean




## [2021-09-24 01:29:26](https://github.com/leanprover-community/mathlib/commit/dd519df)
chore(*): linting ([#9342](https://github.com/leanprover-community/mathlib/pull/9342))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/compact_open.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/stalks.lean




## [2021-09-24 00:26:14](https://github.com/leanprover-community/mathlib/commit/1a341fd)
feat(algebra/*): Tensor product is the fibered coproduct in CommRing ([#9338](https://github.com/leanprover-community/mathlib/pull/9338))
#### Estimated changes
Added src/algebra/category/CommRing/pushout.lean
- \+ *def* CommRing.pushout_cocone
- \+ *lemma* CommRing.pushout_cocone_X
- \+ *lemma* CommRing.pushout_cocone_inl
- \+ *lemma* CommRing.pushout_cocone_inr
- \+ *def* CommRing.pushout_cocone_is_colimit

Modified src/ring_theory/tensor_product.lean
- \+ *def* algebra.tensor_product.lmul'
- \+ *lemma* algebra.tensor_product.lmul'_apply_tmul
- \+ *lemma* algebra.tensor_product.lmul'_comp_include_left
- \+ *lemma* algebra.tensor_product.lmul'_comp_include_right
- \+ *lemma* algebra.tensor_product.lmul'_to_linear_map
- \+ *lemma* algebra.tensor_product.map_comp_include_left
- \+ *lemma* algebra.tensor_product.map_comp_include_right
- \+ *def* algebra.tensor_product.product_map
- \+ *lemma* algebra.tensor_product.product_map_apply_tmul
- \+ *lemma* algebra.tensor_product.product_map_left
- \+ *lemma* algebra.tensor_product.product_map_left_apply
- \+ *lemma* algebra.tensor_product.product_map_right
- \+ *lemma* algebra.tensor_product.product_map_right_apply



## [2021-09-24 00:26:13](https://github.com/leanprover-community/mathlib/commit/2d17f52)
feat(measure_theory/integral/*): integral over map (e : α ≃ᵐ β) μ  ([#9316](https://github.com/leanprover-community/mathlib/pull/9316))
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable_map_equiv

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.integral_map_equiv

Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* measure_theory.integrable_on_map_equiv

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.set_integral_map_equiv

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_measurable_map_equiv_iff
- \+ *lemma* measurable_equiv.restrict_map



## [2021-09-24 00:26:12](https://github.com/leanprover-community/mathlib/commit/18f0093)
feat(measure_theory/measure/measure_space): add measure_Union_of_null_inter ([#9307](https://github.com/leanprover-community/mathlib/pull/9307))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure_Union_of_null_inter



## [2021-09-24 00:26:11](https://github.com/leanprover-community/mathlib/commit/7e3256b)
feat(ring_theory/derivation): helper lemma for custom `derivation_ext` lemmas ([#9255](https://github.com/leanprover-community/mathlib/pull/9255))
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+ *lemma* derivation.eq_on_adjoin
- \+ *lemma* derivation.ext_of_adjoin_eq_top



## [2021-09-24 00:26:10](https://github.com/leanprover-community/mathlib/commit/9b1f0bb)
feat(topology/compact_open): convergence in the compact-open topology can be checked on compact sets ([#9240](https://github.com/leanprover-community/mathlib/pull/9240))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.compact_open_le_induced
- \+ *lemma* continuous_map.continuous_ev₁
- \+ *lemma* continuous_map.continuous_restrict
- \+ *lemma* continuous_map.exists_tendsto_compact_open_iff_forall
- \+ *lemma* continuous_map.tendsto_compact_open_restrict



## [2021-09-23 22:18:50](https://github.com/leanprover-community/mathlib/commit/d2f7b24)
feat(algebra/pointwise): more to_additive attributes for new lemmas ([#9348](https://github.com/leanprover-community/mathlib/pull/9348))
Some of these lemmas introduced in [#9226](https://github.com/leanprover-community/mathlib/pull/9226) I believe.
Spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819).
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* set_smul_subset_set_smul_iff
- \+/\- *lemma* smul_mem_smul_set_iff



## [2021-09-23 22:18:49](https://github.com/leanprover-community/mathlib/commit/88c79e5)
feat(data/fintype/basic): embeddings of fintypes based on cardinal inequalities ([#9346](https://github.com/leanprover-community/mathlib/pull/9346))
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/mapping.20a.20fintype.20into.20a.20finset/near/254493754, based on suggestions by @kmill  and @eric-wieser and @riccardobrasca.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* function.embedding.equiv_of_fintype_self_embedding_to_embedding
- \+ *lemma* function.embedding.exists_of_card_le_finset
- \+/\- *lemma* function.embedding.is_empty_of_card_lt
- \+ *lemma* function.embedding.nonempty_of_card_le
- \+ *def* function.embedding.trunc_of_card_le



## [2021-09-23 22:18:48](https://github.com/leanprover-community/mathlib/commit/c950c45)
feat(analysis/calculus/[f]deriv): derivative of pointwise composition/application of continuous linear maps ([#9174](https://github.com/leanprover-community/mathlib/pull/9174))
This introduces useful analogs to the product rule when working with derivatives in spaces of continuous linear maps.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_clm_apply
- \+ *lemma* deriv_clm_comp
- \+ *lemma* deriv_within_clm_apply
- \+ *lemma* deriv_within_clm_comp
- \+ *lemma* has_deriv_at.clm_apply
- \+ *lemma* has_deriv_at.clm_comp
- \+ *lemma* has_deriv_within_at.clm_apply
- \+ *lemma* has_deriv_within_at.clm_comp
- \+ *lemma* has_strict_deriv_at.clm_apply
- \+ *lemma* has_strict_deriv_at.clm_comp

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable.clm_apply
- \+ *lemma* differentiable.clm_comp
- \+ *lemma* differentiable_at.clm_apply
- \+ *lemma* differentiable_at.clm_comp
- \+ *lemma* differentiable_on.clm_apply
- \+ *lemma* differentiable_on.clm_comp
- \+ *lemma* differentiable_within_at.clm_apply
- \+ *lemma* differentiable_within_at.clm_comp
- \+ *lemma* fderiv_clm_apply
- \+ *lemma* fderiv_clm_comp
- \+ *lemma* fderiv_within_clm_apply
- \+ *lemma* fderiv_within_clm_comp
- \+ *lemma* has_fderiv_at.clm_apply
- \+ *lemma* has_fderiv_at.clm_comp
- \+ *lemma* has_fderiv_within_at.clm_apply
- \+ *lemma* has_fderiv_within_at.clm_comp
- \+ *lemma* has_strict_fderiv_at.clm_apply
- \+ *lemma* has_strict_fderiv_at.clm_comp

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.comp_apply



## [2021-09-23 21:18:45](https://github.com/leanprover-community/mathlib/commit/54eb603)
chore(analysis/normed_space/conformal_linear_map): delay dependence on inner products ([#9293](https://github.com/leanprover-community/mathlib/pull/9293))
#### Estimated changes
Added src/analysis/calculus/conformal/inner_product.lean
- \+ *lemma* conformal_at_iff'
- \+ *lemma* conformal_at_iff
- \+ *def* conformal_factor_at
- \+ *lemma* conformal_factor_at_inner_eq_mul_inner'
- \+ *lemma* conformal_factor_at_inner_eq_mul_inner
- \+ *lemma* conformal_factor_at_pos

Renamed src/analysis/calculus/conformal.lean to src/analysis/calculus/conformal/normed_space.lean
- \- *def* conformal_at.conformal_factor_at
- \- *lemma* conformal_at.conformal_factor_at_inner_eq_mul_inner'
- \- *lemma* conformal_at.conformal_factor_at_inner_eq_mul_inner
- \- *lemma* conformal_at.conformal_factor_at_pos
- \- *lemma* conformal_at_iff'
- \- *lemma* conformal_at_iff

Modified src/analysis/complex/real_deriv.lean


Modified src/analysis/normed_space/conformal_linear_map.lean
- \+/\- *lemma* is_conformal_map.injective
- \+/\- *lemma* is_conformal_map.ne_zero
- \+/\- *def* is_conformal_map
- \- *lemma* is_conformal_map_iff
- \+/\- *lemma* linear_isometry.is_conformal_map

Added src/analysis/normed_space/conformal_linear_map/inner_product.lean
- \+ *lemma* is_conformal_map_iff

Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/conformal_groupoid.lean




## [2021-09-23 19:20:02](https://github.com/leanprover-community/mathlib/commit/14bcb2e)
feat(measure_theory/measure/measure_space_def): some simple lemmas about measures and intersection ([#9306](https://github.com/leanprover-community/mathlib/pull/9306))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Modified src/measure_theory/measure/measure_space_def.lean
- \- *lemma* measure_theory.measure_inter_lt_top
- \+ *lemma* measure_theory.measure_inter_lt_top_of_left_ne_top
- \+ *lemma* measure_theory.measure_inter_lt_top_of_right_ne_top
- \- *lemma* measure_theory.measure_inter_ne_top
- \+ *lemma* measure_theory.measure_inter_null_of_null_left
- \+ *lemma* measure_theory.measure_inter_null_of_null_right



## [2021-09-23 19:20:01](https://github.com/leanprover-community/mathlib/commit/ea59c90)
feat(ring_theory/algebraic): is_algebraic_iff_not_injective ([#9254](https://github.com/leanprover-community/mathlib/pull/9254))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_iff_not_injective



## [2021-09-23 16:42:28](https://github.com/leanprover-community/mathlib/commit/9e367ff)
feat(linear_algebra/invariant_basis_number): strong_rank_condition_iff_succ ([#9128](https://github.com/leanprover-community/mathlib/pull/9128))
We add `strong_rank_condition_iff_succ`: a ring satisfies the strong rank condition if and only if, for all `n : ℕ`, there are no
injective linear maps `(fin (n + 1) → R) →ₗ[R] (fin n → R)`. This will be used to prove that any commutative ring satisfies the strong rank condition.
The proof is simple and it uses the natural inclusion `R^n → R^m`, for `n ≤ m` (adding zeros at the end). We provide this in general as `extend_by_zero.linear_map : (ι → R) →ₗ[R] (η → R)` where `ι` and `η` are types endowed with a function `ι → η`.
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/module/pi.lean
- \+ *lemma* function.extend_smul

Modified src/data/pi.lean
- \+ *lemma* function.extend_div
- \+ *lemma* function.extend_inv
- \+ *lemma* function.extend_mul
- \+ *lemma* function.extend_one

Modified src/linear_algebra/invariant_basis_number.lean
- \+ *lemma* strong_rank_condition_iff_succ

Modified src/linear_algebra/pi.lean


Modified src/logic/function/basic.lean
- \+ *lemma* function.extend_apply'
- \+ *lemma* function.extend_injective



## [2021-09-23 15:31:34](https://github.com/leanprover-community/mathlib/commit/b365367)
feat(README.md): add Oliver Nash ([#9347](https://github.com/leanprover-community/mathlib/pull/9347))
#### Estimated changes
Modified README.md




## [2021-09-23 15:31:33](https://github.com/leanprover-community/mathlib/commit/81f6e88)
chore(analysis/calculus): add 2 simple lemmas ([#9334](https://github.com/leanprover-community/mathlib/pull/9334))
Add `differentiable_on.has_fderiv_at` and `differentiable_on.has_deriv_at`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable_on.has_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_on.has_fderiv_at



## [2021-09-23 15:31:31](https://github.com/leanprover-community/mathlib/commit/0243da3)
feat(ereal): added useful lemmas ([#9313](https://github.com/leanprover-community/mathlib/pull/9313))
Some small addition to the api for ereals.
#### Estimated changes
Modified src/data/real/ereal.lean
- \+ *lemma* ereal.coe_to_real_le
- \+ *lemma* ereal.eq_bot_iff_forall_lt
- \+ *lemma* ereal.eq_top_iff_forall_lt
- \+ *lemma* ereal.le_coe_to_real



## [2021-09-23 14:08:43](https://github.com/leanprover-community/mathlib/commit/cc0d839)
feat(measure_theory/measure/haar): cleanup, link with the is_haar_measure typeclass ([#9244](https://github.com/leanprover-community/mathlib/pull/9244))
We show that the Haar measure constructed in `measure_theory/measure/haar` satisfies the `is_haar_measure` typeclass, and use the existence to show a few further properties of all Haar measures. Also weaken a little bit some assumptions in this file.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.pow_strict_mono

Modified src/measure_theory/measure/haar.lean
- \- *lemma* measure_theory.measure.add_haar_measure_apply
- \+ *def* measure_theory.measure.haar
- \- *lemma* measure_theory.measure.haar_measure_pos_of_is_open
- \+/\- *lemma* measure_theory.measure.haar_measure_self
- \+ *lemma* measure_theory.measure.haar_preimage_inv
- \+ *theorem* measure_theory.measure.is_haar_measure_eq_smul_is_haar_measure
- \+ *lemma* measure_theory.measure.map_haar_inv

Modified src/topology/algebra/group.lean
- \+ *lemma* topological_space.positive_compacts.locally_compact_space_of_group

Modified src/topology/compacts.lean




## [2021-09-23 08:15:13](https://github.com/leanprover-community/mathlib/commit/602ad58)
feat(measure_theory/integral): add a few lemmas ([#9285](https://github.com/leanprover-community/mathlib/pull/9285))
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.integral_coe_le_of_lintegral_coe_le
- \+ *lemma* measure_theory.lintegral_coe_le_coe_iff_integral_le
- \+ *lemma* measure_theory.simple_func.integral_const
- \+ *lemma* measure_theory.simple_func.integral_piecewise_zero

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.range_const_subset



## [2021-09-23 08:15:12](https://github.com/leanprover-community/mathlib/commit/145c5ca)
refactor(topology/category/Top/open_nhds): remove open_nhds.is_filtered ([#9211](https://github.com/leanprover-community/mathlib/pull/9211))
Remove instance that can be inferred automatically.
#### Estimated changes
Modified src/topology/category/Top/open_nhds.lean




## [2021-09-23 06:57:23](https://github.com/leanprover-community/mathlib/commit/8a0d60e)
chore(topology): rename compact_ball to is_compact_closed_ball ([#9337](https://github.com/leanprover-community/mathlib/pull/9337))
The old name didn't follow the naming convention at all, which made it hard to discover.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/normed_space/euclidean_dist.lean
- \- *lemma* euclidean.compact_ball
- \+ *lemma* euclidean.is_compact_closed_ball

Modified src/geometry/manifold/bump_function.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean




## [2021-09-23 06:06:00](https://github.com/leanprover-community/mathlib/commit/7615f83)
chore(archive/100-theorems-list/42): typo ([#9341](https://github.com/leanprover-community/mathlib/pull/9341))
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean




## [2021-09-23 05:13:45](https://github.com/leanprover-community/mathlib/commit/d238087)
chore(data/real/pi/*): correct authorship data ([#9314](https://github.com/leanprover-community/mathlib/pull/9314))
[#9295](https://github.com/leanprover-community/mathlib/pull/9295) split `data.real.pi` into three files with the naive transferral of authorship and copyright data, this updates it to the actual authorship.
#### Estimated changes
Modified src/data/real/pi/bounds.lean


Modified src/data/real/pi/leibniz.lean


Modified src/data/real/pi/wallis.lean




## [2021-09-23 04:17:39](https://github.com/leanprover-community/mathlib/commit/a15ae9c)
chore(measure_theory/measurable_space): add simps config for `measurable_equiv` ([#9315](https://github.com/leanprover-community/mathlib/pull/9315))
Also add `@[ext]` lemma and some standard `equiv` lemmas.
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/measurable_space.lean
- \+ *theorem* measurable_equiv.apply_symm_apply
- \- *lemma* measurable_equiv.coe_eq
- \- *lemma* measurable_equiv.coe_symm_mk
- \+ *lemma* measurable_equiv.coe_to_equiv
- \+ *lemma* measurable_equiv.coe_to_equiv_symm
- \+ *lemma* measurable_equiv.ext
- \+ *theorem* measurable_equiv.self_trans_symm
- \+ *def* measurable_equiv.simps.apply
- \+ *def* measurable_equiv.simps.symm_apply
- \+/\- *def* measurable_equiv.symm
- \+ *theorem* measurable_equiv.symm_apply_apply
- \+ *lemma* measurable_equiv.symm_mk
- \+ *lemma* measurable_equiv.symm_refl
- \+ *theorem* measurable_equiv.symm_trans_self
- \+ *lemma* measurable_equiv.to_equiv_injective
- \+/\- *def* measurable_equiv.trans

Modified src/measure_theory/measure/measure_space.lean




## [2021-09-23 02:22:43](https://github.com/leanprover-community/mathlib/commit/b563e5a)
chore(scripts): update nolints.txt ([#9339](https://github.com/leanprover-community/mathlib/pull/9339))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-09-23 00:38:17](https://github.com/leanprover-community/mathlib/commit/671b179)
refactor(group_theory/subgroup,linear_algebra/basic): put pointwise actions in their own files to match submonoid ([#9312](https://github.com/leanprover-community/mathlib/pull/9312))
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/direct_sum/basic.lean


Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/group_ring_action.lean


Added src/algebra/module/submodule_pointwise.lean
- \+ *lemma* submodule.add_eq_sup
- \+ *lemma* submodule.coe_pointwise_smul
- \+ *lemma* submodule.pointwise_smul_to_add_subgroup
- \+ *lemma* submodule.pointwise_smul_to_add_submonoid
- \+ *lemma* submodule.smul_le_self_of_tower
- \+ *lemma* submodule.smul_mem_pointwise_smul
- \+ *lemma* submodule.zero_eq_bot

Modified src/deprecated/subgroup.lean


Modified src/group_theory/archimedean.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/finiteness.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/general_commutator.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/group_theory/semidirect_product.lean


Renamed src/group_theory/subgroup.lean to src/group_theory/subgroup/basic.lean
- \- *lemma* add_subgroup.coe_pointwise_smul
- \- *lemma* add_subgroup.pointwise_smul_to_add_submonoid
- \- *lemma* add_subgroup.smul_mem_pointwise_smul
- \- *lemma* subgroup.coe_pointwise_smul
- \- *lemma* subgroup.pointwise_smul_to_submonoid
- \- *lemma* subgroup.smul_mem_pointwise_smul

Added src/group_theory/subgroup/pointwise.lean
- \+ *lemma* add_subgroup.coe_pointwise_smul
- \+ *lemma* add_subgroup.pointwise_smul_to_add_submonoid
- \+ *lemma* add_subgroup.smul_mem_pointwise_smul
- \+ *lemma* subgroup.coe_pointwise_smul
- \+ *lemma* subgroup.pointwise_smul_to_submonoid
- \+ *lemma* subgroup.smul_mem_pointwise_smul

Modified src/group_theory/submonoid/pointwise.lean


Modified src/linear_algebra/basic.lean
- \- *lemma* submodule.add_eq_sup
- \- *lemma* submodule.coe_pointwise_smul
- \- *lemma* submodule.lt_add_iff_not_mem
- \+ *lemma* submodule.lt_sup_iff_not_mem
- \+/\- *lemma* submodule.map_add_le
- \- *lemma* submodule.pointwise_smul_to_add_subgroup
- \- *lemma* submodule.pointwise_smul_to_add_submonoid
- \- *lemma* submodule.smul_le_self_of_tower
- \- *lemma* submodule.smul_mem_pointwise_smul
- \- *lemma* submodule.zero_eq_bot

Modified src/ring_theory/subring.lean


Modified src/topology/algebra/nonarchimedean/basic.lean




## [2021-09-23 00:38:16](https://github.com/leanprover-community/mathlib/commit/20981be)
feat(linear_algebra/charpoly): add linear_map.charpoly ([#9279](https://github.com/leanprover-community/mathlib/pull/9279))
We add `linear_map.charpoly`, the characteristic polynomial of an endomorphism of a finite free module, and a basic API.
#### Estimated changes
Added src/linear_algebra/charpoly.lean
- \+ *lemma* linear_map.aeval_self_charpoly
- \+ *def* linear_map.charpoly
- \+ *lemma* linear_map.charpoly_coeff_zero_of_injective
- \+ *lemma* linear_map.charpoly_def
- \+ *lemma* linear_map.charpoly_monic
- \+ *lemma* linear_map.charpoly_to_matrix
- \+ *lemma* linear_map.is_integral
- \+ *lemma* linear_map.minpoly_dvd_charpoly

Modified src/linear_algebra/charpoly/basic.lean
- \+ *lemma* charmatrix_reindex
- \+ *lemma* matrix.charpoly_reindex

Modified src/linear_algebra/dimension.lean
- \+ *def* basis.index_equiv

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/free_module_pid.lean




## [2021-09-22 20:20:50](https://github.com/leanprover-community/mathlib/commit/5b3b71a)
chore(data/equiv): rename `bool_to_equiv_prod` to `bool_arrow_equiv_prod` ([#9333](https://github.com/leanprover-community/mathlib/pull/9333))
Other changes:
* use an explicit definition;
* use `@[simps]`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.bool_arrow_equiv_prod
- \- *def* equiv.bool_to_equiv_prod
- \- *lemma* equiv.bool_to_equiv_prod_apply
- \- *lemma* equiv.bool_to_equiv_prod_symm_apply_ff
- \- *lemma* equiv.bool_to_equiv_prod_symm_apply_tt



## [2021-09-22 16:35:13](https://github.com/leanprover-community/mathlib/commit/6eb8d41)
chore(ring_theory/dedekind_domain): speed up `dedekind_domain.lean` ([#9232](https://github.com/leanprover-community/mathlib/pull/9232))
@eric-wieser [noticed that `dedekind_domain.lean`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeouts.20in.20ring_theory.2Fdedekind_domain.2Elean.3A664.3A9) was compiling slowly and on the verge of a timeout. @kbuzzard, @sgouezel and I reworked some definitions to make everything elaborate much faster: `is_dedekind_domain_inv_iff`, `mul_inv_cancel_of_le_one` and `ideal.unique_factorization_monoid` went from over 10 seconds on my machine to less than 3 seconds. No other declaration in that file now takes over 2 seconds on my machine.
Apart from the three declarations getting new proofs, I also made the following changes:
 * The operations on `localization` (`has_add`, `has_mul`, `has_one`, `has_zero`, `has_neg`, `npow` and `localization.inv`) are now `@[irreducible]`
 * `fraction_ring.field` copies its field from `localization.comm_ring` for faster unification (less relevant after the previous change)
 * Added `fractional_ideal.map_mem_map` and `fractional_ideal.map_injective` to simplify the proof of `is_dedekind_domain_inv_iff`.
 * Split the proof of `matrix.exists_mul_vec_eq_zero_iff` into two parts to speed it up
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *def* localization.lift_on
- \+ *lemma* localization.lift_on_mk'
- \+ *lemma* localization.lift_on_mk
- \+ *def* localization.lift_on₂
- \+ *lemma* localization.lift_on₂_mk'
- \+ *lemma* localization.lift_on₂_mk
- \+ *theorem* localization.mk_eq_mk_iff
- \+ *lemma* localization.mk_mul
- \+ *lemma* localization.mk_one
- \+ *lemma* localization.mk_self
- \+ *def* localization.rec
- \+ *lemma* localization.rec_mk

Modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+ *lemma* matrix.exists_mul_vec_eq_zero_iff'

Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.map_injective
- \+ *lemma* fractional_ideal.map_mem_map

Modified src/ring_theory/localization.lean
- \+ *lemma* localization.add_mk
- \+/\- *lemma* localization.mk_eq_mk'
- \+ *lemma* localization.mk_zero
- \+ *lemma* localization.neg_mk
- \+ *lemma* localization.to_localization_map_eq_monoid_of

Modified src/set_theory/surreal/dyadic.lean




## [2021-09-22 15:37:39](https://github.com/leanprover-community/mathlib/commit/dc5a3db)
feat(algebra/category): Forgetful functors preserve filtered colimits ([#9101](https://github.com/leanprover-community/mathlib/pull/9101))
Shows that forgetful functors of various algebraic categories preserve filtered colimits.
#### Estimated changes
Added src/algebra/category/CommRing/filtered_colimits.lean
- \+ *def* CommRing.filtered_colimits.colimit
- \+ *def* CommRing.filtered_colimits.colimit_cocone
- \+ *def* CommRing.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* CommSemiRing.filtered_colimits.colimit
- \+ *def* CommSemiRing.filtered_colimits.colimit_cocone
- \+ *def* CommSemiRing.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* Ring.filtered_colimits.colimit
- \+ *def* Ring.filtered_colimits.colimit_cocone
- \+ *def* Ring.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* SemiRing.filtered_colimits.colimit
- \+ *def* SemiRing.filtered_colimits.colimit_cocone
- \+ *def* SemiRing.filtered_colimits.colimit_cocone_is_colimit

Added src/algebra/category/Group/filtered_colimits.lean
- \+ *def* CommGroup.filtered_colimits.colimit
- \+ *def* CommGroup.filtered_colimits.colimit_cocone
- \+ *def* CommGroup.filtered_colimits.colimit_cocone_is_colimit
- \+ *lemma* Group.filtered_colimits.G.mk_eq
- \+ *def* Group.filtered_colimits.colimit
- \+ *def* Group.filtered_colimits.colimit_cocone
- \+ *def* Group.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* Group.filtered_colimits.colimit_inv_aux
- \+ *lemma* Group.filtered_colimits.colimit_inv_aux_eq_of_rel
- \+ *lemma* Group.filtered_colimits.colimit_inv_mk_eq

Added src/algebra/category/Module/filtered_colimits.lean
- \+ *lemma* Module.filtered_colimits.M.mk_eq
- \+ *def* Module.filtered_colimits.cocone_morphism
- \+ *def* Module.filtered_colimits.colimit
- \+ *def* Module.filtered_colimits.colimit_cocone
- \+ *def* Module.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* Module.filtered_colimits.colimit_desc
- \+ *def* Module.filtered_colimits.colimit_smul_aux
- \+ *lemma* Module.filtered_colimits.colimit_smul_aux_eq_of_rel
- \+ *lemma* Module.filtered_colimits.colimit_smul_mk_eq

Added src/algebra/category/Mon/filtered_colimits.lean
- \+ *def* CommMon.filtered_colimits.colimit
- \+ *def* CommMon.filtered_colimits.colimit_cocone
- \+ *def* CommMon.filtered_colimits.colimit_cocone_is_colimit
- \+ *lemma* Mon.filtered_colimits.M.mk_eq
- \+ *def* Mon.filtered_colimits.cocone_morphism
- \+ *lemma* Mon.filtered_colimits.cocone_naturality
- \+ *def* Mon.filtered_colimits.colimit
- \+ *def* Mon.filtered_colimits.colimit_cocone
- \+ *def* Mon.filtered_colimits.colimit_cocone_is_colimit
- \+ *def* Mon.filtered_colimits.colimit_desc
- \+ *def* Mon.filtered_colimits.colimit_mul_aux
- \+ *lemma* Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left
- \+ *lemma* Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right
- \+ *lemma* Mon.filtered_colimits.colimit_mul_mk_eq
- \+ *lemma* Mon.filtered_colimits.colimit_one_eq

Modified src/category_theory/filtered.lean


Added src/category_theory/limits/preserves/filtered.lean




## [2021-09-22 14:37:26](https://github.com/leanprover-community/mathlib/commit/41414a3)
chore(analysis/special_functions): typo in module doc ([#9330](https://github.com/leanprover-community/mathlib/pull/9330))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean




## [2021-09-22 14:37:25](https://github.com/leanprover-community/mathlib/commit/2b84c4c)
feat(linear_algebra/matrix/basis): add matrix basis change formula ([#9280](https://github.com/leanprover-community/mathlib/pull/9280))
We add `basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix`, the formula for the change of basis.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix



## [2021-09-22 14:37:23](https://github.com/leanprover-community/mathlib/commit/68dbf27)
feat(number_theory): the class group of an integral closure is finite ([#9059](https://github.com/leanprover-community/mathlib/pull/9059))
This is essentially the proof that the ring of integers of a global field has a finite class group, apart from filling in each hypothesis.
#### Estimated changes
Added src/number_theory/class_number/finite.lean
- \+ *theorem* class_group.exists_mem_finset_approx'
- \+ *theorem* class_group.exists_mem_finset_approx
- \+ *lemma* class_group.exists_min
- \+ *theorem* class_group.exists_mk0_eq_mk0
- \+ *lemma* class_group.finset_approx.zero_not_mem
- \+ *lemma* class_group.mem_finset_approx
- \+ *lemma* class_group.mk_M_mem_surjective
- \+ *lemma* class_group.ne_bot_of_prod_finset_approx_mem
- \+ *lemma* class_group.norm_bound_pos
- \+ *lemma* class_group.norm_le
- \+ *lemma* class_group.norm_lt
- \+ *lemma* class_group.prod_finset_approx_ne_zero

Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_integral_closure.exists_smul_eq_mul



## [2021-09-22 12:11:46](https://github.com/leanprover-community/mathlib/commit/a5d2dbc)
chore(measure_theory/integral/set_integral): generalize, golf ([#9328](https://github.com/leanprover-community/mathlib/pull/9328))
* rename `integrable_on_finite_union` to `integrable_on_finite_Union`;
* rename `integrable_on_finset_union` to `integrable_on_finset_Union`;
* add `integrable_on_fintype_Union`;
* generalize `tendsto_measure_Union` and `tendsto_measure_Inter from
  `s : ℕ → set α` to
  `[semilattice_sup ι] [encodable ι] {s : ι → set α}`;
* add `integral_diff`;
* generalize `integral_finset_bUnion`, `integral_fintype_Union` and
  `has_sum_integral_Union` to require appropriate `integrable_on`
  instead of `integrable`;
* golf some proofs.
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* measure_theory.integrable_on_finite_Union
- \- *lemma* measure_theory.integrable_on_finite_union
- \+ *lemma* measure_theory.integrable_on_finset_Union
- \- *lemma* measure_theory.integrable_on_finset_union
- \+ *lemma* measure_theory.integrable_on_fintype_Union

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_diff
- \+/\- *lemma* measure_theory.integral_finset_bUnion
- \+/\- *lemma* measure_theory.tendsto_set_integral_of_monotone

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.tendsto_measure_Inter
- \+/\- *lemma* measure_theory.tendsto_measure_Union

Modified src/measure_theory/measure/with_density_vector_measure.lean




## [2021-09-22 12:11:44](https://github.com/leanprover-community/mathlib/commit/a994071)
chore(data/complex/module): rename `complex.smul_coe` to `real_smul` ([#9326](https://github.com/leanprover-community/mathlib/pull/9326))
* the name was misleading b/c there is no `coe` in the LHS;
* add `complex.coe_smul`: given `x : ℝ` and `y : E`, we have
  `(x : ℂ) • y = x • y`;
* add `normed_space.complex_to_real`.
#### Estimated changes
Modified src/analysis/complex/basic.lean


Modified src/analysis/complex/isometry.lean


Modified src/data/complex/module.lean
- \+/\- *lemma* complex.coe_algebra_map
- \+ *lemma* complex.coe_smul
- \+ *lemma* complex.real_smul
- \- *lemma* complex.smul_coe

Modified src/linear_algebra/clifford_algebra/equivs.lean


Modified src/measure_theory/decomposition/jordan.lean




## [2021-09-22 12:11:43](https://github.com/leanprover-community/mathlib/commit/7e350c2)
feat(category_theory/*): Fully faithful functors induces equivalence ([#9322](https://github.com/leanprover-community/mathlib/pull/9322))
Needed for AffineSchemes ≌ CommRingᵒᵖ.
#### Estimated changes
Modified src/category_theory/equivalence.lean


Modified src/category_theory/essential_image.lean
- \+/\- *def* category_theory.functor.to_ess_image_comp_essential_image_inclusion

Modified src/category_theory/fully_faithful.lean
- \+ *def* category_theory.full.of_comp_faithful



## [2021-09-22 12:11:42](https://github.com/leanprover-community/mathlib/commit/15730e8)
chore(analysis/convex): trivial generalizations of ℝ ([#9298](https://github.com/leanprover-community/mathlib/pull/9298))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/convex/basic.lean
- \- *lemma* convex_halfspace_im_ge
- \- *lemma* convex_halfspace_im_gt
- \- *lemma* convex_halfspace_im_le
- \- *lemma* convex_halfspace_im_lt
- \- *lemma* convex_halfspace_re_ge
- \- *lemma* convex_halfspace_re_gt
- \- *lemma* convex_halfspace_re_le
- \- *lemma* convex_halfspace_re_lt
- \+/\- *lemma* convex_std_simplex
- \+/\- *lemma* ite_eq_mem_std_simplex
- \+/\- *def* std_simplex

Modified src/analysis/convex/caratheodory.lean


Modified src/analysis/convex/combination.lean
- \+/\- *lemma* convex.center_mass_mem
- \+/\- *lemma* convex.sum_mem
- \+ *def* finset.center_mass
- \+/\- *lemma* finset.center_mass_mem_convex_hull
- \+/\- *lemma* mem_Icc_of_mem_std_simplex

Added src/analysis/convex/complex.lean
- \+ *lemma* convex_halfspace_im_ge
- \+ *lemma* convex_halfspace_im_gt
- \+ *lemma* convex_halfspace_im_le
- \+ *lemma* convex_halfspace_im_lt
- \+ *lemma* convex_halfspace_re_ge
- \+ *lemma* convex_halfspace_re_gt
- \+ *lemma* convex_halfspace_re_le
- \+ *lemma* convex_halfspace_re_lt

Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/function.lean


Modified src/analysis/convex/topology.lean
- \+/\- *lemma* bounded_std_simplex
- \+/\- *lemma* compact_std_simplex
- \+/\- *lemma* is_closed_std_simplex



## [2021-09-22 12:11:41](https://github.com/leanprover-community/mathlib/commit/eb3d600)
feat(data/{list,multiset}): add `can_lift` instances ([#9262](https://github.com/leanprover-community/mathlib/pull/9262))
* add `can_lift` instances for `set`, `list`, `multiset`, and `finset`;
* use them in `submonoid.{list,multiset}_prod_mem`;
* more `to_additive` attrs in `group_theory.submonoid.membership`.
#### Estimated changes
Modified src/data/finset/basic.lean


Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/set/basic.lean


Modified src/group_theory/submonoid/membership.lean
- \- *lemma* add_submonoid.nsmul_mem
- \+/\- *theorem* submonoid.coe_finset_prod
- \+/\- *theorem* submonoid.coe_list_prod
- \+/\- *theorem* submonoid.coe_multiset_prod
- \+/\- *theorem* submonoid.coe_pow
- \+/\- *lemma* submonoid.list_prod_mem
- \+/\- *lemma* submonoid.multiset_prod_mem
- \+/\- *lemma* submonoid.pow_mem



## [2021-09-22 10:01:07](https://github.com/leanprover-community/mathlib/commit/c9638b9)
chore(measure_theory): add 2 lemmas ([#9329](https://github.com/leanprover-community/mathlib/pull/9329))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.bounded_by_measure

Modified src/measure_theory/measure/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.bounded_by_eq_self



## [2021-09-22 10:01:05](https://github.com/leanprover-community/mathlib/commit/6f2cbde)
chore(order/lattice): tidy up pi instances ([#9305](https://github.com/leanprover-community/mathlib/pull/9305))
These were previously defined in the wrong file, and the lemmas were missing the `pi` prefix that is present on `pi.add_apply` etc.
This also removes the instance names as they are autogenerated correctly.
Finally, this adds new `top_def`, `bot_def`, `sup_def`, and `inf_def` lemmas, which are useful for when wanting to rewrite under the lambda. We already have `zero_def`, `add_def`, etc.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/subgraph.lean


Modified src/order/bounded_lattice.lean
- \- *lemma* bot_apply
- \- *lemma* inf_apply
- \+ *lemma* pi.bot_apply
- \+ *lemma* pi.bot_def
- \+ *lemma* pi.top_apply
- \+ *lemma* pi.top_def
- \- *lemma* sup_apply
- \- *lemma* top_apply

Modified src/order/complete_boolean_algebra.lean


Modified src/order/lattice.lean
- \+ *lemma* pi.inf_apply
- \+ *lemma* pi.inf_def
- \+ *lemma* pi.sup_apply
- \+ *lemma* pi.sup_def



## [2021-09-22 10:01:04](https://github.com/leanprover-community/mathlib/commit/f95f216)
feat(linear_algebra/std_basis): add matrix.std_basis_eq_std_basis_matrix ([#9216](https://github.com/leanprover-community/mathlib/pull/9216))
As suggested in [#9072](https://github.com/leanprover-community/mathlib/pull/9072) by @eric-wieser, we modify `matrix.std_basis` to use the more familiar `n × m` as the index of the basis and we prove that the `(i,j)`-th element of this basis is `matrix.std_basis_matrix i j 1`.
#### Estimated changes
Modified src/linear_algebra/std_basis.lean
- \+ *lemma* matrix.std_basis_eq_std_basis_matrix



## [2021-09-22 07:37:28](https://github.com/leanprover-community/mathlib/commit/5b55a86)
chore(analysis/calculate/fderiv): move results about analytic functions to a new file ([#9296](https://github.com/leanprover-community/mathlib/pull/9296))
These are not necessary for many of the downstream files, so we can speed up compilation a bit by parallelising these.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean
- \- *lemma* analytic_at.differentiable_at
- \- *lemma* analytic_at.differentiable_within_at
- \- *lemma* has_fpower_series_at.differentiable_at
- \- *lemma* has_fpower_series_at.fderiv
- \- *lemma* has_fpower_series_at.has_fderiv_at
- \- *lemma* has_fpower_series_at.has_strict_fderiv_at
- \- *lemma* has_fpower_series_on_ball.differentiable_on

Added src/analysis/calculus/fderiv_analytic.lean
- \+ *lemma* analytic_at.differentiable_at
- \+ *lemma* analytic_at.differentiable_within_at
- \+ *lemma* has_fpower_series_at.differentiable_at
- \+ *lemma* has_fpower_series_at.fderiv
- \+ *lemma* has_fpower_series_at.has_fderiv_at
- \+ *lemma* has_fpower_series_at.has_strict_fderiv_at
- \+ *lemma* has_fpower_series_on_ball.differentiable_on

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/exponential.lean




## [2021-09-22 07:37:27](https://github.com/leanprover-community/mathlib/commit/6d86622)
chore(*): removing unneeded imports ([#9278](https://github.com/leanprover-community/mathlib/pull/9278))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed_space/basic.lean
- \- *def* locally_constant.to_continuous_map_alg_hom
- \- *def* locally_constant.to_continuous_map_linear_map
- \- *def* locally_constant.to_continuous_map_monoid_hom

Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean


Modified src/category_theory/preadditive/projective.lean


Modified src/category_theory/sites/types.lean


Modified src/category_theory/subobject/factor_thru.lean


Modified src/category_theory/subobject/mono_over.lean


Modified src/category_theory/triangulated/pretriangulated.lean


Modified src/linear_algebra/clifford_algebra/equivs.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/content.lean


Added src/topology/continuous_function/locally_constant.lean
- \+ *def* locally_constant.to_continuous_map_alg_hom
- \+ *def* locally_constant.to_continuous_map_linear_map
- \+ *def* locally_constant.to_continuous_map_monoid_hom



## [2021-09-22 07:37:21](https://github.com/leanprover-community/mathlib/commit/b77aa3a)
feat(linear_algebra/affine_space/affine_subspace): prove that a set whose affine span is top cannot be empty. ([#9113](https://github.com/leanprover-community/mathlib/pull/9113))
The lemma `finset.card_sdiff_add_card` is unrelated but I've been meaning to add it
and now seemed like a good time since I'm touching `data/finset/basic.lean` anyway.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.card_sdiff_add_card
- \+ *lemma* finset.nonempty_coe_sort

Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty_coe_sort

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.bot_ne_top
- \+ *lemma* affine_subspace.ext_iff
- \+ *lemma* affine_subspace.nonempty_of_affine_span_eq_top



## [2021-09-22 06:45:10](https://github.com/leanprover-community/mathlib/commit/f59dbf2)
chore(data/complex/exponential): add `abs_exp`, golf ([#9327](https://github.com/leanprover-community/mathlib/pull/9327))
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* complex.abs_exp



## [2021-09-22 02:48:40](https://github.com/leanprover-community/mathlib/commit/7112730)
feat(set_theory/cardinal_ordinal): mul_le_max and others ([#9269](https://github.com/leanprover-community/mathlib/pull/9269))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.add_le_max
- \+ *theorem* cardinal.mul_le_max
- \+ *lemma* cardinal.power_nat_le_max



## [2021-09-22 02:48:39](https://github.com/leanprover-community/mathlib/commit/9c34e80)
chore(linear_algebra/basic): generalize `add_monoid_hom_lequiv_{nat,int}` ([#9233](https://github.com/leanprover-community/mathlib/pull/9233))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* add_monoid_hom_lequiv_int
- \+/\- *def* add_monoid_hom_lequiv_nat



## [2021-09-22 01:01:52](https://github.com/leanprover-community/mathlib/commit/5625ec0)
refactor(algebra/module/linear_map): Put linear equivalences in their own file ([#9301](https://github.com/leanprover-community/mathlib/pull/9301))
This is consistent with how we have ring homs and ring equivs in separate files.
By having each of these files smaller than the original, we can split `linear_algebra/basic` more effectively between them.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \- *def* distrib_mul_action.to_linear_equiv
- \- *def* distrib_mul_action.to_linear_map
- \- *theorem* linear_equiv.apply_symm_apply
- \- *theorem* linear_equiv.coe_coe
- \- *lemma* linear_equiv.coe_mk
- \- *lemma* linear_equiv.coe_of_involutive
- \- *lemma* linear_equiv.coe_symm_mk
- \- *lemma* linear_equiv.coe_to_add_equiv
- \- *lemma* linear_equiv.coe_to_equiv
- \- *lemma* linear_equiv.coe_to_linear_map
- \- *lemma* linear_equiv.comp_coe
- \- *lemma* linear_equiv.eq_symm_apply
- \- *lemma* linear_equiv.ext
- \- *lemma* linear_equiv.ext_iff
- \- *lemma* linear_equiv.inv_fun_eq_symm
- \- *theorem* linear_equiv.map_add
- \- *theorem* linear_equiv.map_eq_zero_iff
- \- *theorem* linear_equiv.map_ne_zero_iff
- \- *theorem* linear_equiv.map_smul
- \- *lemma* linear_equiv.map_sum
- \- *theorem* linear_equiv.map_zero
- \- *lemma* linear_equiv.mk_coe'
- \- *lemma* linear_equiv.mk_coe
- \- *def* linear_equiv.of_involutive
- \- *def* linear_equiv.refl
- \- *lemma* linear_equiv.refl_apply
- \- *lemma* linear_equiv.refl_symm
- \- *lemma* linear_equiv.refl_to_linear_map
- \- *lemma* linear_equiv.refl_trans
- \- *def* linear_equiv.restrict_scalars
- \- *lemma* linear_equiv.restrict_scalars_inj
- \- *lemma* linear_equiv.restrict_scalars_injective
- \- *def* linear_equiv.simps.symm_apply
- \- *def* linear_equiv.symm
- \- *theorem* linear_equiv.symm_apply_apply
- \- *lemma* linear_equiv.symm_apply_eq
- \- *lemma* linear_equiv.symm_bijective
- \- *theorem* linear_equiv.symm_mk
- \- *theorem* linear_equiv.symm_symm
- \- *lemma* linear_equiv.symm_trans
- \- *lemma* linear_equiv.symm_trans_apply
- \- *lemma* linear_equiv.to_add_monoid_hom_commutes
- \- *def* linear_equiv.to_equiv
- \- *lemma* linear_equiv.to_equiv_inj
- \- *lemma* linear_equiv.to_equiv_injective
- \- *lemma* linear_equiv.to_fun_eq_coe
- \- *lemma* linear_equiv.to_linear_map_eq_coe
- \- *lemma* linear_equiv.to_linear_map_inj
- \- *lemma* linear_equiv.to_linear_map_injective
- \- *def* linear_equiv.trans
- \- *theorem* linear_equiv.trans_apply
- \- *lemma* linear_equiv.trans_refl
- \- *lemma* linear_equiv.trans_symm
- \- *def* module.comp_hom.to_linear_equiv

Modified src/algebra/module/opposites.lean


Modified src/algebra/module/submodule.lean


Added src/data/equiv/module.lean
- \+ *def* distrib_mul_action.to_linear_equiv
- \+ *def* distrib_mul_action.to_linear_map
- \+ *theorem* linear_equiv.apply_symm_apply
- \+ *theorem* linear_equiv.coe_coe
- \+ *lemma* linear_equiv.coe_mk
- \+ *lemma* linear_equiv.coe_of_involutive
- \+ *lemma* linear_equiv.coe_symm_mk
- \+ *lemma* linear_equiv.coe_to_add_equiv
- \+ *lemma* linear_equiv.coe_to_equiv
- \+ *lemma* linear_equiv.coe_to_linear_map
- \+ *lemma* linear_equiv.comp_coe
- \+ *lemma* linear_equiv.eq_symm_apply
- \+ *lemma* linear_equiv.ext
- \+ *lemma* linear_equiv.ext_iff
- \+ *lemma* linear_equiv.inv_fun_eq_symm
- \+ *theorem* linear_equiv.map_add
- \+ *theorem* linear_equiv.map_eq_zero_iff
- \+ *theorem* linear_equiv.map_ne_zero_iff
- \+ *theorem* linear_equiv.map_smul
- \+ *lemma* linear_equiv.map_sum
- \+ *theorem* linear_equiv.map_zero
- \+ *lemma* linear_equiv.mk_coe'
- \+ *lemma* linear_equiv.mk_coe
- \+ *def* linear_equiv.of_involutive
- \+ *def* linear_equiv.refl
- \+ *lemma* linear_equiv.refl_apply
- \+ *lemma* linear_equiv.refl_symm
- \+ *lemma* linear_equiv.refl_to_linear_map
- \+ *lemma* linear_equiv.refl_trans
- \+ *def* linear_equiv.restrict_scalars
- \+ *lemma* linear_equiv.restrict_scalars_inj
- \+ *lemma* linear_equiv.restrict_scalars_injective
- \+ *def* linear_equiv.simps.symm_apply
- \+ *def* linear_equiv.symm
- \+ *theorem* linear_equiv.symm_apply_apply
- \+ *lemma* linear_equiv.symm_apply_eq
- \+ *lemma* linear_equiv.symm_bijective
- \+ *theorem* linear_equiv.symm_mk
- \+ *theorem* linear_equiv.symm_symm
- \+ *lemma* linear_equiv.symm_trans
- \+ *lemma* linear_equiv.symm_trans_apply
- \+ *lemma* linear_equiv.to_add_monoid_hom_commutes
- \+ *def* linear_equiv.to_equiv
- \+ *lemma* linear_equiv.to_equiv_inj
- \+ *lemma* linear_equiv.to_equiv_injective
- \+ *lemma* linear_equiv.to_fun_eq_coe
- \+ *lemma* linear_equiv.to_linear_map_eq_coe
- \+ *lemma* linear_equiv.to_linear_map_inj
- \+ *lemma* linear_equiv.to_linear_map_injective
- \+ *def* linear_equiv.trans
- \+ *theorem* linear_equiv.trans_apply
- \+ *lemma* linear_equiv.trans_refl
- \+ *lemma* linear_equiv.trans_symm
- \+ *def* module.comp_hom.to_linear_equiv

Modified src/data/finsupp/to_dfinsupp.lean




## [2021-09-21 17:41:00](https://github.com/leanprover-community/mathlib/commit/e0d568e)
feat(analysis/normed_space/basic): the rescaling of a ball is a ball ([#9297](https://github.com/leanprover-community/mathlib/pull/9297))
Also rename all statements with `ball_0` to `ball_zero` for coherence.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* preimage_smul_inv'
- \+ *lemma* preimage_smul_inv

Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/basic.lean
- \- *lemma* ball_0_eq
- \+ *lemma* ball_zero_eq
- \- *lemma* mem_ball_0_iff
- \+ *lemma* mem_ball_zero_iff
- \- *lemma* mem_emetric_ball_0_iff
- \+ *lemma* mem_emetric_ball_zero_iff
- \+ *lemma* preimage_add_ball
- \+ *lemma* preimage_add_closed_ball
- \+ *lemma* preimage_add_sphere
- \+ *theorem* smul_ball
- \+ *theorem* smul_closed_ball'
- \+ *theorem* smul_closed_ball

Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.ball_disjoint_ball



## [2021-09-21 15:54:06](https://github.com/leanprover-community/mathlib/commit/56a6ed6)
chore(algebra/algebra/basic): remove a duplicate instance ([#9320](https://github.com/leanprover-community/mathlib/pull/9320))
`algebra.linear_map.module'` is just a special case of `linear_map.module'`.
`by apply_instance` finds this instance provided it's used after the definition of `is_scalar_tower.to_smul_comm_class`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean




## [2021-09-21 15:54:04](https://github.com/leanprover-community/mathlib/commit/420f11a)
feat(measure_theory/decomposition/radon_nikodym): Radon-Nikodym and Lebesgue decomposition for signed measures ([#9065](https://github.com/leanprover-community/mathlib/pull/9065))
This PR proves the Radon-Nikodym theorem for signed measures.
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean
- \+ *lemma* measure_theory.jordan_decomposition.coe_smul
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_def
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_neg
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_neg_part_neg
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_neg_part_nonneg
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_nonneg
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_pos_part_neg
- \+ *lemma* measure_theory.jordan_decomposition.real_smul_pos_part_nonneg
- \+ *lemma* measure_theory.jordan_decomposition.smul_neg_part
- \+ *lemma* measure_theory.jordan_decomposition.smul_pos_part
- \+ *lemma* measure_theory.jordan_decomposition.to_signed_measure_smul
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_eq
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_smul
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_smul_real
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_smul_real_nonneg
- \+ *lemma* measure_theory.signed_measure.total_variation_mutually_singular_iff

Modified src/measure_theory/decomposition/lebesgue.lean
- \+ *lemma* measure_theory.measure.lintegral_radon_nikodym_deriv_lt_top
- \+ *lemma* measure_theory.measure.singular_part_add
- \+ *lemma* measure_theory.measure.singular_part_smul
- \+ *lemma* measure_theory.measure.singular_part_zero
- \+ *theorem* measure_theory.signed_measure.eq_radon_nikodym_deriv
- \+ *theorem* measure_theory.signed_measure.eq_singular_part
- \+ *lemma* measure_theory.signed_measure.have_lebesgue_decomposition_mk
- \+ *lemma* measure_theory.signed_measure.integrable_radon_nikodym_deriv
- \+ *lemma* measure_theory.signed_measure.jordan_decomposition_add_with_density_mutually_singular
- \+ *lemma* measure_theory.signed_measure.measurable_radon_nikodym_deriv
- \+ *lemma* measure_theory.signed_measure.mutually_singular_singular_part
- \+ *lemma* measure_theory.signed_measure.not_have_lebesgue_decomposition_iff
- \+ *def* measure_theory.signed_measure.radon_nikodym_deriv
- \+ *lemma* measure_theory.signed_measure.radon_nikodym_deriv_add
- \+ *lemma* measure_theory.signed_measure.radon_nikodym_deriv_neg
- \+ *lemma* measure_theory.signed_measure.radon_nikodym_deriv_smul
- \+ *lemma* measure_theory.signed_measure.radon_nikodym_deriv_sub
- \+ *def* measure_theory.signed_measure.singular_part
- \+ *lemma* measure_theory.signed_measure.singular_part_add
- \+ *theorem* measure_theory.signed_measure.singular_part_add_with_density_radon_nikodym_deriv_eq
- \+ *lemma* measure_theory.signed_measure.singular_part_mutually_singular
- \+ *lemma* measure_theory.signed_measure.singular_part_neg
- \+ *lemma* measure_theory.signed_measure.singular_part_smul
- \+ *lemma* measure_theory.signed_measure.singular_part_smul_nnreal
- \+ *lemma* measure_theory.signed_measure.singular_part_sub
- \+ *lemma* measure_theory.signed_measure.singular_part_total_variation
- \+ *lemma* measure_theory.signed_measure.singular_part_zero
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_eq_of_eq_add_with_density

Modified src/measure_theory/decomposition/radon_nikodym.lean
- \+ *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_to_real_eq
- \+ *theorem* measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_radon_nikodym_deriv_eq
- \+ *theorem* measure_theory.signed_measure.with_densityᵥ_radon_nikodym_deriv_eq

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.with_density_of_real_mutually_singular

Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.measure.to_signed_measure_congr

Modified src/measure_theory/measure/with_density_vector_measure.lean




## [2021-09-21 14:54:34](https://github.com/leanprover-community/mathlib/commit/c4fbb6f)
refactor(data/real/ereal): replace `.cases` with `.rec` ([#9321](https://github.com/leanprover-community/mathlib/pull/9321))
This provides a nicer spelling than the pile of `rfl`s we use with the old `ereal.cases`, as follows:
```diff
-rcases x.cases with rfl|⟨y, rfl⟩|rfl,
+induction x using ereal.rec with y,
```
As a bonus, the subgoals now end up with names matching the hypotheses.
#### Estimated changes
Modified src/data/real/ereal.lean


Modified src/topology/instances/ereal.lean




## [2021-09-21 11:46:50](https://github.com/leanprover-community/mathlib/commit/30617c7)
chore(group_theory/order_of_element): bump up ([#9318](https://github.com/leanprover-community/mathlib/pull/9318))
there may be other lemmas that can similarly be moved around here
#### Estimated changes
Modified src/group_theory/order_of_element.lean




## [2021-09-21 09:53:10](https://github.com/leanprover-community/mathlib/commit/b5a6422)
feat(data/finset): add lemmas ([#9209](https://github.com/leanprover-community/mathlib/pull/9209))
* add `finset.image_id'`, a version of `finset.image_id` using `λ x, x` instead of `id`;
* add some lemmas about `finset.bUnion`, `finset.sup`, and `finset.sup'`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.bUnion_nonempty
- \+ *theorem* finset.image_id'
- \+ *lemma* finset.nonempty.bUnion

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf'_bUnion
- \+ *lemma* finset.inf'_congr
- \+ *lemma* finset.inf_bUnion
- \+ *lemma* finset.inf_const
- \+ *lemma* finset.sup'_bUnion
- \+ *lemma* finset.sup'_congr
- \+ *lemma* finset.sup_bUnion



## [2021-09-21 08:03:51](https://github.com/leanprover-community/mathlib/commit/524ded6)
refactor(data/polynomial/{coeff,monomial}): move smul_eq_C_mul ([#9287](https://github.com/leanprover-community/mathlib/pull/9287))
This moves `smul_eq_C_mul` from `monomial.lean` into `coeff.lean` so that the import on `monomial.lean` can be changed from `data.polynomial.coeff` to `data.polynomial.basic`. This should shave about 10 seconds off the [longest pole for parallelized mathlib compilation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/The.20long.20pole.20in.20mathlib/near/253932389).
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.smul_eq_C_mul

Modified src/data/polynomial/monomial.lean
- \- *lemma* polynomial.smul_eq_C_mul



## [2021-09-21 08:03:50](https://github.com/leanprover-community/mathlib/commit/4cee743)
feat(measure_theory/measure/vector_measure): add `mutually_singular.neg` ([#9282](https://github.com/leanprover-community/mathlib/pull/9282))
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.mutually_singular.neg_left
- \+ *lemma* measure_theory.vector_measure.mutually_singular.neg_left_iff
- \+ *lemma* measure_theory.vector_measure.mutually_singular.neg_right
- \+ *lemma* measure_theory.vector_measure.mutually_singular.neg_right_iff



## [2021-09-21 08:03:48](https://github.com/leanprover-community/mathlib/commit/78340e3)
feat(topology/continuous_function/basic): gluing lemmas ([#9239](https://github.com/leanprover-community/mathlib/pull/9239))
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.lift_cover_coe'
- \+ *lemma* continuous_map.lift_cover_coe
- \+ *lemma* continuous_map.lift_cover_restrict'
- \+ *lemma* continuous_map.lift_cover_restrict



## [2021-09-21 06:38:58](https://github.com/leanprover-community/mathlib/commit/49e0bcf)
feat(topology/bases): continuous_of_basis_is_open_preimage ([#9281](https://github.com/leanprover-community/mathlib/pull/9281))
Check continuity on a basis.
#### Estimated changes
Modified src/topology/bases.lean




## [2021-09-21 02:39:51](https://github.com/leanprover-community/mathlib/commit/13780bc)
chore(scripts): update nolints.txt ([#9317](https://github.com/leanprover-community/mathlib/pull/9317))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-20 20:43:00](https://github.com/leanprover-community/mathlib/commit/46ff449)
feat(data/vector/basic): lemmas, and linting ([#9260](https://github.com/leanprover-community/mathlib/pull/9260))
#### Estimated changes
Modified src/data/vector/basic.lean
- \+ *lemma* vector.length_coe
- \+ *lemma* vector.nth_repeat
- \+/\- *theorem* vector.nth_tail
- \+ *theorem* vector.nth_tail_succ
- \+ *lemma* vector.reverse_reverse

Added src/data/vector/zip.lean
- \+ *def* vector.zip_with
- \+ *lemma* vector.zip_with_nth
- \+ *lemma* vector.zip_with_tail
- \+ *lemma* vector.zip_with_to_list



## [2021-09-20 18:11:00](https://github.com/leanprover-community/mathlib/commit/175afa8)
refactor(analysis/convex/{extreme, exposed}): generalize `is_extreme` and `is_exposed` to semimodules ([#9264](https://github.com/leanprover-community/mathlib/pull/9264))
`is_extreme` and `is_exposed` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary `ordered_semiring`s in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid`.
#### Estimated changes
Modified src/analysis/convex/exposed.lean
- \+/\- *lemma* continuous_linear_map.to_exposed.is_exposed
- \+/\- *def* continuous_linear_map.to_exposed
- \+/\- *lemma* exposed_points_subset_extreme_points
- \+/\- *lemma* is_exposed.antisymm
- \+/\- *lemma* is_exposed.eq_inter_halfspace
- \+/\- *lemma* is_exposed.inter
- \+/\- *lemma* is_exposed.inter_left
- \+/\- *lemma* is_exposed.inter_right
- \+/\- *lemma* is_exposed.is_closed
- \+/\- *lemma* is_exposed.is_compact
- \+/\- *lemma* is_exposed.refl
- \+/\- *lemma* is_exposed_empty

Modified src/analysis/convex/extreme.lean
- \+ *lemma* convex.mem_extreme_points_iff_convex_diff
- \- *lemma* convex.mem_extreme_points_iff_convex_remove
- \+ *lemma* convex.mem_extreme_points_iff_mem_diff_convex_hull_diff
- \- *lemma* convex.mem_extreme_points_iff_mem_diff_convex_hull_remove
- \+/\- *lemma* extreme_points_subset
- \- *lemma* is_extreme.Inter
- \- *lemma* is_extreme.antisymm
- \- *lemma* is_extreme.bInter
- \+/\- *lemma* is_extreme.convex_diff
- \+/\- *lemma* is_extreme.extreme_points_eq
- \+/\- *lemma* is_extreme.extreme_points_subset_extreme_points
- \+/\- *lemma* is_extreme.inter
- \- *lemma* is_extreme.mono
- \- *lemma* is_extreme.refl
- \- *lemma* is_extreme.sInter
- \- *lemma* is_extreme.trans
- \+ *lemma* is_extreme_Inter
- \+ *lemma* is_extreme_bInter
- \+ *lemma* is_extreme_sInter
- \+/\- *lemma* mem_extreme_points_iff_forall_segment

Modified src/analysis/convex/independent.lean
- \+ *lemma* convex.convex_independent_extreme_points
- \- *lemma* convex.extreme_points_convex_independent



## [2021-09-20 16:39:36](https://github.com/leanprover-community/mathlib/commit/ae726e1)
chore(ring_theory/polynomial/tower): remove a duplicate instance ([#9302](https://github.com/leanprover-community/mathlib/pull/9302))
`apply_instance` already finds a much more general statement of this instance.
#### Estimated changes
Modified src/ring_theory/polynomial/tower.lean




## [2021-09-20 16:39:35](https://github.com/leanprover-community/mathlib/commit/c2d8a58)
feat(algebra/algebra/basic): lemmas about alg_hom and scalar towers ([#9249](https://github.com/leanprover-community/mathlib/pull/9249))
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* alg_hom.commutes_of_tower
- \+ *lemma* alg_hom.comp_algebra_map_of_tower
- \+/\- *lemma* algebra.lmul_algebra_map

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *lemma* linear_map.to_matrix_algebra_map



## [2021-09-20 14:51:32](https://github.com/leanprover-community/mathlib/commit/866294d)
fix(data/dfinsupp): fix nat- and int- module diamonds ([#9299](https://github.com/leanprover-community/mathlib/pull/9299))
This also defines `has_sub` separately in case it turns out to help with unification
#### Estimated changes
Modified src/data/dfinsupp.lean


Modified src/data/finsupp/to_dfinsupp.lean




## [2021-09-20 13:42:14](https://github.com/leanprover-community/mathlib/commit/3703ab2)
chore(data/real/pi): split into three files ([#9295](https://github.com/leanprover-community/mathlib/pull/9295))
This is the last file to finish compilation in mathlib, and it naturally splits into three chunks, two of which have simpler dependencies.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean


Deleted src/data/real/pi.lean
- \- *lemma* real.integral_sin_pow_div_tendsto_one
- \- *lemma* real.pi_gt_3141592
- \- *lemma* real.pi_gt_31415
- \- *lemma* real.pi_gt_314
- \- *lemma* real.pi_gt_sqrt_two_add_series
- \- *lemma* real.pi_gt_three
- \- *theorem* real.pi_lower_bound_start
- \- *lemma* real.pi_lt_3141593
- \- *lemma* real.pi_lt_31416
- \- *lemma* real.pi_lt_315
- \- *lemma* real.pi_lt_sqrt_two_add_series
- \- *theorem* real.pi_upper_bound_start
- \- *lemma* real.sqrt_two_add_series_step_down
- \- *lemma* real.sqrt_two_add_series_step_up
- \- *theorem* real.tendsto_prod_pi_div_two
- \- *theorem* real.tendsto_sum_pi_div_four

Added src/data/real/pi/bounds.lean
- \+ *lemma* real.pi_gt_3141592
- \+ *lemma* real.pi_gt_31415
- \+ *lemma* real.pi_gt_314
- \+ *lemma* real.pi_gt_sqrt_two_add_series
- \+ *lemma* real.pi_gt_three
- \+ *theorem* real.pi_lower_bound_start
- \+ *lemma* real.pi_lt_3141593
- \+ *lemma* real.pi_lt_31416
- \+ *lemma* real.pi_lt_315
- \+ *lemma* real.pi_lt_sqrt_two_add_series
- \+ *theorem* real.pi_upper_bound_start
- \+ *lemma* real.sqrt_two_add_series_step_down
- \+ *lemma* real.sqrt_two_add_series_step_up

Added src/data/real/pi/leibniz.lean
- \+ *theorem* real.tendsto_sum_pi_div_four

Added src/data/real/pi/wallis.lean
- \+ *lemma* real.integral_sin_pow_div_tendsto_one
- \+ *theorem* real.tendsto_prod_pi_div_two



## [2021-09-20 13:42:12](https://github.com/leanprover-community/mathlib/commit/8c96c54)
feat(ci): Download all possible caches in gitpod ([#9286](https://github.com/leanprover-community/mathlib/pull/9286))
This requests mathlibtools 1.1.0
#### Estimated changes
Modified .gitpod.yml




## [2021-09-20 13:42:11](https://github.com/leanprover-community/mathlib/commit/72a8cd6)
feat(field_theory/algebraic_closure): any two algebraic closures are isomorphic ([#9231](https://github.com/leanprover-community/mathlib/pull/9231))
#### Estimated changes
Modified src/field_theory/is_alg_closed/algebraic_closure.lean


Modified src/field_theory/is_alg_closed/basic.lean


Modified src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_algebraic_of_larger_base
- \- *lemma* algebra.is_algebraic_of_larger_field



## [2021-09-20 11:48:30](https://github.com/leanprover-community/mathlib/commit/cb33f68)
feat(docker): pin version for better reproducibility ([#9304](https://github.com/leanprover-community/mathlib/pull/9304))
Also hopefully force docker rebuild for gitpod
#### Estimated changes
Modified .docker/gitpod/mathlib/Dockerfile




## [2021-09-20 11:48:29](https://github.com/leanprover-community/mathlib/commit/4df2a1b)
feat(topology/instances/ennreal): sum of nonzero constants is infinity ([#9294](https://github.com/leanprover-community/mathlib/pull/9294))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tsum_const_eq_top_of_ne_zero



## [2021-09-20 11:48:28](https://github.com/leanprover-community/mathlib/commit/e41e9bc)
chore(group_theory/submonoid/operations): split a file ([#9292](https://github.com/leanprover-community/mathlib/pull/9292))
#### Estimated changes
Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/operations.lean
- \- *lemma* add_submonoid.coe_pointwise_smul
- \- *lemma* add_submonoid.smul_mem_pointwise_smul
- \- *lemma* submonoid.coe_pointwise_smul
- \- *lemma* submonoid.smul_mem_pointwise_smul

Added src/group_theory/submonoid/pointwise.lean
- \+ *lemma* add_submonoid.coe_pointwise_smul
- \+ *lemma* add_submonoid.smul_mem_pointwise_smul
- \+ *lemma* submonoid.coe_pointwise_smul
- \+ *lemma* submonoid.smul_mem_pointwise_smul



## [2021-09-20 11:48:27](https://github.com/leanprover-community/mathlib/commit/7389a6b)
feat(linear_algebra/matrix/to_lin): simp lemmas for to_matrix and algebra ([#9267](https://github.com/leanprover-community/mathlib/pull/9267))
#### Estimated changes
Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* linear_map.to_matrix'_algebra_map
- \+ *lemma* linear_map.to_matrix_algebra_map



## [2021-09-20 11:48:26](https://github.com/leanprover-community/mathlib/commit/ba28234)
feat(algebra/pointwise): more lemmas about pointwise actions ([#9226](https://github.com/leanprover-community/mathlib/pull/9226))
This:
* Primes the existing lemmas about `group_with_zero` and adds their group counterparts
* Adds:
  * `smul_mem_smul_set_iff`
  * `set_smul_subset_set_smul_iff`
  * `set_smul_subset_iff`
  * `subset_set_smul_iff`
* Generalizes `zero_smul_set` to take weaker typeclasses
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* mem_inv_smul_set_iff'
- \+/\- *lemma* mem_inv_smul_set_iff
- \+ *lemma* mem_smul_set_iff_inv_smul_mem'
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \+/\- *lemma* preimage_smul'
- \+/\- *lemma* preimage_smul
- \+ *lemma* set_smul_subset_iff'
- \+ *lemma* set_smul_subset_iff
- \+ *lemma* set_smul_subset_set_smul_iff'
- \+ *lemma* set_smul_subset_set_smul_iff
- \+ *lemma* smul_mem_smul_set_iff'
- \+ *lemma* smul_mem_smul_set_iff
- \+ *lemma* subset_set_smul_iff'
- \+ *lemma* subset_set_smul_iff
- \+/\- *lemma* zero_smul_set

Modified src/analysis/convex/basic.lean


Modified src/analysis/seminorm.lean




## [2021-09-20 10:37:41](https://github.com/leanprover-community/mathlib/commit/e29dfc1)
chore(analysis/normed_space/finite_dimensional): restructure imports ([#9289](https://github.com/leanprover-community/mathlib/pull/9289))
Delays importing `linear_algebra.finite_dimensional` in the `analysis/normed_space/` directory until it is really needed.
This reduces the ["long pole"](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/The.20long.20pole.20in.20mathlib) of mathlib compilation by 3 minutes (out of 55).
#### Estimated changes
Modified src/analysis/normed_space/affine_isometry.lean
- \- *lemma* affine_isometry.coe_to_affine_isometry_equiv
- \- *lemma* affine_isometry.to_affine_isometry_equiv_apply

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* affine_isometry.coe_to_affine_isometry_equiv
- \+ *def* affine_isometry.to_affine_isometry_equiv
- \+ *lemma* affine_isometry.to_affine_isometry_equiv_apply
- \+ *lemma* linear_isometry.coe_to_linear_isometry_equiv
- \+ *def* linear_isometry.to_linear_isometry_equiv
- \+ *lemma* linear_isometry.to_linear_isometry_equiv_apply

Modified src/analysis/normed_space/linear_isometry.lean
- \- *lemma* linear_isometry.coe_to_linear_isometry_equiv
- \- *lemma* linear_isometry.to_linear_isometry_equiv_apply



## [2021-09-20 08:13:28](https://github.com/leanprover-community/mathlib/commit/d93c6a8)
feat(data/vector/basic): induction principles ([#9261](https://github.com/leanprover-community/mathlib/pull/9261))
#### Estimated changes
Modified src/data/vector/basic.lean
- \+/\- *def* vector.induction_on
- \+ *def* vector.induction_on₂
- \+ *def* vector.induction_on₃



## [2021-09-20 04:23:41](https://github.com/leanprover-community/mathlib/commit/238d792)
chore(scripts): update nolints.txt ([#9290](https://github.com/leanprover-community/mathlib/pull/9290))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-20 04:23:40](https://github.com/leanprover-community/mathlib/commit/035bd24)
refactor(field_theory/algebraic_closure): Move construction of algebraic closure and lemmas about alg closed fields into seperate files. ([#9265](https://github.com/leanprover-community/mathlib/pull/9265))
#### Estimated changes
Modified src/analysis/complex/polynomial.lean


Modified src/category_theory/preadditive/schur.lean


Added src/field_theory/is_alg_closed/algebraic_closure.lean
- \+ *theorem* algebraic_closure.adjoin_monic.algebra_map
- \+ *theorem* algebraic_closure.adjoin_monic.exists_root
- \+ *theorem* algebraic_closure.adjoin_monic.is_integral
- \+ *def* algebraic_closure.adjoin_monic
- \+ *lemma* algebraic_closure.algebra_map_def
- \+ *lemma* algebraic_closure.coe_to_step_of_le
- \+ *def* algebraic_closure.eval_X_self
- \+ *theorem* algebraic_closure.exists_of_step
- \+ *theorem* algebraic_closure.exists_root
- \+ *theorem* algebraic_closure.is_algebraic
- \+ *theorem* algebraic_closure.le_max_ideal
- \+ *def* algebraic_closure.max_ideal
- \+ *def* algebraic_closure.monic_irreducible
- \+ *def* algebraic_closure.of_step
- \+ *def* algebraic_closure.of_step_hom
- \+ *theorem* algebraic_closure.of_step_succ
- \+ *def* algebraic_closure.span_eval
- \+ *theorem* algebraic_closure.span_eval_ne_top
- \+ *theorem* algebraic_closure.step.is_integral
- \+ *def* algebraic_closure.step
- \+ *def* algebraic_closure.step_aux
- \+ *def* algebraic_closure.to_adjoin_monic
- \+ *def* algebraic_closure.to_splitting_field
- \+ *theorem* algebraic_closure.to_splitting_field_eval_X_self
- \+ *def* algebraic_closure.to_step_of_le
- \+ *theorem* algebraic_closure.to_step_succ.exists_root
- \+ *def* algebraic_closure.to_step_succ
- \+ *def* algebraic_closure.to_step_zero
- \+ *def* algebraic_closure

Renamed src/field_theory/algebraic_closure.lean to src/field_theory/is_alg_closed/basic.lean
- \- *theorem* algebraic_closure.adjoin_monic.algebra_map
- \- *theorem* algebraic_closure.adjoin_monic.exists_root
- \- *theorem* algebraic_closure.adjoin_monic.is_integral
- \- *def* algebraic_closure.adjoin_monic
- \- *lemma* algebraic_closure.algebra_map_def
- \- *lemma* algebraic_closure.coe_to_step_of_le
- \- *def* algebraic_closure.eval_X_self
- \- *theorem* algebraic_closure.exists_of_step
- \- *theorem* algebraic_closure.exists_root
- \- *theorem* algebraic_closure.is_algebraic
- \- *theorem* algebraic_closure.le_max_ideal
- \- *def* algebraic_closure.max_ideal
- \- *def* algebraic_closure.monic_irreducible
- \- *def* algebraic_closure.of_step
- \- *def* algebraic_closure.of_step_hom
- \- *theorem* algebraic_closure.of_step_succ
- \- *def* algebraic_closure.span_eval
- \- *theorem* algebraic_closure.span_eval_ne_top
- \- *theorem* algebraic_closure.step.is_integral
- \- *def* algebraic_closure.step
- \- *def* algebraic_closure.step_aux
- \- *def* algebraic_closure.to_adjoin_monic
- \- *def* algebraic_closure.to_splitting_field
- \- *theorem* algebraic_closure.to_splitting_field_eval_X_self
- \- *def* algebraic_closure.to_step_of_le
- \- *theorem* algebraic_closure.to_step_succ.exists_root
- \- *def* algebraic_closure.to_step_succ
- \- *def* algebraic_closure.to_step_zero
- \- *def* algebraic_closure
- \- *def* is_alg_closed.lift
- \- *def* lift.subfield_with_hom.maximal_subfield_with_hom

Modified src/field_theory/primitive_element.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/trace.lean




## [2021-09-20 04:23:39](https://github.com/leanprover-community/mathlib/commit/acb10a5)
feat(linear_algebra/{multilinear,alternating): add of_subsingleton ([#9196](https://github.com/leanprover-community/mathlib/pull/9196))
This was refactored from the `koszul_cx` branch, something I mentioned doing in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/two.20decidable_eq.20instances.20on.20.28fin.201.29.20in.20mathlib.20.3A-.28/near/225596630).
The original version was:
```lean
def multilinear_map.of_subsingleton (ι : Type v) [subsingleton ι] [inhabited ι] {N : Type u}
  [add_comm_group N] [module R N] (f : M →ₗ[R] N) : multilinear_map R (λ (i : ι), M) N :=
{ to_fun := λ x, f (x $ default ι),
  map_add' := λ m i x y, by rw subsingleton.elim i (default ι); simp only
    [function.update_same, f.map_add],
  map_smul' := λ m i r x, by rw subsingleton.elim i (default ι); simp only
    [function.update_same, f.map_smul], }
```
but I decided to remove the `f : M →ₗ[R] N` argument as it can be added later with `(of_subsingleton R M i).comp_linear_map f`.
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *def* alternating_map.of_subsingleton

Modified src/linear_algebra/multilinear.lean
- \+ *def* multilinear_map.of_subsingleton



## [2021-09-20 04:23:38](https://github.com/leanprover-community/mathlib/commit/976b261)
feat(data/{multiset,finset}/basic): card_erase_eq_ite ([#9185](https://github.com/leanprover-community/mathlib/pull/9185))
A generic theorem about the cardinality of a `finset` or `multiset` with an element erased.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_erase_eq_ite
- \+/\- *theorem* finset.erase_empty

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.card_erase_eq_ite



## [2021-09-20 01:59:40](https://github.com/leanprover-community/mathlib/commit/f37f57d)
feat(order/lattice): `sup`/`inf`/`max`/`min` of mono functions ([#9284](https://github.com/leanprover-community/mathlib/pull/9284))
* add `monotone.sup`, `monotone.inf`, `monotone.min`, and
  `monotone.max`;
* add `prod.le_def` and `prod.mk_le_mk`.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* prod.le_def
- \+ *lemma* prod.mk_le_mk

Modified src/order/lattice.lean




## [2021-09-19 21:03:01](https://github.com/leanprover-community/mathlib/commit/4887f80)
chore(measure_theory/function/simple_func_dense): distance to `approx_on` is antitone ([#9271](https://github.com/leanprover-community/mathlib/pull/9271))
#### Estimated changes
Modified src/measure_theory/function/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func.edist_approx_on_mono



## [2021-09-19 20:10:14](https://github.com/leanprover-community/mathlib/commit/f7135f1)
feat(group_theory/p_group): `is_p_group` is preserved by `subgroup.comap` ([#9277](https://github.com/leanprover-community/mathlib/pull/9277))
If `H` is a p-subgroup, then `H.comap f` is a p-subgroup, assuming that `f` is injective.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.comap_injective



## [2021-09-19 17:47:09](https://github.com/leanprover-community/mathlib/commit/965e457)
feat(measure_theory/measure/lebesgue): a linear map rescales Lebesgue by the inverse of its determinant ([#9195](https://github.com/leanprover-community/mathlib/pull/9195))
Also supporting material to be able to apply Fubini in `ι → ℝ` by separating some coordinates.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* fintype.prod_subtype_mul_prod_subtype

Modified src/data/equiv/basic.lean
- \+ *def* equiv.pi_equiv_pi_subtype_prod

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.measure.map_pi_equiv_pi_subtype_prod
- \+ *lemma* measure_theory.measure.map_pi_equiv_pi_subtype_prod_symm

Modified src/measure_theory/constructions/prod.lean
- \+ *lemma* measure_theory.measure.volume_eq_prod

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_pi_equiv_pi_subtype_prod
- \+ *lemma* measurable_pi_equiv_pi_subtype_prod_symm

Modified src/measure_theory/measure/lebesgue.lean
- \+ *lemma* real.map_linear_map_volume_pi_eq_smul_volume_pi
- \+ *lemma* real.map_matrix_volume_pi_eq_smul_volume_pi
- \+ *lemma* real.map_transvection_volume_pi
- \+ *lemma* real.map_volume_pi_add_left
- \+ *lemma* real.smul_map_diagonal_volume_pi
- \+ *lemma* real.volume_pi_preimage_add_left
- \+ *lemma* real.volume_preimage_add_left
- \+ *lemma* real.volume_preimage_add_right
- \+ *lemma* real.volume_preimage_mul_left
- \+ *lemma* real.volume_preimage_mul_right



## [2021-09-19 16:07:52](https://github.com/leanprover-community/mathlib/commit/180c758)
feat(group_theory/p_group): `is_p_group` is preserved by `subgroup.map` ([#9276](https://github.com/leanprover-community/mathlib/pull/9276))
If `H` is a p-subgroup, then `H.map f` is a p-subgroup.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.map

Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.range_restrict_surjective



## [2021-09-19 13:44:55](https://github.com/leanprover-community/mathlib/commit/55a2c1a)
refactor(set_theory/{cardinal,ordinal}): swap the order of universes in `lift` ([#9273](https://github.com/leanprover-community/mathlib/pull/9273))
Swap the order of universe arguments in `cardinal.lift` and `ordinal.lift`. This way (a) they match the order of arguments in `ulift`; (b) usually Lean can deduce the second universe level from the argument.
#### Estimated changes
Modified src/data/complex/module.lean
- \+/\- *lemma* complex.{u}

Modified src/field_theory/tower.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/set_theory/cardinal.lean
- \+/\- *def* cardinal.lift
- \+/\- *lemma* cardinal.lift_eq_nat_iff
- \+/\- *theorem* cardinal.lift_mk
- \+/\- *theorem* cardinal.lift_umax

Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/ordinal.lean
- \+/\- *theorem* cardinal.lift_lt_univ'
- \+/\- *theorem* cardinal.lift_lt_univ
- \+/\- *theorem* cardinal.lift_univ
- \+/\- *theorem* cardinal.lt_univ'
- \+/\- *theorem* cardinal.lt_univ
- \+/\- *def* cardinal.univ
- \+/\- *def* ordinal.lift
- \+/\- *theorem* ordinal.lift_lift
- \+/\- *theorem* ordinal.lift_umax
- \+/\- *theorem* ordinal.lift_univ
- \+/\- *theorem* ordinal.one_eq_lift_type_unit
- \+/\- *def* ordinal.univ
- \+/\- *theorem* ordinal.zero_eq_lift_type_empty

Modified src/set_theory/ordinal_arithmetic.lean




## [2021-09-19 13:44:53](https://github.com/leanprover-community/mathlib/commit/8df86df)
feat(order/ideal, data/set/lattice): when order ideals are a complete lattice ([#9084](https://github.com/leanprover-community/mathlib/pull/9084))
- Added the `ideal_Inter_nonempty` property, which states that the intersection of all ideals in the lattice is nonempty.
- Proved that when a preorder has the above property and is a `semilattice_sup`, its ideals are a complete lattice
- Added some lemmas about empty intersections in set/lattice, akin to [#9033](https://github.com/leanprover-community/mathlib/pull/9033)
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_eq_empty_iff
- \+ *lemma* set.bInter_eq_empty_iff
- \+ *theorem* set.nonempty_Inter
- \+ *theorem* set.nonempty_bInter
- \+ *theorem* set.nonempty_sInter
- \- *theorem* set.sInter_nonempty_iff

Modified src/order/ideal.lean
- \+ *lemma* order.ideal.Inf_le
- \+ *lemma* order.ideal.Inter_nonempty
- \+ *lemma* order.ideal.coe_Inf
- \+ *lemma* order.ideal.coe_top
- \+ *lemma* order.ideal.ideal_Inter_nonempty.all_Inter_nonempty
- \+ *lemma* order.ideal.ideal_Inter_nonempty.all_bInter_nonempty
- \+ *lemma* order.ideal.ideal_Inter_nonempty.exists_all_mem
- \+ *lemma* order.ideal.ideal_Inter_nonempty_iff
- \+ *lemma* order.ideal.ideal_Inter_nonempty_of_exists_all_mem
- \+ *lemma* order.ideal.inter_nonempty
- \+ *lemma* order.ideal.is_glb_Inf
- \+ *lemma* order.ideal.le_Inf
- \+ *lemma* order.ideal.mem_Inf
- \- *lemma* order.ideal.top_carrier
- \- *lemma* order.ideal.top_coe
- \- *lemma* order.inter_nonempty



## [2021-09-19 11:34:13](https://github.com/leanprover-community/mathlib/commit/075ff37)
refactor(algebra/order*): move files about ordered algebraic structures into subfolder ([#9024](https://github.com/leanprover-community/mathlib/pull/9024))
There were many files named `algebra/order_*.lean`. There are also `algebra.{module,algebra}.ordered`. The latter are Prop-valued mixins. This refactor moves the data typeclasses into their own subfolder. That should help facilitate organizing further refactoring to provide the full gamut of the order x algebra hierarchy.
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Modified counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean


Modified src/algebra/big_operators/order.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/floor.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/lattice_ordered_group.lean


Modified src/algebra/module/ordered.lean


Renamed src/algebra/absolute_value.lean to src/algebra/order/absolute_value.lean


Renamed src/algebra/order.lean to src/algebra/order/basic.lean


Renamed src/algebra/euclidean_absolute_value.lean to src/algebra/order/euclidean_absolute_value.lean


Renamed src/algebra/ordered_field.lean to src/algebra/order/field.lean


Renamed src/algebra/order_functions.lean to src/algebra/order/functions.lean


Renamed src/algebra/ordered_group.lean to src/algebra/order/group.lean


Renamed src/algebra/ordered_monoid.lean to src/algebra/order/monoid.lean


Renamed src/algebra/ordered_monoid_lemmas.lean to src/algebra/order/monoid_lemmas.lean


Renamed src/algebra/ordered_pi.lean to src/algebra/order/pi.lean


Renamed src/algebra/ordered_pointwise.lean to src/algebra/order/pointwise.lean


Renamed src/algebra/ordered_ring.lean to src/algebra/order/ring.lean


Renamed src/algebra/ordered_smul.lean to src/algebra/order/smul.lean


Renamed src/algebra/ordered_sub.lean to src/algebra/order/sub.lean


Renamed src/algebra/linear_ordered_comm_group_with_zero.lean to src/algebra/order/with_zero.lean


Modified src/algebra/regular/basic.lean


Modified src/algebra/star/basic.lean


Modified src/computability/turing_machine.lean


Modified src/data/int/absolute_value.lean


Modified src/data/int/basic.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/with_bot.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/polynomial/degree/card_pow_degree.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean


Modified src/number_theory/class_number/admissible_absolute_value.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/order/basic.lean


Modified src/order/pilex.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/tactic/default.lean


Modified src/tactic/linarith/lemmas.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/push_neg.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified test/finish4.lean


Modified test/library_search/ordered_ring.lean


Modified test/monotonicity.lean


Modified test/nontriviality.lean




## [2021-09-19 10:06:14](https://github.com/leanprover-community/mathlib/commit/383e05a)
feat(measure_theory/integral/lebesgue): add set version of `lintegral_with_density_eq_lintegral_mul` ([#9270](https://github.com/leanprover-community/mathlib/pull/9270))
I also made `measurable_space α` an implicit argument whenever `μ : measure α` is explicit.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.lintegral_trim
- \+/\- *lemma* measure_theory.lintegral_trim_ae
- \+/\- *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul
- \+ *lemma* measure_theory.restrict_with_density
- \+ *lemma* measure_theory.set_lintegral_with_density_eq_set_lintegral_mul



## [2021-09-19 07:45:41](https://github.com/leanprover-community/mathlib/commit/25e67dd)
feat(measure_theory/function/lp_space): add mem_Lp_indicator_iff_restrict ([#9221](https://github.com/leanprover-community/mathlib/pull/9221))
We have an equivalent lemma for `integrable`. Here it is generalized to `mem_ℒp`.
#### Estimated changes
Modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_indicator_eq_ess_sup_restrict

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp_indicator_iff_restrict
- \+ *lemma* measure_theory.snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict
- \+ *lemma* measure_theory.snorm_indicator_eq_snorm_restrict

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* map_restrict_ae_le_map_indicator_ae
- \+ *lemma* measure_theory.mem_map_restrict_ae_iff
- \+ *lemma* mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem
- \+ *lemma* mem_map_indicator_ae_iff_of_zero_nmem



## [2021-09-19 06:12:34](https://github.com/leanprover-community/mathlib/commit/f2c162c)
feat(data/dfinsupp): more lemmas about erase, filter, and negation ([#9248](https://github.com/leanprover-community/mathlib/pull/9248))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.erase_add
- \+ *def* dfinsupp.erase_add_hom
- \+ *lemma* dfinsupp.erase_neg
- \+ *lemma* dfinsupp.erase_single
- \+ *lemma* dfinsupp.erase_single_ne
- \+ *lemma* dfinsupp.erase_single_same
- \+ *lemma* dfinsupp.erase_sub
- \+ *lemma* dfinsupp.erase_zero
- \+ *lemma* dfinsupp.filter_single
- \+ *lemma* dfinsupp.filter_single_neg
- \+ *lemma* dfinsupp.filter_single_pos
- \+ *lemma* dfinsupp.single_neg
- \+ *lemma* dfinsupp.single_sub



## [2021-09-19 02:28:42](https://github.com/leanprover-community/mathlib/commit/cbf8788)
chore(scripts): update nolints.txt ([#9275](https://github.com/leanprover-community/mathlib/pull/9275))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-18 23:07:48](https://github.com/leanprover-community/mathlib/commit/fbc9e5e)
feat(measure_theory/function/conditional_expectation): condexp_ind is ae_measurable' ([#9263](https://github.com/leanprover-community/mathlib/pull/9263))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *def* measure_theory.Lp_meas_subgroup
- \+ *lemma* measure_theory.Lp_meas_subgroup_coe
- \+ *def* measure_theory.Lp_meas_subgroup_to_Lp_meas_iso
- \+ *def* measure_theory.Lp_meas_subgroup_to_Lp_trim
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_add
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_ae_eq
- \+ *def* measure_theory.Lp_meas_subgroup_to_Lp_trim_iso
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_left_inv
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_neg
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_norm_map
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_right_inv
- \+ *lemma* measure_theory.Lp_meas_subgroup_to_Lp_trim_sub
- \- *def* measure_theory.Lp_meas_to_Lp_trim
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_add
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_ae_eq
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_left_inv
- \- *def* measure_theory.Lp_meas_to_Lp_trim_lie
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_norm_map
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_right_inv
- \- *lemma* measure_theory.Lp_meas_to_Lp_trim_smul
- \- *def* measure_theory.Lp_trim_to_Lp_meas
- \- *lemma* measure_theory.Lp_trim_to_Lp_meas_ae_eq
- \+ *def* measure_theory.Lp_trim_to_Lp_meas_subgroup
- \+ *lemma* measure_theory.Lp_trim_to_Lp_meas_subgroup_ae_eq
- \+ *lemma* measure_theory.ae_measurable'_condexp_L2
- \+ *lemma* measure_theory.ae_measurable'_condexp_ind
- \+ *lemma* measure_theory.ae_measurable'_condexp_ind_smul
- \+ *lemma* measure_theory.is_closed_ae_measurable'
- \+ *lemma* measure_theory.is_complete_ae_measurable'
- \+ *lemma* measure_theory.isometry_Lp_meas_subgroup_to_Lp_trim
- \+ *lemma* measure_theory.mem_Lp_meas_subgroup_iff_ae_measurable'
- \+ *lemma* measure_theory.mem_Lp_meas_subgroup_to_Lp_of_trim
- \- *lemma* measure_theory.mem_Lp_meas_to_Lp_of_trim
- \- *lemma* measure_theory.mem_ℒp_trim_of_mem_Lp_meas
- \+ *lemma* measure_theory.mem_ℒp_trim_of_mem_Lp_meas_subgroup



## [2021-09-18 23:07:47](https://github.com/leanprover-community/mathlib/commit/6b96736)
feat(measure_theory/integral/set_to_L1): image of an indicator by set_to_fun (and related functions) ([#9205](https://github.com/leanprover-community/mathlib/pull/9205))
We show the following equality, as well as versions of it for other intermediate `set_to_*` functions:
```
set_to_fun (hT : dominated_fin_meas_additive μ T C) (s.indicator (λ _, x)) = T s x
```
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.range_indicator

Modified src/measure_theory/integral/set_to_l1.lean
- \+/\- *def* measure_theory.L1.set_to_L1'
- \+/\- *def* measure_theory.L1.set_to_L1
- \+/\- *lemma* measure_theory.L1.set_to_L1_eq_set_to_L1'
- \+ *lemma* measure_theory.L1.set_to_L1_indicator_const_Lp
- \+/\- *lemma* measure_theory.L1.set_to_L1_smul
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_indicator_const
- \+ *lemma* measure_theory.set_to_fun_indicator_const
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_indicator



## [2021-09-18 23:07:46](https://github.com/leanprover-community/mathlib/commit/c1d7ee5)
feat(measure_theory/measure/finite_measure_weak_convergence): definitions of types of finite_measures and probability_measures, to be equipped with the topologies of weak convergence ([#8904](https://github.com/leanprover-community/mathlib/pull/8904))
feat(measure_theory/measure/finite_measure_weak_convergence): definitions of types of finite_measures and probability_measures, to be equipped with the topologies of weak convergence
This PR defines the types `probability_measure` and `finite_measure`. The next step is to give a topology instance on these types.
#### Estimated changes
Added src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* measure_theory.finite_measure.coe_add
- \+ *def* measure_theory.finite_measure.coe_add_monoid_hom
- \+ *lemma* measure_theory.finite_measure.coe_fn_add
- \+ *lemma* measure_theory.finite_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure
- \+ *lemma* measure_theory.finite_measure.coe_fn_smul
- \+ *lemma* measure_theory.finite_measure.coe_fn_zero
- \+ *lemma* measure_theory.finite_measure.coe_injective
- \+ *lemma* measure_theory.finite_measure.coe_smul
- \+ *lemma* measure_theory.finite_measure.coe_zero
- \+ *lemma* measure_theory.finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure
- \+ *lemma* measure_theory.finite_measure.ennreal_mass
- \+ *def* measure_theory.finite_measure.mass
- \+ *lemma* measure_theory.finite_measure.val_eq_to_measure
- \+ *def* measure_theory.finite_measure
- \+ *lemma* measure_theory.probability_measure.coe_comp_to_finite_measure_eq_coe
- \+ *lemma* measure_theory.probability_measure.coe_fn_comp_to_finite_measure_eq_coe_fn
- \+ *lemma* measure_theory.probability_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure
- \+ *lemma* measure_theory.probability_measure.coe_fn_univ
- \+ *lemma* measure_theory.probability_measure.coe_injective
- \+ *lemma* measure_theory.probability_measure.ennreal_coe_fn_eq_coe_fn_to_measure
- \+ *lemma* measure_theory.probability_measure.mass_to_finite_measure
- \+ *def* measure_theory.probability_measure.to_finite_measure
- \+ *lemma* measure_theory.probability_measure.val_eq_to_measure
- \+ *def* measure_theory.probability_measure



## [2021-09-18 20:45:54](https://github.com/leanprover-community/mathlib/commit/429aaa3)
feat(order/bounded_lattice): coe_unbot simp lemma ([#9258](https://github.com/leanprover-community/mathlib/pull/9258))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* with_bot.coe_unbot
- \+ *lemma* with_top.coe_untop



## [2021-09-18 20:45:53](https://github.com/leanprover-community/mathlib/commit/811c87a)
chore(order/galois_connection): golf ([#9236](https://github.com/leanprover-community/mathlib/pull/9236))
* add `galois_insertion.is_lub_of_u_image`,
  `galois_insertion.is_glb_of_u_image`,
  `galois_coinsertion.is_glb_of_l_image`, and
  `galois_coinsertion.is_lub_of_l_image`;
* get some proofs in `lift_*` from `order_dual` instances;
* this changes definitional equalities for `Inf` and `Sup` so that we can reuse the same `Inf`/`Sup` for a `conditionally_complete_lattice` later.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+/\- *lemma* algebra.coe_Inf
- \+/\- *lemma* algebra.mem_Inf

Modified src/measure_theory/measurable_space_def.lean


Modified src/order/filter/basic.lean


Modified src/order/galois_connection.lean
- \+ *lemma* galois_coinsertion.is_glb_of_l_image
- \+ *lemma* galois_coinsertion.is_lub_of_l_image
- \+ *lemma* galois_insertion.is_glb_of_u_image
- \+ *lemma* galois_insertion.is_lub_of_u_image

Modified src/topology/opens.lean




## [2021-09-18 19:04:24](https://github.com/leanprover-community/mathlib/commit/e4bf496)
feat(data/set/finite): simple infiniteness lemmas ([#9242](https://github.com/leanprover-community/mathlib/pull/9242))
#### Estimated changes
Modified archive/imo/imo2008_q2.lean


Modified src/algebra/big_operators/finprod.lean


Modified src/data/set/finite.lean
- \+ *lemma* set.infinite.diff
- \+ *lemma* set.infinite.exists_nat_lt
- \+ *lemma* set.infinite.exists_not_mem_finset
- \- *theorem* set.infinite_mono

Modified src/data/set/intervals/infinite.lean


Modified src/ring_theory/polynomial/dickson.lean




## [2021-09-18 19:04:23](https://github.com/leanprover-community/mathlib/commit/255862e)
refactor(linear_algebra/char_poly/basic): rename char_poly to matrix.charpoly ([#9230](https://github.com/leanprover-community/mathlib/pull/9230))
We rename `char_matrix` to `charmatrix` and `char_poly` to `matrix.charpoly`, so `M.charpoly` becomes available (and everything is coherent with `minpoly`).
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified docs/100.yaml


Modified docs/overview.yaml


Modified docs/undergrad.yaml


Renamed src/linear_algebra/char_poly/basic.lean to src/linear_algebra/charpoly/basic.lean
- \- *theorem* aeval_self_char_poly
- \+ *theorem* aeval_self_charpoly
- \- *def* char_matrix
- \- *lemma* char_matrix_apply_eq
- \- *lemma* char_matrix_apply_ne
- \- *def* char_poly
- \+ *def* charmatrix
- \+ *lemma* charmatrix_apply_eq
- \+ *lemma* charmatrix_apply_ne
- \- *lemma* mat_poly_equiv_char_matrix
- \+ *lemma* mat_poly_equiv_charmatrix
- \+ *def* matrix.charpoly

Renamed src/linear_algebra/char_poly/coeff.lean to src/linear_algebra/charpoly/coeff.lean
- \- *lemma* char_matrix_apply_nat_degree
- \- *lemma* char_matrix_apply_nat_degree_le
- \- *lemma* char_poly_coeff_eq_prod_coeff_of_le
- \- *theorem* char_poly_degree_eq_dim
- \- *lemma* char_poly_left_mul_matrix
- \- *lemma* char_poly_monic
- \- *theorem* char_poly_nat_degree_eq_dim
- \- *lemma* char_poly_sub_diagonal_degree_lt
- \+ *lemma* charmatrix_apply_nat_degree
- \+ *lemma* charmatrix_apply_nat_degree_le
- \+ *lemma* charpoly_coeff_eq_prod_coeff_of_le
- \+ *theorem* charpoly_degree_eq_dim
- \+ *lemma* charpoly_left_mul_matrix
- \+ *lemma* charpoly_monic
- \+ *theorem* charpoly_nat_degree_eq_dim
- \+ *lemma* charpoly_sub_diagonal_degree_lt
- \- *theorem* det_eq_sign_char_poly_coeff
- \+ *theorem* det_eq_sign_charpoly_coeff
- \- *lemma* finite_field.char_poly_pow_card
- \+ *lemma* finite_field.charpoly_pow_card
- \+/\- *theorem* matrix.is_integral
- \- *theorem* matrix.min_poly_dvd_char_poly
- \+ *theorem* matrix.minpoly_dvd_charpoly
- \- *theorem* trace_eq_neg_char_poly_coeff
- \+ *theorem* trace_eq_neg_charpoly_coeff
- \- *lemma* zmod.char_poly_pow_card
- \+ *lemma* zmod.charpoly_pow_card

Modified src/ring_theory/norm.lean


Modified src/ring_theory/trace.lean




## [2021-09-18 16:39:30](https://github.com/leanprover-community/mathlib/commit/e757936)
chore(data/real/ennreal, measure_theory/): use `≠ ∞` and `≠ 0` in assumptions ([#9219](https://github.com/leanprover-community/mathlib/pull/9219))
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+/\- *lemma* with_top.sum_lt_top

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* canonically_ordered_comm_semiring.mul_pos
- \+/\- *lemma* with_top.mul_lt_top

Modified src/analysis/convex/integral.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/pi_Lp.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/specific_limits.lean
- \+/\- *theorem* ennreal.exists_pos_sum_of_encodable'
- \+/\- *theorem* ennreal.exists_pos_sum_of_encodable
- \+/\- *theorem* ennreal.exists_pos_tsum_mul_lt_of_encodable
- \+/\- *theorem* nnreal.exists_pos_sum_of_encodable

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_left_inj
- \+/\- *lemma* ennreal.add_right_inj
- \+/\- *lemma* ennreal.add_sub_self'
- \+/\- *lemma* ennreal.add_sub_self
- \+ *lemma* ennreal.coe_ne_zero
- \+/\- *lemma* ennreal.div_lt_top
- \+ *lemma* ennreal.div_zero
- \+/\- *lemma* ennreal.half_pos
- \+/\- *lemma* ennreal.le_of_add_le_add_left
- \+/\- *lemma* ennreal.le_of_add_le_add_right
- \+/\- *lemma* ennreal.le_of_forall_pos_le_add
- \+ *lemma* ennreal.le_to_real_sub
- \+/\- *lemma* ennreal.lt_add_right
- \- *lemma* ennreal.lt_top_of_mul_lt_top_left
- \- *lemma* ennreal.lt_top_of_mul_lt_top_right
- \+ *lemma* ennreal.lt_top_of_mul_ne_top_left
- \+ *lemma* ennreal.lt_top_of_mul_ne_top_right
- \+ *lemma* ennreal.lt_top_of_sum_ne_top
- \+/\- *lemma* ennreal.mem_Iio_self_add
- \+/\- *lemma* ennreal.mem_Ioo_self_sub_add
- \+/\- *lemma* ennreal.mul_lt_top
- \+/\- *lemma* ennreal.mul_pos
- \+ *lemma* ennreal.mul_pos_iff
- \- *lemma* ennreal.ne_top_of_mul_ne_top_left
- \- *lemma* ennreal.ne_top_of_mul_ne_top_right
- \- *lemma* ennreal.not_mem_Ioo_self_sub
- \+/\- *lemma* ennreal.pow_eq_top
- \+ *lemma* ennreal.pow_eq_top_iff
- \+/\- *lemma* ennreal.prod_lt_top
- \+ *lemma* ennreal.sub_lt_of_sub_lt
- \+/\- *lemma* ennreal.sub_right_inj
- \+/\- *lemma* ennreal.sub_sub_cancel
- \+/\- *lemma* ennreal.sum_lt_top
- \+/\- *lemma* ennreal.to_nnreal_add
- \+/\- *lemma* ennreal.to_nnreal_sum
- \+/\- *lemma* ennreal.to_real_eq_to_real
- \+/\- *lemma* ennreal.to_real_sum
- \- *lemma* ennreal.zero_lt_coe_iff
- \- *lemma* ennreal.zero_lt_sub_iff_lt

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.smul_measure

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/simple_func_dense.lean


Modified src/measure_theory/group/basic.lean
- \+ *lemma* measure_theory.is_mul_left_invariant.measure_pos_iff_nonempty

Modified src/measure_theory/group/prod.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.ae_lt_top'
- \+/\- *lemma* measure_theory.ae_lt_top
- \- *lemma* measure_theory.exists_integrable_pos_of_sigma_finite
- \+ *lemma* measure_theory.exists_pos_lintegral_lt_of_sigma_finite
- \+/\- *lemma* measure_theory.exists_pos_set_lintegral_lt_of_measure_lt
- \+/\- *lemma* measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.lintegral_lt_top
- \- *lemma* measure_theory.simple_func.fin_meas_supp.of_lintegral_lt_top
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.of_lintegral_ne_top
- \+ *lemma* measure_theory.simple_func.lintegral_eq_of_subset'
- \+/\- *lemma* measure_theory.tendsto_set_lintegral_zero

Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/measure_theory/integral/vitali_caratheodory.lean
- \+/\- *lemma* measure_theory.simple_func.exists_le_lower_semicontinuous_lintegral_ge
- \+/\- *lemma* measure_theory.simple_func.exists_upper_semicontinuous_le_lintegral_le

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/content.lean
- \+/\- *lemma* measure_theory.content.outer_measure_exists_compact
- \+/\- *lemma* measure_theory.content.outer_measure_exists_open

Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.smul_finite
- \+/\- *lemma* measure_theory.measure_compl

Modified src/measure_theory/measure/measure_space_def.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/regular.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/measure_theory/measure/with_density_vector_measure.lean


Modified src/order/bounded_lattice.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.Icc_mem_nhds
- \+/\- *lemma* ennreal.nhds_of_ne_top
- \- *lemma* ennreal.tendsto_at_top_zero_of_tsum_lt_top
- \+ *lemma* ennreal.tendsto_at_top_zero_of_tsum_ne_top
- \- *lemma* ennreal.tendsto_cofinite_zero_of_tsum_lt_top
- \+ *lemma* ennreal.tendsto_cofinite_zero_of_tsum_ne_top
- \+/\- *lemma* ennreal.tsum_sub

Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* edist_ne_top

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean
- \+/\- *lemma* contracting_with.edist_efixed_point_le
- \+/\- *lemma* contracting_with.edist_efixed_point_lt_top
- \+/\- *lemma* contracting_with.edist_inequality
- \+/\- *lemma* contracting_with.efixed_point_eq_of_edist_lt_top
- \+/\- *lemma* contracting_with.efixed_point_is_fixed_pt
- \+/\- *theorem* contracting_with.exists_fixed_point
- \+/\- *lemma* contracting_with.one_sub_K_ne_top
- \+/\- *lemma* contracting_with.tendsto_iterate_efixed_point

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/lipschitz.lean
- \+/\- *lemma* lipschitz_with.edist_lt_top



## [2021-09-18 15:14:00](https://github.com/leanprover-community/mathlib/commit/33db1c7)
chore(data/mv_polynomial/basic): add ring_hom_ext' and move ext attribute to ring_hom_ext' ([#9235](https://github.com/leanprover-community/mathlib/pull/9235))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.ring_hom_ext'
- \+/\- *lemma* mv_polynomial.ring_hom_ext

Modified src/data/mv_polynomial/equiv.lean


Modified src/data/mv_polynomial/monad.lean




## [2021-09-18 13:22:05](https://github.com/leanprover-community/mathlib/commit/10a6201)
feat(set_theory/ordinal): add conditionally_complete_linear_order_bot instance ([#9266](https://github.com/leanprover-community/mathlib/pull/9266))
Currently, it is not possible to talk about `Inf s` when `s` is a set of ordinals. This is fixed by this PR.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* not_mem_of_cSup_lt
- \+ *lemma* not_mem_of_lt_cInf

Modified src/set_theory/ordinal.lean
- \+ *lemma* ordinal.Inf_eq_omin
- \+ *lemma* ordinal.Inf_mem
- \+ *lemma* ordinal.bot_eq_zero
- \+ *lemma* ordinal.induction



## [2021-09-18 12:00:20](https://github.com/leanprover-community/mathlib/commit/d6b4cd7)
chore(ring_theory/adjoin/basic): split ([#9257](https://github.com/leanprover-community/mathlib/pull/9257))
I want to use basic facts about `adjoin` in `polynomial.basic`.
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \- *theorem* algebra.adjoin_eq_range
- \- *lemma* algebra.adjoin_range_eq_range_aeval
- \- *theorem* algebra.adjoin_singleton_eq_range_aeval
- \- *theorem* algebra.fg_trans
- \- *theorem* is_noetherian_ring_of_fg
- \- *theorem* is_noetherian_subring_closure
- \- *def* subalgebra.fg
- \- *lemma* subalgebra.fg_adjoin_finset
- \- *theorem* subalgebra.fg_bot
- \- *theorem* subalgebra.fg_def
- \- *lemma* subalgebra.fg_map
- \- *lemma* subalgebra.fg_of_fg_map
- \- *theorem* subalgebra.fg_of_fg_to_submodule
- \- *theorem* subalgebra.fg_of_noetherian
- \- *lemma* subalgebra.fg_of_submodule_fg
- \- *lemma* subalgebra.fg_prod
- \- *lemma* subalgebra.fg_top
- \- *lemma* subalgebra.induction_on_adjoin

Added src/ring_theory/adjoin/fg.lean
- \+ *theorem* algebra.fg_trans
- \+ *theorem* is_noetherian_ring_of_fg
- \+ *theorem* is_noetherian_subring_closure
- \+ *def* subalgebra.fg
- \+ *lemma* subalgebra.fg_adjoin_finset
- \+ *theorem* subalgebra.fg_bot
- \+ *theorem* subalgebra.fg_def
- \+ *lemma* subalgebra.fg_map
- \+ *lemma* subalgebra.fg_of_fg_map
- \+ *theorem* subalgebra.fg_of_fg_to_submodule
- \+ *theorem* subalgebra.fg_of_noetherian
- \+ *lemma* subalgebra.fg_of_submodule_fg
- \+ *lemma* subalgebra.fg_prod
- \+ *lemma* subalgebra.fg_top
- \+ *lemma* subalgebra.induction_on_adjoin

Added src/ring_theory/adjoin/polynomial.lean
- \+ *theorem* algebra.adjoin_eq_range
- \+ *lemma* algebra.adjoin_range_eq_range_aeval
- \+ *theorem* algebra.adjoin_singleton_eq_range_aeval

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/integral_closure.lean




## [2021-09-18 10:03:09](https://github.com/leanprover-community/mathlib/commit/0ee36a3)
feat(order/conditionally_complete_lattice): add lemmas ([#9237](https://github.com/leanprover-community/mathlib/pull/9237))
* add lemmas about `conditionally_complete_linear_order_bot`; in this
  case we can drop some `nonempty` assumptions;
* add lemmas for the case of `[is_well_order α (<)]`; in this case
  infimum of a nonempty set is the least element of this set.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* Inf_eq_argmin_on
- \+ *lemma* Inf_mem
- \+ *lemma* cSup_le'
- \+ *lemma* cSup_le_iff'
- \+ *lemma* csupr_le'
- \+ *lemma* csupr_le_iff'
- \+ *lemma* exists_lt_of_lt_cSup'
- \+ *lemma* exists_lt_of_lt_csupr'
- \+/\- *lemma* is_glb.cinfi_eq
- \+ *lemma* is_least_Inf
- \+ *lemma* is_lub_cSup'
- \+ *lemma* le_cInf_iff'



## [2021-09-18 06:53:44](https://github.com/leanprover-community/mathlib/commit/36751e4)
chore(algebra/algebra/tower): golf `algebra.lsmul` ([#9253](https://github.com/leanprover-community/mathlib/pull/9253))
#### Estimated changes
Modified src/algebra/algebra/tower.lean




## [2021-09-18 06:53:43](https://github.com/leanprover-community/mathlib/commit/41e152f)
fix(algebra/algebra/tower): remove `subalgebra.res` which duplicates `subalgebra.restrict_scalars` ([#9251](https://github.com/leanprover-community/mathlib/pull/9251))
We use the name `restrict_scalars` everywhere else, so I kept that one instead of `res`.
`res` was here first, but the duplicate was added by [#7949](https://github.com/leanprover-community/mathlib/pull/7949) presumably because the `res` name wasn't discoverable.
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \- *lemma* subalgebra.mem_res
- \+ *lemma* subalgebra.mem_restrict_scalars
- \- *def* subalgebra.res
- \- *lemma* subalgebra.res_inj
- \- *lemma* subalgebra.res_top
- \+/\- *def* subalgebra.restrict_scalars
- \+ *lemma* subalgebra.restrict_scalars_injective
- \+ *lemma* subalgebra.restrict_scalars_to_submodule
- \+ *lemma* subalgebra.restrict_scalars_top

Modified src/field_theory/normal.lean


Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebra_tower.lean
- \- *lemma* algebra.adjoin_res
- \+ *lemma* algebra.adjoin_restrict_scalars



## [2021-09-18 06:53:42](https://github.com/leanprover-community/mathlib/commit/5e58247)
feat(algebra/ordered_pi): ordered_comm_monoid and canonically_ordered_monoid instances ([#9194](https://github.com/leanprover-community/mathlib/pull/9194))
Presumably these instances were missing because they were not actually constructible until we fixed the definition of `ordered_monoid` in [#8877](https://github.com/leanprover-community/mathlib/pull/8877)!
#### Estimated changes
Modified src/algebra/ordered_pi.lean




## [2021-09-18 02:27:19](https://github.com/leanprover-community/mathlib/commit/0bdd47f)
feat(data/list/basic): add lemmas about list.take list.drop ([#9245](https://github.com/leanprover-community/mathlib/pull/9245))
I added these lemmas about list.take and list.drop, which are present in Coq for example. Note that they are not entirely equivalent to list.take_append and list.drop_append because they also handle the case when `n ≤ l₁.length`
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.drop_append_eq_append_drop
- \+/\- *lemma* list.drop_append_of_le_length
- \+ *lemma* list.take_append_eq_append_take
- \+/\- *lemma* list.take_append_of_le_length



## [2021-09-18 02:27:17](https://github.com/leanprover-community/mathlib/commit/a8f2bab)
chore(set_theory/cardinal): use notation `#`, add notation `ω` ([#9217](https://github.com/leanprover-community/mathlib/pull/9217))
The only API change: rename `cardinal.eq_congr` to `cardinal.mk_congr`.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean
- \+/\- *lemma* two_le_mk_bcubes

Modified src/category_theory/limits/small_complete.lean


Modified src/data/rat/denumerable.lean
- \+/\- *lemma* cardinal.mk_rat

Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/index.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_span_le

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* finsupp.dim_eq

Modified src/linear_algebra/linear_independent.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.add_def
- \+/\- *theorem* cardinal.add_lt_omega
- \+/\- *lemma* cardinal.add_lt_omega_iff
- \+/\- *lemma* cardinal.cast_to_nat_of_lt_omega
- \+/\- *lemma* cardinal.cast_to_nat_of_omega_le
- \+/\- *lemma* cardinal.countable_iff
- \+/\- *lemma* cardinal.denumerable_iff
- \+/\- *lemma* cardinal.eq_zero_iff_is_empty
- \+/\- *lemma* cardinal.eq_zero_of_is_empty
- \+/\- *lemma* cardinal.finset_card
- \+/\- *lemma* cardinal.finset_card_lt_omega
- \+/\- *theorem* cardinal.fintype_card
- \+/\- *theorem* cardinal.infinite_iff
- \+/\- *theorem* cardinal.le_def
- \+/\- *theorem* cardinal.le_one_iff_subsingleton
- \+/\- *theorem* cardinal.lift_mk
- \+/\- *theorem* cardinal.lift_mk_fin
- \+/\- *theorem* cardinal.lift_omega
- \+/\- *theorem* cardinal.lt_omega
- \+/\- *theorem* cardinal.lt_omega_iff_finite
- \+/\- *theorem* cardinal.lt_omega_iff_fintype
- \+/\- *theorem* cardinal.mk_Prop
- \+/\- *theorem* cardinal.mk_Union_le_sum_mk
- \+/\- *theorem* cardinal.mk_bool
- \+/\- *theorem* cardinal.mk_def
- \+/\- *theorem* cardinal.mk_empty
- \+/\- *theorem* cardinal.mk_emptyc
- \+/\- *lemma* cardinal.mk_emptyc_iff
- \+/\- *theorem* cardinal.mk_fin
- \+/\- *theorem* cardinal.mk_image_le
- \+/\- *lemma* cardinal.mk_int
- \+/\- *lemma* cardinal.mk_le_mk_of_subset
- \+/\- *theorem* cardinal.mk_le_of_injective
- \+/\- *theorem* cardinal.mk_le_of_surjective
- \+/\- *theorem* cardinal.mk_list_eq_sum_pow
- \+/\- *lemma* cardinal.mk_nat
- \+/\- *theorem* cardinal.mk_option
- \+/\- *theorem* cardinal.mk_out
- \+/\- *theorem* cardinal.mk_pempty
- \+/\- *theorem* cardinal.mk_plift_of_false
- \+/\- *theorem* cardinal.mk_plift_of_true
- \+/\- *lemma* cardinal.mk_pnat
- \+/\- *theorem* cardinal.mk_punit
- \+/\- *theorem* cardinal.mk_quot_le
- \+/\- *theorem* cardinal.mk_quotient_le
- \+/\- *lemma* cardinal.mk_range_eq
- \+/\- *theorem* cardinal.mk_range_le
- \+/\- *lemma* cardinal.mk_sep
- \+/\- *theorem* cardinal.mk_set
- \+/\- *lemma* cardinal.mk_set_le
- \+/\- *theorem* cardinal.mk_singleton
- \+/\- *theorem* cardinal.mk_subtype_le
- \+/\- *lemma* cardinal.mk_subtype_mono
- \+/\- *lemma* cardinal.mk_to_enat_eq_coe_card
- \+/\- *lemma* cardinal.mk_to_enat_of_infinite
- \+/\- *lemma* cardinal.mk_to_nat_eq_card
- \+/\- *lemma* cardinal.mk_to_nat_of_infinite
- \+/\- *lemma* cardinal.mk_union_le
- \+/\- *theorem* cardinal.mk_unit
- \+/\- *theorem* cardinal.mk_univ
- \+/\- *theorem* cardinal.mul_def
- \+/\- *theorem* cardinal.mul_lt_omega
- \+/\- *lemma* cardinal.mul_lt_omega_iff
- \+/\- *theorem* cardinal.nat_lt_omega
- \+/\- *theorem* cardinal.ne_zero_iff_nonempty
- \+/\- *def* cardinal.omega
- \+/\- *theorem* cardinal.omega_le
- \+/\- *theorem* cardinal.omega_ne_zero
- \+/\- *theorem* cardinal.omega_pos
- \+/\- *theorem* cardinal.one_lt_iff_nontrivial
- \+/\- *theorem* cardinal.one_lt_omega
- \+/\- *theorem* cardinal.power_def
- \+/\- *theorem* cardinal.power_lt_omega
- \+/\- *def* cardinal.prod
- \+/\- *theorem* cardinal.prod_const
- \+/\- *theorem* cardinal.prod_mk
- \+/\- *theorem* cardinal.prop_eq_two
- \+/\- *theorem* cardinal.sum_const
- \+/\- *theorem* cardinal.sum_le_sup
- \+/\- *theorem* cardinal.sum_mk
- \+/\- *lemma* cardinal.to_enat_apply_of_lt_omega
- \+/\- *lemma* cardinal.to_enat_apply_of_omega_le
- \+/\- *lemma* cardinal.to_nat_apply_of_lt_omega
- \+/\- *lemma* cardinal.to_nat_apply_of_omega_le
- \+/\- *lemma* cardinal.two_le_iff'
- \+/\- *lemma* cardinal.two_le_iff
- \- *lemma* equiv.cardinal_eq

Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \+/\- *theorem* cardinal.mk_cardinal
- \+/\- *theorem* cardinal.mk_finset_eq_mk
- \+/\- *theorem* cardinal.mk_list_eq_mk

Modified src/set_theory/cofinality.lean
- \+/\- *theorem* cardinal.lt_cof_power
- \+/\- *theorem* cardinal.lt_power_cof
- \+/\- *theorem* cardinal.omega_is_regular
- \+/\- *theorem* cardinal.succ_is_regular
- \+/\- *theorem* ordinal.cof_omega
- \+/\- *theorem* ordinal.infinite_pigeonhole
- \+/\- *theorem* ordinal.infinite_pigeonhole_card
- \+/\- *theorem* ordinal.lt_cof_type
- \+/\- *theorem* ordinal.omega_le_cof
- \+/\- *theorem* ordinal.sup_lt
- \+/\- *theorem* ordinal.sup_lt_ord

Modified src/set_theory/ordinal.lean
- \+/\- *lemma* cardinal.mk_ord_out
- \+/\- *lemma* cardinal.ord_eq_min
- \+/\- *theorem* cardinal.ord_le_type
- \+/\- *def* cardinal.univ
- \+/\- *theorem* cardinal.univ_id



## [2021-09-18 00:17:26](https://github.com/leanprover-community/mathlib/commit/ec9d520)
feat(order/filter,*): lemmas about `filter.ne_bot` ([#9234](https://github.com/leanprover-community/mathlib/pull/9234))
* add `prod.range_fst`, `prod.range_snd`, `set.range_eval`;
* add `function.surjective_eval`;
* add `filter.*_ne_bot` and/or `filter.*_ne_bot_iff` lemmas for `sup`, `supr`,
  `comap prod.fst _`, `comap prod.snd _`, `coprod`, `Coprod`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* prod.range_fst
- \+ *theorem* prod.range_snd
- \+ *theorem* set.range_eval

Modified src/logic/function/basic.lean
- \+ *lemma* function.surjective_eval

Modified src/order/filter/basic.lean
- \+ *lemma* filter.Coprod_ne_bot
- \+ *lemma* filter.Coprod_ne_bot_iff'
- \+ *lemma* filter.Coprod_ne_bot_iff
- \+ *lemma* filter.comap_eval_ne_bot
- \+ *lemma* filter.comap_eval_ne_bot_iff'
- \+ *lemma* filter.comap_eval_ne_bot_iff
- \+ *lemma* filter.comap_fst_ne_bot
- \+ *lemma* filter.comap_fst_ne_bot_iff
- \+ *lemma* filter.comap_snd_ne_bot
- \+ *lemma* filter.comap_snd_ne_bot_iff
- \+ *lemma* filter.coprod_ne_bot_iff
- \+ *lemma* filter.coprod_ne_bot_left
- \+ *lemma* filter.coprod_ne_bot_right
- \+ *lemma* filter.ne_bot.Coprod
- \+ *lemma* filter.sup_ne_bot
- \+ *lemma* filter.supr_ne_bot



## [2021-09-17 20:09:59](https://github.com/leanprover-community/mathlib/commit/a80e1d7)
chore(topology/metric_space): split `iff` into 2 lemmas ([#9238](https://github.com/leanprover-community/mathlib/pull/9238))
One of the implications of `compact_iff_closed_bounded` doesn't need `t2_space`. Also add `compact_space_iff_bounded_univ`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.compact_space_iff_bounded_univ
- \+ *lemma* metric.is_compact_of_is_closed_bounded



## [2021-09-17 20:09:58](https://github.com/leanprover-community/mathlib/commit/c42a9ad)
chore(data/finsupp/basic): lemmas about sub and neg on filter and erase ([#9228](https://github.com/leanprover-community/mathlib/pull/9228))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.erase_add_hom
- \+ *lemma* finsupp.erase_neg
- \+ *lemma* finsupp.erase_sub
- \+ *lemma* finsupp.filter_neg
- \+ *lemma* finsupp.filter_sub



## [2021-09-17 20:09:57](https://github.com/leanprover-community/mathlib/commit/54217b6)
chore(data/list): make separate lexicographic file ([#9193](https://github.com/leanprover-community/mathlib/pull/9193))
A minor effort to reduce the `data.list.basic` monolithic, today inspired by yet again being annoyed that I couldn't find something.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *theorem* decidable.list.lex.ne_iff
- \- *theorem* list.lex.append_left
- \- *theorem* list.lex.append_right
- \- *theorem* list.lex.cons_iff
- \- *theorem* list.lex.imp
- \- *theorem* list.lex.ne_iff
- \- *theorem* list.lex.not_nil_right
- \- *theorem* list.lex.to_ne
- \- *theorem* list.nil_lt_cons

Added src/data/list/lex.lean
- \+ *theorem* decidable.list.lex.ne_iff
- \+ *theorem* list.lex.append_left
- \+ *theorem* list.lex.append_right
- \+ *theorem* list.lex.cons_iff
- \+ *theorem* list.lex.imp
- \+ *theorem* list.lex.ne_iff
- \+ *theorem* list.lex.not_nil_right
- \+ *theorem* list.lex.to_ne
- \+ *theorem* list.nil_lt_cons

Modified src/data/list/pairwise.lean


Modified src/data/string/basic.lean


Modified src/order/lexicographic.lean




## [2021-09-17 20:09:56](https://github.com/leanprover-community/mathlib/commit/696db1e)
feat(analysis/convex/topology): add lemma `convex.subset_interior_image_homothety_of_one_lt` ([#9044](https://github.com/leanprover-community/mathlib/pull/9044))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.subset_interior_image_homothety_of_one_lt

Modified src/topology/algebra/affine.lean
- \+ *lemma* affine_map.homothety_continuous
- \+ *lemma* affine_map.homothety_is_open_map



## [2021-09-17 16:23:57](https://github.com/leanprover-community/mathlib/commit/58f26a0)
chore(order/bounded_lattice): trivial generalizations ([#9246](https://github.com/leanprover-community/mathlib/pull/9246))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_bot.coe_le
- \+/\- *lemma* with_bot.coe_lt_coe
- \+/\- *theorem* with_top.coe_le_coe
- \+/\- *lemma* with_top.coe_lt_coe
- \+/\- *theorem* with_top.coe_lt_iff
- \+/\- *lemma* with_top.coe_lt_top
- \+/\- *theorem* with_top.le_coe
- \+/\- *lemma* with_top.not_top_le_coe



## [2021-09-17 14:39:08](https://github.com/leanprover-community/mathlib/commit/dfd4bf5)
split(analysis/convex/function): move `convex_on` and `concave_on` to their own file ([#9247](https://github.com/leanprover-community/mathlib/pull/9247))
Convex/concave functions now earn their own file. This cuts down `analysis.convex.basic` by 500 lines.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \- *lemma* concave_on.add
- \- *lemma* concave_on.comp_affine_map
- \- *lemma* concave_on.comp_linear_map
- \- *lemma* concave_on.concave_le
- \- *lemma* concave_on.convex_hypograph
- \- *lemma* concave_on.convex_lt
- \- *lemma* concave_on.inf
- \- *lemma* concave_on.le_on_segment'
- \- *lemma* concave_on.le_on_segment
- \- *lemma* concave_on.le_right_of_left_le'
- \- *lemma* concave_on.le_right_of_left_le
- \- *lemma* concave_on.left_le_of_le_right'
- \- *lemma* concave_on.left_le_of_le_right
- \- *lemma* concave_on.slope_mono_adjacent
- \- *lemma* concave_on.smul
- \- *lemma* concave_on.subset
- \- *lemma* concave_on.translate_left
- \- *lemma* concave_on.translate_right
- \- *def* concave_on
- \- *lemma* concave_on_const
- \- *lemma* concave_on_id
- \- *lemma* concave_on_iff_convex_hypograph
- \- *lemma* concave_on_iff_div
- \- *lemma* concave_on_real_iff_slope_mono_adjacent
- \- *lemma* concave_on_real_of_slope_mono_adjacent
- \- *lemma* convex_on.add
- \- *lemma* convex_on.comp_affine_map
- \- *lemma* convex_on.comp_linear_map
- \- *lemma* convex_on.convex_epigraph
- \- *lemma* convex_on.convex_le
- \- *lemma* convex_on.convex_lt
- \- *lemma* convex_on.le_left_of_right_le'
- \- *lemma* convex_on.le_left_of_right_le
- \- *lemma* convex_on.le_on_segment'
- \- *lemma* convex_on.le_on_segment
- \- *lemma* convex_on.le_right_of_left_le'
- \- *lemma* convex_on.le_right_of_left_le
- \- *lemma* convex_on.slope_mono_adjacent
- \- *lemma* convex_on.smul
- \- *lemma* convex_on.subset
- \- *lemma* convex_on.sup
- \- *lemma* convex_on.translate_left
- \- *lemma* convex_on.translate_right
- \- *def* convex_on
- \- *lemma* convex_on_const
- \- *lemma* convex_on_id
- \- *lemma* convex_on_iff_convex_epigraph
- \- *lemma* convex_on_iff_div
- \- *lemma* convex_on_real_iff_slope_mono_adjacent
- \- *lemma* convex_on_real_of_slope_mono_adjacent
- \- *lemma* linear_map.concave_on
- \- *lemma* linear_map.convex_on
- \- *lemma* linear_order.concave_on_of_lt
- \- *lemma* linear_order.convex_on_of_lt
- \- *lemma* neg_concave_on_iff
- \- *lemma* neg_convex_on_iff

Modified src/analysis/convex/combination.lean
- \- *lemma* convex_on.exists_ge_of_center_mass
- \- *lemma* convex_on.exists_ge_of_mem_convex_hull
- \- *lemma* convex_on.map_center_mass_le
- \- *lemma* convex_on.map_sum_le

Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/extrema.lean


Added src/analysis/convex/function.lean
- \+ *lemma* concave_on.add
- \+ *lemma* concave_on.comp_affine_map
- \+ *lemma* concave_on.comp_linear_map
- \+ *lemma* concave_on.concave_le
- \+ *lemma* concave_on.convex_hypograph
- \+ *lemma* concave_on.convex_lt
- \+ *lemma* concave_on.inf
- \+ *lemma* concave_on.le_on_segment'
- \+ *lemma* concave_on.le_on_segment
- \+ *lemma* concave_on.le_right_of_left_le'
- \+ *lemma* concave_on.le_right_of_left_le
- \+ *lemma* concave_on.left_le_of_le_right'
- \+ *lemma* concave_on.left_le_of_le_right
- \+ *lemma* concave_on.slope_mono_adjacent
- \+ *lemma* concave_on.smul
- \+ *lemma* concave_on.subset
- \+ *lemma* concave_on.translate_left
- \+ *lemma* concave_on.translate_right
- \+ *def* concave_on
- \+ *lemma* concave_on_const
- \+ *lemma* concave_on_id
- \+ *lemma* concave_on_iff_convex_hypograph
- \+ *lemma* concave_on_iff_div
- \+ *lemma* concave_on_real_iff_slope_mono_adjacent
- \+ *lemma* concave_on_real_of_slope_mono_adjacent
- \+ *lemma* convex_on.add
- \+ *lemma* convex_on.comp_affine_map
- \+ *lemma* convex_on.comp_linear_map
- \+ *lemma* convex_on.convex_epigraph
- \+ *lemma* convex_on.convex_le
- \+ *lemma* convex_on.convex_lt
- \+ *lemma* convex_on.exists_ge_of_center_mass
- \+ *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+ *lemma* convex_on.le_left_of_right_le'
- \+ *lemma* convex_on.le_left_of_right_le
- \+ *lemma* convex_on.le_on_segment'
- \+ *lemma* convex_on.le_on_segment
- \+ *lemma* convex_on.le_right_of_left_le'
- \+ *lemma* convex_on.le_right_of_left_le
- \+ *lemma* convex_on.map_center_mass_le
- \+ *lemma* convex_on.map_sum_le
- \+ *lemma* convex_on.slope_mono_adjacent
- \+ *lemma* convex_on.smul
- \+ *lemma* convex_on.subset
- \+ *lemma* convex_on.sup
- \+ *lemma* convex_on.translate_left
- \+ *lemma* convex_on.translate_right
- \+ *def* convex_on
- \+ *lemma* convex_on_const
- \+ *lemma* convex_on_id
- \+ *lemma* convex_on_iff_convex_epigraph
- \+ *lemma* convex_on_iff_div
- \+ *lemma* convex_on_real_iff_slope_mono_adjacent
- \+ *lemma* convex_on_real_of_slope_mono_adjacent
- \+ *lemma* linear_map.concave_on
- \+ *lemma* linear_map.convex_on
- \+ *lemma* linear_order.concave_on_of_lt
- \+ *lemma* linear_order.convex_on_of_lt
- \+ *lemma* neg_concave_on_iff
- \+ *lemma* neg_convex_on_iff

Modified src/analysis/convex/integral.lean


Modified src/analysis/convex/topology.lean


Modified src/linear_algebra/affine_space/ordered.lean




## [2021-09-17 12:18:09](https://github.com/leanprover-community/mathlib/commit/5f140ab)
chore(*): rename `coe_fn_inj` to `coe_fn_injective` ([#9241](https://github.com/leanprover-community/mathlib/pull/9241))
This also removes some comments about it not being possible to use `function.injective`, since now we use it without problem.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *theorem* alg_hom.coe_fn_inj
- \+ *theorem* alg_hom.coe_fn_injective

Modified src/algebra/category/Algebra/limits.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* affine_equiv.coe_fn_injective

Modified src/order/rel_iso.lean
- \- *theorem* rel_embedding.coe_fn_inj
- \+ *theorem* rel_embedding.coe_fn_injective
- \- *theorem* rel_hom.coe_fn_inj
- \+ *theorem* rel_hom.coe_fn_injective

Modified src/set_theory/ordinal.lean




## [2021-09-17 09:52:16](https://github.com/leanprover-community/mathlib/commit/5b75f5a)
chore(algebra/group/basic): add `ite_one_mul` and `ite_zero_add` ([#9227](https://github.com/leanprover-community/mathlib/pull/9227))
We already had the versions with the arguments in the other order.
Follows on from [#3217](https://github.com/leanprover-community/mathlib/pull/3217)
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* ite_one_mul



## [2021-09-17 09:00:53](https://github.com/leanprover-community/mathlib/commit/18d031d)
fix(ring_theory/dedekind_domain): Speed up ideal.unique_factorization_monoid ([#9243](https://github.com/leanprover-community/mathlib/pull/9243))
The old proof was causing timeouts in CI.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeouts.20in.20ring_theory.2Fdedekind_domain.2Elean.3A664.3A9/near/253579691)
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean




## [2021-09-17 06:22:56](https://github.com/leanprover-community/mathlib/commit/15bf066)
feat(measure_theory/function/l1_space): add integrability lemmas for composition with `to_real` ([#9199](https://github.com/leanprover-community/mathlib/pull/9199))
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.has_finite_integral_to_real_of_lintegral_ne_top
- \+ *lemma* measure_theory.integrable_to_real_of_lintegral_ne_top
- \+ *lemma* measure_theory.mem_ℒ1_to_real_of_lintegral_ne_top

Modified src/measure_theory/measure/with_density_vector_measure.lean
- \+ *lemma* measure_theory.with_densityᵥ_add'
- \+ *lemma* measure_theory.with_densityᵥ_neg'
- \+ *lemma* measure_theory.with_densityᵥ_smul'
- \+ *lemma* measure_theory.with_densityᵥ_sub'
- \+ *lemma* measure_theory.with_densityᵥ_to_real



## [2021-09-16 19:59:45](https://github.com/leanprover-community/mathlib/commit/59cda6d)
feat(measure_theory/group/basic): introduce a class is_haar_measure, and its basic properties ([#9142](https://github.com/leanprover-community/mathlib/pull/9142))
We have in mathlib a construction of Haar measures. But there are many measures which do not come from this construction, and are still Haar measures (Lebesgue measure on a vector space, Hausdorff measure of the right dimension, for instance). We introduce a new class `is_haar_measure` (and its additive analogue) to be able to express facts simultaneously for all these measures, and prove their basic properties.
#### Estimated changes
Modified src/measure_theory/group/basic.lean
- \+ *lemma* is_compact.haar_lt_top
- \+ *lemma* is_open.haar_pos
- \+ *lemma* measure_theory.is_mul_left_invariant.measure_lt_top_of_is_compact'
- \+ *lemma* measure_theory.is_mul_left_invariant.measure_lt_top_of_is_compact
- \+ *lemma* measure_theory.is_mul_left_invariant.measure_pos_of_is_open
- \+ *lemma* measure_theory.is_mul_left_invariant.measure_preimage_mul
- \+/\- *lemma* measure_theory.is_mul_left_invariant.null_iff_empty
- \+ *lemma* measure_theory.is_mul_left_invariant.smul
- \+ *lemma* measure_theory.is_mul_right_invariant.smul
- \+ *lemma* measure_theory.measure.haar_pos_of_nonempty_interior
- \+ *lemma* measure_theory.measure.haar_preimage_mul
- \+ *lemma* measure_theory.measure.haar_preimage_mul_right
- \+ *lemma* measure_theory.measure.haar_singleton
- \+ *lemma* measure_theory.measure.is_haar_measure.smul
- \+ *lemma* measure_theory.measure.is_haar_measure_map
- \+ *lemma* measure_theory.measure.is_haar_measure_of_is_compact_nonempty_interior
- \+ *lemma* measure_theory.measure.is_mul_left_invariant_haar

Modified src/topology/separation.lean
- \+ *lemma* finite.is_closed
- \+ *lemma* infinite_of_mem_nhds



## [2021-09-16 16:02:06](https://github.com/leanprover-community/mathlib/commit/76f87b7)
feat(group_theory/group_action/basic): Action on an orbit ([#9220](https://github.com/leanprover-community/mathlib/pull/9220))
A `mul_action` restricts to a `mul_action` on an orbit.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.orbit.coe_smul



## [2021-09-16 13:26:32](https://github.com/leanprover-community/mathlib/commit/ca38357)
feat(group_theory/group_action): add `distrib_mul_action.to_add_aut` and `mul_distrib_mul_action.to_mul_aut` ([#9224](https://github.com/leanprover-community/mathlib/pull/9224))
These can be used to golf the existing `mul_aut_arrow`.
This also moves some definitions out of `algebra/group_ring_action.lean` into a more appropriate file.
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \- *def* distrib_mul_action.to_add_equiv
- \- *def* mul_distrib_mul_action.to_mul_equiv

Modified src/algebra/module/linear_map.lean


Modified src/group_theory/group_action/group.lean
- \+ *def* arrow_mul_distrib_mul_action
- \+ *def* distrib_mul_action.to_add_aut
- \+ *def* distrib_mul_action.to_add_equiv
- \+/\- *def* mul_aut_arrow
- \+ *def* mul_distrib_mul_action.to_mul_aut
- \+ *def* mul_distrib_mul_action.to_mul_equiv



## [2021-09-16 13:26:31](https://github.com/leanprover-community/mathlib/commit/17a473e)
feat(group_theory/p_group): Sup of p-subgroups is a p-subgroup ([#9222](https://github.com/leanprover-community/mathlib/pull/9222))
The sup of p-subgroups is a p-subgroup, assuming normality.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+/\- *lemma* is_p_group.to_inf_left
- \+/\- *lemma* is_p_group.to_inf_right
- \+ *lemma* is_p_group.to_sup_of_normal_left'
- \+ *lemma* is_p_group.to_sup_of_normal_left
- \+ *lemma* is_p_group.to_sup_of_normal_right'
- \+ *lemma* is_p_group.to_sup_of_normal_right



## [2021-09-16 13:26:30](https://github.com/leanprover-community/mathlib/commit/b0d961b)
chore(algebra/indicator_function): add `finset.sum_indicator_eq_sum_filter` ([#9208](https://github.com/leanprover-community/mathlib/pull/9208))
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* finset.prod_mul_indicator_eq_prod_filter
- \+ *lemma* set.indicator_smul_apply



## [2021-09-16 13:26:29](https://github.com/leanprover-community/mathlib/commit/fdfe782)
feat(combinatorics/derangements/*): add lemmas about counting derangements ([#9089](https://github.com/leanprover-community/mathlib/pull/9089))
This defines `card_derangements` as the cardinality of the set of derangements of a fintype, and `num_derangements` as a function from N to N, and proves their equality, along with some other lemmas.
Context: PR [#7526](https://github.com/leanprover-community/mathlib/pull/7526) grew too large and had to be split in half. The first half retained the original PR ID, and this is the second half. This adds back the finite.lean and exponential.lean files. Also, added entries back to 100.yaml.
#### Estimated changes
Modified docs/100.yaml


Added src/combinatorics/derangements/exponential.lean
- \+ *theorem* num_derangements_tendsto_inv_e

Added src/combinatorics/derangements/finite.lean
- \+ *lemma* card_derangements_eq_num_derangements
- \+ *lemma* card_derangements_fin_add_two
- \+ *lemma* card_derangements_fin_eq_num_derangements
- \+ *lemma* card_derangements_invariant
- \+ *def* num_derangements
- \+ *lemma* num_derangements_add_two
- \+ *lemma* num_derangements_one
- \+ *lemma* num_derangements_succ
- \+ *theorem* num_derangements_sum
- \+ *lemma* num_derangements_zero



## [2021-09-16 13:26:27](https://github.com/leanprover-community/mathlib/commit/89b0cfb)
refactor(analysis/convex/basic): generalize convexity to vector spaces ([#9058](https://github.com/leanprover-community/mathlib/pull/9058))
`convex` and `convex_hull` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary ordered_semirings in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid` where possible.
#### Estimated changes
Modified src/analysis/calculus/darboux.lean
- \+/\- *theorem* convex_image_has_deriv_at
- \+/\- *theorem* deriv_forall_lt_or_forall_gt_of_forall_ne

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* concave_on_of_deriv2_nonpos
- \+/\- *theorem* concave_on_of_deriv_antimono
- \+/\- *theorem* concave_on_open_of_deriv2_nonpos
- \+/\- *theorem* convex.antimono_of_deriv_nonpos
- \+/\- *theorem* convex.image_sub_le_mul_sub_of_deriv_le
- \+/\- *theorem* convex.image_sub_lt_mul_sub_of_deriv_lt
- \+/\- *theorem* convex.is_const_of_fderiv_within_eq_zero
- \+/\- *theorem* convex.mono_of_deriv_nonneg
- \+/\- *theorem* convex.mul_sub_le_image_sub_of_le_deriv
- \+/\- *theorem* convex.mul_sub_lt_image_sub_of_lt_deriv
- \+/\- *theorem* convex.strict_antimono_of_deriv_neg
- \+/\- *theorem* convex.strict_mono_of_deriv_pos
- \+/\- *theorem* convex_on_of_deriv2_nonneg
- \+/\- *theorem* convex_on_of_deriv_mono
- \+/\- *theorem* convex_on_open_of_deriv2_nonneg

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *theorem* unique_diff_on_convex

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* affine_map.image_convex_hull
- \+/\- *lemma* concave_on_const
- \+/\- *lemma* concave_on_id
- \+/\- *lemma* concave_on_real_iff_slope_mono_adjacent
- \+/\- *lemma* concave_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex.add
- \+/\- *lemma* convex.add_smul
- \+/\- *lemma* convex.add_smul_mem
- \+/\- *lemma* convex.add_smul_sub_mem
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.affinity
- \+/\- *lemma* convex.combo_affine_apply
- \+ *lemma* convex.combo_eq_vadd
- \- *lemma* convex.combo_to_vadd
- \+/\- *lemma* convex.convex_hull_eq
- \+/\- *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \+/\- *lemma* convex.inter
- \+/\- *lemma* convex.is_linear_image
- \+/\- *lemma* convex.is_linear_preimage
- \+/\- *lemma* convex.linear_image
- \+/\- *lemma* convex.linear_preimage
- \+/\- *lemma* convex.mem_smul_of_zero_mem
- \+/\- *lemma* convex.neg
- \+/\- *lemma* convex.neg_preimage
- \+/\- *lemma* convex.open_segment_subset
- \+/\- *lemma* convex.prod
- \+/\- *lemma* convex.segment_subset
- \+/\- *lemma* convex.smul
- \+/\- *lemma* convex.smul_mem_of_zero_mem
- \+/\- *lemma* convex.smul_preimage
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex.translate
- \+/\- *lemma* convex.translate_preimage_left
- \+/\- *lemma* convex.translate_preimage_right
- \+/\- *lemma* convex_Icc
- \+/\- *lemma* convex_Ici
- \+/\- *lemma* convex_Ico
- \+/\- *lemma* convex_Iic
- \+/\- *lemma* convex_Iio
- \+/\- *lemma* convex_Inter
- \+/\- *lemma* convex_Ioc
- \+/\- *lemma* convex_Ioi
- \+/\- *lemma* convex_Ioo
- \+/\- *lemma* convex_convex_hull
- \+/\- *lemma* convex_empty
- \+/\- *lemma* convex_halfspace_ge
- \+/\- *lemma* convex_halfspace_gt
- \+ *lemma* convex_halfspace_im_ge
- \+/\- *lemma* convex_halfspace_im_gt
- \+/\- *lemma* convex_halfspace_im_le
- \- *lemma* convex_halfspace_im_lge
- \+/\- *lemma* convex_halfspace_im_lt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_lt
- \+ *lemma* convex_halfspace_re_ge
- \+/\- *lemma* convex_halfspace_re_gt
- \+/\- *lemma* convex_halfspace_re_le
- \- *lemma* convex_halfspace_re_lge
- \+/\- *lemma* convex_halfspace_re_lt
- \+/\- *lemma* convex_hull_min
- \+/\- *lemma* convex_hull_mono
- \+/\- *lemma* convex_hull_singleton
- \+/\- *lemma* convex_hyperplane
- \- *lemma* convex_iff_div:
- \+ *lemma* convex_iff_div
- \+ *lemma* convex_iff_ord_connected
- \- *lemma* convex_iff_pointwise_add_subset:
- \+ *lemma* convex_iff_pointwise_add_subset
- \+/\- *lemma* convex_interval
- \+/\- *lemma* convex_on_const
- \+/\- *lemma* convex_on_id
- \+/\- *lemma* convex_on_real_iff_slope_mono_adjacent
- \+/\- *lemma* convex_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex_open_segment
- \+/\- *lemma* convex_sInter
- \+/\- *lemma* convex_segment
- \+/\- *lemma* convex_singleton
- \+/\- *lemma* convex_std_simplex
- \+/\- *lemma* convex_univ
- \+/\- *lemma* is_linear_map.convex_hull_image
- \+/\- *lemma* is_linear_map.image_convex_hull
- \+/\- *lemma* linear_map.concave_on
- \+/\- *lemma* linear_map.convex_hull_image
- \+/\- *lemma* linear_map.convex_on
- \+/\- *lemma* linear_map.image_convex_hull
- \+/\- *lemma* linear_order.concave_on_of_lt
- \+/\- *lemma* linear_order.convex_on_of_lt
- \- *lemma* real.convex_iff_ord_connected
- \+ *lemma* set.ord_connected.convex
- \+ *lemma* set.ord_connected.convex_of_chain
- \+/\- *lemma* submodule.convex
- \+/\- *lemma* subset_convex_hull
- \+/\- *lemma* subspace.convex

Modified src/analysis/convex/caratheodory.lean
- \+/\- *theorem* eq_pos_convex_span_of_mem_convex_hull

Modified src/analysis/convex/combination.lean
- \+/\- *lemma* convex.center_mass_mem
- \+/\- *lemma* convex.sum_mem
- \+/\- *lemma* convex_on.exists_ge_of_mem_convex_hull

Modified src/analysis/convex/cone.lean
- \+/\- *def* convex.to_cone
- \+/\- *lemma* convex_cone.convex

Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/extrema.lean
- \+/\- *lemma* is_min_on.of_is_local_min_on_of_convex_on_Icc

Modified src/analysis/convex/extreme.lean
- \+/\- *lemma* convex.mem_extreme_points_iff_convex_remove
- \+/\- *lemma* convex.mem_extreme_points_iff_mem_diff_convex_hull_remove
- \+/\- *lemma* is_extreme.convex_diff

Modified src/analysis/convex/independent.lean
- \+/\- *lemma* convex.extreme_points_convex_independent
- \+/\- *lemma* convex_independent_iff_finset

Modified src/analysis/convex/integral.lean
- \+/\- *lemma* convex.integral_mem

Modified src/analysis/convex/topology.lean
- \+/\- *lemma* convex.add_smul_mem_interior
- \+/\- *lemma* convex.add_smul_sub_mem_interior
- \+/\- *lemma* convex.closure
- \+/\- *lemma* convex.interior
- \+/\- *lemma* convex.is_path_connected
- \+/\- *lemma* convex_ball
- \+/\- *lemma* convex_closed_ball
- \+/\- *lemma* convex_hull_exists_dist_ge
- \+/\- *lemma* convex_on_dist
- \+/\- *lemma* real.convex_iff_is_preconnected

Modified src/analysis/normed_space/inner_product.lean
- \+/\- *theorem* norm_eq_infi_iff_real_inner_le_zero

Modified src/data/set/intervals/ord_connected.lean


Modified src/measure_theory/measure/hausdorff.lean




## [2021-09-16 11:34:14](https://github.com/leanprover-community/mathlib/commit/f536b4f)
fix(group_theory/submonoid/operations): add missing `to_additive` tags on galois lemmas ([#9225](https://github.com/leanprover-community/mathlib/pull/9225))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean




## [2021-09-16 11:34:13](https://github.com/leanprover-community/mathlib/commit/8a1fc68)
feat(measure_theory/measure/with_density_vector_measure): `with_densityᵥ` of a real function equals the density of the pos part - density of the neg part ([#9215](https://github.com/leanprover-community/mathlib/pull/9215))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.of_real_le_ennnorm

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.is_finite_measure_with_density_of_real

Modified src/measure_theory/measure/with_density_vector_measure.lean
- \+ *lemma* measure_theory.with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part



## [2021-09-16 11:34:12](https://github.com/leanprover-community/mathlib/commit/232ff44)
feat(measure_theory/measure/measure_space): add mutually singular lemmas ([#9213](https://github.com/leanprover-community/mathlib/pull/9213))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.mutually_singular.add_iff
- \+ *lemma* measure_theory.measure.mutually_singular.of_absolutely_continuous



## [2021-09-16 11:34:11](https://github.com/leanprover-community/mathlib/commit/bc7cde8)
feat(data/dfinsupp): add `filter_ne_eq_erase` ([#9182](https://github.com/leanprover-community/mathlib/pull/9182))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.erase_add_single
- \+ *lemma* dfinsupp.filter_ne_eq_erase'
- \+ *lemma* dfinsupp.filter_ne_eq_erase
- \+/\- *lemma* dfinsupp.single_add_erase



## [2021-09-16 11:34:09](https://github.com/leanprover-community/mathlib/commit/86d20e5)
feat(data/dfinsupp): add arithmetic lemmas about filter ([#9175](https://github.com/leanprover-community/mathlib/pull/9175))
This adds `dfinsupp.filter_{zero,add,neg,sub,smul}` and `dfinsupp.subtype_domain_smul`, along with some bundled maps.
This also cleans up some variable explicitness.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.coe_smul
- \+ *lemma* dfinsupp.filter_add
- \+ *def* dfinsupp.filter_add_monoid_hom
- \+ *def* dfinsupp.filter_linear_map
- \+ *lemma* dfinsupp.filter_neg
- \+ *lemma* dfinsupp.filter_smul
- \+ *lemma* dfinsupp.filter_sub
- \+ *lemma* dfinsupp.filter_zero
- \+/\- *lemma* dfinsupp.mk_smul
- \+/\- *lemma* dfinsupp.single_smul
- \+/\- *lemma* dfinsupp.smul_apply
- \+ *def* dfinsupp.subtype_domain_linear_map
- \+ *lemma* dfinsupp.subtype_domain_smul

Modified src/linear_algebra/dfinsupp.lean




## [2021-09-16 10:37:03](https://github.com/leanprover-community/mathlib/commit/b759384)
feat(field_theory/algebraic_closure): map from algebraic extensions into the algebraic closure ([#9110](https://github.com/leanprover-community/mathlib/pull/9110))
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *theorem* is_alg_closed.exists_aeval_eq_zero
- \+ *theorem* is_alg_closed.exists_eval₂_eq_zero
- \+/\- *theorem* is_alg_closed.exists_root
- \+ *def* is_alg_closed.lift
- \+ *lemma* lift.subfield_with_hom.compat
- \+ *lemma* lift.subfield_with_hom.exists_maximal_subfield_with_hom
- \+ *lemma* lift.subfield_with_hom.le_def
- \+ *def* lift.subfield_with_hom.maximal_subfield_with_hom
- \+ *lemma* lift.subfield_with_hom.maximal_subfield_with_hom_chain_bounded
- \+ *lemma* lift.subfield_with_hom.maximal_subfield_with_hom_eq_top
- \+ *lemma* lift.subfield_with_hom.maximal_subfield_with_hom_is_maximal

Modified src/ring_theory/algebraic.lean




## [2021-09-16 05:50:06](https://github.com/leanprover-community/mathlib/commit/18dc1a1)
feat(group_theory/p_group): p-groups are preserved by isomorphisms ([#9203](https://github.com/leanprover-community/mathlib/pull/9203))
Adds three lemmas about transporting `is_p_group` across injective, surjective, and bijective homomorphisms.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.of_equiv
- \+ *lemma* is_p_group.of_injective
- \+ *lemma* is_p_group.of_surjective



## [2021-09-15 23:41:53](https://github.com/leanprover-community/mathlib/commit/519b4e9)
chore(algebra/big_operators): move, golf ([#9218](https://github.com/leanprover-community/mathlib/pull/9218))
move 2 lemmas up and golf the proof of `finset.prod_subset`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean




## [2021-09-15 18:42:11](https://github.com/leanprover-community/mathlib/commit/2b589ca)
feat(group_theory/subgroup): Generalize `comap_sup_eq` ([#9212](https://github.com/leanprover-community/mathlib/pull/9212))
The lemma `comap_sup_eq` can be generalized from assuming `function.surjective f` to assuming `≤ f.range`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+/\- *lemma* subgroup.comap_sup_eq
- \+ *lemma* subgroup.comap_sup_eq_of_le_range
- \+ *lemma* subgroup.sup_subgroup_of_eq



## [2021-09-15 18:42:10](https://github.com/leanprover-community/mathlib/commit/8185637)
refactor(data/real/nnreal): use `has_ordered_sub` ([#9167](https://github.com/leanprover-community/mathlib/pull/9167))
* provide a `has_ordered_sub` instance for `nnreal`;
* drop most lemmas about subtraction in favor of lemmas from `algebra/ordered_sub`;
* add `mul_sub'` and `sub_mul'`;
* generalize some lemmas about `has_ordered_sub` to `has_add`;
* add `add_hom.mul_left` and `add_hom.mul_right`.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_sub'
- \+ *lemma* sub_mul'

Modified src/algebra/ordered_sub.lean
- \+ *lemma* add_hom.le_map_sub
- \+ *lemma* add_monoid_hom.le_map_sub
- \+ *lemma* le_mul_sub
- \+ *lemma* le_sub_mul
- \+ *lemma* order_iso.map_sub

Modified src/algebra/ring/basic.lean
- \+ *def* add_hom.mul_left
- \+ *def* add_hom.mul_right

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/data/bool.lean
- \+ *theorem* bool.cond_bnot

Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean
- \- *lemma* nnreal.add_sub_cancel'
- \- *lemma* nnreal.add_sub_cancel
- \- *lemma* nnreal.add_sub_eq_max
- \+ *lemma* nnreal.coe_sub_def
- \- *lemma* nnreal.lt_sub_iff_add_lt
- \- *lemma* nnreal.sub_add_cancel_of_le
- \- *lemma* nnreal.sub_add_eq_max
- \+ *lemma* nnreal.sub_div
- \- *lemma* nnreal.sub_eq_iff_eq_add
- \- *lemma* nnreal.sub_eq_zero
- \- *lemma* nnreal.sub_le_iff_le_add
- \- *lemma* nnreal.sub_le_self
- \- *lemma* nnreal.sub_lt_iff_lt_add
- \- *lemma* nnreal.sub_pos
- \- *lemma* nnreal.sub_self
- \- *lemma* nnreal.sub_sub_cancel_of_le
- \- *lemma* nnreal.sub_zero

Modified src/measure_theory/integral/lebesgue.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/metric_space/basic.lean




## [2021-09-15 18:42:09](https://github.com/leanprover-community/mathlib/commit/a4341f9)
refactor(data/set/finite): use a custom inductive type ([#9164](https://github.com/leanprover-community/mathlib/pull/9164))
Currently Lean treats local assumptions `h : finite s` as local instances, so one needs to do something like
```lean
  unfreezingI { lift s to finset α using hs },
```
I change the definition of `set.finite` to an inductive predicate that replicates the definition of `nonempty` and remove `unfreezingI` here and there. Equivalence to the old definition is given by `set.finite_def`.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean


Modified src/data/mv_polynomial/funext.lean


Modified src/data/set/finite.lean
- \- *def* set.finite
- \+ *lemma* set.finite_def

Modified src/field_theory/finiteness.lean


Modified src/field_theory/separable.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/basic.lean


Modified src/set_theory/cardinal.lean




## [2021-09-15 18:42:07](https://github.com/leanprover-community/mathlib/commit/244285c)
feat(linear_algebra/free_module): add instances ([#9087](https://github.com/leanprover-community/mathlib/pull/9087))
We add some `module.finite` instances. These are in the `linear_algebra/free_module.lean` files since they concern free modules.
From LTE
#### Estimated changes
Modified src/linear_algebra/free_module.lean
- \+ *lemma* module.finite.of_basis



## [2021-09-15 18:42:06](https://github.com/leanprover-community/mathlib/commit/bab7e99)
docs(data/part): add module docstring ([#8966](https://github.com/leanprover-community/mathlib/pull/8966))
#### Estimated changes
Modified src/data/part.lean
- \+/\- *theorem* part.dom_iff_mem
- \+/\- *lemma* part.ne_none_iff



## [2021-09-15 17:09:28](https://github.com/leanprover-community/mathlib/commit/b63c560)
feat(data/set/Union_lift): lift functions to Unions of sets ([#9019](https://github.com/leanprover-community/mathlib/pull/9019))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_supr_of_directed
- \+ *lemma* subalgebra.supr_lift_comp_inclusion
- \+ *lemma* subalgebra.supr_lift_inclusion
- \+ *lemma* subalgebra.supr_lift_mk
- \+ *lemma* subalgebra.supr_lift_of_mem

Added src/data/set/Union_lift.lean
- \+ *lemma* set.Union_lift_binary
- \+ *lemma* set.Union_lift_const
- \+ *lemma* set.Union_lift_inclusion
- \+ *lemma* set.Union_lift_mk
- \+ *lemma* set.Union_lift_of_mem
- \+ *lemma* set.Union_lift_unary
- \+ *lemma* set.lift_cover_coe
- \+ *lemma* set.lift_cover_of_mem



## [2021-09-15 15:40:39](https://github.com/leanprover-community/mathlib/commit/2597264)
chore(ring_theory/ideal/operations): golf a definition using new actions ([#9152](https://github.com/leanprover-community/mathlib/pull/9152))
This action can be expressed more directly in terms of other actions, without the unfolded definition changing.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean




## [2021-09-15 13:22:40](https://github.com/leanprover-community/mathlib/commit/3a6340c)
chore(data/dfinsupp): golf using `quotient.map` instead of `quotient.lift_on` ([#9176](https://github.com/leanprover-community/mathlib/pull/9176))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *def* dfinsupp.erase
- \+/\- *def* dfinsupp.filter
- \+/\- *def* dfinsupp.map_range
- \+/\- *def* dfinsupp.subtype_domain
- \+/\- *def* dfinsupp.zip_with



## [2021-09-15 13:22:39](https://github.com/leanprover-community/mathlib/commit/f8d8171)
refactor(logic/relator): turn *_unique and *_total into defs, not classes ([#9135](https://github.com/leanprover-community/mathlib/pull/9135))
We had (almost) no instances for these classes and (almost) no lemmas taking these assumptions as TC arguments.
#### Estimated changes
Modified src/computability/turing_machine.lean


Modified src/data/list/forall2.lean
- \- *lemma* list.bi_unique_forall₂
- \- *lemma* list.left_unique_forall₂
- \- *lemma* list.right_unique_forall₂
- \+ *lemma* relator.bi_unique.forall₂
- \+ *lemma* relator.left_unique.forall₂
- \+ *lemma* relator.right_unique.forall₂

Modified src/data/list/perm.lean


Modified src/data/option/basic.lean


Modified src/data/part.lean


Modified src/data/seq/computation.lean


Modified src/logic/relation.lean


Modified src/logic/relator.lean
- \+ *lemma* relator.bi_total.rel_exists
- \+ *lemma* relator.bi_total.rel_forall
- \+ *def* relator.bi_total
- \+ *lemma* relator.bi_total_eq
- \+ *def* relator.bi_unique
- \+ *lemma* relator.left_total.rel_exists
- \+ *def* relator.left_total
- \+ *lemma* relator.left_unique.flip
- \- *lemma* relator.left_unique.unique
- \+ *def* relator.left_unique
- \- *lemma* relator.left_unique_flip
- \- *lemma* relator.rel_exists_of_left_total
- \- *lemma* relator.rel_exists_of_total
- \- *lemma* relator.rel_forall_of_right_total
- \- *lemma* relator.rel_forall_of_total
- \+ *lemma* relator.right_total.rel_forall
- \+ *def* relator.right_total
- \- *lemma* relator.right_unique.unique
- \+ *def* relator.right_unique



## [2021-09-15 12:38:53](https://github.com/leanprover-community/mathlib/commit/f1bf7b8)
feat(category_theory/filtered): Special support for bowtie and tulip diagrams ([#9099](https://github.com/leanprover-community/mathlib/pull/9099))
Add special support for two kinds of diagram categories: The "bowtie" and the "tulip". These are convenient when proving that forgetful functors of algebraic categories preserve filtered colimits.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* category_theory.is_filtered.bowtie
- \+ *lemma* category_theory.is_filtered.coeq₃_condition₁
- \+ *lemma* category_theory.is_filtered.coeq₃_condition₂
- \+ *lemma* category_theory.is_filtered.coeq₃_condition₃
- \+ *lemma* category_theory.is_filtered.tulip



## [2021-09-15 10:33:05](https://github.com/leanprover-community/mathlib/commit/bb38ce9)
feat(ring_theory/artinian): is_nilpotent_jacobson ([#9153](https://github.com/leanprover-community/mathlib/pull/9153))
#### Estimated changes
Modified src/ring_theory/artinian.lean
- \+ *theorem* is_artinian.monotone_stabilizes
- \+ *theorem* is_artinian.set_has_minimal
- \+ *lemma* is_artinian_ring.is_nilpotent_jacobson_bot



## [2021-09-15 07:15:07](https://github.com/leanprover-community/mathlib/commit/85dc9f3)
refactor(measure_theory/measure): redefine `measure_theory.sigma_finite` ([#9207](https://github.com/leanprover-community/mathlib/pull/9207))
* don't require in the definition that covering sets are measurable;
* use `to_measurable` in `sigma_finite.out` to get measurable sets.
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/regular.lean




## [2021-09-15 06:12:44](https://github.com/leanprover-community/mathlib/commit/7492aa6)
refactor(measure_theory/integral/lebesgue): golf a proof ([#9206](https://github.com/leanprover-community/mathlib/pull/9206))
* add `exists_pos_tsum_mul_lt_of_encodable`;
* add `measure.spanning_sets_index` and lemmas about this definition;
* replace the proof of `exists_integrable_pos_of_sigma_finite` with a simpler one.
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *theorem* ennreal.exists_pos_tsum_mul_lt_of_encodable

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measurable_spanning_sets_index
- \+ *lemma* measure_theory.mem_disjointed_spanning_sets_index
- \+ *lemma* measure_theory.mem_spanning_sets_index
- \+ *lemma* measure_theory.preimage_spanning_sets_index_singleton
- \+ *def* measure_theory.spanning_sets_index
- \+ *lemma* measure_theory.spanning_sets_index_eq_iff

Modified src/order/disjointed.lean
- \+ *lemma* preimage_find_eq_disjointed



## [2021-09-15 02:43:59](https://github.com/leanprover-community/mathlib/commit/591ff3a)
feat(group_theory/subgroup): Subgroup of subgroup is isomorphic to itself ([#9204](https://github.com/leanprover-community/mathlib/pull/9204))
If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *def* subgroup.comap_subtype_equiv_of_le



## [2021-09-15 02:43:58](https://github.com/leanprover-community/mathlib/commit/463089d)
feat(order/rel_classes): A total relation is trichotomous ([#9181](https://github.com/leanprover-community/mathlib/pull/9181))
#### Estimated changes
Modified src/order/rel_classes.lean




## [2021-09-15 02:43:57](https://github.com/leanprover-community/mathlib/commit/23eac53)
chore(*): upgrade to Lean 3.33.0c ([#9165](https://github.com/leanprover-community/mathlib/pull/9165))
My main goal is to fix various diamonds with `sup`/`inf`, see leanprover-community/lean[#609](https://github.com/leanprover-community/mathlib/pull/609). I use lean-master + 1 fixup commit leanprover-community/lean[#615](https://github.com/leanprover-community/mathlib/pull/615).
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/ordered_monoid.lean


Modified src/data/bool.lean


Modified src/data/finsupp/lattice.lean


Modified src/data/list/func.lean


Modified src/data/list/intervals.lean
- \+/\- *lemma* list.Ico.filter_le

Modified src/data/list/min_max.lean


Modified src/data/nat/cast.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/rat/cast.lean


Modified src/data/real/nnreal.lean


Modified src/data/string/basic.lean


Modified src/field_theory/separable.lean


Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/number_theory/pell.lean


Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean
- \+/\- *lemma* with_bot.coe_max
- \+/\- *lemma* with_bot.coe_min
- \- *theorem* with_bot.inf_eq_min
- \- *theorem* with_bot.lattice_eq_DLO
- \- *theorem* with_bot.sup_eq_max
- \+/\- *lemma* with_top.coe_max
- \+/\- *lemma* with_top.coe_min
- \- *theorem* with_top.inf_eq_min
- \- *theorem* with_top.lattice_eq_DLO
- \- *theorem* with_top.sup_eq_max

Modified src/order/conditionally_complete_lattice.lean


Modified src/order/lattice.lean
- \+ *def* lattice.to_linear_order

Modified src/tactic/fin_cases.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/path_connected.lean




## [2021-09-15 00:53:15](https://github.com/leanprover-community/mathlib/commit/82dced6)
feat(analysis/normed_space/finite_dimension): Riesz theorem on compact unit ball and finite dimension ([#9147](https://github.com/leanprover-community/mathlib/pull/9147))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/finite_dimension.lean
- \+ *theorem* exists_norm_le_le_norm_sub_of_finset
- \+ *theorem* exists_seq_norm_le_one_le_norm_sub'
- \+ *theorem* exists_seq_norm_le_one_le_norm_sub
- \+ *theorem* finite_dimensional_of_is_compact_closed_ball

Modified src/analysis/normed_space/riesz_lemma.lean
- \+ *lemma* riesz_lemma_of_norm_lt

Modified src/data/fintype/basic.lean
- \+ *lemma* exists_seq_of_forall_finset_exists'
- \+ *lemma* exists_seq_of_forall_finset_exists

Modified src/ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_top_iff



## [2021-09-14 20:59:54](https://github.com/leanprover-community/mathlib/commit/27b0a76)
feat(ring_theory/adjoin): adjoin_range_eq_range_aeval ([#9179](https://github.com/leanprover-community/mathlib/pull/9179))
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.adjoin_range_eq_range_aeval
- \- *theorem* algebra.adjoin_singleton_eq_range
- \+ *theorem* algebra.adjoin_singleton_eq_range_aeval

Modified src/ring_theory/adjoin/power_basis.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/integral_closure.lean




## [2021-09-14 18:16:26](https://github.com/leanprover-community/mathlib/commit/bf0b5df)
chore(combinatorics/simple_graph): fixup docs ([#9161](https://github.com/leanprover-community/mathlib/pull/9161))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-09-14 17:25:52](https://github.com/leanprover-community/mathlib/commit/ec118dd)
ci(.github/workflows/*): lint PR style on GitHub runners ([#9198](https://github.com/leanprover-community/mathlib/pull/9198))
Since the style linter usually finishes in just a few seconds, we can move it off our self-hosted runners to give PR authors quicker feedback when the build queue is long.
We do this only for PR runs, so that `bors` won't be held up in case the GitHub runners are backed up for whatever reason.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml


Modified .github/workflows/mk_build_yml.sh




## [2021-09-14 15:08:00](https://github.com/leanprover-community/mathlib/commit/6a6b0a5)
chore(order/pilex): use `*_order_of_*TO` from `order.rel_classes` ([#9129](https://github.com/leanprover-community/mathlib/pull/9129))
This changes definitional equality for `≤` on `pilex` from
`x < y ∨ x = y` to `x = y ∨ x < y`.
#### Estimated changes
Modified src/order/pilex.lean
- \+ *lemma* pilex.le_of_forall_le

Modified src/order/rel_classes.lean
- \+/\- *def* partial_order_of_SO



## [2021-09-14 13:37:53](https://github.com/leanprover-community/mathlib/commit/91f053e)
chore(*): simplify `data.real.cau_seq` import ([#9197](https://github.com/leanprover-community/mathlib/pull/9197))
Some files were still importing `data.real.cau_seq` when their dependency really was on `is_absolute_value`, which has been moved to `algebra.absolute_value`. Hopefully simplifying the dependency tree slightly reduces build complexity.
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean


Modified src/topology/uniform_space/absolute_value.lean




## [2021-09-14 12:09:47](https://github.com/leanprover-community/mathlib/commit/e489ca1)
feat(group_theory/p_group): Intersection with p-subgroup is a p-subgroup ([#9189](https://github.com/leanprover-community/mathlib/pull/9189))
Two lemmas stating that the intersection with a p-subgroup is a p-subgroup.
Not sure which one should be called left and which one should be called right though :)
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.to_inf_left
- \+ *lemma* is_p_group.to_inf_right



## [2021-09-14 12:09:45](https://github.com/leanprover-community/mathlib/commit/eb20390)
refactor(group_theory/p_group): Move lemmas to is_p_group namespace ([#9188](https://github.com/leanprover-community/mathlib/pull/9188))
Moves `card_modeq_card_fixed_points`, `nonempty_fixed_point_of_prime_not_dvd_card`, and `exists_fixed_point_of_prime_dvd_card_of_fixed_point` to the `is_p_group` namespace. I think this simplifies things, since they already had explicit `hG : is_p_group G` hypotheses anyway.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.card_modeq_card_fixed_points
- \+/\- *lemma* is_p_group.card_orbit
- \+ *lemma* is_p_group.exists_fixed_point_of_prime_dvd_card_of_fixed_point
- \+ *lemma* is_p_group.nonempty_fixed_point_of_prime_not_dvd_card
- \+/\- *lemma* is_p_group.of_card
- \- *lemma* mul_action.card_modeq_card_fixed_points
- \- *lemma* mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
- \- *lemma* mul_action.nonempty_fixed_point_of_prime_not_dvd_card

Modified src/group_theory/sylow.lean




## [2021-09-14 12:09:44](https://github.com/leanprover-community/mathlib/commit/6309c81)
chore(ring_theory/adjoin) elab_as_eliminator attribute ([#9168](https://github.com/leanprover-community/mathlib/pull/9168))
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* algebra.adjoin_induction



## [2021-09-14 12:09:43](https://github.com/leanprover-community/mathlib/commit/251e418)
feat(ring_theory/nakayama): Alternative Statements of Nakayama's Lemma ([#9150](https://github.com/leanprover-community/mathlib/pull/9150))
#### Estimated changes
Modified src/ring_theory/jacobson_ideal.lean
- \+ *lemma* ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson
- \+ *lemma* ideal.is_unit_of_sub_one_mem_jacobson_bot

Added src/ring_theory/nakayama.lean
- \+ *lemma* submodule.eq_bot_of_le_smul_of_le_jacobson_bot
- \+ *lemma* submodule.eq_smul_of_le_smul_of_le_jacobson
- \+ *lemma* submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
- \+ *lemma* submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot



## [2021-09-14 12:09:42](https://github.com/leanprover-community/mathlib/commit/19949a0)
feat(linear_algebra/free_module): add instances ([#9072](https://github.com/leanprover-community/mathlib/pull/9072))
From LTE.
We prove that `M →ₗ[R] N` is free if both `M` and `N` are finite and free. This needs the quite long result that for a finite and free module any basis is finite.
Co-authored with @jcommelin
#### Estimated changes
Modified src/linear_algebra/free_module.lean


Modified src/linear_algebra/matrix/diagonal.lean


Modified src/linear_algebra/std_basis.lean




## [2021-09-14 12:09:41](https://github.com/leanprover-community/mathlib/commit/2a3cd41)
feat(group_theory/free_product): equivalence with reduced words ([#7395](https://github.com/leanprover-community/mathlib/pull/7395))
We show that each element of the free product is represented by a unique reduced word.
#### Estimated changes
Modified src/group_theory/free_product.lean
- \+ *lemma* free_product.word.cons_eq_rcons
- \+ *lemma* free_product.word.cons_eq_smul
- \+ *def* free_product.word.empty
- \+ *def* free_product.word.equiv
- \+ *def* free_product.word.equiv_pair
- \+ *lemma* free_product.word.equiv_pair_eq_of_fst_idx_ne
- \+ *lemma* free_product.word.equiv_pair_symm
- \+ *def* free_product.word.fst_idx
- \+ *lemma* free_product.word.fst_idx_ne_iff
- \+ *lemma* free_product.word.of_smul_def
- \+ *def* free_product.word.prod
- \+ *lemma* free_product.word.prod_nil
- \+ *lemma* free_product.word.prod_rcons
- \+ *lemma* free_product.word.prod_smul
- \+ *def* free_product.word.rcons
- \+ *lemma* free_product.word.rcons_inj
- \+ *lemma* free_product.word.smul_induction



## [2021-09-14 10:41:25](https://github.com/leanprover-community/mathlib/commit/7deb32c)
chore(data/fintype/intervals): finiteness of `Ioo`, `Ioc`, and `Icc` over `ℕ` ([#9096](https://github.com/leanprover-community/mathlib/pull/9096))
We already have the analogous lemmas and instance for `ℤ`.
#### Estimated changes
Modified src/data/fintype/intervals.lean
- \+ *lemma* set.Icc_ℕ_card
- \+ *lemma* set.Icc_ℕ_finite
- \+ *lemma* set.Ico_ℕ_finite
- \+ *lemma* set.Ioc_ℕ_card
- \+ *lemma* set.Ioc_ℕ_finite
- \+ *lemma* set.Ioo_ℕ_card
- \+ *lemma* set.Ioo_ℕ_finite



## [2021-09-14 08:41:19](https://github.com/leanprover-community/mathlib/commit/2d57545)
feat(measure_theory/measure/integral): integral over an encodable type ([#9191](https://github.com/leanprover-community/mathlib/pull/9191))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_encodable

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.map_eq_sum
- \+ *lemma* measure_theory.measure.sum_smul_dirac



## [2021-09-14 08:41:17](https://github.com/leanprover-community/mathlib/commit/790e98f)
feat(linear_algebra/matrix/is_diag): add a file ([#9010](https://github.com/leanprover-community/mathlib/pull/9010))
#### Estimated changes
Added src/linear_algebra/matrix/is_diag.lean
- \+ *lemma* matrix.is_diag.add
- \+ *lemma* matrix.is_diag.conj_transpose
- \+ *lemma* matrix.is_diag.exists_diagonal
- \+ *lemma* matrix.is_diag.from_blocks
- \+ *lemma* matrix.is_diag.from_blocks_of_is_symm
- \+ *lemma* matrix.is_diag.is_symm
- \+ *lemma* matrix.is_diag.kronecker
- \+ *lemma* matrix.is_diag.map
- \+ *lemma* matrix.is_diag.minor
- \+ *lemma* matrix.is_diag.neg
- \+ *lemma* matrix.is_diag.smul
- \+ *lemma* matrix.is_diag.sub
- \+ *lemma* matrix.is_diag.transpose
- \+ *def* matrix.is_diag
- \+ *lemma* matrix.is_diag_conj_transpose_iff
- \+ *lemma* matrix.is_diag_diagonal
- \+ *lemma* matrix.is_diag_from_blocks_iff
- \+ *lemma* matrix.is_diag_iff_exists_diagonal
- \+ *lemma* matrix.is_diag_neg_iff
- \+ *lemma* matrix.is_diag_of_subsingleton
- \+ *lemma* matrix.is_diag_one
- \+ *lemma* matrix.is_diag_smul_one
- \+ *lemma* matrix.is_diag_transpose_iff
- \+ *lemma* matrix.is_diag_zero
- \+ *lemma* matrix.mul_transpose_self_is_diag_iff_has_orthogonal_rows
- \+ *lemma* matrix.transpose_mul_self_is_diag_iff_has_orthogonal_cols

Added src/linear_algebra/matrix/orthogonal.lean
- \+ *lemma* matrix.has_orthogonal_cols.has_orthogonal_rows
- \+ *lemma* matrix.has_orthogonal_cols.transpose_has_orthogonal_rows
- \+ *def* matrix.has_orthogonal_cols
- \+ *lemma* matrix.has_orthogonal_rows.has_orthogonal_cols
- \+ *lemma* matrix.has_orthogonal_rows.transpose_has_orthogonal_cols
- \+ *def* matrix.has_orthogonal_rows
- \+ *lemma* matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows
- \+ *lemma* matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols



## [2021-09-14 06:36:12](https://github.com/leanprover-community/mathlib/commit/9af1db3)
feat(measure_theory/measure/measure_space): The pushfoward measure of a finite measure is a finite measure ([#9186](https://github.com/leanprover-community/mathlib/pull/9186))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.is_finite_measure_map



## [2021-09-14 06:36:11](https://github.com/leanprover-community/mathlib/commit/ceab0e7)
chore(order/bounded_lattice): make `bot_lt_some` and `some_lt_none` consistent ([#9180](https://github.com/leanprover-community/mathlib/pull/9180))
`with_bot.bot_lt_some` gets renamed to `with_bot.none_lt_some` and now syntactically applies to `none : with_bot α` (`with_bot.bot_le_coe` already applies to `⊥` and `↑a`).
`with_top.some_lt_none` now takes `a` explicit.
#### Estimated changes
Modified src/data/nat/with_bot.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/div.lean


Modified src/order/bounded_lattice.lean
- \+/\- *lemma* with_bot.bot_lt_coe
- \- *lemma* with_bot.bot_lt_some
- \+ *lemma* with_bot.none_lt_some
- \+/\- *lemma* with_top.coe_lt_top
- \+/\- *theorem* with_top.some_lt_none

Modified src/ring_theory/power_basis.lean




## [2021-09-14 06:36:10](https://github.com/leanprover-community/mathlib/commit/ef78b32)
feat(measure_theory/function/lp_space): add lemmas about snorm and mem_Lp ([#9146](https://github.com/leanprover-community/mathlib/pull/9146))
Also move lemma `snorm_add_le` (and related others) out of the borel space section, since `opens_measurable_space` is a sufficient hypothesis.
#### Estimated changes
Modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_smul_measure

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.congr_norm
- \+ *lemma* measure_theory.mem_ℒp.mono'
- \+ *lemma* measure_theory.mem_ℒp_congr_norm
- \+ *lemma* measure_theory.mem_ℒp_const_iff
- \+ *lemma* measure_theory.mem_ℒp_finset_sum
- \+ *lemma* measure_theory.mem_ℒp_neg_iff
- \+ *lemma* measure_theory.mem_ℒp_norm_iff
- \+ *lemma* measure_theory.snorm'_smul_measure
- \+ *lemma* measure_theory.snorm_const_lt_top_iff
- \+ *lemma* measure_theory.snorm_ess_sup_smul_measure
- \+ *lemma* measure_theory.snorm_mono
- \+ *lemma* measure_theory.snorm_mono_ae_real
- \+ *lemma* measure_theory.snorm_mono_real
- \+ *lemma* measure_theory.snorm_one_smul_measure
- \+ *lemma* measure_theory.snorm_smul_measure_of_ne_top
- \+ *lemma* measure_theory.snorm_smul_measure_of_ne_zero
- \+ *lemma* measure_theory.snorm_sub_le
- \+ *lemma* measure_theory.snorm_zero'
- \+ *lemma* measure_theory.zero_mem_ℒp'



## [2021-09-14 06:36:09](https://github.com/leanprover-community/mathlib/commit/5aaa5fa)
chore(measure_theory/integral/set_integral): update old lemmas that were in comments at the end of the file ([#9111](https://github.com/leanprover-community/mathlib/pull/9111))
The file `set_integral` had a list of lemmas in comments at the end of the file, which were written for an old implementation of the set integral. This PR deletes the comments, and adds the corresponding results when they don't already exist.
The lemmas `set_integral_congr_set_ae` and `set_integral_mono_set` are also moved to relevant sections.
#### Estimated changes
Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_union_ae
- \+ *lemma* measure_theory.set_integral_mono_on_ae
- \+/\- *lemma* measure_theory.set_integral_mono_set
- \+ *lemma* measure_theory.set_integral_nonneg_ae
- \+/\- *lemma* measure_theory.set_integral_nonneg_of_ae
- \+ *lemma* measure_theory.set_integral_nonpos
- \+ *lemma* measure_theory.set_integral_nonpos_ae
- \+ *lemma* measure_theory.set_integral_nonpos_of_ae
- \+ *lemma* measure_theory.set_integral_nonpos_of_ae_restrict
- \+ *lemma* measure_theory.tendsto_set_integral_of_antimono
- \+ *lemma* measure_theory.tendsto_set_integral_of_monotone

Modified src/measure_theory/measure/measure_space.lean




## [2021-09-14 06:36:08](https://github.com/leanprover-community/mathlib/commit/4b7593f)
feat(data/last/basic): a lemma specifying list.split_on ([#9104](https://github.com/leanprover-community/mathlib/pull/9104))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.intersperse_cons_cons
- \+ *lemma* list.intersperse_nil
- \+ *lemma* list.intersperse_singleton
- \+ *lemma* list.join_nil
- \+ *lemma* list.split_on_nil
- \+ *def* list.split_on_p_aux'
- \+ *lemma* list.split_on_p_aux_eq
- \+ *lemma* list.split_on_p_aux_nil
- \+ *lemma* list.split_on_p_spec



## [2021-09-14 04:32:20](https://github.com/leanprover-community/mathlib/commit/d3b345d)
feat(group_theory/p_group): Bottom subgroup is a p-group ([#9190](https://github.com/leanprover-community/mathlib/pull/9190))
The bottom subgroup is a p-group.
Name is consistent with `is_p_group.of_card`
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.of_bot



## [2021-09-14 04:32:19](https://github.com/leanprover-community/mathlib/commit/8dffafd)
feat(topology): one-point compactification of a topological space ([#8579](https://github.com/leanprover-community/mathlib/pull/8579))
Define `alexandroff X` to be the one-point compactification of a topological space `X` and prove some basic lemmas about this definition.
Co-authored by: Yury G. Kudryashov <urkud@urkud.name>
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/data/set/basic.lean
- \+ *theorem* function.injective.compl_image_eq

Modified src/data/set/function.lean
- \+ *theorem* set.maps_to_singleton

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.sup_principal
- \+ *lemma* filter.has_basis.sup_pure
- \+ *lemma* filter.has_basis_pure

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.tendsto_comap_iff
- \+/\- *lemma* filter.tendsto_map'_iff
- \+/\- *lemma* filter.tendsto_sup

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* ultrafilter.coe_comap
- \+ *lemma* ultrafilter.mem_comap

Added src/topology/alexandroff.lean
- \+ *lemma* alexandroff.coe_eq_coe
- \+ *lemma* alexandroff.coe_injective
- \+ *lemma* alexandroff.coe_ne_infty
- \+ *lemma* alexandroff.coe_preimage_infty
- \+ *lemma* alexandroff.comap_coe_nhds
- \+ *lemma* alexandroff.comap_coe_nhds_infty
- \+ *lemma* alexandroff.compl_image_coe
- \+ *lemma* alexandroff.compl_infty
- \+ *lemma* alexandroff.compl_range_coe
- \+ *lemma* alexandroff.continuous_at_coe
- \+ *lemma* alexandroff.continuous_at_infty'
- \+ *lemma* alexandroff.continuous_at_infty
- \+ *lemma* alexandroff.continuous_coe
- \+ *lemma* alexandroff.dense_embedding_coe
- \+ *lemma* alexandroff.dense_range_coe
- \+ *lemma* alexandroff.has_basis_nhds_infty
- \+ *def* alexandroff.infty
- \+ *lemma* alexandroff.infty_mem_opens_of_compl
- \+ *lemma* alexandroff.infty_ne_coe
- \+ *lemma* alexandroff.infty_not_mem_image_coe
- \+ *lemma* alexandroff.infty_not_mem_range_coe
- \+ *lemma* alexandroff.is_closed_iff_of_mem
- \+ *lemma* alexandroff.is_closed_iff_of_not_mem
- \+ *lemma* alexandroff.is_closed_image_coe
- \+ *lemma* alexandroff.is_closed_infty
- \+ *lemma* alexandroff.is_compl_range_coe_infty
- \+ *lemma* alexandroff.is_open_compl_image_coe
- \+ *lemma* alexandroff.is_open_def
- \+ *lemma* alexandroff.is_open_iff_of_mem'
- \+ *lemma* alexandroff.is_open_iff_of_mem
- \+ *lemma* alexandroff.is_open_iff_of_not_mem
- \+ *lemma* alexandroff.is_open_image_coe
- \+ *lemma* alexandroff.is_open_map_coe
- \+ *lemma* alexandroff.is_open_range_coe
- \+ *lemma* alexandroff.le_nhds_infty
- \+ *lemma* alexandroff.ne_infty_iff_exists
- \+ *lemma* alexandroff.nhds_coe_eq
- \+ *lemma* alexandroff.nhds_infty_eq
- \+ *lemma* alexandroff.nhds_within_coe
- \+ *lemma* alexandroff.nhds_within_coe_image
- \+ *lemma* alexandroff.nhds_within_compl_infty_eq
- \+ *lemma* alexandroff.not_mem_range_coe_iff
- \+ *lemma* alexandroff.open_embedding_coe
- \+ *def* alexandroff.opens_of_compl
- \+ *lemma* alexandroff.range_coe_inter_infty
- \+ *lemma* alexandroff.range_coe_union_infty
- \+ *lemma* alexandroff.tendsto_nhds_infty'
- \+ *lemma* alexandroff.tendsto_nhds_infty
- \+ *lemma* alexandroff.ultrafilter_le_nhds_infty
- \+ *def* alexandroff

Modified src/topology/continuous_on.lean
- \+ *lemma* embedding.map_nhds_within_eq
- \+ *theorem* is_open.nhds_within_eq
- \+ *theorem* nhds_within_compl_singleton_sup_pure
- \- *theorem* nhds_within_eq_of_open
- \+ *lemma* open_embedding.map_nhds_within_preimage_eq

Modified src/topology/separation.lean
- \+ *lemma* filter.coclosed_compact_eq_cocompact

Modified src/topology/subset_properties.lean
- \+ *def* filter.coclosed_compact
- \+/\- *def* filter.cocompact
- \+ *lemma* filter.cocompact_le_coclosed_compact
- \+ *lemma* filter.cocompact_ne_bot_tfae
- \+ *lemma* filter.has_basis_coclosed_compact
- \+/\- *lemma* filter.has_basis_cocompact
- \+ *lemma* filter.mem_coclosed_compact'
- \+ *lemma* filter.mem_coclosed_compact
- \+/\- *lemma* filter.mem_cocompact'
- \+/\- *lemma* filter.mem_cocompact
- \+/\- *lemma* is_compact.compl_mem_cocompact
- \+ *lemma* is_compact_univ_iff



## [2021-09-14 03:42:22](https://github.com/leanprover-community/mathlib/commit/f88f3a7)
chore(scripts): update nolints.txt ([#9192](https://github.com/leanprover-community/mathlib/pull/9192))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-14 01:19:50](https://github.com/leanprover-community/mathlib/commit/f0a1356)
feat(linear_algebra/matrix/circulant): add a file ([#9011](https://github.com/leanprover-community/mathlib/pull/9011))
#### Estimated changes
Added src/linear_algebra/matrix/circulant.lean
- \+ *def* matrix.circulant
- \+ *lemma* matrix.circulant_add
- \+ *lemma* matrix.circulant_col_zero_eq
- \+ *lemma* matrix.circulant_inj
- \+ *lemma* matrix.circulant_injective
- \+ *lemma* matrix.circulant_is_symm_apply
- \+ *lemma* matrix.circulant_is_symm_iff
- \+ *lemma* matrix.circulant_mul
- \+ *lemma* matrix.circulant_mul_comm
- \+ *lemma* matrix.circulant_neg
- \+ *lemma* matrix.circulant_single
- \+ *lemma* matrix.circulant_single_one
- \+ *lemma* matrix.circulant_smul
- \+ *lemma* matrix.circulant_sub
- \+ *lemma* matrix.circulant_zero
- \+ *lemma* matrix.conj_transpose_circulant
- \+ *lemma* matrix.fin.circulant_inj
- \+ *lemma* matrix.fin.circulant_injective
- \+ *lemma* matrix.fin.circulant_is_symm_apply
- \+ *lemma* matrix.fin.circulant_is_symm_iff
- \+ *lemma* matrix.fin.circulant_ite
- \+ *lemma* matrix.fin.circulant_mul
- \+ *lemma* matrix.fin.circulant_mul_comm
- \+ *lemma* matrix.fin.conj_transpose_circulant
- \+ *lemma* matrix.fin.transpose_circulant
- \+ *lemma* matrix.map_circulant
- \+ *lemma* matrix.transpose_circulant



## [2021-09-13 23:34:39](https://github.com/leanprover-community/mathlib/commit/103c1ff)
feat(data/(d)finsupp): (d)finsupp.update ([#9015](https://github.com/leanprover-community/mathlib/pull/9015))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.coe_update
- \+ *lemma* dfinsupp.support_update
- \+ *lemma* dfinsupp.support_update_ne_zero
- \+ *def* dfinsupp.update
- \+ *lemma* dfinsupp.update_eq_erase
- \+ *lemma* dfinsupp.update_self

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_update
- \+ *lemma* finsupp.support_update
- \+ *lemma* finsupp.support_update_ne_zero
- \+ *lemma* finsupp.support_update_zero
- \+ *def* finsupp.update
- \+ *lemma* finsupp.update_self



## [2021-09-13 18:35:51](https://github.com/leanprover-community/mathlib/commit/d9476d4)
fix(tactic/rcases): Don't parameterize parsers ([#9159](https://github.com/leanprover-community/mathlib/pull/9159))
The parser description generator only unfolds parser constants if they have no arguments, which means that parsers like `rcases_patt_parse tt` and `rcases_patt_parse ff` don't generate descriptions even though they have a `with_desc` clause. We fix this by naming the parsers separately.
Fixes [#9158](https://github.com/leanprover-community/mathlib/pull/9158)
#### Estimated changes
Modified src/tactic/congr.lean


Modified src/tactic/ext.lean


Modified src/tactic/rcases.lean


Modified test/ext.lean




## [2021-09-13 17:45:52](https://github.com/leanprover-community/mathlib/commit/ec5f496)
feat(README.md): add Rémy Degenne ([#9187](https://github.com/leanprover-community/mathlib/pull/9187))
#### Estimated changes
Modified README.md




## [2021-09-13 16:19:14](https://github.com/leanprover-community/mathlib/commit/40247bd)
feat(measure_theory/measure/vector_measure): add `vector_measure.trim` ([#9169](https://github.com/leanprover-community/mathlib/pull/9169))
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.restrict_trim
- \+ *def* measure_theory.vector_measure.trim
- \+ *lemma* measure_theory.vector_measure.trim_eq_self
- \+ *lemma* measure_theory.vector_measure.trim_measurable_set_eq
- \+ *lemma* measure_theory.vector_measure.zero_trim



## [2021-09-13 16:19:13](https://github.com/leanprover-community/mathlib/commit/3b4f4da)
feat(linear_algebra/determinant): more on the determinant of linear maps ([#9139](https://github.com/leanprover-community/mathlib/pull/9139))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_map.det_conj
- \+ *lemma* linear_map.det_smul
- \+ *lemma* linear_map.det_to_matrix'
- \+ *lemma* linear_map.det_zero'
- \+/\- *lemma* linear_map.det_zero
- \+ *def* linear_map.equiv_of_det_ne_zero

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* linear_map.to_matrix_eq_to_matrix'
- \+ *lemma* matrix.to_lin_eq_to_lin'



## [2021-09-13 13:59:40](https://github.com/leanprover-community/mathlib/commit/a9e7d33)
chore(analysis/calculus/[f]deriv): generalize product formula to product in normed algebras ([#9163](https://github.com/leanprover-community/mathlib/pull/9163))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \- *lemma* deriv_const_mul'
- \+/\- *lemma* deriv_const_mul
- \+ *lemma* deriv_const_mul_field'
- \+ *lemma* deriv_const_mul_field
- \- *lemma* deriv_mul_const'
- \+/\- *lemma* deriv_mul_const
- \+ *lemma* deriv_mul_const_field'
- \+ *lemma* deriv_mul_const_field
- \+/\- *theorem* has_deriv_at.const_mul
- \+/\- *theorem* has_deriv_at.mul_const
- \+/\- *theorem* has_deriv_within_at.const_mul
- \+/\- *theorem* has_deriv_within_at.mul_const
- \+/\- *theorem* has_strict_deriv_at.const_mul
- \+/\- *theorem* has_strict_deriv_at.mul_const

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable.const_mul
- \+/\- *lemma* differentiable.mul
- \+/\- *lemma* differentiable.mul_const
- \+/\- *lemma* differentiable_at.const_mul
- \+/\- *lemma* differentiable_at.mul
- \+/\- *lemma* differentiable_at.mul_const
- \+/\- *lemma* differentiable_on.const_mul
- \+/\- *lemma* differentiable_on.mul
- \+/\- *lemma* differentiable_on.mul_const
- \+/\- *lemma* fderiv_const_mul
- \+ *lemma* fderiv_mul'
- \+ *lemma* fderiv_mul_const'
- \+/\- *lemma* fderiv_mul_const
- \+ *lemma* fderiv_within_mul'
- \+ *lemma* fderiv_within_mul_const'
- \+/\- *theorem* has_fderiv_at.const_mul
- \+ *theorem* has_fderiv_at.mul'
- \+ *theorem* has_fderiv_at.mul_const'
- \+/\- *theorem* has_fderiv_at.mul_const
- \+ *theorem* has_fderiv_within_at.mul'
- \+ *theorem* has_fderiv_within_at.mul_const'
- \+/\- *theorem* has_fderiv_within_at.mul_const
- \+/\- *theorem* has_strict_fderiv_at.const_mul
- \+ *theorem* has_strict_fderiv_at.mul'
- \+ *theorem* has_strict_fderiv_at.mul_const'
- \+/\- *theorem* has_strict_fderiv_at.mul_const

Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean




## [2021-09-13 13:59:39](https://github.com/leanprover-community/mathlib/commit/ad62583)
chore(algebra/big_operators): add a lemma ([#9120](https://github.com/leanprover-community/mathlib/pull/9120))
(product over `s.filter p`) * (product over `s.filter (λ x, ¬p x)) = product over s
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_filter_mul_prod_filter_not

Modified src/data/finset/basic.lean
- \+/\- *theorem* finset.filter_inter_filter_neg_eq



## [2021-09-13 10:22:39](https://github.com/leanprover-community/mathlib/commit/b0e8ced)
feat(group_theory/nilpotent): add intermediate lemmas ([#9016](https://github.com/leanprover-community/mathlib/pull/9016))
Add two new lemmas on nilpotent groups.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* is_nilpotent_of_ker_le_center
- \+ *lemma* lower_central_series_succ_eq_bot



## [2021-09-13 09:34:19](https://github.com/leanprover-community/mathlib/commit/a8a8edc)
feat(group_theory/p_group): Generalize to infinite p-groups ([#9082](https://github.com/leanprover-community/mathlib/pull/9082))
Defines p-groups, and generalizes the results of `p_group.lean` to infinite p-groups. The eventual goal is to generalize Sylow's theorems to infinite groups.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.card_orbit
- \+ *lemma* is_p_group.iff_card
- \+ *lemma* is_p_group.iff_order_of
- \+ *lemma* is_p_group.index
- \+ *lemma* is_p_group.of_card
- \+ *lemma* is_p_group.to_le
- \+ *lemma* is_p_group.to_quotient
- \+ *lemma* is_p_group.to_subgroup
- \+ *def* is_p_group
- \+/\- *lemma* mul_action.nonempty_fixed_point_of_prime_not_dvd_card

Modified src/group_theory/sylow.lean




## [2021-09-13 09:34:17](https://github.com/leanprover-community/mathlib/commit/d4f8b92)
feat(measure_theory/measure/with_density_vector_measure): define vector measures by an integral over a function ([#9008](https://github.com/leanprover-community/mathlib/pull/9008))
This PR defined the vector measure corresponding to mapping the set `s` to the integral `∫ x in s, f x ∂μ` given some measure `μ` and some integrable function `f`.
#### Estimated changes
Added src/measure_theory/measure/with_density_vector_measure.lean
- \+ *lemma* measure_theory.integrable.ae_eq_of_with_densityᵥ_eq
- \+ *lemma* measure_theory.integrable.with_densityᵥ_eq_iff
- \+ *def* measure_theory.measure.with_densityᵥ
- \+ *lemma* measure_theory.measure.with_densityᵥ_absolutely_continuous
- \+ *lemma* measure_theory.with_densityᵥ_add
- \+ *lemma* measure_theory.with_densityᵥ_apply
- \+ *lemma* measure_theory.with_densityᵥ_eq.congr_ae
- \+ *lemma* measure_theory.with_densityᵥ_neg
- \+ *lemma* measure_theory.with_densityᵥ_smul
- \+ *lemma* measure_theory.with_densityᵥ_sub
- \+ *lemma* measure_theory.with_densityᵥ_zero



## [2021-09-13 09:34:16](https://github.com/leanprover-community/mathlib/commit/80085fc)
feat(number_theory/padics/padic_integers): Z_p is adically complete ([#8995](https://github.com/leanprover-community/mathlib/pull/8995))
#### Estimated changes
Modified src/number_theory/padics/padic_integers.lean




## [2021-09-13 08:46:12](https://github.com/leanprover-community/mathlib/commit/d082001)
feat(analysis/convex/independent): convex independence ([#9018](https://github.com/leanprover-community/mathlib/pull/9018))
#### Estimated changes
Added src/analysis/convex/independent.lean
- \+ *lemma* convex.extreme_points_convex_independent
- \+ *lemma* convex_independent.comp_embedding
- \+ *def* convex_independent
- \+ *lemma* convex_independent_iff_finset
- \+ *lemma* convex_independent_iff_not_mem_convex_hull_diff
- \+ *lemma* convex_independent_set_iff_inter_convex_hull_subset
- \+ *lemma* convex_independent_set_iff_not_mem_convex_hull_diff
- \+ *lemma* function.injective.convex_independent_iff_set
- \+ *lemma* subsingleton.convex_independent

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent.indicator_eq_of_affine_combination_eq



## [2021-09-13 06:36:44](https://github.com/leanprover-community/mathlib/commit/1cf1704)
chore(order/filter): more readable proof ([#9173](https://github.com/leanprover-community/mathlib/pull/9173))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean




## [2021-09-13 06:36:43](https://github.com/leanprover-community/mathlib/commit/1479068)
chore(ring_theory/polynomial/cyclotomic): fix namespacing ([#9116](https://github.com/leanprover-community/mathlib/pull/9116))
@riccardobrasca told me I got it wrong, so I fixed it :)
#### Estimated changes
Modified src/number_theory/primes_congruent_one.lean


Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* minpoly_dvd_cyclotomic
- \- *lemma* polynomial.minpoly_primitive_root_dvd_cyclotomic
- \- *lemma* polynomial.order_of_root_cyclotomic
- \+ *lemma* polynomial.order_of_root_cyclotomic_eq



## [2021-09-13 06:00:30](https://github.com/leanprover-community/mathlib/commit/5651157)
feat(linear_algebra/adic_completion): le_jacobson_bot ([#9125](https://github.com/leanprover-community/mathlib/pull/9125))
This PR proves that in an `I`-adically complete commutative ring `R`, the ideal `I` is contained in the Jacobson radical of `R`.
#### Estimated changes
Modified src/linear_algebra/adic_completion.lean
- \+ *lemma* is_adic_complete.le_jacobson_bot



## [2021-09-13 04:04:40](https://github.com/leanprover-community/mathlib/commit/ca23d52)
feat(set_theory/surreal): add dyadic surreals ([#7843](https://github.com/leanprover-community/mathlib/pull/7843))
We define `surreal.dyadic` using a map from \int localized away from 2 to surreals. As currently we do not have the ring structure on `surreal` we do this "by hand". 
Next steps: 
1. Prove that `dyadic_map` is injective
2. Prove that `dyadic_map` is a group hom
3. Show that \int localized away from 2 is a subgroup of \rat.
#### Estimated changes
Modified docs/references.bib


Modified src/set_theory/pgame.lean
- \+ *def* pgame.half
- \+ *theorem* pgame.half_lt_one
- \+ *lemma* pgame.half_move_left
- \+ *lemma* pgame.half_move_right
- \+ *theorem* pgame.zero_lt_half
- \+ *theorem* pgame.zero_lt_one

Renamed src/set_theory/surreal.lean to src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.half_add_half_equiv_one
- \+ *theorem* pgame.numeric_half

Added src/set_theory/surreal/dyadic.lean
- \+ *theorem* pgame.add_pow_half_succ_self_eq_pow_half
- \+ *theorem* pgame.numeric_pow_half
- \+ *def* pgame.pow_half
- \+ *lemma* pgame.pow_half_left_moves
- \+ *lemma* pgame.pow_half_move_left'
- \+ *lemma* pgame.pow_half_move_left
- \+ *lemma* pgame.pow_half_move_right'
- \+ *lemma* pgame.pow_half_move_right
- \+ *lemma* pgame.pow_half_right_moves
- \+ *theorem* pgame.pow_half_succ_le_pow_half
- \+ *theorem* pgame.pow_half_succ_lt_pow_half
- \+ *theorem* pgame.zero_le_pow_half
- \+ *theorem* pgame.zero_lt_pow_half
- \+ *theorem* surreal.add_half_self_eq_one
- \+ *lemma* surreal.double_pow_half_succ_eq_pow_half
- \+ *def* surreal.dyadic
- \+ *lemma* surreal.dyadic_aux
- \+ *def* surreal.dyadic_map
- \+ *def* surreal.half
- \+ *lemma* surreal.nsmul_int_pow_two_pow_half
- \+ *lemma* surreal.nsmul_pow_two_pow_half'
- \+ *lemma* surreal.nsmul_pow_two_pow_half
- \+ *def* surreal.pow_half
- \+ *lemma* surreal.pow_half_one
- \+ *lemma* surreal.pow_half_zero



## [2021-09-13 02:40:27](https://github.com/leanprover-community/mathlib/commit/f0effbd)
chore(scripts): update nolints.txt ([#9177](https://github.com/leanprover-community/mathlib/pull/9177))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-13 00:53:07](https://github.com/leanprover-community/mathlib/commit/87c1820)
feat(group_theory/perm/concrete_cycle): perms from cycle data structure ([#8866](https://github.com/leanprover-community/mathlib/pull/8866))
#### Estimated changes
Modified src/group_theory/perm/concrete_cycle.lean
- \+ *def* cycle.form_perm
- \+ *lemma* cycle.form_perm_apply_mem_eq_next
- \+ *lemma* cycle.form_perm_coe
- \+ *lemma* cycle.form_perm_eq_form_perm_iff
- \+ *lemma* cycle.form_perm_eq_self_of_not_mem
- \+ *lemma* cycle.form_perm_reverse
- \+ *lemma* cycle.form_perm_subsingleton
- \+ *lemma* cycle.is_cycle_form_perm
- \+ *lemma* cycle.support_form_perm



## [2021-09-12 22:30:08](https://github.com/leanprover-community/mathlib/commit/f6c8aff)
feat(order/zorn) : `chain_univ` ([#9162](https://github.com/leanprover-community/mathlib/pull/9162))
`univ` is a `r`-chain iff `r` is trichotomous
#### Estimated changes
Modified src/order/zorn.lean
- \+ *lemma* zorn.chain_of_trichotomous
- \+ *lemma* zorn.chain_univ_iff



## [2021-09-12 20:47:08](https://github.com/leanprover-community/mathlib/commit/5b702ec)
chore(linear_algebra/basic): move map_comap_eq into submodule namespace ([#9160](https://github.com/leanprover-community/mathlib/pull/9160))
We change the following lemmas from the `linear_map` namespace into the `submodule` namespace
- map_comap_eq
- comap_map_eq
- map_comap_eq_self
- comap_map_eq_self
This is consistent with `subgroup.map_comap_eq`, and the lemmas are about `submodule.map` so it make sense to keep them in the submodule namespace.
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean


Modified src/algebra/lie/submodule.lean


Modified src/linear_algebra/basic.lean
- \- *lemma* linear_map.comap_map_eq
- \- *lemma* linear_map.comap_map_eq_self
- \- *lemma* linear_map.map_comap_eq
- \- *lemma* linear_map.map_comap_eq_self
- \+ *lemma* submodule.comap_map_eq
- \+ *lemma* submodule.comap_map_eq_self
- \+ *lemma* submodule.map_comap_eq
- \+ *lemma* submodule.map_comap_eq_self

Modified src/ring_theory/artinian.lean


Modified src/ring_theory/noetherian.lean




## [2021-09-12 18:41:01](https://github.com/leanprover-community/mathlib/commit/00d570a)
doc(algebra/covariant_and_contravariant): fix parameter documentation… ([#9171](https://github.com/leanprover-community/mathlib/pull/9171))
… in covariant_class and contravariant_class
In the documentation of `algebra.covariant_and_contravariant.covariant_class` and `algebra.covariant_and_contravariant.contravariant_class`, the parameter `r` is described as having type `N → N`. It's actual type is `N → N → Prop`. We change the documentation to give the correct type of `r`.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean




## [2021-09-12 18:41:00](https://github.com/leanprover-community/mathlib/commit/65f8148)
chore(algebra/field_power): golf some proofs ([#9170](https://github.com/leanprover-community/mathlib/pull/9170))
#### Estimated changes
Modified src/algebra/field_power.lean




## [2021-09-12 18:40:59](https://github.com/leanprover-community/mathlib/commit/3366a68)
feat(data/fin): eq_zero_or_eq_succ ([#9136](https://github.com/leanprover-community/mathlib/pull/9136))
Particularly useful with `rcases i.eq_zero_or_eq_succ with rfl|⟨j,rfl⟩`.
Perhaps it not worth having as a separate lemma, but it seems to avoid breaking the flow of a proof I was writing.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.eq_zero_or_eq_succ



## [2021-09-12 17:53:26](https://github.com/leanprover-community/mathlib/commit/a7d872f)
chore(category/abelian/pseudoelements): localize expensive typeclass ([#9156](https://github.com/leanprover-community/mathlib/pull/9156))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).
#### Estimated changes
Modified src/category_theory/abelian/diagram_lemmas/four.lean


Modified src/category_theory/abelian/pseudoelements.lean
- \+ *def* category_theory.abelian.pseudoelement.has_zero



## [2021-09-12 15:14:38](https://github.com/leanprover-community/mathlib/commit/995f481)
feat(logic/basic): a few lemmas ([#9166](https://github.com/leanprover-community/mathlib/pull/9166))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* and_forall_ne
- \+ *theorem* decidable.imp_iff_right_iff
- \+/\- *theorem* exists_imp_distrib
- \+ *theorem* forall_exists_index
- \+ *theorem* forall_imp_iff_exists_imp
- \+ *theorem* imp_iff_right_iff

Modified src/logic/function/basic.lean




## [2021-09-12 09:48:17](https://github.com/leanprover-community/mathlib/commit/04d2b12)
feat(ring_theory/ideal/operations): annihilator_smul ([#9151](https://github.com/leanprover-community/mathlib/pull/9151))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* submodule.annihilator_mul
- \+ *theorem* submodule.annihilator_smul
- \+ *theorem* submodule.mul_annihilator



## [2021-09-12 06:48:16](https://github.com/leanprover-community/mathlib/commit/f863703)
fix(category_theory/concrete_category): remove bad instance ([#9154](https://github.com/leanprover-community/mathlib/pull/9154))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/category_theory/concrete_category/reflects_isomorphisms.lean
- \+ *lemma* category_theory.reflects_isomorphisms_forget₂



## [2021-09-12 06:48:15](https://github.com/leanprover-community/mathlib/commit/858e764)
fix(ring_theory/ideal/basic): ideal.module_pi speedup ([#9148](https://github.com/leanprover-community/mathlib/pull/9148))
Eric and Yael were both complaining that `ideal.module_pi` would occasionally cause random timeouts on unrelated PRs. This PR (a) makes the `smul` proof obligation much tidier (factoring out a sublemma) and (b) replaces the `all_goals` trick by 6 slightly more refined proofs (making the new proof longer, but quicker). On my machine the profiler stats are:
```
ORIG
parsing took 74.1ms
elaboration of module_pi took 3.83s
type checking of module_pi took 424ms
decl post-processing of module_pi took 402ms
NEW
parsing took 136ms
elaboration of module_pi took 1.19s
type checking of module_pi took 82.8ms
decl post-processing of module_pi took 82.5ms
```
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.mul_sub_mul_mem



## [2021-09-12 06:48:14](https://github.com/leanprover-community/mathlib/commit/b55483a)
feat(category_theory/monoidal): rigid (autonomous) monoidal categories ([#8946](https://github.com/leanprover-community/mathlib/pull/8946))
Defines rigid monoidal categories and creates the instance of finite dimensional vector spaces.
#### Estimated changes
Added src/algebra/category/FinVect.lean
- \+ *def* FinVect.FinVect_coevaluation
- \+ *lemma* FinVect.FinVect_coevaluation_apply_one
- \+ *def* FinVect.FinVect_dual
- \+ *def* FinVect.FinVect_evaluation
- \+ *lemma* FinVect.FinVect_evaluation_apply
- \+ *def* FinVect

Modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* Module.monoidal_category.associator_inv_apply
- \+ *lemma* Module.monoidal_category.left_unitor_inv_apply
- \+ *lemma* Module.monoidal_category.right_unitor_inv_apply

Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.associator_conjugation
- \+ *lemma* category_theory.monoidal_category.associator_inv_conjugation
- \+ *def* category_theory.monoidal_category.full_monoidal_subcategory
- \+ *lemma* category_theory.monoidal_category.id_tensor_right_unitor_inv
- \+ *lemma* category_theory.monoidal_category.left_unitor_inv_comp_tensor
- \+ *lemma* category_theory.monoidal_category.left_unitor_inv_tensor_id
- \+ *lemma* category_theory.monoidal_category.pentagon_comp_id_tensor
- \+ *lemma* category_theory.monoidal_category.pentagon_hom_inv
- \+ *lemma* category_theory.monoidal_category.pentagon_inv_hom
- \+ *lemma* category_theory.monoidal_category.pentagon_inv_inv_hom
- \+ *lemma* category_theory.monoidal_category.right_unitor_inv_comp_tensor

Added src/category_theory/monoidal/rigid.lean
- \+ *lemma* category_theory.comp_left_adjoint_mate
- \+ *lemma* category_theory.comp_right_adjoint_mate
- \+ *def* category_theory.left_adjoint_mate
- \+ *lemma* category_theory.left_adjoint_mate_comp
- \+ *lemma* category_theory.left_adjoint_mate_id
- \+ *def* category_theory.left_dual_iso
- \+ *lemma* category_theory.left_dual_iso_id
- \+ *lemma* category_theory.left_dual_right_dual
- \+ *def* category_theory.right_adjoint_mate
- \+ *lemma* category_theory.right_adjoint_mate_comp
- \+ *lemma* category_theory.right_adjoint_mate_id
- \+ *def* category_theory.right_dual_iso
- \+ *lemma* category_theory.right_dual_iso_id
- \+ *lemma* category_theory.right_dual_left_dual

Added src/linear_algebra/coevaluation.lean
- \+ *def* coevaluation
- \+ *lemma* coevaluation_apply_one
- \+ *lemma* contract_left_assoc_coevaluation'
- \+ *lemma* contract_left_assoc_coevaluation

Modified src/linear_algebra/finsupp_vector_space.lean
- \- *def* finsupp.basis.tensor_product

Added src/linear_algebra/tensor_product_basis.lean
- \+ *def* basis.tensor_product



## [2021-09-12 05:54:55](https://github.com/leanprover-community/mathlib/commit/e1bed5a)
fix(category_theory/adjunction/limits): remove bad instance ([#9157](https://github.com/leanprover-community/mathlib/pull/9157))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean
- \+ *lemma* category_theory.adjunction.has_colimit_comp_equivalence
- \+ *lemma* category_theory.adjunction.has_limit_comp_equivalence

Modified src/category_theory/limits/over.lean




## [2021-09-12 05:54:54](https://github.com/leanprover-community/mathlib/commit/059eba4)
fix(category/preadditive/single_obj): remove superfluous instance ([#9155](https://github.com/leanprover-community/mathlib/pull/9155))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).
#### Estimated changes
Modified src/category_theory/preadditive/single_obj.lean




## [2021-09-12 02:16:49](https://github.com/leanprover-community/mathlib/commit/96c1d69)
doc(data/list/*): Elaborate module docstrings ([#9076](https://github.com/leanprover-community/mathlib/pull/9076))
Just adding some elaboration that @YaelDillies requested in [#8867](https://github.com/leanprover-community/mathlib/pull/8867), but which didn't get included before it was merged.
#### Estimated changes
Modified src/data/list/alist.lean


Modified src/data/list/of_fn.lean




## [2021-09-12 01:07:51](https://github.com/leanprover-community/mathlib/commit/f75bee3)
chore(ring_theory/noetherian): fix URL ([#9149](https://github.com/leanprover-community/mathlib/pull/9149))
#### Estimated changes
Modified src/ring_theory/noetherian.lean




## [2021-09-11 22:57:24](https://github.com/leanprover-community/mathlib/commit/55aaebe)
feat(data/real/ennreal): add `contravariant_class ennreal ennreal (+) (<)` ([#9143](https://github.com/leanprover-community/mathlib/pull/9143))
## `algebra/ordered_monoid`
* use `≠ ⊤`/`≠ ⊥` instead of `< ⊤`/`⊥ <`  in the assumptions of `with_top.add_lt_add_iff_left`, `with_top.add_lt_add_iff_right`, `with_bot.add_lt_add_iff_left`, and `with_bot.add_lt_add_iff_right`;
* add instances for `contravariant_class (with_top α) (with_top α) (+) (<)` and `contravariant_class (with_bot α) (with_bot α) (+) (<)`.
## `data/real/ennreal`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `ennreal.add_lt_add_iff_left`, `ennreal.add_lt_add_iff_right`, `ennreal.lt_add_right`,
* add an instance `contravariant_class ℝ≥0∞ ℝ≥0∞ (+) (<)`;
* rename `ennreal.sub_infty` to `ennreal.sub_top`.
## `measure_theory/measure/outer_measure`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `induced_outer_measure_exists_set`;
## `topology/metric_space/emetric_space`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `emetric.ball_subset`.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+/\- *lemma* with_bot.add_lt_add_iff_left
- \+/\- *lemma* with_bot.add_lt_add_iff_right
- \+/\- *lemma* with_top.add_lt_add_iff_left
- \+/\- *lemma* with_top.add_lt_add_iff_right

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_lt_add_iff_left
- \+/\- *lemma* ennreal.add_lt_add_iff_right
- \+/\- *lemma* ennreal.lt_add_right
- \- *lemma* ennreal.sub_infty
- \+ *lemma* ennreal.sub_top

Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measure/content.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/regular.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/order/filter/ennreal.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.ball_subset

Modified src/topology/metric_space/hausdorff_distance.lean




## [2021-09-11 21:56:23](https://github.com/leanprover-community/mathlib/commit/c0693ca)
chore(analysis/calculus/*): add `filter.eventually_eq.deriv` etc. ([#9131](https://github.com/leanprover-community/mathlib/pull/9131))
* add `filter.eventually_eq.deriv` and `filter.eventually_eq.fderiv`;
* add `times_cont_diff_within_at.eventually` and `times_cont_diff_at.eventually`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/times_cont_diff.lean




## [2021-09-11 20:56:00](https://github.com/leanprover-community/mathlib/commit/1605b85)
feat(data/real/ennreal): add ennreal.to_(nn)real_inv and ennreal.to_(nn)real_div ([#9144](https://github.com/leanprover-community/mathlib/pull/9144))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_nnreal_div
- \+ *lemma* ennreal.to_nnreal_inv
- \+ *lemma* ennreal.to_real_div
- \+ *lemma* ennreal.to_real_inv



## [2021-09-11 17:31:41](https://github.com/leanprover-community/mathlib/commit/b9ad733)
split(analysis/convex/combination): split off `analysis.convex.basic` ([#9115](https://github.com/leanprover-community/mathlib/pull/9115))
This moves `finset.center_mass` into its own new file.
About the copyright header, `finset.center_mass` comes from [#1804](https://github.com/leanprover-community/mathlib/pull/1804), which was written by Yury in December 2019.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \- *lemma* convex.center_mass_mem
- \- *lemma* convex.sum_mem
- \- *lemma* convex_hull_basis_eq_std_simplex
- \- *lemma* convex_hull_eq
- \- *lemma* convex_hull_eq_union_convex_hull_finite_subsets
- \- *lemma* convex_iff_sum_mem
- \- *lemma* convex_on.exists_ge_of_center_mass
- \- *lemma* convex_on.exists_ge_of_mem_convex_hull
- \- *lemma* convex_on.map_center_mass_le
- \- *lemma* convex_on.map_sum_le
- \- *lemma* finset.center_mass_empty
- \- *lemma* finset.center_mass_eq_of_sum_1
- \- *lemma* finset.center_mass_filter_ne_zero
- \- *lemma* finset.center_mass_insert
- \- *lemma* finset.center_mass_ite_eq
- \- *lemma* finset.center_mass_mem_convex_hull
- \- *lemma* finset.center_mass_pair
- \- *lemma* finset.center_mass_segment'
- \- *lemma* finset.center_mass_segment
- \- *lemma* finset.center_mass_singleton
- \- *lemma* finset.center_mass_smul
- \- *lemma* finset.center_mass_subset
- \- *lemma* finset.convex_hull_eq
- \- *lemma* mem_Icc_of_mem_std_simplex
- \- *lemma* set.finite.convex_hull_eq
- \- *lemma* set.finite.convex_hull_eq_image

Modified src/analysis/convex/caratheodory.lean


Added src/analysis/convex/combination.lean
- \+ *lemma* convex.center_mass_mem
- \+ *lemma* convex.sum_mem
- \+ *lemma* convex_hull_basis_eq_std_simplex
- \+ *lemma* convex_hull_eq
- \+ *lemma* convex_hull_eq_union_convex_hull_finite_subsets
- \+ *lemma* convex_iff_sum_mem
- \+ *lemma* convex_on.exists_ge_of_center_mass
- \+ *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+ *lemma* convex_on.map_center_mass_le
- \+ *lemma* convex_on.map_sum_le
- \+ *lemma* finset.center_mass_empty
- \+ *lemma* finset.center_mass_eq_of_sum_1
- \+ *lemma* finset.center_mass_filter_ne_zero
- \+ *lemma* finset.center_mass_insert
- \+ *lemma* finset.center_mass_ite_eq
- \+ *lemma* finset.center_mass_mem_convex_hull
- \+ *lemma* finset.center_mass_pair
- \+ *lemma* finset.center_mass_segment'
- \+ *lemma* finset.center_mass_segment
- \+ *lemma* finset.center_mass_singleton
- \+ *lemma* finset.center_mass_smul
- \+ *lemma* finset.center_mass_subset
- \+ *lemma* finset.convex_hull_eq
- \+ *lemma* mem_Icc_of_mem_std_simplex
- \+ *lemma* set.finite.convex_hull_eq
- \+ *lemma* set.finite.convex_hull_eq_image

Modified src/analysis/convex/integral.lean


Modified src/analysis/convex/topology.lean




## [2021-09-11 15:52:14](https://github.com/leanprover-community/mathlib/commit/62de591)
feat(interval_integral): generalize change of variables ([#8869](https://github.com/leanprover-community/mathlib/pull/8869))
* Generalizes `interval_integral.integral_comp_mul_deriv'`.
In this version:
(1) `f` need not be differentiable at the endpoints of `[a,b]`, only continuous,
(2) I removed the `measurable_at_filter` assumption
(3) I assumed that `g` was continuous on `f '' [a,b]`, instead of continuous at every point of `f '' [a,b]` (which differs in the endpoints).
This was possible after @sgouezel's PR [#7978](https://github.com/leanprover-community/mathlib/pull/7978).
The proof was a lot longer/messier than expected. Under these assumptions we have to be careful to sometimes take one-sided derivatives. For example, we cannot take the 2-sided derivative of `λ u, ∫ x in f a..u, g x` when `u` is the maximum/minimum of `f` on `[a, b]`.
@urkud: I needed more `FTC_filter` classes, namely for closed intervals (to be precise: `FTC_filter x (𝓝[[a, b]] x) (𝓝[[a, b]] x)`). Was there a conscious reason to exclude these classes? (The documentation explicitly enumerates the existing instances.)
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_deriv_within_at.Ioi_iff_Ioo
- \+ *theorem* has_deriv_within_at_congr_set

Modified src/data/set/intervals/unordered_interval.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.continuous_on_primitive_interval'
- \+ *theorem* interval_integral.integral_comp_mul_deriv''

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* continuous_on.measurable_at_filter_nhds_within

Modified src/order/filter/interval.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_eq_nhds_within'

Modified src/topology/instances/real.lean
- \+ *lemma* real.image_interval
- \+ *lemma* real.image_interval_eq_Icc
- \+ *lemma* real.interval_subset_image_interval



## [2021-09-11 14:06:54](https://github.com/leanprover-community/mathlib/commit/6823886)
feat(measure_theory/function/conditional_expectation): conditional expectation of an indicator ([#8920](https://github.com/leanprover-community/mathlib/pull/8920))
This PR builds `condexp_ind  (s : set α) : E →L[ℝ] α →₁[μ] E`, which takes `x : E` to the conditional expectation of the indicator of the set `s` with value `x`, seen as an element of `α →₁[μ] E`.
This linear map will be used in a next PR to define the conditional expectation from L1 to L1, by using the same extension mechanism as in the Bochner integral construction.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.ae_measurable'.const_inner
- \+ *lemma* measure_theory.ae_measurable'.measurable_comp
- \+/\- *lemma* measure_theory.ae_measurable'.measurable_mk
- \+ *lemma* measure_theory.condexp_L2_ae_eq_zero_of_ae_eq_zero
- \+ *lemma* measure_theory.condexp_L2_comp_continuous_linear_map
- \+ *lemma* measure_theory.condexp_L2_const_inner
- \+ *lemma* measure_theory.condexp_L2_indicator_ae_eq_smul
- \+ *lemma* measure_theory.condexp_L2_indicator_eq_to_span_singleton_comp
- \+ *def* measure_theory.condexp_ind
- \+ *def* measure_theory.condexp_ind_L1
- \+ *lemma* measure_theory.condexp_ind_L1_add
- \+ *lemma* measure_theory.condexp_ind_L1_disjoint_union
- \+ *def* measure_theory.condexp_ind_L1_fin
- \+ *lemma* measure_theory.condexp_ind_L1_fin_add
- \+ *lemma* measure_theory.condexp_ind_L1_fin_ae_eq_condexp_ind_smul
- \+ *lemma* measure_theory.condexp_ind_L1_fin_disjoint_union
- \+ *lemma* measure_theory.condexp_ind_L1_fin_smul'
- \+ *lemma* measure_theory.condexp_ind_L1_fin_smul
- \+ *lemma* measure_theory.condexp_ind_L1_of_measurable_set_of_measure_ne_top
- \+ *lemma* measure_theory.condexp_ind_L1_of_measure_eq_top
- \+ *lemma* measure_theory.condexp_ind_L1_of_not_measurable_set
- \+ *lemma* measure_theory.condexp_ind_L1_smul'
- \+ *lemma* measure_theory.condexp_ind_L1_smul
- \+ *lemma* measure_theory.condexp_ind_ae_eq_condexp_ind_smul
- \+ *lemma* measure_theory.condexp_ind_disjoint_union
- \+ *lemma* measure_theory.condexp_ind_disjoint_union_apply
- \+ *lemma* measure_theory.condexp_ind_empty
- \+ *lemma* measure_theory.condexp_ind_smul'
- \+ *def* measure_theory.condexp_ind_smul
- \+ *lemma* measure_theory.condexp_ind_smul_add
- \+ *lemma* measure_theory.condexp_ind_smul_ae_eq_smul
- \+ *lemma* measure_theory.condexp_ind_smul_empty
- \+ *lemma* measure_theory.condexp_ind_smul_smul'
- \+ *lemma* measure_theory.condexp_ind_smul_smul
- \+ *lemma* measure_theory.continuous_condexp_ind_L1
- \+ *lemma* measure_theory.integrable_condexp_L2_indicator
- \+ *lemma* measure_theory.integrable_condexp_ind_smul
- \+ *lemma* measure_theory.integral_condexp_L2_eq
- \+ *lemma* measure_theory.integral_condexp_L2_eq_of_fin_meas_real
- \+ *lemma* measure_theory.lintegral_nnnorm_condexp_L2_indicator_le
- \+ *lemma* measure_theory.lintegral_nnnorm_condexp_L2_indicator_le_real
- \+ *lemma* measure_theory.lintegral_nnnorm_condexp_L2_le
- \+ *lemma* measure_theory.lintegral_nnnorm_condexp_ind_smul_le
- \+ *lemma* measure_theory.norm_condexp_ind_L1_fin_le
- \+ *lemma* measure_theory.norm_condexp_ind_L1_le
- \+ *lemma* measure_theory.norm_condexp_ind_apply_le
- \+ *lemma* measure_theory.norm_condexp_ind_le
- \+ *lemma* measure_theory.set_lintegral_nnnorm_condexp_L2_indicator_le
- \+ *lemma* measure_theory.set_lintegral_nnnorm_condexp_ind_smul_le

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* continuous_linear_map.add_comp_Lp
- \+ *lemma* continuous_linear_map.add_comp_LpL
- \+ *lemma* continuous_linear_map.coe_fn_comp_Lp'
- \+ *lemma* continuous_linear_map.coe_fn_comp_LpL
- \+ *lemma* continuous_linear_map.smul_comp_Lp
- \+ *lemma* continuous_linear_map.smul_comp_LpL
- \+ *lemma* continuous_linear_map.smul_comp_LpL_apply
- \+ *lemma* measure_theory.indicator_const_Lp_eq_to_span_singleton_comp_Lp

Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* continuous_linear_map.set_integral_comp_Lp



## [2021-09-11 12:23:38](https://github.com/leanprover-community/mathlib/commit/241ee9e)
feat(data/finsupp): more lemmas about `α →₀ ℕ` ([#9137](https://github.com/leanprover-community/mathlib/pull/9137))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.le_iff'
- \+ *lemma* finsupp.nat_add_sub_assoc
- \+ *lemma* finsupp.nat_sub_self
- \+ *lemma* finsupp.single_le_iff



## [2021-09-11 12:23:37](https://github.com/leanprover-community/mathlib/commit/e009354)
chore(data/mv_polynomials): golf, add a lemma ([#9132](https://github.com/leanprover-community/mathlib/pull/9132))
* add `monoid_algebra.support_mul_single`;
* transfer a few more lemmas from `monoid_algebra` to `add_monoid_algebra`
* add `mv_polynomial.support_mul_X`
* reuse a proof.
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *lemma* add_monoid_algebra.mul_single_apply
- \+ *lemma* add_monoid_algebra.single_mul_apply
- \+ *lemma* add_monoid_algebra.support_mul_single
- \+ *lemma* monoid_algebra.support_mul_single

Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.support_mul_X



## [2021-09-11 12:23:36](https://github.com/leanprover-community/mathlib/commit/d72119c)
feat(data/mv_polynomial/equiv): empty_equiv ([#9122](https://github.com/leanprover-community/mathlib/pull/9122))
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *def* mv_polynomial.is_empty_alg_equiv
- \+ *def* mv_polynomial.is_empty_ring_equiv
- \- *def* mv_polynomial.pempty_alg_equiv
- \- *def* mv_polynomial.pempty_ring_equiv

Modified src/data/mv_polynomial/funext.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-09-11 11:48:10](https://github.com/leanprover-community/mathlib/commit/f318e5d)
chore(ring_theory/artinian): typo ([#9140](https://github.com/leanprover-community/mathlib/pull/9140))
#### Estimated changes
Modified src/ring_theory/artinian.lean
- \+ *theorem* set_has_minimal_iff_artinian
- \- *theorem* set_has_minimal_iff_artinrian



## [2021-09-11 04:25:26](https://github.com/leanprover-community/mathlib/commit/579ca5e)
chore(combinatorics/simple_graph): rename sym to symm ([#9134](https://github.com/leanprover-community/mathlib/pull/9134))
The naming convention for symmetry of a relation in mathlib seems to be symm, so this commit renames the axiom for the symmetry of the adjacency relation of a simple graph to this.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/combinatorics/simple_graph/basic.lean
- \+/\- *lemma* simple_graph.adj_comm
- \+/\- *lemma* simple_graph.adj_symm
- \+/\- *def* simple_graph.edge_set

Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/combinatorics/simple_graph/subgraph.lean
- \+/\- *lemma* simple_graph.subgraph.adj_symm
- \+/\- *def* simple_graph.subgraph.edge_set



## [2021-09-11 04:25:25](https://github.com/leanprover-community/mathlib/commit/919aad2)
refactor(topology/path_connected): make `path` extend `C(I, X)` ([#9133](https://github.com/leanprover-community/mathlib/pull/9133))
#### Estimated changes
Modified src/topology/path_connected.lean
- \+/\- *lemma* path.coe_mk



## [2021-09-11 04:25:24](https://github.com/leanprover-community/mathlib/commit/8413622)
chore(algebra/ordered_smul): reduce instance assumptions & delete duplicated instances ([#9130](https://github.com/leanprover-community/mathlib/pull/9130))
These instances all assumed `semiring R` superfluously:
* `order_dual.smul_with_zero`
* `order_dual.mul_action`
* `order_dual.mul_action_with_zero`
* `order_dual.distrib_mul_action`
and these instances were duplicates (with their `opposite.`-less counterparts):
* `opposite.mul_zero_class.to_opposite_smul_with_zero`
* `opposite.monoid_with_zero.to_opposite_mul_action_with_zero`
* `opposite.semiring.to_opposite_module`
#### Estimated changes
Modified src/algebra/module/basic.lean


Modified src/algebra/module/opposites.lean


Modified src/algebra/ordered_smul.lean


Modified src/algebra/smul_with_zero.lean




## [2021-09-11 04:25:23](https://github.com/leanprover-community/mathlib/commit/2e9f708)
feat(algebra/ordered_monoid): order_embedding.mul_left ([#9127](https://github.com/leanprover-community/mathlib/pull/9127))
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean
- \+ *def* order_embedding.mul_left
- \+ *def* order_embedding.mul_right



## [2021-09-11 03:46:20](https://github.com/leanprover-community/mathlib/commit/4c96b8a)
feat(measure_theory/measure/set_integral): new lemma integral_Union ([#9093](https://github.com/leanprover-community/mathlib/pull/9093))
#### Estimated changes
Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.has_sum_integral_Union
- \+ *lemma* measure_theory.integral_Union
- \+ *lemma* measure_theory.integral_finset_bUnion
- \+ *lemma* measure_theory.integral_fintype_Union



## [2021-09-11 01:08:22](https://github.com/leanprover-community/mathlib/commit/426227d)
chore(algebra/group/basic): add 3 `simp` attrs ([#9050](https://github.com/leanprover-community/mathlib/pull/9050))
#### Estimated changes
Modified archive/imo/imo2008_q2.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* sub_add_sub_cancel
- \+ *lemma* sub_sub_cancel_left
- \+/\- *lemma* sub_sub_sub_cancel_right

Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean




## [2021-09-10 20:31:43](https://github.com/leanprover-community/mathlib/commit/e4ca117)
feat(ring_theory/algebraic): is_algebraic_of_larger_base ([#9109](https://github.com/leanprover-community/mathlib/pull/9109))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_algebraic_of_larger_field



## [2021-09-10 18:48:06](https://github.com/leanprover-community/mathlib/commit/7500529)
refactor(analysis/convex/basic): generalize segments to vector spaces ([#9094](https://github.com/leanprover-community/mathlib/pull/9094))
`segment` and `open_segment` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary ordered_semirings in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid` where possible.
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean
- \+/\- *lemma* mem_pos_tangent_cone_at_of_segment_subset'
- \+/\- *lemma* mem_pos_tangent_cone_at_of_segment_subset

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* mem_tangent_cone_of_segment_subset

Modified src/analysis/convex/basic.lean
- \+ *lemma* Icc_subset_segment
- \+ *lemma* Ioo_subset_open_segment
- \+/\- *lemma* convex.add
- \+/\- *lemma* convex.combo_self
- \+/\- *lemma* convex.mem_Icc
- \+/\- *lemma* convex.mem_Ico
- \+/\- *lemma* convex.mem_Ioc
- \+/\- *lemma* convex.mem_Ioo
- \+/\- *lemma* convex.segment_subset
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex_empty
- \+/\- *lemma* convex_open_segment
- \+/\- *lemma* convex_segment
- \+/\- *lemma* left_mem_open_segment_iff
- \+/\- *lemma* left_mem_segment
- \+/\- *lemma* mem_open_segment_of_ne_left_right
- \+/\- *lemma* mem_segment_translate
- \+/\- *def* open_segment
- \+/\- *lemma* open_segment_eq_Ioo'
- \+/\- *lemma* open_segment_eq_Ioo
- \+/\- *lemma* open_segment_image
- \+ *lemma* open_segment_subset_Ioo
- \+ *lemma* open_segment_subset_iff_segment_subset
- \+/\- *lemma* open_segment_translate_preimage
- \+/\- *lemma* right_mem_segment
- \+/\- *def* segment
- \+/\- *lemma* segment_eq_Icc'
- \+/\- *lemma* segment_eq_Icc
- \+/\- *lemma* segment_eq_image'
- \+/\- *lemma* segment_eq_image
- \+/\- *lemma* segment_eq_interval
- \+/\- *lemma* segment_image
- \+/\- *lemma* segment_same
- \+ *lemma* segment_subset_Icc
- \+/\- *lemma* segment_symm
- \+/\- *lemma* segment_translate_image
- \+/\- *lemma* segment_translate_preimage

Modified src/analysis/convex/extreme.lean


Modified src/data/set/intervals/unordered_interval.lean




## [2021-09-10 18:48:05](https://github.com/leanprover-community/mathlib/commit/0e014ba)
feat(combinatorics/simple_graph/adj_matrix): more lemmas ([#9021](https://github.com/leanprover-community/mathlib/pull/9021))
#### Estimated changes
Modified src/combinatorics/simple_graph/adj_matrix.lean
- \+ *def* matrix.compl
- \+ *lemma* matrix.compl_apply
- \+ *lemma* matrix.compl_apply_diag
- \+ *lemma* matrix.is_adj_matrix.adj_matrix_to_graph_eq
- \+ *lemma* matrix.is_adj_matrix.apply_diag_ne
- \+ *lemma* matrix.is_adj_matrix.apply_ne_one_iff
- \+ *lemma* matrix.is_adj_matrix.apply_ne_zero_iff
- \+ *lemma* matrix.is_adj_matrix.compl
- \+ *def* matrix.is_adj_matrix.to_graph
- \+ *lemma* matrix.is_adj_matrix.to_graph_compl_eq
- \+ *lemma* matrix.is_adj_matrix_compl
- \+ *lemma* matrix.is_symm_compl
- \+/\- *def* simple_graph.adj_matrix
- \+/\- *lemma* simple_graph.adj_matrix_apply
- \+/\- *lemma* simple_graph.adj_matrix_dot_product
- \+/\- *lemma* simple_graph.adj_matrix_mul_apply
- \+/\- *theorem* simple_graph.adj_matrix_mul_self_apply_self
- \+/\- *lemma* simple_graph.adj_matrix_mul_vec_apply
- \+/\- *lemma* simple_graph.adj_matrix_mul_vec_const_apply
- \+/\- *lemma* simple_graph.adj_matrix_mul_vec_const_apply_of_regular
- \+/\- *lemma* simple_graph.adj_matrix_vec_mul_apply
- \+/\- *lemma* simple_graph.dot_product_adj_matrix
- \+ *lemma* simple_graph.is_adj_matrix_adj_matrix
- \+ *lemma* simple_graph.is_symm_adj_matrix
- \+/\- *lemma* simple_graph.mul_adj_matrix_apply
- \+ *lemma* simple_graph.to_graph_adj_matrix_eq
- \+/\- *theorem* simple_graph.trace_adj_matrix
- \+/\- *theorem* simple_graph.transpose_adj_matrix



## [2021-09-10 16:18:38](https://github.com/leanprover-community/mathlib/commit/a949b57)
feat(data/mv_polynomial): mv_polynomial.subsingleton ([#9124](https://github.com/leanprover-community/mathlib/pull/9124))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean




## [2021-09-10 16:18:37](https://github.com/leanprover-community/mathlib/commit/92e7bbe)
refactor(algebra/group/units): better defeq for is_unit.unit ([#9112](https://github.com/leanprover-community/mathlib/pull/9112))
Make sure that, for `x : M` and `h : is_unit M`, then `is_unit.unit x h : M` is defeq to `x`.
#### Estimated changes
Modified src/algebra/group/units.lean


Modified src/category_theory/endomorphism.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean




## [2021-09-10 16:18:36](https://github.com/leanprover-community/mathlib/commit/574864d)
feat(topology/compact_open): express the compact-open topology as an Inf of topologies ([#9106](https://github.com/leanprover-community/mathlib/pull/9106))
For `f : C(α, β)` and a set `s` in `α`, define `f.restrict s` to be the restriction of `f` as an element of `C(s, β)`.  This PR then proves that the compact-open topology on `C(α, β)` is equal to the infimum of the induced compact-open topologies from the restrictions to compact sets.
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.compact_open_eq_Inf_induced
- \+ *lemma* continuous_map.nhds_compact_open_eq_Inf_nhds_induced
- \+ *lemma* continuous_map.tendsto_compact_open_iff_forall

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.coe_restrict
- \+ *def* continuous_map.restrict



## [2021-09-10 16:18:35](https://github.com/leanprover-community/mathlib/commit/d2afdc5)
feat(ring_theory/dedekind_domain): add proof that `I \sup J` is the product of `factors I \inf factors J` for `I, J` ideals in a Dedekind Domain  ([#9055](https://github.com/leanprover-community/mathlib/pull/9055))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* multiset.prod_ne_zero_of_prime

Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* count_le_of_ideal_ge
- \+ *lemma* factors_prod_factors_eq_factors
- \+ *lemma* prod_factors_eq_self
- \+ *lemma* sup_eq_prod_inf_factors

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.zero_not_mem_factors



## [2021-09-10 15:18:22](https://github.com/leanprover-community/mathlib/commit/6d2cbf9)
feat(ring_theory/artinian): Artinian modules ([#9009](https://github.com/leanprover-community/mathlib/pull/9009))
#### Estimated changes
Added src/ring_theory/artinian.lean
- \+ *theorem* is_artinian.bijective_of_injective_endomorphism
- \+ *lemma* is_artinian.disjoint_partial_infs_eventually_top
- \+ *theorem* is_artinian.exists_endomorphism_iterate_ker_sup_range_eq_top
- \+ *lemma* is_artinian.finite_of_linear_independent
- \+ *lemma* is_artinian.induction
- \+ *theorem* is_artinian.surjective_of_injective_endomorphism
- \+ *theorem* is_artinian_iff_well_founded
- \+ *lemma* is_artinian_of_fg_of_artinian'
- \+ *theorem* is_artinian_of_fg_of_artinian
- \+ *lemma* is_artinian_of_fintype
- \+ *theorem* is_artinian_of_injective
- \+ *lemma* is_artinian_of_le
- \+ *theorem* is_artinian_of_linear_equiv
- \+ *theorem* is_artinian_of_quotient_of_artinian
- \+ *theorem* is_artinian_of_range_eq_ker
- \+ *theorem* is_artinian_of_submodule_of_artinian
- \+ *theorem* is_artinian_of_surjective
- \+ *theorem* is_artinian_of_tower
- \+ *theorem* is_artinian_ring_iff
- \+ *theorem* is_artinian_ring_of_ring_equiv
- \+ *theorem* is_artinian_ring_of_surjective
- \+ *theorem* is_artinian_span_of_finite
- \+ *theorem* monotone_stabilizes_iff_artinian
- \+ *theorem* ring.is_artinian_of_zero_eq_one
- \+ *theorem* set_has_minimal_iff_artinrian



## [2021-09-10 15:18:21](https://github.com/leanprover-community/mathlib/commit/2410c1f)
feat(topology/homotopy): Define homotopy between functions ([#8947](https://github.com/leanprover-community/mathlib/pull/8947))
More PRs are to come, with homotopy between paths etc. So this will probably become a folder at some point, but for now I've just put it in `topology/homotopy.lean`. There's also not that much API here at the moment, more will be added later on.
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.curry_apply

Added src/topology/homotopy.lean
- \+ *lemma* continuous_map.homotopy.apply_one
- \+ *lemma* continuous_map.homotopy.apply_zero
- \+ *def* continuous_map.homotopy.curry
- \+ *lemma* continuous_map.homotopy.ext
- \+ *def* continuous_map.homotopy.extend
- \+ *lemma* continuous_map.homotopy.extend_apply_one
- \+ *lemma* continuous_map.homotopy.extend_apply_zero
- \+ *def* continuous_map.homotopy.refl
- \+ *def* continuous_map.homotopy.symm
- \+ *lemma* continuous_map.homotopy.symm_apply
- \+ *lemma* continuous_map.homotopy.symm_symm
- \+ *lemma* continuous_map.homotopy.symm_trans
- \+ *lemma* continuous_map.homotopy.to_continuous_map_apply
- \+ *def* continuous_map.homotopy.trans
- \+ *lemma* continuous_map.homotopy.trans_apply

Modified src/topology/unit_interval.lean
- \+ *lemma* unit_interval.coe_symm_eq
- \+ *lemma* unit_interval.mul_pos_mem_iff
- \+ *lemma* unit_interval.symm_symm
- \+ *lemma* unit_interval.two_mul_sub_one_mem_iff



## [2021-09-10 13:08:34](https://github.com/leanprover-community/mathlib/commit/5ce9280)
feat(measure_theory/integral/bochner): generalize the Bochner integral construction ([#8939](https://github.com/leanprover-community/mathlib/pull/8939))
The construction of the Bochner integral is generalized to a process extending a set function `T : set α → (E →L[ℝ] F)` from sets to functions in L1. The integral corresponds to `T s` equal to the linear map `E →L[ℝ] E` with value `λ x, (μ s).to_real • x`.
The conditional expectation from L1 to L1 will be defined by taking for `T` the function `condexp_ind : set α → (E →L[ℝ] α →₁[μ] E)` defined in [#8920](https://github.com/leanprover-community/mathlib/pull/8920) .
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.inv_singleton

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.to_L1_smul'

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.L1.integral_eq_set_to_L1
- \+ *lemma* measure_theory.L1.simple_func.integral_eq_set_to_L1s
- \+ *lemma* measure_theory.dominated_fin_meas_additive_weighted_smul
- \+ *lemma* measure_theory.integral_eq_set_to_fun
- \+ *lemma* measure_theory.norm_weighted_smul_le
- \+/\- *lemma* measure_theory.simple_func.integral_congr
- \+ *lemma* measure_theory.simple_func.integral_def
- \+ *lemma* measure_theory.simple_func.integral_eq
- \+/\- *lemma* measure_theory.simple_func.integral_sub
- \+ *lemma* measure_theory.simple_func.norm_set_to_simple_func_le_integral_norm
- \+/\- *def* measure_theory.simple_func.pos_part
- \+ *def* measure_theory.weighted_smul
- \+ *lemma* measure_theory.weighted_smul_add_measure
- \+ *lemma* measure_theory.weighted_smul_apply
- \+ *lemma* measure_theory.weighted_smul_congr
- \+ *lemma* measure_theory.weighted_smul_empty
- \+ *lemma* measure_theory.weighted_smul_null
- \+ *lemma* measure_theory.weighted_smul_smul
- \+ *lemma* measure_theory.weighted_smul_union
- \+ *lemma* measure_theory.weighted_smul_zero_measure

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.range_eq_empty_of_is_empty

Added src/measure_theory/integral/set_to_l1.lean
- \+ *def* measure_theory.L1.set_to_L1'
- \+ *def* measure_theory.L1.set_to_L1
- \+ *lemma* measure_theory.L1.set_to_L1_eq_set_to_L1'
- \+ *lemma* measure_theory.L1.set_to_L1_eq_set_to_L1s_clm
- \+ *lemma* measure_theory.L1.set_to_L1_smul
- \+ *lemma* measure_theory.L1.set_to_fun_eq_set_to_L1
- \+ *lemma* measure_theory.L1.simple_func.norm_eq_sum_mul
- \+ *lemma* measure_theory.L1.simple_func.norm_set_to_L1s_le
- \+ *def* measure_theory.L1.simple_func.set_to_L1s
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_add
- \+ *def* measure_theory.L1.simple_func.set_to_L1s_clm'
- \+ *def* measure_theory.L1.simple_func.set_to_L1s_clm
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_congr
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_eq_set_to_simple_func
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_smul
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_smul_real
- \+ *def* measure_theory.dominated_fin_meas_additive
- \+ *def* measure_theory.fin_meas_additive
- \+ *lemma* measure_theory.map_Union_fin_meas_set_eq_sum
- \+ *lemma* measure_theory.map_empty_eq_zero_of_map_union
- \+ *def* measure_theory.set_to_fun
- \+ *lemma* measure_theory.set_to_fun_add
- \+ *lemma* measure_theory.set_to_fun_congr_ae
- \+ *lemma* measure_theory.set_to_fun_eq
- \+ *lemma* measure_theory.set_to_fun_neg
- \+ *lemma* measure_theory.set_to_fun_non_ae_measurable
- \+ *lemma* measure_theory.set_to_fun_smul
- \+ *lemma* measure_theory.set_to_fun_sub
- \+ *lemma* measure_theory.set_to_fun_undef
- \+ *lemma* measure_theory.set_to_fun_zero
- \+ *lemma* measure_theory.simple_func.map_set_to_simple_func
- \+ *lemma* measure_theory.simple_func.norm_set_to_simple_func_le_sum_mul_norm
- \+ *lemma* measure_theory.simple_func.norm_set_to_simple_func_le_sum_op_norm
- \+ *def* measure_theory.simple_func.set_to_simple_func
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_add
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_add_left'
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_add_left
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_congr'
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_congr
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_eq_sum_filter
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_mono
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_neg
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_smul
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_smul_real
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_sub
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_zero
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_zero_apply

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.measure_inter_lt_top
- \+ *lemma* measure_theory.measure_inter_ne_top
- \+ *lemma* measure_theory.measure_union_lt_top
- \+ *lemma* measure_theory.measure_union_lt_top_iff
- \+ *lemma* measure_theory.measure_union_ne_top



## [2021-09-10 13:08:33](https://github.com/leanprover-community/mathlib/commit/56ff42b)
feat(linear_algebra/matrix/transvection): matrices are generated by transvections and diagonal matrices ([#8898](https://github.com/leanprover-community/mathlib/pull/8898))
One version of Gauss' pivot: any matrix can be obtained starting from a diagonal matrix and doing elementary moves on rows and columns. Phrased in terms of multiplication by transvections.
#### Estimated changes
Modified src/algebra/lie/classical.lean
- \- *lemma* lie_algebra.special_linear.E_apply_one
- \- *lemma* lie_algebra.special_linear.E_apply_zero
- \- *lemma* lie_algebra.special_linear.E_diag_zero
- \- *lemma* lie_algebra.special_linear.E_trace_zero
- \+/\- *lemma* lie_algebra.special_linear.Eb_val

Modified src/data/matrix/basis.lean
- \+ *lemma* matrix.std_basis_matrix.apply_of_col_ne
- \+ *lemma* matrix.std_basis_matrix.apply_of_ne
- \+ *lemma* matrix.std_basis_matrix.apply_of_row_ne
- \+ *lemma* matrix.std_basis_matrix.apply_same
- \+ *lemma* matrix.std_basis_matrix.diag_zero
- \+ *lemma* matrix.std_basis_matrix.mul_left_apply_of_ne
- \+ *lemma* matrix.std_basis_matrix.mul_left_apply_same
- \+ *lemma* matrix.std_basis_matrix.mul_of_ne
- \+ *lemma* matrix.std_basis_matrix.mul_right_apply_of_ne
- \+ *lemma* matrix.std_basis_matrix.mul_right_apply_same
- \+ *lemma* matrix.std_basis_matrix.mul_same
- \+ *lemma* matrix.std_basis_matrix.trace_zero

Modified src/data/matrix/block.lean
- \+ *def* matrix.is_two_block_diagonal

Modified src/data/nat/basic.lean
- \+ *def* nat.decreasing_induction'
- \+ *def* nat.le_rec_on'

Modified src/data/option/basic.lean
- \+ *lemma* option.to_list_none
- \+ *lemma* option.to_list_some

Added src/linear_algebra/matrix/transvection.lean
- \+ *lemma* matrix.det_transvection_of_ne
- \+ *lemma* matrix.diagonal_transvection_induction
- \+ *lemma* matrix.diagonal_transvection_induction_of_det_ne_zero
- \+ *lemma* matrix.mul_transvection_apply_of_ne
- \+ *lemma* matrix.mul_transvection_apply_same
- \+ *lemma* matrix.pivot.exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec
- \+ *lemma* matrix.pivot.exists_is_two_block_diagonal_of_ne_zero
- \+ *theorem* matrix.pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
- \+ *theorem* matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
- \+ *lemma* matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
- \+ *lemma* matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
- \+ *lemma* matrix.pivot.is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row
- \+ *def* matrix.pivot.list_transvec_col
- \+ *lemma* matrix.pivot.list_transvec_col_mul_last_col
- \+ *lemma* matrix.pivot.list_transvec_col_mul_last_row
- \+ *lemma* matrix.pivot.list_transvec_col_mul_last_row_drop
- \+ *lemma* matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_col
- \+ *lemma* matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_row
- \+ *def* matrix.pivot.list_transvec_row
- \+ *lemma* matrix.pivot.mul_list_transvec_row_last_col
- \+ *lemma* matrix.pivot.mul_list_transvec_row_last_col_take
- \+ *lemma* matrix.pivot.mul_list_transvec_row_last_row
- \+ *lemma* matrix.pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal
- \+ *def* matrix.transvection
- \+ *lemma* matrix.transvection_mul_apply_of_ne
- \+ *lemma* matrix.transvection_mul_apply_same
- \+ *lemma* matrix.transvection_mul_transvection_same
- \+ *lemma* matrix.transvection_struct.det_to_matrix_prod
- \+ *lemma* matrix.transvection_struct.inv_mul
- \+ *lemma* matrix.transvection_struct.mul_inv
- \+ *lemma* matrix.transvection_struct.mul_sum_inl_to_matrix_prod
- \+ *lemma* matrix.transvection_struct.prod_mul_reverse_inv_prod
- \+ *def* matrix.transvection_struct.reindex_equiv
- \+ *lemma* matrix.transvection_struct.reverse_inv_prod_mul_prod
- \+ *def* matrix.transvection_struct.sum_inl
- \+ *lemma* matrix.transvection_struct.sum_inl_to_matrix_prod_mul
- \+ *def* matrix.transvection_struct.to_matrix
- \+ *lemma* matrix.transvection_struct.to_matrix_mk
- \+ *lemma* matrix.transvection_struct.to_matrix_reindex_equiv
- \+ *lemma* matrix.transvection_struct.to_matrix_reindex_equiv_prod
- \+ *lemma* matrix.transvection_struct.to_matrix_sum_inl
- \+ *lemma* matrix.transvection_zero
- \+ *lemma* matrix.update_row_eq_transvection

Modified src/ring_theory/matrix_algebra.lean




## [2021-09-10 10:53:36](https://github.com/leanprover-community/mathlib/commit/a057a8e)
feat(ring_theory/norm): `norm R x = 0 ↔ x = 0` ([#9042](https://github.com/leanprover-community/mathlib/pull/9042))
Nonzero values of `S / R` have nonzero norm over `R`.
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+/\- *lemma* algebra.norm_apply
- \+ *lemma* algebra.norm_eq_zero_iff'
- \+ *lemma* algebra.norm_eq_zero_iff
- \+ *lemma* algebra.norm_eq_zero_iff_of_basis
- \+ *lemma* algebra.norm_ne_zero_iff_of_basis



## [2021-09-10 07:18:23](https://github.com/leanprover-community/mathlib/commit/37e17c5)
feat(measure_theory/integral/lebesgue): add some lintegral lemmas ([#9064](https://github.com/leanprover-community/mathlib/pull/9064))
This PR contains some lemmas useful for [#9065](https://github.com/leanprover-community/mathlib/pull/9065).
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_eq_top_of_measure_eq_top_pos
- \- *lemma* measure_theory.lintegral_in_measure_zero
- \+ *lemma* measure_theory.set_lintegral_empty
- \+ *lemma* measure_theory.set_lintegral_eq_const
- \+ *lemma* measure_theory.set_lintegral_measure_zero
- \+ *lemma* measure_theory.set_lintegral_univ



## [2021-09-10 07:18:22](https://github.com/leanprover-community/mathlib/commit/ae86776)
feat(measure_theory/measure/vector_measure): define mutually singular for vector measures ([#8896](https://github.com/leanprover-community/mathlib/pull/8896))
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean
- \+ *lemma* measure_theory.signed_measure.absolutely_continuous_ennreal_iff
- \- *lemma* measure_theory.signed_measure.absolutely_continuous_iff
- \+ *lemma* measure_theory.signed_measure.mutually_singular_ennreal_iff
- \+ *lemma* measure_theory.signed_measure.mutually_singular_iff
- \+ *lemma* measure_theory.signed_measure.null_of_total_variation_zero

Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.mutually_singular.add_left
- \+ *lemma* measure_theory.vector_measure.mutually_singular.add_right
- \+ *lemma* measure_theory.vector_measure.mutually_singular.mk
- \+ *lemma* measure_theory.vector_measure.mutually_singular.smul_left
- \+ *lemma* measure_theory.vector_measure.mutually_singular.smul_right
- \+ *lemma* measure_theory.vector_measure.mutually_singular.symm
- \+ *lemma* measure_theory.vector_measure.mutually_singular.zero_left
- \+ *lemma* measure_theory.vector_measure.mutually_singular.zero_right
- \+ *def* measure_theory.vector_measure.mutually_singular



## [2021-09-10 02:16:47](https://github.com/leanprover-community/mathlib/commit/aec02d8)
chore(scripts): update nolints.txt ([#9126](https://github.com/leanprover-community/mathlib/pull/9126))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-09-09 20:12:35](https://github.com/leanprover-community/mathlib/commit/4d88ae8)
feat(tactic/lint): better fails_quickly linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932))
This linter catches a lot more loops.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/tactic/lint/type_classes.lean


Modified test/lint.lean


Modified test/lint_coe_t.lean




## [2021-09-09 17:58:39](https://github.com/leanprover-community/mathlib/commit/138d98b)
feat(ring_theory/mv_polynomial): linear_independent_X ([#9118](https://github.com/leanprover-community/mathlib/pull/9118))
#### Estimated changes
Modified src/ring_theory/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.linear_independent_X



## [2021-09-09 16:13:53](https://github.com/leanprover-community/mathlib/commit/b9fcf9b)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate_mul_distrib ([#8682](https://github.com/leanprover-community/mathlib/pull/8682))
We prove that the adjugate of a matrix distributes over the product. To do so, a separate file 
`linear_algebra.matrix.polynomial` states some general facts about the polynomial `det (t I + A)`.
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_mul_distrib
- \+ *lemma* matrix.adjugate_pow

Added src/linear_algebra/matrix/polynomial.lean
- \+ *lemma* polynomial.coeff_det_X_add_C_card
- \+ *lemma* polynomial.coeff_det_X_add_C_zero
- \+ *lemma* polynomial.leading_coeff_det_X_one_add_C
- \+ *lemma* polynomial.nat_degree_det_X_add_C_le



## [2021-09-09 14:10:32](https://github.com/leanprover-community/mathlib/commit/2331607)
feat(group_theory/sub{monoid,group}): pointwise actions on `add_sub{monoid,group}`s and `sub{monoid,group,module,semiring,ring,algebra}`s ([#8945](https://github.com/leanprover-community/mathlib/pull/8945))
This adds the pointwise actions characterized by `↑(m • S) = (m • ↑S : set R)` on:
* `submonoid`
* `subgroup`
* `add_submonoid`
* `add_subgroup`
* `submodule` ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Lost.20instance/near/249467913))
* `subsemiring`
* `subring`
* `subalgebra`
within the locale `pointwise` (which must be open to state the RHS of the characterization above anyway).
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_pointwise_smul
- \+ *lemma* subalgebra.map_id
- \+ *lemma* subalgebra.map_map
- \+ *lemma* subalgebra.pointwise_smul_to_submodule
- \+ *lemma* subalgebra.pointwise_smul_to_subring
- \+ *lemma* subalgebra.pointwise_smul_to_subsemiring
- \+ *lemma* subalgebra.smul_mem_pointwise_smul

Modified src/algebra/group_ring_action.lean
- \+ *lemma* subring.coe_pointwise_smul
- \+ *lemma* subring.pointwise_smul_to_add_subgroup
- \+ *lemma* subring.pointwise_smul_to_subsemiring
- \+ *lemma* subring.smul_mem_pointwise_smul
- \+ *lemma* subsemiring.coe_pointwise_smul
- \+ *lemma* subsemiring.pointwise_smul_to_add_submonoid
- \+ *lemma* subsemiring.smul_mem_pointwise_smul

Modified src/group_theory/group_action/defs.lean
- \+ *def* mul_distrib_mul_action.to_monoid_End
- \- *lemma* mul_distrib_mul_action.to_monoid_hom_one

Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.coe_pointwise_smul
- \+ *lemma* add_subgroup.pointwise_smul_to_add_submonoid
- \+ *lemma* add_subgroup.smul_mem_pointwise_smul
- \+ *lemma* subgroup.coe_pointwise_smul
- \+ *lemma* subgroup.pointwise_smul_to_submonoid
- \+ *lemma* subgroup.smul_mem_pointwise_smul

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* add_submonoid.coe_pointwise_smul
- \+ *lemma* add_submonoid.smul_mem_pointwise_smul
- \+ *lemma* submonoid.coe_pointwise_smul
- \+ *lemma* submonoid.smul_mem_pointwise_smul

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.coe_pointwise_smul
- \+ *lemma* submodule.pointwise_smul_to_add_subgroup
- \+ *lemma* submodule.pointwise_smul_to_add_submonoid
- \+ *lemma* submodule.smul_le_self_of_tower
- \+ *lemma* submodule.smul_mem_pointwise_smul



## [2021-09-09 12:54:22](https://github.com/leanprover-community/mathlib/commit/1825671)
feat(ring_theory/unique_factorization_domain): add lemma that a member of `factors a` divides `a` ([#9108](https://github.com/leanprover-community/mathlib/pull/9108))
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.dvd_of_mem_factors



## [2021-09-09 09:36:30](https://github.com/leanprover-community/mathlib/commit/e597b75)
feat(algebra/algebra/subalgebra): mem_under ([#9107](https://github.com/leanprover-community/mathlib/pull/9107))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.mem_under



## [2021-09-09 09:36:29](https://github.com/leanprover-community/mathlib/commit/694da7e)
feat(ring_theory): the surjective image of a PID is a PID ([#9069](https://github.com/leanprover-community/mathlib/pull/9069))
If the preimage of an ideal/submodule under a surjective map is principal, so is the original ideal. Therefore, the image of a principal ideal domain under a surjective ring hom is again a PID.
#### Estimated changes
Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* ideal.is_principal.of_comap
- \+ *lemma* ideal.span_singleton_generator
- \+ *lemma* is_principal_ideal_ring.of_surjective
- \+ *lemma* submodule.is_principal.of_comap



## [2021-09-09 09:36:28](https://github.com/leanprover-community/mathlib/commit/1356397)
refactor(linear_algebra/*): linear_equiv.of_bijective over semirings ([#9061](https://github.com/leanprover-community/mathlib/pull/9061))
`linear_equiv.of_injective` and `linear_equiv.of_bijective`
took as assumption `f.ker = \bot`,
which is equivalent to injectivity of `f` over rings,
but not over semirings.
This PR changes the assumption to `injective f`.
For reasons of symmetry,
the surjectivity assumption is also switched to `surjective f`.
As a consequence, this PR also renames:
* `linear_equiv_of_ker_eq_bot` to `linear_equiv_of_injective`
* `linear_equiv_of_ker_eq_bot_apply` to `linear_equiv_of_injective_apply`
#### Estimated changes
Modified src/algebra/category/Module/subobject.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.arrow_congr
- \+/\- *lemma* linear_equiv.arrow_congr_apply
- \+/\- *lemma* linear_equiv.arrow_congr_symm_apply
- \+/\- *theorem* linear_equiv.of_injective_apply

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.nondegenerate.ker_eq_bot

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* linear_equiv.coe_of_injective_endo
- \+/\- *lemma* linear_equiv.of_injective_endo_left_inv
- \+/\- *lemma* linear_equiv.of_injective_endo_right_inv
- \+ *lemma* linear_map.linear_equiv_of_injective_apply
- \- *lemma* linear_map.linear_equiv_of_ker_eq_bot_apply

Modified src/linear_algebra/free_module_pid.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/projection.lean


Modified src/ring_theory/noetherian.lean




## [2021-09-09 07:32:09](https://github.com/leanprover-community/mathlib/commit/f6ccb6b)
chore(ring_theory/polynomial/cyclotomic): golf+remove `nontrivial` ([#9090](https://github.com/leanprover-community/mathlib/pull/9090))
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic.lean
- \- *lemma* cyclotomic.irreducible
- \- *lemma* cyclotomic_eq_minpoly
- \- *lemma* minpoly_primitive_root_dvd_cyclotomic
- \+ *lemma* polynomial.cyclotomic.irreducible
- \+/\- *lemma* polynomial.cyclotomic_eq_X_pow_sub_one_div
- \+/\- *lemma* polynomial.cyclotomic_eq_geom_sum
- \+ *lemma* polynomial.cyclotomic_eq_minpoly
- \+/\- *lemma* polynomial.eq_cyclotomic_iff
- \+ *lemma* polynomial.int_coeff_of_cyclotomic'
- \- *lemma* polynomial.int_coeff_of_cyclotomic
- \+ *lemma* polynomial.minpoly_primitive_root_dvd_cyclotomic



## [2021-09-09 07:32:08](https://github.com/leanprover-community/mathlib/commit/90475a9)
refactor(data/matrix): put std_basis_matrix in its own file ([#9088](https://github.com/leanprover-community/mathlib/pull/9088))
The authors here are recovered from the git history.
I've avoided the temptation to generalize typeclasses in this PR; the lemmas are copied to this file unmodified.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *lemma* matrix.matrix_eq_sum_std_basis
- \- *lemma* matrix.smul_std_basis_matrix
- \- *lemma* matrix.std_basis_eq_basis_mul_basis
- \- *def* matrix.std_basis_matrix
- \- *lemma* matrix.std_basis_matrix_add
- \- *lemma* matrix.std_basis_matrix_zero

Added src/data/matrix/basis.lean
- \+ *lemma* matrix.matrix_eq_sum_std_basis
- \+ *lemma* matrix.smul_std_basis_matrix
- \+ *lemma* matrix.std_basis_eq_basis_mul_basis
- \+ *def* matrix.std_basis_matrix
- \+ *lemma* matrix.std_basis_matrix_add
- \+ *lemma* matrix.std_basis_matrix_zero

Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean




## [2021-09-09 07:32:07](https://github.com/leanprover-community/mathlib/commit/9568977)
fix(group_theory/group_action): generalize assumptions on `ite_smul` and `smul_ite` ([#9085](https://github.com/leanprover-community/mathlib/pull/9085))
#### Estimated changes
Modified src/group_theory/group_action/defs.lean




## [2021-09-09 07:32:06](https://github.com/leanprover-community/mathlib/commit/3e10324)
feat(data/polynomial/taylor): Taylor expansion of polynomials ([#9000](https://github.com/leanprover-community/mathlib/pull/9000))
#### Estimated changes
Modified src/data/polynomial/hasse_deriv.lean


Added src/data/polynomial/taylor.lean
- \+ *lemma* polynomial.eq_zero_of_hasse_deriv_eq_zero
- \+ *def* polynomial.taylor
- \+ *lemma* polynomial.taylor_C
- \+ *lemma* polynomial.taylor_X
- \+ *lemma* polynomial.taylor_apply
- \+ *lemma* polynomial.taylor_coeff
- \+ *lemma* polynomial.taylor_coeff_one
- \+ *lemma* polynomial.taylor_coeff_zero
- \+ *lemma* polynomial.taylor_eval
- \+ *lemma* polynomial.taylor_eval_sub
- \+ *lemma* polynomial.taylor_injective
- \+ *lemma* polynomial.taylor_one



## [2021-09-09 06:19:13](https://github.com/leanprover-community/mathlib/commit/e336caf)
chore(algebra/floor): add a trivial lemma ([#9098](https://github.com/leanprover-community/mathlib/pull/9098))
* add `nat_ceil_eq_zero`;
* add `@[simp]` to `nat_ceil_le`.
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *theorem* nat_ceil_eq_zero
- \+/\- *theorem* nat_ceil_le



## [2021-09-09 04:01:05](https://github.com/leanprover-community/mathlib/commit/796efae)
feat(data/real/sqrt): `nnreal.coe_sqrt` and `nnreal.sqrt_eq_rpow` ([#9025](https://github.com/leanprover-community/mathlib/pull/9025))
Also rename a few lemmas:
* `nnreal.mul_sqrt_self` -> `nnreal.mul_self_sqrt` to follow `real.mul_self_sqrt`
* `real.sqrt_le` -> `real.sqrt_le_sqrt_iff`
* `real.sqrt_lt` -> `real.sqrt_lt_sqrt_iff`
and provide a few more for commodity:
* `nnreal.sqrt_sq`
* `nnreal.sq_sqrt`
* `real.sqrt_lt_sqrt`
* `real.sqrt_lt_sqrt_iff_of_pos`
* `nnreal.sqrt_le_sqrt_iff`
* `nnreal.sqrt_lt_sqrt_iff`
Closes [#8016](https://github.com/leanprover-community/mathlib/pull/8016)
#### Estimated changes
Modified archive/imo/imo2008_q3.lean


Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/pow.lean
- \+ *lemma* nnreal.sqrt_eq_rpow
- \+/\- *lemma* real.sqrt_eq_rpow

Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/real/sqrt.lean
- \+ *lemma* nnreal.mul_self_sqrt
- \- *lemma* nnreal.mul_sqrt_self
- \+ *lemma* nnreal.sq_sqrt
- \+ *lemma* nnreal.sqrt_le_sqrt_iff
- \+ *lemma* nnreal.sqrt_lt_sqrt_iff
- \+ *lemma* nnreal.sqrt_sq
- \+ *lemma* real.coe_sqrt
- \+/\- *theorem* real.sq_sqrt
- \- *theorem* real.sqrt_le
- \+ *theorem* real.sqrt_le_sqrt_iff
- \- *theorem* real.sqrt_lt
- \+ *theorem* real.sqrt_lt_sqrt
- \+ *theorem* real.sqrt_lt_sqrt_iff
- \+ *theorem* real.sqrt_lt_sqrt_iff_of_pos



## [2021-09-09 02:59:19](https://github.com/leanprover-community/mathlib/commit/15b6c56)
refactor(category_theory/limits/types): Refactor filtered colimits. ([#9100](https://github.com/leanprover-community/mathlib/pull/9100))
- Rename `filtered_colimit.r` into `filtered_colimit.rel`, to match up with `quot.rel`,
- Rename lemma `r_ge`,
- Abstract out lemma `eqv_gen_quot_rel_of_rel` from later proof.
#### Estimated changes
Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.filtered_colimit.eqv_gen_quot_rel_of_rel
- \+/\- *lemma* category_theory.limits.types.filtered_colimit.is_colimit_eq_iff
- \+ *lemma* category_theory.limits.types.filtered_colimit.rel_of_quot_rel



## [2021-09-09 02:09:44](https://github.com/leanprover-community/mathlib/commit/cfc6b48)
chore(scripts): update nolints.txt ([#9105](https://github.com/leanprover-community/mathlib/pull/9105))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-09-09 00:00:26](https://github.com/leanprover-community/mathlib/commit/49cf386)
feat(measure_theory/measure/vector_measure): add `absolutely_continuous.add` and `absolutely_continuous.smul` ([#9086](https://github.com/leanprover-community/mathlib/pull/9086))
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.add
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.neg_left
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.neg_right
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.smul
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.sub



## [2021-09-08 21:47:47](https://github.com/leanprover-community/mathlib/commit/87e7a0c)
feat(linear_algebra/matrix): `M` maps some `v ≠ 0` to zero iff `det M = 0` ([#9041](https://github.com/leanprover-community/mathlib/pull/9041))
A result I have wanted for a long time: the two notions of a "singular" matrix are equivalent over an integral domain. Namely, a matrix `M` is singular iff it maps some nonzero vector to zero, which happens iff its determinant is zero.
Here, I find such a `v` by going through the field of fractions, where everything is a lot easier because all injective endomorphisms are automorphisms. Maybe a bit overkill (and unsatisfying constructively), but it works and is a lot nicer to write out than explicitly finding an element of the kernel.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.dot_product_mul_vec
- \+ *lemma* matrix.dot_product_single
- \+ *lemma* matrix.mul_vec_smul
- \+ *lemma* matrix.single_dot_product
- \+ *lemma* matrix.vec_mul_smul
- \+ *lemma* ring_hom.map_dot_product
- \+ *lemma* ring_hom.map_mul_vec
- \+ *lemma* ring_hom.map_vec_mul

Modified src/linear_algebra/bilinear_form.lean
- \+ *theorem* matrix.nondegenerate.to_bilin'

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.det_ne_zero_of_left_inverse
- \+ *lemma* matrix.det_ne_zero_of_right_inverse
- \+ *theorem* matrix.eq_zero_of_mul_vec_eq_zero
- \+ *theorem* matrix.eq_zero_of_vec_mul_eq_zero
- \+ *lemma* matrix.nondegenerate.eq_zero_of_ortho
- \+ *lemma* matrix.nondegenerate.exists_not_ortho_of_ne_zero
- \+ *def* matrix.nondegenerate
- \+/\- *theorem* matrix.nondegenerate_of_det_ne_zero

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.ker_to_lin'_eq_bot_iff

Modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+ *lemma* matrix.exists_mul_vec_eq_zero_iff
- \+ *lemma* matrix.exists_mul_vec_eq_zero_iff_aux
- \+ *lemma* matrix.exists_vec_mul_eq_zero_iff
- \+ *theorem* matrix.nondegenerate_iff_det_ne_zero



## [2021-09-08 21:02:02](https://github.com/leanprover-community/mathlib/commit/ab0a295)
feat(linear_algebra/matrix): some bounds on the determinant of matrices ([#9029](https://github.com/leanprover-community/mathlib/pull/9029))
This PR shows that matrices with bounded entries also have bounded determinants.
`matrix.det_le` is the most generic version of these results, which we specialise in two steps to `matrix.det_sum_smul_le`. In a follow-up PR we will connect this to `algebra.left_mul_matrix` to provide an upper bound on `algebra.norm`.
#### Estimated changes
Added src/linear_algebra/matrix/absolute_value.lean
- \+ *lemma* matrix.det_le
- \+ *lemma* matrix.det_sum_le
- \+ *lemma* matrix.det_sum_smul_le



## [2021-09-08 17:50:43](https://github.com/leanprover-community/mathlib/commit/4222c32)
lint(testing/slim_check/*): break long lines ([#9091](https://github.com/leanprover-community/mathlib/pull/9091))
#### Estimated changes
Modified src/testing/slim_check/gen.lean


Modified src/testing/slim_check/testable.lean
- \+/\- *def* slim_check.minimize
- \+/\- *def* slim_check.minimize_aux
- \+/\- *def* slim_check.testable.check



## [2021-09-08 17:50:42](https://github.com/leanprover-community/mathlib/commit/56a59d3)
feat(data/polynomial/hasse_deriv): Hasse derivatives ([#8998](https://github.com/leanprover-community/mathlib/pull/8998))
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *def* polynomial.lsum

Added src/data/polynomial/hasse_deriv.lean
- \+ *lemma* polynomial.factorial_smul_hasse_deriv
- \+ *def* polynomial.hasse_deriv
- \+ *lemma* polynomial.hasse_deriv_C
- \+ *lemma* polynomial.hasse_deriv_X
- \+ *lemma* polynomial.hasse_deriv_apply
- \+ *lemma* polynomial.hasse_deriv_apply_one
- \+ *lemma* polynomial.hasse_deriv_coeff
- \+ *lemma* polynomial.hasse_deriv_comp
- \+ *lemma* polynomial.hasse_deriv_monomial
- \+ *lemma* polynomial.hasse_deriv_mul
- \+ *lemma* polynomial.hasse_deriv_one'
- \+ *lemma* polynomial.hasse_deriv_one
- \+ *lemma* polynomial.hasse_deriv_zero'
- \+ *lemma* polynomial.hasse_deriv_zero



## [2021-09-08 17:50:41](https://github.com/leanprover-community/mathlib/commit/42dda89)
feat(ring_theory/discrete_valuation_ring): is_Hausdorff ([#8994](https://github.com/leanprover-community/mathlib/pull/8994))
Discrete valuation rings are Hausdorff in the algebraic sense
that the intersection of all powers of the maximal ideal is 0.
#### Estimated changes
Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* irreducible.add_val_pow
- \+ *lemma* irreducible.maximal_ideal_eq



## [2021-09-08 16:06:33](https://github.com/leanprover-community/mathlib/commit/f4f1cd3)
feat(algebra/module/ordered): simple `smul` lemmas ([#9077](https://github.com/leanprover-community/mathlib/pull/9077))
These are the negative versions of the lemmas in `ordered_smul`, which suggests that both files should be merged.
Note however that, contrary to those, they need `module k M` instead of merely `smul_with_zero k M`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* neg_smul_neg

Modified src/algebra/module/ordered.lean
- \+ *lemma* eq_of_smul_eq_smul_of_neg_of_le
- \+ *lemma* lt_of_smul_lt_smul_of_nonpos
- \+ *lemma* lt_smul_iff_of_neg
- \+/\- *lemma* smul_le_smul_iff_of_neg
- \+ *lemma* smul_le_smul_of_nonpos
- \+ *lemma* smul_lt_iff_of_neg
- \+ *lemma* smul_lt_smul_iff_of_neg
- \+ *lemma* smul_lt_smul_of_neg
- \+ *lemma* smul_neg_iff_of_neg
- \+ *lemma* smul_neg_iff_of_pos
- \+ *lemma* smul_pos_iff_of_neg

Modified src/algebra/ordered_smul.lean
- \+ *lemma* lt_smul_iff_of_pos



## [2021-09-08 16:06:31](https://github.com/leanprover-community/mathlib/commit/76ab749)
feat(analysis/normed_space/operator_norm): variants of continuous_linear_map.lsmul and their properties ([#8984](https://github.com/leanprover-community/mathlib/pull/8984))
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.norm_to_span_singleton
- \+ *lemma* continuous_linear_map.to_span_singleton_add
- \+ *lemma* continuous_linear_map.to_span_singleton_apply
- \+ *lemma* continuous_linear_map.to_span_singleton_smul'
- \+ *lemma* continuous_linear_map.to_span_singleton_smul



## [2021-09-08 14:01:04](https://github.com/leanprover-community/mathlib/commit/146dddc)
feat(measure_theory/group/arithmetic): add more to_additive attributes for actions ([#9032](https://github.com/leanprover-community/mathlib/pull/9032))
Introduce additivised versions of some more smul classes and corresponding instances and lemmas for different types of (measurable) additive actions.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* pi.vadd_apply

Modified src/algebra/module/pi.lean
- \+/\- *lemma* pi.smul_apply

Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/measure/haar.lean
- \+ *lemma* measure_theory.measure.add_haar_measure_apply



## [2021-09-08 14:01:03](https://github.com/leanprover-community/mathlib/commit/99b70d9)
feat(data/(fin)set/basic): `image` and `mem` lemmas ([#9031](https://github.com/leanprover-community/mathlib/pull/9031))
I rename `set.mem_image_of_injective` to `function.injective.mem_set_image_iff` to allow dot notation and fit the new  `function.injective.mem_finset_image_iff`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* function.injective.mem_finset_image

Modified src/data/set/basic.lean
- \+ *theorem* function.injective.mem_set_image
- \- *theorem* set.mem_image_of_injective
- \+ *lemma* subsingleton.mem_iff_nonempty
- \+ *lemma* subtype.coe_image_of_subset

Modified src/data/set/function.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_iff_subset_compl_left
- \+ *lemma* set.disjoint_iff_subset_compl_right

Modified src/linear_algebra/affine_space/independent.lean




## [2021-09-08 14:01:01](https://github.com/leanprover-community/mathlib/commit/3d31c2d)
chore(linear_algebra/affine_space/independent): allow dot notation on affine_independent ([#8974](https://github.com/leanprover-community/mathlib/pull/8974))
This renames a few lemmas to make dot notation on `affine_independent` possible.
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean


Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine_independent.exists_unique_dist_eq
- \- *lemma* euclidean_geometry.exists_unique_dist_eq_of_affine_independent

Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_independent.affine_span_eq_of_le_of_card_eq_finrank_add_one
- \+ *lemma* affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one
- \+ *lemma* affine_independent.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one
- \+ *lemma* affine_independent.finrank_vector_span
- \+ *lemma* affine_independent.finrank_vector_span_image_finset
- \+ *lemma* affine_independent.vector_span_eq_of_le_of_card_eq_finrank_add_one
- \+ *lemma* affine_independent.vector_span_eq_top_of_card_eq_finrank_add_one
- \+ *lemma* affine_independent.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one
- \- *lemma* affine_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* affine_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* finrank_vector_span_image_finset_of_affine_independent
- \- *lemma* finrank_vector_span_of_affine_independent
- \- *lemma* vector_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* vector_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one
- \- *lemma* vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent.affine_span_disjoint_of_disjoint
- \+ *lemma* affine_independent.comp_embedding
- \+ *lemma* affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span
- \+ *lemma* affine_independent.not_mem_affine_span_diff
- \+ *lemma* affine_independent.of_set_of_injective
- \- *lemma* affine_independent_embedding_of_affine_independent
- \- *lemma* affine_independent_of_affine_independent_set_of_injective
- \- *lemma* affine_independent_of_subset_affine_independent
- \- *lemma* affine_independent_set_of_affine_independent
- \- *lemma* affine_independent_subtype_of_affine_independent
- \- *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \- *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \- *lemma* injective_of_affine_independent
- \- *lemma* mem_affine_span_iff_mem_of_affine_independent
- \- *lemma* not_mem_affine_span_diff_of_affine_independent



## [2021-09-08 14:00:59](https://github.com/leanprover-community/mathlib/commit/7a2ccb6)
feat(group_theory/group_action): Extract a smaller typeclass out of `mul_semiring_action` ([#8918](https://github.com/leanprover-community/mathlib/pull/8918))
This new typeclass, `mul_distrib_mul_action`, is satisfied by conjugation actions. This PR provides instances for:
* `mul_aut`
* `prod` of two types with a `mul_distrib_mul_action`
* `pi` of types with a `mul_distrib_mul_action`
* `units` of types with a `mul_distrib_mul_action`
* `ulift` of types with a `mul_distrib_mul_action`
* `opposite` of types with a `mul_distrib_mul_action`
* `sub(monoid|group|semiring|ring)`s of types with a `mul_distrib_mul_action`
* anything already satisfying a `mul_semiring_action`
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \- *lemma* list.smul_prod
- \+ *def* mul_distrib_mul_action.to_mul_equiv
- \- *lemma* multiset.smul_prod
- \+ *lemma* smul_inv''
- \- *lemma* smul_inv'
- \- *lemma* smul_mul'
- \- *lemma* smul_pow
- \- *lemma* smul_prod

Modified src/algebra/module/pi.lean


Modified src/algebra/module/ulift.lean


Modified src/algebra/opposites.lean


Modified src/algebra/polynomial/group_ring_action.lean


Modified src/data/equiv/mul_add_aut.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean


Modified src/group_theory/group_action/basic.lean
- \+ *lemma* finset.smul_prod
- \+ *lemma* list.smul_prod
- \+ *lemma* multiset.smul_prod
- \+ *lemma* smul_pow

Modified src/group_theory/group_action/defs.lean
- \+ *def* mul_distrib_mul_action.comp_hom
- \+ *def* mul_distrib_mul_action.to_monoid_hom
- \+ *lemma* mul_distrib_mul_action.to_monoid_hom_apply
- \+ *lemma* mul_distrib_mul_action.to_monoid_hom_one
- \+ *theorem* smul_div'
- \+ *theorem* smul_inv'
- \+ *theorem* smul_mul'

Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/group_action/units.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-09-08 14:00:58](https://github.com/leanprover-community/mathlib/commit/4c7d95f)
feat(analysis/normed_space/inner_product): reflections API ([#8884](https://github.com/leanprover-community/mathlib/pull/8884))
Reflections, as isometries of an inner product space, were defined in [#8660](https://github.com/leanprover-community/mathlib/pull/8660).  In this PR, various elementary lemmas filling out the API:
- Lemmas about reflection through a subspace K, of a point which is in (i) K itself; (ii) the orthogonal complement of K.
- Lemmas relating the orthogonal projection/reflection on the `submodule.map` of a subspace, with the orthogonal projection/reflection on the original subspace.
- Lemma characterizing the reflection in the trivial subspace.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthogonal_projection_eq_self_iff
- \+ *lemma* orthogonal_projection_map_apply
- \+ *lemma* reflection_bot
- \+ *lemma* reflection_eq_self_iff
- \+ *lemma* reflection_map
- \+ *lemma* reflection_map_apply
- \+ *lemma* reflection_mem_subspace_eq_self
- \+ *lemma* reflection_mem_subspace_orthogonal_complement_eq_neg
- \+ *lemma* reflection_mem_subspace_orthogonal_precomplement_eq_neg
- \+ *lemma* reflection_orthogonal_complement_singleton_eq_neg



## [2021-09-08 12:15:54](https://github.com/leanprover-community/mathlib/commit/71df310)
chore(*): remove instance binders in exists, for mathport ([#9083](https://github.com/leanprover-community/mathlib/pull/9083))
Per @digama0's request at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Instance.20binders.20in.20exists.
Instance binders under an "Exists" aren't allowed in Lean4, so we're backport removing them. I've just turned relevant `[X]` binders into `(_ : X)` binders, and it seems to all still work. (i.e. the instance binders weren't actually doing anything).
It turns out two of the problem binders were in `infi` or `supr`, not `Exists`, but I treated them the same way.
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean


Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/essentially_small.lean


Modified src/combinatorics/hales_jewett.lean


Modified src/group_theory/subgroup.lean


Modified src/order/extension.lean


Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* algebra.finite_presentation.iff_quotient_mv_polynomial'
- \+/\- *lemma* algebra.finite_type.iff_quotient_mv_polynomial'

Modified src/ring_theory/polynomial/dickson.lean


Modified src/topology/metric_space/basic.lean




## [2021-09-08 12:15:53](https://github.com/leanprover-community/mathlib/commit/3108153)
feat(linear_algebra/affine_space/independent): homotheties preserve affine independence ([#9070](https://github.com/leanprover-community/mathlib/pull/9070))
#### Estimated changes
Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_equiv.affine_independent_iff
- \+ *lemma* affine_map.homothety_affine_independent_iff



## [2021-09-08 12:15:52](https://github.com/leanprover-community/mathlib/commit/e4e07ea)
feat(ring_theory): `map f (span s) = span (f '' s)` ([#9068](https://github.com/leanprover-community/mathlib/pull/9068))
We already had this for submodules and linear maps, here it is for ideals and ring homs.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.submodule_span_eq

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.map_span

Modified src/ring_theory/localization.lean




## [2021-09-08 12:15:50](https://github.com/leanprover-community/mathlib/commit/aae2b37)
feat(field_theory/separable): a finite field extension in char 0 is separable ([#9066](https://github.com/leanprover-community/mathlib/pull/9066))
#### Estimated changes
Modified src/field_theory/separable.lean




## [2021-09-08 12:15:49](https://github.com/leanprover-community/mathlib/commit/157e99d)
feat(ring_theory): PIDs are Dedekind domains ([#9063](https://github.com/leanprover-community/mathlib/pull/9063))
We had all the ingredients ready for a while, apparently I just forgot to PR the instance itself.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean




## [2021-09-08 12:15:48](https://github.com/leanprover-community/mathlib/commit/c3f2c23)
feat(analysis/convex/basic): the affine image of the convex hull is the convex hull of the affine image ([#9057](https://github.com/leanprover-community/mathlib/pull/9057))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* affine_map.image_convex_hull



## [2021-09-08 12:15:46](https://github.com/leanprover-community/mathlib/commit/57a0789)
chore(topology/order): relate Sup and Inf of topologies to `generate_from` ([#9045](https://github.com/leanprover-community/mathlib/pull/9045))
Since there is a Galois insertion between `generate_from : set (set α) → topological_space α` and the "forgetful functor" `topological_space α → set (set α)`, all kinds of lemmas about the interaction of `generate_from` and the ordering on topologies automatically follow.  But it is hard to use the Galois insertion lemmas directly, because the Galois insertion is actually provided for the dual order on topologies, which confuses Lean.  Here we re-state most of the Galois insertion API in this special case.
#### Estimated changes
Modified src/topology/order.lean
- \+ *lemma* generate_from_Inter
- \+ *lemma* generate_from_Inter_of_generate_from_eq_self
- \+ *lemma* generate_from_Union
- \+ *lemma* generate_from_Union_is_open
- \+ *lemma* generate_from_inter
- \+ *lemma* generate_from_sUnion
- \+ *lemma* generate_from_set_of_is_open
- \+ *lemma* generate_from_surjective
- \+ *lemma* generate_from_union
- \+ *lemma* generate_from_union_is_open
- \+ *lemma* is_open_implies_is_open_iff
- \+ *lemma* left_inverse_generate_from
- \+ *lemma* set_of_is_open_Sup
- \+ *lemma* set_of_is_open_injective
- \+ *lemma* set_of_is_open_sup
- \+ *lemma* set_of_is_open_supr



## [2021-09-08 12:15:45](https://github.com/leanprover-community/mathlib/commit/a8c5c5a)
feat(algebra/module/basic): add `module.to_add_monoid_End` ([#8968](https://github.com/leanprover-community/mathlib/pull/8968))
I also removed `smul_add_hom_one` since it's a special case of the ring_hom.
I figured I'd replace a `simp` with a `rw` when fixing `finsupp.to_free_abelian_group_comp_to_finsupp` for this removal.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *def* module.to_add_monoid_End
- \- *lemma* smul_add_hom_one

Modified src/group_theory/free_abelian_group_finsupp.lean




## [2021-09-08 10:25:38](https://github.com/leanprover-community/mathlib/commit/4e8d966)
feat(algebra/subalgebra): add missing actions by and on subalgebras ([#9081](https://github.com/leanprover-community/mathlib/pull/9081))
For `S : subalgebra R A`, this adds the instances:
* for actions on subalgebras (generalizing the existing `algebra R S`):
  * `module R' S`
  * `algebra R' S`
  * `is_scalar_tower R' R S`
* for actions by subalgebras (generalizing the existing `algebra S α`):
  * `mul_action S α`
  * `smul_comm_class S α β`
  * `smul_comm_class α S β`
  * `is_scalar_tower S α β`
  * `has_faithful_scalar S α`
  * `distrib_mul_action S α`
  * `module S α`
This also removes the commutativity requirement on `A` for the `no_zero_smul_divisors S A` instance.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+/\- *lemma* subalgebra.coe_algebra_map
- \+/\- *lemma* subalgebra.coe_smul
- \+ *lemma* subalgebra.smul_def



## [2021-09-08 10:25:37](https://github.com/leanprover-community/mathlib/commit/585c5ad)
feat(data/finset): monotone maps preserve the maximum of a finset ([#9035](https://github.com/leanprover-community/mathlib/pull/9035))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.max'_image
- \+ *lemma* finset.min'_image



## [2021-09-08 08:23:11](https://github.com/leanprover-community/mathlib/commit/fc75aea)
feat(topology/algebra/ordered): `{prod,pi}.order_closed_topology` ([#9073](https://github.com/leanprover-community/mathlib/pull/9073))
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean




## [2021-09-08 08:23:10](https://github.com/leanprover-community/mathlib/commit/8341d16)
feat(linear_algebra/finite_dimensional): make finite_dimensional_bot an instance ([#9053](https://github.com/leanprover-community/mathlib/pull/9053))
This was previously made into a local instance in several places, but there appears to be no reason it can't be a global instance.
cf discussion at [#8884](https://github.com/leanprover-community/mathlib/pull/8884).
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/linear_algebra/finite_dimensional.lean
- \- *lemma* finite_dimensional_bot
- \- *lemma* subalgebra.finite_dimensional_bot



## [2021-09-08 08:23:08](https://github.com/leanprover-community/mathlib/commit/b4a88e2)
feat(data/equiv/derangements/basic): define derangements ([#7526](https://github.com/leanprover-community/mathlib/pull/7526))
This proves two formulas for the number of derangements on _n_ elements, and defines some combinatorial equivalences
involving derangements on α and derangements on certain subsets of α. This proves Theorem 88 on Freek's list.
#### Estimated changes
Added src/combinatorics/derangements/basic.lean
- \+ *def* derangements.at_most_one_fixed_point_equiv_sum_derangements
- \+ *def* derangements.derangements_option_equiv_sigma_at_most_one_fixed_point
- \+ *def* derangements.derangements_recursion_equiv
- \+ *def* derangements.equiv.remove_none.fiber
- \+ *lemma* derangements.equiv.remove_none.fiber_none
- \+ *lemma* derangements.equiv.remove_none.fiber_some
- \+ *lemma* derangements.equiv.remove_none.mem_fiber
- \+ *def* derangements
- \+ *def* equiv.derangements_congr
- \+ *lemma* mem_derangements_iff_fixed_points_eq_empty

Modified src/data/equiv/basic.lean
- \+ *def* equiv.sigma_option_equiv_of_some



## [2021-09-08 06:17:22](https://github.com/leanprover-community/mathlib/commit/189fe5b)
feat(data/nat/enat): refactor coe from nat to enat ([#9023](https://github.com/leanprover-community/mathlib/pull/9023))
The coercion from nat to enat was defined to be enat.some. But another
coercion could be inferred from the additive structure on enat, leading to
confusing goals of the form
`↑n = ↑n` where the two sides were not defeq.
We now make the coercion inferred from the additive structure the default, 
even though it is not computable.
A dedicated function `enat.some` is introduced, to be used whenever
computability is important.
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/data/nat/enat.lean
- \- *lemma* enat.coe_add
- \+ *lemma* enat.coe_coe_hom
- \+/\- *def* enat.coe_hom
- \+/\- *lemma* enat.coe_inj
- \- *lemma* enat.coe_one
- \- *lemma* enat.coe_zero
- \+/\- *lemma* enat.dom_coe
- \+ *lemma* enat.dom_of_le_coe
- \+/\- *lemma* enat.dom_of_le_some
- \+ *lemma* enat.dom_some
- \+/\- *lemma* enat.get_coe'
- \+/\- *lemma* enat.get_coe
- \+ *lemma* enat.get_eq_iff_eq_coe
- \+ *lemma* enat.get_eq_iff_eq_some
- \+/\- *lemma* enat.ne_top_iff
- \+ *def* enat.some
- \+ *lemma* enat.some_eq_coe
- \+/\- *lemma* enat.to_with_top_coe
- \+ *lemma* enat.to_with_top_some

Modified src/data/nat/multiplicity.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/separable.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.eq_coe_iff
- \- *lemma* multiplicity.eq_some_iff

Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/set_theory/cardinal.lean




## [2021-09-08 06:17:21](https://github.com/leanprover-community/mathlib/commit/cef862d)
feat(ring_theory/noetherian): is_noetherian_of_range_eq_ker ([#8988](https://github.com/leanprover-community/mathlib/pull/8988))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.map_sup_comap_of_surjective

Modified src/order/modular_lattice.lean
- \+ *theorem* eq_of_le_of_inf_le_of_sup_le
- \+ *theorem* inf_lt_inf_of_lt_of_sup_le_sup
- \+/\- *theorem* is_modular_lattice.sup_inf_sup_assoc
- \+ *theorem* sup_lt_sup_of_lt_of_inf_le_inf
- \+ *theorem* well_founded_gt_exact_sequence
- \+ *theorem* well_founded_lt_exact_sequence

Modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_of_range_eq_ker



## [2021-09-08 06:17:20](https://github.com/leanprover-community/mathlib/commit/4dc96e4)
feat(group_theory/index): define the index of a subgroup ([#8971](https://github.com/leanprover-community/mathlib/pull/8971))
Defines `subgroup.index` and proves various divisibility properties.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+/\- *lemma* subgroup.card_eq_card_quotient_mul_card_subgroup
- \+ *def* subgroup.quotient_equiv_prod_of_le'

Added src/group_theory/index.lean
- \+ *lemma* subgroup.index_dvd_card
- \+ *lemma* subgroup.index_dvd_of_le
- \+ *lemma* subgroup.index_eq_card
- \+ *lemma* subgroup.index_eq_mul_of_le
- \+ *lemma* subgroup.index_mul_card

Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_group.quotient_bot



## [2021-09-08 06:17:19](https://github.com/leanprover-community/mathlib/commit/ded0d64)
feat(number_theory): define "admissible" absolute values ([#8964](https://github.com/leanprover-community/mathlib/pull/8964))
We say an absolute value `abv : absolute_value R ℤ` is admissible if it agrees with the Euclidean domain structure on R (see also `is_euclidean` in [#8949](https://github.com/leanprover-community/mathlib/pull/8949)), and large enough sets of elements in `R^n` contain two elements whose remainders are close together.
Examples include `abs : ℤ → ℤ` and `card_pow_degree := λ (p : polynomial Fq), (q ^ p.degree : ℤ)`, where `Fq` is a finite field with `q` elements. (These two correspond to the number field and function field case respectively, in our proof that the class number of a global field is finite.) Proving these two are indeed admissible involves a lot of pushing values between `ℤ` and `ℝ`, but is otherwise not so exciting.
#### Estimated changes
Modified src/algebra/euclidean_absolute_value.lean


Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.coe_lt_degree

Added src/number_theory/class_number/admissible_abs.lean
- \+ *lemma* absolute_value.exists_partition_int

Added src/number_theory/class_number/admissible_absolute_value.lean
- \+ *lemma* absolute_value.is_admissible.exists_approx
- \+ *lemma* absolute_value.is_admissible.exists_approx_aux
- \+ *lemma* absolute_value.is_admissible.exists_partition

Added src/number_theory/class_number/admissible_card_pow_degree.lean
- \+ *lemma* polynomial.card_pow_degree_anti_archimedean
- \+ *lemma* polynomial.exists_approx_polynomial
- \+ *lemma* polynomial.exists_approx_polynomial_aux
- \+ *lemma* polynomial.exists_eq_polynomial
- \+ *lemma* polynomial.exists_partition_polynomial
- \+ *lemma* polynomial.exists_partition_polynomial_aux



## [2021-09-08 06:17:18](https://github.com/leanprover-community/mathlib/commit/ec51460)
feat(data/finset): define `finset.pimage` ([#8907](https://github.com/leanprover-community/mathlib/pull/8907))
#### Estimated changes
Added src/data/finset/pimage.lean
- \+ *lemma* finset.coe_pimage
- \+ *lemma* finset.mem_pimage
- \+ *def* finset.pimage
- \+ *lemma* finset.pimage_congr
- \+ *lemma* finset.pimage_empty
- \+ *lemma* finset.pimage_eq_image_filter
- \+ *lemma* finset.pimage_inter
- \+ *lemma* finset.pimage_mono
- \+ *lemma* finset.pimage_some
- \+ *lemma* finset.pimage_subset
- \+ *lemma* finset.pimage_union
- \+ *lemma* part.coe_to_finset
- \+ *lemma* part.mem_to_finset
- \+ *def* part.to_finset
- \+ *theorem* part.to_finset_none
- \+ *theorem* part.to_finset_some

Modified src/data/part.lean
- \+ *theorem* part.bind_of_mem
- \+ *lemma* part.eq_get_iff_mem
- \+ *lemma* part.get_eq_iff_mem
- \+/\- *lemma* part.get_or_else_none
- \+/\- *lemma* part.get_or_else_some
- \+/\- *def* part.map
- \+ *lemma* part.none_ne_some
- \+ *lemma* part.none_to_option
- \+/\- *def* part.restrict
- \+/\- *lemma* part.some_ne_none
- \+ *lemma* part.some_to_option

Modified src/logic/basic.lean
- \+ *theorem* and.exists



## [2021-09-08 04:46:13](https://github.com/leanprover-community/mathlib/commit/628969b)
chore(linear_algebra/basic): speed up slow decl ([#9060](https://github.com/leanprover-community/mathlib/pull/9060))
#### Estimated changes
Modified src/linear_algebra/basic.lean




## [2021-09-08 02:22:54](https://github.com/leanprover-community/mathlib/commit/782a20a)
chore(scripts): update nolints.txt ([#9079](https://github.com/leanprover-community/mathlib/pull/9079))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-09-07 23:04:14](https://github.com/leanprover-community/mathlib/commit/dcd8782)
feat(algebra/algebra): lemmas connecting `basis ι R A`, `no_zero_smul_divisors R A` and `injective (algebra_map R A)` ([#9039](https://github.com/leanprover-community/mathlib/pull/9039))
Additions:
 * `basis.algebra_map_injective`
 * `no_zero_smul_divisors.algebra_map_injective`
 * `no_zero_smul_divisors.iff_algebra_map_injective`
Renamed:
 * `algebra.no_zero_smul_divisors.of_algebra_map_injective` → `no_zero_smul_divisors.of_algebra_map_injective`
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* algebra.no_zero_smul_divisors.of_algebra_map_injective
- \+ *lemma* no_zero_smul_divisors.algebra_map_injective
- \+ *lemma* no_zero_smul_divisors.iff_algebra_map_injective
- \+ *lemma* no_zero_smul_divisors.of_algebra_map_injective

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* basis.algebra_map_injective



## [2021-09-07 21:34:33](https://github.com/leanprover-community/mathlib/commit/50f5d8b)
docs(linear_algebra/bilinear_map): fix inconsistency in docstring ([#9075](https://github.com/leanprover-community/mathlib/pull/9075))
#### Estimated changes
Modified src/linear_algebra/bilinear_map.lean




## [2021-09-07 21:34:32](https://github.com/leanprover-community/mathlib/commit/b0b0a24)
feat(data/int): absolute values and integers ([#9028](https://github.com/leanprover-community/mathlib/pull/9028))
We prove that an absolute value maps all `units ℤ` to `1`.
I added a new file since there is no neat place in the import hierarchy where this fit (the meet of `algebra.algebra.basic` and `data.int.cast`).
#### Estimated changes
Added src/data/int/absolute_value.lean
- \+ *lemma* absolute_value.map_units_int
- \+ *lemma* absolute_value.map_units_int_cast
- \+ *lemma* absolute_value.map_units_int_smul



## [2021-09-07 19:33:39](https://github.com/leanprover-community/mathlib/commit/fd453cf)
chore(data/set/basic): add some simp attrs ([#9074](https://github.com/leanprover-community/mathlib/pull/9074))
Also add `set.pairwise_on_union`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.diff_eq_self
- \+/\- *theorem* set.diff_inter_self
- \+/\- *theorem* set.diff_inter_self_eq_diff
- \+/\- *theorem* set.diff_self_inter
- \+ *lemma* set.pairwise_on_union
- \+ *lemma* set.pairwise_on_union_of_symmetric
- \+/\- *theorem* set.sep_subset



## [2021-09-07 16:31:29](https://github.com/leanprover-community/mathlib/commit/463e753)
feat(linear_algebra/finite_dimensional): generalisations to division_ring ([#8822](https://github.com/leanprover-community/mathlib/pull/8822))
I generalise a few results about finite dimensional modules from fields to division rings. Mostly this is me trying out @alexjbest's `generalisation_linter`. (review: it works really well, and is very helpful for finding the right home for lemmas, but it is slow).
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_eq_card_basis
- \- *lemma* dim_of_ring
- \+/\- *theorem* dim_quotient_le
- \+ *lemma* dim_self

Modified src/linear_algebra/finite_dimensional.lean
- \- *lemma* finite_dimensional.dim_eq_card_basis
- \+/\- *lemma* finite_dimensional.finite_dimensional_of_finrank
- \+/\- *lemma* finite_dimensional.finrank_eq_dim
- \- *lemma* finite_dimensional.finrank_of_field
- \+/\- *lemma* finite_dimensional.finrank_of_infinite_dimensional
- \+ *lemma* finite_dimensional.finrank_self
- \+/\- *lemma* finite_dimensional.of_finset_basis
- \+/\- *def* finite_dimensional

Modified src/measure_theory/measure/hausdorff.lean




## [2021-09-07 15:17:24](https://github.com/leanprover-community/mathlib/commit/9c886ff)
chore(ring_theory): typo fix ([#9067](https://github.com/leanprover-community/mathlib/pull/9067))
`principal_idea_ring` -> `principal_ideal_ring`
#### Estimated changes
Modified src/ring_theory/principal_ideal_domain.lean




## [2021-09-07 15:17:23](https://github.com/leanprover-community/mathlib/commit/f8cfed4)
feat(algebra/tropical/basic): define tropical semiring ([#8864](https://github.com/leanprover-community/mathlib/pull/8864))
Just the initial algebraic structures. Follow up PRs will provide these with a topology, prove that tropical polynomials can be interpreted as sums of affine maps, and further towards tropical geometry.
#### Estimated changes
Added src/algebra/tropical/basic.lean
- \+ *lemma* tropical.add_eq_iff
- \+ *lemma* tropical.add_eq_left
- \+ *lemma* tropical.add_eq_right
- \+ *lemma* tropical.add_eq_zero_iff
- \+ *lemma* tropical.add_pow
- \+ *lemma* tropical.add_self
- \+ *lemma* tropical.bit0
- \+ *lemma* tropical.injective_trop
- \+ *lemma* tropical.injective_untrop
- \+ *lemma* tropical.le_zero
- \+ *lemma* tropical.left_inverse_trop
- \+ *lemma* tropical.mul_eq_zero_iff
- \+ *lemma* tropical.right_inverse_trop
- \+ *lemma* tropical.succ_nsmul
- \+ *lemma* tropical.surjective_trop
- \+ *lemma* tropical.surjective_untrop
- \+ *def* tropical.trop
- \+ *lemma* tropical.trop_add_def
- \+ *lemma* tropical.trop_coe_ne_zero
- \+ *lemma* tropical.trop_eq_iff_eq_untrop
- \+ *def* tropical.trop_equiv
- \+ *lemma* tropical.trop_equiv_coe_fn
- \+ *lemma* tropical.trop_equiv_symm_coe_fn
- \+ *lemma* tropical.trop_inj_iff
- \+ *lemma* tropical.trop_injective
- \+ *lemma* tropical.trop_mul_def
- \+ *lemma* tropical.trop_nsmul
- \+ *def* tropical.trop_order_iso
- \+ *lemma* tropical.trop_order_iso_coe_fn
- \+ *lemma* tropical.trop_order_iso_symm_coe_fn
- \+ *def* tropical.trop_rec
- \+ *lemma* tropical.trop_top
- \+ *lemma* tropical.trop_untrop
- \+ *def* tropical.untrop
- \+ *lemma* tropical.untrop_add
- \+ *lemma* tropical.untrop_div
- \+ *lemma* tropical.untrop_eq_iff_eq_trop
- \+ *lemma* tropical.untrop_inj_iff
- \+ *lemma* tropical.untrop_injective
- \+ *lemma* tropical.untrop_inv
- \+ *lemma* tropical.untrop_le_iff
- \+ *lemma* tropical.untrop_mul
- \+ *lemma* tropical.untrop_one
- \+ *lemma* tropical.untrop_pow
- \+ *lemma* tropical.untrop_trop
- \+ *lemma* tropical.untrop_zero
- \+ *lemma* tropical.zero_ne_trop_coe
- \+ *def* tropical



## [2021-09-07 13:48:09](https://github.com/leanprover-community/mathlib/commit/eeb4bb6)
feat(algebra/big_operators): absolute values and big operators  ([#9027](https://github.com/leanprover-community/mathlib/pull/9027))
This PR extends `absolute_value.add_le` and `absolute_value.map_mul` to `finset.sum` and `finset.prod` respectively.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* absolute_value.map_prod
- \+ *lemma* absolute_value.sum_le



## [2021-09-07 11:06:56](https://github.com/leanprover-community/mathlib/commit/6c8203f)
chore(linear_algebra/bilinear_map): split off new file from linear_algebra/tensor_product ([#9054](https://github.com/leanprover-community/mathlib/pull/9054))
The first part of linear_algebra/tensor_product consisted of some basics on bilinear maps that are not directly related to the construction of the tensor product.
This PR moves them to a new file.
#### Estimated changes
Added src/linear_algebra/bilinear_map.lean
- \+ *def* linear_map.compl₂
- \+ *theorem* linear_map.compl₂_apply
- \+ *def* linear_map.compr₂
- \+ *theorem* linear_map.compr₂_apply
- \+ *theorem* linear_map.ext₂
- \+ *def* linear_map.flip
- \+ *theorem* linear_map.flip_apply
- \+ *theorem* linear_map.flip_inj
- \+ *lemma* linear_map.ker_lsmul
- \+ *def* linear_map.lcomp
- \+ *theorem* linear_map.lcomp_apply
- \+ *def* linear_map.lflip
- \+ *theorem* linear_map.lflip_apply
- \+ *def* linear_map.llcomp
- \+ *theorem* linear_map.llcomp_apply
- \+ *def* linear_map.lsmul
- \+ *theorem* linear_map.lsmul_apply
- \+ *lemma* linear_map.lsmul_injective
- \+ *theorem* linear_map.map_add₂
- \+ *theorem* linear_map.map_neg₂
- \+ *theorem* linear_map.map_smul₂
- \+ *theorem* linear_map.map_sub₂
- \+ *theorem* linear_map.map_sum₂
- \+ *theorem* linear_map.map_zero₂
- \+ *def* linear_map.mk₂'
- \+ *theorem* linear_map.mk₂'_apply
- \+ *def* linear_map.mk₂
- \+ *theorem* linear_map.mk₂_apply

Modified src/linear_algebra/tensor_product.lean
- \- *def* linear_map.compl₂
- \- *theorem* linear_map.compl₂_apply
- \- *def* linear_map.compr₂
- \- *theorem* linear_map.compr₂_apply
- \- *theorem* linear_map.ext₂
- \- *def* linear_map.flip
- \- *theorem* linear_map.flip_apply
- \- *theorem* linear_map.flip_inj
- \- *lemma* linear_map.ker_lsmul
- \- *def* linear_map.lcomp
- \- *theorem* linear_map.lcomp_apply
- \- *def* linear_map.lflip
- \- *theorem* linear_map.lflip_apply
- \- *def* linear_map.llcomp
- \- *theorem* linear_map.llcomp_apply
- \- *def* linear_map.lsmul
- \- *theorem* linear_map.lsmul_apply
- \- *lemma* linear_map.lsmul_injective
- \- *theorem* linear_map.map_add₂
- \- *theorem* linear_map.map_neg₂
- \- *theorem* linear_map.map_smul₂
- \- *theorem* linear_map.map_sub₂
- \- *theorem* linear_map.map_sum₂
- \- *theorem* linear_map.map_zero₂
- \- *def* linear_map.mk₂'
- \- *theorem* linear_map.mk₂'_apply
- \- *def* linear_map.mk₂
- \- *theorem* linear_map.mk₂_apply



## [2021-09-07 11:06:55](https://github.com/leanprover-community/mathlib/commit/0508c7b)
feat(analysis/specific_limits): add `set.countable.exists_pos_has_sum_le` ([#9052](https://github.com/leanprover-community/mathlib/pull/9052))
Add versions of `pos_sum_of_encodable` for countable sets.
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* set.countable.exists_pos_forall_sum_le
- \+ *lemma* set.countable.exists_pos_has_sum_le



## [2021-09-07 11:06:54](https://github.com/leanprover-community/mathlib/commit/98942ab)
feat(ring_theory): non-zero divisors are not zero ([#9043](https://github.com/leanprover-community/mathlib/pull/9043))
I'm kind of suprised we didn't have this before!
#### Estimated changes
Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* non_zero_divisors.coe_ne_zero
- \+ *lemma* non_zero_divisors.ne_zero



## [2021-09-07 11:06:53](https://github.com/leanprover-community/mathlib/commit/812ff38)
docs(algebra/ordered_ring): add module docstring ([#9030](https://github.com/leanprover-community/mathlib/pull/9030))
#### Estimated changes
Modified src/algebra/ordered_ring.lean




## [2021-09-07 11:06:52](https://github.com/leanprover-community/mathlib/commit/a84b538)
feat(algebra/algebra/subalgebra): inclusion map of subalgebras ([#9013](https://github.com/leanprover-community/mathlib/pull/9013))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_inclusion
- \+ *def* subalgebra.inclusion
- \+ *lemma* subalgebra.inclusion_inclusion
- \+ *lemma* subalgebra.inclusion_injective
- \+ *lemma* subalgebra.inclusion_right
- \+ *lemma* subalgebra.inclusion_self



## [2021-09-07 11:06:51](https://github.com/leanprover-community/mathlib/commit/d69c12e)
feat(ring_theory/ideal/local_ring): residue field is an algebra ([#8991](https://github.com/leanprover-community/mathlib/pull/8991))
Also, the kernel of a surjective map to a field is equal to the unique maximal ideal.
#### Estimated changes
Modified src/ring_theory/ideal/local_ring.lean
- \+ *lemma* local_ring.ker_eq_maximal_ideal



## [2021-09-07 11:06:50](https://github.com/leanprover-community/mathlib/commit/58a8853)
doc(data/list/*): Add missing documentation ([#8867](https://github.com/leanprover-community/mathlib/pull/8867))
Fixing the missing module docstrings in `data/list`, as well as documenting some `def`s and `theorem`s.
#### Estimated changes
Modified src/data/list/alist.lean


Modified src/data/list/func.lean


Modified src/data/list/of_fn.lean
- \+ *lemma* list.length_of_fn_aux
- \- *theorem* list.length_of_fn_aux
- \+ *lemma* list.nth_of_fn_aux
- \- *theorem* list.nth_of_fn_aux

Modified src/data/list/perm.lean


Modified src/data/list/sigma.lean




## [2021-09-07 11:06:49](https://github.com/leanprover-community/mathlib/commit/d366eb3)
feat(ring_theory/ideal/operations): add some theorems about taking the quotient of a ring by a sum of ideals  ([#8668](https://github.com/leanprover-community/mathlib/pull/8668))
The aim of this section is to prove that if `I, J` are ideals of the ring `R`, then the quotients `R/(I+J)` and `(R/I)/J'`are isomorphic, where `J'` is the image of `J` in `R/I`.
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *def* ideal.quotient.factor
- \+ *lemma* ideal.quotient.factor_comp_mk
- \+ *lemma* ideal.quotient.factor_mk

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* double_quot.ker_quot_left_to_quot_sup
- \+ *lemma* double_quot.ker_quot_quot_mk
- \+ *def* double_quot.lift_sup_quot_quot_mk
- \+ *def* double_quot.quot_left_to_quot_sup
- \+ *def* double_quot.quot_quot_equiv_quot_sup
- \+ *def* double_quot.quot_quot_mk
- \+ *def* double_quot.quot_quot_to_quot_sup
- \+ *lemma* ideal.ker_quotient_lift
- \+ *theorem* ideal.map_eq_iff_sup_ker_eq_of_surjective
- \+ *lemma* ideal.map_mk_eq_bot_of_le



## [2021-09-07 08:01:11](https://github.com/leanprover-community/mathlib/commit/d0c02bc)
feat(order/filter/basic): add `supr_inf_principal` and `tendsto_supr` ([#9051](https://github.com/leanprover-community/mathlib/pull/9051))
Also golf a few proofs
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.supr_inf_principal



## [2021-09-07 08:01:09](https://github.com/leanprover-community/mathlib/commit/6b0c73a)
chore(analysis/normed_space): add `dist_sum_sum_le` ([#9049](https://github.com/leanprover-community/mathlib/pull/9049))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* dist_sum_sum_le
- \+ *lemma* dist_sum_sum_le_of_le



## [2021-09-07 08:01:08](https://github.com/leanprover-community/mathlib/commit/3fdfc8e)
chore(data/bool): add a few lemmas about inequalities and `band`/`bor` ([#9048](https://github.com/leanprover-community/mathlib/pull/9048))
#### Estimated changes
Modified src/data/bool.lean
- \+ *lemma* bool.band_le_left
- \+ *lemma* bool.band_le_right
- \+ *lemma* bool.bor_le
- \+ *lemma* bool.le_band
- \+ *lemma* bool.le_iff_imp
- \+ *lemma* bool.left_le_bor
- \+ *lemma* bool.right_le_bor



## [2021-09-07 08:01:07](https://github.com/leanprover-community/mathlib/commit/c4f3707)
chore(scripts): update nolints.txt ([#9047](https://github.com/leanprover-community/mathlib/pull/9047))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-09-07 05:56:36](https://github.com/leanprover-community/mathlib/commit/77f4ed4)
docs(set_theory/lists): add module docstring and def docstrings ([#8967](https://github.com/leanprover-community/mathlib/pull/8967))
#### Estimated changes
Modified src/set_theory/lists.lean




## [2021-09-07 05:56:34](https://github.com/leanprover-community/mathlib/commit/0c19d5f)
feat(topology/uniform_space/basic): add corollary of Lebesgue number lemma `lebesgue_number_of_compact_open` ([#8963](https://github.com/leanprover-community/mathlib/pull/8963))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* is_open_iff_open_ball_subset
- \+ *lemma* lebesgue_number_of_compact_open



## [2021-09-07 05:56:33](https://github.com/leanprover-community/mathlib/commit/a7be93b)
feat(data/matrix/hadamard): add the Hadamard product ([#8956](https://github.com/leanprover-community/mathlib/pull/8956))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.diagonal_conj_transpose

Added src/data/matrix/hadamard.lean
- \+ *lemma* matrix.add_hadamard
- \+ *lemma* matrix.diagonal_hadamard_diagonal
- \+ *lemma* matrix.dot_product_vec_mul_hadamard
- \+ *def* matrix.hadamard
- \+ *lemma* matrix.hadamard_add
- \+ *lemma* matrix.hadamard_assoc
- \+ *lemma* matrix.hadamard_comm
- \+ *lemma* matrix.hadamard_one
- \+ *lemma* matrix.hadamard_smul
- \+ *lemma* matrix.hadamard_zero
- \+ *lemma* matrix.one_hadamard
- \+ *lemma* matrix.smul_hadamard
- \+ *lemma* matrix.sum_hadamard_eq
- \+ *lemma* matrix.zero_hadamard



## [2021-09-07 05:56:32](https://github.com/leanprover-community/mathlib/commit/91824e5)
feat(group_theory/subgroup): Normal Core ([#8940](https://github.com/leanprover-community/mathlib/pull/8940))
Defines normal core, and proves lemmas analogous to those for normal closure.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* subgroup.normal_core_eq_ker

Modified src/group_theory/subgroup.lean
- \+ *def* subgroup.normal_core
- \+ *lemma* subgroup.normal_core_eq_self
- \+ *lemma* subgroup.normal_core_eq_supr
- \+ *theorem* subgroup.normal_core_idempotent
- \+ *lemma* subgroup.normal_core_le
- \+ *lemma* subgroup.normal_core_mono
- \+ *lemma* subgroup.normal_le_normal_core



## [2021-09-07 05:56:31](https://github.com/leanprover-community/mathlib/commit/298f231)
feat(*): trivial lemmas from [#8903](https://github.com/leanprover-community/mathlib/pull/8903) ([#8909](https://github.com/leanprover-community/mathlib/pull/8909))
#### Estimated changes
Modified src/algebra/module/pi.lean
- \+ *lemma* pi.single_smul''

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.lsmul_apply

Modified src/data/part.lean


Modified src/data/subtype.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* symmetric_disjoint

Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto_supr

Modified src/topology/algebra/monoid.lean




## [2021-09-07 05:56:30](https://github.com/leanprover-community/mathlib/commit/5b29630)
chore(linear_algebra/tensor_product): remove `@[ext]` tag from `tensor_product.mk_compr₂_inj` ([#8868](https://github.com/leanprover-community/mathlib/pull/8868))
This PR removes the `@[ext]` tag from `tensor_product.mk_compr₂_inj` and readds it locally only where it is needed. This is a workaround for the issue discussed [in this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/odd.20repeated.20type.20class.20search): basically, when `ext` tries to apply this lemma to linear maps, it fails only after a very long typeclass search. While this problem is already present to some extent in current mathlib, it is exacerbated by the [upcoming generalization of linear maps to semilinear maps](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps).
In addition to this change, a few individual uses of `ext` have been replaced by a manual application of the relevant ext lemma(s) for performance reasons.
For discoverability, the lemma `tensor_product.mk_compr₂_inj` is renamed to `tensor_product.ext` and the former `tensor_product.ext` to `tensor_product.ext'`.
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Module/monoidal.lean


Modified src/algebra/category/Module/subobject.lean


Modified src/algebra/lie/tensor_product.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* tensor_product.ext'
- \+/\- *theorem* tensor_product.ext
- \- *theorem* tensor_product.mk_compr₂_inj

Modified src/representation_theory/maschke.lean


Modified src/ring_theory/tensor_product.lean




## [2021-09-07 03:50:01](https://github.com/leanprover-community/mathlib/commit/ceb9da6)
feat(analysis/convex/caratheodory): strengthen Caratheodory's lemma to provide affine independence ([#8892](https://github.com/leanprover-community/mathlib/pull/8892))
The changes here are:
- Use hypothesis `¬ affine_independent ℝ (coe : t → E)` instead of `finrank ℝ E + 1 < t.card`
- Drop no-longer-necessary `[finite_dimensional ℝ E]` assumption
- Do not use a shrinking argument but start by choosing an appropriate subset of minimum cardinality via `min_card_finset_of_mem_convex_hull`
- Provide a single alternative form of Carathéodory's lemma `eq_pos_convex_span_of_mem_convex_hull`
- In the alternate form, define the explicit linear combination using elements parameterised by a new `fintype` rather than on the entire ambient space `E` (we thus avoid the issue of junk values outside of the relevant subset)
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean
- \+ *lemma* caratheodory.affine_independent_min_card_finset_of_mem_convex_hull
- \+/\- *lemma* caratheodory.mem_convex_hull_erase
- \+ *lemma* caratheodory.mem_min_card_finset_of_mem_convex_hull
- \+ *lemma* caratheodory.min_card_finset_of_mem_convex_hull_card_le_card
- \+ *lemma* caratheodory.min_card_finset_of_mem_convex_hull_nonempty
- \+ *lemma* caratheodory.min_card_finset_of_mem_convex_hull_subseteq
- \- *lemma* caratheodory.shrink'
- \- *lemma* caratheodory.shrink
- \- *lemma* caratheodory.step
- \+ *lemma* convex_hull_eq_union
- \- *theorem* convex_hull_eq_union
- \- *lemma* convex_hull_subset_union
- \- *theorem* eq_center_mass_card_le_dim_succ_of_mem_convex_hull
- \- *theorem* eq_pos_center_mass_card_le_dim_succ_of_mem_convex_hull
- \+ *theorem* eq_pos_convex_span_of_mem_convex_hull

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* exists_nontrivial_relation_sum_zero_of_not_affine_ind



## [2021-09-07 03:49:59](https://github.com/leanprover-community/mathlib/commit/5eb1918)
feat(group_theory/perm/concrete_cycle): is_cycle_form_perm ([#8859](https://github.com/leanprover-community/mathlib/pull/8859))
#### Estimated changes
Added src/group_theory/perm/concrete_cycle.lean
- \+ *lemma* list.cycle_of_form_perm
- \+ *lemma* list.cycle_type_form_perm
- \+ *lemma* list.form_perm_apply_mem_eq_next
- \+ *lemma* list.form_perm_disjoint_iff
- \+ *lemma* list.is_cycle_form_perm
- \+ *lemma* list.pairwise_same_cycle_form_perm

Modified src/group_theory/perm/list.lean
- \- *lemma* list.form_perm_apply_not_mem
- \+ *lemma* list.form_perm_eq_self_of_not_mem
- \- *lemma* list.form_perm_ne_self_imp_mem
- \+ *lemma* list.mem_of_form_perm_ne_self



## [2021-09-07 03:49:58](https://github.com/leanprover-community/mathlib/commit/f157b6d)
feat(linear_algebra): introduce notation for `linear_map.comp` and `linear_equiv.trans` ([#8857](https://github.com/leanprover-community/mathlib/pull/8857))
This PR introduces new notation for the composition of linear maps and linear equivalences: `∘ₗ` denotes `linear_map.comp` and `≫ₗ` denotes `linear_equiv.trans`. This will be needed by an upcoming PR generalizing linear maps to semilinear maps (see discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps)): in some places, we need to help the elaborator a bit by telling it that we are composing plain linear maps/equivs as opposed to semilinear ones. We have not made the change systematically throughout the library, only in places where it is needed in our semilinear maps branch.
#### Estimated changes
Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/monoidal.lean


Modified src/algebra/lie/base_change.lean


Modified src/algebra/lie/tensor_product.lean


Modified src/algebra/lie/weights.lean


Modified src/algebra/module/linear_map.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/basis.lean
- \+/\- *def* basis.coord

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/direct_sum/finsupp.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/projection.lean


Modified src/linear_algebra/std_basis.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/linear_algebra/trace.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.coe_comp



## [2021-09-07 03:49:57](https://github.com/leanprover-community/mathlib/commit/d262500)
feat(group_theory/nilpotent): add antimono and functorial lemma for lower central series ([#8853](https://github.com/leanprover-community/mathlib/pull/8853))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series.map
- \+ *lemma* lower_central_series_antimono



## [2021-09-07 03:49:56](https://github.com/leanprover-community/mathlib/commit/f0f6c1c)
feat(tactic/lint): reducible non-instance linter ([#8540](https://github.com/leanprover-community/mathlib/pull/8540))
* This linter checks that if an instances uses a non-instance with as type a class, the non-instances is reducible.
* There are many false positives to this rule, which we probably want to allow (that are unlikely to cause problems). To cut down on the many many false positives, the linter currently only consider classes that have either an `add` or a `mul` field. Maybe we want to also include order-structures, but there are (for example) a bunch of `complete_lattice` structures that are derived using Galois insertions that haven't ever caused problems (I think).
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/hierarchy_design.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean




## [2021-09-07 01:49:05](https://github.com/leanprover-community/mathlib/commit/d6a1fc0)
feat(algebra/ordered_monoid): correct definition ([#8877](https://github.com/leanprover-community/mathlib/pull/8877))
Our definition of `ordered_monoid` is not the usual one, and this PR corrects that.
The standard definition just says
```
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
```
while we currently have an extra axiom
```
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)
```
(This was introduced in ancient times, https://github.com/leanprover-community/mathlib/commit/7d8e3f3a6de70da504406727dbe7697b2f7a62ee, with no indication of where the definition came from. I couldn't find it in other sources.)
As @urkud pointed out a while ago [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered_comm_monoid), these really are different.
The second axiom *does* automatically hold for cancellative ordered monoids, however.
This PR simply drops the axiom. In practice this causes no harm, because all the interesting examples are cancellative. There's a little bit of cleanup to do. In `src/algebra/ordered_sub.lean` four lemmas break, so I just added the necessary `[contravariant_class _ _ (+) (<)]` hypothesis. These lemmas aren't currently used in mathlib, but presumably where they are needed this typeclass will be available.
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \- *lemma* ex_L.lt_of_add_lt_add_left

Modified counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left

Modified src/algebra/ordered_sub.lean
- \+/\- *lemma* lt_of_sub_lt_sub_left_of_le
- \+/\- *lemma* sub_lt_sub_iff_left_of_le_of_le

Modified src/algebra/punit_instances.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/real/nnreal.lean


Modified src/set_theory/cardinal.lean




## [2021-09-07 00:33:29](https://github.com/leanprover-community/mathlib/commit/ce31c1c)
feat(order/prime_ideal): prime ideals are maximal ([#9004](https://github.com/leanprover-community/mathlib/pull/9004))
Proved that in boolean algebras:
1. An ideal is prime iff it always contains one of x, x^c
2. A prime ideal is maximal
#### Estimated changes
Modified src/order/ideal.lean
- \+ *lemma* order.ideal.is_proper.not_mem_of_compl_mem
- \+ *lemma* order.ideal.is_proper.not_mem_or_compl_not_mem
- \+ *lemma* order.ideal.is_proper.top_not_mem

Modified src/order/prime_ideal.lean
- \+ *lemma* order.ideal.is_prime_iff_mem_or_compl_mem
- \+ *lemma* order.ideal.is_prime_of_mem_or_compl_mem



## [2021-09-07 00:33:28](https://github.com/leanprover-community/mathlib/commit/5431521)
refactor(topology/sheaves/sheaf_condition): Generalize unique gluing API ([#9002](https://github.com/leanprover-community/mathlib/pull/9002))
Previously, the sheaf condition in terms of unique gluings has been defined only for type-valued presheaves. This PR generalizes this to arbitrary concrete categories, whose forgetful functor preserves limits and reflects isomorphisms (e.g. algebraic categories like `CommRing`). As a side effect, this solves a TODO in `structure_sheaf.lean`.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+/\- *lemma* Top.presheaf.sheaf_condition_equalizer_products.res_π

Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \+/\- *def* Top.presheaf.gluing
- \- *lemma* Top.presheaf.res_π_apply
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_unique_gluing_types
- \- *def* Top.presheaf.sheaf_condition_of_sheaf_condition_unique_gluing
- \+ *def* Top.presheaf.sheaf_condition_of_sheaf_condition_unique_gluing_types
- \+/\- *def* Top.presheaf.sheaf_condition_unique_gluing
- \- *def* Top.presheaf.sheaf_condition_unique_gluing_of_sheaf_condition
- \+ *def* Top.presheaf.sheaf_condition_unique_gluing_of_sheaf_condition_types

Modified src/topology/sheaves/stalks.lean




## [2021-09-07 00:33:27](https://github.com/leanprover-community/mathlib/commit/d472c56)
feat(linear_algebra/affine_space/affine_equiv): affine homotheties as equivalences ([#8983](https://github.com/leanprover-community/mathlib/pull/8983))
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.coe_coe
- \+ *lemma* affine_equiv.coe_homothety_units_mul_hom_apply
- \+ *lemma* affine_equiv.coe_homothety_units_mul_hom_apply_symm
- \+ *lemma* affine_equiv.coe_homothety_units_mul_hom_eq_homothety_hom_coe
- \+ *lemma* affine_equiv.coe_mk
- \+ *def* affine_equiv.homothety_units_mul_hom

Modified src/linear_algebra/affine_space/affine_map.lean




## [2021-09-06 21:09:20](https://github.com/leanprover-community/mathlib/commit/309674d)
feat(linear_algebra/basis): a nontrivial module has nonempty bases ([#9040](https://github.com/leanprover-community/mathlib/pull/9040))
A tiny little lemma that guarantees the dimension of a nontrivial module is nonzero. Noticeably simplifies the proof that the dimension of a power basis is positive in this case.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.index_nonempty

Modified src/ring_theory/power_basis.lean
- \+/\- *lemma* power_basis.dim_ne_zero



## [2021-09-06 21:09:19](https://github.com/leanprover-community/mathlib/commit/3218c37)
feat(linear_algebra/smodeq): sub_mem, eval ([#8993](https://github.com/leanprover-community/mathlib/pull/8993))
#### Estimated changes
Modified src/linear_algebra/smodeq.lean
- \+ *lemma* smodeq.eval
- \+ *lemma* smodeq.sub_mem



## [2021-09-06 21:09:18](https://github.com/leanprover-community/mathlib/commit/fde1fc2)
feat(*): make more non-instances reducible ([#8941](https://github.com/leanprover-community/mathlib/pull/8941))
* Also add some docstrings to `cau_seq_completion`.
* Related PR: [#7835](https://github.com/leanprover-community/mathlib/pull/7835)
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/module/basic.lean


Modified src/category_theory/monoidal/skeleton.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/localization.lean




## [2021-09-06 17:52:24](https://github.com/leanprover-community/mathlib/commit/bfcf73f)
feat(data/multiset/basic): Add a result on intersection of multiset with `repeat a n` ([#9038](https://github.com/leanprover-community/mathlib/pull/9038))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.repeat_inf



## [2021-09-06 17:52:23](https://github.com/leanprover-community/mathlib/commit/3148cfe)
feat(field_theory/algebraic_closure): polynomials in an algebraically closed fields have roots ([#9037](https://github.com/leanprover-community/mathlib/pull/9037))
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *theorem* is_alg_closed.exists_root



## [2021-09-06 17:52:21](https://github.com/leanprover-community/mathlib/commit/3a62419)
chore(data/nat/mul_ind): make docgen happy ([#9036](https://github.com/leanprover-community/mathlib/pull/9036))
#### Estimated changes
Modified src/data/nat/mul_ind.lean




## [2021-09-06 17:52:20](https://github.com/leanprover-community/mathlib/commit/11284f2)
feat(ring_theory): `y ≠ 0` in a UFD has finitely many divisors ([#9034](https://github.com/leanprover-community/mathlib/pull/9034))
This implies ideals in a Dedekind domain are contained in only finitely many larger ideals.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean




## [2021-09-06 17:52:19](https://github.com/leanprover-community/mathlib/commit/86dd706)
feat(set/lattice): two lemmas about when sInter is empty ([#9033](https://github.com/leanprover-community/mathlib/pull/9033))
- Added sInter_eq_empty_iff
- Added sInter_nonempty_iff
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.sInter_eq_empty_iff
- \+ *theorem* set.sInter_nonempty_iff



## [2021-09-06 17:52:18](https://github.com/leanprover-community/mathlib/commit/98cbad7)
chore(set_theory/pgame): add protected ([#9022](https://github.com/leanprover-community/mathlib/pull/9022))
Breaks [#7843](https://github.com/leanprover-community/mathlib/pull/7843) into smaller PRs.
These lemmas about `pgame` conflict with the ones for `game` when used in `calc` mode proofs, which confuses Lean.
There is no way to use the lemmas for `game` (required for surreal numbers) without using `_root_` as `game` inherits these lemmas from its abelian group structure.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/winner.lean


Modified src/set_theory/pgame.lean
- \+/\- *theorem* pgame.equiv_refl
- \- *theorem* pgame.le_refl
- \- *theorem* pgame.lt_irrefl
- \- *theorem* pgame.ne_of_lt



## [2021-09-06 17:52:17](https://github.com/leanprover-community/mathlib/commit/c83c22d)
feat(measure_theory/measure/vector_measure): zero is absolutely continuous wrt any vector measure ([#9007](https://github.com/leanprover-community/mathlib/pull/9007))
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.zero



## [2021-09-06 17:52:16](https://github.com/leanprover-community/mathlib/commit/339c2c3)
feat(linear_algebra/affine_space/independent): affine independence is preserved by affine maps ([#9005](https://github.com/leanprover-community/mathlib/pull/9005))
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.injective_iff_linear_injective

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent.map'
- \+ *lemma* affine_independent.of_comp
- \+ *lemma* affine_map.affine_independent_iff



## [2021-09-06 12:26:04](https://github.com/leanprover-community/mathlib/commit/c2e6e62)
feat(algebra/absolute_value): generalize a few results to `linear_ordered_ring`s ([#9026](https://github.com/leanprover-community/mathlib/pull/9026))
The proofs were copied literally from `is_absolute_value`, which was defined on fields, but we can generalize them to rings with only a few tweaks.
#### Estimated changes
Modified src/algebra/absolute_value.lean




## [2021-09-06 12:26:02](https://github.com/leanprover-community/mathlib/commit/448f821)
feat(algebra/pointwise): enable pointwise add_action ([#9017](https://github.com/leanprover-community/mathlib/pull/9017))
Just a little to_additive declaration
#### Estimated changes
Modified src/algebra/pointwise.lean




## [2021-09-06 12:26:01](https://github.com/leanprover-community/mathlib/commit/f0c3f9e)
feat(linear_algebra/basic): surjective_of_iterate_surjective ([#9006](https://github.com/leanprover-community/mathlib/pull/9006))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.surjective_of_iterate_surjective



## [2021-09-06 12:26:00](https://github.com/leanprover-community/mathlib/commit/d16cb00)
feat(linear_algebra/basic): of_le_injective ([#8977](https://github.com/leanprover-community/mathlib/pull/8977))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* submodule.of_le_injective



## [2021-09-06 12:25:59](https://github.com/leanprover-community/mathlib/commit/c0f01ee)
feat(data/fin): pos_iff_nonempty ([#8975](https://github.com/leanprover-community/mathlib/pull/8975))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.pos_iff_nonempty



## [2021-09-06 12:25:58](https://github.com/leanprover-community/mathlib/commit/de37a6a)
chore(field_theory/fixed): reuse existing `mul_semiring_action.to_alg_hom`  by providing `smul_comm_class` ([#8965](https://github.com/leanprover-community/mathlib/pull/8965))
This removes `fixed_points.to_alg_hom` as this is really just a bundled form of `mul_semiring_action.to_alg_hom` + `mul_semiring_action.to_alg_hom_injective`, once we provide the missing `smul_comm_class`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *theorem* mul_semiring_action.to_alg_equiv_injective
- \+ *theorem* mul_semiring_action.to_alg_hom_injective

Modified src/field_theory/fixed.lean
- \- *def* fixed_points.to_alg_hom
- \- *lemma* fixed_points.to_alg_hom_apply_apply



## [2021-09-06 12:25:57](https://github.com/leanprover-community/mathlib/commit/2aebabc)
feat(topology/continuous_function/basic): add `continuous_map.Icc_extend` ([#8952](https://github.com/leanprover-community/mathlib/pull/8952))
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *def* continuous_map.Icc_extend
- \+ *lemma* continuous_map.coe_Icc_extend



## [2021-09-06 12:25:55](https://github.com/leanprover-community/mathlib/commit/773b45f)
feat(algebra/module/ordered): redefine `ordered_module` as `ordered_smul` ([#8930](https://github.com/leanprover-community/mathlib/pull/8930))
One would like to talk about `ordered_monoid R (with_top R)`, but the `module` constraint is too strict to allow this.
The definition of `ordered_monoid` works if it is loosened to `has_scalar R M`. Most of the proofs that are part of its API need at most `smul_with_zero`. So it has been loosened to `smul_with_zero`, since a lawless `ordered_monoid` wouldn't do much.
In the `ordered_field` portion, `module` has been loosened to `mul_action_with_zero`.
`order_dual` instances of `smul` instances have also been generalized to better transmit. There are more generalizations possible, but seem out of scope for a single PR.
Unfortunately, these generalizations exposed a gnarly misalignment between `prod.has_lt` and `prod.has_le`, which have incompatible definitions, when inferred through separate paths. In particular, the `lt` definition of generated by `prod.preorder` is different than the core `prod.has_lt`. Due to this, the `prod.ordered_monoid` instance has not been generalized.
#### Estimated changes
Modified src/algebra/algebra/ordered.lean


Modified src/algebra/module/ordered.lean
- \- *lemma* eq_of_smul_eq_smul_of_pos_of_le
- \- *lemma* le_smul_iff_of_pos
- \- *lemma* lt_of_smul_lt_smul_of_nonneg
- \- *lemma* ordered_module.mk''
- \- *lemma* ordered_module.mk'
- \- *lemma* smul_le_iff_of_pos
- \+/\- *lemma* smul_le_smul_iff_of_neg
- \- *lemma* smul_le_smul_iff_of_pos
- \- *lemma* smul_le_smul_of_nonneg
- \- *lemma* smul_lt_iff_of_pos
- \- *lemma* smul_lt_smul_iff_of_pos
- \- *lemma* smul_lt_smul_of_pos
- \- *lemma* smul_pos_iff_of_pos

Added src/algebra/ordered_smul.lean
- \+ *lemma* eq_of_smul_eq_smul_of_pos_of_le
- \+ *lemma* le_smul_iff_of_pos
- \+ *lemma* lt_of_smul_lt_smul_of_nonneg
- \+ *lemma* ordered_smul.mk''
- \+ *lemma* ordered_smul.mk'
- \+ *lemma* smul_le_iff_of_pos
- \+ *lemma* smul_le_smul_iff_of_pos
- \+ *lemma* smul_le_smul_of_nonneg
- \+ *lemma* smul_lt_iff_of_pos
- \+ *lemma* smul_lt_smul_iff_of_pos
- \+ *lemma* smul_lt_smul_of_pos
- \+ *lemma* smul_pos_iff_of_pos

Modified src/algebra/star/chsh.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.smul

Modified src/analysis/convex/cone.lean
- \- *lemma* convex_cone.to_ordered_module
- \+ *lemma* convex_cone.to_ordered_smul

Modified src/analysis/convex/extrema.lean


Modified src/data/complex/module.lean
- \- *lemma* complex.complex_ordered_module
- \+ *lemma* complex.complex_ordered_smul

Modified src/linear_algebra/affine_space/ordered.lean




## [2021-09-06 12:25:54](https://github.com/leanprover-community/mathlib/commit/e8fff26)
refactor(group_theory/*): Move Cauchy's theorem ([#8916](https://github.com/leanprover-community/mathlib/pull/8916))
Moves Cauchy's theorem from `sylow.lean` to `perm/cycle_type.lean`. Now `perm/cycle_type.lean` no longer depends on `sylow.lean`, and `p_group.lean` can use Cauchy's theorem (e.g. for equivalent characterizations of p-groups).
#### Estimated changes
Modified src/group_theory/p_group.lean


Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.exists_prime_order_of_dvd_card
- \+ *lemma* equiv.perm.vectors_prod_eq_one.card
- \+ *def* equiv.perm.vectors_prod_eq_one.equiv_vector
- \+ *lemma* equiv.perm.vectors_prod_eq_one.mem_iff
- \+ *lemma* equiv.perm.vectors_prod_eq_one.one_eq
- \+ *def* equiv.perm.vectors_prod_eq_one.rotate
- \+ *lemma* equiv.perm.vectors_prod_eq_one.rotate_length
- \+ *lemma* equiv.perm.vectors_prod_eq_one.rotate_rotate
- \+ *lemma* equiv.perm.vectors_prod_eq_one.rotate_zero
- \+ *def* equiv.perm.vectors_prod_eq_one.vector_equiv
- \+ *lemma* equiv.perm.vectors_prod_eq_one.zero_eq
- \+ *def* equiv.perm.vectors_prod_eq_one

Modified src/group_theory/sylow.lean
- \- *lemma* sylow.exists_prime_order_of_dvd_card
- \- *lemma* sylow.mem_vectors_prod_eq_one
- \- *lemma* sylow.mem_vectors_prod_eq_one_iff
- \- *def* sylow.mk_vector_prod_eq_one
- \- *lemma* sylow.mk_vector_prod_eq_one_injective
- \- *lemma* sylow.one_mem_fixed_points_rotate
- \- *lemma* sylow.one_mem_vectors_prod_eq_one
- \- *def* sylow.rotate_vectors_prod_eq_one
- \- *def* sylow.vectors_prod_eq_one



## [2021-09-06 12:25:53](https://github.com/leanprover-community/mathlib/commit/893c474)
feat(group_theory/submonoid/membership): add log, exp lemmas ([#8870](https://github.com/leanprover-community/mathlib/pull/8870))
Breaking up a previous PR ([#7843](https://github.com/leanprover-community/mathlib/pull/7843)) into smaller ones.
This PR adds lemmas about injectivity of `pow` and `log` functions under appropriate conditions.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238870)
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *def* submonoid.log
- \+ *theorem* submonoid.log_pow_eq_self
- \+ *theorem* submonoid.log_pow_int_eq_self
- \+ *def* submonoid.pow
- \+ *theorem* submonoid.pow_log_eq_self
- \+ *lemma* submonoid.pow_right_injective_iff_pow_injective



## [2021-09-06 12:25:52](https://github.com/leanprover-community/mathlib/commit/74373b8)
feat(algebra/lattice_ordered_group): add basic theory of lattice ordered groups ([#8673](https://github.com/leanprover-community/mathlib/pull/8673))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/field_power.lean


Modified src/algebra/group/basic.lean
- \+ *lemma* div_mul_comm

Added src/algebra/lattice_ordered_group.lean
- \+ *lemma* inf_mul_sup
- \+ *lemma* inv_inf_eq_sup_inv
- \+ *lemma* inv_sup_eq_inv_inf_inv
- \+ *theorem* lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf
- \+ *lemma* lattice_ordered_comm_group.inf_eq_div_pos_div
- \+ *lemma* lattice_ordered_comm_group.inv_le_abs
- \+ *def* lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice
- \+ *lemma* lattice_ordered_comm_group.le_mabs
- \+ *theorem* lattice_ordered_comm_group.m_Birkhoff_inequalities
- \+ *lemma* lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge
- \+ *lemma* lattice_ordered_comm_group.m_le_neg
- \+ *lemma* lattice_ordered_comm_group.m_le_pos
- \+ *lemma* lattice_ordered_comm_group.m_neg_pos
- \+ *lemma* lattice_ordered_comm_group.m_pos_pos
- \+ *lemma* lattice_ordered_comm_group.m_pos_pos_id
- \+ *lemma* lattice_ordered_comm_group.mabs_idempotent
- \+ *lemma* lattice_ordered_comm_group.mabs_pos
- \+ *lemma* lattice_ordered_comm_group.mabs_pos_eq
- \+ *lemma* lattice_ordered_comm_group.mabs_triangle
- \+ *def* lattice_ordered_comm_group.mneg
- \+ *def* lattice_ordered_comm_group.mpos
- \+ *lemma* lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul
- \+ *lemma* lattice_ordered_comm_group.neg_eq_inv_inf_one
- \+ *lemma* lattice_ordered_comm_group.neg_eq_pos_inv
- \+ *lemma* lattice_ordered_comm_group.pos_div_neg'
- \+ *lemma* lattice_ordered_comm_group.pos_eq_neg_inv
- \+ *lemma* lattice_ordered_comm_group.pos_inf_neg_eq_one
- \+ *lemma* lattice_ordered_comm_group.pos_inv_neg
- \+ *lemma* lattice_ordered_comm_group.pos_mul_neg
- \+ *lemma* lattice_ordered_comm_group.sup_div_inf_eq_abs_div
- \+ *lemma* lattice_ordered_comm_group.sup_eq_mul_pos_div
- \+ *lemma* lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div
- \+ *lemma* lattice_ordered_comm_group.two_inf_eq_mul_div_abs_div
- \+ *lemma* mul_sup_eq_mul_sup_mul

Modified src/algebra/ordered_group.lean
- \- *def* abs
- \+ *lemma* abs_eq_max_neg
- \+ *def* mabs

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* abs_eq_neg_self
- \+/\- *lemma* abs_eq_self

Modified src/data/int/cast.lean


Modified src/data/rat/cast.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.coe_abs

Modified src/order/filter/filter_product.lean
- \+ *lemma* filter.germ.lattice_of_linear_order_eq_filter_germ_lattice

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/metric_space/basic.lean




## [2021-09-06 11:10:12](https://github.com/leanprover-community/mathlib/commit/c563692)
feat(data/polynomial/eval): leval, eval as linear map ([#8999](https://github.com/leanprover-community/mathlib/pull/8999))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/eval.lean
- \+ *def* polynomial.leval



## [2021-09-06 05:31:16](https://github.com/leanprover-community/mathlib/commit/1f10390)
lint(tactic/*): break long lines ([#8973](https://github.com/leanprover-community/mathlib/pull/8973))
For code lines, the fix was often simple, just break that damn line.
For strings, you shouldn't break a line inside one as this will be a visible change to the tactic's output. When nothing else can be done, I used the trick of breaking the string into two appended strings. "A B" becomes "A" ++ " B", and that's line-breakable.
#### Estimated changes
Modified src/tactic/converter/interactive.lean


Modified src/tactic/converter/old_conv.lean


Modified src/tactic/core.lean


Modified src/tactic/delta_instance.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/generalizes.lean


Modified src/tactic/interactive.lean


Modified src/tactic/interactive_expr.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/lean_core_docs.lean


Modified src/tactic/linarith/elimination.lean


Modified src/tactic/linarith/parsing.lean


Modified src/tactic/linarith/preprocessing.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/slim_check.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tidy.lean


Modified src/tactic/transfer.lean


Modified src/tactic/transform_decl.lean


Modified src/tactic/transport.lean


Modified src/tactic/wlog.lean




## [2021-09-06 03:41:00](https://github.com/leanprover-community/mathlib/commit/1bc59c9)
refactor(*): replace `function.swap` by `swap` ([#8612](https://github.com/leanprover-community/mathlib/pull/8612))
This shortens some statements without decreasing legibility (IMO).
#### Estimated changes
Modified src/algebra/bounds.lean


Modified src/algebra/covariant_and_contravariant.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* div_le_inv_mul_iff

Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_monoid_lemmas.lean
- \+/\- *lemma* le_mul_of_one_le_of_le
- \+/\- *lemma* le_of_mul_le_mul_right'
- \+/\- *lemma* lt_mul_of_one_lt_left'
- \+/\- *lemma* lt_mul_of_one_lt_of_le
- \+/\- *lemma* lt_of_mul_lt_mul_right'
- \+/\- *lemma* monotone.mul'
- \+/\- *lemma* monotone.mul_const'
- \+/\- *lemma* mul_le_mul_right'
- \+/\- *lemma* mul_le_of_le_one_of_le
- \+/\- *lemma* mul_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_lt_mul_right'
- \+/\- *lemma* mul_lt_of_le_one_of_lt
- \+/\- *lemma* mul_lt_of_lt_one_of_le
- \+/\- *lemma* right.mul_lt_one
- \+/\- *lemma* right.mul_lt_one_of_lt_of_lt_one
- \+/\- *lemma* right.one_le_mul
- \+/\- *lemma* right.one_lt_mul

Modified src/computability/primrec.lean
- \+/\- *theorem* nat.primrec.swap'
- \+/\- *theorem* primrec₂.swap

Modified src/data/nat/bitwise.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/wseq.lean


Modified src/logic/basic.lean




## [2021-09-05 23:31:30](https://github.com/leanprover-community/mathlib/commit/a399728)
feat(group_theory/coset): Interaction between quotient_group.mk and right multiplication by elements of the subgroup ([#8970](https://github.com/leanprover-community/mathlib/pull/8970))
Two helpful lemmas regarding the interaction between `quotient_group.mk` and right multiplication by elements of the subgroup.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.mk_mul_of_mem
- \+ *lemma* quotient_group.mk_out'_eq_mul



## [2021-09-05 22:12:20](https://github.com/leanprover-community/mathlib/commit/0a94b29)
feat(data/nat/choose/vandermonde): Vandermonde's identity for binomial coefficients ([#8992](https://github.com/leanprover-community/mathlib/pull/8992))
I place this identity in a new file because the current proof depends on `polynomial`.
#### Estimated changes
Added src/data/nat/choose/vandermonde.lean
- \+ *lemma* nat.add_choose_eq

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.coeff_X_add_one_pow
- \+ *lemma* polynomial.coeff_one_add_X_pow



## [2021-09-05 02:26:54](https://github.com/leanprover-community/mathlib/commit/9fc45d8)
chore(scripts): update nolints.txt ([#9014](https://github.com/leanprover-community/mathlib/pull/9014))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-09-04 20:06:15](https://github.com/leanprover-community/mathlib/commit/2ea1650)
fix(algebra/ordered_monoid): slay with_top monoid diamonds caused by irreducibility ([#8926](https://github.com/leanprover-community/mathlib/pull/8926))
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Diamond.20in.20instances.20on.20.60with_top.20R.60
Instead of copying over from `with_zero`, just work through the definitions directly.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/data/polynomial/ring_division.lean


Modified test/instance_diamonds.lean




## [2021-09-04 18:18:07](https://github.com/leanprover-community/mathlib/commit/fd0cdae)
feat(linear_algebra/pi): pi_option_equiv_prod ([#9003](https://github.com/leanprover-community/mathlib/pull/9003))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.pi_option_equiv_prod

Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.pi_option_equiv_prod



## [2021-09-04 18:18:06](https://github.com/leanprover-community/mathlib/commit/8ff139a)
feat(data/equiv/fin): fin_sum_fin_equiv simp lemmas ([#9001](https://github.com/leanprover-community/mathlib/pull/9001))
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+/\- *lemma* fin_sum_fin_equiv_apply_left
- \+/\- *lemma* fin_sum_fin_equiv_apply_right
- \+ *lemma* fin_sum_fin_equiv_symm_apply_cast_add
- \+ *lemma* fin_sum_fin_equiv_symm_apply_cast_add_right



## [2021-09-04 18:18:05](https://github.com/leanprover-community/mathlib/commit/7729bb6)
feat(algebra): define "Euclidean" absolute values ([#8949](https://github.com/leanprover-community/mathlib/pull/8949))
We say an absolute value `abv : absolute_value R S` is Euclidean if agrees with the Euclidean domain structure on `R`, namely `abv x < abv y ↔ euclidean_domain.r x y`.
Examples include `abs : ℤ → ℤ` and `λ (p : polynomial Fq), (q ^ p.degree : ℤ)`, where `Fq` is a finite field with `q` elements. (These two correspond to the number field and function field case respectively, in our proof that the class number of a global field is finite.)
#### Estimated changes
Modified src/algebra/absolute_value.lean
- \+ *lemma* absolute_value.map_sub_eq_zero_iff

Added src/algebra/euclidean_absolute_value.lean
- \+ *lemma* absolute_value.is_euclidean.map_lt_map_iff
- \+ *lemma* absolute_value.is_euclidean.sub_mod_lt

Added src/data/polynomial/degree/card_pow_degree.lean
- \+ *lemma* polynomial.card_pow_degree_apply
- \+ *lemma* polynomial.card_pow_degree_is_euclidean
- \+ *lemma* polynomial.card_pow_degree_nonzero
- \+ *lemma* polynomial.card_pow_degree_zero



## [2021-09-04 18:18:04](https://github.com/leanprover-community/mathlib/commit/28592d9)
feat(set_theory/cardinal): cardinal.to_nat_mul ([#8943](https://github.com/leanprover-community/mathlib/pull/8943))
`cardinal.to_nat` distributes over multiplication.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.cast_to_nat_of_omega_le
- \+ *lemma* cardinal.nat_cast_injective
- \+ *lemma* cardinal.to_nat_mul



## [2021-09-04 17:05:08](https://github.com/leanprover-community/mathlib/commit/9df3f0d)
feat(data/nat/prime): nat.prime.eq_pow_iff ([#8917](https://github.com/leanprover-community/mathlib/pull/8917))
If a^k=p then a=p and k=1.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.eq_one_of_pow
- \+ *lemma* nat.prime.pow_eq_iff
- \+ *lemma* nat.prime.pow_not_prime'



## [2021-09-04 15:15:27](https://github.com/leanprover-community/mathlib/commit/a4df460)
feat(linear_algebra/matrix/symmetric): add a file ([#8955](https://github.com/leanprover-community/mathlib/pull/8955))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.transpose_smul
- \+/\- *lemma* matrix.transpose_sub

Added src/linear_algebra/matrix/symmetric.lean
- \+ *lemma* matrix.is_symm.add
- \+ *lemma* matrix.is_symm.apply
- \+ *lemma* matrix.is_symm.conj_transpose
- \+ *lemma* matrix.is_symm.eq
- \+ *lemma* matrix.is_symm.ext
- \+ *lemma* matrix.is_symm.ext_iff
- \+ *lemma* matrix.is_symm.from_blocks
- \+ *lemma* matrix.is_symm.map
- \+ *lemma* matrix.is_symm.minor
- \+ *lemma* matrix.is_symm.neg
- \+ *lemma* matrix.is_symm.smul
- \+ *lemma* matrix.is_symm.sub
- \+ *lemma* matrix.is_symm.transpose
- \+ *def* matrix.is_symm
- \+ *lemma* matrix.is_symm_add_transpose_self
- \+ *lemma* matrix.is_symm_diagonal
- \+ *lemma* matrix.is_symm_from_blocks_iff
- \+ *lemma* matrix.is_symm_mul_transpose_self
- \+ *lemma* matrix.is_symm_one
- \+ *lemma* matrix.is_symm_transpose_add_self
- \+ *lemma* matrix.is_symm_transpose_mul_self
- \+ *lemma* matrix.is_symm_zero



## [2021-09-04 13:21:59](https://github.com/leanprover-community/mathlib/commit/18d7b74)
feat(data/nat/choose/dvd): generalize to division rings ([#8997](https://github.com/leanprover-community/mathlib/pull/8997))
#### Estimated changes
Modified src/data/nat/choose/dvd.lean
- \+/\- *lemma* nat.cast_add_choose
- \+/\- *lemma* nat.cast_choose



## [2021-09-04 11:21:20](https://github.com/leanprover-community/mathlib/commit/4435e90)
feat(ring_theory/ideal/operations): ideal.pow_mem_pow ([#8996](https://github.com/leanprover-community/mathlib/pull/8996))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.pow_mem_pow



## [2021-09-04 11:21:19](https://github.com/leanprover-community/mathlib/commit/dcc45b4)
feat(order/prime_ideal, order/boolean_algebra): small lemmas about prime ideals ([#8980](https://github.com/leanprover-community/mathlib/pull/8980))
- Added is_prime.mem_or_compl_mem 
- Added is_prime.mem_compl_of_not_mem 
- Added sup_inf_inf_compl
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* sup_inf_inf_compl

Modified src/order/prime_ideal.lean
- \+ *lemma* order.ideal.is_prime.mem_compl_of_not_mem
- \+ *lemma* order.ideal.is_prime.mem_or_compl_mem



## [2021-09-04 10:04:21](https://github.com/leanprover-community/mathlib/commit/7f7f3d9)
feat(ring_theory/ideal/operations): ring_hom.ker_is_maximal_of_surjective ([#8990](https://github.com/leanprover-community/mathlib/pull/8990))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ring_hom.ker_is_maximal_of_surjective



## [2021-09-04 08:16:53](https://github.com/leanprover-community/mathlib/commit/9d86dad)
feat(linear_algebra/prod): lemmas about ker and range ([#8989](https://github.com/leanprover-community/mathlib/pull/8989))
#### Estimated changes
Modified src/linear_algebra/prod.lean
- \+ *theorem* linear_map.fst_surjective
- \+ *theorem* linear_map.ker_fst
- \+ *theorem* linear_map.ker_snd
- \+ *theorem* linear_map.range_inl
- \+ *theorem* linear_map.range_inr
- \+ *theorem* linear_map.snd_surjective



## [2021-09-04 08:16:52](https://github.com/leanprover-community/mathlib/commit/855613e)
feat(linear_algebra/basic): galois insertion lemmas for map and comap ([#8978](https://github.com/leanprover-community/mathlib/pull/8978))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.comap_injective_of_surjective
- \+ *lemma* submodule.comap_le_comap_iff_of_surjective
- \+ *lemma* submodule.comap_strict_mono_of_surjective
- \+ *def* submodule.gi_map_comap
- \+ *lemma* submodule.map_comap_eq_of_surjective
- \+ *lemma* submodule.map_inf_comap_of_surjective
- \+ *lemma* submodule.map_infi_comap_of_surjective
- \+ *lemma* submodule.map_sup_comap_of_surjective
- \+ *lemma* submodule.map_supr_comap_of_sujective
- \+ *lemma* submodule.map_surjective_of_surjective



## [2021-09-04 06:46:17](https://github.com/leanprover-community/mathlib/commit/b57af8a)
feat(category_theory/basic/category): Combine and improve API on preorder categories. ([#8982](https://github.com/leanprover-community/mathlib/pull/8982))
Material on preorders as categories was previously scattered throughout the library. This PR unites this material into a single file `category_theory/category/preorder` and also expands upon it, by relating adjoints to galois connections.
#### Estimated changes
Modified src/category_theory/category/default.lean
- \- *def* category_theory.hom_of_le
- \- *lemma* category_theory.hom_of_le_comp
- \- *lemma* category_theory.hom_of_le_le_of_hom
- \- *lemma* category_theory.hom_of_le_refl
- \- *lemma* category_theory.le_of_hom
- \- *lemma* category_theory.le_of_hom_hom_of_le

Added src/category_theory/category/preorder.lean
- \+ *def* category_theory.Preorder_to_Cat
- \+ *lemma* category_theory.adjunction.gc
- \+ *def* category_theory.equivalence.to_order_iso
- \+ *lemma* category_theory.equivalence.to_order_iso_apply
- \+ *lemma* category_theory.equivalence.to_order_iso_symm_apply
- \+ *lemma* category_theory.functor.monotone
- \+ *def* category_theory.hom_of_le
- \+ *lemma* category_theory.hom_of_le_comp
- \+ *lemma* category_theory.hom_of_le_le_of_hom
- \+ *lemma* category_theory.hom_of_le_refl
- \+ *lemma* category_theory.iso.to_eq
- \+ *lemma* category_theory.le_of_hom
- \+ *lemma* category_theory.le_of_hom_hom_of_le
- \+ *lemma* category_theory.le_of_op_hom
- \+ *def* category_theory.op_hom_of_le
- \+ *def* galois_connection.adjunction
- \+ *def* monotone.functor
- \+ *lemma* monotone.functor_obj

Modified src/category_theory/equivalence.lean
- \- *def* category_theory.equivalence.to_order_iso
- \- *lemma* category_theory.equivalence.to_order_iso_apply
- \- *lemma* category_theory.equivalence.to_order_iso_symm_apply

Modified src/category_theory/filtered.lean


Modified src/category_theory/functor.lean
- \- *lemma* category_theory.functor.monotone

Modified src/category_theory/isomorphism.lean
- \- *lemma* category_theory.iso.to_eq

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.le_of_op_hom
- \- *def* category_theory.op_hom_of_le

Modified src/category_theory/skeletal.lean


Modified src/topology/category/Top/opens.lean




## [2021-09-04 02:26:04](https://github.com/leanprover-community/mathlib/commit/b9d8081)
chore(scripts): update nolints.txt ([#8987](https://github.com/leanprover-community/mathlib/pull/8987))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-09-04 00:27:12](https://github.com/leanprover-community/mathlib/commit/464c3d7)
chore(group_theory/group_action/defs): weaken assumptions of `mul_smul_comm` and `smul_mul_assoc` ([#8972](https://github.com/leanprover-community/mathlib/pull/8972))
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* mul_smul_comm
- \+/\- *lemma* smul_mul_assoc



## [2021-09-04 00:27:11](https://github.com/leanprover-community/mathlib/commit/6ab6695)
docs(topology/algebra/floor_ring): add module docstring ([#8969](https://github.com/leanprover-community/mathlib/pull/8969))
#### Estimated changes
Modified src/topology/algebra/floor_ring.lean




## [2021-09-03 22:57:17](https://github.com/leanprover-community/mathlib/commit/66cb5e0)
fix(data/setoid/partition): make def more readable ([#8951](https://github.com/leanprover-community/mathlib/pull/8951))
If we change the statement of `partition.order_iso` from `setoid α ≃o subtype (@is_partition α)` to `setoid α ≃o {C : set (set α) // is_partition C}` then this doesn't change anything up to defeq and it's much easier for a beginner to read, as well as avoiding the `@`. I also change some variable names. Why? I want to show this part of this file to undergraduates and I want to make it look as easy and nice as possible.
#### Estimated changes
Modified src/data/setoid/partition.lean




## [2021-09-03 22:57:16](https://github.com/leanprover-community/mathlib/commit/93a15d6)
feat(ring_theory/subring): field structure on centers of a division_ring ([#8472](https://github.com/leanprover-community/mathlib/pull/8472))
I've also tidied up the subtitles. Previously there was a mix of h1 and h3s, I've made them all h2s.
#### Estimated changes
Modified src/group_theory/submonoid/center.lean
- \+ *lemma* set.div_mem_center'
- \+ *lemma* set.div_mem_center

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.center.coe_div
- \+ *lemma* subring.center.coe_inv



## [2021-09-03 20:53:49](https://github.com/leanprover-community/mathlib/commit/3a0dddc)
feat(algebra/order_functions): (min|max)_eq_iff ([#8911](https://github.com/leanprover-community/mathlib/pull/8911))
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_eq_iff
- \+ *lemma* min_eq_iff



## [2021-09-03 20:53:48](https://github.com/leanprover-community/mathlib/commit/39cea43)
docs(data/subtype): add module docstring ([#8900](https://github.com/leanprover-community/mathlib/pull/8900))
#### Estimated changes
Modified src/data/subtype.lean
- \+/\- *def* subtype.coind
- \+/\- *theorem* subtype.coind_bijective
- \+/\- *theorem* subtype.coind_injective
- \+/\- *theorem* subtype.coind_surjective
- \+/\- *def* subtype.map
- \+/\- *theorem* subtype.map_id
- \+/\- *lemma* subtype.map_injective
- \+/\- *lemma* subtype.map_involutive
- \+/\- *def* subtype.restrict
- \+/\- *lemma* subtype.restrict_apply



## [2021-09-03 18:48:25](https://github.com/leanprover-community/mathlib/commit/710a76e)
chore(algebra/divisibility): help dot notation on `dvd` ([#8766](https://github.com/leanprover-community/mathlib/pull/8766))
Add aliases
* `dvd_mul_of_dvd_left` -> `has_dvd.dvd.mul_right`
* `dvd_mul_of_dvd_right` -> `has_dvd.dvd.mul_left`
Add, to help with a few proofs,
* `dvd_rfl`
* `dvd_pow_self`
Use `has_dvd.dvd.trans` more largely.
#### Estimated changes
Modified archive/imo/imo1959_q1.lean


Modified archive/imo/imo2011_q5.lean


Modified src/algebra/associated.lean


Modified src/algebra/divisibility.lean
- \+ *lemma* dvd_rfl
- \+/\- *theorem* one_dvd

Modified src/algebra/euclidean_domain.lean


Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right

Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/gcd_monoid/multiset.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* dvd_pow
- \+ *lemma* dvd_pow_self

Modified src/algebra/ring/basic.lean


Modified src/algebra/squarefree.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/factorial.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/pow.lean


Modified src/data/nat/prime.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/rat/basic.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/pell.lean
- \+/\- *theorem* pell.asq_pos
- \+/\- *def* pell.az
- \+/\- *theorem* pell.d_pos
- \+/\- *theorem* pell.dvd_of_ysq_dvd
- \+/\- *theorem* pell.dz_val
- \+/\- *theorem* pell.eq_of_xn_modeq'
- \+/\- *theorem* pell.eq_of_xn_modeq
- \+/\- *theorem* pell.eq_of_xn_modeq_le
- \+/\- *theorem* pell.eq_of_xn_modeq_lem1
- \+/\- *theorem* pell.eq_of_xn_modeq_lem2
- \+/\- *theorem* pell.eq_of_xn_modeq_lem3
- \+/\- *theorem* pell.eq_pell
- \+/\- *lemma* pell.eq_pell_lem
- \+/\- *theorem* pell.eq_pell_zd
- \+/\- *def* pell.is_pell
- \+/\- *theorem* pell.is_pell_conj
- \+/\- *theorem* pell.is_pell_mul
- \+/\- *theorem* pell.is_pell_nat
- \+/\- *theorem* pell.is_pell_norm
- \+/\- *theorem* pell.is_pell_one
- \+/\- *theorem* pell.is_pell_pell_zd
- \+/\- *theorem* pell.modeq_of_xn_modeq
- \+/\- *theorem* pell.n_lt_a_pow
- \+/\- *theorem* pell.n_lt_xn
- \+/\- *def* pell.pell
- \+/\- *theorem* pell.pell_eq
- \+/\- *theorem* pell.pell_eqz
- \+/\- *theorem* pell.pell_val
- \+/\- *def* pell.pell_zd
- \+/\- *theorem* pell.pell_zd_add
- \+/\- *theorem* pell.pell_zd_im
- \+/\- *theorem* pell.pell_zd_re
- \+/\- *theorem* pell.pell_zd_sub
- \+/\- *theorem* pell.pell_zd_succ
- \+/\- *theorem* pell.pell_zd_succ_succ
- \+/\- *theorem* pell.x_increasing
- \+/\- *theorem* pell.x_pos
- \+/\- *theorem* pell.x_sub_y_dvd_pow
- \+/\- *lemma* pell.x_sub_y_dvd_pow_lem
- \+/\- *def* pell.xn
- \+/\- *theorem* pell.xn_add
- \+/\- *theorem* pell.xn_ge_a_pow
- \+/\- *theorem* pell.xn_modeq_x2n_add
- \+/\- *theorem* pell.xn_modeq_x2n_add_lem
- \+/\- *theorem* pell.xn_modeq_x2n_sub
- \+/\- *lemma* pell.xn_modeq_x2n_sub_lem
- \+/\- *theorem* pell.xn_modeq_x4n_add
- \+/\- *theorem* pell.xn_modeq_x4n_sub
- \+/\- *theorem* pell.xn_one
- \+/\- *theorem* pell.xn_succ
- \+/\- *theorem* pell.xn_succ_succ
- \+/\- *theorem* pell.xn_zero
- \+/\- *theorem* pell.xy_coprime
- \+/\- *theorem* pell.xy_modeq_yn
- \+/\- *theorem* pell.xy_succ_succ
- \+/\- *def* pell.xz
- \+/\- *theorem* pell.xz_sub
- \+/\- *theorem* pell.xz_succ
- \+/\- *theorem* pell.xz_succ_succ
- \+/\- *theorem* pell.y_dvd_iff
- \+/\- *theorem* pell.y_increasing
- \+/\- *theorem* pell.y_mul_dvd
- \+/\- *def* pell.yn
- \+/\- *theorem* pell.yn_add
- \+/\- *theorem* pell.yn_ge_n
- \+/\- *theorem* pell.yn_modeq_a_sub_one
- \+/\- *theorem* pell.yn_modeq_two
- \+/\- *theorem* pell.yn_one
- \+/\- *theorem* pell.yn_succ
- \+/\- *theorem* pell.yn_succ_succ
- \+/\- *theorem* pell.yn_zero
- \+/\- *theorem* pell.ysq_dvd_yy
- \+/\- *def* pell.yz
- \+/\- *theorem* pell.yz_sub
- \+/\- *theorem* pell.yz_succ
- \+/\- *theorem* pell.yz_succ_succ

Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/coprime.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/set_theory/ordinal_notation.lean




## [2021-09-03 09:56:24](https://github.com/leanprover-community/mathlib/commit/5e27f50)
feat(analysis/complex/basic): convex_on.sup ([#8958](https://github.com/leanprover-community/mathlib/pull/8958))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* concave_on.inf
- \+ *lemma* convex_on.sup



## [2021-09-02 21:50:49](https://github.com/leanprover-community/mathlib/commit/fdc24f5)
feat(algebra/ordered_ring): `linear_ordered_semiring` extends `linear_ordered_add_comm_monoid` ([#8961](https://github.com/leanprover-community/mathlib/pull/8961))
#### Estimated changes
Modified src/algebra/ordered_ring.lean




## [2021-09-02 19:07:49](https://github.com/leanprover-community/mathlib/commit/d821860)
feat(group_theory/group_action/basic): class formula, Burnside's lemma ([#8801](https://github.com/leanprover-community/mathlib/pull/8801))
This adds class formula and Burnside's lemma for group action, both as an equiv and using cardinals.
I also added a cardinal version of the Orbit-stabilizer theorem.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/data/equiv/basic.lean
- \+ *def* equiv.sigma_assoc

Modified src/group_theory/group_action/basic.lean
- \+ *lemma* add_action.stabilizer_vadd_eq_stabilizer_map_conj
- \+ *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer'
- \+ *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer
- \+ *lemma* mul_action.card_orbit_mul_card_stabilizer_eq_card_group
- \+ *def* mul_action.self_equiv_sigma_orbits'
- \+ *lemma* mul_action.stabilizer_smul_eq_stabilizer_map_conj
- \+ *lemma* mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group

Modified src/group_theory/subgroup.lean
- \+ *def* mul_equiv.subgroup_equiv_map

Modified src/group_theory/submonoid/operations.lean
- \+ *def* mul_equiv.submonoid_equiv_map



## [2021-09-02 15:21:36](https://github.com/leanprover-community/mathlib/commit/17747c0)
feat(number_theory): define number fields, function fields and their rings of integers ([#8701](https://github.com/leanprover-community/mathlib/pull/8701))
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* char_zero.of_algebra

Modified src/algebraic_geometry/structure_sheaf.lean


Added src/number_theory/function_field.lean
- \+ *def* function_field.ring_of_integers

Added src/number_theory/number_field.lean
- \+ *lemma* number_field.ring_of_integers.is_integral_coe
- \+ *def* number_field.ring_of_integers

Modified src/ring_theory/integrally_closed.lean
- \+ *lemma* integral_closure.is_integrally_closed_of_finite_extension

Modified src/ring_theory/localization.lean
- \- *lemma* is_localization.epic_of_localization_map
- \+ *lemma* is_localization.monoid_hom_ext
- \+ *lemma* is_localization.ring_hom_ext



## [2021-09-02 14:35:26](https://github.com/leanprover-community/mathlib/commit/88525a9)
feat(ring_theory/ideal): generalize from `integral_closure` to `is_integral_closure` ([#8944](https://github.com/leanprover-community/mathlib/pull/8944))
This PR restates a couple of lemmas about ideals the integral closure to use an instance of `is_integral_closure` instead. The originals are still available, but their proofs are now oneliners shelling out to `is_integral_closure`.
#### Estimated changes



## [2021-09-02 12:25:11](https://github.com/leanprover-community/mathlib/commit/55a7d38)
feat(group_theory/coset): rw lemmas involving quotient_group.mk ([#8957](https://github.com/leanprover-community/mathlib/pull/8957))
When doing computations with quotient groups, I found these lemmas to be helpful when rewriting.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.eq'
- \+ *lemma* quotient_group.out_eq'



## [2021-09-02 12:25:09](https://github.com/leanprover-community/mathlib/commit/baefdf3)
fix(group_theory/group_action/defs): deduplicate `const_smul_hom` and `distrib_mul_action.to_add_monoid_hom` ([#8953](https://github.com/leanprover-community/mathlib/pull/8953))
This removes `const_smul_hom` as `distrib_mul_action.to_add_monoid_hom` fits a larger family of similarly-named definitions.
This also renames `distrib_mul_action.hom_add_monoid_hom` to `distrib_mul_action.to_add_monoid_End` to better match its statement.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Definition.20elimination.20contest/near/237347199)
#### Estimated changes
Modified src/algebra/direct_sum/algebra.lean


Modified src/algebra/group_ring_action.lean
- \- *def* distrib_mul_action.hom_add_monoid_hom
- \- *def* distrib_mul_action.to_add_monoid_hom

Modified src/algebra/module/basic.lean


Modified src/algebra/polynomial/group_ring_action.lean


Modified src/group_theory/group_action/basic.lean


Modified src/group_theory/group_action/defs.lean
- \- *def* const_smul_hom
- \- *lemma* const_smul_hom_apply
- \- *lemma* const_smul_hom_one
- \+ *def* distrib_mul_action.to_add_monoid_End
- \+ *def* distrib_mul_action.to_add_monoid_hom

Modified src/topology/algebra/infinite_sum.lean




## [2021-09-02 10:34:12](https://github.com/leanprover-community/mathlib/commit/1dddd7f)
feat(algebra/group/hom_instance): additive endomorphisms form a ring ([#8954](https://github.com/leanprover-community/mathlib/pull/8954))
We already have all the data to state this, this just provides the extra proofs.
The multiplicative version is nasty because `monoid.End` has two different multiplicative structures depending on whether `End` is unfolded; so this PR leaves that until someone actually needs it.
With this in place we can provide `module.to_add_monoid_End : R →+* add_monoid.End M` in a future PR.
#### Estimated changes
Modified src/algebra/group/hom_instances.lean




## [2021-09-02 09:31:58](https://github.com/leanprover-community/mathlib/commit/2fa8251)
refactor(*): rename {topological,smooth}_semiring to {topological,smooth}_ring ([#8902](https://github.com/leanprover-community/mathlib/pull/8902))
A topological semiring that is a ring, is a topological ring.
A smooth semiring that is a ring, is a smooth ring.
This PR renames:
* `topological_semiring` -> `topological_ring`
* `smooth_semiring` -> `smooth_ring`
It drops the existing `topological_ring` and `smooth_ring`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/algebra/structures.lean
- \+/\- *lemma* topological_ring_of_smooth
- \- *lemma* topological_semiring_of_smooth

Modified src/topology/algebra/algebra.lean
- \+/\- *lemma* continuous_algebra_map
- \+/\- *lemma* continuous_algebra_map_iff_smul
- \+/\- *lemma* has_continuous_smul_of_algebra_map

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/polynomial.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean




## [2021-09-02 08:19:17](https://github.com/leanprover-community/mathlib/commit/289e6dc)
feat(category_theory/limits/kan_extension): Prove (co)reflectivity for Kan extensions ([#8962](https://github.com/leanprover-community/mathlib/pull/8962))
#### Estimated changes
Modified src/category_theory/limits/kan_extension.lean
- \+ *lemma* category_theory.Lan.coreflective
- \+ *lemma* category_theory.Ran.reflective



## [2021-09-02 08:19:16](https://github.com/leanprover-community/mathlib/commit/8da6699)
chore(analysis/convex/basic): generalize `concave_on.le_on_segment` to monoids ([#8959](https://github.com/leanprover-community/mathlib/pull/8959))
This matches the generalization already present on `convex_on.le_on_segment`.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.le_on_segment



## [2021-09-02 08:19:14](https://github.com/leanprover-community/mathlib/commit/9d3e3e8)
feat(ring_theory/dedekind_domain): the integral closure of a DD is a DD ([#8847](https://github.com/leanprover-community/mathlib/pull/8847))
Let `L` be a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain. Then any `is_integral_closure C A L` is also a Dedekind domain, in particular for `C := integral_closure A L`.
In combination with the definitions of [#8701](https://github.com/leanprover-community/mathlib/pull/8701), we can conclude that rings of integers are Dedekind domains.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* exists_integral_multiples
- \+ *lemma* finite_dimensional.exists_is_basis_integral
- \+ *lemma* integral_closure.is_dedekind_domain
- \+ *lemma* integral_closure.is_noetherian_ring
- \+ *lemma* integral_closure_le_span_dual_basis
- \+ *lemma* is_integral_closure.is_dedekind_domain
- \+ *lemma* is_integral_closure.is_noetherian_ring
- \+ *lemma* is_integral_closure.range_le_span_dual_basis
- \+ *lemma* ring.dimension_le_one.is_integral_closure

Modified src/ring_theory/ideal/over.lean
- \+ *lemma* ideal.is_integral_closure.comap_lt_comap
- \+ *lemma* ideal.is_integral_closure.comap_ne_bot
- \+ *lemma* ideal.is_integral_closure.eq_bot_of_comap_eq_bot
- \+ *lemma* ideal.is_integral_closure.is_maximal_of_is_maximal_comap

Modified src/ring_theory/localization.lean
- \+ *lemma* is_integral_closure.is_fraction_ring_of_algebraic
- \+ *lemma* is_integral_closure.is_fraction_ring_of_finite_extension

Modified src/ring_theory/trace.lean
- \+/\- *lemma* det_trace_form_ne_zero
- \+ *theorem* trace_form_nondegenerate



## [2021-09-02 06:16:19](https://github.com/leanprover-community/mathlib/commit/6c24731)
feat(order/bounded_lattice): `ne_(bot|top)_iff_exists` ([#8960](https://github.com/leanprover-community/mathlib/pull/8960))
Like `ne_zero_iff_exists`
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* with_bot.ne_bot_iff_exists
- \+ *lemma* with_top.ne_top_iff_exists



## [2021-09-01 19:25:02](https://github.com/leanprover-community/mathlib/commit/07c57b5)
feat(group_theory): Add `monoid_hom.mker` and generalise the codomain for `monoid_hom.ker` ([#8532](https://github.com/leanprover-community/mathlib/pull/8532))
Add `monoid_hom.mker` for `f : M ->* N`, where `M` and `N` are `mul_one_class`es, and `monoid_hom.ker` is now defined for `f : G ->* H`, where `H` is a `mul_one_class`
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+/\- *lemma* monoid_hom.coe_ker
- \+/\- *def* monoid_hom.ker
- \+/\- *lemma* monoid_hom.ker_one
- \+/\- *lemma* monoid_hom.mem_ker

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* monoid_hom.coe_mker
- \+ *lemma* monoid_hom.comap_bot'
- \+ *lemma* monoid_hom.comap_mker
- \+ *lemma* monoid_hom.mem_mker
- \+ *def* monoid_hom.mker
- \+ *lemma* monoid_hom.mker_one
- \+ *lemma* monoid_hom.mker_prod_map
- \+ *lemma* monoid_hom.prod_map_comap_prod'
- \+ *lemma* monoid_hom.range_restrict_mker



## [2021-09-01 17:19:33](https://github.com/leanprover-community/mathlib/commit/0b8a858)
feat(tactic/lint): minor linter improvements ([#8934](https://github.com/leanprover-community/mathlib/pull/8934))
* Change `#print foo` with `#check @foo` in the output of the linter
* Include the number of linters in the output message
* add `attribute [nolint syn_taut] rfl`
#### Estimated changes
Modified scripts/lint_mathlib.lean


Modified src/tactic/lint/frontend.lean


Modified src/tactic/lint/misc.lean


Modified test/lint.lean




## [2021-09-01 15:38:10](https://github.com/leanprover-community/mathlib/commit/9b00046)
chore(algebra,group_theory,right_theory,linear_algebra): add missing lemmas ([#8948](https://github.com/leanprover-community/mathlib/pull/8948))
This adds:
* `sub{group,ring,semiring}.map_id`
* `submodule.add_mem_sup`
* `submodule.map_add_le`
And moves `submodule.sum_mem_supr` and `submodule.sum_mem_bsupr` to an earlier file.
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* submodule.add_mem_sup
- \+ *lemma* submodule.sum_mem_bsupr
- \+ *lemma* submodule.sum_mem_supr

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.map_id

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.map_add_le
- \- *lemma* submodule.sum_mem_bsupr
- \- *lemma* submodule.sum_mem_supr

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.map_id

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.map_id



## [2021-09-01 14:07:44](https://github.com/leanprover-community/mathlib/commit/2beaa28)
fix(category_theory/adjunction/basic): Fix typo in docstring ([#8950](https://github.com/leanprover-community/mathlib/pull/8950))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean




## [2021-09-01 14:07:42](https://github.com/leanprover-community/mathlib/commit/510e65d)
feat(topology/algebra/localization): add topological localization ([#8894](https://github.com/leanprover-community/mathlib/pull/8894))
We show that ring topologies on a ring `R` form a complete lattice.
We use this to define the topological localization of a topological commutative ring `R` at a submonoid `M`.
#### Estimated changes
Added src/topology/algebra/localization.lean
- \+ *def* localization.ring_topology

Modified src/topology/algebra/ring.lean
- \+ *def* ring_topology.coinduced
- \+ *lemma* ring_topology.coinduced_continuous
- \+ *lemma* ring_topology.ext'



## [2021-09-01 12:16:34](https://github.com/leanprover-community/mathlib/commit/d472e1b)
feat(order/basic): recursor for order_dual ([#8938](https://github.com/leanprover-community/mathlib/pull/8938))
#### Estimated changes
Modified src/order/basic.lean


Modified src/order/order_dual.lean




## [2021-09-01 12:16:33](https://github.com/leanprover-community/mathlib/commit/0970d07)
feat(order/well_founded): define `function.argmin`, `function.argmin_on` ([#8895](https://github.com/leanprover-community/mathlib/pull/8895))
Evidently, these are just thin wrappers around `well_founded.min` but I think
this use case is common enough to deserve this specialisation.
#### Estimated changes
Modified src/order/well_founded.lean
- \+ *lemma* function.argmin_le
- \+ *lemma* function.argmin_on_le
- \+ *lemma* function.argmin_on_mem
- \+ *lemma* function.not_lt_argmin
- \+ *lemma* function.not_lt_argmin_on



## [2021-09-01 12:16:32](https://github.com/leanprover-community/mathlib/commit/faf5e5c)
feat(order/bounded_lattice): unbot and untop ([#8885](https://github.com/leanprover-community/mathlib/pull/8885))
`unbot` sends non-`⊥` elements of `with_bot α` to the corresponding element of `α`. `untop` does the analogous thing for `with_top`.
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *def* with_bot.unbot
- \+ *lemma* with_bot.unbot_coe
- \+ *def* with_top.untop
- \+ *lemma* with_top.untop_coe



## [2021-09-01 10:35:59](https://github.com/leanprover-community/mathlib/commit/f3101e8)
feat(group_theory/perm/basic): permutations of a subtype ([#8691](https://github.com/leanprover-community/mathlib/pull/8691))
This is the same as `(equiv.refl _)^.set.compl .symm.trans (subtype_equiv_right $ by simp)` (up to a `compl`) but with better unfolding.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.subtype_equiv_subtype_perm_apply_of_mem
- \+ *lemma* equiv.perm.subtype_equiv_subtype_perm_apply_of_not_mem



## [2021-09-01 07:45:41](https://github.com/leanprover-community/mathlib/commit/73f50ac)
feat(algebraic_geometry): Redefine Schemes in terms of isos of locally ringed spaces ([#8888](https://github.com/leanprover-community/mathlib/pull/8888))
Addresses the project mentioned in `Scheme.lean` to redefine Schemes in terms of isomorphisms of locally ringed spaces, instead of presheafed spaces.
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean
- \+ *def* algebraic_geometry.SheafedSpace.restrict_top_iso



## [2021-09-01 07:45:39](https://github.com/leanprover-community/mathlib/commit/5b04a89)
feat(measure_theory/conditional_expectation): the integral of the norm of the conditional expectation is lower  ([#8318](https://github.com/leanprover-community/mathlib/pull/8318))
Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable function, such that their integrals coincide on `m`-measurable sets with finite measure. Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure.
This PR also defines a notation `measurable[m] f`, to mean that `f : α → β` is measurable with respect to the `measurable_space` `m` on `α`.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.indicator_le_indicator_nonneg
- \+ *lemma* set.indicator_nonpos_le_indicator

Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.integral_norm_le_of_forall_fin_meas_integral_eq
- \+ *lemma* measure_theory.lintegral_nnnorm_le_of_forall_fin_meas_integral_eq

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.of_real_integral_norm_eq_lintegral_nnnorm

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_add_compl
- \+ *lemma* measure_theory.set_lintegral_congr_fun

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_norm_eq_pos_sub_neg
- \+ *lemma* measure_theory.set_integral_eq_zero_of_forall_eq_zero
- \+ *lemma* measure_theory.set_integral_le_nonneg
- \+ *lemma* measure_theory.set_integral_neg_eq_set_integral_nonpos
- \+ *lemma* measure_theory.set_integral_nonpos_le
- \+ *lemma* measure_theory.set_integral_union_eq_left

Modified src/measure_theory/measurable_space_def.lean




## [2021-09-01 05:57:01](https://github.com/leanprover-community/mathlib/commit/f0451d8)
feat(algebra/group/defs): ext lemmas for (semi)groups and monoids ([#8391](https://github.com/leanprover-community/mathlib/pull/8391))
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.236476.20boolean_algebra.2Eto_boolean_ring/near/242118386)
#### Estimated changes
Modified src/algebra/group/defs.lean
- \+ *lemma* cancel_comm_monoid.ext
- \+ *lemma* cancel_comm_monoid.to_comm_monoid_injective
- \+ *lemma* cancel_monoid.ext
- \+ *lemma* cancel_monoid.to_left_cancel_monoid_injective
- \+ *lemma* comm_group.ext
- \+ *lemma* comm_group.to_group_injective
- \+ *lemma* comm_monoid.ext
- \+ *lemma* comm_monoid.to_monoid_injective
- \+ *lemma* div_inv_monoid.ext
- \+ *lemma* group.ext
- \+ *lemma* group.to_div_inv_monoid_injective
- \+ *lemma* left_cancel_monoid.ext
- \+ *lemma* left_cancel_monoid.to_monoid_injective
- \+ *lemma* monoid.ext
- \+ *lemma* mul_one_class.ext
- \+ *lemma* right_cancel_monoid.ext
- \+ *lemma* right_cancel_monoid.to_monoid_injective

Modified src/category_theory/preadditive/schur.lean


Modified test/equiv_rw.lean


