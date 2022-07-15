## [2021-08-31 23:00:50](https://github.com/leanprover-community/mathlib/commit/065a35d)
feat(algebra/{pointwise,algebra/operations}): add `supr_mul` and `mul_supr` ([#8923](https://github.com/leanprover-community/mathlib/pull/8923))
Requested by @eric-wieser  on Zulip, https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/submodule.2Esupr_mul/near/250122435
and a couple of helper lemmas.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.mul_eq_span_mul_set
- \+ *lemma* submodule.mul_supr
- \+ *lemma* submodule.supr_mul

Modified src/algebra/pointwise.lean
- \+ *lemma* set.Union_mul
- \+ *lemma* set.mul_Union



## [2021-08-31 21:31:09](https://github.com/leanprover-community/mathlib/commit/9339006)
feat(algebra/{module/linear_map, algebra/basic}): Add `distrib_mul_action.to_linear_(map|equiv)` and `mul_semiring_action.to_alg_(hom|equiv)` ([#8936](https://github.com/leanprover-community/mathlib/pull/8936))
This adds the following stronger versions of `distrib_mul_action.to_add_monoid_hom`:
* `distrib_mul_action.to_linear_map`
* `distrib_mul_action.to_linear_equiv`
* `mul_semiring_action.to_alg_hom`
* `mul_semiring_action.to_alg_equiv`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/group.20acting.20on.20algebra/near/251372497)
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* mul_semiring_action.to_alg_equiv
- \+ *def* mul_semiring_action.to_alg_hom

Modified src/algebra/group_ring_action.lean
- \+ *def* mul_semiring_action.to_ring_equiv
- \- *def* mul_semiring_action.to_semiring_equiv

Modified src/algebra/module/linear_map.lean
- \+ *def* distrib_mul_action.to_linear_equiv
- \+ *def* distrib_mul_action.to_linear_map



## [2021-08-31 15:40:30](https://github.com/leanprover-community/mathlib/commit/3d6a828)
chore(order/bounded_lattice): dot-notation lemmas ne.bot_lt and ne.lt_top ([#8935](https://github.com/leanprover-community/mathlib/pull/8935))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* ne.bot_lt'
- \+ *lemma* ne.bot_lt
- \+ *lemma* ne.lt_top'
- \+ *lemma* ne.lt_top



## [2021-08-31 15:40:29](https://github.com/leanprover-community/mathlib/commit/12bbd53)
chore(topology/metric_space/basic): add `metric.uniform_continuous_on_iff_le` ([#8906](https://github.com/leanprover-community/mathlib/pull/8906))
This is a version of `metric.uniform_continuous_on_iff` with `≤ δ` and
`≤ ε` instead of `< δ` and `< ε`. Also golf the proof of
`metric.uniform_continuous_on_iff`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.uniform_continuous_on_iff_le



## [2021-08-31 15:40:28](https://github.com/leanprover-community/mathlib/commit/603a606)
feat(measure_theory/hausdorff_measure): dimH and Hölder/Lipschitz maps ([#8361](https://github.com/leanprover-community/mathlib/pull/8361))
* expand module docs;
* prove that a Lipschitz continuous map does not increase Hausdorff measure and Hausdorff dimension of sets;
* prove similar lemmas about Hölder continuous and antilipschitz maps;
* add convenience lemmas for some bundled types and for `Cⁿ` smooth maps;
* Hausdorff dimension of `ℝⁿ` equals `n`;
* prove a baby version of Sard's theorem: if `f : E → F` is a `C¹` smooth map between normed vector spaces such that `finrank ℝ E < finrank ℝ F`, then `(range f)ᶜ` is dense.
#### Estimated changes
Modified src/measure_theory/measure/hausdorff.lean
- \+ *lemma* antilipschitz_with.dimH_preimage_le
- \+ *lemma* antilipschitz_with.hausdorff_measure_preimage_le
- \+ *lemma* antilipschitz_with.le_dimH_image
- \+ *lemma* antilipschitz_with.le_hausdorff_measure_image
- \+ *lemma* continuous_linear_equiv.dimH_image
- \+ *lemma* continuous_linear_equiv.dimH_preimage
- \+ *lemma* continuous_linear_equiv.dimH_univ
- \+ *theorem* dense_compl_of_dimH_lt_finrank
- \+ *lemma* dimH_image_le_of_locally_holder_on
- \+ *lemma* dimH_image_le_of_locally_lipschitz_on
- \+ *lemma* dimH_range_le_of_locally_holder_on
- \+ *lemma* dimH_range_le_of_locally_lipschitz_on
- \+ *lemma* holder_on_with.dimH_image_le
- \+ *lemma* holder_on_with.hausdorff_measure_image_le
- \+ *lemma* holder_with.dimH_image_le
- \+ *lemma* holder_with.dimH_range_le
- \+ *lemma* isometric.dimH_image
- \+ *lemma* isometric.dimH_preimage
- \+ *lemma* isometric.dimH_univ
- \+ *lemma* isometric.hausdorff_measure_image
- \+ *lemma* isometric.hausdorff_measure_preimage
- \+ *lemma* isometry.dimH_image
- \+ *lemma* isometry.hausdorff_measure_image
- \+ *lemma* isometry.hausdorff_measure_preimage
- \+ *lemma* isometry.map_hausdorff_measure
- \+ *lemma* lipschitz_on_with.dimH_image_le
- \+ *lemma* lipschitz_on_with.hausdorff_measure_image_le
- \+ *lemma* lipschitz_with.dimH_image_le
- \+ *lemma* lipschitz_with.dimH_range_le
- \+ *lemma* lipschitz_with.hausdorff_measure_image_le
- \+ *lemma* measure_theory.dimH_le_of_hausdorff_measure_ne_top
- \+ *lemma* measure_theory.dimH_of_hausdorff_measure_ne_zero_ne_top
- \+/\- *theorem* measure_theory.hausdorff_measure_pi_real
- \+ *lemma* measure_theory.le_dimH_of_hausdorff_measure_ne_zero
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

Modified src/ring_theory/noetherian.lean


Modified src/topology/bases.lean
- \+ *lemma* topological_space.countable_cover_nhds_within

Modified src/topology/continuous_on.lean
- \+ *theorem* mem_nhds_subtype_iff_nhds_within
- \+ *theorem* preimage_coe_mem_nhds_subtype



## [2021-08-31 13:58:34](https://github.com/leanprover-community/mathlib/commit/d9b2db9)
chore(group_theory/submonoid/center): fix typo and extend docstring ([#8937](https://github.com/leanprover-community/mathlib/pull/8937))
#### Estimated changes
Modified src/group_theory/submonoid/center.lean




## [2021-08-31 10:54:15](https://github.com/leanprover-community/mathlib/commit/ab967d2)
feat(group_theory/submonoid): center of a submonoid ([#8921](https://github.com/leanprover-community/mathlib/pull/8921))
This adds `set.center`, `submonoid.center`, `subsemiring.center`, and `subring.center`, to complement the existing `subgroup.center`.
This ran into a timeout, so had to squeeze some `simp`s in an unrelated file.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.center_to_submonoid
- \+ *lemma* subgroup.coe_center

Added src/group_theory/submonoid/center.lean
- \+ *lemma* set.add_mem_center
- \+ *def* set.center
- \+ *lemma* set.center_eq_univ
- \+ *lemma* set.center_units_eq
- \+ *lemma* set.center_units_subset
- \+ *lemma* set.inv_mem_center'
- \+ *lemma* set.inv_mem_center
- \+ *lemma* set.mem_center_iff
- \+ *lemma* set.mul_mem_center
- \+ *lemma* set.neg_mem_center
- \+ *lemma* set.one_mem_center
- \+ *lemma* set.subset_center_units
- \+ *lemma* set.zero_mem_center
- \+ *def* submonoid.center
- \+ *lemma* submonoid.center_eq_top
- \+ *lemma* submonoid.coe_center
- \+ *lemma* submonoid.mem_center_iff

Modified src/ring_theory/subring.lean
- \+ *def* subring.center
- \+ *lemma* subring.center_eq_top
- \+ *lemma* subring.center_to_subsemiring
- \+ *lemma* subring.coe_center
- \+ *lemma* subring.mem_center_iff

Modified src/ring_theory/subsemiring.lean
- \+ *def* subsemiring.center
- \+ *lemma* subsemiring.center_eq_top
- \+ *lemma* subsemiring.center_to_submonoid
- \+ *lemma* subsemiring.coe_center
- \+ *lemma* subsemiring.mem_center_iff



## [2021-08-31 09:04:38](https://github.com/leanprover-community/mathlib/commit/6b63c03)
fix(order/rel_classes): remove looping instance ([#8931](https://github.com/leanprover-community/mathlib/pull/8931))
This instance causes loop with `is_total_preorder.to_is_total`, and was unused in the library.
Caught by the new linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932)).
#### Estimated changes
Modified src/order/rel_classes.lean




## [2021-08-31 09:04:37](https://github.com/leanprover-community/mathlib/commit/53f074c)
fix(data/complex/basic): better formulas for nsmul and gsmul on complex to fix a diamond ([#8928](https://github.com/leanprover-community/mathlib/pull/8928))
As diagnosed by @eric-wieser in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/diamond.20in.20data.2Ecomplex.2Emodule/near/250318167
After the PR,
```lean
example :
  (sub_neg_monoid.has_scalar_int : has_scalar ℤ ℂ) = (complex.has_scalar : has_scalar ℤ ℂ) :=
rfl
```
works fine, while it fails on current master.
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/complex/module.lean


Modified test/instance_diamonds.lean




## [2021-08-31 09:04:36](https://github.com/leanprover-community/mathlib/commit/c04e8a4)
feat(logic/basic): equivalence of by_contra and choice ([#8912](https://github.com/leanprover-community/mathlib/pull/8912))
Based on an email suggestion from Freek Wiedijk: `classical.choice` is equivalent to the following Type-valued variation on `by_contradiction`:
```lean
axiom classical.by_contradiction' {α : Sort*} : ¬ (α → false) → α
```
#### Estimated changes
Modified src/logic/basic.lean
- \+ *def* classical.choice_of_by_contradiction'



## [2021-08-31 09:04:35](https://github.com/leanprover-community/mathlib/commit/1c13454)
feat(algebraic_geometry): Restriction of locally ringed spaces ([#8809](https://github.com/leanprover-community/mathlib/pull/8809))
Proves that restriction of presheafed spaces doesn't change the stalks and defines the restriction of a locally ringed space along an open embedding.
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.of_restrict

Modified src/algebraic_geometry/stalks.lean
- \+ *def* algebraic_geometry.PresheafedSpace.restrict_stalk_iso
- \+ *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_hom_eq_germ
- \+ *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_germ

Modified src/topology/category/Top/open_nhds.lean
- \+ *def* is_open_map.adjunction_nhds
- \+ *def* is_open_map.functor_nhds



## [2021-08-31 07:22:54](https://github.com/leanprover-community/mathlib/commit/1dbd561)
refactor(order/atoms): reorder arguments of `is_simple_lattice.fintype` ([#8933](https://github.com/leanprover-community/mathlib/pull/8933))
Previously, this instance would first look for `decidable_eq` instances and after that for `is_simple_lattice` instances. The latter has only 4 instances, while the former takes hundreds of steps. Reordering the arguments makes a lot of type-class searches fail a lot quicker.
Caught by the new linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932)).
#### Estimated changes
Modified src/order/atoms.lean




## [2021-08-31 02:54:16](https://github.com/leanprover-community/mathlib/commit/22a297c)
feat(algebra/module/prod,pi): instances for actions with zero ([#8929](https://github.com/leanprover-community/mathlib/pull/8929))
#### Estimated changes
Modified src/algebra/module/pi.lean


Modified src/algebra/module/prod.lean




## [2021-08-31 01:35:58](https://github.com/leanprover-community/mathlib/commit/f4d7205)
chore(measure_theory/*): rename `probability_measure` and `finite_measure` ([#8831](https://github.com/leanprover-community/mathlib/pull/8831))
Renamed to `is_probability_measure` and `is_finite_measure`, respectively.  Also, `locally_finite_measure` becomes `is_locally_finite_measure`. See
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238337.20Weak.20convergence
#### Estimated changes
Modified counterexamples/phillips.lean
- \+/\- *lemma* phillips_1940.extension_to_bounded_functions_apply
- \+/\- *lemma* phillips_1940.to_functions_to_measure

Modified docs/undergrad.yaml


Modified src/analysis/convex/integral.lean
- \+/\- *lemma* convex.integral_mem
- \+/\- *lemma* convex_on.map_integral_le
- \+/\- *lemma* convex_on.map_smul_integral_le

Modified src/analysis/fourier.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/dynamics/ergodic/measure_preserving.lean
- \+/\- *lemma* measure_theory.measure_preserving.exists_mem_image_mem

Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *def* real.finite_spanning_sets_in_Ioo_rat
- \+/\- *lemma* real.measure_ext_Ioo_rat

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean
- \+/\- *lemma* measurable_measure_prod_mk_left_finite

Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean
- \+/\- *lemma* measure_theory.hahn_decomposition

Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/function/conditional_expectation.lean
- \- *lemma* measure_theory.integrable_condexp_L2_of_finite_measure
- \+ *lemma* measure_theory.integrable_condexp_L2_of_is_finite_measure

Modified src/measure_theory/function/continuous_map_dense.lean
- \+/\- *lemma* bounded_continuous_function.to_Lp_dense_range
- \+/\- *lemma* continuous_map.to_Lp_dense_range

Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.has_finite_integral_const
- \+/\- *lemma* measure_theory.has_finite_integral_of_bounded
- \+/\- *lemma* measure_theory.integrable.const_mul
- \+/\- *lemma* measure_theory.integrable.mul_const
- \+/\- *lemma* measure_theory.integrable_const
- \+/\- *lemma* measure_theory.integrable_neg_iff
- \+/\- *lemma* measure_theory.mem_ℒp.integrable

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* measure_theory.Lp.antimono
- \+/\- *lemma* measure_theory.Lp.mem_Lp_const
- \+/\- *lemma* measure_theory.Lp.mem_Lp_of_ae_bound
- \+/\- *lemma* measure_theory.Lp.norm_le_of_ae_bound
- \+/\- *lemma* measure_theory.mem_ℒp.mem_ℒp_of_exponent_le
- \+/\- *lemma* measure_theory.mem_ℒp.of_bound
- \+/\- *lemma* measure_theory.mem_ℒp_const
- \+/\- *lemma* measure_theory.snorm'_const'
- \+ *lemma* measure_theory.snorm'_const_of_is_probability_measure
- \- *lemma* measure_theory.snorm'_const_of_probability_measure
- \+/\- *lemma* measure_theory.snorm'_le_snorm_ess_sup
- \+/\- *lemma* measure_theory.snorm'_lt_top_of_snorm'_lt_top_of_exponent_le
- \+/\- *lemma* measure_theory.snorm_le_snorm_of_exponent_le

Modified src/measure_theory/function/simple_func_dense.lean
- \- *lemma* measure_theory.simple_func.integrable_of_finite_measure
- \+ *lemma* measure_theory.simple_func.integrable_of_is_finite_measure
- \+/\- *lemma* measure_theory.simple_func.measure_support_lt_top_of_integrable
- \- *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_is_finite_measure

Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.norm_integral_le_of_norm_le_const

Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_const_of_cdf

Modified src/measure_theory/integral/lebesgue.lean
- \- *lemma* measure_theory.finite_measure_with_density
- \+ *lemma* measure_theory.is_finite_measure_with_density

Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* is_compact.finite_measure
- \- *lemma* is_compact.finite_measure_of_nhds_within
- \+ *lemma* is_compact.is_finite_measure
- \+ *lemma* is_compact.is_finite_measure_of_nhds_within
- \+/\- *lemma* measure_theory.coe_measure_univ_nnreal
- \+/\- *lemma* measure_theory.ext_of_generate_finite
- \- *lemma* measure_theory.finite_measure_of_le
- \+ *lemma* measure_theory.is_finite_measure_of_le
- \+ *lemma* measure_theory.is_probability_measure.ne_zero
- \+/\- *lemma* measure_theory.measure.finite_at_filter_of_finite
- \+/\- *lemma* measure_theory.measure.le_of_add_le_add_left
- \+/\- *lemma* measure_theory.measure.smul_finite
- \+/\- *lemma* measure_theory.measure.sub_add_cancel_of_le
- \+/\- *lemma* measure_theory.measure.sub_apply
- \+/\- *lemma* measure_theory.measure_lt_top
- \+/\- *lemma* measure_theory.measure_ne_top
- \+/\- *lemma* measure_theory.measure_univ_nnreal_eq_zero
- \+/\- *lemma* measure_theory.measure_univ_nnreal_pos
- \+/\- *lemma* measure_theory.prob_add_prob_compl
- \+/\- *lemma* measure_theory.prob_le_one
- \- *lemma* measure_theory.probability_measure.ne_zero
- \+/\- *lemma* measure_theory.summable_measure_to_real
- \- *lemma* metric.bounded.finite_measure
- \+ *lemma* metric.bounded.is_finite_measure

Modified src/measure_theory/measure/regular.lean
- \- *lemma* measurable_set.measure_eq_supr_is_closed_of_finite_measure
- \+ *lemma* measurable_set.measure_eq_supr_is_closed_of_is_finite_measure
- \- *theorem* measure_theory.measure.weakly_regular.weakly_regular_of_inner_regular_of_finite_measure
- \+ *theorem* measure_theory.measure.weakly_regular.weakly_regular_of_inner_regular_of_is_finite_measure

Modified src/measure_theory/measure/vector_measure.lean
- \+/\- *def* measure_theory.measure.to_signed_measure
- \+/\- *lemma* measure_theory.measure.to_signed_measure_add
- \+/\- *lemma* measure_theory.measure.to_signed_measure_apply_measurable
- \+/\- *lemma* measure_theory.measure.to_signed_measure_smul
- \+/\- *lemma* measure_theory.measure.to_signed_measure_sub_apply

Modified src/probability_theory/independence.lean




## [2021-08-30 18:18:38](https://github.com/leanprover-community/mathlib/commit/6adb5e8)
feat(topology/algebra/ordered): monotone convergence in pi types ([#8841](https://github.com/leanprover-community/mathlib/pull/8841))
* add typeclasses `Sup_convergence_class` and `Inf_convergence_class`
* reformulate theorems about monotone convergence in terms of these typeclasses;
* provide instances for a linear order with order topology, for products, and for pi types.
#### Estimated changes
Modified src/data/set/function.lean


Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* tendsto_at_bot_cinfi
- \+/\- *lemma* tendsto_at_bot_csupr
- \+/\- *lemma* tendsto_at_bot_infi
- \+/\- *lemma* tendsto_at_bot_is_glb
- \+ *lemma* tendsto_at_bot_is_lub
- \+/\- *lemma* tendsto_at_bot_supr
- \+/\- *lemma* tendsto_at_top_cinfi
- \+/\- *lemma* tendsto_at_top_csupr
- \+/\- *lemma* tendsto_at_top_infi
- \+ *lemma* tendsto_at_top_is_glb
- \+/\- *lemma* tendsto_at_top_is_lub
- \+/\- *lemma* tendsto_at_top_supr



## [2021-08-30 16:14:57](https://github.com/leanprover-community/mathlib/commit/4a65197)
chore(algebra/direct_sum/algebra): add missing rfl lemmas ([#8924](https://github.com/leanprover-community/mathlib/pull/8924))
I realized I was resorting to nasty unfolding to get these mid-proof
#### Estimated changes
Modified src/algebra/direct_sum/algebra.lean
- \+ *lemma* direct_sum.algebra_map_apply
- \+ *lemma* direct_sum.algebra_map_to_add_monoid_hom



## [2021-08-30 16:14:56](https://github.com/leanprover-community/mathlib/commit/aa0694a)
fix(data/set/finite): drop {α : Type}, fixes universe issue ([#8922](https://github.com/leanprover-community/mathlib/pull/8922))
#### Estimated changes
Modified src/data/set/finite.lean
- \+/\- *lemma* set.finite.infinite_compl
- \+/\- *lemma* set.infinite_of_finite_compl



## [2021-08-30 16:14:55](https://github.com/leanprover-community/mathlib/commit/ad7519a)
doc(tactic/lint): instructions on fails_quickly failure ([#8910](https://github.com/leanprover-community/mathlib/pull/8910))
* Also set `is_fast` to `tt`, since it takes ~10s on all of mathlib.
#### Estimated changes
Modified src/tactic/lint/type_classes.lean




## [2021-08-30 16:14:54](https://github.com/leanprover-community/mathlib/commit/b3807ee)
chore(data/finset/basic): lemmas about `(range n).nonempty` ([#8905](https://github.com/leanprover-community/mathlib/pull/8905))
Add `finset.nonempty_range_iff`, `finset.range_eq_empty_iff`, and
`range.nonempty_range_succ`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.nonempty_range_iff
- \+ *lemma* finset.nonempty_range_succ
- \+ *lemma* finset.range_eq_empty_iff



## [2021-08-30 14:54:37](https://github.com/leanprover-community/mathlib/commit/1e89df2)
chore(algebra/monoid_algebra): convert a filename prefix into a folder ([#8925](https://github.com/leanprover-community/mathlib/pull/8925))
This moves:
* `algebra.monoid_algebra` to `algebra.monoid_algebra.basic`
* `algebra.monoid_algebra_to_direct_sum` to `algebra.monoid_algebra.to_direct_sum`
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/algebra/free_non_unital_non_assoc_algebra.lean


Renamed src/algebra/monoid_algebra.lean to src/algebra/monoid_algebra/basic.lean


Renamed src/algebra/monoid_algebra_to_direct_sum.lean to src/algebra/monoid_algebra/to_direct_sum.lean


Modified src/data/polynomial/basic.lean


Modified src/representation_theory/maschke.lean




## [2021-08-30 13:16:49](https://github.com/leanprover-community/mathlib/commit/98466d2)
feat(algebra/direct_sum): graded algebras ([#8783](https://github.com/leanprover-community/mathlib/pull/8783))
This provides a `direct_sum.galgebra` structure on top of the existing `direct_sum.gmonoid` structure.
This typeclass is used to provide an `algebra R (⨁ i, A i)` instance.
This also renames and improves the stateement of `direct_sum.module.ext` to `direct_sum.linear_map_ext` and adds `direect_sum.ring_hom_ext` and `direct_sum.alg_hom_ext` to match.
#### Estimated changes
Added src/algebra/direct_sum/algebra.lean
- \+ *lemma* direct_sum.alg_hom_ext
- \+ *def* direct_sum.to_algebra

Modified src/algebra/direct_sum/module.lean
- \+ *theorem* direct_sum.linear_map_ext
- \+ *lemma* direct_sum.lof_eq_of
- \- *theorem* direct_sum.to_module.ext

Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* direct_sum.ring_hom_ext

Modified src/algebra/monoid_algebra_to_direct_sum.lean


Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-08-29 18:50:41](https://github.com/leanprover-community/mathlib/commit/2bae06a)
fix(ring_theory/polynomial/homogeneous): spelling mistake in `homogeneous` ([#8914](https://github.com/leanprover-community/mathlib/pull/8914))
#### Estimated changes
Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* mv_polynomial.homogeneous_submodule_eq_finsupp_supported
- \+ *lemma* mv_polynomial.homogeneous_submodule_mul
- \- *lemma* mv_polynomial.homogenous_submodule_eq_finsupp_supported
- \- *lemma* mv_polynomial.homogenous_submodule_mul



## [2021-08-29 14:08:26](https://github.com/leanprover-community/mathlib/commit/395bb6c)
feat(algebraic_geometry): Lift isomorphism of sheafed spaces to locally ringed spaces ([#8887](https://github.com/leanprover-community/mathlib/pull/8887))
Adds the fact that an isomorphism of sheafed spaces can be lifted to an isomorphism of locally ringed spaces. The main ingredient is the fact that stalk maps of isomorphisms are again isomorphisms.
In particular, this implies that the forgetful functor `LocallyRingedSpace ⥤ SheafedSpace CommRing` reflects isomorphisms.
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.hom_of_SheafedSpace_hom_of_is_iso
- \+ *def* algebraic_geometry.LocallyRingedSpace.iso_of_SheafedSpace_iso

Modified src/algebraic_geometry/stalks.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr_hom
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr_point
- \+ *def* algebraic_geometry.PresheafedSpace.stalk_map.stalk_iso



## [2021-08-28 19:59:37](https://github.com/leanprover-community/mathlib/commit/d75a2d9)
refactor(data/set/finite): use `[fintype (plift ι)]` in `finite_Union` ([#8872](https://github.com/leanprover-community/mathlib/pull/8872))
This way we can use `finite_Union` instead of `finite_Union_Prop`.
#### Estimated changes
Modified src/data/set/finite.lean
- \+/\- *theorem* set.finite_Union
- \- *theorem* set.finite_Union_Prop
- \+/\- *theorem* set.finite_range

Modified src/topology/uniform_space/cauchy.lean




## [2021-08-28 18:30:09](https://github.com/leanprover-community/mathlib/commit/db06b5a)
feat(group_theory/perm/cycle_type): Fixed points of permutations of prime order ([#8832](https://github.com/leanprover-community/mathlib/pull/8832))
A few basic lemmas about fixed points of permutations of prime order.
#### Estimated changes
Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.card_compl_support_modeq
- \+ *lemma* equiv.perm.exists_fixed_point_of_prime'
- \+ *lemma* equiv.perm.exists_fixed_point_of_prime



## [2021-08-28 18:30:08](https://github.com/leanprover-community/mathlib/commit/e824b88)
refactor(category_theory/limits/final): Symmetric API for final and initial functors ([#8808](https://github.com/leanprover-community/mathlib/pull/8808))
Dualise the API for cofinal functors to symmetrically support final and initial functors.
This PR renames `cofinal` functors to `final` functors.
#### Estimated changes
Renamed src/category_theory/limits/cofinal.lean to src/category_theory/limits/final.lean
- \- *def* category_theory.cofinal.cocones_equiv
- \- *lemma* category_theory.cofinal.cofinal_of_colimit_comp_coyoneda_iso_punit
- \- *def* category_theory.cofinal.colimit_cocone_comp
- \- *lemma* category_theory.cofinal.colimit_cocone_comp_aux
- \- *def* category_theory.cofinal.colimit_cocone_of_comp
- \- *def* category_theory.cofinal.colimit_comp_coyoneda_iso
- \- *def* category_theory.cofinal.colimit_iso'
- \- *def* category_theory.cofinal.colimit_iso
- \- *lemma* category_theory.cofinal.colimit_pre_is_iso_aux
- \- *def* category_theory.cofinal.cones_equiv
- \- *def* category_theory.cofinal.extend_cocone
- \- *def* category_theory.cofinal.extend_cone
- \- *def* category_theory.cofinal.extend_cone_cocone_to_cone
- \- *def* category_theory.cofinal.extend_cone_cone_to_cocone
- \- *lemma* category_theory.cofinal.has_colimit_of_comp
- \- *lemma* category_theory.cofinal.has_limit_of_comp
- \- *def* category_theory.cofinal.hom_to_lift
- \- *lemma* category_theory.cofinal.induction
- \- *def* category_theory.cofinal.is_colimit_extend_cocone_equiv
- \- *def* category_theory.cofinal.is_colimit_whisker_equiv
- \- *def* category_theory.cofinal.is_limit_extend_cone_equiv
- \- *def* category_theory.cofinal.is_limit_whisker_equiv
- \- *def* category_theory.cofinal.lift
- \- *def* category_theory.cofinal.limit_cone_comp
- \- *lemma* category_theory.cofinal.limit_cone_comp_aux
- \- *def* category_theory.cofinal.limit_cone_of_comp
- \- *def* category_theory.cofinal.limit_iso'
- \- *def* category_theory.cofinal.limit_iso
- \- *lemma* category_theory.cofinal.limit_pre_is_iso_aux
- \- *lemma* category_theory.cofinal.zigzag_of_eqv_gen_quot_rel
- \+ *def* category_theory.functor.final.cocones_equiv
- \+ *lemma* category_theory.functor.final.cofinal_of_colimit_comp_coyoneda_iso_punit
- \+ *def* category_theory.functor.final.colimit_cocone_comp
- \+ *lemma* category_theory.functor.final.colimit_cocone_comp_aux
- \+ *def* category_theory.functor.final.colimit_cocone_of_comp
- \+ *def* category_theory.functor.final.colimit_comp_coyoneda_iso
- \+ *def* category_theory.functor.final.colimit_iso'
- \+ *def* category_theory.functor.final.colimit_iso
- \+ *lemma* category_theory.functor.final.colimit_pre_is_iso_aux
- \+ *def* category_theory.functor.final.extend_cocone
- \+ *lemma* category_theory.functor.final.has_colimit_of_comp
- \+ *def* category_theory.functor.final.hom_to_lift
- \+ *def* category_theory.functor.final.induction
- \+ *def* category_theory.functor.final.is_colimit_extend_cocone_equiv
- \+ *def* category_theory.functor.final.is_colimit_whisker_equiv
- \+ *def* category_theory.functor.final.lift
- \+ *lemma* category_theory.functor.final.zigzag_of_eqv_gen_quot_rel
- \+ *lemma* category_theory.functor.final_of_adjunction
- \+ *lemma* category_theory.functor.final_of_initial_op
- \+ *def* category_theory.functor.initial.cones_equiv
- \+ *def* category_theory.functor.initial.extend_cone
- \+ *lemma* category_theory.functor.initial.has_limit_of_comp
- \+ *def* category_theory.functor.initial.hom_to_lift
- \+ *def* category_theory.functor.initial.induction
- \+ *def* category_theory.functor.initial.is_limit_extend_cone_equiv
- \+ *def* category_theory.functor.initial.is_limit_whisker_equiv
- \+ *def* category_theory.functor.initial.lift
- \+ *def* category_theory.functor.initial.limit_cone_comp
- \+ *lemma* category_theory.functor.initial.limit_cone_comp_aux
- \+ *def* category_theory.functor.initial.limit_cone_of_comp
- \+ *def* category_theory.functor.initial.limit_iso'
- \+ *def* category_theory.functor.initial.limit_iso
- \+ *lemma* category_theory.functor.initial.limit_pre_is_iso_aux
- \+ *lemma* category_theory.functor.initial_of_adjunction
- \+ *lemma* category_theory.functor.initial_of_final_op

Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean




## [2021-08-28 18:30:07](https://github.com/leanprover-community/mathlib/commit/14a992b)
chore(data/set_like): some additional documentation ([#8765](https://github.com/leanprover-community/mathlib/pull/8765))
Gives some more explanation for `set_like` and what it does and is for.
#### Estimated changes
Modified src/data/set_like/basic.lean




## [2021-08-28 17:56:07](https://github.com/leanprover-community/mathlib/commit/0b48570)
feat(group_theory/nilpotent): add subgroups of nilpotent group are nilpotent ([#8854](https://github.com/leanprover-community/mathlib/pull/8854))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_map_subtype_le
- \+ *lemma* lower_central_series_succ



## [2021-08-28 16:48:45](https://github.com/leanprover-community/mathlib/commit/1aaff8d)
feat(measure_theory/decomposition/lebesgue): Lebesgue decomposition for sigma-finite measures ([#8875](https://github.com/leanprover-community/mathlib/pull/8875))
This PR shows sigma-finite measures `have_lebesgue_decomposition`. With this instance, `absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq` will provide the Radon-Nikodym theorem for sigma-finite measures.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable.ennreal_tsum'

Modified src/measure_theory/decomposition/lebesgue.lean
- \+ *theorem* measure_theory.measure.have_lebesgue_decomposition_of_finite_measure

Modified src/measure_theory/decomposition/radon_nikodym.lean
- \+ *theorem* measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
- \- *theorem* measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_derive_eq

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.with_density_indicator
- \+ *lemma* measure_theory.with_density_tsum

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.sum_add_sum
- \+ *lemma* measure_theory.measure.sum_congr



## [2021-08-28 09:42:18](https://github.com/leanprover-community/mathlib/commit/42b5e80)
feat(data/polynomial/basic): monomial_eq_zero_iff ([#8897](https://github.com/leanprover-community/mathlib/pull/8897))
Via a new `monomial_injective`.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.monomial_eq_zero_iff
- \+ *lemma* polynomial.monomial_injective



## [2021-08-28 08:03:49](https://github.com/leanprover-community/mathlib/commit/8ee05e9)
feat(data/nat/log): Ceil log ([#8764](https://github.com/leanprover-community/mathlib/pull/8764))
Defines the upper natural log, which is the least `k` such that `n ≤ b^k`.
Also expand greatly the docs of `data.nat.multiplicity`, in particular to underline that it proves Legendre's theorem.
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *def* nat.clog
- \+ *lemma* nat.clog_eq_one
- \+ *lemma* nat.clog_le_clog_of_le
- \+ *lemma* nat.clog_mono
- \+ *lemma* nat.clog_of_left_le_one
- \+ *lemma* nat.clog_of_right_le_one
- \+ *lemma* nat.clog_of_two_le
- \+ *lemma* nat.clog_one_left
- \+ *lemma* nat.clog_one_right
- \+ *lemma* nat.clog_pos
- \+ *lemma* nat.clog_pow
- \+ *lemma* nat.clog_zero_left
- \+ *lemma* nat.clog_zero_right
- \+ *lemma* nat.le_pow_clog
- \+ *lemma* nat.le_pow_iff_clog_le
- \- *lemma* nat.log_b_one_eq_zero
- \- *lemma* nat.log_b_zero_eq_zero
- \- *lemma* nat.log_eq_zero_of_le
- \- *lemma* nat.log_eq_zero_of_lt
- \+ *lemma* nat.log_le_clog
- \- *lemma* nat.log_le_log_succ
- \+ *lemma* nat.log_of_left_le_one
- \+ *lemma* nat.log_of_lt
- \- *lemma* nat.log_one_eq_zero
- \+ *lemma* nat.log_one_left
- \+ *lemma* nat.log_one_right
- \+ *lemma* nat.log_pos
- \+/\- *lemma* nat.log_pow
- \- *lemma* nat.log_zero_eq_zero
- \+ *lemma* nat.log_zero_left
- \+ *lemma* nat.log_zero_right
- \+ *lemma* nat.lt_pow_succ_log_self
- \+/\- *lemma* nat.pow_le_iff_le_log
- \+/\- *lemma* nat.pow_log_le_self
- \+ *lemma* nat.pow_pred_clog_lt_self
- \- *lemma* nat.pow_succ_log_gt_self

Modified src/data/nat/multiplicity.lean
- \+/\- *lemma* nat.multiplicity_eq_card_pow_dvd



## [2021-08-28 02:16:20](https://github.com/leanprover-community/mathlib/commit/d3c592f)
chore(scripts): update nolints.txt ([#8899](https://github.com/leanprover-community/mathlib/pull/8899))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-08-28 01:06:00](https://github.com/leanprover-community/mathlib/commit/0fd51b1)
feat(data/real/irrational): exists irrational between any two distinct rationals and reals ([#8753](https://github.com/leanprover-community/mathlib/pull/8753))
Did not find these proofs in `data/real/irrational`, seemed like they belong here.  Just proving the standard facts about irrationals between rats and reals.  I am using these lemmas in a repo about the Thomae's function.
#### Estimated changes
Modified src/data/real/irrational.lean
- \+ *theorem* exists_irrational_btwn



## [2021-08-27 17:22:21](https://github.com/leanprover-community/mathlib/commit/2eaec05)
feat(ring_theory): define integrally closed domains ([#8893](https://github.com/leanprover-community/mathlib/pull/8893))
In this follow-up to [#8882](https://github.com/leanprover-community/mathlib/pull/8882), we define the notion of an integrally closed domain `R`, which contains all integral elements of `Frac(R)`.
We show the equivalence to `is_integral_closure R R K` for a field of fractions `K`.
We provide instances for `is_dedekind_domain`s, `unique_fractorization_monoid`s, and to the integers of a valuation. In particular, the rational root theorem provides a proof that `ℤ` is integrally closed.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.algebra_map_eq_apply
- \+ *lemma* alg_hom.algebra_map_eq_apply

Modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* is_dedekind_domain_inv.integrally_closed

Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_alg_equiv

Added src/ring_theory/integrally_closed.lean
- \+ *lemma* is_integrally_closed.integral_closure_eq_bot
- \+ *lemma* is_integrally_closed.integral_closure_eq_bot_iff
- \+ *lemma* is_integrally_closed.is_integral_iff
- \+ *theorem* is_integrally_closed_iff
- \+ *theorem* is_integrally_closed_iff_is_integral_closure

Modified src/ring_theory/polynomial/rational_root.lean
- \- *lemma* unique_factorization_monoid.integrally_closed

Modified src/ring_theory/valuation/integral.lean
- \+ *lemma* valuation.integers.integrally_closed



## [2021-08-27 15:28:35](https://github.com/leanprover-community/mathlib/commit/c4cf4c2)
feat(algebra/polynomial/big_operators): coeff of sums and prods of polynomials ([#8680](https://github.com/leanprover-community/mathlib/pull/8680))
Additionally, provide results for degree and nat_degree over lists,
which generalize away from requiring commutativity.
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.coeff_list_prod_of_nat_degree_le
- \+ *lemma* polynomial.coeff_multiset_prod_of_nat_degree_le
- \+ *lemma* polynomial.coeff_prod_of_nat_degree_le
- \+ *lemma* polynomial.degree_list_sum_le
- \+/\- *lemma* polynomial.leading_coeff_multiset_prod'
- \+ *lemma* polynomial.nat_degree_list_prod_le
- \+ *lemma* polynomial.nat_degree_list_sum_le
- \+ *lemma* polynomial.nat_degree_multiset_sum_le
- \+ *lemma* polynomial.nat_degree_sum_le

Modified src/data/list/basic.lean
- \+ *lemma* list.sum_le_foldr_max



## [2021-08-27 14:36:55](https://github.com/leanprover-community/mathlib/commit/dcd60e2)
feat(ring_theory/trace): the trace form is nondegenerate ([#8777](https://github.com/leanprover-community/mathlib/pull/8777))
This PR shows the determinant of the trace form is nonzero over a finite separable field extension. This is an important ingredient in showing the integral closure of a Dedekind domain in a finite separable extension is again a Dedekind domain, i.e. that rings of integers are Dedekind domains. We extend the results of [#8762](https://github.com/leanprover-community/mathlib/pull/8762) to write the trace form as a Vandermonde matrix to get a nice expression for the determinant, then use separability to show this value is nonzero.
#### Estimated changes
Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.to_matrix_mul_to_matrix_flip

Modified src/ring_theory/trace.lean
- \+ *lemma* det_trace_form_ne_zero'
- \+ *lemma* det_trace_form_ne_zero



## [2021-08-27 14:36:54](https://github.com/leanprover-community/mathlib/commit/7f25698)
feat(analysis/complex/isometry): Show that certain complex isometries are not equal ([#8646](https://github.com/leanprover-community/mathlib/pull/8646))
1. Lemma `reflection_rotation` proves that rotation by `(a : circle)` is not equal to reflection over the x-axis (i.e, `conj_lie`).  
2. Lemma `rotation_injective` proves that rotation by different `(a b: circle)` are not the same,(i.e, `rotation` is injective).
Co-authored by Kyle Miller
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* linear_isometry_equiv.congr_fun
- \+ *lemma* rotation_injective
- \+ *lemma* rotation_ne_conj_lie
- \+ *def* rotation_of
- \+ *lemma* rotation_of_rotation



## [2021-08-27 14:02:35](https://github.com/leanprover-community/mathlib/commit/7cfc987)
feat(measure_theory/decomposition/radon_nikodym): the Radon-Nikodym theorem ([#8763](https://github.com/leanprover-community/mathlib/pull/8763))
The Radon-Nikodym theorem 🎉
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean
- \- *def* measure_theory.measure.have_lebesgue_decomposition
- \+/\- *lemma* measure_theory.measure.have_lebesgue_decomposition_add
- \- *theorem* measure_theory.measure.have_lebesgue_decomposition_of_finite_measure
- \+/\- *lemma* measure_theory.measure.have_lebesgue_decomposition_spec

Added src/measure_theory/decomposition/radon_nikodym.lean
- \+ *theorem* measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_derive_eq
- \+ *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_eq



## [2021-08-27 12:25:45](https://github.com/leanprover-community/mathlib/commit/023a816)
feat(algebra): define a bundled type of absolute values ([#8881](https://github.com/leanprover-community/mathlib/pull/8881))
The type `absolute_value R S` is a bundled version of the typeclass `is_absolute_value R S` defined in `data/real/cau_seq.lean` (why was it defined there?), putting both in one file `algebra/absolute_value.lean`. The lemmas from `is_abs_val` have been copied mostly literally, with weakened assumptions when possible. Maps between the bundled and unbundled versions are also available.
We also define `absolute_value.abs` that represents the "standard" absolute value `abs`.
The point of this PR is both to modernize absolute values into bundled structures, and to make it easier to extend absolute values to represent "absolute values respecting the Euclidean domain structure", and from there "absolute values that show the class group is finite".
#### Estimated changes
Added src/algebra/absolute_value.lean
- \+ *lemma* absolute_value.abs_abv_sub_le_abv_sub
- \+ *lemma* absolute_value.coe_to_monoid_hom
- \+ *lemma* absolute_value.coe_to_monoid_with_zero_hom
- \+ *lemma* absolute_value.coe_to_mul_hom
- \+ *def* absolute_value.to_monoid_hom
- \+ *def* absolute_value.to_monoid_with_zero_hom
- \+ *lemma* is_absolute_value.abs_abv_sub_le_abv_sub
- \+ *theorem* is_absolute_value.abv_div
- \+ *def* is_absolute_value.abv_hom
- \+ *theorem* is_absolute_value.abv_inv
- \+ *theorem* is_absolute_value.abv_neg
- \+ *theorem* is_absolute_value.abv_one
- \+ *theorem* is_absolute_value.abv_pos
- \+ *lemma* is_absolute_value.abv_pow
- \+ *theorem* is_absolute_value.abv_sub
- \+ *lemma* is_absolute_value.abv_sub_le
- \+ *theorem* is_absolute_value.abv_zero
- \+ *lemma* is_absolute_value.sub_abv_le_abv_sub
- \+ *def* is_absolute_value.to_absolute_value

Modified src/data/real/cau_seq.lean
- \- *lemma* is_absolute_value.abs_abv_sub_le_abv_sub
- \- *theorem* is_absolute_value.abv_div
- \- *def* is_absolute_value.abv_hom
- \- *theorem* is_absolute_value.abv_inv
- \- *theorem* is_absolute_value.abv_neg
- \- *theorem* is_absolute_value.abv_one
- \- *theorem* is_absolute_value.abv_pos
- \- *lemma* is_absolute_value.abv_pow
- \- *theorem* is_absolute_value.abv_sub
- \- *lemma* is_absolute_value.abv_sub_le
- \- *theorem* is_absolute_value.abv_zero
- \- *lemma* is_absolute_value.sub_abv_le_abv_sub



## [2021-08-27 11:47:58](https://github.com/leanprover-community/mathlib/commit/a327851)
feat(ring_theory): a typeclass `is_integral_closure` ([#8882](https://github.com/leanprover-community/mathlib/pull/8882))
The typeclass `is_integral_closure A R B` states `A` is the integral closure of `R` in `B`, i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
We also show that any integral extension of `R` contained in `B` is contained in `A`, and the integral closure is unique up to isomorphism.
This was suggested in the review of [#8701](https://github.com/leanprover-community/mathlib/pull/8701), in order to define a characteristic predicate for rings of integers.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral.algebra_map
- \+ *lemma* is_integral_closure.algebra_map_equiv
- \+ *lemma* is_integral_closure.algebra_map_lift
- \+ *lemma* is_integral_closure.algebra_map_mk'
- \+ *theorem* is_integral_closure.is_integral_algebra
- \+ *lemma* is_integral_closure.mk'_add
- \+ *lemma* is_integral_closure.mk'_algebra_map
- \+ *lemma* is_integral_closure.mk'_mul
- \+ *lemma* is_integral_closure.mk'_one
- \+ *lemma* is_integral_closure.mk'_zero



## [2021-08-27 10:03:00](https://github.com/leanprover-community/mathlib/commit/88e47d7)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate_mul_distrib_aux ([#8681](https://github.com/leanprover-community/mathlib/pull/8681))
We prove towards the fact that the adjugate of a matrix distributes
over the product. The current proof assumes regularity of the matrices.
In the general case, this hypothesis is not required, but this lemma
will be crucial in a follow-up PR
which has to use polynomial matrices for the general case.
Additionally, we provide many API lemmas for det, cramer, 
nonsing_inv, and adjugate.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.one_eq_pi_single

Modified src/data/pi.lean
- \+ *lemma* pi.single_apply
- \+ *lemma* pi.single_comm
- \+ *lemma* pi.single_eq_of_ne'

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_eq_elem_of_subsingleton

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* is_unit.coe_inv_mul
- \+ *lemma* is_unit.inv_smul
- \+ *lemma* is_unit.mul_coe_inv
- \+ *lemma* matrix.adjugate_mul_distrib_aux
- \+ *lemma* matrix.adjugate_one
- \+ *lemma* matrix.adjugate_subsingleton
- \+ *lemma* matrix.cramer_one
- \+ *lemma* matrix.cramer_row_self
- \+ *lemma* matrix.cramer_subsingleton_apply
- \+ *lemma* matrix.cramer_zero
- \+ *lemma* matrix.inv_adjugate
- \+ *lemma* matrix.inv_def
- \+ *lemma* matrix.inv_inj
- \+ *lemma* matrix.inv_inv_inv
- \+ *lemma* matrix.inv_one
- \+ *lemma* matrix.inv_smul'
- \+ *lemma* matrix.inv_smul
- \+ *lemma* matrix.inv_zero
- \+ *lemma* matrix.is_regular_of_is_left_regular_det
- \+ *lemma* matrix.is_unit_nonsing_inv_det_iff
- \+ *lemma* matrix.mul_inv_rev
- \+ *lemma* matrix.nonsing_inv_apply_not_is_unit
- \+ *lemma* matrix.ring_hom.map_adjugate



## [2021-08-27 08:03:55](https://github.com/leanprover-community/mathlib/commit/0c50326)
refactor(*): use `is_empty` instead of `not (nonempty α)` ([#8858](https://github.com/leanprover-community/mathlib/pull/8858))
`eq_empty_of_not_nonempty` gets dropped in favour of `eq_empty_of_is_empty`.
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* eq.not_gt
- \+ *lemma* eq.not_lt

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/category_theory/preadditive/schur.lean


Modified src/data/finset/basic.lean
- \- *lemma* finset.eq_empty_of_not_nonempty

Modified src/data/fintype/basic.lean
- \- *lemma* finset.univ_eq_empty'
- \+/\- *lemma* finset.univ_eq_empty
- \+ *lemma* finset.univ_eq_empty_iff
- \+ *lemma* fintype.card_eq_zero
- \- *lemma* not_nonempty_fintype

Modified src/data/set/basic.lean
- \- *theorem* set.eq_empty_of_not_nonempty

Modified src/field_theory/primitive_element.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/logic/embedding.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/ae_measurable_sequence.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_const'
- \+ *lemma* measurable_of_empty
- \+ *lemma* measurable_of_empty_codomain
- \- *lemma* measurable_of_not_nonempty

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.eq_zero_of_is_empty
- \- *lemma* measure_theory.measure.eq_zero_of_not_nonempty
- \- *lemma* measure_theory.measure.sigma_finite_of_not_nonempty

Modified src/order/compactly_generated.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.filter_eq_bot_of_not_nonempty
- \+ *lemma* filter.tendsto_of_is_empty
- \- *lemma* filter.tendsto_of_not_nonempty

Modified src/order/order_iso_nat.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/category/Profinite/cofiltered_limit.lean




## [2021-08-27 07:04:59](https://github.com/leanprover-community/mathlib/commit/fe13f03)
feat(category_theory/structured_arrow): Duality between structured and costructured arrows ([#8807](https://github.com/leanprover-community/mathlib/pull/8807))
This PR formally sets up the duality of structured and costructured arrows as equivalences of categories. Unfortunately, the code is a bit repetitive, as the four functors introduced all follow a similar pattern, which I wasn't able to abstract out. Suggestions are welcome!
#### Estimated changes
Modified src/category_theory/structured_arrow.lean
- \+ *def* category_theory.costructured_arrow.to_structured_arrow'
- \+ *def* category_theory.costructured_arrow.to_structured_arrow
- \+ *def* category_theory.costructured_arrow_op_equivalence
- \+ *def* category_theory.structured_arrow.to_costructured_arrow'
- \+ *def* category_theory.structured_arrow.to_costructured_arrow
- \+ *def* category_theory.structured_arrow_op_equivalence



## [2021-08-27 06:31:17](https://github.com/leanprover-community/mathlib/commit/4705a6b)
doc(ring_theory/hahn_series): Update Hahn Series docstring ([#8883](https://github.com/leanprover-community/mathlib/pull/8883))
Updates `ring_theory/hahn_series` docstring to remove outdated TODOs
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/hahn_series.lean




## [2021-08-27 05:01:51](https://github.com/leanprover-community/mathlib/commit/a9de197)
feat(algebra/big_operators/basic): add `prod_dite_of_false`, `prod_dite_of_true` ([#8865](https://github.com/leanprover-community/mathlib/pull/8865))
The proofs are not mine cf [Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60prod_dite_of_true.60)
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_dite_of_false
- \+ *lemma* finset.prod_dite_of_true



## [2021-08-27 03:31:00](https://github.com/leanprover-community/mathlib/commit/bcd5cd3)
feat(algebra/pointwise): add to_additive attributes for pointwise smul ([#8878](https://github.com/leanprover-community/mathlib/pull/8878))
I wanted this to generalize some definitions in [#2819](https://github.com/leanprover-community/mathlib/pull/2819) but it should be independent.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* set.singleton_vadd

Modified src/algebra/pointwise.lean




## [2021-08-27 02:26:16](https://github.com/leanprover-community/mathlib/commit/bb4026f)
chore(scripts): update nolints.txt ([#8886](https://github.com/leanprover-community/mathlib/pull/8886))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-08-27 00:42:51](https://github.com/leanprover-community/mathlib/commit/11e3047)
feat(algebra/ordered_monoid): min_top_(left|right) ([#8880](https://github.com/leanprover-community/mathlib/pull/8880))
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+ *lemma* min_top_left
- \+ *lemma* min_top_right



## [2021-08-26 19:37:09](https://github.com/leanprover-community/mathlib/commit/e290569)
feat(data/nat/totient): add nat.totient_prime_iff ([#8833](https://github.com/leanprover-community/mathlib/pull/8833))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.filter_card_eq
- \+ *theorem* finset.not_subset

Modified src/data/nat/prime.lean
- \+ *theorem* nat.prime_of_coprime

Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_eq_iff_prime



## [2021-08-26 19:37:08](https://github.com/leanprover-community/mathlib/commit/080362d)
feat(data/finset/pi_induction): induction on `Π i, finset (α i)` ([#8794](https://github.com/leanprover-community/mathlib/pull/8794))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.not_ssubset_empty
- \+ *theorem* finset.sigma_eq_empty
- \+/\- *theorem* finset.sigma_mono
- \+ *theorem* finset.sigma_nonempty
- \+/\- *def* option.to_finset

Added src/data/finset/pi_induction.lean
- \+ *lemma* finset.induction_on_pi
- \+ *lemma* finset.induction_on_pi_max
- \+ *lemma* finset.induction_on_pi_min
- \+ *lemma* finset.induction_on_pi_of_choice



## [2021-08-26 19:37:07](https://github.com/leanprover-community/mathlib/commit/83490fc)
feat(data/multiset/basic): add some lemmas ([#8787](https://github.com/leanprover-community/mathlib/pull/8787))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.countp_cons
- \+ *theorem* multiset.countp_map
- \+ *theorem* multiset.filter_cons
- \+ *lemma* multiset.filter_nsmul
- \+/\- *lemma* multiset.mem_nsmul
- \+ *lemma* multiset.mem_of_mem_nsmul
- \+ *lemma* multiset.nsmul_cons
- \+ *lemma* multiset.nsmul_repeat
- \+ *theorem* multiset.nsmul_singleton
- \+ *lemma* multiset.prod_nonneg

Modified src/data/pnat/factors.lean




## [2021-08-26 18:49:05](https://github.com/leanprover-community/mathlib/commit/d9f4713)
feat(ring_theory/trace): Tr(x) is the sum of embeddings σ x into an algebraically closed field ([#8762](https://github.com/leanprover-community/mathlib/pull/8762))
The point of this PR is to provide the other formulation of "the trace of `x` is the sum of its conjugates", alongside `trace_eq_sum_roots`, namely `trace_eq_sum_embeddings`. We do so by exploiting the bijection between conjugate roots to `x : L` over `K` and embeddings of `K(x)`, then counting the number of embeddings of `x` to go to the whole of `L`.
#### Estimated changes
Modified src/field_theory/adjoin.lean


Modified src/field_theory/primitive_element.lean
- \+ *lemma* alg_hom.card

Modified src/field_theory/separable.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/ring_theory/power_basis.lean


Modified src/ring_theory/trace.lean
- \+ *lemma* sum_embeddings_eq_finrank_mul
- \+ *lemma* trace_eq_sum_embeddings
- \+ *lemma* trace_eq_sum_embeddings_gen
- \+ *lemma* trace_eq_trace_adjoin



## [2021-08-26 16:48:12](https://github.com/leanprover-community/mathlib/commit/5a2082d)
chore(category/grothendieck): split definition to avoid timeout ([#8871](https://github.com/leanprover-community/mathlib/pull/8871))
Helpful for [#8807](https://github.com/leanprover-community/mathlib/pull/8807).
#### Estimated changes
Modified src/category_theory/grothendieck.lean
- \+ *def* category_theory.grothendieck.grothendieck_Type_to_Cat_functor
- \+ *def* category_theory.grothendieck.grothendieck_Type_to_Cat_inverse



## [2021-08-26 16:48:10](https://github.com/leanprover-community/mathlib/commit/9038709)
feat(analysis/normed_space/inner_product): multiplication by I is real-orthogonal ([#8852](https://github.com/leanprover-community/mathlib/pull/8852))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* real_inner_I_smul_self



## [2021-08-26 16:48:09](https://github.com/leanprover-community/mathlib/commit/5bd69fd)
feat(ring_theory/ideal/local_ring): Isomorphisms are local ([#8850](https://github.com/leanprover-community/mathlib/pull/8850))
Adds the fact that isomorphisms (and ring equivs) are local ring homomorphisms.
#### Estimated changes
Modified src/ring_theory/ideal/local_ring.lean
- \+ *lemma* is_local_ring_hom_of_iso



## [2021-08-26 16:48:08](https://github.com/leanprover-community/mathlib/commit/5afdaea)
feat(data/fin): reverse_induction ([#8845](https://github.com/leanprover-community/mathlib/pull/8845))
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.last_cases
- \+ *lemma* fin.last_cases_cast_succ
- \+ *lemma* fin.last_cases_last
- \+ *def* fin.reverse_induction
- \+ *lemma* fin.reverse_induction_cast_succ
- \+ *lemma* fin.reverse_induction_last



## [2021-08-26 16:48:07](https://github.com/leanprover-community/mathlib/commit/678a2b5)
feat(data/list,multiset,finset): monotone_filter_(left|right) ([#8842](https://github.com/leanprover-community/mathlib/pull/8842))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.monotone_filter_left
- \+ *lemma* finset.monotone_filter_right

Modified src/data/list/basic.lean
- \- *theorem* list.filter_sublist_filter
- \+ *lemma* list.is_infix.filter
- \+ *lemma* list.is_prefix.filter
- \+ *lemma* list.is_suffix.filter
- \+ *lemma* list.monotone_filter_left
- \+ *lemma* list.monotone_filter_right
- \+ *theorem* list.sublist.filter

Modified src/data/list/perm.lean
- \+ *lemma* list.subperm.filter

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.monotone_filter_left
- \+ *lemma* multiset.monotone_filter_right



## [2021-08-26 16:48:06](https://github.com/leanprover-community/mathlib/commit/8e87f42)
feat(tactic/lint/misc): Add syntactic tautology linter ([#8821](https://github.com/leanprover-community/mathlib/pull/8821))
Add a linter that checks whether a lemma is a declaration that `∀ a b ... z,e₁ = e₂` where `e₁` and `e₂` are equal
exprs, we call declarations of this form syntactic tautologies.
Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving basic facts
with rfl when elaboration results in a different term than the user intended.
@PatrickMassot suggested this at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/syntactic.20tautology.20linter/near/250267477.
The found problems are fixed in [#8811](https://github.com/leanprover-community/mathlib/pull/8811).
#### Estimated changes
Modified src/tactic/lint/default.lean


Modified src/tactic/lint/misc.lean




## [2021-08-26 13:06:18](https://github.com/leanprover-community/mathlib/commit/70e1f9a)
feat(data/fin): add_cases ([#8876](https://github.com/leanprover-community/mathlib/pull/8876))
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.add_cases
- \+ *lemma* fin.add_cases_left
- \+ *lemma* fin.add_cases_right



## [2021-08-26 13:06:17](https://github.com/leanprover-community/mathlib/commit/976e930)
chore(archive/imo/README): whitespace breaks links ([#8874](https://github.com/leanprover-community/mathlib/pull/8874))
#### Estimated changes
Modified archive/imo/README.md




## [2021-08-26 13:06:15](https://github.com/leanprover-community/mathlib/commit/0d07d04)
chore(data/set): add a few lemmas and `@[simp]` attrs ([#8873](https://github.com/leanprover-community/mathlib/pull/8873))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.inter_eq_left_iff_subset
- \+/\- *theorem* set.inter_eq_right_iff_subset
- \+/\- *theorem* set.inter_univ
- \+ *theorem* set.union_eq_left_iff_subset
- \+ *theorem* set.union_eq_right_iff_subset
- \+/\- *theorem* set.univ_inter

Modified src/linear_algebra/multilinear.lean




## [2021-08-26 13:06:14](https://github.com/leanprover-community/mathlib/commit/1f13610)
feat(*): remove the `fintype` requirement from matrices. ([#8810](https://github.com/leanprover-community/mathlib/pull/8810))
For historical reasons, `matrix` has always had `fintype` attached to it. I remove this artificial limitation, but with a big caveat; multiplication is currently defined in terms of the dot product, which requires finiteness; therefore, any multiplicative structure on matrices currently requires fintypes. This can be removed in future contributions, however.
#### Estimated changes
Modified src/algebra/lie/classical.lean
- \+/\- *lemma* lie_algebra.matrix_trace_commutator_zero
- \+/\- *lemma* lie_algebra.orthogonal.JD_transform
- \+/\- *lemma* lie_algebra.orthogonal.PD_inv
- \+/\- *lemma* lie_algebra.orthogonal.is_unit_PD
- \+/\- *lemma* lie_algebra.orthogonal.mem_so
- \+/\- *def* lie_algebra.orthogonal.so'
- \+/\- *def* lie_algebra.orthogonal.so
- \+/\- *def* lie_algebra.orthogonal.type_B
- \+/\- *def* lie_algebra.orthogonal.type_D
- \+/\- *def* lie_algebra.special_linear.sl
- \+/\- *lemma* lie_algebra.special_linear.sl_bracket
- \+/\- *lemma* lie_algebra.special_linear.sl_non_abelian
- \+/\- *def* lie_algebra.symplectic.sp

Modified src/algebra/lie/matrix.lean
- \+/\- *def* matrix.reindex_lie_equiv
- \+/\- *lemma* matrix.reindex_lie_equiv_apply
- \+/\- *lemma* matrix.reindex_lie_equiv_symm

Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.add_monoid_hom_mul_left
- \+/\- *def* matrix.add_monoid_hom_mul_right
- \+/\- *lemma* matrix.add_mul_vec
- \+/\- *lemma* matrix.add_vec_mul
- \+/\- *lemma* matrix.col_mul_vec
- \+/\- *lemma* matrix.col_vec_mul
- \+/\- *lemma* matrix.conj_transpose_mul
- \+/\- *theorem* matrix.diagonal_mul
- \+/\- *theorem* matrix.diagonal_mul_diagonal'
- \+/\- *theorem* matrix.diagonal_mul_diagonal
- \+/\- *def* matrix.diagonal_ring_hom
- \+/\- *lemma* matrix.dot_product_assoc
- \+/\- *lemma* matrix.map_mul
- \+/\- *lemma* matrix.matrix_eq_sum_std_basis
- \+/\- *lemma* matrix.minor_minor
- \+/\- *lemma* matrix.minor_mul
- \+/\- *lemma* matrix.minor_mul_equiv
- \+/\- *theorem* matrix.mul_apply'
- \+/\- *theorem* matrix.mul_apply
- \+/\- *theorem* matrix.mul_diagonal
- \+/\- *theorem* matrix.mul_eq_mul
- \+/\- *lemma* matrix.mul_minor_one
- \+/\- *lemma* matrix.mul_mul_left
- \+/\- *lemma* matrix.mul_smul
- \+/\- *def* matrix.mul_vec.add_monoid_hom_left
- \+/\- *def* matrix.mul_vec
- \+/\- *lemma* matrix.mul_vec_add
- \+/\- *lemma* matrix.mul_vec_diagonal
- \+/\- *lemma* matrix.mul_vec_mul_vec
- \+/\- *lemma* matrix.mul_vec_neg
- \+/\- *lemma* matrix.mul_vec_smul_assoc
- \+/\- *lemma* matrix.mul_vec_transpose
- \+/\- *lemma* matrix.mul_vec_zero
- \+/\- *lemma* matrix.neg_mul_vec
- \+/\- *lemma* matrix.neg_vec_mul
- \+/\- *lemma* matrix.one_minor_mul
- \+/\- *lemma* matrix.one_mul_vec
- \+/\- *lemma* matrix.reindex_trans
- \+/\- *lemma* matrix.row_mul_col_apply
- \+/\- *lemma* matrix.row_mul_vec
- \+/\- *lemma* matrix.row_vec_mul
- \+/\- *lemma* matrix.smul_eq_diagonal_mul
- \+/\- *lemma* matrix.smul_mul
- \+/\- *lemma* matrix.smul_mul_vec_assoc
- \+/\- *lemma* matrix.star_mul
- \+/\- *lemma* matrix.transpose_mul
- \+/\- *def* matrix.vec_mul
- \+/\- *lemma* matrix.vec_mul_add
- \+/\- *lemma* matrix.vec_mul_diagonal
- \+/\- *lemma* matrix.vec_mul_neg
- \+/\- *lemma* matrix.vec_mul_one
- \+/\- *lemma* matrix.vec_mul_transpose
- \+/\- *lemma* matrix.vec_mul_vec_mul
- \+/\- *lemma* matrix.vec_mul_zero
- \+/\- *lemma* matrix.zero_mul_vec
- \+/\- *lemma* matrix.zero_vec_mul
- \+/\- *def* matrix

Modified src/data/matrix/block.lean
- \+/\- *lemma* matrix.block_diagonal'_mul
- \+/\- *lemma* matrix.block_diagonal_mul
- \+/\- *lemma* matrix.from_blocks_multiply
- \+/\- *def* matrix.to_block
- \+/\- *lemma* matrix.to_block_apply
- \+/\- *def* matrix.to_square_block_prop
- \+/\- *lemma* matrix.to_square_block_prop_def

Modified src/data/matrix/kronecker.lean
- \+/\- *lemma* matrix.mul_kronecker_mul
- \+/\- *lemma* matrix.mul_kronecker_tmul_mul

Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.cons_mul
- \+/\- *lemma* matrix.cons_mul_vec
- \+/\- *lemma* matrix.empty_mul
- \+/\- *lemma* matrix.empty_mul_vec
- \+/\- *lemma* matrix.mul_empty
- \+/\- *lemma* matrix.mul_val_succ
- \+/\- *lemma* matrix.vec_mul_empty

Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* pequiv.matrix_mul_apply
- \+/\- *lemma* pequiv.mul_matrix_apply
- \+/\- *lemma* pequiv.single_mul_single
- \+/\- *lemma* pequiv.single_mul_single_of_ne
- \+/\- *lemma* pequiv.single_mul_single_right
- \+/\- *lemma* pequiv.to_matrix_trans
- \+/\- *lemma* pequiv.to_pequiv_mul_matrix

Modified src/linear_algebra/bilinear_form.lean
- \+/\- *def* matrix.to_bilin'_aux
- \+/\- *lemma* matrix.to_bilin'_aux_std_basis

Modified src/linear_algebra/matrix/basis.lean
- \+/\- *lemma* basis.sum_to_matrix_smul_self
- \+/\- *lemma* basis.to_lin_to_matrix
- \+/\- *lemma* basis.to_matrix_eq_to_matrix_constr
- \+/\- *def* basis.to_matrix_equiv
- \+/\- *lemma* basis.to_matrix_mul_to_matrix

Modified src/linear_algebra/matrix/block.lean
- \+/\- *def* matrix.block_triangular_matrix'
- \+/\- *def* matrix.block_triangular_matrix
- \+/\- *lemma* matrix.upper_two_block_triangular'
- \+/\- *lemma* matrix.upper_two_block_triangular

Modified src/linear_algebra/matrix/reindex.lean
- \+/\- *lemma* matrix.det_reindex_alg_equiv
- \+/\- *lemma* matrix.det_reindex_linear_equiv_self
- \+/\- *lemma* matrix.mul_reindex_linear_equiv_one
- \+/\- *lemma* matrix.reindex_linear_equiv_mul

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *def* alg_equiv_matrix'
- \+/\- *def* alg_equiv_matrix
- \+/\- *lemma* linear_map.to_matrix'_comp
- \+/\- *lemma* linear_map.to_matrix'_mul
- \+/\- *lemma* linear_map.to_matrix_comp
- \+/\- *def* matrix.mul_vec_lin
- \+/\- *lemma* matrix.mul_vec_lin_apply
- \+/\- *lemma* matrix.rank_vec_mul_vec
- \+/\- *lemma* matrix.to_lin'_mul
- \+/\- *lemma* matrix.to_lin'_mul_apply
- \+/\- *def* matrix.to_lin'_of_inv
- \+/\- *lemma* matrix.to_lin_mul
- \+/\- *lemma* matrix.to_lin_mul_apply

Modified src/linear_algebra/matrix/trace.lean
- \+/\- *def* matrix.trace

Modified src/ring_theory/matrix_algebra.lean




## [2021-08-26 11:17:26](https://github.com/leanprover-community/mathlib/commit/0861cc7)
refactor(*): move code about `ulift`/`plift` ([#8863](https://github.com/leanprover-community/mathlib/pull/8863))
* move old file about `ulift`/`plift` from `data.ulift` to `control.ulift`;
* redefine `ulift.map` etc without pattern matching;
* create new `data.ulift`, move `ulift.subsingleton` etc from `data.equiv.basic` to this file;
* add `ulift.is_empty` and `plift.is_empty`;
* add `ulift.exists`, `plift.exists`, `ulift.forall`, and `plift.forall`;
* rename `equiv.nonempty_iff_nonempty` to `equiv.nonempty_congr` to match `equiv.subsingleton_congr` etc;
* rename `plift.fintype` to `plift.fintype_Prop`, add a new `plift.fintype`.
#### Estimated changes
Modified src/category_theory/discrete_category.lean


Modified src/category_theory/isomorphism_classes.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/control/functor.lean


Added src/control/ulift.lean
- \+ *lemma* plift.bind_up
- \+ *lemma* plift.map_up
- \+ *lemma* plift.rec.constant
- \+ *lemma* plift.seq_up
- \+ *lemma* ulift.bind_up
- \+ *lemma* ulift.map_up
- \+ *lemma* ulift.rec.constant
- \+ *lemma* ulift.seq_up

Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.nonempty_congr
- \- *lemma* equiv.nonempty_iff_nonempty

Modified src/data/fintype/basic.lean
- \+ *theorem* fintype.card_plift

Modified src/data/ulift.lean
- \- *lemma* plift.rec.constant
- \+ *lemma* plift.«exists»
- \+ *lemma* plift.«forall»
- \- *lemma* ulift.rec.constant
- \+ *lemma* ulift.«exists»
- \+ *lemma* ulift.«forall»

Modified src/testing/slim_check/sampleable.lean




## [2021-08-26 11:17:25](https://github.com/leanprover-community/mathlib/commit/2a6fef3)
refactor(order/filter/bases): allow `ι : Sort*` ([#8856](https://github.com/leanprover-community/mathlib/pull/8856))
* `ι` in `filter.has_basis (l : filter α) (p : ι → Prop) (s : ι → set )` now can be a `Sort *`;
* some lemmas now have "primed" versions that use `pprod` instead of `prod`;
* new lemma: `filter.has_basis_supr`.
I also added a few missing lemmas to `data.pprod` and golfed a couple of proofs.
#### Estimated changes
Modified src/data/pprod.lean
- \+ *theorem* pprod.exists'
- \+ *theorem* pprod.forall'
- \+/\- *lemma* pprod.mk.eta
- \+ *theorem* pprod.«exists»
- \+ *theorem* pprod.«forall»

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.inf'
- \+/\- *lemma* filter.has_basis.inf
- \+ *lemma* filter.has_basis.prod''
- \+/\- *lemma* filter.has_basis.prod
- \+ *lemma* filter.has_basis.sup'
- \+/\- *lemma* filter.has_basis.sup
- \+/\- *lemma* filter.has_basis_binfi_principal'
- \+/\- *lemma* filter.has_basis_infi_principal_finite
- \+ *lemma* filter.has_basis_supr

Modified src/topology/uniform_space/separation.lean




## [2021-08-26 11:17:24](https://github.com/leanprover-community/mathlib/commit/3287c94)
refactor(tactic/ext): simplify ext attribute ([#8785](https://github.com/leanprover-community/mathlib/pull/8785))
This simplifies the `ext` attribute from taking a list with `*`, `(->)` and names to just `@[ext]` or `@[ext ident]`. The `(->)` option is only used once, in the file that declares the `ext` attribute itself, so it's not worth the parser complexity. The ability to remove attributes with `@[ext -foo]` is removed, but I don't think it was tested because it was never used and doesn't work anyway.
Also fixes an issue with ext attributes being quadratic (in the number of ext attributes applied), and also makes `ext` attributes remove themselves (the real work of ext attributes is done by two internal attributes `_ext_core` and `_ext_lemma_core`), so that they don't pollute `#print` output. Before:
```lean
#print funext
@[_ext_lemma_core, ext list.cons.{0} ext_param_type (sum.inr.{0 0} (option.{0} name) (option.{0} name) (option.some.{0} name (name.mk_numeral (unsigned.of_nat' (has_zero.zero.{0} nat nat.has_zero)) name.anonymous))) (list.cons.{0} ext_param_type (sum.inr.{0 0} (option.{0} name) (option.{0} name) (option.some.{0} name (name.mk_string "thunk" name.anonymous))) (list.nil.{0} ext_param_type)), intro!]
theorem funext : ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂ :=
```
After:
```lean
#print funext
@[_ext_lemma_core, intro!]
theorem funext : ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂ :=
```
#### Estimated changes
Modified src/tactic/ext.lean
- \- *def* ext_param_type



## [2021-08-26 11:17:23](https://github.com/leanprover-community/mathlib/commit/a4b33d3)
feat(data/matrix/kronecker): add two reindex lemmas ([#8774](https://github.com/leanprover-community/mathlib/pull/8774))
Added two lemmas `kronecker_map_reindex_right` and `kronecker_map_reindex_left` (used in LTE) and moved the two `assoc` lemmas some lines up, before the `linear` section, because they are unrelated to any linearity business.
#### Estimated changes
Modified src/data/matrix/kronecker.lean
- \+ *lemma* matrix.kronecker_map_reindex
- \+ *lemma* matrix.kronecker_map_reindex_left
- \+ *lemma* matrix.kronecker_map_reindex_right



## [2021-08-26 11:17:22](https://github.com/leanprover-community/mathlib/commit/3e5bbca)
feat(field_theory/intermediate_field): generalize `algebra` instances ([#8761](https://github.com/leanprover-community/mathlib/pull/8761))
The `algebra` and `is_scalar_tower` instances for `intermediate_field` are (again) as general as those for `subalgebra`.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/polynomial_galois_group.lean




## [2021-08-26 11:17:21](https://github.com/leanprover-community/mathlib/commit/2c698bd)
docs(set_theory/zfc): add module docstring and missing def docstrings ([#8744](https://github.com/leanprover-community/mathlib/pull/8744))
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+/\- *def* Class.fval
- \+/\- *def* Class.iota
- \+/\- *theorem* Class.iota_val
- \+/\- *def* Class.to_Set
- \+/\- *theorem* Set.Union_lem
- \+/\- *theorem* Set.choice_mem_aux
- \+/\- *theorem* Set.eq_empty
- \+/\- *theorem* Set.ext
- \+/\- *theorem* Set.ext_iff
- \+/\- *theorem* Set.induction_on
- \+/\- *theorem* Set.mem_empty
- \+/\- *theorem* Set.mem_image
- \+/\- *theorem* Set.mem_prod
- \+/\- *def* Set.prod
- \+/\- *def* arity
- \+/\- *def* pSet.embed
- \+ *theorem* pSet.equiv.rfl
- \+/\- *theorem* pSet.equiv_iff_mem
- \+/\- *theorem* pSet.mem.congr_left
- \+/\- *theorem* pSet.mem.congr_right
- \+/\- *theorem* pSet.mem.ext
- \+/\- *theorem* pSet.mem_Union
- \+/\- *theorem* pSet.mem_empty
- \+/\- *theorem* pSet.mem_image
- \+/\- *def* pSet.omega
- \+/\- *def* pSet.resp



## [2021-08-26 10:02:38](https://github.com/leanprover-community/mathlib/commit/2e1e98f)
feat(linear_algebra/bilinear_form): bilinear forms with `det ≠ 0` are nonsingular ([#8824](https://github.com/leanprover-community/mathlib/pull/8824))
In particular, the trace form is such a bilinear form (see [#8777](https://github.com/leanprover-community/mathlib/pull/8777)).
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *theorem* bilin_form.nondegenerate_of_det_ne_zero'
- \+ *theorem* bilin_form.nondegenerate_of_det_ne_zero

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *theorem* matrix.nondegenerate_of_det_ne_zero



## [2021-08-26 10:02:37](https://github.com/leanprover-community/mathlib/commit/147af57)
feat(category_theory/is_connected): The opposite of a connected category is connected ([#8806](https://github.com/leanprover-community/mathlib/pull/8806))
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+ *lemma* category_theory.is_connected_of_is_connected_op
- \+ *lemma* category_theory.is_preconnected_of_is_preconnected_op



## [2021-08-26 10:02:36](https://github.com/leanprover-community/mathlib/commit/058f639)
feat(data/equiv/fin): fin_succ_equiv_last ([#8805](https://github.com/leanprover-community/mathlib/pull/8805))
This commit changes the type of `fin_succ_equiv'`. `fin_succ_equiv' i` used to take an argument of type `fin n` which was 
strange and it now takes an argument of type `fin (n + 1)` meaning it is now possible to send `fin.last n` to `none` if desired. I also defined `fin.succ_equiv_last`, the canonical equiv `fin (n + 1)` to `option (fin n)` sending `fin.last` to `none`.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+/\- *def* fin_succ_equiv'
- \+/\- *lemma* fin_succ_equiv'_above
- \+/\- *lemma* fin_succ_equiv'_below
- \+ *lemma* fin_succ_equiv'_symm_coe_above
- \+ *lemma* fin_succ_equiv'_symm_coe_below
- \+ *lemma* fin_succ_equiv'_symm_some_above
- \+ *lemma* fin_succ_equiv'_symm_some_below
- \+ *def* fin_succ_equiv_last
- \+ *lemma* fin_succ_equiv_last_cast_succ
- \+ *lemma* fin_succ_equiv_last_last
- \+ *lemma* fin_succ_equiv_last_symm_coe
- \+ *lemma* fin_succ_equiv_last_symm_none
- \+ *lemma* fin_succ_equiv_last_symm_some
- \- *lemma* fin_succ_equiv_symm'_coe_above
- \- *lemma* fin_succ_equiv_symm'_coe_below
- \- *lemma* fin_succ_equiv_symm'_some_above
- \- *lemma* fin_succ_equiv_symm'_some_below

Modified src/linear_algebra/linear_independent.lean




## [2021-08-26 09:18:22](https://github.com/leanprover-community/mathlib/commit/94d4a32)
feat(linear_algebra/bilinear_form): the dual basis for a nondegenerate bilin form ([#8823](https://github.com/leanprover-community/mathlib/pull/8823))
Let `B` be a nondegenerate (symmetric) bilinear form on a finite-dimensional vector space `V` and `b` a basis on `V`. Then there is a "dual basis" `d` such that `d.repr x i = B x (b i)` and `B (d i) (b j) = B (b i) (d j) = if i = j then 1 else 0`.
In a follow-up PR, we'll show that the trace form for `L / K` produces a dual basis consisting only of elements integral over the ring of integers of `K`.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.apply_dual_basis_left
- \+ *lemma* bilin_form.apply_dual_basis_right
- \+ *lemma* bilin_form.dual_basis_repr_apply



## [2021-08-26 07:01:23](https://github.com/leanprover-community/mathlib/commit/acbe935)
chore(topology/metric_space): add 2 lemmas, golf ([#8861](https://github.com/leanprover-community/mathlib/pull/8861))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* comap_dist_left_at_top_eq_cocompact
- \+ *lemma* comap_dist_left_at_top_le_cocompact
- \+ *lemma* comap_dist_right_at_top_eq_cocompact
- \+ *lemma* comap_dist_right_at_top_le_cocompact
- \+ *lemma* metric.bounded.subset_ball
- \+ *lemma* tendsto_cocompact_of_tendsto_dist_comp_at_top



## [2021-08-26 07:01:22](https://github.com/leanprover-community/mathlib/commit/9438552)
feat(data/fin): cast_add_lt ([#8830](https://github.com/leanprover-community/mathlib/pull/8830))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_add_lt



## [2021-08-26 07:01:21](https://github.com/leanprover-community/mathlib/commit/6c6fc02)
feat(data/fin): cast_add_right ([#8829](https://github.com/leanprover-community/mathlib/pull/8829))
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.cast_add_right
- \+ *lemma* fin.coe_cast_add_right
- \+ *lemma* fin.le_cast_add_right



## [2021-08-26 07:01:20](https://github.com/leanprover-community/mathlib/commit/bafeccf)
feat(data/fin): fin.succ_cast_succ ([#8828](https://github.com/leanprover-community/mathlib/pull/8828))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.succ_cast_succ



## [2021-08-26 07:01:19](https://github.com/leanprover-community/mathlib/commit/cb1932d)
feat(data/complex/exponential): bound on exp for arbitrary arguments ([#8667](https://github.com/leanprover-community/mathlib/pull/8667))
This PR is for a new lemma (currently called `exp_bound'`) which proves `exp x` is close to its `n`th degree taylor expansion for sufficiently large `n`. Unlike the previous bound, this lemma can be instantiated on any real `x` rather than just `x` with absolute value less than or equal to 1. I am separating this lemma out from [#8002](https://github.com/leanprover-community/mathlib/pull/8002) because I think it stands on its own.
The last time I checked it was sorry free - but that was before I merged with master and moved it to a different branch. It may also benefit from a little golfing.
There are a few lemmas I proved as well to support this - one about the relative size of factorials and a few about sums of geometric sequences. The ~~geometric series ones should probably be generalized and moved to another file~~ this generalization sort of exists and is in the algebra.geom_sum file. I didn't find it initially since I was searching for "geometric" not "geom".
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_range_add_div_prod_range

Modified src/algebra/group/basic.lean
- \+ *lemma* div_eq_of_eq_mul'
- \- *lemma* sub_eq_of_eq_add'

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.exp_bound'

Modified src/data/nat/factorial.lean
- \+ *lemma* nat.factorial_mul_pow_sub_le_factorial



## [2021-08-26 05:17:35](https://github.com/leanprover-community/mathlib/commit/fe47777)
feat(analysis/complex/upper_half_plane): new file ([#8377](https://github.com/leanprover-community/mathlib/pull/8377))
This file defines `upper_half_plane` to be the upper half plane in `ℂ`.
We furthermore equip it with the structure of an `SL(2,ℝ)` action by
fractional linear transformations.
Co-authored by Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
Co-authored by Marc Masdeu <marc.masdeu@gmail.com>
#### Estimated changes
Added src/analysis/complex/upper_half_plane.lean
- \+ *lemma* upper_half_plane.coe_im
- \+ *lemma* upper_half_plane.coe_re
- \+ *lemma* upper_half_plane.coe_smul
- \+ *def* upper_half_plane.denom
- \+ *lemma* upper_half_plane.denom_cocycle
- \+ *lemma* upper_half_plane.denom_ne_zero
- \+ *def* upper_half_plane.im
- \+ *lemma* upper_half_plane.im_ne_zero
- \+ *lemma* upper_half_plane.im_pos
- \+ *lemma* upper_half_plane.im_smul
- \+ *lemma* upper_half_plane.im_smul_eq_div_norm_sq
- \+ *lemma* upper_half_plane.linear_ne_zero
- \+ *lemma* upper_half_plane.mul_smul'
- \+ *lemma* upper_half_plane.ne_zero
- \+ *lemma* upper_half_plane.neg_smul
- \+ *lemma* upper_half_plane.norm_sq_denom_ne_zero
- \+ *lemma* upper_half_plane.norm_sq_denom_pos
- \+ *lemma* upper_half_plane.norm_sq_ne_zero
- \+ *lemma* upper_half_plane.norm_sq_pos
- \+ *def* upper_half_plane.num
- \+ *def* upper_half_plane.re
- \+ *lemma* upper_half_plane.re_smul
- \+ *def* upper_half_plane.smul_aux'
- \+ *lemma* upper_half_plane.smul_aux'_im
- \+ *def* upper_half_plane.smul_aux

Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_fin_even

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_fin_one
- \+ *lemma* matrix.det_fin_three
- \+ *lemma* matrix.det_fin_two
- \+ *lemma* matrix.det_fin_zero
- \+/\- *lemma* matrix.det_smul

Modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* matrix.special_linear_group.coe_neg
- \+ *lemma* matrix.special_linear_group.det_ne_zero
- \+ *lemma* matrix.special_linear_group.row_ne_zero



## [2021-08-26 03:51:48](https://github.com/leanprover-community/mathlib/commit/7e781a8)
chore(*): Fix syntactic tautologies ([#8811](https://github.com/leanprover-community/mathlib/pull/8811))
Fix a few lemmas that were accidentally tautological in the sense that they were equations with syntactically equal LHS and RHS.
A linter will be added in a second PR, for now we just fix the found issues.
It would be great if a category expert like @semorrison would check the category ones, as its unclear to me which direction they are meant to go.
As pointed out by @PatrickMassot on Zulip https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/syntactic.20tautology.20linter/near/250267477.
Thanks to @eric-wieser for helping figure out the corrected versions.
#### Estimated changes
Modified src/analysis/normed_space/affine_isometry.lean
- \+/\- *lemma* affine_isometry.coe_id

Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry.coe_id

Modified src/category_theory/sums/basic.lean
- \+/\- *lemma* category_theory.sum_comp_inl
- \+/\- *lemma* category_theory.sum_comp_inr

Modified src/linear_algebra/basic.lean
- \+/\- *theorem* submodule.quotient.mk_eq_mk



## [2021-08-26 02:42:53](https://github.com/leanprover-community/mathlib/commit/daf0d02)
feat(archive/imo): README.md ([#8799](https://github.com/leanprover-community/mathlib/pull/8799))
Proposed text for a README file in the IMO directory. I don't think we have a particular problem with IMO submissions, but thought it could be useful to set the parameters around IMO problems, as it's never been completely clear they belong in mathlib.
If we merge this, or something like it, I'll link #imo on Zulip to it.
#### Estimated changes
Added archive/imo/README.md




## [2021-08-25 21:27:03](https://github.com/leanprover-community/mathlib/commit/8befa82)
feat(group_theory/perm/list): lemmas on form_perm ([#8848](https://github.com/leanprover-community/mathlib/pull/8848))
#### Estimated changes
Modified src/group_theory/perm/list.lean
- \+ *lemma* list.form_perm_apply_mem_eq_self_iff
- \+ *lemma* list.form_perm_apply_mem_ne_self_iff
- \+ *lemma* list.form_perm_apply_not_mem
- \+ *lemma* list.form_perm_eq_form_perm_iff
- \+ *lemma* list.form_perm_eq_one_iff
- \+ *lemma* list.form_perm_gpow_apply_mem_imp_mem
- \+ *lemma* list.form_perm_ne_self_imp_mem
- \+ *lemma* list.form_perm_pow_apply_head
- \+ *lemma* list.form_perm_pow_length_eq_one_of_nodup

Modified src/group_theory/perm/support.lean
- \+ *lemma* equiv.perm.coe_support_eq_set_support
- \+ *lemma* equiv.perm.set_support_apply_mem
- \+ *lemma* equiv.perm.set_support_gpow_subset
- \+ *lemma* equiv.perm.set_support_inv_eq
- \+ *lemma* equiv.perm.set_support_mul_subset



## [2021-08-25 21:27:01](https://github.com/leanprover-community/mathlib/commit/49af34d)
feat(group_theory/perm/cycles): same_cycle and cycle_of lemmas ([#8835](https://github.com/leanprover-community/mathlib/pull/8835))
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.card_support_cycle_of_pos_iff
- \+ *lemma* equiv.perm.cycle_of_self_apply
- \+ *lemma* equiv.perm.cycle_of_self_apply_gpow
- \+ *lemma* equiv.perm.cycle_of_self_apply_pow
- \+ *lemma* equiv.perm.pow_mod_card_support_cycle_of_self_apply
- \+ *lemma* equiv.perm.same_cycle.cycle_of_eq
- \+ *lemma* equiv.perm.same_cycle.mem_support_iff
- \+/\- *lemma* equiv.perm.same_cycle.symm
- \+/\- *lemma* equiv.perm.same_cycle.trans
- \+ *lemma* equiv.perm.same_cycle_gpow_left_iff
- \+ *lemma* equiv.perm.support_cycle_of_le
- \+ *lemma* equiv.perm.two_le_card_support_cycle_of_iff



## [2021-08-25 18:32:55](https://github.com/leanprover-community/mathlib/commit/40bd7c6)
feat(data/nat/modeq): Rotating list.repeat ([#8817](https://github.com/leanprover-community/mathlib/pull/8817))
Some consequences of `list.rotate_eq_self_iff_eq_repeat`.
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* list.rotate_one_eq_self_iff_eq_repeat
- \+ *lemma* list.rotate_repeat



## [2021-08-25 18:32:54](https://github.com/leanprover-community/mathlib/commit/c544742)
feat(linear_algebra/finite_dimensional): add finrank_map_le ([#8815](https://github.com/leanprover-community/mathlib/pull/8815))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* linear_equiv.dim_map_eq

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.finrank_map_le
- \+ *lemma* linear_equiv.finrank_map_eq



## [2021-08-25 18:32:53](https://github.com/leanprover-community/mathlib/commit/6a41805)
chore(group_theory/group_action/basic): `to_additive` attributes throughout ([#8814](https://github.com/leanprover-community/mathlib/pull/8814))
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* add_action.exists_vadd_eq
- \- *lemma* exists_smul_eq
- \+ *lemma* mul_action.exists_smul_eq
- \+/\- *theorem* mul_action.fixed_eq_Inter_fixed_by
- \+/\- *theorem* mul_action.injective_of_quotient_stabilizer
- \+/\- *lemma* mul_action.mem_fixed_by
- \+/\- *lemma* mul_action.mem_fixed_points'
- \+/\- *lemma* mul_action.mem_fixed_points
- \+/\- *lemma* mul_action.mem_fixed_points_iff_card_orbit_eq_one
- \+/\- *lemma* mul_action.mem_orbit
- \+/\- *lemma* mul_action.mem_orbit_iff
- \+/\- *lemma* mul_action.mem_orbit_self
- \+/\- *lemma* mul_action.mem_orbit_smul
- \+/\- *lemma* mul_action.mem_stabilizer_iff
- \+/\- *lemma* mul_action.mem_stabilizer_submonoid_iff
- \+/\- *theorem* mul_action.of_quotient_stabilizer_mem_orbit
- \+/\- *theorem* mul_action.of_quotient_stabilizer_mk
- \+/\- *theorem* mul_action.of_quotient_stabilizer_smul
- \+/\- *lemma* mul_action.orbit_eq_iff
- \+/\- *theorem* mul_action.orbit_equiv_quotient_stabilizer_symm_apply
- \+/\- *lemma* mul_action.quotient.smul_coe
- \+/\- *lemma* mul_action.quotient.smul_mk
- \+/\- *lemma* mul_action.smul_mem_orbit_smul
- \+/\- *lemma* mul_action.stabilizer_quotient



## [2021-08-25 18:32:52](https://github.com/leanprover-community/mathlib/commit/b6e6c84)
feat(data/finset/basic): to_list ([#8797](https://github.com/leanprover-community/mathlib/pull/8797))
Produce a list of the elements of a finite set using choice.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.coe_to_list
- \+ *lemma* finset.length_to_list
- \+ *lemma* finset.mem_to_list
- \+ *lemma* finset.nodup_to_list
- \+ *lemma* finset.to_list_empty
- \+ *lemma* finset.to_list_to_finset

Modified src/data/finset/sort.lean
- \+ *lemma* finset.sort_perm_to_list



## [2021-08-25 18:32:50](https://github.com/leanprover-community/mathlib/commit/aca0874)
chore(algebra/direct_sum): Move all the algebraic structure on `direct_sum` into a single directory ([#8771](https://github.com/leanprover-community/mathlib/pull/8771))
This ends up splitting one file in two, but all the contents are just moved.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Renamed src/algebra/direct_sum.lean to src/algebra/direct_sum/basic.lean


Added src/algebra/direct_sum/finsupp.lean
- \+ *def* finsupp_lequiv_direct_sum
- \+ *theorem* finsupp_lequiv_direct_sum_single
- \+ *theorem* finsupp_lequiv_direct_sum_symm_lof

Renamed src/linear_algebra/direct_sum_module.lean to src/algebra/direct_sum/module.lean


Renamed src/algebra/direct_sum_graded.lean to src/algebra/direct_sum/ring.lean


Modified src/algebra/monoid_algebra_to_direct_sum.lean


Modified src/linear_algebra/direct_sum/finsupp.lean
- \- *def* finsupp_lequiv_direct_sum
- \- *theorem* finsupp_lequiv_direct_sum_single
- \- *theorem* finsupp_lequiv_direct_sum_symm_lof

Modified src/linear_algebra/direct_sum/tensor_product.lean


Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-08-25 18:32:49](https://github.com/leanprover-community/mathlib/commit/df8818c)
feat(data/nat/multiplicity): bound on the factorial multiplicity ([#8767](https://github.com/leanprover-community/mathlib/pull/8767))
This proves `multiplicity p n! ≤ n/(p - 1)`, for `p` prime and `n` natural.
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *lemma* nat.geom_sum_Ico_le
- \+ *lemma* nat.geom_sum_le
- \+ *lemma* nat.pred_mul_geom_sum_le

Modified src/data/nat/multiplicity.lean
- \+ *lemma* nat.prime.multiplicity_factorial_le_div_pred



## [2021-08-25 18:32:48](https://github.com/leanprover-community/mathlib/commit/301eb10)
feat(data/polynomial/monic): monic.is_regular ([#8679](https://github.com/leanprover-community/mathlib/pull/8679))
This golfs/generalizes some proofs.
Additionally, provide some helper API for `is_regular`,
for non-zeros in domains,
and for smul of units.
#### Estimated changes
Modified src/algebra/regular/smul.lean
- \+ *lemma* is_smul_regular_of_group
- \+/\- *lemma* units.is_smul_regular

Modified src/algebra/ring/basic.lean


Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.degree_smul_of_non_zero_divisor
- \+ *lemma* polynomial.degree_smul_of_smul_regular
- \- *lemma* polynomial.leading_coeff_smul_of_non_zero_divisor
- \+ *lemma* polynomial.leading_coeff_smul_of_smul_regular
- \+ *lemma* polynomial.monic.is_regular
- \- *lemma* polynomial.nat_degree_smul_of_non_zero_divisor
- \+ *lemma* polynomial.nat_degree_smul_of_smul_regular



## [2021-08-25 17:03:35](https://github.com/leanprover-community/mathlib/commit/b364cfc)
feat(linear_algebra/basis): if `R ≃ R'`, map a basis for `R`-module `M` to `R'`-module `M` ([#8699](https://github.com/leanprover-community/mathlib/pull/8699))
If `R` and `R'` are isomorphic rings that act identically on a module `M`, then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_of_bijective
- \+ *lemma* ring_equiv.of_bijective_apply

Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.coe_map_coeffs
- \+ *def* basis.map_coeffs
- \+ *lemma* basis.map_coeffs_apply

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* basis.algebra_map_coeffs_apply
- \+ *lemma* basis.coe_algebra_map_coeffs



## [2021-08-25 15:26:51](https://github.com/leanprover-community/mathlib/commit/0ad5abc)
chore(data/set/finite): golf 2 proofs ([#8862](https://github.com/leanprover-community/mathlib/pull/8862))
Also add `finset.coe_emb`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.coe_coe_emb
- \+ *def* finset.coe_emb

Modified src/data/set/finite.lean
- \+ *lemma* set.subset_to_finset_iff



## [2021-08-25 12:58:19](https://github.com/leanprover-community/mathlib/commit/97c327c)
feat(tactic/suggest): suggest using X, to filter results ([#8819](https://github.com/leanprover-community/mathlib/pull/8819))
You can now write `suggest using X`, to only give suggestions which make use of the local hypothesis `X`.
Similarly `suggest using X Y Z` for multiple hypotheses. `library_search using X` is also enabled.
This makes `suggest` much more useful. Previously
```
example (P Q : list ℕ) : list ℕ := by suggest
```
would have just said `exact P`.
Now you can write
```
example (P Q : list ℕ) : list ℕ := by suggest using P Q
```
and get:
```
Try this: exact list.diff P Q
Try this: exact list.union P Q
Try this: exact list.inter P Q
Try this: exact list.append P Q
Try this: exact list.bag_inter P Q
Try this: exact list.remove_all P Q
Try this: exact list.reverse_core P Q
```
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean




## [2021-08-25 06:39:27](https://github.com/leanprover-community/mathlib/commit/26a3286)
fix(data/set/lattice): lemmas about `Union`/`Inter` over `p : Prop` ([#8860](https://github.com/leanprover-community/mathlib/pull/8860))
With recently added `@[congr]` lemmas, it suffices to deal with unions/inters over `true` and `false`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Infi_eq_dif
- \+ *lemma* set.Inter_eq_if
- \+ *lemma* set.Union_eq_dif
- \+ *lemma* set.Union_eq_if
- \- *lemma* set.Union_prop
- \- *lemma* set.Union_prop_neg
- \- *lemma* set.Union_prop_pos



## [2021-08-25 06:39:26](https://github.com/leanprover-community/mathlib/commit/4a0c3d7)
feat(linear_algebra/finite_dimension): nontriviality lemmas ([#8851](https://github.com/leanprover-community/mathlib/pull/8851))
A vector space of `finrank` greater than zero is `nontrivial`, likewise a vector space whose `finrank` is equal to the successor of a natural number.
Also write the non-`fact` version of `finite_dimensional_of_finrank_eq_succ`, a lemma which previously existed under a `fact` hypothesis, and rename the `fact` version to `fact_finite_dimensional_of_finrank_eq_succ`.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/pi_Lp.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.fact_finite_dimensional_of_finrank_eq_succ
- \+/\- *lemma* finite_dimensional.finite_dimensional_of_finrank_eq_succ
- \+ *lemma* finite_dimensional.nontrivial_of_finrank_eq_succ
- \+ *lemma* finite_dimensional.nontrivial_of_finrank_pos



## [2021-08-25 06:39:25](https://github.com/leanprover-community/mathlib/commit/fd03625)
chore(ring_theory/ideal): Move local rings into separate file ([#8849](https://github.com/leanprover-community/mathlib/pull/8849))
Moves the material on local rings and local ring homomorphisms into a separate file and adds a module docstring.
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/ideal/basic.lean
- \- *lemma* is_unit_map_iff
- \- *lemma* is_unit_of_map_unit
- \- *lemma* local_of_nonunits_ideal
- \- *lemma* local_of_surjective
- \- *lemma* local_of_unique_max_ideal
- \- *lemma* local_of_unique_nonzero_prime
- \- *lemma* local_ring.eq_maximal_ideal
- \- *lemma* local_ring.is_unit_of_mem_nonunits_one_sub_self
- \- *lemma* local_ring.is_unit_one_sub_self_of_mem_nonunits
- \- *lemma* local_ring.is_unit_or_is_unit_one_sub_self
- \- *lemma* local_ring.le_maximal_ideal
- \- *def* local_ring.maximal_ideal
- \- *lemma* local_ring.maximal_ideal_unique
- \- *lemma* local_ring.mem_maximal_ideal
- \- *lemma* local_ring.nonunits_add
- \- *def* local_ring.residue
- \- *def* local_ring.residue_field
- \- *lemma* map_nonunit
- \- *theorem* of_irreducible_map

Added src/ring_theory/ideal/local_ring.lean
- \+ *lemma* is_unit_map_iff
- \+ *lemma* is_unit_of_map_unit
- \+ *lemma* local_of_nonunits_ideal
- \+ *lemma* local_of_surjective
- \+ *lemma* local_of_unique_max_ideal
- \+ *lemma* local_of_unique_nonzero_prime
- \+ *lemma* local_ring.eq_maximal_ideal
- \+ *lemma* local_ring.is_unit_of_mem_nonunits_one_sub_self
- \+ *lemma* local_ring.is_unit_one_sub_self_of_mem_nonunits
- \+ *lemma* local_ring.is_unit_or_is_unit_one_sub_self
- \+ *lemma* local_ring.le_maximal_ideal
- \+ *def* local_ring.maximal_ideal
- \+ *lemma* local_ring.maximal_ideal_unique
- \+ *lemma* local_ring.mem_maximal_ideal
- \+ *lemma* local_ring.nonunits_add
- \+ *def* local_ring.residue
- \+ *def* local_ring.residue_field
- \+ *lemma* map_nonunit
- \+ *theorem* of_irreducible_map

Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-08-25 06:39:24](https://github.com/leanprover-community/mathlib/commit/88db4e2)
feat(ring_theory): `M / S` is noetherian if `M / S / R` is ([#8846](https://github.com/leanprover-community/mathlib/pull/8846))
Let `M` be an `S`-module and `S` an `R`-algebra. Then to show `M` is noetherian as an `S`-module, it suffices to show it is noetherian as an `R`-module.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *def* submodule.restrict_scalars_embedding

Modified src/linear_algebra/basic.lean


Modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_of_tower



## [2021-08-25 06:39:23](https://github.com/leanprover-community/mathlib/commit/00e57d3)
chore(order/rel_iso): rename `order_embedding.of_map_rel_iff` to `of_map_le_iff` ([#8839](https://github.com/leanprover-community/mathlib/pull/8839))
The old name comes from `rel_embedding`.
#### Estimated changes
Modified src/data/list/nodup_equiv_fin.lean


Modified src/order/rel_iso.lean
- \+ *lemma* order_embedding.coe_of_map_le_iff
- \- *lemma* order_embedding.coe_of_map_rel_iff
- \+ *def* order_embedding.of_map_le_iff
- \- *def* order_embedding.of_map_rel_iff



## [2021-08-25 06:39:21](https://github.com/leanprover-community/mathlib/commit/ef428c6)
feat(topology/metric_space): add `uniform_embedding.comap_metric_space` ([#8838](https://github.com/leanprover-community/mathlib/pull/8838))
* add `uniform_embedding.comap_metric_space` and
  `uniform_inducing.comap_pseudo_metric_space`;
* use the former for `int.metric_space`;
* also add `emetric.closed_ball_mem_nhds`.
#### Estimated changes
Modified src/topology/instances/real.lean
- \+ *lemma* int.uniform_embedding_coe_real

Modified src/topology/metric_space/basic.lean
- \+ *def* uniform_embedding.comap_metric_space
- \+ *def* uniform_inducing.comap_pseudo_metric_space

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.closed_ball_mem_nhds



## [2021-08-25 05:54:13](https://github.com/leanprover-community/mathlib/commit/bd9622f)
chore(category_theory/Fintype): Fix universe restriction in skeleton ([#8855](https://github.com/leanprover-community/mathlib/pull/8855))
This removes a universe restriction in the existence of a skeleton for the category `Fintype`.
Once merged, `Fintype.skeleton.{u}` will be a (small) skeleton for `Fintype.{u}`, with `u` any universe parameter.
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \+ *lemma* Fintype.comp_apply
- \+ *lemma* Fintype.id_apply
- \+ *lemma* Fintype.skeleton.ext
- \+/\- *def* Fintype.skeleton.incl
- \+/\- *lemma* Fintype.skeleton.incl_mk_nat_card
- \+/\- *lemma* Fintype.skeleton.is_skeletal
- \+ *def* Fintype.skeleton.len
- \+/\- *def* Fintype.skeleton.mk
- \- *def* Fintype.skeleton.to_nat
- \+/\- *def* Fintype.skeleton



## [2021-08-24 21:23:20](https://github.com/leanprover-community/mathlib/commit/6c3dda5)
feat(measure_theory/measure/vector_measure): add absolute continuity for vector measures ([#8779](https://github.com/leanprover-community/mathlib/pull/8779))
This PR defines absolute continuity for vector measures and shows that a signed measure is absolutely continuous wrt to a positive measure iff its total variation is absolutely continuous wrt to that measure.
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean
- \+ *lemma* measure_theory.signed_measure.absolutely_continuous_iff
- \+ *def* measure_theory.signed_measure.total_variation
- \+ *lemma* measure_theory.signed_measure.total_variation_absolutely_continuous_iff
- \+ *lemma* measure_theory.signed_measure.total_variation_neg
- \+ *lemma* measure_theory.signed_measure.total_variation_zero

Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.ennreal_to_measure
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.eq
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.map
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.mk
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.refl
- \+ *lemma* measure_theory.vector_measure.absolutely_continuous.trans
- \+ *def* measure_theory.vector_measure.absolutely_continuous
- \+ *def* measure_theory.vector_measure.ennreal_to_measure
- \+ *lemma* measure_theory.vector_measure.ennreal_to_measure_apply
- \+ *def* measure_theory.vector_measure.equiv_measure
- \+ *lemma* measure_theory.vector_measure.map_not_measurable



## [2021-08-24 10:50:23](https://github.com/leanprover-community/mathlib/commit/1dda1cd)
feat(algebra/big_operators/finprod): a few more lemmas ([#8843](https://github.com/leanprover-community/mathlib/pull/8843))
* versions of `monoid_hom.map_finprod` that assume properties of
  `f : M →* N` instead of finiteness of the support;
* `finsum_smul`, `smul_finsum`, `finprod_inv_distrib`: missing
  analogues of lemmas from `finset.prod`/`finset.sum` API.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_inv_distrib
- \+ *lemma* finsum_smul
- \+ *lemma* monoid_hom.map_finprod_of_injective
- \+ *lemma* monoid_hom.map_finprod_of_preimage_one
- \+ *lemma* mul_equiv.map_finprod
- \+ *lemma* smul_finsum



## [2021-08-24 09:54:38](https://github.com/leanprover-community/mathlib/commit/a21fcfa)
feat(data/real/nnreal): upgrade `nnabs` to a `monoid_with_zero_hom` ([#8844](https://github.com/leanprover-community/mathlib/pull/8844))
Other changes:
* add `nnreal.finset_sup_div`;
* rename `nnreal.coe_nnabs` to `real.coe_nnabs`;
* add `real.nndist_eq` and `real.nndist_eq'`.
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean


Modified src/data/real/nnreal.lean
- \- *lemma* cast_nat_abs_eq_nnabs_cast
- \- *lemma* nnreal.coe_nnabs
- \+ *lemma* nnreal.finset_sup_div
- \+ *lemma* real.cast_nat_abs_eq_nnabs_cast
- \+ *lemma* real.coe_nnabs
- \+/\- *lemma* real.coe_to_nnreal_le
- \+/\- *def* real.nnabs
- \+/\- *lemma* real.nnabs_of_nonneg

Modified src/topology/metric_space/basic.lean
- \+ *theorem* real.nndist_eq'
- \+ *theorem* real.nndist_eq



## [2021-08-24 08:27:38](https://github.com/leanprover-community/mathlib/commit/19ae317)
feat(measure_theory/interval_integral): strong version of FTC-2 ([#7978](https://github.com/leanprover-community/mathlib/pull/7978))
The equality `∫ y in a..b, f' y = f b - f a` is currently proved in mathlib assuming that `f'` is continuous. We weaken the assumption, assuming only that `f'` is integrable.
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* measure_theory.integrable_on.continuous_on_mul
- \+ *lemma* measure_theory.integrable_on.continuous_on_mul_of_subset
- \+/\- *lemma* measure_theory.integrable_on.mul_continuous_on
- \+ *lemma* measure_theory.integrable_on.mul_continuous_on_of_subset

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* continuous_linear_map.interval_integral_comp_comm
- \+ *lemma* interval_integrable.continuous_on_mul
- \+ *lemma* interval_integrable.mul_continuous_on
- \+ *lemma* interval_integrable_iff_integrable_Ioc_of_le
- \- *theorem* interval_integral.continuous_on_integral_of_continuous
- \- *lemma* interval_integral.continuous_on_primitive''
- \- *lemma* interval_integral.continuous_on_primitive'
- \+ *lemma* interval_integral.continuous_on_primitive_Icc
- \+ *lemma* interval_integral.continuous_on_primitive_interval
- \+ *lemma* interval_integral.continuous_on_primitive_interval_left
- \+ *lemma* interval_integral.integrable_on_Icc_iff_integrable_on_Ioc'
- \+ *lemma* interval_integral.integrable_on_Icc_iff_integrable_on_Ioc
- \+ *lemma* interval_integral.integral_Icc_eq_integral_Ioc'
- \+/\- *lemma* interval_integral.integral_Icc_eq_integral_Ioc
- \- *theorem* interval_integral.integral_eq_sub_of_has_deriv_at'
- \- *theorem* interval_integral.integral_eq_sub_of_has_deriv_at'_of_le
- \+/\- *theorem* interval_integral.integral_eq_sub_of_has_deriv_at
- \+ *theorem* interval_integral.integral_eq_sub_of_has_deriv_at_of_le
- \+ *lemma* interval_integral.integral_eq_sub_of_has_deriv_right_of_le_real'
- \+ *lemma* interval_integral.integral_eq_sub_of_has_deriv_right_of_le_real
- \+ *lemma* interval_integral.integral_le_sub_of_has_deriv_right_of_le
- \+ *lemma* interval_integral.interval_integrable_iff_integrable_Icc_of_le
- \+ *lemma* interval_integral.sub_le_integral_of_has_deriv_right_of_le
- \+ *lemma* measure_theory.integrable_on.interval_integrable



## [2021-08-24 04:00:04](https://github.com/leanprover-community/mathlib/commit/737b208)
feat(linear_algebra/dimension): generalize dim_map_le to heterogeneous universes ([#8800](https://github.com/leanprover-community/mathlib/pull/8800))
Per @hrmacbeth's [request on zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Behaviour.20of.20finrank.20under.20morphisms).
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* lift_dim_map_le
- \+ *lemma* lift_dim_range_le

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.lift_mk_eq'



## [2021-08-24 02:16:33](https://github.com/leanprover-community/mathlib/commit/4aa8705)
chore(scripts): update nolints.txt ([#8840](https://github.com/leanprover-community/mathlib/pull/8840))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-23 20:37:30](https://github.com/leanprover-community/mathlib/commit/26448a2)
feat(analysis/normed_space/exponential): define exponential in a Banach algebra and prove basic results ([#8576](https://github.com/leanprover-community/mathlib/pull/8576))
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* formal_multilinear_series.summable_nnnorm_mul_pow
- \+ *lemma* formal_multilinear_series.summable_norm_apply
- \+/\- *lemma* formal_multilinear_series.summable_norm_mul_pow
- \- *lemma* formal_multilinear_series.summable_norm_of_lt_radius
- \- *lemma* formal_multilinear_series.summable_of_nnnorm_lt_radius

Added src/analysis/normed_space/exponential.lean
- \+ *lemma* analytic_at_exp_of_mem_ball
- \+ *lemma* complex.exp_eq_exp_ℂ_ℂ
- \+ *lemma* continuous_on_exp
- \+ *lemma* exp_add
- \+ *lemma* exp_add_of_commute
- \+ *lemma* exp_add_of_commute_of_mem_ball
- \+ *lemma* exp_add_of_mem_ball
- \+ *lemma* exp_analytic
- \+ *lemma* exp_continuous
- \+ *lemma* exp_eq_exp_of_field_extension
- \+ *lemma* exp_eq_tsum
- \+ *lemma* exp_eq_tsum_field
- \+ *lemma* exp_has_fpower_series_at_zero
- \+ *lemma* exp_has_fpower_series_on_ball
- \+ *def* exp_series
- \+ *lemma* exp_series_apply_eq'
- \+ *lemma* exp_series_apply_eq
- \+ *lemma* exp_series_apply_eq_field'
- \+ *lemma* exp_series_apply_eq_field
- \+ *lemma* exp_series_eq_exp_series_of_field_extension
- \+ *lemma* exp_series_field_has_sum_exp
- \+ *lemma* exp_series_field_has_sum_exp_of_mem_ball
- \+ *lemma* exp_series_field_summable
- \+ *lemma* exp_series_field_summable_of_mem_ball
- \+ *lemma* exp_series_has_sum_exp'
- \+ *lemma* exp_series_has_sum_exp
- \+ *lemma* exp_series_has_sum_exp_of_mem_ball'
- \+ *lemma* exp_series_has_sum_exp_of_mem_ball
- \+ *lemma* exp_series_radius_eq_top
- \+ *lemma* exp_series_radius_pos
- \+ *lemma* exp_series_sum_eq
- \+ *lemma* exp_series_sum_eq_field
- \+ *lemma* exp_series_summable'
- \+ *lemma* exp_series_summable
- \+ *lemma* exp_series_summable_of_mem_ball'
- \+ *lemma* exp_series_summable_of_mem_ball
- \+ *lemma* exp_zero
- \+ *lemma* exp_ℝ_ℂ_eq_exp_ℂ_ℂ
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* has_deriv_at_exp_of_mem_ball
- \+ *lemma* has_deriv_at_exp_zero
- \+ *lemma* has_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_fderiv_at_exp
- \+ *lemma* has_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_fderiv_at_exp_zero
- \+ *lemma* has_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* has_fpower_series_at_exp_zero_of_radius_pos
- \+ *lemma* has_fpower_series_on_ball_exp_of_radius_pos
- \+ *lemma* has_strict_deriv_at_exp
- \+ *lemma* has_strict_deriv_at_exp_of_mem_ball
- \+ *lemma* has_strict_deriv_at_exp_zero
- \+ *lemma* has_strict_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_strict_fderiv_at_exp
- \+ *lemma* has_strict_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_strict_fderiv_at_exp_zero
- \+ *lemma* has_strict_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* norm_exp_series_field_summable
- \+ *lemma* norm_exp_series_field_summable_of_mem_ball
- \+ *lemma* norm_exp_series_summable'
- \+ *lemma* norm_exp_series_summable
- \+ *lemma* norm_exp_series_summable_of_mem_ball'
- \+ *lemma* norm_exp_series_summable_of_mem_ball
- \+ *lemma* real.exp_eq_exp_ℝ_ℝ

Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* finset.nat.antidiagonal.fst_le
- \+ *lemma* finset.nat.antidiagonal.snd_le

Modified src/data/nat/choose/dvd.lean
- \+ *lemma* nat.cast_add_choose
- \+/\- *lemma* nat.cast_choose

Modified src/number_theory/bernoulli_polynomials.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.congr
- \+ *lemma* summable_congr

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.eball_top_eq_univ



## [2021-08-23 17:56:01](https://github.com/leanprover-community/mathlib/commit/2f4dc3a)
feat(ring_theory): generalize `exists_integral_multiple` ([#8827](https://github.com/leanprover-community/mathlib/pull/8827))
Not only is `z * (y : integral_closure R A)` integral, so is `z * (y : R)`!
#### Estimated changes
Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/localization.lean




## [2021-08-23 17:55:59](https://github.com/leanprover-community/mathlib/commit/700effa)
feat(ring_theory/localization): the algebraic elements over `Frac(R)` are those over `R` ([#8826](https://github.com/leanprover-community/mathlib/pull/8826))
We had this lemma for `L / K` is algebraic iff `L / A` is, but now we also have it elementwise!
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.is_algebraic_iff



## [2021-08-23 17:55:58](https://github.com/leanprover-community/mathlib/commit/2a69dc2)
feat(ring_theory): two little lemmas on Noetherianness ([#8825](https://github.com/leanprover-community/mathlib/pull/8825))
No real deep thoughts behind these lemmas, just that they are needed to show the integral closure of a Dedekind domain is Noetherian.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_noetherian_adjoin_finset

Modified src/ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_of_le



## [2021-08-23 17:55:57](https://github.com/leanprover-community/mathlib/commit/8a7e4f7)
feat(measure_theory): volume of a (closed) L∞-ball ([#8791](https://github.com/leanprover-community/mathlib/pull/8791))
* pi measure of a (closed or open) ball;
* volume of a (closed or open) ball in
  - `Π i, α i`;
  - `ℝ`;
  - `ι → ℝ`;
* volumes of `univ`, `emetric.ball`, and `emetric.closed_ball` in `ℝ`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_pow

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.measure.pi_ball
- \+ *lemma* measure_theory.measure.pi_closed_ball
- \+ *lemma* measure_theory.volume_pi_ball
- \+ *lemma* measure_theory.volume_pi_closed_ball

Modified src/measure_theory/measure/lebesgue.lean
- \+ *lemma* real.volume_ball
- \+ *lemma* real.volume_closed_ball
- \+ *lemma* real.volume_emetric_ball
- \+ *lemma* real.volume_emetric_closed_ball
- \+ *lemma* real.volume_pi_ball
- \+ *lemma* real.volume_pi_closed_ball
- \+ *lemma* real.volume_univ



## [2021-08-23 17:55:56](https://github.com/leanprover-community/mathlib/commit/ff85e9c)
feat(measure_theory/measure/measure_space): obtain pairwise disjoint spanning sets wrt. two measures ([#8750](https://github.com/leanprover-community/mathlib/pull/8750))
Given two sigma finite measures, there exists a sequence of pairwise disjoint spanning sets that are finite wrt. both measures
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.exists_eq_disjoint_finite_spanning_sets_in
- \+ *lemma* measure_theory.measure.finite_spanning_sets_in.disjointed_set_eq
- \+ *def* measure_theory.measure.finite_spanning_sets_in.of_le



## [2021-08-23 17:55:55](https://github.com/leanprover-community/mathlib/commit/98a6329)
refactor(algebra/group_power): use `covariant_class` ([#8713](https://github.com/leanprover-community/mathlib/pull/8713))
## Main changes
* use `covariant_class` instead of `canonically_ordered_*` or `ordered_add_*` as an assumption in many lemmas;
* move some lemmas to the root namespace;
* use `to_additive` for more lemmas;
## Detailed list of API changes
* `canonically_ordered_comm_semiring.pow_le_pow_of_le_left`:
  - rename to `pow_le_pow_of_le_left'`;
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_le_nsmul_of_le_right`;
* `canonically_ordered_comm_semiring.one_le_pow_of_one_le`:
  - rename to `one_le_pow_of_one_le`';
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_nonneg`;
* `canonically_ordered_comm_semiring.pow_le_one`:
  - rename to `pow_le_one'`;
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_nonpos`;
* add `pow_le_pow'`, generate `nsmul_le_nsmul`;
* add `pow_le_pow_of_le_one'` and `nsmul_le_nsmul_of_nonpos`;
* add `one_lt_pow'`, generate `nsmul_pos`;
  - as a side effect, `nsmul_pos` now assumes `n ≠ 0` instead of `0 < n`.
* add `pow_lt_one'`, generate `nsmul_neg`;
* add `pow_lt_pow'`, generate `nsmul_lt_nsmul`;
* generalize `one_le_pow_iff` and `pow_le_one_iff`, generate `nsmul_nonneg_iff` and `nsmul_nonpos_iff`;
* generalize `one_lt_pow_iff`, `pow_lt_one_iff`, and `pow_eq_one_iff`, generate `nsmul_pos_iff`, `nsmul_neg_iff`, and `nsmul_eq_zero_iff`;
* add `one_le_gpow`, generate `gsmul_nonneg`;
* rename `eq_of_sq_eq_sq` to `sq_eq_sq`, golf;
* drop `eq_one_of_pow_eq_one` in favor of the `iff` version `pow_eq_one_iff`;
* add missing instance `nat.ordered_comm_semiring`;
## Misc changes
* replace some proofs about `nat.pow` with references to generic lemmas;
* add `nnreal.coe_eq_one`;
#### Estimated changes
Modified archive/imo/imo2008_q4.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_power/order.lean
- \- *theorem* canonically_ordered_comm_semiring.one_le_pow_of_one_le
- \- *theorem* canonically_ordered_comm_semiring.pow_le_one
- \- *lemma* canonically_ordered_comm_semiring.pow_le_pow_of_le_left
- \+/\- *theorem* canonically_ordered_comm_semiring.pow_pos
- \- *lemma* eq_of_sq_eq_sq
- \- *theorem* gsmul_nonneg
- \- *theorem* nsmul_le_nsmul
- \- *lemma* nsmul_le_nsmul_of_le_right
- \- *theorem* nsmul_lt_nsmul
- \- *theorem* nsmul_nonneg
- \- *lemma* nsmul_pos
- \+ *theorem* one_le_gpow
- \+ *lemma* one_le_pow_iff
- \+ *theorem* one_le_pow_of_one_le'
- \+ *theorem* one_lt_pow'
- \+ *lemma* one_lt_pow_iff
- \+ *lemma* pow_eq_one_iff
- \+ *theorem* pow_le_one'
- \+ *lemma* pow_le_one_iff
- \+ *theorem* pow_le_pow'
- \+ *lemma* pow_le_pow_of_le_left'
- \+ *theorem* pow_le_pow_of_le_one'
- \+/\- *theorem* pow_left_inj
- \+ *theorem* pow_lt_one'
- \+ *lemma* pow_lt_one_iff
- \+ *theorem* pow_lt_pow''
- \+ *lemma* sq_eq_sq

Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \- *lemma* eq_one_of_pow_eq_one
- \- *lemma* one_le_pow_iff
- \- *lemma* one_le_pow_of_one_le'
- \- *lemma* pow_eq_one_iff
- \- *lemma* pow_le_one_iff
- \- *lemma* pow_le_one_of_le_one

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/specific_limits.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/pow.lean
- \+/\- *theorem* nat.mod_pow_succ
- \+/\- *theorem* nat.pow_le_pow_of_le_right
- \+/\- *theorem* nat.pow_lt_pow_of_lt_right

Modified src/data/real/nnreal.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/valuation/integral.lean




## [2021-08-23 17:55:54](https://github.com/leanprover-community/mathlib/commit/b7f0323)
feat(topology): interior of a finite product of sets ([#8695](https://github.com/leanprover-community/mathlib/pull/8695))
Also finishes the filter inf work from [#8657](https://github.com/leanprover-community/mathlib/pull/8657) proving stronger lemmas for
filter.infi
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_dite
- \+ *lemma* set.Inter_ite
- \+ *lemma* set.Union_dite
- \+ *lemma* set.Union_ite
- \+ *lemma* set.image_projection_prod

Modified src/measure_theory/measurable_space.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* infi_dite
- \+ *lemma* infi_ite
- \+ *lemma* supr_dite
- \+ *lemma* supr_ite

Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.exists_Inter_of_mem_infi
- \+ *lemma* filter.mem_infi_of_Inter
- \+ *lemma* filter.mem_infi_of_fintype

Modified src/topology/bases.lean


Modified src/topology/constructions.lean
- \+ *lemma* interior_pi_set
- \+ *lemma* mem_nhds_pi
- \+ *lemma* set_pi_mem_nhds_iff

Modified src/topology/continuous_on.lean




## [2021-08-23 16:45:34](https://github.com/leanprover-community/mathlib/commit/608faf0)
feat(measure_theory/function/conditional_expectation): uniqueness of the conditional expectation ([#8802](https://github.com/leanprover-community/mathlib/pull/8802))
The main part of the PR is the new file `ae_eq_of_integral`, in which many different lemmas prove variants of the statement "if two functions have same integral on all sets, then they are equal almost everywhere".
In the file `conditional_expectation`, a similar lemma is written for functions which have same integral on all sets in a sub-sigma-algebra and are measurable with respect to that sigma-algebra. This proves the uniqueness of the conditional expectation.
#### Estimated changes
Modified src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* exists_dual_vector''

Added src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* measure_theory.Lp.ae_eq_of_forall_set_integral_eq
- \+ *lemma* measure_theory.Lp.ae_eq_zero_of_forall_set_integral_eq_zero
- \+ *lemma* measure_theory.ae_const_le_iff_forall_lt_measure_zero
- \+ *lemma* measure_theory.ae_eq_of_forall_set_integral_eq_of_sigma_finite
- \+ *lemma* measure_theory.ae_eq_restrict_of_forall_set_integral_eq
- \+ *lemma* measure_theory.ae_eq_zero_of_forall_dual
- \+ *lemma* measure_theory.ae_eq_zero_of_forall_inner
- \+ *lemma* measure_theory.ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim
- \+ *lemma* measure_theory.ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite
- \+ *lemma* measure_theory.ae_eq_zero_restrict_of_forall_set_integral_eq_zero
- \+ *lemma* measure_theory.ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg
- \+ *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure
- \+ *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable
- \+ *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite
- \+ *lemma* measure_theory.ae_nonneg_restrict_of_forall_set_integral_nonneg
- \+ *lemma* measure_theory.ae_nonneg_restrict_of_forall_set_integral_nonneg_inter
- \+ *lemma* measure_theory.integrable.ae_eq_of_forall_set_integral_eq
- \+ *lemma* measure_theory.integrable.ae_eq_zero_of_forall_set_integral_eq_zero
- \+ *lemma* measure_theory.integrable.ae_nonneg_of_forall_set_integral_nonneg

Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.Lp.ae_eq_of_forall_set_integral_eq'
- \+ *lemma* measure_theory.Lp.ae_eq_zero_of_forall_set_integral_eq_zero'
- \+ *lemma* measure_theory.Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero
- \+ *lemma* measure_theory.Lp_meas.ae_fin_strongly_measurable'
- \+ *lemma* measure_theory.ae_eq_of_forall_set_integral_eq_of_sigma_finite'
- \+ *lemma* measure_theory.ae_eq_trim_iff_of_ae_measurable'
- \+ *lemma* measure_theory.ae_measurable'.ae_eq_mk
- \+ *lemma* measure_theory.ae_measurable'.measurable_mk
- \+ *def* measure_theory.ae_measurable'.mk
- \+ *lemma* measure_theory.ae_measurable'.neg
- \+ *lemma* measure_theory.ae_measurable'.sub
- \+ *lemma* measure_theory.measurable.ae_measurable'

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_of_ae_restrict_of_ae_restrict_compl
- \+ *lemma* measure_theory.sub_ae_eq_zero

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* exists_seq_strict_antimono_tendsto'
- \+ *lemma* exists_seq_strict_mono_tendsto'



## [2021-08-23 16:02:50](https://github.com/leanprover-community/mathlib/commit/9a7d9a8)
feat(group_theory/nilpotent): add def lemmas, basic lemmas on central series ([#8730](https://github.com/leanprover-community/mathlib/pull/8730))
Add to API for nilpotent groups with simp def lemmas and other basic properties of central series.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+/\- *def* is_ascending_central_series
- \+ *lemma* lower_central_series_zero
- \+ *lemma* mem_lower_central_series_succ_iff
- \+/\- *lemma* mem_upper_central_series_succ_iff
- \+ *lemma* upper_central_series.map
- \+ *lemma* upper_central_series_mono
- \+ *lemma* upper_central_series_zero
- \- *lemma* upper_central_series_zero_def



## [2021-08-23 14:22:14](https://github.com/leanprover-community/mathlib/commit/df3e886)
feat(group_theory/group_action): generalize mul_action.function_End to other endomorphisms ([#8724](https://github.com/leanprover-community/mathlib/pull/8724))
The main aim of this PR is to remove [`intermediate_field.subgroup_action`](https://leanprover-community.github.io/mathlib_docs/field_theory/galois.html#intermediate_field.subgroup_action) which is a weird special case of the much more general instance `f • a = f a`, added in this PR as `alg_equiv.apply_mul_semiring_action`. We add the same actions for all the other hom types for consistency.
These generalizations are in line with the `mul_action.function_End` (renamed to `function.End.apply_mul_action`) and `mul_action.perm` (renamed to `equiv.perm.apply_mul_action`) instances introduced by @dwarn, providing any endomorphism that has a monoid structure with a faithful `mul_action` corresponding to function application.
Note that there is no monoid structure on `ring_equiv`, or `alg_hom`, so this PR does not bother with the corresponding action.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean


Modified src/data/equiv/mul_add_aut.lean


Modified src/field_theory/galois.lean


Modified src/group_theory/group_action/defs.lean
- \+ *lemma* add_monoid.End.smul_def

Modified src/group_theory/group_action/group.lean
- \- *lemma* equiv.perm.smul_def

Modified src/linear_algebra/basic.lean


Modified src/ring_theory/derivation.lean




## [2021-08-23 12:46:47](https://github.com/leanprover-community/mathlib/commit/3c49044)
feat(data/list/nodup): nodup.nth_le_inj_iff ([#8813](https://github.com/leanprover-community/mathlib/pull/8813))
This allows rewriting as an `inj_iff` lemma directly via proj notation.
#### Estimated changes
Modified src/data/list/nodup.lean
- \+ *theorem* list.nodup.nth_le_inj_iff



## [2021-08-23 12:46:47](https://github.com/leanprover-community/mathlib/commit/f8f551a)
feat(data/fintype/basic): choose_subtype_eq ([#8812](https://github.com/leanprover-community/mathlib/pull/8812))
Choosing out of a finite subtype such that the underlying value is precisely some value of the parent type works as intended.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.choose_subtype_eq



## [2021-08-23 12:00:47](https://github.com/leanprover-community/mathlib/commit/a85c9f6)
chore(field_theory): make `is_separable` an instance parameter ([#8741](https://github.com/leanprover-community/mathlib/pull/8741))
There were a few places that had an explicit `is_separable` parameter. For simplicity and consistency, let's make them all instance params.
#### Estimated changes
Modified src/field_theory/galois.lean
- \+/\- *lemma* is_galois.card_aut_eq_finrank
- \+/\- *lemma* is_galois.is_separable_splitting_field
- \+/\- *lemma* is_galois.separable

Modified src/field_theory/primitive_element.lean
- \+/\- *theorem* field.exists_primitive_element
- \+/\- *lemma* field.primitive_element_inf_aux

Modified src/field_theory/separable.lean
- \+/\- *theorem* is_separable.is_integral
- \+/\- *theorem* is_separable.separable
- \+/\- *lemma* is_separable_tower_top_of_is_separable



## [2021-08-23 10:17:14](https://github.com/leanprover-community/mathlib/commit/8b9a47b)
feat(data/finset/basic): finset.exists_ne_of_one_lt_card ([#8816](https://github.com/leanprover-community/mathlib/pull/8816))
Analog of `fintype.exists_ne_of_one_lt_card`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.exists_ne_of_one_lt_card

Modified src/group_theory/p_group.lean




## [2021-08-23 10:17:13](https://github.com/leanprover-community/mathlib/commit/a52a9fe)
chore(data/multiset/basic): move abs_sum_le_sum_abs from algebra/big_operators/basic.lean. ([#8804](https://github.com/leanprover-community/mathlib/pull/8804))
There doesn't seem to be a reason for the place it has now.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \- *lemma* multiset.abs_sum_le_sum_abs

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.abs_sum_le_sum_abs



## [2021-08-23 10:17:12](https://github.com/leanprover-community/mathlib/commit/f98fc00)
docs(logic/relation): add module docstring ([#8773](https://github.com/leanprover-community/mathlib/pull/8773))
Also fix whitespaces
#### Estimated changes
Modified src/logic/relation.lean
- \+/\- *def* relation.comp
- \+/\- *def* relation.join
- \+/\- *lemma* relation.refl_gen.to_refl_trans_gen
- \+/\- *lemma* relation.refl_trans_gen.cases_head
- \+/\- *lemma* relation.refl_trans_gen.cases_head_iff
- \+/\- *lemma* relation.refl_trans_gen.cases_tail
- \+/\- *lemma* relation.refl_trans_gen_iff_eq
- \+/\- *lemma* relation.transitive_join



## [2021-08-23 10:17:11](https://github.com/leanprover-community/mathlib/commit/c811dd7)
feat(data/nat/mul_ind): multiplicative induction principles ([#8514](https://github.com/leanprover-community/mathlib/pull/8514))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.dvd_div_iff

Added src/data/nat/mul_ind.lean
- \+ *def* nat.rec_on_mul
- \+ *def* nat.rec_on_pos_prime_coprime
- \+ *def* nat.rec_on_prime_coprime
- \+ *def* nat.rec_on_prime_pow

Modified src/data/nat/pow.lean
- \+ *lemma* nat.one_lt_pow_iff



## [2021-08-23 09:16:14](https://github.com/leanprover-community/mathlib/commit/f949172)
feat(data/polynomial/basic): polynomial.op_ring_equiv ([#8537](https://github.com/leanprover-community/mathlib/pull/8537))
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *def* polynomial.op_ring_equiv



## [2021-08-22 20:10:11](https://github.com/leanprover-community/mathlib/commit/9945a16)
refactor(analysis/normed_space/{add_torsor, mazur_ulam}): adjust Mazur-Ulam file to use affine isometries ([#8661](https://github.com/leanprover-community/mathlib/pull/8661))
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* affine_map.continuous_linear_iff
- \- *lemma* isometric.coe_const_vadd
- \- *lemma* isometric.coe_const_vsub
- \- *lemma* isometric.coe_const_vsub_symm
- \- *lemma* isometric.coe_vadd_const
- \- *lemma* isometric.coe_vadd_const_symm
- \- *def* isometric.const_vadd
- \- *lemma* isometric.const_vadd_zero
- \- *def* isometric.const_vsub
- \- *lemma* isometric.dist_point_reflection_fixed
- \- *lemma* isometric.dist_point_reflection_self'
- \- *lemma* isometric.dist_point_reflection_self
- \- *lemma* isometric.dist_point_reflection_self_real
- \- *def* isometric.point_reflection
- \- *lemma* isometric.point_reflection_apply
- \- *lemma* isometric.point_reflection_fixed_iff
- \- *lemma* isometric.point_reflection_involutive
- \- *lemma* isometric.point_reflection_midpoint_left
- \- *lemma* isometric.point_reflection_midpoint_right
- \- *lemma* isometric.point_reflection_self
- \- *lemma* isometric.point_reflection_symm
- \- *lemma* isometric.point_reflection_to_equiv
- \- *def* isometric.vadd_const
- \- *lemma* isometric.vadd_const_to_equiv
- \- *lemma* isometry.vadd_vsub

Modified src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* affine_isometry_equiv.coe_const_vadd
- \+ *lemma* affine_isometry_equiv.coe_const_vsub
- \+ *lemma* affine_isometry_equiv.coe_vadd_const
- \+ *lemma* affine_isometry_equiv.coe_vadd_const_symm
- \+ *def* affine_isometry_equiv.const_vadd
- \+ *lemma* affine_isometry_equiv.const_vadd_zero
- \+ *def* affine_isometry_equiv.const_vsub
- \+ *lemma* affine_isometry_equiv.dist_point_reflection_fixed
- \+ *lemma* affine_isometry_equiv.dist_point_reflection_self'
- \+ *lemma* affine_isometry_equiv.dist_point_reflection_self
- \+ *lemma* affine_isometry_equiv.dist_point_reflection_self_real
- \+ *def* affine_isometry_equiv.point_reflection
- \+ *lemma* affine_isometry_equiv.point_reflection_apply
- \+ *lemma* affine_isometry_equiv.point_reflection_fixed_iff
- \+ *lemma* affine_isometry_equiv.point_reflection_involutive
- \+ *lemma* affine_isometry_equiv.point_reflection_midpoint_left
- \+ *lemma* affine_isometry_equiv.point_reflection_midpoint_right
- \+ *lemma* affine_isometry_equiv.point_reflection_self
- \+ *lemma* affine_isometry_equiv.point_reflection_symm
- \+ *lemma* affine_isometry_equiv.point_reflection_to_affine_equiv
- \+ *lemma* affine_isometry_equiv.symm_const_vsub
- \+ *def* affine_isometry_equiv.vadd_const
- \+ *lemma* affine_isometry_equiv.vadd_const_to_affine_equiv
- \+ *lemma* affine_isometry_equiv.vadd_vsub
- \+ *lemma* affine_map.continuous_linear_iff

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_neg
- \+ *def* linear_isometry_equiv.neg
- \+ *lemma* linear_isometry_equiv.symm_neg

Modified src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* isometric.coe_fn_to_real_affine_isometry_equiv
- \- *lemma* isometric.coe_to_affine_equiv
- \+ *lemma* isometric.coe_to_real_affine_isometry_equiv
- \- *def* isometric.to_affine_equiv
- \+ *def* isometric.to_real_affine_isometry_equiv



## [2021-08-22 19:02:17](https://github.com/leanprover-community/mathlib/commit/d9113ec)
doc(linear_algebra/trace): fix error in title ([#8803](https://github.com/leanprover-community/mathlib/pull/8803))
the first two lines of this were super contradictory
#### Estimated changes
Modified src/linear_algebra/trace.lean




## [2021-08-22 16:54:23](https://github.com/leanprover-community/mathlib/commit/87f14e3)
feat(topology/basic): interior of a singleton ([#8784](https://github.com/leanprover-community/mathlib/pull/8784))
* add generic lemmas `interior_singleton`, `closure_compl_singleton`;
* add more lemmas and instances about `ne_bot (𝓝[{x}ᶜ] x)`;
* rename `dense_compl_singleton` to `dense_compl_singleton_iff_not_open`,
  add new `dense_compl_singleton` that assumes `[ne_bot (𝓝[{x}ᶜ] x)]`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* module.punctured_nhds_ne_bot
- \+/\- *lemma* submodule.eq_top_of_nonempty_interior'

Modified src/topology/basic.lean
- \+ *lemma* closure_compl_singleton
- \+ *lemma* dense.interior_compl
- \+/\- *lemma* dense_compl_singleton
- \+ *lemma* dense_compl_singleton_iff_not_open
- \+ *lemma* interior_eq_empty_iff_dense_compl
- \+ *lemma* interior_singleton
- \+ *lemma* mem_closure_iff_nhds_within_ne_bot

Modified src/topology/continuous_on.lean
- \- *lemma* mem_closure_iff_nhds_within_ne_bot



## [2021-08-22 16:54:22](https://github.com/leanprover-community/mathlib/commit/db9d4a3)
feat(data/finset,order/conditionally_complete_lattice): lemmas about `min'/max'` ([#8782](https://github.com/leanprover-community/mathlib/pull/8782))
## `data/finset/*`
* add `finset.nonempty.to_set`;
* add lemmas `finset.max'_lt_iff`, `finset.lt_min'_iff`,
  `finset.max'_eq_sup'`, `finset.min'_eq_inf'`;
* rewrite `finset.induction_on_max` without using `finset.card`,
  move one step to `finset.lt_max'_of_mem_erase_max'`;
## `order/conditionally_complete_lattice`
* add lemmas relating `Sup`/`Inf` of a nonempty finite set in a
  conditionally complete lattice to
 `finset.sup'`/`finset.inf'`/`finset.max'`/`finset.min'`;
* a few more lemmas about `Sup`/`Inf` of a nonempty finite set
  in a conditionally complete lattice / linear order;
## `order/filter/at_top_bot`
* golf the proof of `filter.high_scores`.
#### Estimated changes
Modified src/data/finset/basic.lean


Modified src/data/finset/lattice.lean
- \+ *lemma* finset.lt_max'_of_mem_erase_max'
- \+ *lemma* finset.lt_min'_iff
- \+ *lemma* finset.max'_eq_sup'
- \+ *lemma* finset.max'_lt_iff
- \+ *lemma* finset.min'_eq_inf'
- \+ *lemma* finset.min'_lt_of_mem_erase_min'

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* finset.nonempty.cInf_eq_min'
- \+ *lemma* finset.nonempty.cSup_eq_max'
- \+ *lemma* finset.nonempty.sup'_eq_cSup_image
- \+ *lemma* finset.nonempty.sup'_id_eq_cSup
- \+ *lemma* set.finite.cSup_lt_iff
- \+ *lemma* set.finite.lt_cInf_iff

Modified src/order/filter/at_top_bot.lean




## [2021-08-22 16:54:21](https://github.com/leanprover-community/mathlib/commit/ea9cd02)
refactor(geometry/euclidean/basic): adjust Euclidean geometry to use affine isometries for reflections ([#8662](https://github.com/leanprover-community/mathlib/pull/8662))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* norm_sub_eq_norm_add
- \+ *def* reflection
- \+ *lemma* reflection_apply
- \+ *lemma* reflection_involutive
- \+ *lemma* reflection_reflection
- \+ *lemma* reflection_symm

Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.orthogonal_projection_mem_subspace_eq_self
- \+ *lemma* euclidean_geometry.orthogonal_projection_vsub_orthogonal_projection

Modified src/geometry/euclidean/circumcenter.lean




## [2021-08-22 15:49:31](https://github.com/leanprover-community/mathlib/commit/a9c1300)
refactor(topology/metric_space/basic): rename `closed_ball_Icc` ([#8790](https://github.com/leanprover-community/mathlib/pull/8790))
* rename `closed_ball_Icc` to `real.closed_ball_eq`;
* add `real.ball_eq`, `int.ball_eq`, `int.closed_ball_eq`,
  `int.preimage_ball`, `int.preimage_closed_ball`.
#### Estimated changes
Modified src/number_theory/liouville/basic.lean


Modified src/topology/instances/real.lean
- \+ *theorem* int.ball_eq
- \+ *theorem* int.closed_ball_eq
- \+/\- *theorem* int.dist_cast_rat
- \+/\- *theorem* int.dist_cast_real
- \+/\- *theorem* int.dist_eq
- \+ *theorem* int.preimage_ball
- \+ *theorem* int.preimage_closed_ball

Modified src/topology/metric_space/basic.lean
- \- *lemma* closed_ball_Icc
- \+ *lemma* real.ball_eq
- \+ *lemma* real.closed_ball_eq



## [2021-08-22 13:58:19](https://github.com/leanprover-community/mathlib/commit/373911d)
chore(measure_theory): make `μ` an explicit argument in `subsingleton.measure_zero` etc ([#8793](https://github.com/leanprover-community/mathlib/pull/8793))
#### Estimated changes
Modified counterexamples/phillips.lean


Modified src/measure_theory/measure/hausdorff.lean
- \+ *lemma* measure_theory.dimH_countable
- \+/\- *lemma* measure_theory.dimH_empty
- \+/\- *lemma* measure_theory.dimH_singleton

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* finset.measure_zero
- \- *lemma* measure_theory.measure_subsingleton
- \+/\- *lemma* set.countable.measure_zero
- \+/\- *lemma* set.finite.measure_zero
- \+ *lemma* set.subsingleton.measure_zero



## [2021-08-22 03:08:52](https://github.com/leanprover-community/mathlib/commit/8a96d00)
chore(scripts): update nolints.txt ([#8798](https://github.com/leanprover-community/mathlib/pull/8798))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-22 01:10:57](https://github.com/leanprover-community/mathlib/commit/f915106)
chore(data/set/lattice): a few lemmas, golf ([#8795](https://github.com/leanprover-community/mathlib/pull/8795))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_nonempty_index
- \+ *lemma* set.Union_nonempty_self
- \+ *lemma* set.bUnion_Union
- \+ *lemma* set.bUnion_self



## [2021-08-21 21:43:39](https://github.com/leanprover-community/mathlib/commit/d3e20b4)
chore(data/multiset/basic): consistently use singleton notation ([#8786](https://github.com/leanprover-community/mathlib/pull/8786))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/gcd_monoid/multiset.lean
- \+/\- *lemma* multiset.gcd_singleton
- \+/\- *lemma* multiset.lcm_singleton

Modified src/data/finset/basic.lean
- \+/\- *theorem* finset.singleton_val
- \+ *lemma* multiset.to_finset_singleton

Modified src/data/finset/noncomm_prod.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* multiset.to_finsupp_singleton

Modified src/data/multiset/antidiagonal.lean
- \+/\- *theorem* multiset.antidiagonal_zero

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.bind_singleton
- \+/\- *theorem* multiset.card_eq_one
- \+/\- *theorem* multiset.card_singleton
- \+/\- *theorem* multiset.count_singleton
- \+ *theorem* multiset.count_singleton_self
- \+/\- *theorem* multiset.disjoint_singleton
- \+ *theorem* multiset.foldr_singleton
- \+ *theorem* multiset.map_singleton
- \- *lemma* multiset.map_singleton
- \+/\- *theorem* multiset.mem_singleton
- \+/\- *theorem* multiset.mem_singleton_self
- \+/\- *theorem* multiset.prod_singleton
- \+/\- *theorem* multiset.product_singleton
- \+/\- *lemma* multiset.repeat_one
- \+/\- *theorem* multiset.repeat_subset_singleton
- \+/\- *theorem* multiset.singleton_add
- \+ *theorem* multiset.singleton_bind
- \+/\- *theorem* multiset.singleton_disjoint
- \+ *theorem* multiset.singleton_eq_cons
- \- *theorem* multiset.singleton_eq_singleton
- \+/\- *theorem* multiset.singleton_inj
- \+ *theorem* multiset.singleton_join
- \+/\- *theorem* multiset.singleton_le
- \+/\- *theorem* multiset.singleton_ne_zero
- \+/\- *theorem* multiset.sum_map_singleton

Modified src/data/multiset/erase_dup.lean
- \+/\- *theorem* multiset.erase_dup_singleton

Modified src/data/multiset/finset_ops.lean
- \+/\- *theorem* multiset.ndinsert_zero

Modified src/data/multiset/fold.lean
- \+/\- *theorem* multiset.fold_singleton

Modified src/data/multiset/functor.lean
- \+/\- *lemma* multiset.pure_def

Modified src/data/multiset/lattice.lean
- \+/\- *lemma* multiset.inf_singleton
- \+/\- *lemma* multiset.sup_singleton

Modified src/data/multiset/nodup.lean
- \+/\- *theorem* multiset.nodup_singleton

Modified src/data/multiset/pi.lean
- \+/\- *lemma* multiset.pi_zero

Modified src/data/multiset/powerset.lean
- \+/\- *theorem* multiset.powerset_zero

Modified src/data/multiset/sections.lean
- \+/\- *lemma* multiset.sections_zero

Modified src/data/pnat/factors.lean
- \+/\- *def* prime_multiset.of_prime

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.roots_X_sub_C

Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/fin.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/number_theory/ADE_inequality.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2021-08-21 21:43:38](https://github.com/leanprover-community/mathlib/commit/252cb02)
feat(linear_algebra/vandermonde): `vandermonde v` multiplied by its transpose ([#8776](https://github.com/leanprover-community/mathlib/pull/8776))
Two not very exciting lemmas about multiplying a Vandermonde matrix by its transpose (one for each side). I don't know if they are really useful, so I could also just inline them in [#8777](https://github.com/leanprover-community/mathlib/pull/8777).
#### Estimated changes
Modified src/linear_algebra/vandermonde.lean
- \+ *lemma* matrix.vandermonde_mul_vandermonde_transpose
- \+ *lemma* matrix.vandermonde_transpose_mul_vandermonde



## [2021-08-21 21:43:37](https://github.com/leanprover-community/mathlib/commit/5f51771)
feat(linear_algebra/bilinear_form): basis changing `bilin_form.to_matrix` ([#8775](https://github.com/leanprover-community/mathlib/pull/8775))
A few `simp` lemmas on bilinear forms.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.comp_id_id
- \+ *lemma* bilin_form.comp_id_left
- \+ *lemma* bilin_form.comp_id_right
- \+ *lemma* bilin_form.comp_left_id
- \+ *lemma* bilin_form.comp_right_id
- \+ *lemma* bilin_form.to_matrix_mul_basis_to_matrix



## [2021-08-21 21:43:36](https://github.com/leanprover-community/mathlib/commit/c44f19f)
feat(algebra/associated): simple lemmas and dot notation ([#8770](https://github.com/leanprover-community/mathlib/pull/8770))
Introduce
* `prime.exists_mem_finset_dvd`
* `prime.not_dvd_one`
Rename
* `exists_mem_multiset_dvd_of_prime` -> `prime.exists_mem_multiset_dvd`
* `left_dvd_or_dvd_right_of_dvd_prime_mul ` ->`prime.left_dvd_or_dvd_right_of_dvd_mul`
#### Estimated changes
Modified archive/imo/imo2001_q6.lean


Modified src/algebra/associated.lean
- \- *lemma* exists_mem_multiset_dvd_of_prime
- \- *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul
- \+ *lemma* prime.exists_mem_finset_dvd
- \+ *lemma* prime.exists_mem_multiset_dvd
- \+ *lemma* prime.exists_mem_multiset_map_dvd
- \+ *lemma* prime.left_dvd_or_dvd_right_of_dvd_mul
- \+/\- *lemma* prime.ne_one
- \+/\- *lemma* prime.ne_zero
- \+ *lemma* prime.not_dvd_one
- \+/\- *lemma* prime.not_unit

Modified src/ring_theory/unique_factorization_domain.lean




## [2021-08-21 19:52:15](https://github.com/leanprover-community/mathlib/commit/57e127a)
refactor(order/complete_lattice): use `is_empty` ([#8796](https://github.com/leanprover-community/mathlib/pull/8796))
* change `set.univ_eq_empty_iff` to use `is_empty`;
* rename `set.range_eq_empty` to `set.range_eq_empty_iff`;
* add new `set.range_eq_empty`, it assumes `[is_empty α]`;
* combine `supr_of_empty`, `supr_of_empty'`, and `supr_empty` into `supr_of_empty`, same for `infi`;
* replace `csupr_neg` with `csupr_of_empty` and `csupr_false`;
* adjust some proofs to use `casesI is_empty_of_nonempty α` instead of `by_cases h : nonempty α`.
#### Estimated changes
Modified src/data/matrix/notation.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* set.empty_ne_univ
- \+/\- *lemma* set.range_eq_empty
- \+ *lemma* set.range_eq_empty_iff
- \+/\- *lemma* set.univ_eq_empty_iff

Modified src/linear_algebra/affine_space/combination.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/order/complete_lattice.lean
- \- *theorem* infi_empty
- \+/\- *theorem* infi_of_empty'
- \+/\- *theorem* infi_of_empty
- \- *theorem* supr_empty
- \+/\- *theorem* supr_of_empty'
- \+/\- *theorem* supr_of_empty

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_false
- \- *lemma* csupr_neg
- \+ *lemma* csupr_of_empty

Modified src/order/filter/lift.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/uniform_space/basic.lean




## [2021-08-21 19:52:14](https://github.com/leanprover-community/mathlib/commit/8eba262)
feat(topology/metric_space/basic): union of balls `ball x n`, `n : ℕ` ([#8792](https://github.com/leanprover-community/mathlib/pull/8792))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.Union_ball_nat
- \+ *lemma* metric.Union_ball_nat_succ
- \+ *lemma* metric.Union_closed_ball_nat



## [2021-08-21 19:52:13](https://github.com/leanprover-community/mathlib/commit/9b60e0f)
feat(data/set/basic): add `pairwise_on_pair` ([#8789](https://github.com/leanprover-community/mathlib/pull/8789))
Add `set.pairwise_on_insert`, `set.pairwise_on_pair`, and `set.pairwise_on_pair_of_symmetric`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.pairwise_on_insert
- \+ *lemma* set.pairwise_on_pair
- \+ *lemma* set.pairwise_on_pair_of_symmetric



## [2021-08-21 19:52:12](https://github.com/leanprover-community/mathlib/commit/44b8138)
chore(topology/instances/ennreal): use `tactic.lift` ([#8788](https://github.com/leanprover-community/mathlib/pull/8788))
* use `tactic.lift` in two proofs;
* use the `order_dual` trick in one proof.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/instances/ennreal.lean




## [2021-08-21 19:52:11](https://github.com/leanprover-community/mathlib/commit/e00afed)
feat(topology/metric_space): turn `nonempty_ball` into an `iff` ([#8747](https://github.com/leanprover-community/mathlib/pull/8747))
* add `set.univ_pi_empty`;
* turn `metric.nonempty_ball` into an `iff`, mark it with `@[simp]`; add `metric.ball_eq_empty`
* do the same thing to `closed_ball`s;
* add primed versions of `metric.ball_pi` and `metric.closed_ball_pi`.
#### Estimated changes
Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.univ_pi_empty

Modified src/topology/metric_space/basic.lean
- \+ *lemma* ball_pi'
- \+ *lemma* closed_ball_pi'
- \+ *lemma* metric.ball_eq_empty
- \- *theorem* metric.ball_eq_empty_iff_nonpos
- \+ *lemma* metric.closed_ball_eq_empty
- \- *theorem* metric.closed_ball_eq_empty_iff_neg
- \+/\- *lemma* metric.nonempty_ball
- \+/\- *lemma* metric.nonempty_closed_ball



## [2021-08-21 18:46:32](https://github.com/leanprover-community/mathlib/commit/d31b85f)
feat(data/list/rotate): is_rotated_append ([#8780](https://github.com/leanprover-community/mathlib/pull/8780))
`list.append` is commutative with respect to `~r`.
#### Estimated changes
Modified src/data/list/rotate.lean
- \+ *lemma* list.is_rotated_append
- \+ *lemma* list.rotate_append_length_eq



## [2021-08-21 18:46:31](https://github.com/leanprover-community/mathlib/commit/0760b20)
feat(topology/metric_space): metrizable spaces ([#8759](https://github.com/leanprover-community/mathlib/pull/8759))
Define (pseudo)-metric space constructors for metrizable topological spaces.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.is_open_singleton_iff
- \+ *def* metric_space.of_metrizable
- \+ *def* pseudo_metric_space.of_metrizable
- \+ *def* uniform_space.core_of_dist



## [2021-08-21 17:31:49](https://github.com/leanprover-community/mathlib/commit/bafe207)
chore(linear_algebra): remove `→ₗ` notation where the ring is not specified ([#8778](https://github.com/leanprover-community/mathlib/pull/8778))
This PR removes the notation `M →ₗ N` for linear maps, where the ring is not specified. This is not used much in the library, and is needed for an upcoming refactor that will generalize linear maps to semilinear maps. See the discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps).
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/algebra/basic.lean
- \+/\- *def* alg_hom.to_linear_map
- \+/\- *def* algebra.lmul_left
- \+/\- *def* algebra.lmul_right

Modified src/algebra/module/linear_map.lean
- \+/\- *def* is_linear_map.mk'

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.congr_right

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/contraction.lean
- \+/\- *def* dual_tensor_hom

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* rank_comp_le2

Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *def* finsupp.restrict_dom

Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent.image_subtype

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* linear_map.compl₂
- \+/\- *def* linear_map.compr₂
- \+/\- *theorem* linear_map.lcomp_apply
- \+/\- *def* linear_map.llcomp
- \+/\- *def* linear_map.lsmul
- \+/\- *def* tensor_product.curry
- \+/\- *def* tensor_product.lift.equiv
- \+/\- *def* tensor_product.lift
- \+/\- *theorem* tensor_product.lift_compr₂
- \+/\- *theorem* tensor_product.lift_mk_compr₂
- \+/\- *def* tensor_product.map
- \+/\- *def* tensor_product.mk
- \+/\- *theorem* tensor_product.mk_compr₂_inj

Modified src/ring_theory/integral_closure.lean


Modified src/topology/algebra/module.lean




## [2021-08-21 15:59:17](https://github.com/leanprover-community/mathlib/commit/897e4ed)
feat(field_theory): finite fields exist ([#8692](https://github.com/leanprover-community/mathlib/pull/8692))
#### Estimated changes
Modified src/algebra/char_p/algebra.lean
- \+ *lemma* algebra.char_p_iff

Modified src/algebra/char_p/basic.lean
- \+ *lemma* char_p.neg_one_pow_char
- \+ *lemma* char_p.neg_one_pow_char_pow
- \+/\- *lemma* ring_hom.char_p_iff_char_p

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* commute.cast_int_left
- \+ *lemma* commute.cast_int_right

Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.one_lt_card

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.coeff_zero_eq_aeval_zero'

Added src/data/zmod/algebra.lean
- \+ *def* zmod.algebra'

Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/basic.lean
- \+ *lemma* card_eq_pow_finrank
- \+ *lemma* finite_field.X_pow_card_pow_sub_X_nat_degree_eq
- \+ *lemma* finite_field.X_pow_card_pow_sub_X_ne_zero
- \+ *lemma* finite_field.X_pow_card_sub_X_nat_degree_eq
- \+ *lemma* finite_field.X_pow_card_sub_X_ne_zero
- \+ *lemma* finite_field.pow_card_pow
- \+ *lemma* finite_field.roots_X_pow_card_sub_X
- \+ *lemma* zmod.pow_card_pow

Added src/field_theory/finite/galois_field.lean
- \+ *lemma* galois_field.card
- \+ *def* galois_field.equiv_zmod_p
- \+ *lemma* galois_field.finrank
- \+ *theorem* galois_field.splits_zmod_X_pow_sub_X
- \+ *def* galois_field
- \+ *lemma* galois_poly_separable

Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.exists_finset_of_splits
- \+ *lemma* polynomial.not_separable_zero

Modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* algebra.adjoin_univ



## [2021-08-21 12:26:51](https://github.com/leanprover-community/mathlib/commit/f72126b)
chore(algebra/gcd_monoid): move `algebra.gcd_monoid` to `algebra.gcd_monoid.basic` ([#8772](https://github.com/leanprover-community/mathlib/pull/8772))
#### Estimated changes
Renamed src/algebra/gcd_monoid.lean to src/algebra/gcd_monoid/basic.lean


Modified src/algebra/gcd_monoid/multiset.lean


Modified src/data/polynomial/field_division.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2021-08-21 05:42:59](https://github.com/leanprover-community/mathlib/commit/f36c98e)
chore(*): remove spurious whitespace ([#8769](https://github.com/leanprover-community/mathlib/pull/8769))
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Module/colimits.lean


Modified src/algebra/category/Mon/adjunctions.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/monoidal/center.lean


Modified src/category_theory/subobject/limits.lean


Modified src/control/bitraversable/instances.lean


Modified src/control/traversable/derive.lean


Modified src/control/uliftable.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/embedding.lean


Modified src/data/fin.lean


Modified src/data/fin_enum.lean


Modified src/data/finsupp/basic.lean


Modified src/data/holor.lean


Modified src/data/int/basic.lean


Modified src/data/list/chain.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/list/perm.lean


Modified src/data/list/sigma.lean


Modified src/data/mllist.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/bitwise.lean


Modified src/data/nat/digits.lean


Modified src/data/pfunctor/univariate/M.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/qpf/multivariate/constructions/cofix.lean


Modified src/data/qpf/multivariate/constructions/quot.lean


Modified src/data/real/sqrt.lean


Modified src/data/set/accumulate.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* set.diagonal_eq_range

Modified src/data/set/intervals/image_preimage.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/submonoid.lean


Modified src/dynamics/flow.lean


Modified src/dynamics/omega_limit.lean


Modified src/field_theory/perfect_closure.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/semidirect_product.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/multilinear.lean


Modified src/logic/relation.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/meta/expr_lens.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/order/bounded_lattice.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/well_founded_set.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/set_theory/pgame.lean


Modified src/tactic/converter/apply_congr.lean


Modified src/tactic/core.lean


Modified src/tactic/dependencies.lean


Modified src/tactic/doc_commands.lean


Modified src/tactic/ext.lean


Modified src/tactic/generalizes.lean


Modified src/tactic/induction.lean


Modified src/tactic/interactive.lean


Modified src/tactic/itauto.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/protected.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/simp_command.lean


Modified src/tactic/unify_equations.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/basic.lean


Modified src/topology/compacts.lean
- \+/\- *def* topological_space.positive_compacts:

Modified src/topology/connected.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/holder.lean


Modified src/topology/order.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean


Modified src/topology/sheaves/sheaf_of_functions.lean


Modified src/topology/sheaves/stalks.lean


Modified src/topology/subset_properties.lean


Modified test/conv/apply_congr.lean


Modified test/equiv_rw.lean


Modified test/generalizes.lean


Modified test/induction.lean


Modified test/library_search/basic.lean


Modified test/monotonicity.lean




## [2021-08-20 21:38:03](https://github.com/leanprover-community/mathlib/commit/d869256)
refactor(data/nat/lattice): move code, add lemmas ([#8708](https://github.com/leanprover-community/mathlib/pull/8708))
* move `nat.conditionally_complete_linear_order_with_bot` and `enat.complete_linear_order` to a new file `data.nat.lattice`;
* add a few lemmas (`nat.supr_lt_succ` etc), move `set.bUnion_lt_succ` to the same file;
* use `galois_insertion.lift_complete_lattice` to define `enat.complete_linear_order`.
#### Estimated changes
Added src/data/nat/lattice.lean
- \+ *lemma* nat.Inf_def
- \+ *lemma* nat.Inf_eq_zero
- \+ *lemma* nat.Inf_mem
- \+ *lemma* nat.Inf_upward_closed_eq_succ_iff
- \+ *lemma* nat.Sup_def
- \+ *lemma* nat.eq_Ici_of_nonempty_of_upward_closed
- \+ *lemma* nat.infi_lt_succ'
- \+ *lemma* nat.infi_lt_succ
- \+ *lemma* nat.nonempty_of_Inf_eq_succ
- \+ *lemma* nat.nonempty_of_pos_Inf
- \+ *lemma* nat.not_mem_of_lt_Inf
- \+ *lemma* nat.supr_lt_succ'
- \+ *lemma* nat.supr_lt_succ
- \+ *lemma* set.bInter_lt_succ'
- \+ *lemma* set.bInter_lt_succ
- \+ *lemma* set.bUnion_lt_succ'
- \+ *lemma* set.bUnion_lt_succ

Modified src/data/set/lattice.lean
- \- *lemma* set.bInter_lt_succ
- \- *lemma* set.bUnion_lt_succ

Modified src/measure_theory/measure/outer_measure.lean


Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* nat.Inf_def
- \- *lemma* nat.Inf_eq_zero
- \- *lemma* nat.Inf_mem
- \- *lemma* nat.Inf_upward_closed_eq_succ_iff
- \- *lemma* nat.Sup_def
- \- *lemma* nat.eq_Ici_of_nonempty_of_upward_closed
- \- *lemma* nat.nonempty_of_Inf_eq_succ
- \- *lemma* nat.nonempty_of_pos_Inf
- \- *lemma* nat.not_mem_of_lt_Inf

Modified src/order/filter/partial.lean


Modified src/order/order_iso_nat.lean




## [2021-08-20 14:42:08](https://github.com/leanprover-community/mathlib/commit/45e7eb8)
feat(dynamics/fixed_points): simple lemmas ([#8768](https://github.com/leanprover-community/mathlib/pull/8768))
#### Estimated changes
Modified src/dynamics/fixed_points/basic.lean
- \+ *lemma* function.injective.is_fixed_pt_apply_iff
- \+ *lemma* function.mem_fixed_points_iff



## [2021-08-20 14:42:07](https://github.com/leanprover-community/mathlib/commit/6ae3747)
feat(algebra/big_operators): the product over `{x // x ∈ m}` is the product over `m.to_finset` ([#8742](https://github.com/leanprover-community/mathlib/pull/8742))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_mem_multiset



## [2021-08-20 14:42:06](https://github.com/leanprover-community/mathlib/commit/d62a461)
feat(linear_algebra/determinant): `det (M ⬝ N) = det (N ⬝ M)` if `M` is invertible ([#8720](https://github.com/leanprover-community/mathlib/pull/8720))
If `M` is a square or invertible matrix, then `det (M ⬝ N) = det (N ⬝ M)`. This is basically just using `mul_comm` on `det M * det N`, except for some tricky rewriting to handle the invertible case.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_comm'
- \+ *lemma* matrix.det_comm
- \+/\- *lemma* matrix.det_conj
- \+/\- *def* matrix.index_equiv_of_inv



## [2021-08-20 14:42:05](https://github.com/leanprover-community/mathlib/commit/7ccf463)
feat(algebra): is_smul_regular for `pi`, `finsupp`, `matrix`, `polynomial` ([#8716](https://github.com/leanprover-community/mathlib/pull/8716))
Also provide same lemma for finsupp, and specialize it for matrices and polynomials
Inspired by 
https://github.com/leanprover-community/mathlib/pull/8681#discussion_r689320217
https://github.com/leanprover-community/mathlib/pull/8679#discussion_r689545373
#### Estimated changes
Modified src/algebra/module/pi.lean
- \+ *lemma* is_smul_regular.pi

Modified src/algebra/regular/smul.lean
- \+ *lemma* is_left_regular.is_smul_regular
- \+ *lemma* is_left_regular_iff
- \+ *lemma* is_right_regular.is_smul_regular
- \+ *lemma* is_right_regular_iff
- \+ *lemma* is_smul_regular.is_left_regular
- \- *lemma* is_smul_regular.is_left_regular_iff
- \+ *lemma* is_smul_regular.is_right_regular

Modified src/data/finsupp/basic.lean
- \+ *lemma* is_smul_regular.finsupp

Modified src/data/matrix/basic.lean
- \+ *lemma* is_left_regular.matrix
- \+ *lemma* is_smul_regular.matrix

Modified src/data/polynomial/basic.lean
- \+ *lemma* is_smul_regular.polynomial



## [2021-08-20 14:42:03](https://github.com/leanprover-community/mathlib/commit/aee7bad)
feat(data/list/rotate): cyclic_permutations ([#8678](https://github.com/leanprover-community/mathlib/pull/8678))
For `l ~ l'` we have `list.permutations`. We provide the list of cyclic permutations of `l` such that all members are `l ~r l'`. This relationship is proven, as well as the induced `nodup` of the list of cyclic permutants.
This also simplifies the `cycle.list` definition, and removed the requirement for decidable equality in it.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.length_inits
- \+ *lemma* list.length_tails
- \+ *lemma* list.nth_le_inits
- \+ *lemma* list.nth_le_tails

Modified src/data/list/cycle.lean


Modified src/data/list/rotate.lean
- \+ *def* list.cyclic_permutations
- \+ *lemma* list.cyclic_permutations_cons
- \+ *lemma* list.cyclic_permutations_eq_nil_iff
- \+ *lemma* list.cyclic_permutations_eq_singleton_iff
- \+ *lemma* list.cyclic_permutations_nil
- \+ *lemma* list.cyclic_permutations_of_ne_nil
- \+ *lemma* list.cyclic_permutations_rotate
- \+ *lemma* list.is_rotated.cyclic_permutations
- \+ *lemma* list.is_rotated_cyclic_permutations_iff
- \+/\- *lemma* list.is_rotated_nil_iff'
- \+ *lemma* list.is_rotated_singleton_iff'
- \+ *lemma* list.is_rotated_singleton_iff
- \+ *lemma* list.length_cyclic_permutations_cons
- \+ *lemma* list.length_cyclic_permutations_of_ne_nil
- \+ *lemma* list.length_mem_cyclic_permutations
- \+ *lemma* list.mem_cyclic_permutations_iff
- \+ *lemma* list.mem_cyclic_permutations_self
- \+ *lemma* list.nil_eq_rotate_iff
- \+ *lemma* list.nodup.cyclic_permutations
- \+ *lemma* list.nodup.rotate_congr
- \+ *theorem* list.nodup.rotate_eq_self_iff
- \+ *lemma* list.nth_le_cyclic_permutations
- \+ *lemma* list.rotate_eq_singleton_iff
- \+ *lemma* list.singleton_eq_rotate_iff



## [2021-08-20 14:42:02](https://github.com/leanprover-community/mathlib/commit/7e8432d)
chore(algebra/group_power/lemmas): Lemmas about gsmul ([#8618](https://github.com/leanprover-community/mathlib/pull/8618))
This restates some existing lemmas as `monotone` and `strict_monotone`, and provides new lemmas about the right argument of gsmul:
* `gsmul_le_gsmul'`
* `gsmul_lt_gsmul'`
* `gsmul_le_gsmul_iff'`
* `gsmul_lt_gsmul_iff'`
This also removes an unnecessary `linear_order` assumption from `gsmul_le_gsmul_iff` and `gsmul_lt_gsmul_iff`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* gsmul_eq_gsmul_iff'
- \+ *theorem* gsmul_le_gsmul'
- \+ *theorem* gsmul_le_gsmul_iff'
- \+ *theorem* gsmul_lt_gsmul'
- \+ *theorem* gsmul_lt_gsmul_iff'
- \+ *theorem* gsmul_mono_left
- \+ *lemma* gsmul_mono_right
- \+ *lemma* gsmul_right_inj
- \+ *lemma* gsmul_right_injective
- \+ *theorem* gsmul_strict_mono_left
- \+ *lemma* gsmul_strict_mono_right



## [2021-08-20 14:42:00](https://github.com/leanprover-community/mathlib/commit/7265a4e)
feat(linear_algebra/dimension): generalize inequalities and invariance of dimension to arbitrary rings ([#8343](https://github.com/leanprover-community/mathlib/pull/8343))
We implement some of the results of [_Les familles libres maximales d'un module ont-elles le meme cardinal?_](http://www.numdam.org/article/PSMIR_1973___4_A4_0.pdf).
We also generalize many theorems which were previously proved only for vector spaces, but are true for modules over arbitrary rings or rings satisfying the (strong) rank condition or have invariant basis number. (These typically need entire new proofs, as the original proofs e.g. used rank-nullity.)
The main new results are:
* `basis_fintype_of_finite_spans`: 
  Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
* `union_support_maximal_linear_independent_eq_range_basis`: 
  Over any ring `R`, if `b` is a basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
* `infinite_basis_le_maximal_linear_independent`:
  Over any ring `R`, if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.
* `mk_eq_mk_of_basis`:
  We generalize the invariance of dimension theorem to any ring with the invariant basis number property.
* `basis.le_span`:
  We generalize this statement (the size of a basis is bounded by the size of any spanning set)
  to any ring satisfying the rank condition.
* `linear_independent_le_span`:
  If `R` satisfies the strong rank condition,
  then for any linearly independent family `v : ι → M`
  and any finite spanning set `w : set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linear_independent_le_basis`:
  Over any ring `R` satisfying the strong rank condition,
  if `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.
  
There is a naming discrepancy: most of the theorem names refer to `dim`,
even though the definition is of `module.rank`.
This reflects that `module.rank` was originally called `dim`, and only defined for vector spaces.
I would prefer to address this in a separate PR (note this discrepancy wasn't introduced in this PR).
#### Estimated changes
Modified docs/references.bib


Modified src/data/equiv/basic.lean


Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.equiv_fun_on_fintype_symm_coe

Modified src/data/fintype/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.ne_univ_iff_exists_not_mem
- \+ *lemma* set.not_subset_iff_exists_mem_not_mem

Modified src/data/set/finite.lean
- \+ *lemma* set.not_infinite

Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/fixed.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.maximal
- \+ *lemma* basis.mem_span_repr_support

Modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.le_span''
- \+/\- *theorem* basis.le_span
- \+/\- *theorem* basis.mk_eq_dim''
- \+/\- *theorem* basis.mk_eq_dim
- \+/\- *theorem* basis.mk_range_eq_dim
- \+ *def* basis_fintype_of_finite_spans
- \+ *lemma* basis_le_span'
- \+/\- *lemma* dim_bot
- \+/\- *lemma* dim_eq_of_injective
- \- *lemma* dim_le_of_injective
- \+/\- *lemma* dim_le_of_submodule
- \- *lemma* dim_le_of_surjective
- \+/\- *lemma* dim_map_le
- \- *lemma* dim_of_field
- \+ *lemma* dim_of_ring
- \+ *lemma* dim_punit
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_set
- \+/\- *lemma* dim_submodule_le
- \+/\- *lemma* dim_top
- \+ *lemma* infinite_basis_le_maximal_linear_independent'
- \+ *lemma* infinite_basis_le_maximal_linear_independent
- \+/\- *theorem* linear_equiv.dim_eq
- \- *theorem* linear_equiv.dim_eq_lift
- \+/\- *theorem* linear_equiv.lift_dim_eq
- \+ *def* linear_independent_fintype_of_le_span_fintype
- \+ *lemma* linear_independent_le_basis
- \- *lemma* linear_independent_le_dim
- \+ *lemma* linear_independent_le_infinite_basis
- \+ *lemma* linear_independent_le_span'
- \+ *lemma* linear_independent_le_span
- \+ *lemma* linear_independent_le_span_aux'
- \+ *theorem* linear_map.dim_le_of_injective
- \+ *lemma* linear_map.dim_le_of_surjective
- \+ *theorem* linear_map.lift_dim_le_of_injective
- \+ *lemma* maximal_linear_independent_eq_infinite_basis
- \+/\- *theorem* mk_eq_mk_of_basis'
- \+/\- *theorem* mk_eq_mk_of_basis
- \+ *lemma* union_support_maximal_linear_independent_eq_range_basis
- \+/\- *theorem* {m}
- \- *theorem* {u₁}

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean
- \+ *theorem* finsupp.apply_total
- \+ *lemma* finsupp.total_option
- \+ *lemma* finsupp.total_total
- \+/\- *def* span.repr

Modified src/linear_algebra/linear_independent.lean
- \+ *def* linear_independent.maximal
- \+ *lemma* linear_independent.maximal_iff
- \+ *lemma* linear_independent_bounded_of_finset_linear_independent_bounded
- \+ *lemma* linear_independent_finset_map_embedding_subtype

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.lift_mk_le'
- \+ *lemma* cardinal.lift_sup_le_lift_sup'



## [2021-08-20 14:41:58](https://github.com/leanprover-community/mathlib/commit/15b1461)
feat(archive/imo): IMO 2006 Q3 ([#8052](https://github.com/leanprover-community/mathlib/pull/8052))
Formalization of IMO 2006/3
#### Estimated changes
Added archive/imo/imo2006_q3.lean
- \+ *lemma* four_pow_four_pos
- \+ *theorem* imo2006_q3
- \+ *lemma* lhs_identity
- \+ *lemma* lhs_ineq
- \+ *lemma* mid_ineq
- \+ *theorem* proof₁
- \+ *theorem* proof₂
- \+ *lemma* rhs_ineq
- \+ *theorem* subst_proof₁
- \+ *theorem* subst_wlog
- \+ *lemma* zero_lt_32

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_nonneg_of_three



## [2021-08-19 16:19:58](https://github.com/leanprover-community/mathlib/commit/5dc8bc1)
feat(linear_algebra/clifford_algebra/equivs): the equivalences preserve conjugation ([#8739](https://github.com/leanprover-community/mathlib/pull/8739))
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* quaternion_algebra.conj_mk

Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+ *def* clifford_algebra_complex.of_complex
- \+ *lemma* clifford_algebra_complex.of_complex_I
- \+ *lemma* clifford_algebra_complex.of_complex_comp_to_complex
- \+ *lemma* clifford_algebra_complex.of_complex_conj
- \+ *lemma* clifford_algebra_complex.of_complex_to_complex
- \+ *lemma* clifford_algebra_complex.reverse_apply
- \+ *lemma* clifford_algebra_complex.reverse_eq_id
- \+ *lemma* clifford_algebra_complex.to_complex_comp_of_complex
- \+ *lemma* clifford_algebra_complex.to_complex_involute
- \+ *lemma* clifford_algebra_complex.to_complex_of_complex
- \- *lemma* clifford_algebra_quaternion.of_quaternion_apply
- \+ *lemma* clifford_algebra_quaternion.of_quaternion_conj
- \+ *lemma* clifford_algebra_quaternion.of_quaternion_mk
- \+ *lemma* clifford_algebra_quaternion.of_quaternion_to_quaternion
- \+ *lemma* clifford_algebra_quaternion.to_quaternion_involute_reverse
- \+ *lemma* clifford_algebra_quaternion.to_quaternion_of_quaternion
- \+ *lemma* clifford_algebra_ring.involute_eq_id
- \+ *lemma* clifford_algebra_ring.reverse_apply
- \+ *lemma* clifford_algebra_ring.reverse_eq_id



## [2021-08-19 14:31:16](https://github.com/leanprover-community/mathlib/commit/dd5e779)
fix(linear_algebra/basic): fix incorrect namespaces ([#8757](https://github.com/leanprover-community/mathlib/pull/8757))
Previously there were names in the `linear_map` namespace which were about `linear_equiv`s.
This moves:
* `linear_map.fun_congr_left` to `linear_equiv.fun_congr_left`
* `linear_map.automorphism_group` to `linear_equiv.automorphism_group`
* `linear_map.automorphism_group.to_linear_map_monoid_hom` to `linear_equiv.automorphism_group.to_linear_map_monoid_hom`
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* linear_equiv.automorphism_group.to_linear_map_monoid_hom
- \+ *def* linear_equiv.fun_congr_left
- \+ *theorem* linear_equiv.fun_congr_left_apply
- \+ *theorem* linear_equiv.fun_congr_left_comp
- \+ *theorem* linear_equiv.fun_congr_left_id
- \+ *lemma* linear_equiv.fun_congr_left_symm
- \- *def* linear_map.automorphism_group.to_linear_map_monoid_hom
- \- *def* linear_map.fun_congr_left
- \- *theorem* linear_map.fun_congr_left_apply
- \- *theorem* linear_map.fun_congr_left_comp
- \- *theorem* linear_map.fun_congr_left_id
- \- *lemma* linear_map.fun_congr_left_symm

Modified src/linear_algebra/invariant_basis_number.lean




## [2021-08-19 14:31:14](https://github.com/leanprover-community/mathlib/commit/d172085)
docs(overview): add weak-* topology ([#8755](https://github.com/leanprover-community/mathlib/pull/8755))
#### Estimated changes
Modified docs/overview.yaml




## [2021-08-19 14:31:13](https://github.com/leanprover-community/mathlib/commit/86fccaa)
feat(measure_theory/strongly_measurable): define strongly measurable functions ([#8623](https://github.com/leanprover-community/mathlib/pull/8623))
A function `f` is said to be strongly measurable with respect to a measure `μ` if `f` is the sequential limit of simple functions whose support has finite measure.
Functions in `Lp` for `0 < p < ∞` are strongly measurable. If the measure is sigma-finite, measurable and strongly measurable are equivalent.
The main property of strongly measurable functions is `strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that `f` is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some results for those functions as if the measure was sigma-finite.
I will use this to prove properties of the form `f =ᵐ[μ] g` for `Lp` functions.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_of_subsingleton

Modified src/measure_theory/function/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top_of_integrable
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top_of_mem_ℒp

Added src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measurable.strongly_measurable
- \+ *lemma* measure_theory.Lp.fin_strongly_measurable
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.ae_eq_zero_compl
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.exists_set_sigma_finite
- \+ *def* measure_theory.ae_fin_strongly_measurable.sigma_finite_set
- \+ *def* measure_theory.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.ae_fin_strongly_measurable_iff_ae_measurable
- \+ *lemma* measure_theory.fin_strongly_measurable.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.fin_strongly_measurable.exists_set_sigma_finite
- \+ *def* measure_theory.fin_strongly_measurable
- \+ *lemma* measure_theory.fin_strongly_measurable_iff_measurable
- \+ *lemma* measure_theory.integrable.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.mem_ℒp.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.mem_ℒp.fin_strongly_measurable_of_measurable
- \+ *def* measure_theory.strongly_measurable.approx
- \+ *lemma* measure_theory.strongly_measurable.fin_strongly_measurable_of_set_sigma_finite
- \+ *def* measure_theory.strongly_measurable
- \+ *lemma* measure_theory.strongly_measurable_iff_measurable
- \+ *lemma* measure_theory.subsingleton.strongly_measurable

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.measurable_set_support



## [2021-08-19 12:44:51](https://github.com/leanprover-community/mathlib/commit/802859f)
chore(algebra/big_operators): weaken assumption for multiset.exists_smul_of_dvd_count ([#8758](https://github.com/leanprover-community/mathlib/pull/8758))
This is slightly more convenient than doing a case split on `a ∈ s` in the caller.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *theorem* multiset.exists_smul_of_dvd_count

Modified src/ring_theory/unique_factorization_domain.lean




## [2021-08-19 12:44:50](https://github.com/leanprover-community/mathlib/commit/1efa367)
feat(group_action/defs): add missing comp_hom smul instances ([#8707](https://github.com/leanprover-community/mathlib/pull/8707))
This adds missing `smul_comm_class` and `is_scalar_tower` instances about the `comp_hom` definitions.
To resolve unification issues in finding these instances caused by the reducibility of the `comp_hom` defs, this introduces a semireducible def `has_scalar.comp.smul`.
#### Estimated changes
Modified src/algebra/module/basic.lean


Modified src/algebra/module/linear_map.lean
- \+ *def* module.comp_hom.to_linear_equiv
- \+ *def* module.comp_hom.to_linear_map

Modified src/group_theory/group_action/defs.lean
- \+ *def* has_scalar.comp.smul
- \+ *def* has_scalar.comp



## [2021-08-19 12:44:49](https://github.com/leanprover-community/mathlib/commit/4113db5)
feat(ring_theory): the trace of an integral element is integral ([#8702](https://github.com/leanprover-community/mathlib/pull/8702))
This PR uses `trace_gen_eq_sum_roots` and `trace_trace` to show the trace of an integral element `x : L` over `K` is a multiple of the sum of all conjugates of `x`, and concludes that the trace of `x` is integral.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval₂_dvd
- \+ *lemma* polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero

Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.aeval_of_is_scalar_tower

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral.gsmul
- \+ *lemma* is_integral.multiset_prod
- \+ *lemma* is_integral.multiset_sum
- \+ *lemma* is_integral.nsmul
- \+ *lemma* is_integral.pow
- \+ *lemma* is_integral.prod
- \+ *lemma* is_integral.sum

Modified src/ring_theory/trace.lean
- \+ *lemma* algebra.is_integral_trace
- \- *lemma* algebra.trace_gen_eq_sum_roots
- \+ *lemma* intermediate_field.adjoin_simple.trace_gen_eq_sum_roots
- \+ *lemma* intermediate_field.adjoin_simple.trace_gen_eq_zero
- \+ *lemma* power_basis.trace_gen_eq_sum_roots
- \+ *lemma* trace_eq_sum_roots



## [2021-08-19 11:02:14](https://github.com/leanprover-community/mathlib/commit/159e34e)
Revert "feat(field_theory/intermediate_field): generalize `algebra` instances"
OOPS!
This reverts commit 4b525bf25aa33201bd26942a938b84b2df71f175.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean




## [2021-08-19 11:01:55](https://github.com/leanprover-community/mathlib/commit/4b525bf)
feat(field_theory/intermediate_field): generalize `algebra` instances
The `algebra` and `is_scalar_tower` instances for `intermediate_field` are (again) as general as those for `subalgebra`.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean




## [2021-08-19 09:57:42](https://github.com/leanprover-community/mathlib/commit/902d3ac)
chore(tactic/rewrite_search): reuse rw_rules_p parser ([#8752](https://github.com/leanprover-community/mathlib/pull/8752))
The parser defined here is the same as `rw_rules_p`, so use it.
#### Estimated changes
Modified src/tactic/rewrite_search/frontend.lean




## [2021-08-19 08:28:44](https://github.com/leanprover-community/mathlib/commit/28a360a)
feat(analysis/calculus/deriv): prove `deriv_inv` at `x = 0` as well ([#8748](https://github.com/leanprover-community/mathlib/pull/8748))
* turn `differentiable_at_inv` and `differentiable_at_fpow` into `iff` lemmas;
* slightly weaker assumptions for `differentiable_within_at_fpow` etc;
* prove `deriv_inv` and `fderiv_inv` for all `x`;
* prove formulas for iterated derivs of `x⁻¹` and `x ^ m`, `m : int`;
* push `coe` in these formulas;
#### Estimated changes
Modified src/algebra/big_operators/ring.lean
- \+ *lemma* finset.prod_range_cast_nat_sub

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_fpow'
- \+/\- *lemma* deriv_fpow
- \+ *lemma* deriv_inv''
- \+/\- *lemma* deriv_inv'
- \+/\- *lemma* deriv_inv
- \+/\- *lemma* deriv_within_fpow
- \+/\- *lemma* differentiable_at_fpow
- \+/\- *lemma* differentiable_at_inv
- \+/\- *lemma* differentiable_on_fpow
- \+/\- *lemma* differentiable_within_at_fpow
- \+/\- *lemma* fderiv_inv
- \+/\- *lemma* has_deriv_at_fpow
- \+/\- *theorem* has_deriv_within_at_fpow
- \+/\- *lemma* has_strict_deriv_at_fpow
- \+ *lemma* iter_deriv_fpow'
- \+/\- *lemma* iter_deriv_fpow
- \+ *lemma* iter_deriv_inv'
- \+ *lemma* iter_deriv_inv
- \+/\- *lemma* iter_deriv_pow'
- \+/\- *lemma* iter_deriv_pow

Modified src/analysis/convex/specific_functions.lean




## [2021-08-19 06:51:43](https://github.com/leanprover-community/mathlib/commit/1c60e61)
feat(topology/metric_space/basic): `emetric.ball x ∞ = univ` ([#8745](https://github.com/leanprover-community/mathlib/pull/8745))
* add `@[simp]` to `metric.emetric_ball`,
  `metric.emetric_ball_nnreal`, and
  `metric.emetric_closed_ball_nnreal`;
* add `@[simp]` lemmas `metric.emetric_ball_top` and
  `emetric.closed_ball_top`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.emetric_ball
- \+/\- *lemma* metric.emetric_ball_nnreal
- \+ *lemma* metric.emetric_ball_top
- \+/\- *lemma* metric.emetric_closed_ball_nnreal

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.closed_ball_top



## [2021-08-19 03:46:27](https://github.com/leanprover-community/mathlib/commit/0e0a240)
chore(scripts): update nolints.txt ([#8754](https://github.com/leanprover-community/mathlib/pull/8754))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-19 01:51:34](https://github.com/leanprover-community/mathlib/commit/ee3f8b8)
chore(order/complete_lattice): golf some proofs ([#8746](https://github.com/leanprover-community/mathlib/pull/8746))
#### Estimated changes
Modified src/order/complete_lattice.lean




## [2021-08-18 23:53:44](https://github.com/leanprover-community/mathlib/commit/8455433)
doc(tactic/simps): typo ([#8751](https://github.com/leanprover-community/mathlib/pull/8751))
Missed this review comment in [#8729](https://github.com/leanprover-community/mathlib/pull/8729)
#### Estimated changes
Modified src/tactic/simps.lean




## [2021-08-18 23:53:43](https://github.com/leanprover-community/mathlib/commit/6fe5b55)
feat(algebra/algebra): `alg_{hom,equiv}.restrict_scalars` is injective ([#8743](https://github.com/leanprover-community/mathlib/pull/8743))
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* alg_equiv.restrict_scalars_injective
- \+ *lemma* alg_hom.restrict_scalars_injective



## [2021-08-18 21:30:49](https://github.com/leanprover-community/mathlib/commit/e0bf9a1)
doc({topology.algebra.weak_dual_topology, analysis.normed_space.weak_dual}): fix docstrings ([#8710](https://github.com/leanprover-community/mathlib/pull/8710))
Fixing docstrings from the recently merged PR [#8598](https://github.com/leanprover-community/mathlib/pull/8598) on weak-* topology.
#### Estimated changes
Modified src/analysis/normed_space/weak_dual.lean


Modified src/topology/algebra/weak_dual_topology.lean




## [2021-08-18 21:30:47](https://github.com/leanprover-community/mathlib/commit/23cf025)
feat(algebra/ordered_sub): define truncated subtraction in general ([#8503](https://github.com/leanprover-community/mathlib/pull/8503))
* Define and prove properties of truncated subtraction in general
* We currently only instantiate it for `nat`. The other types (`multiset`, `finsupp`, `nnreal`, `ennreal`, ...) will be in future PRs.
Todo in future PRs:
* Provide `has_ordered_sub` instances for all specific cases
* Remove the lemmas specific to each individual type
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* lt_iff_exists_mul
- \+/\- *lemma* min_mul_distrib'
- \+/\- *lemma* min_mul_distrib
- \+ *lemma* min_one
- \+ *lemma* one_min
- \+/\- *lemma* with_zero.lt_of_mul_lt_mul_left

Modified src/algebra/ordered_monoid_lemmas.lean
- \+ *lemma* contravariant.mul_le_cancellable
- \+ *def* mul_le_cancellable
- \+ *lemma* mul_left_cancel''
- \+ *lemma* mul_right_cancel''

Added src/algebra/ordered_sub.lean
- \+ *lemma* add_le_add_add_sub
- \+ *lemma* add_le_of_le_sub_left_of_le
- \+ *lemma* add_le_of_le_sub_right_of_le
- \+ *lemma* add_sub_add_eq_sub_left'
- \+ *lemma* add_sub_add_right_eq_sub'
- \+ *lemma* add_sub_assoc_of_le
- \+ *lemma* add_sub_cancel_iff_le
- \+ *lemma* add_sub_cancel_left
- \+ *lemma* add_sub_cancel_of_le
- \+ *lemma* add_sub_cancel_right
- \+ *lemma* add_sub_eq_max
- \+ *lemma* add_sub_le_assoc
- \+ *lemma* add_sub_le_left
- \+ *lemma* add_sub_le_right
- \+ *lemma* add_sub_sub_cancel'
- \+ *lemma* eq_sub_iff_add_eq_of_le
- \+ *lemma* eq_sub_of_add_eq''
- \+ *lemma* le_add_sub'
- \+ *lemma* le_add_sub
- \+ *lemma* le_add_sub_swap
- \+ *lemma* le_sub_add
- \+ *lemma* le_sub_add_add
- \+ *lemma* le_sub_iff_le_sub
- \+ *lemma* le_sub_iff_left
- \+ *lemma* le_sub_iff_right
- \+ *lemma* le_sub_of_add_le_left'
- \+ *lemma* le_sub_of_add_le_right'
- \+ *lemma* lt_add_of_sub_lt_left'
- \+ *lemma* lt_add_of_sub_lt_right'
- \+ *lemma* lt_of_sub_lt_sub_left
- \+ *lemma* lt_of_sub_lt_sub_left_of_le
- \+ *lemma* lt_of_sub_lt_sub_right
- \+ *lemma* lt_of_sub_lt_sub_right_of_le
- \+ *lemma* lt_sub_iff_left
- \+ *lemma* lt_sub_iff_left_of_le
- \+ *lemma* lt_sub_iff_lt_sub
- \+ *lemma* lt_sub_iff_right
- \+ *lemma* lt_sub_iff_right_of_le
- \+ *lemma* lt_sub_of_add_lt_left
- \+ *lemma* lt_sub_of_add_lt_right
- \+ *lemma* sub_add_cancel_iff_le
- \+ *lemma* sub_add_cancel_of_le
- \+ *lemma* sub_add_eq_add_sub'
- \+ *lemma* sub_add_eq_max
- \+ *lemma* sub_add_eq_sub_sub'
- \+ *lemma* sub_add_eq_sub_sub_swap'
- \+ *lemma* sub_add_min
- \+ *lemma* sub_add_sub_cancel''
- \+ *lemma* sub_eq_iff_eq_add_of_le
- \+ *lemma* sub_eq_of_eq_add''
- \+ *lemma* sub_eq_sub_min
- \+ *lemma* sub_eq_zero_iff_le
- \+ *lemma* sub_inj_left
- \+ *lemma* sub_inj_right
- \+ *lemma* sub_le_iff_left
- \+ *lemma* sub_le_iff_right
- \+ *lemma* sub_le_iff_sub_le
- \+ *lemma* sub_le_self'
- \+ *lemma* sub_le_sub'
- \+ *lemma* sub_le_sub_add_sub
- \+ *lemma* sub_le_sub_iff_left'
- \+ *lemma* sub_le_sub_iff_right'
- \+ *lemma* sub_le_sub_left'
- \+ *lemma* sub_le_sub_right'
- \+ *lemma* sub_left_inj'
- \+ *lemma* sub_lt_iff_left
- \+ *lemma* sub_lt_iff_right
- \+ *lemma* sub_lt_iff_sub_lt
- \+ *lemma* sub_lt_self'
- \+ *lemma* sub_lt_self_iff'
- \+ *lemma* sub_lt_sub_iff_left_of_le
- \+ *lemma* sub_lt_sub_iff_left_of_le_of_le
- \+ *lemma* sub_lt_sub_iff_right'
- \+ *lemma* sub_lt_sub_right_of_le
- \+ *lemma* sub_min
- \+ *lemma* sub_pos_iff_lt
- \+ *lemma* sub_pos_iff_not_le
- \+ *lemma* sub_pos_of_lt'
- \+ *lemma* sub_right_comm'
- \+ *lemma* sub_right_inj'
- \+ *lemma* sub_self'
- \+ *lemma* sub_self_add
- \+ *lemma* sub_sub'
- \+ *lemma* sub_sub_assoc
- \+ *lemma* sub_sub_cancel_of_le
- \+ *lemma* sub_sub_le
- \+ *lemma* sub_sub_sub_cancel_right'
- \+ *lemma* sub_sub_sub_le_sub
- \+ *lemma* sub_zero'
- \+ *lemma* zero_sub'

Modified src/algebra/regular/basic.lean


Modified src/data/nat/basic.lean
- \- *lemma* nat.add_sub_cancel_right
- \- *theorem* nat.add_sub_eq_max
- \- *theorem* nat.sub_add_eq_max
- \- *theorem* nat.sub_add_min
- \- *theorem* nat.sub_min

Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.sub_eq_zero_iff_le

Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.sub_eq_zero_iff_le

Modified src/set_theory/ordinal_notation.lean




## [2021-08-18 18:52:52](https://github.com/leanprover-community/mathlib/commit/0860c41)
feat(data/nat/pairing): add some `nat.pair` lemmas ([#8740](https://github.com/leanprover-community/mathlib/pull/8740))
#### Estimated changes
Modified src/data/nat/pairing.lean
- \+ *lemma* infi_unpair
- \+ *lemma* set.Inter_unpair
- \+ *lemma* set.Union_unpair
- \+ *lemma* supr_unpair



## [2021-08-18 18:52:51](https://github.com/leanprover-community/mathlib/commit/e6fda2a)
fix(transform_decl): fix namespace bug ([#8733](https://github.com/leanprover-community/mathlib/pull/8733))
* The problem was that when writing `@[to_additive] def foo ...` every declaration used in `foo` in namespace `foo` would be additivized without changing the last part of the name. This behavior was intended to translate automatically generated declarations like `foo._proof_1`. However, if `foo` contains a non-internal declaration `foo.bar` and `add_foo.bar` didn't exist yet, it would also create a declaration `add_foo.bar` additivizing `foo.bar`.
* This PR changes the behavior: if `foo.bar` has the `@[to_additive]` attribute (potentially with a custom additive name), then we won't create a second additive version of `foo.bar`, and succeed normally. However, if `foo.bar` doesn't have the `@[to_additive]` attribute, then we fail with a nice error message. We could potentially support this behavior, but it doesn't seem that worthwhile and it would require changing a couple low-level definitions that `@[to_additive]` uses (e.g. by replacing `name.map_prefix` so that it only maps prefixes if the name is `internal`).
* So far this didn't happen in the library yet. There are currently 5 non-internal declarations `foo.bar` that are used in `foo` where `foo` has the `@[to_additive]` attribute, but all of these declarations were already had an additive version `add_foo.bar`.
* These 5 declarations are `[Mon.has_limits.limit_cone, Mon.has_limits.limit_cone_is_limit, con_gen.rel, magma.free_semigroup.r, localization.r]`
* This fixes the error in [#8707](https://github.com/leanprover-community/mathlib/pull/8707) and resolves the Zulip thread https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238707.20linter.20weirdness
* I also added some documentation / comments to the function `transform_decl_with_prefix_fun_aux`, made it non-private, and rewrote some steps.
#### Estimated changes
Modified src/tactic/transform_decl.lean


Modified test/to_additive.lean
- \+ *def* some_def.in_namespace
- \+ *def* some_def



## [2021-08-18 18:52:50](https://github.com/leanprover-community/mathlib/commit/9a249ee)
doc(tactic/simps): expand ([#8729](https://github.com/leanprover-community/mathlib/pull/8729))
* Better document custom projections that are composites of multiple projections
* Give examples of `initialize_simps_projections`
* Add `initialize_simps_projections` entry to commands.
#### Estimated changes
Modified src/tactic/simps.lean




## [2021-08-18 18:52:49](https://github.com/leanprover-community/mathlib/commit/6a83c7d)
feat(topology/compact_open): the family of constant maps collectively form a continuous map ([#8721](https://github.com/leanprover-community/mathlib/pull/8721))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.coe_const'
- \+ *def* continuous_map.const'
- \+ *lemma* continuous_map.continuous_const'



## [2021-08-18 18:52:48](https://github.com/leanprover-community/mathlib/commit/3ac609b)
chore(topology/continuous_function/compact): relax typeclass assumptions for metric space structure on C(X, Y) ([#8717](https://github.com/leanprover-community/mathlib/pull/8717))
#### Estimated changes
Modified src/topology/continuous_function/compact.lean
- \+/\- *def* continuous_map.equiv_bounded_of_compact



## [2021-08-18 18:52:47](https://github.com/leanprover-community/mathlib/commit/0d59511)
feat(topology/{continuous_function/bounded, metric_space/algebra}): new mixin classes ([#8580](https://github.com/leanprover-community/mathlib/pull/8580))
This PR defines mixin classes `has_lipschitz_add` and `has_bounded_smul` which are designed to abstract algebraic properties of metric spaces shared by normed groups/fields/modules and by `ℝ≥0`.
This permits the bounded continuous functions `α →ᵇ ℝ≥0` to be naturally a topological (ℝ≥0)-module, by a generalization of the proof previously written for normed groups/fields/modules.
Frankly, these typeclasses are a bit ad hoc -- but it all seems to work!
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/normed_space/basic.lean


Modified src/topology/continuous_function/bounded.lean
- \+/\- *def* bounded_continuous_function.coe_fn_add_hom
- \+/\- *lemma* bounded_continuous_function.forall_coe_zero_iff_zero
- \+/\- *def* bounded_continuous_function.forget_boundedness_add_hom

Added src/topology/metric_space/algebra.lean
- \+ *lemma* dist_pair_smul
- \+ *lemma* dist_smul_pair
- \+ *def* has_lipschitz_mul.C
- \+ *lemma* lipschitz_with_lipschitz_const_mul
- \+ *lemma* lipschitz_with_lipschitz_const_mul_edist



## [2021-08-18 18:52:46](https://github.com/leanprover-community/mathlib/commit/26590e9)
feat(data/list/min_max): maximum is a fold, bounded prod ([#8543](https://github.com/leanprover-community/mathlib/pull/8543))
Also provide the same lemmas for multiset.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.prod_le_of_forall_le

Modified src/data/list/basic.lean
- \+ *lemma* list.prod_le_of_forall_le

Modified src/data/list/min_max.lean
- \+ *lemma* list.le_min_of_le_forall
- \+ *lemma* list.max_le_of_forall_le
- \+ *lemma* list.max_nat_le_of_forall_le
- \+ *lemma* list.maximum_eq_coe_foldr_max_of_ne_nil
- \+ *lemma* list.maximum_nat_eq_coe_foldr_max_of_ne_nil
- \+ *lemma* list.minimum_eq_coe_foldr_min_of_ne_nil

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.prod_le_of_forall_le

Modified src/data/multiset/fold.lean
- \+ *lemma* multiset.max_le_of_forall_le
- \+ *lemma* multiset.max_nat_le_of_forall_le



## [2021-08-18 18:52:45](https://github.com/leanprover-community/mathlib/commit/4e7e7df)
feat(algebra/monoid_algebra): add_monoid_algebra.op_{add,ring}_equiv ([#8536](https://github.com/leanprover-community/mathlib/pull/8536))
Transport an opposite `add_monoid_algebra` to the algebra over the opposite ring.
On the way, 
- provide API lemma `mul_equiv.inv_fun_eq_symm {f : M ≃* N} : f.inv_fun = f.symm` and the additive version
- generalize simp lemmas `equiv_to_opposite_(symm_)apply` to `equiv_to_opposite_(symm_)coe`
- tag `map_range.(add_)equiv_symm` with `[simp]
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.op_ring_equiv_single
- \+ *lemma* add_monoid_algebra.op_ring_equiv_symm_single
- \+ *lemma* monoid_algebra.op_ring_equiv_single
- \+ *lemma* monoid_algebra.op_ring_equiv_symm_single

Modified src/algebra/opposites.lean
- \+ *lemma* add_monoid_hom.op_ext

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.inv_fun_eq_symm
- \+ *theorem* mul_equiv.symm_trans_apply

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.map_range.add_equiv_symm
- \+/\- *lemma* finsupp.map_range.equiv_symm

Modified src/data/opposite.lean
- \- *lemma* opposite.equiv_to_opposite_apply
- \+ *lemma* opposite.equiv_to_opposite_coe
- \- *lemma* opposite.equiv_to_opposite_symm_apply
- \+ *lemma* opposite.equiv_to_opposite_symm_coe



## [2021-08-18 18:52:43](https://github.com/leanprover-community/mathlib/commit/15444e1)
feat(model_theory/basic): more substructure API, including subtype, map, and comap ([#7937](https://github.com/leanprover-community/mathlib/pull/7937))
Defines `first_order.language.embedding.of_injective`, which bundles an injective hom in an algebraic language as an embedding
Defines the induced `L.Structure` on an `L.substructure`
Defines the embedding `S.subtype` from `S : L.substructure M` into `M`
Defines `substructure.map` and `substructure.comap` and associated API including Galois insertions
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.embedding.coe_fn_of_injective
- \+ *def* first_order.language.embedding.of_injective
- \+ *lemma* first_order.language.embedding.of_injective_to_hom
- \+ *lemma* first_order.language.substructure.apply_coe_mem_map
- \+ *lemma* first_order.language.substructure.closure_induction'
- \+ *theorem* first_order.language.substructure.coe_subtype
- \+ *def* first_order.language.substructure.comap
- \+ *lemma* first_order.language.substructure.comap_comap
- \+ *lemma* first_order.language.substructure.comap_id
- \+ *lemma* first_order.language.substructure.comap_inf
- \+ *lemma* first_order.language.substructure.comap_inf_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_infi
- \+ *lemma* first_order.language.substructure.comap_infi_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_injective_of_surjective
- \+ *lemma* first_order.language.substructure.comap_le_comap_iff_of_surjective
- \+ *lemma* first_order.language.substructure.comap_map_comap
- \+ *lemma* first_order.language.substructure.comap_map_eq_of_injective
- \+ *lemma* first_order.language.substructure.comap_strict_mono_of_surjective
- \+ *lemma* first_order.language.substructure.comap_sup_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_supr_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_surjective_of_injective
- \+ *lemma* first_order.language.substructure.comap_top
- \+ *lemma* first_order.language.substructure.gc_map_comap
- \+ *def* first_order.language.substructure.gci_map_comap
- \+ *def* first_order.language.substructure.gi_map_comap
- \+ *lemma* first_order.language.substructure.le_comap_map
- \+ *lemma* first_order.language.substructure.le_comap_of_map_le
- \+ *def* first_order.language.substructure.map
- \+ *lemma* first_order.language.substructure.map_bot
- \+ *lemma* first_order.language.substructure.map_comap_eq_of_surjective
- \+ *lemma* first_order.language.substructure.map_comap_le
- \+ *lemma* first_order.language.substructure.map_comap_map
- \+ *lemma* first_order.language.substructure.map_id
- \+ *lemma* first_order.language.substructure.map_inf_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_infi_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_injective_of_injective
- \+ *lemma* first_order.language.substructure.map_le_iff_le_comap
- \+ *lemma* first_order.language.substructure.map_le_map_iff_of_injective
- \+ *lemma* first_order.language.substructure.map_le_of_le_comap
- \+ *lemma* first_order.language.substructure.map_map
- \+ *lemma* first_order.language.substructure.map_strict_mono_of_injective
- \+ *lemma* first_order.language.substructure.map_sup
- \+ *lemma* first_order.language.substructure.map_sup_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_supr
- \+ *lemma* first_order.language.substructure.map_supr_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_surjective_of_surjective
- \+ *lemma* first_order.language.substructure.mem_comap
- \+ *lemma* first_order.language.substructure.mem_map
- \+ *lemma* first_order.language.substructure.mem_map_of_mem
- \+ *lemma* first_order.language.substructure.monotone_comap
- \+ *lemma* first_order.language.substructure.monotone_map
- \+ *def* first_order.language.substructure.subtype



## [2021-08-18 16:14:18](https://github.com/leanprover-community/mathlib/commit/a47d49d)
chore(set/function): remove reducible on eq_on ([#8738](https://github.com/leanprover-community/mathlib/pull/8738))
This backs out [#8736](https://github.com/leanprover-community/mathlib/pull/8736), and instead removes the unnecessary `@[reducible]`. 
This leaves the `simp` lemma available if anyone wants it (although it is not currently used in mathlib3), but should still resolve the problem that @dselsam's experimental `simp` in the binport of mathlib3 was excessively enthusiastic about using this lemma.
#### Estimated changes
Modified src/data/set/function.lean
- \+/\- *def* set.eq_on
- \+/\- *lemma* set.eq_on_empty



## [2021-08-18 16:14:17](https://github.com/leanprover-community/mathlib/commit/02b90ab)
doc(tactic/monotonicity): bad ac_mono syntax doc ([#8734](https://github.com/leanprover-community/mathlib/pull/8734))
The syntax `ac_mono h` was at some point changed to `ac_mono := h` but the documentation did not reflect the change.
#### Estimated changes
Modified src/tactic/monotonicity/interactive.lean




## [2021-08-18 12:08:53](https://github.com/leanprover-community/mathlib/commit/83c7821)
fix(algebra/algebra/restrict_scalars): Remove a bad instance ([#8732](https://github.com/leanprover-community/mathlib/pull/8732))
This instance forms a non-defeq diamond with the following one
```lean
instance submodule.restricted_module' [module R M] [is_scalar_tower R S M] (V : submodule S M) :
  module R V :=
by apply_instance
```
The `submodule.restricted_module_is_scalar_tower` instance is harmless, but it can't exist without the first one so we remove it too.
Based on the CI result, this instance wasn't used anyway.
#### Estimated changes
Modified src/algebra/algebra/restrict_scalars.lean




## [2021-08-18 12:08:52](https://github.com/leanprover-community/mathlib/commit/c0f16d2)
feat(analysis/normed_space/affine_isometry): new file, bundled affine isometries ([#8660](https://github.com/leanprover-community/mathlib/pull/8660))
This PR defines bundled affine isometries and affine isometry equivs, adapting the theory more or less wholesale from the linear isometry and affine map theories.
In follow-up PRs I re-work the Mazur-Ulam and Euclidean geometry libraries to use these objects where appropriate.
#### Estimated changes
Modified docs/undergrad.yaml


Added src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* affine_isometry.coe_comp
- \+ *lemma* affine_isometry.coe_fn_injective
- \+ *lemma* affine_isometry.coe_id
- \+ *lemma* affine_isometry.coe_mul
- \+ *lemma* affine_isometry.coe_one
- \+ *lemma* affine_isometry.coe_to_affine_isometry_equiv
- \+ *lemma* affine_isometry.coe_to_affine_map
- \+ *def* affine_isometry.comp
- \+ *lemma* affine_isometry.comp_assoc
- \+ *lemma* affine_isometry.comp_continuous_iff
- \+ *lemma* affine_isometry.comp_id
- \+ *lemma* affine_isometry.diam_image
- \+ *lemma* affine_isometry.diam_range
- \+ *lemma* affine_isometry.dist_map
- \+ *lemma* affine_isometry.ediam_image
- \+ *lemma* affine_isometry.ediam_range
- \+ *lemma* affine_isometry.edist_map
- \+ *lemma* affine_isometry.ext
- \+ *def* affine_isometry.id
- \+ *lemma* affine_isometry.id_apply
- \+ *lemma* affine_isometry.id_comp
- \+ *lemma* affine_isometry.id_to_affine_map
- \+ *lemma* affine_isometry.linear_eq_linear_isometry
- \+ *lemma* affine_isometry.map_eq_iff
- \+ *lemma* affine_isometry.map_ne
- \+ *lemma* affine_isometry.map_vadd
- \+ *lemma* affine_isometry.map_vsub
- \+ *lemma* affine_isometry.nndist_map
- \+ *lemma* affine_isometry.to_affine_isometry_equiv_apply
- \+ *lemma* affine_isometry.to_affine_map_injective
- \+ *lemma* affine_isometry_equiv.apply_symm_apply
- \+ *lemma* affine_isometry_equiv.coe_inv
- \+ *lemma* affine_isometry_equiv.coe_mk'
- \+ *lemma* affine_isometry_equiv.coe_mk
- \+ *lemma* affine_isometry_equiv.coe_mul
- \+ *lemma* affine_isometry_equiv.coe_one
- \+ *lemma* affine_isometry_equiv.coe_refl
- \+ *lemma* affine_isometry_equiv.coe_symm_trans
- \+ *lemma* affine_isometry_equiv.coe_to_affine_equiv
- \+ *lemma* affine_isometry_equiv.coe_to_affine_isometry
- \+ *lemma* affine_isometry_equiv.coe_to_homeomorph
- \+ *lemma* affine_isometry_equiv.coe_to_isometric
- \+ *lemma* affine_isometry_equiv.coe_trans
- \+ *lemma* affine_isometry_equiv.comp_continuous_iff
- \+ *lemma* affine_isometry_equiv.comp_continuous_on_iff
- \+ *lemma* affine_isometry_equiv.diam_image
- \+ *lemma* affine_isometry_equiv.dist_map
- \+ *lemma* affine_isometry_equiv.ediam_image
- \+ *lemma* affine_isometry_equiv.edist_map
- \+ *lemma* affine_isometry_equiv.ext
- \+ *lemma* affine_isometry_equiv.linear_eq_linear_isometry
- \+ *lemma* affine_isometry_equiv.linear_isometry_equiv_mk'
- \+ *lemma* affine_isometry_equiv.map_eq_iff
- \+ *lemma* affine_isometry_equiv.map_ne
- \+ *lemma* affine_isometry_equiv.map_vadd
- \+ *lemma* affine_isometry_equiv.map_vsub
- \+ *def* affine_isometry_equiv.mk'
- \+ *lemma* affine_isometry_equiv.range_eq_univ
- \+ *def* affine_isometry_equiv.refl
- \+ *lemma* affine_isometry_equiv.refl_trans
- \+ *def* affine_isometry_equiv.symm
- \+ *lemma* affine_isometry_equiv.symm_apply_apply
- \+ *lemma* affine_isometry_equiv.symm_symm
- \+ *lemma* affine_isometry_equiv.symm_trans
- \+ *lemma* affine_isometry_equiv.to_affine_equiv_injective
- \+ *lemma* affine_isometry_equiv.to_affine_equiv_refl
- \+ *lemma* affine_isometry_equiv.to_affine_equiv_symm
- \+ *def* affine_isometry_equiv.to_affine_isometry
- \+ *def* affine_isometry_equiv.to_homeomorph
- \+ *lemma* affine_isometry_equiv.to_homeomorph_refl
- \+ *lemma* affine_isometry_equiv.to_homeomorph_symm
- \+ *def* affine_isometry_equiv.to_isometric
- \+ *lemma* affine_isometry_equiv.to_isometric_refl
- \+ *lemma* affine_isometry_equiv.to_isometric_symm
- \+ *def* affine_isometry_equiv.trans
- \+ *lemma* affine_isometry_equiv.trans_assoc
- \+ *lemma* affine_isometry_equiv.trans_refl
- \+ *lemma* affine_isometry_equiv.trans_symm
- \+ *lemma* linear_isometry.coe_to_affine_isometry
- \+ *def* linear_isometry.to_affine_isometry
- \+ *lemma* linear_isometry.to_affine_isometry_linear_isometry
- \+ *lemma* linear_isometry.to_affine_isometry_to_affine_map
- \+ *lemma* linear_isometry_equiv.coe_to_affine_isometry_equiv
- \+ *def* linear_isometry_equiv.to_affine_isometry_equiv
- \+ *lemma* linear_isometry_equiv.to_affine_isometry_equiv_linear_isometry_equiv
- \+ *lemma* linear_isometry_equiv.to_affine_isometry_equiv_to_affine_equiv
- \+ *lemma* linear_isometry_equiv.to_affine_isometry_equiv_to_affine_isometry

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.id_apply
- \+ *lemma* linear_isometry.id_to_linear_map
- \- *lemma* linear_isometry_equiv.linear_isometry.id_apply
- \- *lemma* linear_isometry_equiv.linear_isometry.id_to_linear_map

Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *def* affine_equiv.mk'
- \- *lemma* affine_equiv.to_equiv_mk'



## [2021-08-18 12:08:51](https://github.com/leanprover-community/mathlib/commit/d1b34f7)
feat(ring_theory): define the ideal class group ([#8626](https://github.com/leanprover-community/mathlib/pull/8626))
This PR defines the ideal class group of an integral domain, as the quotient of the invertible fractional ideals by the principal fractional ideals. It also shows that this corresponds to the more traditional definition in a Dedekind domain, namely the quotient of the nonzero ideals by `I ~ J ↔ ∃ xy, xI = yJ`.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr
#### Estimated changes
Added src/ring_theory/class_group.lean
- \+ *lemma* card_class_group_eq_one
- \+ *lemma* card_class_group_eq_one_iff
- \+ *lemma* class_group.mk0_eq_mk0_iff
- \+ *lemma* class_group.mk0_eq_mk0_iff_exists_fraction_ring
- \+ *lemma* class_group.mk0_eq_one_iff
- \+ *lemma* class_group.mk0_surjective
- \+ *lemma* class_group.mk_eq_one_iff
- \+ *def* class_group
- \+ *lemma* coe_to_principal_ideal
- \+ *lemma* quotient_group.mk'_eq_mk'
- \+ *def* to_principal_ideal
- \+ *lemma* to_principal_ideal_eq_iff

Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.div_surjective
- \+ *lemma* is_fraction_ring.lift_algebra_map
- \+/\- *lemma* is_fraction_ring.lift_mk'
- \+/\- *lemma* is_fraction_ring.mk'_eq_div
- \+ *lemma* is_localization.mk'_spec'_mk
- \+ *lemma* is_localization.mk'_spec_mk

Modified src/ring_theory/non_zero_divisors.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean




## [2021-08-18 10:32:47](https://github.com/leanprover-community/mathlib/commit/a0aee51)
chore({group,ring}_theory/sub{group,monoid,ring,semiring}): Add missing scalar action typeclasses ([#8731](https://github.com/leanprover-community/mathlib/pull/8731))
This adds `has_faithful_scalar` and `mul_semiring_action` instances for simple subtypes. 
Neither typeclass associates any new actions with these types; they just provide additionally properties of the existing actions.
#### Estimated changes
Modified src/algebra/group_ring_action.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-08-18 10:32:46](https://github.com/leanprover-community/mathlib/commit/6bd6c11)
refactor(field_theory,ring_theory): generalize adjoin_root.equiv to `power_basis` ([#8726](https://github.com/leanprover-community/mathlib/pull/8726))
We had two proofs that `A`-preserving maps from `A[x]` or `A(x)` to `B` are in bijection with the set of conjugate roots to `x` in `B`, so by stating the result for `power_basis` we can avoid reproving it twice, and get some generalizations (to a `comm_ring` instead of an `integral_domain`) for free.
There's probably a bit more to generalize in `adjoin_root` or `intermediate_field.adjoin`, which I will do in follow-up PRs.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \- *lemma* intermediate_field.adjoin.power_basis.gen_eq
- \+ *lemma* intermediate_field.minpoly_gen

Modified src/field_theory/separable.lean
- \+ *lemma* alg_hom.card_of_power_basis

Modified src/ring_theory/adjoin_root.lean
- \+/\- *def* adjoin_root.equiv
- \+ *lemma* adjoin_root.is_algebraic_root
- \+ *lemma* adjoin_root.is_integral_root
- \+ *lemma* adjoin_root.minpoly_power_basis_gen
- \+ *lemma* adjoin_root.minpoly_power_basis_gen_of_monic
- \+ *lemma* adjoin_root.minpoly_root

Modified src/ring_theory/power_basis.lean




## [2021-08-18 10:32:45](https://github.com/leanprover-community/mathlib/commit/3de385a)
feat(ring_theory/dedekind_domain): prime elements of `ideal A` are the prime ideals ([#8718](https://github.com/leanprover-community/mathlib/pull/8718))
This shows that Dedekind domains have unique factorization into prime *ideals*, not just prime *elements* of the monoid `ideal A`.
After some thinking, I believe Dedekind domains are the most common setting in which this equality hold. If anyone has a reference showing how to generalize this, that would be much appreciated.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* ideal.dvd_span_singleton
- \+ *lemma* ideal.is_prime_of_prime
- \+ *theorem* ideal.prime_iff_is_prime
- \+ *theorem* ideal.prime_of_is_prime



## [2021-08-18 10:32:44](https://github.com/leanprover-community/mathlib/commit/f1b6c8f)
feat(data/matrix/kronecker): add two lemmas ([#8700](https://github.com/leanprover-community/mathlib/pull/8700))
Added two lemmas `kronecker_map_assoc` and `kronecker_assoc` showing associativity of the Kronecker product
#### Estimated changes
Modified src/data/matrix/kronecker.lean
- \+ *lemma* matrix.kronecker_assoc
- \+ *lemma* matrix.kronecker_map_assoc
- \+ *lemma* matrix.kronecker_map_assoc₁
- \+ *def* matrix.kronecker_map_bilinear
- \+ *lemma* matrix.kronecker_map_bilinear_mul_mul
- \- *def* matrix.kronecker_map_linear
- \- *lemma* matrix.kronecker_map_linear_mul_mul
- \+ *lemma* matrix.kronecker_tmul_assoc



## [2021-08-18 08:28:19](https://github.com/leanprover-community/mathlib/commit/5335c67)
refactor(topology/algebra/ring): `topological_ring` extends `topological_add_group` ([#8709](https://github.com/leanprover-community/mathlib/pull/8709))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/topology/algebra/ring.lean




## [2021-08-18 08:28:18](https://github.com/leanprover-community/mathlib/commit/1151611)
feat(algebra/pointwise): instances in locale pointwise ([#8689](https://github.com/leanprover-community/mathlib/pull/8689))
@rwbarton and @bryangingechen mentioned in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Friday.20afternoon.20puzzle.20--.2037.20.E2.88.88.2037.3F that we should put pointwise instances on sets in a locale.
This PR does that. You now have to write `open_locale pointwise` to get algebraic operations on sets and finsets.
#### Estimated changes
Modified src/algebra/add_torsor.lean


Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/bounds.lean


Modified src/algebra/ordered_pointwise.lean


Modified src/algebra/pointwise.lean
- \- *lemma* finset.add_card_le

Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/seminorm.lean


Modified src/data/real/basic.lean


Modified src/data/set/intervals/image_preimage.lean


Modified src/data/set/intervals/unordered_interval.lean
- \+/\- *lemma* set.preimage_neg_interval

Modified src/group_theory/finiteness.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/linear_algebra/basic.lean


Modified src/measure_theory/group/basic.lean


Modified src/measure_theory/measure/haar.lean


Modified src/order/filter/pointwise.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/nonarchimedean/basic.lean




## [2021-08-18 08:28:17](https://github.com/leanprover-community/mathlib/commit/efa34dc)
feat(data/list/perm): nodup_permutations ([#8616](https://github.com/leanprover-community/mathlib/pull/8616))
A simpler version of [#8494](https://github.com/leanprover-community/mathlib/pull/8494)
TODO: `nodup s.permutations ↔ nodup s`
TODO: `count s s.permutations = (zip_with count s s.tails).prod`
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.count_bind
- \+ *lemma* list.count_map_map
- \+ *lemma* list.inj_on_insert_nth_index_of_not_mem
- \+ *lemma* list.insert_nth_injective
- \+ *lemma* list.insert_nth_length_self
- \- *lemma* list.insert_nth_nil
- \+ *lemma* list.insert_nth_of_length_lt
- \+ *lemma* list.insert_nth_succ_cons
- \+ *lemma* list.insert_nth_zero
- \+ *lemma* list.length_insert_nth_le_succ
- \+ *lemma* list.length_le_length_insert_nth
- \+ *lemma* list.nth_le_insert_nth_add_succ
- \+ *lemma* list.nth_le_insert_nth_of_lt
- \+ *lemma* list.nth_le_insert_nth_self

Modified src/data/list/perm.lean
- \+ *lemma* list.count_permutations'_aux_self
- \+ *lemma* list.injective_permutations'_aux
- \+ *lemma* list.length_permutations'_aux
- \+ *lemma* list.nodup_permutations'_aux_iff
- \+ *lemma* list.nodup_permutations'_aux_of_not_mem
- \+ *lemma* list.nodup_permutations
- \+ *lemma* list.nth_le_permutations'_aux
- \+ *lemma* list.permutations'_aux_nth_le_zero



## [2021-08-18 07:53:20](https://github.com/leanprover-community/mathlib/commit/41f7b5b)
feat(linear_algebra/clifford_algebra/equivs): there is a clifford algebra isomorphic to every quaternion algebra ([#8670](https://github.com/leanprover-community/mathlib/pull/8670))
The proofs are not particularly fast here unfortunately.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/basic.lean
- \+ *lemma* clifford_algebra.ι_mul_ι_add_swap

Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+/\- *lemma* clifford_algebra_complex.to_complex_ι
- \+ *def* clifford_algebra_quaternion.Q
- \+ *lemma* clifford_algebra_quaternion.Q_apply
- \+ *def* clifford_algebra_quaternion.of_quaternion
- \+ *lemma* clifford_algebra_quaternion.of_quaternion_apply
- \+ *lemma* clifford_algebra_quaternion.of_quaternion_comp_to_quaternion
- \+ *def* clifford_algebra_quaternion.quaternion_basis
- \+ *def* clifford_algebra_quaternion.to_quaternion
- \+ *lemma* clifford_algebra_quaternion.to_quaternion_comp_of_quaternion
- \+ *lemma* clifford_algebra_quaternion.to_quaternion_ι



## [2021-08-18 05:11:57](https://github.com/leanprover-community/mathlib/commit/40b7dc7)
chore(data/set/function): remove useless @[simp] ([#8736](https://github.com/leanprover-community/mathlib/pull/8736))
This lemma
```
lemma eq_on_empty (f₁ f₂ : α → β) : eq_on f₁ f₂ ∅ := λ x, false.elim
```
is currently marked `@[simp]`, but can never fire, because after noting `eq_on` is `@[reducible]`, the pattern we would be replacing looks like `?f ?x`, which Lean3's simp doesn't like.
On the other hand, @dselsam's experiments with discrimination trees in simp in the binport of mathlib are spending most of their time on this lemma!
Let's get rid of it.
#### Estimated changes
Modified src/data/set/function.lean
- \+/\- *lemma* set.eq_on_empty



## [2021-08-18 03:17:06](https://github.com/leanprover-community/mathlib/commit/cb3d5db)
feat(algebra/ordered_monoid): generalize {min,max}_mul_mul_{left,right} ([#8725](https://github.com/leanprover-community/mathlib/pull/8725))
Before, it has assumptions about `cancel_comm_monoid` for all the lemmas.
In fact, they hold under much weaker `has_mul`.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+/\- *lemma* max_le_mul_of_one_le
- \+/\- *lemma* min_le_mul_of_one_le_left
- \+/\- *lemma* min_le_mul_of_one_le_right



## [2021-08-18 02:21:49](https://github.com/leanprover-community/mathlib/commit/e23e6eb)
chore(scripts): update nolints.txt ([#8735](https://github.com/leanprover-community/mathlib/pull/8735))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-08-18 00:41:07](https://github.com/leanprover-community/mathlib/commit/ce965a5)
feat(measure_theory/decomposition/lebesgue): the Lebesgue decomposition theorem ([#8687](https://github.com/leanprover-community/mathlib/pull/8687))
This PR proves the existence and uniqueness of the Lebesgue decompositions theorem which is the last step before proving the Radon-Nikodym theorem 🎉
#### Estimated changes
Added src/measure_theory/decomposition/lebesgue.lean
- \+ *theorem* measure_theory.measure.eq_radon_nikodym_deriv
- \+ *theorem* measure_theory.measure.eq_singular_part
- \+ *lemma* measure_theory.measure.exists_positive_of_not_mutually_singular
- \+ *def* measure_theory.measure.have_lebesgue_decomposition
- \+ *lemma* measure_theory.measure.have_lebesgue_decomposition_add
- \+ *theorem* measure_theory.measure.have_lebesgue_decomposition_of_finite_measure
- \+ *lemma* measure_theory.measure.have_lebesgue_decomposition_spec
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.max_measurable_le
- \+ *def* measure_theory.measure.lebesgue_decomposition.measurable_le
- \+ *def* measure_theory.measure.lebesgue_decomposition.measurable_le_eval
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.sup_mem_measurable_le
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_le_le
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le'
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_monotone'
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_monotone
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.supr_succ_eq_sup
- \+ *lemma* measure_theory.measure.lebesgue_decomposition.zero_mem_measurable_le
- \+ *lemma* measure_theory.measure.measurable_radon_nikodym_deriv
- \+ *lemma* measure_theory.measure.mutually_singular_singular_part
- \+ *def* measure_theory.measure.radon_nikodym_deriv
- \+ *def* measure_theory.measure.singular_part
- \+ *lemma* measure_theory.measure.singular_part_le
- \+ *lemma* measure_theory.measure.with_density_radon_nikodym_deriv_le

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.with_density_zero

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.finite_measure_of_le
- \+ *lemma* measure_theory.measure.sigma_finite_of_le

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.exists_measure_pos_of_not_measure_Union_null



## [2021-08-17 22:18:00](https://github.com/leanprover-community/mathlib/commit/67501f6)
feat(algebra): generalize `ring_hom.map_dvd` ([#8722](https://github.com/leanprover-community/mathlib/pull/8722))
Now it is available for `mul_hom` and `monoid_hom`, and in a `monoid` (or `semiring` in the `ring_hom` case), not just `comm_semiring`
#### Estimated changes
Modified src/algebra/divisibility.lean
- \+ *lemma* monoid_hom.map_dvd
- \+ *lemma* mul_hom.map_dvd

Modified src/algebra/ring/basic.lean
- \+/\- *lemma* ring_hom.map_dvd



## [2021-08-17 21:07:52](https://github.com/leanprover-community/mathlib/commit/e6e5718)
chore(lie/semisimple): tweak `lie_algebra.subsingleton_of_semisimple_lie_abelian` ([#8728](https://github.com/leanprover-community/mathlib/pull/8728))
#### Estimated changes
Modified src/algebra/lie/semisimple.lean




## [2021-08-17 21:07:51](https://github.com/leanprover-community/mathlib/commit/31d5549)
docs(overview): nilpotent and presented groups ([#8711](https://github.com/leanprover-community/mathlib/pull/8711))
#### Estimated changes
Modified docs/overview.yaml




## [2021-08-17 18:30:13](https://github.com/leanprover-community/mathlib/commit/5b5b432)
fix(tactic/tfae): remove unused arg in tfae_have ([#8727](https://github.com/leanprover-community/mathlib/pull/8727))
Since this "discharger" argument is not using the interactive tactic parser, you can only give names of tactics here, and in any case it's unused by the body, so there is no point in specifying the discharger in the first place.
#### Estimated changes
Modified src/tactic/tfae.lean




## [2021-08-17 18:30:12](https://github.com/leanprover-community/mathlib/commit/e0656d1)
chore(algebra/module/basic): golf a proof ([#8723](https://github.com/leanprover-community/mathlib/pull/8723))
#### Estimated changes
Modified src/algebra/module/basic.lean




## [2021-08-17 18:30:11](https://github.com/leanprover-community/mathlib/commit/579ec7d)
feat(ring_theory/power_basis): `pb.minpoly_gen = minpoly pb.gen` ([#8719](https://github.com/leanprover-community/mathlib/pull/8719))
It actually kind of surprised me that this lemma was never added!
#### Estimated changes
Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.degree_minpoly_gen
- \+ *lemma* power_basis.dim_le_degree_of_root
- \+ *lemma* power_basis.minpoly_gen_eq



## [2021-08-17 18:30:10](https://github.com/leanprover-community/mathlib/commit/fefdcf5)
feat(tactic/lint): add universe linter ([#8685](https://github.com/leanprover-community/mathlib/pull/8685))
* The linter checks that there are no bad `max u v` occurrences in declarations (bad means that neither `u` nor `v` occur by themselves). See documentation for more details.
* `meta/expr` now imports `meta/rb_map` (but this doesn't give any new transitive imports, so it barely matters). I also removed a transitive import from `meta/rb_map`.
#### Estimated changes
Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/model_theory/basic.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/misc.lean


Modified src/topology/category/Profinite/projective.lean
- \+/\- *def* Profinite.projective_presentation



## [2021-08-17 18:30:09](https://github.com/leanprover-community/mathlib/commit/3453f7a)
docs(order/filter/partial): add module docstring ([#8620](https://github.com/leanprover-community/mathlib/pull/8620))
Fix up some names:
* `core_preimage_gc ` -> `image_core_gc`
* `rtendsto_iff_le_comap` -> `rtendsto_iff_le_rcomap`
Add whitespaces around tokens
#### Estimated changes
Modified src/data/rel.lean
- \- *theorem* rel.core_preimage_gc
- \+ *theorem* rel.image_core_gc
- \+/\- *lemma* rel.mem_core
- \+/\- *lemma* rel.mem_preimage
- \+/\- *def* rel.preimage

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.Sup_sets_eq
- \+/\- *lemma* filter.comap_Sup
- \+/\- *lemma* filter.comap_infi
- \+/\- *lemma* filter.comap_ne_bot
- \+/\- *lemma* filter.exists_mem_subset_iff
- \+/\- *lemma* filter.filter_eq
- \+/\- *lemma* filter.inter_mem
- \+/\- *lemma* filter.map_supr
- \+/\- *theorem* filter.mem_comap
- \+/\- *lemma* filter.mem_infi_of_mem
- \+/\- *lemma* filter.mem_map_iff_exists_image
- \+/\- *lemma* filter.mem_of_superset
- \+/\- *lemma* filter.mem_principal_self
- \+/\- *lemma* filter.mem_top_iff_forall
- \+/\- *lemma* filter.monotone_mem
- \+/\- *lemma* filter.prod_comm
- \+/\- *lemma* filter.seq_pure
- \+/\- *lemma* filter.supr_principal
- \+/\- *lemma* filter.supr_sets_eq
- \+/\- *lemma* filter.tendsto_const_pure

Modified src/order/filter/partial.lean
- \+/\- *def* filter.rmap
- \+/\- *theorem* filter.rmap_sets
- \- *theorem* filter.rtendsto_iff_le_comap
- \+ *theorem* filter.rtendsto_iff_le_rcomap



## [2021-08-17 18:30:08](https://github.com/leanprover-community/mathlib/commit/90fc064)
chore(algebra/associated): use more dot notation ([#8556](https://github.com/leanprover-community/mathlib/pull/8556))
I was getting annoyed that working with definitions such as `irreducible`, `prime` and `associated`, I had to write quite verbose terms like `dvd_symm_of_irreducible (irreducible_of_prime (prime_of_factor _ hp)) (irreducible_of_prime (prime_of_factor _ hq)) hdvd`, where a lot of redundancy can be eliminated with dot notation: `(prime_of_factor _ hp).irreducible.dvd_symm (prime_of_factor _ hq).irreducible hdvd`. This PR changes the spelling of many of the lemmas in `algebra/associated.lean` to make usage of dot notation easier. It also adds a few shortcut lemmas that address common patterns.
Since this change touches a lot of files, I'll add a RFC label / [open a thread on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/RFC.3A.20adding.20dot.20notations.20.238556) to see what everyone thinks.
Renamings:
 * `irreducible_of_prime` → `prime.irreducible`
 * `dvd_symm_of_irreducible` → `irreducible.dvd_symm`
 * `dvd_symm_iff_of_irreducible` → `irreducible.dvd_comm` (cf. `eq.symm` versus `eq_comm`)
 * `associated_mul_mul` → `associated.mul_mul`
 * `associated_pow_pow` → `associated.pow_pow`
 * `dvd_of_associated` → `associated.dvd`
 * `dvd_dvd_of_associated` → `associated.dvd_dvd`
 * `dvd_iff_dvd_of_rel_{left,right}` → `associated.dvd_iff_dvd_{left,right}`
 * `{eq,ne}_zero_iff_of_associated` → `associated.{eq,ne}_zero_iff`
 * `{irreducible,prime}_of_associated` → `associated.{irreducible,prime}`
 * `{irreducible,is_unit,prime}_iff_of_associated` → `associated.{irreducible,is_unit,prime}_iff`
  * `associated_of_{irreducible,prime}_of_dvd` → `{irreducible,prime}.associated_of_dvd`
 * `gcd_eq_of_associated_{left,right}` → `associated.gcd_eq_{left,right}`
 * `{irreducible,prime}_of_degree_eq_one_of_monic` → `monic.{irreducible,prime}_of_degree_eq_one`
  * `gcd_monoid.prime_of_irreducible` → `irreducible.prime` (since the GCD case is probably the only case we care about for this implication. And we could generalize to Schreier domains if not)
Additions:
 * `associated.is_unit := (associated.is_unit_iff _).mp` (to match `associated.prime` and `associated.irreducible`)
 * `associated.mul_left := associated.mul_mul (associated.refl _) _`
 * `associated.mul_right := associated.mul_mul _  (associated.refl _)`
Other changes:
 * `associated_normalize`, `normalize_associated`, `associates.mk_normalize`, `normalize_apply`, `prime_X_sub_C`: make their final parameter explicit, since it is only inferrable when trying to apply these lemmas. This change helped to golf a few proofs from tactic mode to term mode.
 * slight golfing and style fixes
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associated.dvd_iff_dvd_left
- \+ *lemma* associated.dvd_iff_dvd_right
- \+ *lemma* associated.eq_zero_iff
- \+ *lemma* associated.is_unit_iff
- \+ *lemma* associated.mul_left
- \+ *lemma* associated.mul_mul
- \+ *lemma* associated.mul_right
- \+ *lemma* associated.ne_zero_iff
- \+ *lemma* associated.of_mul_left
- \+ *lemma* associated.of_mul_right
- \+ *lemma* associated.pow_pow
- \+ *lemma* associated.prime_iff
- \- *lemma* associated_mul_left_cancel
- \- *lemma* associated_mul_mul
- \- *lemma* associated_mul_right_cancel
- \- *lemma* associated_of_irreducible_of_dvd
- \- *lemma* associated_of_prime_of_dvd
- \- *lemma* associated_pow_pow
- \- *lemma* dvd_dvd_of_associated
- \- *lemma* dvd_iff_dvd_of_rel_left
- \- *lemma* dvd_iff_dvd_of_rel_right
- \- *lemma* dvd_of_associated
- \- *lemma* dvd_symm_iff_of_irreducible
- \- *lemma* dvd_symm_of_irreducible
- \- *lemma* eq_zero_iff_of_associated
- \+ *lemma* irreducible.associated_of_dvd
- \+ *lemma* irreducible.dvd_comm
- \+ *lemma* irreducible.dvd_symm
- \- *lemma* irreducible_iff_of_associated
- \- *lemma* irreducible_of_associated
- \- *lemma* irreducible_of_prime
- \- *lemma* is_unit_iff_of_associated
- \- *lemma* ne_zero_iff_of_associated
- \+ *lemma* prime.associated_of_dvd
- \- *lemma* prime_iff_of_associated
- \- *lemma* prime_of_associated

Modified src/algebra/divisibility.lean


Modified src/algebra/gcd_monoid.lean
- \+ *theorem* associated.gcd_eq_left
- \+ *theorem* associated.gcd_eq_right
- \+/\- *theorem* associated_normalize
- \+/\- *lemma* associates.mk_normalize
- \- *theorem* gcd_eq_of_associated_left
- \- *theorem* gcd_eq_of_associated_right
- \+/\- *lemma* normalize_apply
- \+/\- *theorem* normalize_associated

Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/gcd_monoid/multiset.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/squarefree.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/prime.lean


Modified src/data/polynomial/cancel_leads.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/ring_division.lean
- \- *lemma* polynomial.irreducible_of_degree_eq_one_of_monic
- \+ *lemma* polynomial.monic.irreducible_of_degree_eq_one
- \+ *lemma* polynomial.monic.prime_of_degree_eq_one
- \+/\- *theorem* polynomial.prime_X_sub_C
- \- *lemma* polynomial.prime_of_degree_eq_one_of_monic

Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/number_theory/divisors.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2021-08-17 16:30:01](https://github.com/leanprover-community/mathlib/commit/508b13e)
chore(*): flip various `subsingleton_iff`, `nontrivial_iff` lemmas and add `simp` ([#8703](https://github.com/leanprover-community/mathlib/pull/8703))
#### Estimated changes
Modified src/algebra/lie/submodule.lean
- \+/\- *lemma* lie_submodule.nontrivial_iff
- \+/\- *lemma* lie_submodule.subsingleton_iff

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* subgroup.nontrivial_iff
- \+/\- *lemma* subgroup.subsingleton_iff

Modified src/group_theory/submonoid/basic.lean
- \+/\- *lemma* submonoid.nontrivial_iff
- \+/\- *lemma* submonoid.subsingleton_iff

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.nontrivial_iff
- \+/\- *lemma* submodule.subsingleton_iff



## [2021-08-17 13:05:54](https://github.com/leanprover-community/mathlib/commit/450c2d0)
refactor(algebra/algebra/basic): move restrict_scalars into more appropriate files ([#8712](https://github.com/leanprover-community/mathlib/pull/8712))
This puts:
* `submodule.restrict_scalars` in `submodule.lean` since the proofs are all available there, and this is consistent with how `linear_map.restrict_scalars` is placed.
  This is almost a copy-paste, but all the `R` and `S` variables are swapped to match the existing convention in that file.
* The type alias `restrict_scalars` is now in its own file.
  The docstring at the top of the file is entirely new, but the rest is a direct copy and paste.
The motivation is primarily to reduce the size of `algebra/algebra/basic` a little.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* restrict_scalars.alg_equiv
- \- *def* restrict_scalars.linear_equiv
- \- *lemma* restrict_scalars.linear_equiv_map_smul
- \- *def* restrict_scalars
- \- *lemma* restrict_scalars_smul_def
- \- *def* submodule.restrict_scalars
- \- *lemma* submodule.restrict_scalars_bot
- \- *def* submodule.restrict_scalars_equiv
- \- *lemma* submodule.restrict_scalars_inj
- \- *lemma* submodule.restrict_scalars_injective
- \- *lemma* submodule.restrict_scalars_mem
- \- *lemma* submodule.restrict_scalars_top

Added src/algebra/algebra/restrict_scalars.lean
- \+ *def* restrict_scalars.alg_equiv
- \+ *def* restrict_scalars.linear_equiv
- \+ *lemma* restrict_scalars.linear_equiv_map_smul
- \+ *def* restrict_scalars
- \+ *lemma* restrict_scalars_smul_def

Modified src/algebra/lie/base_change.lean


Modified src/algebra/module/submodule.lean
- \+ *def* submodule.restrict_scalars
- \+ *def* submodule.restrict_scalars_equiv
- \+ *lemma* submodule.restrict_scalars_inj
- \+ *lemma* submodule.restrict_scalars_injective
- \+ *lemma* submodule.restrict_scalars_mem

Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* submodule.restrict_scalars_bot
- \+ *lemma* submodule.restrict_scalars_top

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/extend.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/noetherian.lean




## [2021-08-17 12:21:22](https://github.com/leanprover-community/mathlib/commit/0c145d8)
feat(measure_theory/measure/measure_space): add formula for `(map f μ).to_outer_measure` ([#8714](https://github.com/leanprover-community/mathlib/pull/8714))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.map_to_outer_measure

Modified src/measure_theory/measure/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.trim_eq_trim_iff
- \+ *theorem* measure_theory.outer_measure.trim_le_trim_iff



## [2021-08-17 10:49:29](https://github.com/leanprover-community/mathlib/commit/4df3fb9)
chore(topology/maps): add tendsto_nhds_iff lemmas ([#8693](https://github.com/leanprover-community/mathlib/pull/8693))
This adds lemmas of the form `something.tendsto_nhds_iff` to ease use.
I also had to get lemmas out of a section because `α` was duplicated and that caused typechecking problems.
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* closed_embedding.tendsto_nhds_iff
- \+ *lemma* open_embedding.tendsto_nhds_iff

Modified src/topology/metric_space/isometry.lean
- \+/\- *theorem* isometry.closed_embedding
- \+ *lemma* isometry.tendsto_nhds_iff
- \+/\- *theorem* isometry.uniform_embedding



## [2021-08-17 09:42:21](https://github.com/leanprover-community/mathlib/commit/edb0ba4)
chore(measure_theory/measure/hausdorff): golf ([#8706](https://github.com/leanprover-community/mathlib/pull/8706))
* add a `mk_metric` version of `hausdorff_measure_le`, add `finset.sum` versions for both `mk_metric` and `hausdorff_measure`;
* slightly golf the proof.
#### Estimated changes
Modified src/measure_theory/measure/hausdorff.lean
- \- *lemma* measure_theory.measure.hausdorff_measure_le
- \+ *lemma* measure_theory.measure.hausdorff_measure_le_liminf_sum
- \+ *lemma* measure_theory.measure.hausdorff_measure_le_liminf_tsum
- \+ *lemma* measure_theory.measure.mk_metric_le_liminf_sum
- \+ *lemma* measure_theory.measure.mk_metric_le_liminf_tsum

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* emetric.diam_Union_mem_option



## [2021-08-17 08:38:06](https://github.com/leanprover-community/mathlib/commit/0591c27)
feat(ring_theory/fractional_ideal): lemmas on `span_singleton _ x * I` ([#8624](https://github.com/leanprover-community/mathlib/pull/8624))
Useful in proving the basic properties of the ideal class group. See also [#8622](https://github.com/leanprover-community/mathlib/pull/8622) which proves similar things for integral ideals.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.eq_span_singleton_mul
- \+ *lemma* fractional_ideal.le_span_singleton_mul_iff
- \+ *lemma* fractional_ideal.mk'_mul_coe_ideal_eq_coe_ideal
- \+ *lemma* fractional_ideal.span_singleton_mul_coe_ideal_eq_coe_ideal
- \+ *lemma* fractional_ideal.span_singleton_mul_le_iff



## [2021-08-17 01:58:23](https://github.com/leanprover-community/mathlib/commit/b6f1214)
chore(scripts): update nolints.txt ([#8715](https://github.com/leanprover-community/mathlib/pull/8715))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-08-16 18:56:34](https://github.com/leanprover-community/mathlib/commit/1263906)
chore(data/nat/pairing): add `pp_nodot`, fix some non-finalizing `simp`s ([#8705](https://github.com/leanprover-community/mathlib/pull/8705))
#### Estimated changes
Modified src/data/nat/pairing.lean
- \+/\- *def* nat.mkpair
- \+/\- *def* nat.unpair



## [2021-08-16 18:56:33](https://github.com/leanprover-community/mathlib/commit/40d2602)
chore(analysis/calculus/deriv): weaker assumptions for `deriv_mul_const` ([#8704](https://github.com/leanprover-community/mathlib/pull/8704))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_add_const'
- \+ *lemma* deriv_const_add'
- \+ *lemma* deriv_const_mul'
- \+/\- *lemma* deriv_const_mul
- \+/\- *lemma* deriv_div_const
- \+/\- *lemma* deriv_id''
- \+/\- *lemma* deriv_id'
- \+ *lemma* deriv_mul_const'
- \+/\- *lemma* deriv_mul_const



## [2021-08-16 18:56:32](https://github.com/leanprover-community/mathlib/commit/d5ce7e5)
chore(data/vector): rename vector2 ([#8697](https://github.com/leanprover-community/mathlib/pull/8697))
This file was named this way to avoid clashing with `data/vector.lean` in core.
This renames it to `data/vector/basic.lean` which avoids the problem.
There was never a `vector2` definition, this was only ever a filename.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/data/array/lemmas.lean


Modified src/data/bitvec/core.lean


Modified src/data/sym/basic.lean


Renamed src/data/vector2.lean to src/data/vector/basic.lean




## [2021-08-16 16:19:26](https://github.com/leanprover-community/mathlib/commit/253712e)
feat(ring_theory/ideal): lemmas on `ideal.span {x} * I` ([#8622](https://github.com/leanprover-community/mathlib/pull/8622))
Originally created for being used in the context of the ideal class group, but didn't end up being used. Hopefully they are still useful for others.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.eq_span_singleton_mul
- \+ *lemma* ideal.le_span_singleton_mul_iff
- \+ *lemma* ideal.mem_mul_span_singleton
- \+ *lemma* ideal.mem_span_singleton_mul
- \+ *lemma* ideal.span_singleton_mul_eq_span_singleton_mul
- \+ *lemma* ideal.span_singleton_mul_le_iff
- \+ *lemma* ideal.span_singleton_mul_le_span_singleton_mul



## [2021-08-16 16:19:25](https://github.com/leanprover-community/mathlib/commit/65b0c58)
feat(ring_theory/localization): some lemmas on `coe_submodule` ([#8621](https://github.com/leanprover-community/mathlib/pull/8621))
A small assortment of results on `is_localization.coe_submodule`, needed for elementary facts about the ideal class group.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.coe_submodule_injective
- \+ *lemma* is_fraction_ring.coe_submodule_is_principal
- \+ *lemma* is_localization.coe_submodule_injective
- \+ *lemma* is_localization.coe_submodule_is_principal
- \+ *lemma* is_localization.coe_submodule_span
- \+ *lemma* is_localization.coe_submodule_span_singleton



## [2021-08-16 16:19:24](https://github.com/leanprover-community/mathlib/commit/80b699b)
chore(ring_theory): generalize `non_zero_divisors` lemmas to `monoid_with_zero` ([#8607](https://github.com/leanprover-community/mathlib/pull/8607))
None of the results about `non_zero_divisors` needed a ring structure, just a `monoid_with_zero`. So the generalization is obvious.
Shall we move this file to the `algebra` namespace sometime soon?
#### Estimated changes
Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/non_zero_divisors.lean
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_left_eq_zero
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_right_eq_zero
- \- *lemma* le_non_zero_divisors_of_domain
- \+ *lemma* le_non_zero_divisors_of_no_zero_divisors
- \- *lemma* map_le_non_zero_divisors_of_injective
- \- *lemma* map_mem_non_zero_divisors
- \- *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+/\- *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
- \+ *lemma* monoid_with_zero_hom.map_mem_non_zero_divisors
- \+ *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors
- \+/\- *lemma* mul_mem_non_zero_divisors
- \- *lemma* powers_le_non_zero_divisors_of_domain
- \+ *lemma* powers_le_non_zero_divisors_of_no_zero_divisors
- \+/\- *lemma* prod_zero_iff_exists_zero
- \+ *lemma* ring_hom.map_le_non_zero_divisors_of_injective
- \+ *lemma* ring_hom.map_mem_non_zero_divisors
- \+ *lemma* ring_hom.map_ne_zero_of_mem_non_zero_divisors

Modified src/ring_theory/polynomial/scale_roots.lean




## [2021-08-16 16:19:23](https://github.com/leanprover-community/mathlib/commit/106bd3b)
feat(group_theory/nilpotent): add nilpotent groups ([#8538](https://github.com/leanprover-community/mathlib/pull/8538))
We make basic definitions of nilpotent groups and prove the standard theorem that a group is nilpotent iff the upper resp. lower central series reaches top resp. bot.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.forall_coe

Added src/group_theory/nilpotent.lean
- \+ *lemma* ascending_central_series_le_upper
- \+ *lemma* descending_central_series_ge_lower
- \+ *def* is_ascending_central_series
- \+ *def* is_descending_central_series
- \+ *def* lower_central_series
- \+ *theorem* lower_central_series_is_descending_central_series
- \+ *lemma* mem_upper_central_series_step
- \+ *lemma* mem_upper_central_series_succ_iff
- \+ *theorem* nilpotent_iff_finite_ascending_central_series
- \+ *theorem* nilpotent_iff_finite_descending_central_series
- \+ *theorem* nilpotent_iff_lower_central_series
- \+ *def* upper_central_series
- \+ *def* upper_central_series_aux
- \+ *lemma* upper_central_series_is_ascending_central_series
- \+ *def* upper_central_series_step
- \+ *lemma* upper_central_series_step_eq_comap_center
- \+ *lemma* upper_central_series_zero_def



## [2021-08-16 16:19:22](https://github.com/leanprover-community/mathlib/commit/a55084f)
feat(data/fintype/basic): card_sum, card_subtype_or ([#8490](https://github.com/leanprover-community/mathlib/pull/8490))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_subtype
- \+ *lemma* fintype.card_subtype_or
- \+ *lemma* fintype.card_subtype_or_disjoint
- \+ *theorem* fintype.card_sum

Modified src/data/fintype/card.lean
- \- *theorem* fintype.card_sum



## [2021-08-16 16:19:21](https://github.com/leanprover-community/mathlib/commit/f8241b7)
feat(algebra/big_operators/basic): prod_subsingleton ([#8423](https://github.com/leanprover-community/mathlib/pull/8423))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_unique_nonempty
- \+ *lemma* fintype.prod_subsingleton
- \+ *lemma* fintype.prod_unique

Modified src/algebra/group/units.lean
- \+ *lemma* unique_has_one

Modified src/data/fintype/card.lean
- \- *lemma* fintype.prod_unique



## [2021-08-16 16:19:20](https://github.com/leanprover-community/mathlib/commit/e195347)
feat(finsupp/basic): lemmas about emb_domain ([#7883](https://github.com/leanprover-community/mathlib/pull/7883))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.emb_domain.add_monoid_hom
- \+ *lemma* finsupp.emb_domain_add
- \+ *lemma* finsupp.emb_domain_single



## [2021-08-16 15:18:10](https://github.com/leanprover-community/mathlib/commit/53d97e1)
puzzle(archive/oxford_invariants): Oxford Invariants Puzzle Challenges, Summer 2021, Week 3, Problem 1 ([#8656](https://github.com/leanprover-community/mathlib/pull/8656))
This is a formalisation of a problem posed by the Oxford Invariants.
Co-authored by @b-mehta
#### Estimated changes
Added archive/oxford_invariants/2021summer/week3_p1.lean
- \+ *theorem* week3_p1



## [2021-08-16 15:18:08](https://github.com/leanprover-community/mathlib/commit/55b2e86)
feat(analysis/normed_space): normed group hom completion ([#8499](https://github.com/leanprover-community/mathlib/pull/8499))
From LTE
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.mem_range_self
- \+ *lemma* normed_group_hom.surjective_on_with.exists_pos
- \+ *lemma* normed_group_hom.surjective_on_with.mono

Added src/analysis/normed_space/normed_group_hom_completion.lean
- \+ *lemma* normed_group.dense_range_to_compl
- \+ *lemma* normed_group.norm_to_compl
- \+ *def* normed_group.to_compl
- \+ *def* normed_group_hom.completion
- \+ *lemma* normed_group_hom.completion_add
- \+ *lemma* normed_group_hom.completion_coe
- \+ *lemma* normed_group_hom.completion_coe_to_fun
- \+ *lemma* normed_group_hom.completion_comp
- \+ *lemma* normed_group_hom.completion_def
- \+ *lemma* normed_group_hom.completion_id
- \+ *lemma* normed_group_hom.completion_neg
- \+ *lemma* normed_group_hom.completion_sub
- \+ *lemma* normed_group_hom.completion_to_compl
- \+ *lemma* normed_group_hom.ker_completion
- \+ *lemma* normed_group_hom.ker_le_ker_completion
- \+ *lemma* normed_group_hom.norm_completion
- \+ *lemma* normed_group_hom.zero_completion
- \+ *def* normed_group_hom_completion_hom



## [2021-08-16 15:18:07](https://github.com/leanprover-community/mathlib/commit/217308c)
feat(analysis): `x^y` is smooth as a function of `(x, y)` ([#8262](https://github.com/leanprover-community/mathlib/pull/8262))
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean
- \+ *lemma* has_deriv_at_of_has_deriv_at_of_ne'

Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.has_strict_fderiv_at_cpow'
- \+ *lemma* continuous.rpow
- \+ *lemma* continuous.rpow_const
- \+ *lemma* continuous_at.rpow
- \+ *lemma* continuous_at.rpow_const
- \+ *lemma* continuous_on.rpow
- \+ *lemma* continuous_on.rpow_const
- \+ *lemma* continuous_within_at.rpow
- \+ *lemma* continuous_within_at.rpow_const
- \- *lemma* deriv_rpow
- \+ *lemma* deriv_rpow_const
- \- *lemma* deriv_rpow_of_one_le
- \- *lemma* deriv_within_rpow
- \+ *lemma* deriv_within_rpow_const
- \- *lemma* deriv_within_rpow_of_one_le
- \+/\- *lemma* differentiable.rpow
- \+ *lemma* differentiable.rpow_const
- \- *lemma* differentiable.rpow_of_one_le
- \+/\- *lemma* differentiable_at.rpow
- \+ *lemma* differentiable_at.rpow_const
- \- *lemma* differentiable_at.rpow_of_one_le
- \+/\- *lemma* differentiable_on.rpow
- \+ *lemma* differentiable_on.rpow_const
- \- *lemma* differentiable_on.rpow_of_one_le
- \+/\- *lemma* differentiable_within_at.rpow
- \+ *lemma* differentiable_within_at.rpow_const
- \- *lemma* differentiable_within_at.rpow_of_one_le
- \+ *lemma* filter.tendsto.rpow
- \+ *lemma* filter.tendsto.rpow_const
- \+/\- *lemma* has_deriv_at.rpow
- \+ *lemma* has_deriv_at.rpow_const
- \- *lemma* has_deriv_at.rpow_of_one_le
- \+/\- *lemma* has_deriv_within_at.rpow
- \+ *lemma* has_deriv_within_at.rpow_const
- \- *lemma* has_deriv_within_at.rpow_of_one_le
- \+ *lemma* has_fderiv_at.const_rpow
- \+ *lemma* has_fderiv_at.rpow
- \+ *lemma* has_fderiv_at.rpow_const
- \+ *lemma* has_fderiv_within_at.const_rpow
- \+ *lemma* has_fderiv_within_at.rpow
- \+ *lemma* has_fderiv_within_at.rpow_const
- \+ *lemma* has_strict_deriv_at.rpow
- \+ *lemma* has_strict_fderiv_at.const_rpow
- \+ *lemma* has_strict_fderiv_at.rpow
- \+ *lemma* has_strict_fderiv_at.rpow_const
- \+ *lemma* real.abs_rpow_le_exp_log_mul
- \+/\- *lemma* real.continuous_at_rpow
- \+ *lemma* real.continuous_at_rpow_of_ne
- \- *lemma* real.continuous_at_rpow_of_ne_zero
- \+/\- *lemma* real.continuous_at_rpow_of_pos
- \- *lemma* real.continuous_rpow
- \- *lemma* real.continuous_rpow_aux1
- \- *lemma* real.continuous_rpow_aux2
- \- *lemma* real.continuous_rpow_aux3
- \- *lemma* real.continuous_rpow_of_ne_zero
- \- *lemma* real.continuous_rpow_of_pos
- \+ *lemma* real.deriv_rpow_const'
- \+ *lemma* real.deriv_rpow_const
- \+ *lemma* real.differentiable_at_rpow_of_ne
- \+ *lemma* real.differentiable_rpow_const
- \- *lemma* real.has_deriv_at_rpow
- \+ *lemma* real.has_deriv_at_rpow_const
- \- *lemma* real.has_deriv_at_rpow_of_neg
- \- *lemma* real.has_deriv_at_rpow_of_one_le
- \- *lemma* real.has_deriv_at_rpow_of_pos
- \- *lemma* real.has_deriv_at_rpow_zero_of_one_le
- \+ *lemma* real.has_strict_deriv_at_const_rpow
- \+ *lemma* real.has_strict_deriv_at_const_rpow_of_neg
- \+ *lemma* real.has_strict_deriv_at_rpow_const
- \+ *lemma* real.has_strict_deriv_at_rpow_const_of_ne
- \+ *lemma* real.has_strict_fderiv_at_rpow_of_neg
- \+ *lemma* real.has_strict_fderiv_at_rpow_of_pos
- \+ *lemma* real.rpow_add_int
- \+ *lemma* real.rpow_add_nat
- \+ *lemma* real.rpow_add_one
- \+ *lemma* real.rpow_sub_int
- \+ *lemma* real.rpow_sub_nat
- \+ *lemma* real.rpow_sub_one
- \+ *lemma* real.times_cont_diff_at_rpow_const
- \+ *lemma* real.times_cont_diff_at_rpow_const_of_le
- \+ *lemma* real.times_cont_diff_at_rpow_const_of_ne
- \+ *lemma* real.times_cont_diff_at_rpow_of_ne
- \+ *lemma* real.times_cont_diff_rpow_const_of_le
- \+ *lemma* times_cont_diff.rpow
- \+ *lemma* times_cont_diff.rpow_const_of_le
- \+ *lemma* times_cont_diff.rpow_const_of_ne
- \+ *lemma* times_cont_diff_at.rpow
- \+ *lemma* times_cont_diff_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_at.rpow_const_of_ne
- \+ *lemma* times_cont_diff_on.rpow
- \+ *lemma* times_cont_diff_on.rpow_const_of_le
- \+ *lemma* times_cont_diff_on.rpow_const_of_ne
- \+ *lemma* times_cont_diff_within_at.rpow
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_le
- \+ *lemma* times_cont_diff_within_at.rpow_const_of_ne



## [2021-08-16 13:12:47](https://github.com/leanprover-community/mathlib/commit/d6aae6c)
feat(tactic/abel): check for defeq of atoms instead of syntactic eq ([#8628](https://github.com/leanprover-community/mathlib/pull/8628))
I had a call to `abel` break after adding a new typeclass instance, and it turns out this was because two terms became defeq-but-not-syntactically-eq. This PR modifies the equality check in `abel` to follow the implementation in e.g. `ring`.
By default, `abel` now unifies atoms up to `reducible`, which should not have a huge impact on build times. Use `abel!` for trying to unify up to `semireducible`.
I also renamed the `tactic.abel.cache` to `tactic.abel.context`, since we store more things in there than a few elaborated terms. To appease the docstring linter, I added docs for all of the renamed `def`s.
#### Estimated changes
Modified src/tactic/abel.lean


Modified test/abel.lean
- \+ *def* id'



## [2021-08-16 11:55:51](https://github.com/leanprover-community/mathlib/commit/deedf25)
feat(algebra/lie/semisimple): adjoint action is injective for semisimple Lie algebras ([#8698](https://github.com/leanprover-community/mathlib/pull/8698))
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_algebra.ad_ker_eq_self_module_ker
- \- *lemma* lie_algebra.center_eq_adjoint_kernel
- \+ *lemma* lie_algebra.self_module_ker_eq_center

Modified src/algebra/lie/semisimple.lean
- \+ *lemma* lie_algebra.ad_ker_eq_bot_of_semisimple



## [2021-08-16 08:39:16](https://github.com/leanprover-community/mathlib/commit/c416a48)
feat(algebra/gcd_monoid): move the `gcd_monoid nat` instance ([#7180](https://github.com/leanprover-community/mathlib/pull/7180))
moves `gcd_monoid nat` instance, removes corresponding todos.
removes:
* `nat.normalize_eq` -- use `normalize_eq` instead
renames:
* `nat.gcd_eq_gcd` to `gcd_eq_nat_gcd`
* `nat.lcm_eq_lcm` to `lcm_eq_nat_lcm`
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \- *lemma* nat.gcd_eq_gcd
- \- *lemma* nat.lcm_eq_lcm
- \- *lemma* nat.normalize_eq

Modified src/group_theory/perm/cycle_type.lean


Modified src/ring_theory/int/basic.lean
- \+ *lemma* gcd_eq_nat_gcd
- \+ *lemma* lcm_eq_nat_lcm



## [2021-08-16 08:06:39](https://github.com/leanprover-community/mathlib/commit/2b43587)
feat(measure_theory/hausdorff_measure): Hausdorff measure and volume coincide in pi types ([#8554](https://github.com/leanprover-community/mathlib/pull/8554))
co-authored by Yury Kudryashov
#### Estimated changes
Modified src/measure_theory/measure/hausdorff.lean
- \+ *theorem* measure_theory.hausdorff_measure_pi_real
- \+ *lemma* measure_theory.measure.hausdorff_measure_le
- \+ *lemma* measure_theory.measure.le_hausdorff_measure
- \+ *lemma* measure_theory.measure.le_mk_metric
- \+ *lemma* measure_theory.outer_measure.le_mk_metric



## [2021-08-16 06:19:36](https://github.com/leanprover-community/mathlib/commit/a983f24)
fix(*): fix universe levels ([#8677](https://github.com/leanprover-community/mathlib/pull/8677))
The universe levels in the following declarations have been fixed . 
This means that there was an argument of the form `Type (max u v)` or `Sort (max u v)`, which could be generalized to `Type u` or `Sort u`. In a few cases, I made explicit that there is a universe restriction (sometimes `max u v` is legitimately used as an arbitrary universe level higher than `u`)
In some files I also cleaned up some declarations around these.
```
algebraic_geometry.Spec.SheafedSpace_map
algebraic_geometry.Spec.to_SheafedSpace
algebraic_geometry.Spec.to_PresheafedSpace
category_theory.discrete_is_connected_equiv_punit
writer_t.uliftable'
writer_t.uliftable
equiv.prod_equiv_of_equiv_nat
free_algebra.dim_eq
linear_equiv.alg_conj
module.flat
cardinal.add_def
slim_check.injective_function.mk
topological_add_group.of_nhds_zero'
topological_group.of_nhds_one'
topological_group.of_comm_of_nhds_one
topological_add_group.of_comm_of_nhds_zero
has_continuous_mul.of_nhds_one
has_continuous_add.of_nhds_zero
has_continuous_add_of_comm_of_nhds_zero
has_continuous_mul_of_comm_of_nhds_one
uniform_space_of_compact_t2
AddCommGroup.cokernel_iso_quotient
algebraic_geometry.Scheme
algebraic_geometry.Scheme.Spec_obj
simplex_category.skeletal_functor
category_theory.Type_to_Cat.full
CommMon_.equiv_lax_braided_functor_punit.lax_braided_to_CommMon
CommMon_.equiv_lax_braided_functor_punit.unit_iso
Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon
Mon_.equiv_lax_monoidal_functor_punit.unit_iso
uliftable.down_map
weak_dual.has_continuous_smul
stone_cech_equivalence
Compactum_to_CompHaus.full
TopCommRing.category_theory.forget₂.category_theory.reflects_isomorphisms
```
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean


Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* algebraic_geometry.Spec.SheafedSpace_map

Modified src/algebraic_topology/simplex_category.lean
- \+/\- *lemma* simplex_category.epi_iff_surjective
- \+/\- *lemma* simplex_category.ext
- \+/\- *def* simplex_category.is_skeleton_of
- \+/\- *def* simplex_category.len
- \+/\- *lemma* simplex_category.len_le_of_epi
- \+/\- *lemma* simplex_category.len_le_of_mono
- \+/\- *def* simplex_category.mk
- \+/\- *lemma* simplex_category.mk_len
- \+/\- *theorem* simplex_category.mono_iff_injective
- \+/\- *lemma* simplex_category.skeletal
- \+/\- *def* simplex_category.skeletal_functor
- \+/\- *def* simplex_category.truncated.inclusion
- \+/\- *def* simplex_category.truncated

Modified src/category_theory/category/Cat.lean


Modified src/category_theory/is_connected.lean
- \+/\- *def* category_theory.discrete_is_connected_equiv_punit

Modified src/category_theory/monoidal/CommMon_.lean
- \+/\- *def* CommMon_.equiv_lax_braided_functor_punit.CommMon_to_lax_braided
- \+/\- *def* CommMon_.equiv_lax_braided_functor_punit.lax_braided_to_CommMon
- \+/\- *def* CommMon_.equiv_lax_braided_functor_punit

Modified src/category_theory/monoidal/Mon_.lean
- \+/\- *def* Mon_.equiv_lax_monoidal_functor_punit.Mon_to_lax_monoidal
- \+/\- *def* Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon
- \+/\- *def* Mon_.equiv_lax_monoidal_functor_punit

Modified src/control/uliftable.lean
- \+/\- *def* cont_t.uliftable'
- \+/\- *def* reader_t.uliftable'
- \+/\- *def* state_t.uliftable'
- \+/\- *def* uliftable.down_map
- \+/\- *def* writer_t.uliftable'

Modified src/data/equiv/nat.lean
- \+/\- *def* equiv.prod_equiv_of_equiv_nat

Modified src/data/fin_enum.lean
- \+/\- *lemma* fin_enum.mem_pi
- \+/\- *def* fin_enum.pi.cons
- \+/\- *def* fin_enum.pi.enum
- \+/\- *lemma* fin_enum.pi.mem_enum
- \+/\- *def* fin_enum.pi.tail
- \+/\- *def* fin_enum.pi

Modified src/linear_algebra/free_algebra.lean
- \+/\- *lemma* free_algebra.dim_eq

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *def* alg_equiv_matrix'
- \+/\- *def* alg_equiv_matrix
- \+/\- *def* linear_equiv.alg_conj

Modified src/model_theory/basic.lean


Modified src/ring_theory/flat.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.add_def

Modified src/testing/slim_check/functions.lean
- \+/\- *def* slim_check.injective_function.apply
- \+/\- *lemma* slim_check.injective_function.apply_id_injective
- \+/\- *lemma* slim_check.injective_function.apply_id_mem_iff
- \+/\- *def* slim_check.injective_function.list.apply_id
- \+/\- *lemma* slim_check.injective_function.list.apply_id_cons
- \+/\- *lemma* slim_check.injective_function.list.apply_id_eq_self
- \+/\- *lemma* slim_check.injective_function.list.apply_id_zip_eq
- \+/\- *def* slim_check.injective_function.perm.slice
- \+/\- *def* slim_check.total_function.apply
- \+/\- *def* slim_check.total_function.list.to_finmap'
- \+/\- *def* slim_check.total_function.repr_aux

Modified src/topology/algebra/group.lean
- \+/\- *lemma* topological_group.of_comm_of_nhds_one
- \+/\- *lemma* topological_group.of_nhds_one'

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* has_continuous_mul.of_nhds_one
- \+/\- *lemma* has_continuous_mul_of_comm_of_nhds_one

Modified src/topology/algebra/weak_dual_topology.lean
- \+/\- *lemma* weak_dual.continuous_of_continuous_eval
- \+/\- *theorem* weak_dual.tendsto_iff_forall_eval_tendsto

Modified src/topology/category/CompHaus/default.lean
- \+/\- *lemma* CompHaus.is_closed_map
- \+/\- *lemma* CompHaus.is_iso_of_bijective
- \+/\- *def* CompHaus.iso_of_bijective

Modified src/topology/category/Compactum.lean
- \+/\- *def* Compactum_to_CompHaus.full

Modified src/topology/category/TopCommRing.lean


Modified src/topology/uniform_space/compact_separated.lean
- \+/\- *def* uniform_space_of_compact_t2
- \+/\- *lemma* unique_uniformity_of_compact_t2



## [2021-08-16 05:42:56](https://github.com/leanprover-community/mathlib/commit/69785fe)
chore(scripts): update nolints.txt ([#8696](https://github.com/leanprover-community/mathlib/pull/8696))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-08-16 03:52:43](https://github.com/leanprover-community/mathlib/commit/b97344c)
chore(algebra/module): Swap the naming of `smul_(left|right)_injective` to match the naming guide ([#8659](https://github.com/leanprover-community/mathlib/pull/8659))
The naming conventions say:
> An injectivity lemma that uses "left" or "right" should refer to the argument that "changes". For example, a lemma with the statement `a - b = a - c ↔ b = c` could be called `sub_right_inj`.
This corrects the name of `function.injective (λ c : R, c • x)` to be `smul_left_injective` instead of the previous `smul_right_injective`, and vice versa for `function.injective (λ x : M, r • x)`.
This also brings it in line with `mul_left_injective` and `mul_right_injective`.
#### Estimated changes
Modified src/algebra/algebra/tower.lean


Modified src/algebra/module/basic.lean
- \+/\- *lemma* smul_left_injective
- \+/\- *lemma* smul_right_injective

Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/conformal_linear_map.lean


Modified src/group_theory/complement.lean
- \- *lemma* subgroup.smul_injective
- \+ *lemma* subgroup.smul_left_injective

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/tensor_product.lean




## [2021-08-16 03:52:42](https://github.com/leanprover-community/mathlib/commit/2e9029f)
feat(tactic/ext): add tracing option ([#8633](https://github.com/leanprover-community/mathlib/pull/8633))
Adds an option to trace all lemmas that `ext` tries to apply, along with the time each attempted application takes. This was useful in debugging a slow `ext` call.
#### Estimated changes
Modified src/tactic/ext.lean




## [2021-08-16 02:20:04](https://github.com/leanprover-community/mathlib/commit/59954c1)
docs(data/pfun): add module docstring and def docstrings ([#8629](https://github.com/leanprover-community/mathlib/pull/8629))
#### Estimated changes
Modified src/data/pfun.lean
- \+/\- *def* pfun.core
- \+/\- *lemma* pfun.core_def
- \+/\- *lemma* pfun.core_res
- \+/\- *lemma* pfun.core_restrict
- \+/\- *theorem* pfun.dom_iff_graph
- \+/\- *def* pfun.image
- \+/\- *lemma* pfun.image_def
- \+/\- *lemma* pfun.mem_core
- \+/\- *lemma* pfun.mem_image
- \+/\- *lemma* pfun.mem_preimage
- \+/\- *def* pfun.preimage
- \+/\- *lemma* pfun.preimage_def
- \+/\- *theorem* pfun.pure_defined
- \+/\- *def* pfun.ran
- \+/\- *def* pfun



## [2021-08-16 02:20:03](https://github.com/leanprover-community/mathlib/commit/46b3fae)
feat(topology/category/*/projective): CompHaus and Profinite have enough projectives ([#8613](https://github.com/leanprover-community/mathlib/pull/8613))
#### Estimated changes
Modified docs/references.bib


Renamed src/topology/category/CompHaus.lean to src/topology/category/CompHaus/default.lean
- \+ *lemma* CompHaus.epi_iff_surjective
- \+ *lemma* CompHaus.mono_iff_injective

Added src/topology/category/CompHaus/projective.lean
- \+ *def* CompHaus.projective_presentation

Modified src/topology/category/Profinite/default.lean
- \+ *lemma* Profinite.epi_iff_surjective
- \+ *lemma* Profinite.mono_iff_injective

Added src/topology/category/Profinite/projective.lean
- \+ *def* Profinite.projective_presentation

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.compact_space
- \+ *lemma* homeomorph.t2_space

Modified src/topology/stone_cech.lean




## [2021-08-16 02:20:02](https://github.com/leanprover-community/mathlib/commit/4bf5177)
feat(algebraic_geometry/EllipticCurve): add working definition of elliptic curve ([#8558](https://github.com/leanprover-community/mathlib/pull/8558))
The word "elliptic curve" is used in the literature in many different ways. Differential geometers use it to mean a 1-dimensional complex torus. Algebraic geometers nowadays use it to mean some morphism of schemes with a section and some axioms. However classically number theorists used to use a low-brow definition of the form y^2=cubic in x; this works great when the base scheme is, for example, Spec of the rationals. 
It occurred to me recently that the standard minor modification of the low-brow definition works for all commutative rings with trivial Picard group, and because this covers a lot of commutative rings (e.g. all fields, all PIDs, all integral domains with trivial class group) it would not be unreasonable to have it as a working definition in mathlib. The advantage of this definition is that people will be able to begin writing algorithms which compute various invariants of the curve, for example we can begin to formally verify the database of elliptic curves at LMFDB.org .
#### Estimated changes
Modified docs/references.bib


Added src/algebraic_geometry/EllipticCurve.lean
- \+ *def* EllipticCurve.disc
- \+ *def* EllipticCurve.disc_aux
- \+ *lemma* EllipticCurve.disc_is_unit
- \+ *def* EllipticCurve.j



## [2021-08-16 01:12:19](https://github.com/leanprover-community/mathlib/commit/ec68c7e)
feat(set_theory/cardinal): lift_sup ([#8675](https://github.com/leanprover-community/mathlib/pull/8675))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.lift_sup
- \+ *lemma* cardinal.lift_sup_le
- \+ *lemma* cardinal.lift_sup_le_iff
- \+ *lemma* cardinal.lift_sup_le_lift_sup



## [2021-08-16 00:24:41](https://github.com/leanprover-community/mathlib/commit/462359d)
feat(measure): prove Haar measure = Lebesgue measure on R ([#8639](https://github.com/leanprover-community/mathlib/pull/8639))
#### Estimated changes
Added src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* measure_theory.haar_measure_eq_lebesgue_measure
- \+ *lemma* measure_theory.is_add_left_invariant_real_volume
- \+ *def* topological_space.positive_compacts.Icc01



## [2021-08-15 23:17:23](https://github.com/leanprover-community/mathlib/commit/8e50863)
chore(analysis/normed_space/dual): golf some proofs ([#8694](https://github.com/leanprover-community/mathlib/pull/8694))
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+/\- *lemma* normed_space.double_dual_bound
- \+/\- *lemma* normed_space.dual_def
- \- *def* normed_space.inclusion_in_double_dual'
- \+ *lemma* normed_space.inclusion_in_double_dual_norm_eq
- \+ *lemma* normed_space.inclusion_in_double_dual_norm_le



## [2021-08-15 21:24:22](https://github.com/leanprover-community/mathlib/commit/8ac0242)
feat(topology/algebra/ring): pi instances ([#8686](https://github.com/leanprover-community/mathlib/pull/8686))
Add instances `pi.topological_ring` and `pi.topological_semiring`.
#### Estimated changes
Modified src/topology/algebra/ring.lean




## [2021-08-15 21:24:21](https://github.com/leanprover-community/mathlib/commit/9af80f3)
feat(algebra/opposites): more scalar action instances ([#8672](https://github.com/leanprover-community/mathlib/pull/8672))
This adds weaker and stronger versions of `monoid.to_opposite_mul_action` for `has_mul`, `monoid_with_zero`, and `semiring`. It also adds an `smul_comm_class` instance.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/opposites.lean
- \+/\- *lemma* opposite.op_smul_eq_mul

Modified src/algebra/smul_with_zero.lean




## [2021-08-15 21:24:20](https://github.com/leanprover-community/mathlib/commit/fc7da8d)
chore(data/vector3): extract to a new file ([#8669](https://github.com/leanprover-community/mathlib/pull/8669))
This is simply a file move, with no other changes other than a minimal docstring.
In it's old location this was very hard to find.
#### Estimated changes
Added src/data/vector3.lean
- \+ *theorem* exists_vector_succ
- \+ *theorem* exists_vector_zero
- \+ *def* vector3.append
- \+ *theorem* vector3.append_add
- \+ *theorem* vector3.append_cons
- \+ *theorem* vector3.append_insert
- \+ *theorem* vector3.append_left
- \+ *theorem* vector3.append_nil
- \+ *def* vector3.cons
- \+ *def* vector3.cons_elim
- \+ *theorem* vector3.cons_elim_cons
- \+ *theorem* vector3.cons_fs
- \+ *theorem* vector3.cons_fz
- \+ *theorem* vector3.cons_head_tail
- \+ *theorem* vector3.eq_nil
- \+ *def* vector3.head
- \+ *def* vector3.insert
- \+ *theorem* vector3.insert_fs
- \+ *theorem* vector3.insert_fz
- \+ *def* vector3.nil
- \+ *def* vector3.nil_elim
- \+ *def* vector3.nth
- \+ *def* vector3.of_fn
- \+ *theorem* vector3.rec_on_cons
- \+ *theorem* vector3.rec_on_nil
- \+ *def* vector3.tail
- \+ *def* vector3
- \+ *def* vector_all
- \+ *theorem* vector_all_iff_forall
- \+ *theorem* vector_allp.imp
- \+ *def* vector_allp
- \+ *theorem* vector_allp_cons
- \+ *theorem* vector_allp_iff_forall
- \+ *theorem* vector_allp_nil
- \+ *theorem* vector_allp_singleton
- \+ *def* vector_ex
- \+ *theorem* vector_ex_iff_exists

Modified src/number_theory/dioph.lean
- \- *theorem* exists_vector_succ
- \- *theorem* exists_vector_zero
- \- *def* vector3.append
- \- *theorem* vector3.append_add
- \- *theorem* vector3.append_cons
- \- *theorem* vector3.append_insert
- \- *theorem* vector3.append_left
- \- *theorem* vector3.append_nil
- \- *def* vector3.cons
- \- *def* vector3.cons_elim
- \- *theorem* vector3.cons_elim_cons
- \- *theorem* vector3.cons_fs
- \- *theorem* vector3.cons_fz
- \- *theorem* vector3.cons_head_tail
- \- *theorem* vector3.eq_nil
- \- *def* vector3.head
- \- *def* vector3.insert
- \- *theorem* vector3.insert_fs
- \- *theorem* vector3.insert_fz
- \- *def* vector3.nil
- \- *def* vector3.nil_elim
- \- *def* vector3.nth
- \- *def* vector3.of_fn
- \- *theorem* vector3.rec_on_cons
- \- *theorem* vector3.rec_on_nil
- \- *def* vector3.tail
- \- *def* vector3
- \- *def* vector_all
- \- *theorem* vector_all_iff_forall
- \- *theorem* vector_allp.imp
- \- *def* vector_allp
- \- *theorem* vector_allp_cons
- \- *theorem* vector_allp_iff_forall
- \- *theorem* vector_allp_nil
- \- *theorem* vector_allp_singleton
- \- *def* vector_ex
- \- *theorem* vector_ex_iff_exists



## [2021-08-15 21:24:18](https://github.com/leanprover-community/mathlib/commit/6aefa38)
chore(topology/algebra/*,analysis/specific_limits): continuity of `fpow` ([#8665](https://github.com/leanprover-community/mathlib/pull/8665))
* add more API lemmas about continuity of `x ^ n` for natural and integer `n`;
* prove that `x⁻¹` and `x ^ n`, `n < 0`, are discontinuous at zero.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* inv_surjective

Modified src/analysis/fourier.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* normed_field.continuous_at_fpow
- \+ *lemma* normed_field.continuous_at_inv
- \+ *lemma* normed_field.tendsto_norm_fpow_nhds_within_0_at_top
- \+/\- *lemma* normed_field.tendsto_norm_inverse_nhds_within_0_at_top

Modified src/topology/algebra/group_with_zero.lean
- \+/\- *lemma* continuous.fpow
- \+/\- *lemma* continuous_at.fpow
- \+/\- *lemma* continuous_at_fpow
- \+ *lemma* continuous_on.fpow
- \+ *lemma* continuous_within_at.fpow
- \+/\- *lemma* filter.tendsto.fpow
- \- *lemma* tendsto_fpow

Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_at.pow
- \+ *lemma* continuous_at_pow
- \+ *lemma* continuous_on.pow
- \+ *lemma* continuous_within_at.pow
- \+ *lemma* filter.tendsto.pow



## [2021-08-15 21:24:18](https://github.com/leanprover-community/mathlib/commit/fddc1f4)
doc(tactic/congr): improve convert_to docs ([#8664](https://github.com/leanprover-community/mathlib/pull/8664))
The docs should explain how `convert` and `convert_to` differ.
#### Estimated changes
Modified src/tactic/congr.lean




## [2021-08-15 19:29:26](https://github.com/leanprover-community/mathlib/commit/ca5987f)
chore(data/set/basic): add `image_image` and `preimage_preimage` to `function.left_inverse` ([#8688](https://github.com/leanprover-community/mathlib/pull/8688))
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* function.left_inverse.image_image
- \+ *lemma* function.left_inverse.preimage_preimage



## [2021-08-15 13:05:32](https://github.com/leanprover-community/mathlib/commit/bf6eeb2)
feat(data/list/cycle): cycle.map and has_repr ([#8170](https://github.com/leanprover-community/mathlib/pull/8170))
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *def* cycle.lists
- \+ *def* cycle.map
- \+ *lemma* cycle.mem_lists_iff_coe_eq

Modified src/data/list/rotate.lean
- \+ *theorem* list.is_rotated.map
- \+ *lemma* list.map_rotate

Added test/cycle.lean




## [2021-08-15 07:43:38](https://github.com/leanprover-community/mathlib/commit/0bb283b)
feat(algebra/bounds): add `csupr_mul` etc ([#8584](https://github.com/leanprover-community/mathlib/pull/8584))
* add `csupr_mul`, `mul_csupr`, `csupr_div`, `csupr_add`,
  `mul_csupr`, `add_csupr`, `csupr_sub`;
* add `is_lub_csupr`, `is_lub_csupr_set`, `is_glb_cinfi`,
  `is_glb_cinfi_set`;
* add `is_lub.csupr_eq`, `is_lub.csupr_set_eq`, `is_glb.cinfi_eq`,
  `is_glb.cinfi_set_eq`;
* add `is_greatest.Sup_mem`, `is_least.Inf_mem`;
* add lemmas about `galois_connection` and `Sup`/`Inf` in
  conditionally complete lattices;
* add lemmas about `order_iso` and `Sup`/`Inf` in conditionally
  complete lattices.
#### Estimated changes
Modified src/algebra/bounds.lean
- \+ *lemma* csupr_div
- \+ *lemma* csupr_mul
- \+ *lemma* mul_csupr

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* galois_connection.l_cSup
- \+ *lemma* galois_connection.l_csupr
- \+ *lemma* galois_connection.l_csupr_set
- \+ *lemma* galois_connection.u_cInf
- \+ *lemma* galois_connection.u_cinfi
- \+ *lemma* galois_connection.u_cinfi_set
- \+ *lemma* is_glb.cinfi_eq
- \+ *lemma* is_glb.cinfi_set_eq
- \+ *lemma* is_glb_cinfi
- \+ *lemma* is_glb_cinfi_set
- \+ *lemma* is_greatest.Sup_mem
- \+ *lemma* is_least.Inf_mem
- \+ *lemma* is_lub.csupr_eq
- \+ *lemma* is_lub.csupr_set_eq
- \+ *lemma* is_lub_csupr
- \+ *lemma* is_lub_csupr_set
- \+ *lemma* order_iso.map_cInf
- \+ *lemma* order_iso.map_cSup
- \+ *lemma* order_iso.map_cinfi
- \+ *lemma* order_iso.map_cinfi_set
- \+ *lemma* order_iso.map_csupr
- \+ *lemma* order_iso.map_csupr_set



## [2021-08-15 02:59:48](https://github.com/leanprover-community/mathlib/commit/b7d980c)
feat(topology/algebra/weak_dual_topology + analysis/normed_space/weak_dual_of_normed_space): add definition and first lemmas about weak-star topology ([#8598](https://github.com/leanprover-community/mathlib/pull/8598))
Add definition and first lemmas about weak-star topology.
#### Estimated changes
Added src/analysis/normed_space/weak_dual.lean
- \+ *def* normed_space.dual.continuous_linear_map_to_weak_dual
- \+ *theorem* normed_space.dual.dual_norm_topology_le_weak_dual_topology
- \+ *def* normed_space.dual.to_weak_dual
- \+ *theorem* normed_space.dual.to_weak_dual_continuous
- \+ *lemma* normed_space.dual.to_weak_dual_eq_iff
- \+ *lemma* weak_dual.coe_to_fun_eq_normed_coe_to_fun
- \+ *def* weak_dual.to_normed_dual
- \+ *lemma* weak_dual.to_normed_dual_eq_iff

Added src/topology/algebra/weak_dual_topology.lean
- \+ *lemma* weak_dual.coe_fn_continuous
- \+ *lemma* weak_dual.continuous_of_continuous_eval
- \+ *lemma* weak_dual.eval_continuous
- \+ *theorem* weak_dual.tendsto_iff_forall_eval_tendsto
- \+ *def* weak_dual



## [2021-08-15 02:18:05](https://github.com/leanprover-community/mathlib/commit/ff721ad)
chore(scripts): update nolints.txt ([#8676](https://github.com/leanprover-community/mathlib/pull/8676))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-15 00:01:46](https://github.com/leanprover-community/mathlib/commit/708d99a)
feat(data/real/ennreal): add `to_real_sub_of_le` ([#8674](https://github.com/leanprover-community/mathlib/pull/8674))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_real_sub_of_le



## [2021-08-15 00:01:45](https://github.com/leanprover-community/mathlib/commit/4644447)
fix(tactic/norm_cast): assumption_mod_cast should only work on one goal ([#8649](https://github.com/leanprover-community/mathlib/pull/8649))
fixes [#8438](https://github.com/leanprover-community/mathlib/pull/8438)
#### Estimated changes
Modified src/tactic/norm_cast.lean


Modified test/norm_cast.lean
- \+ *lemma* b



## [2021-08-14 23:29:05](https://github.com/leanprover-community/mathlib/commit/c4208d2)
chore(measure_theory): fix namespace in docstrings for docgen ([#8671](https://github.com/leanprover-community/mathlib/pull/8671))
#### Estimated changes
Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/signed_hahn.lean


Modified src/measure_theory/measure/vector_measure.lean




## [2021-08-14 13:38:26](https://github.com/leanprover-community/mathlib/commit/8f863f6)
feat(measure_theory/decomposition/jordan): the Jordan decomposition theorem for signed measures ([#8645](https://github.com/leanprover-community/mathlib/pull/8645))
This PR proves the Jordan decomposition theorem for signed measures, that is, given a signed measure `s`, there exists a unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.
#### Estimated changes
Added src/measure_theory/decomposition/jordan.lean
- \+ *lemma* measure_theory.jordan_decomposition.exists_compl_positive_negative
- \+ *lemma* measure_theory.jordan_decomposition.neg_neg_part
- \+ *lemma* measure_theory.jordan_decomposition.neg_pos_part
- \+ *lemma* measure_theory.jordan_decomposition.to_jordan_decomposition_to_signed_measure
- \+ *def* measure_theory.jordan_decomposition.to_signed_measure
- \+ *theorem* measure_theory.jordan_decomposition.to_signed_measure_injective
- \+ *lemma* measure_theory.jordan_decomposition.to_signed_measure_neg
- \+ *lemma* measure_theory.jordan_decomposition.to_signed_measure_zero
- \+ *lemma* measure_theory.jordan_decomposition.zero_neg_part
- \+ *lemma* measure_theory.jordan_decomposition.zero_pos_part
- \+ *lemma* measure_theory.signed_measure.of_diff_eq_zero_of_symm_diff_eq_zero_negative
- \+ *lemma* measure_theory.signed_measure.of_diff_eq_zero_of_symm_diff_eq_zero_positive
- \+ *lemma* measure_theory.signed_measure.of_inter_eq_of_symm_diff_eq_zero_negative
- \+ *lemma* measure_theory.signed_measure.of_inter_eq_of_symm_diff_eq_zero_positive
- \+ *lemma* measure_theory.signed_measure.subset_negative_null_set
- \+ *lemma* measure_theory.signed_measure.subset_positive_null_set
- \+ *def* measure_theory.signed_measure.to_jordan_decomposition
- \+ *def* measure_theory.signed_measure.to_jordan_decomposition_equiv
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_neg
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_spec
- \+ *lemma* measure_theory.signed_measure.to_jordan_decomposition_zero
- \+ *lemma* measure_theory.signed_measure.to_signed_measure_to_jordan_decomposition

Modified src/measure_theory/measure/vector_measure.lean
- \- *def* measure_theory.measure.sub_to_signed_measure
- \- *lemma* measure_theory.measure.sub_to_signed_measure_apply
- \+ *lemma* measure_theory.measure.to_signed_measure_eq_to_signed_measure_iff
- \+ *lemma* measure_theory.measure.to_signed_measure_sub_apply
- \+ *lemma* measure_theory.vector_measure.of_diff_of_diff_eq_zero



## [2021-08-14 11:55:36](https://github.com/leanprover-community/mathlib/commit/ba76bf7)
chore(data/option,data/set): a few lemmas, golf ([#8636](https://github.com/leanprover-community/mathlib/pull/8636))
* add `option.subsingleton_iff_is_empty` and an instance
  `option.unique`;
* add `set.is_compl_range_some_none`, `set.compl_range_some`,
  `set.range_some_inter_none`, `set.range_some_union_none`;
* split the proof of `set.pairwise_on_eq_iff_exists_eq` into
  `set.nonempty.pairwise_on_eq_iff_exists_eq` and
  `set.pairwise_on_eq_iff_exists_eq`.
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)
#### Estimated changes
Modified src/data/option/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.compl_range_some
- \+ *lemma* set.is_compl_range_some_none
- \+ *theorem* set.nonempty.pairwise_on_eq_iff_exists_eq
- \+ *theorem* set.nonempty.pairwise_on_iff_exists_forall
- \+ *lemma* set.pairwise_on_iff_exists_forall
- \+ *lemma* set.range_some_inter_none
- \+ *lemma* set.range_some_union_none

Modified src/logic/relation.lean


Modified src/logic/unique.lean
- \+ *lemma* option.subsingleton_iff_is_empty



## [2021-08-14 10:40:01](https://github.com/leanprover-community/mathlib/commit/721f571)
feat(linear_algebra/basic) : add a small lemma for simplifying a map between equivalent quotient spaces ([#8640](https://github.com/leanprover-community/mathlib/pull/8640))
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.equiv_quotient_of_eq_mk

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.quot_equiv_of_eq_mk

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.quot_equiv_of_eq_mk



## [2021-08-14 06:36:18](https://github.com/leanprover-community/mathlib/commit/c765b04)
chore(data/(int, nat)/modeq): rationalize lemma names ([#8644](https://github.com/leanprover-community/mathlib/pull/8644))
Many `modeq` lemmas were called `nat.modeq.modeq_something` or `int.modeq.modeq_something`. I'm deleting the duplicated `modeq`, so that lemmas (usually) become `nat.modeq.something` and `int.modeq.something`. Most of them must be `protected`.
This facilitates greatly the use of dot notation on `nat.modeq` and `int.modeq` while shortening lemma names.
I'm adding a few lemmas:
* `nat.modeq.rfl`, `int.modeq.rfl`
* `nat.modeq.dvd`, `int.modeq.dvd`
* `nat.modeq_of_dvd`, `int.modeq_of_dvd`
* `has_dvd.dvd.modeq_zero_nat`, `has_dvd.dvd.zero_modeq_nat`, `has_dvd.dvd.modeq_zero_int`, `has_dvd.dvd.zero_modeq_int`
* `nat.modeq.add_left`, `nat.modeq.add_right`, `int.modeq.add_left`, `int.modeq.add_right`
* `nat.modeq.add_left_cancel'`, `nat.modeq.add_right_cancel'`, `int.modeq.add_left_cancel'`, `int.modeq.add_right_cancel'`
* `int.modeq.sub_left`, `int.modeq.sub_right`
* `nat.modeq_sub`, `int.modeq_sub`
* `int.modeq_one`
* `int.modeq_pow`
I'm also renaming some lemmas (on top of the general renaming):
* `add_cancel_left` -> `add_left_cancel`, `add_cancel_right` -> `add_right_cancel`
* `modeq_zero_iff` -> `modeq_zero_iff_dvd` in prevision of an upcoming PR
#### Estimated changes
Modified archive/imo/imo1964_q1.lean


Modified archive/miu_language/decision_suf.lean


Modified src/algebra/char_p/basic.lean


Modified src/data/int/modeq.lean
- \+ *lemma* has_dvd.dvd.modeq_zero_int
- \+ *lemma* has_dvd.dvd.zero_modeq_int
- \+ *lemma* int.coe_nat_modeq_iff
- \+ *lemma* int.exists_unique_equiv
- \+ *lemma* int.exists_unique_equiv_nat
- \+ *lemma* int.gcd_a_modeq
- \+ *lemma* int.mod_coprime
- \+ *theorem* int.mod_modeq
- \- *lemma* int.modeq.coe_nat_modeq_iff
- \+ *theorem* int.modeq.dvd
- \- *lemma* int.modeq.exists_unique_equiv
- \- *lemma* int.modeq.exists_unique_equiv_nat
- \- *lemma* int.modeq.gcd_a_modeq
- \- *lemma* int.modeq.mod_coprime
- \- *theorem* int.modeq.mod_modeq
- \- *theorem* int.modeq.modeq_add
- \- *theorem* int.modeq.modeq_add_cancel_left
- \- *theorem* int.modeq.modeq_add_cancel_right
- \- *theorem* int.modeq.modeq_add_fac
- \- *lemma* int.modeq.modeq_and_modeq_iff_modeq_mul
- \- *theorem* int.modeq.modeq_iff_dvd
- \- *theorem* int.modeq.modeq_mul
- \- *theorem* int.modeq.modeq_mul_left'
- \- *theorem* int.modeq.modeq_mul_left
- \- *theorem* int.modeq.modeq_mul_right'
- \- *theorem* int.modeq.modeq_mul_right
- \- *theorem* int.modeq.modeq_neg
- \- *theorem* int.modeq.modeq_of_dvd_of_modeq
- \- *theorem* int.modeq.modeq_of_modeq_mul_left
- \- *theorem* int.modeq.modeq_of_modeq_mul_right
- \- *theorem* int.modeq.modeq_sub
- \- *theorem* int.modeq.modeq_zero_iff
- \+ *theorem* int.modeq.of_modeq_mul_left
- \+ *theorem* int.modeq.of_modeq_mul_right
- \+ *theorem* int.modeq_add_fac
- \+ *lemma* int.modeq_and_modeq_iff_modeq_mul
- \+ *theorem* int.modeq_iff_dvd
- \+ *theorem* int.modeq_of_dvd
- \+ *theorem* int.modeq_one
- \+ *lemma* int.modeq_sub
- \+ *theorem* int.modeq_zero_iff_dvd

Modified src/data/int/parity.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/modeq.lean
- \+ *lemma* has_dvd.dvd.modeq_zero_nat
- \+ *lemma* has_dvd.dvd.zero_modeq_nat
- \+ *def* nat.chinese_remainder'
- \+ *def* nat.chinese_remainder
- \+ *lemma* nat.coprime_of_mul_modeq_one
- \+ *theorem* nat.mod_modeq
- \- *def* nat.modeq.chinese_remainder'
- \- *def* nat.modeq.chinese_remainder
- \- *lemma* nat.modeq.coprime_of_mul_modeq_one
- \- *theorem* nat.modeq.dvd_of_modeq
- \- *theorem* nat.modeq.mod_modeq
- \- *theorem* nat.modeq.modeq_add
- \- *theorem* nat.modeq.modeq_add_cancel_left
- \- *theorem* nat.modeq.modeq_add_cancel_right
- \- *lemma* nat.modeq.modeq_and_modeq_iff_modeq_mul
- \- *theorem* nat.modeq.modeq_iff_dvd'
- \- *theorem* nat.modeq.modeq_iff_dvd
- \- *theorem* nat.modeq.modeq_mul
- \- *theorem* nat.modeq.modeq_mul_left'
- \- *theorem* nat.modeq.modeq_mul_left
- \- *theorem* nat.modeq.modeq_mul_right'
- \- *theorem* nat.modeq.modeq_mul_right
- \- *theorem* nat.modeq.modeq_of_dvd
- \- *theorem* nat.modeq.modeq_of_dvd_of_modeq
- \- *theorem* nat.modeq.modeq_of_modeq_mul_left
- \- *theorem* nat.modeq.modeq_of_modeq_mul_right
- \- *theorem* nat.modeq.modeq_one
- \- *theorem* nat.modeq.modeq_pow
- \- *theorem* nat.modeq.modeq_zero_iff
- \+ *theorem* nat.modeq.of_modeq_mul_left
- \+ *theorem* nat.modeq.of_modeq_mul_right
- \+ *lemma* nat.modeq_and_modeq_iff_modeq_mul
- \+ *theorem* nat.modeq_iff_dvd'
- \+ *theorem* nat.modeq_iff_dvd
- \+ *theorem* nat.modeq_of_dvd
- \+ *theorem* nat.modeq_one
- \+ *lemma* nat.modeq_sub
- \+ *theorem* nat.modeq_zero_iff_dvd

Modified src/data/nat/totient.lean


Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.val_le

Modified src/dynamics/ergodic/conservative.lean


Modified src/group_theory/p_group.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/primes_congruent_one.lean




## [2021-08-14 04:51:40](https://github.com/leanprover-community/mathlib/commit/679a8a7)
docs(data/int/basic): add module docstring ([#8655](https://github.com/leanprover-community/mathlib/pull/8655))
#### Estimated changes
Modified src/data/int/basic.lean




## [2021-08-14 02:16:22](https://github.com/leanprover-community/mathlib/commit/36826cb)
chore(scripts): update nolints.txt ([#8666](https://github.com/leanprover-community/mathlib/pull/8666))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-14 02:16:21](https://github.com/leanprover-community/mathlib/commit/1b1088c)
feat(linear_algeba/linear_independent): coe_range ([#8341](https://github.com/leanprover-community/mathlib/pull/8341))
#### Estimated changes
Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.coe_range



## [2021-08-14 00:25:39](https://github.com/leanprover-community/mathlib/commit/50d3de9)
feat(logic/basic): a few lemmas about `xor` ([#8650](https://github.com/leanprover-community/mathlib/pull/8650))
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* xor_comm
- \+ *theorem* xor_false
- \+ *theorem* xor_self
- \+ *theorem* xor_true



## [2021-08-13 21:43:57](https://github.com/leanprover-community/mathlib/commit/94e4667)
feat(order/filter): change definition of inf ([#8657](https://github.com/leanprover-community/mathlib/pull/8657))
The current definition of `filter.inf` came directly from the Galois insertion: `u ∈ f ⊓ g` if it contains `s ∩ t` for some `s ∈ f` and `t ∈ g`, but the new one is tidier: `u ∈ f ⊓ g` if `u = s ∩ t` for some `s ∈ f` and `t ∈ g`. This gives a stronger assertion to work with when assuming a set belongs to a filter inf. On the other hand it makes it harder to prove such a statement so we keep the old version as a lemma `filter.mem_inf_of_inter :  ∀ {f g : filter α} {s t u : set α}, s ∈ f → t ∈ g → s ∩ t ⊆ u → u ∈ f ⊓ g`.
Also renames lots of lemmas to remove the word "sets" that was a remnant of the very early days.
In passing I also changed the simp lemma `filter.mem_map` from  `t ∈ map m f ↔ {x | m x ∈ t} ∈ f` to 
`t ∈ map m f ↔ m ⁻¹' t ∈ f` which seemed more normal form to me. But this led to a lot of breakage, so I also kept the old version as `mem_map'`.
#### Estimated changes
Modified roadmap/topology/paracompact.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/data/analysis/filter.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.union_distrib_bInter_left
- \+ *lemma* set.union_distrib_bInter_right

Modified src/dynamics/omega_limit.lean


Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/bump_function.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/geometry/manifold/whitney_embedding.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.Inter_mem
- \- *lemma* filter.Inter_mem_sets
- \+ *lemma* filter.bInter_finset_mem
- \- *lemma* filter.bInter_finset_mem_sets
- \+ *lemma* filter.bInter_mem
- \- *lemma* filter.bInter_mem_sets
- \+ *lemma* filter.compl_not_mem
- \- *lemma* filter.compl_not_mem_sets
- \- *lemma* filter.empty_in_sets_eq_bot
- \+ *lemma* filter.empty_mem_iff_bot
- \- *lemma* filter.empty_nmem_sets
- \+ *lemma* filter.empty_not_mem
- \+ *lemma* filter.eq_Inf_of_mem_iff_exists_mem
- \- *lemma* filter.eq_Inf_of_mem_sets_iff_exists_mem
- \+ *lemma* filter.eq_binfi_of_mem_iff_exists_mem
- \- *lemma* filter.eq_binfi_of_mem_sets_iff_exists_mem
- \+ *lemma* filter.eq_infi_of_mem_iff_exists_mem
- \- *lemma* filter.eq_infi_of_mem_sets_iff_exists_mem
- \+ *lemma* filter.eventually_inf
- \+/\- *lemma* filter.eventually_true
- \+ *lemma* filter.exists_mem_subset_iff
- \- *lemma* filter.exists_sets_subset_iff
- \+ *lemma* filter.forall_mem_nonempty_iff_ne_bot
- \- *lemma* filter.forall_sets_nonempty_iff_ne_bot
- \+ *lemma* filter.image_coe_mem_of_mem_comap
- \- *lemma* filter.image_coe_mem_sets
- \+ *lemma* filter.image_mem_of_mem_comap
- \- *lemma* filter.image_mem_sets
- \+ *lemma* filter.inter_mem
- \+ *lemma* filter.inter_mem_iff
- \+ *lemma* filter.inter_mem_inf
- \- *lemma* filter.inter_mem_inf_sets
- \- *lemma* filter.inter_mem_sets
- \- *lemma* filter.inter_mem_sets_iff
- \+ *lemma* filter.mem_Sup
- \- *lemma* filter.mem_Sup_sets
- \+ *lemma* filter.mem_bind'
- \+ *lemma* filter.mem_bind
- \- *lemma* filter.mem_bind_sets'
- \- *lemma* filter.mem_bind_sets
- \- *lemma* filter.mem_binfi
- \+ *lemma* filter.mem_binfi_of_directed
- \+ *lemma* filter.mem_bot
- \- *lemma* filter.mem_bot_sets
- \+ *theorem* filter.mem_comap
- \- *theorem* filter.mem_comap_sets
- \+ *lemma* filter.mem_inf_iff
- \+ *lemma* filter.mem_inf_iff_superset
- \+ *lemma* filter.mem_inf_of_inter
- \+ *lemma* filter.mem_inf_of_left
- \+ *lemma* filter.mem_inf_of_right
- \- *lemma* filter.mem_inf_sets
- \- *lemma* filter.mem_inf_sets_of_left
- \- *lemma* filter.mem_inf_sets_of_right
- \+ *lemma* filter.mem_infi'
- \+/\- *lemma* filter.mem_infi
- \+ *lemma* filter.mem_infi_finset
- \- *lemma* filter.mem_infi_iff'
- \- *lemma* filter.mem_infi_iff
- \+ *lemma* filter.mem_infi_of_directed
- \+ *lemma* filter.mem_infi_of_mem
- \- *lemma* filter.mem_infi_sets
- \- *lemma* filter.mem_infi_sets_finset
- \+ *lemma* filter.mem_join
- \- *lemma* filter.mem_join_sets
- \+ *lemma* filter.mem_map'
- \+/\- *lemma* filter.mem_map
- \+ *lemma* filter.mem_map_iff_exists_image
- \- *lemma* filter.mem_map_sets_iff
- \+ *lemma* filter.mem_of_eq_bot
- \+ *lemma* filter.mem_of_superset
- \+ *lemma* filter.mem_principal
- \- *lemma* filter.mem_principal_sets
- \+ *lemma* filter.mem_pure
- \- *lemma* filter.mem_pure_sets
- \+ *lemma* filter.mem_seq_def
- \+ *lemma* filter.mem_seq_iff
- \- *lemma* filter.mem_seq_sets_def
- \- *lemma* filter.mem_seq_sets_iff
- \- *lemma* filter.mem_sets_of_eq_bot
- \- *lemma* filter.mem_sets_of_superset
- \+ *lemma* filter.mem_sup
- \- *lemma* filter.mem_sup_sets
- \+ *lemma* filter.mem_supr
- \- *lemma* filter.mem_supr_sets
- \+ *lemma* filter.mem_top
- \+ *lemma* filter.mem_top_iff_forall
- \- *lemma* filter.mem_top_sets
- \- *lemma* filter.mem_top_sets_iff_forall
- \+ *lemma* filter.mem_traverse
- \+ *lemma* filter.mem_traverse_iff
- \- *lemma* filter.mem_traverse_sets
- \- *lemma* filter.mem_traverse_sets_iff
- \+ *lemma* filter.monotone_mem
- \- *lemma* filter.monotone_mem_sets
- \+ *lemma* filter.mp_mem
- \- *lemma* filter.mp_sets
- \+ *lemma* filter.nonempty_of_mem
- \- *lemma* filter.nonempty_of_mem_sets
- \+ *lemma* filter.sInter_mem
- \- *lemma* filter.sInter_mem_sets
- \+ *lemma* filter.seq_mem_seq
- \- *lemma* filter.seq_mem_seq_sets
- \+ *lemma* filter.singleton_mem_pure
- \- *lemma* filter.singleton_mem_pure_sets
- \+ *lemma* filter.univ_mem'
- \+ *lemma* filter.univ_mem
- \- *lemma* filter.univ_mem_sets'
- \- *lemma* filter.univ_mem_sets

Modified src/order/filter/cofinite.lean


Modified src/order/filter/countable_Inter.lean
- \+ *lemma* countable_bInter_mem
- \- *lemma* countable_bInter_mem_sets

Modified src/order/filter/extr.lean


Modified src/order/filter/lift.lean


Modified src/order/filter/partial.lean


Modified src/order/filter/pointwise.lean


Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* ultrafilter.empty_not_mem
- \+ *lemma* ultrafilter.mem_pure
- \- *lemma* ultrafilter.mem_pure_sets
- \+/\- *lemma* ultrafilter.nonempty_of_mem

Modified src/order/liminf_limsup.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/ordered/liminf_limsup.lean


Modified src/topology/algebra/uniform_field.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/extend_from.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/ereal.lean


Modified src/topology/instances/real.lean


Modified src/topology/list.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/order.lean


Modified src/topology/partition_of_unity.lean


Modified src/topology/path_connected.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* mem_map_iff_exists_image'
- \- *lemma* mem_map_sets_iff'

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-08-13 20:14:43](https://github.com/leanprover-community/mathlib/commit/fdeb064)
feat(topology/*): lemmas about `dense`/`dense_range` and `is_(pre)connected` ([#8651](https://github.com/leanprover-community/mathlib/pull/8651))
* add `dense_compl_singleton`;
* extract new lemma `is_preconnected_range` from the proof of
  `is_connected_range`;
* add `dense_range.preconnected_space` and
  `dense_inducing.preconnected_space`;
* rename `self_sub_closure_image_preimage_of_open` to
  `self_subset_closure_image_preimage_of_open`.
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* dense.open_subset_closure_inter
- \+ *lemma* dense_compl_singleton
- \+ *lemma* dense_range.subset_closure_image_preimage_of_is_open

Modified src/topology/connected.lean
- \+ *lemma* dense_range.preconnected_space
- \+ *lemma* is_preconnected_range

Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_inducing.closure_image_mem_nhds
- \- *lemma* dense_inducing.closure_image_nhds_of_nhds
- \+ *lemma* dense_inducing.preconnected_space
- \- *lemma* dense_inducing.self_sub_closure_image_preimage_of_open



## [2021-08-13 18:20:13](https://github.com/leanprover-community/mathlib/commit/8b9c4cf)
fix(tactic/core): fix incorrect uses of with_ident_list ([#8653](https://github.com/leanprover-community/mathlib/pull/8653))
`with_ident_list` uses `tk "with" >> ident_*`, which is incorrect for some tactics, where `_` doesn't mean anything. (It is good for tactics that name hypotheses like `cases`, but not tactics that use the list to reference hypotheses like `revert_deps`.)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean




## [2021-08-13 18:20:12](https://github.com/leanprover-community/mathlib/commit/7f5d5b9)
feat(ring_theory): ideals in a Dedekind domain have unique factorization ([#8530](https://github.com/leanprover-community/mathlib/pull/8530))
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \- *theorem* fractional_ideal.mul_inv_cancel
- \+ *lemma* ideal.dvd_iff_le
- \+ *lemma* ideal.dvd_not_unit_iff_lt

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.is_unit_iff
- \+ *lemma* ideal.le_of_dvd



## [2021-08-13 17:03:29](https://github.com/leanprover-community/mathlib/commit/8eca293)
feat(field_theory): more general `algebra _ (algebraic_closure k)` instance ([#8658](https://github.com/leanprover-community/mathlib/pull/8658))
For example, now we can take a field extension `L / K` and map `x : K` into the algebraic closure of `L`.
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* algebraic_closure.algebra_map_def



## [2021-08-13 17:03:28](https://github.com/leanprover-community/mathlib/commit/c711909)
feat(linear_algebra/basic, group_theory/quotient_group, algebra/lie/quotient): ext lemmas for morphisms out of quotients ([#8641](https://github.com/leanprover-community/mathlib/pull/8641))
This allows `ext` to see through quotients by subobjects of a type `A`, and apply ext lemmas specific to `A`.
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_module_hom.congr_fun

Modified src/algebra/lie/quotient.lean
- \+ *lemma* lie_submodule.quotient.lie_module_hom_ext
- \+ *def* lie_submodule.quotient.mk'

Modified src/algebra/ring_quot.lean


Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.monoid_hom_ext
- \+ *lemma* quotient_group.quotient_map_subgroup_of_of_le_coe

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.linear_map_qext

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.quotient.ring_hom_ext



## [2021-08-13 15:23:28](https://github.com/leanprover-community/mathlib/commit/9e83de2)
feat(data/list/perm): subperm_ext_iff ([#8504](https://github.com/leanprover-community/mathlib/pull/8504))
A helper lemma to construct proofs of `l <+~ l'`. On the way to proving
`l ~ l' -> l.permutations ~ l'.permutations`.
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *lemma* list.subperm.cons_left
- \+ *lemma* list.subperm.cons_right
- \+ *lemma* list.subperm_append_diff_self_of_count_le
- \+ *lemma* list.subperm_ext_iff



## [2021-08-13 08:01:49](https://github.com/leanprover-community/mathlib/commit/733e6e3)
chore(*): update lean to 3.32.1 ([#8652](https://github.com/leanprover-community/mathlib/pull/8652))
#### Estimated changes
Modified archive/miu_language/decision_suf.lean


Modified leanpkg.toml


Modified src/analysis/convex/caratheodory.lean


Modified src/data/bitvec/core.lean


Modified src/data/fin.lean
- \+/\- *def* fin.cast_add

Modified src/data/fin2.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/sort.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/nat_antidiagonal.lean


Modified src/data/list/nodup.lean


Modified src/data/list/of_fn.lean


Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean


Modified src/data/list/range.lean


Modified src/data/list/zip.lean


Modified src/data/matrix/notation.lean


Modified src/data/multiset/fold.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/choose/basic.lean


Modified src/data/nat/choose/dvd.lean


Modified src/data/nat/dist.lean


Modified src/data/nat/factorial.lean


Modified src/data/nat/fib.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/log.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/pow.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/psub.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/bitwise.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/pfunctor/univariate/M.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/logic/function/iterate.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/order/filter/at_top_bot.lean


Modified src/ring_theory/multiplicity.lean


Modified src/set_theory/lists.lean


Modified src/system/random/basic.lean


Modified src/tactic/core.lean


Modified src/testing/slim_check/gen.lean




## [2021-08-13 06:38:14](https://github.com/leanprover-community/mathlib/commit/03ddb8d)
feat(finsupp/basic): restrict a finitely supported function on option A to A ([#8342](https://github.com/leanprover-community/mathlib/pull/8342))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.prod_option_index
- \+ *def* finsupp.some
- \+ *lemma* finsupp.some_add
- \+ *lemma* finsupp.some_apply
- \+ *lemma* finsupp.some_single_none
- \+ *lemma* finsupp.some_single_some
- \+ *lemma* finsupp.some_zero
- \+ *lemma* finsupp.sum_option_index_smul



## [2021-08-13 05:15:52](https://github.com/leanprover-community/mathlib/commit/d0804ba)
feat(linear_algebra/invariant_basis_number): basic API lemmas ([#7882](https://github.com/leanprover-community/mathlib/pull/7882))
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_equiv.coe_symm_mk

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* finsupp.linear_equiv_fun_on_fintype_single
- \+ *lemma* finsupp.linear_equiv_fun_on_fintype_symm_coe
- \+/\- *lemma* finsupp.linear_equiv_fun_on_fintype_symm_single

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/invariant_basis_number.lean
- \+ *lemma* card_eq_of_lequiv
- \+ *lemma* card_le_of_injective'
- \+ *lemma* card_le_of_injective
- \+ *lemma* card_le_of_surjective'
- \+ *lemma* card_le_of_surjective



## [2021-08-13 02:17:49](https://github.com/leanprover-community/mathlib/commit/3b37614)
chore(scripts): update nolints.txt ([#8654](https://github.com/leanprover-community/mathlib/pull/8654))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-12 19:28:31](https://github.com/leanprover-community/mathlib/commit/4a864ed)
fix(tactic/core): mk_simp_attribute: remove superfluous disjunct ([#8648](https://github.com/leanprover-community/mathlib/pull/8648))
`with_ident_list` already returns `[]` if `with` is not present.
#### Estimated changes
Modified src/tactic/core.lean




## [2021-08-12 19:28:30](https://github.com/leanprover-community/mathlib/commit/ce26133)
feat(data/nat/(basic, modeq)): simple lemmas ([#8647](https://github.com/leanprover-community/mathlib/pull/8647))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_sub_sub_cancel

Modified src/data/nat/modeq.lean
- \+ *lemma* nat.add_modeq_left
- \+ *lemma* nat.add_modeq_right
- \+ *lemma* nat.modeq_zero_iff



## [2021-08-12 19:28:29](https://github.com/leanprover-community/mathlib/commit/c2580eb)
refactor(tactic/*): mark internal attrs as `parser := failed` ([#8635](https://github.com/leanprover-community/mathlib/pull/8635))
I saw this trick in some of the other user attributes, and it seems like a good idea to apply generally. Any attribute that is "internal use only" should have its `parser` field set to `failed`, so that it is impossible for the user to write the attribute. It is still possible for meta code to set the attributes programmatically, which is generally what's happening anyway.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/alias.lean


Modified src/tactic/doc_commands.lean


Modified src/tactic/lift.lean


Modified src/tactic/localized.lean


Modified src/tactic/simps.lean




## [2021-08-12 19:28:28](https://github.com/leanprover-community/mathlib/commit/8a2a630)
feat(analysis/convex/basic): add lemma add_smul regarding linear combinations of convex sets ([#8608](https://github.com/leanprover-community/mathlib/pull/8608))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.add_smul



## [2021-08-12 19:28:27](https://github.com/leanprover-community/mathlib/commit/2412b97)
feat(algebra/quaternion_basis): add a quaternion version of complex.lift ([#8551](https://github.com/leanprover-community/mathlib/pull/8551))
This is some prework to show `clifford_algebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂]` for an appropriate `Q`.
For `complex.lift : {I' // I' * I' = -1} ≃ (ℂ →ₐ[ℝ] A)`, we could just use a subtype. For quaternions, we now have two generators and three relations, so a subtype isn't particularly viable any more; so instead this commit creates a new `quaternion_algebra.basis` structure.
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* quaternion_algebra.algebra_map_eq
- \+ *def* quaternion_algebra.im_i_lm
- \+ *def* quaternion_algebra.im_j_lm
- \+ *def* quaternion_algebra.im_k_lm
- \+ *def* quaternion_algebra.re_lm

Added src/algebra/quaternion_basis.lean
- \+ *def* quaternion_algebra.basis.comp_hom
- \+ *lemma* quaternion_algebra.basis.i_mul_k
- \+ *lemma* quaternion_algebra.basis.j_mul_k
- \+ *lemma* quaternion_algebra.basis.k_mul_i
- \+ *lemma* quaternion_algebra.basis.k_mul_j
- \+ *lemma* quaternion_algebra.basis.k_mul_k
- \+ *def* quaternion_algebra.basis.lift
- \+ *lemma* quaternion_algebra.basis.lift_add
- \+ *def* quaternion_algebra.basis.lift_hom
- \+ *lemma* quaternion_algebra.basis.lift_mul
- \+ *lemma* quaternion_algebra.basis.lift_one
- \+ *lemma* quaternion_algebra.basis.lift_smul
- \+ *lemma* quaternion_algebra.basis.lift_zero
- \+ *def* quaternion_algebra.lift



## [2021-08-12 19:28:26](https://github.com/leanprover-community/mathlib/commit/8914b68)
feat(ring_theory/dedekind_domain): ideals in a DD are cancellative  ([#8513](https://github.com/leanprover-community/mathlib/pull/8513))
This PR provides a `comm_cancel_monoid_with_zero` instance on integral ideals in a Dedekind domain.
As a bonus, it deletes an out of date TODO comment.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean




## [2021-08-12 17:46:21](https://github.com/leanprover-community/mathlib/commit/0f59141)
docs(data/fintype/sort): add module docstring ([#8643](https://github.com/leanprover-community/mathlib/pull/8643))
And correct typo in the docstrings
#### Estimated changes
Modified src/data/fintype/sort.lean
- \+/\- *def* mono_equiv_of_fin



## [2021-08-12 17:46:20](https://github.com/leanprover-community/mathlib/commit/3689655)
feat(measure_theory/stieltjes_measure): Stieltjes measures associated to monotone functions ([#8266](https://github.com/leanprover-community/mathlib/pull/8266))
Given a monotone right-continuous real function `f`, there exists a measure giving mass `f b - f a` to the interval `(a, b]`. These measures are called Stieltjes measures, and are especially important in probability theory. The real Lebesgue measure is a particular case of this construction, for `f x = x`. This PR extends the already existing construction of the Lebesgue measure to cover all Stieltjes measures.
#### Estimated changes
Modified docs/overview.yaml


Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ioc_diff_Ioi
- \+ *lemma* set.Ioc_inter_Ioi
- \+ *lemma* set.Ioc_subset_Ioc_iff

Modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* measure_theory.borel_le_lebesgue_measurable
- \- *lemma* measure_theory.is_lebesgue_measurable_Iio
- \- *def* measure_theory.lebesgue_length
- \- *lemma* measure_theory.lebesgue_length_Icc
- \- *lemma* measure_theory.lebesgue_length_Ico
- \- *lemma* measure_theory.lebesgue_length_Ioo
- \- *lemma* measure_theory.lebesgue_length_empty
- \- *lemma* measure_theory.lebesgue_length_eq_infi_Icc
- \- *lemma* measure_theory.lebesgue_length_eq_infi_Ioo
- \- *lemma* measure_theory.lebesgue_length_mono
- \- *lemma* measure_theory.lebesgue_length_subadditive
- \- *def* measure_theory.lebesgue_outer
- \- *lemma* measure_theory.lebesgue_outer_Icc
- \- *lemma* measure_theory.lebesgue_outer_Ico
- \- *lemma* measure_theory.lebesgue_outer_Ioc
- \- *lemma* measure_theory.lebesgue_outer_Ioo
- \- *lemma* measure_theory.lebesgue_outer_le_length
- \- *lemma* measure_theory.lebesgue_outer_singleton
- \- *theorem* measure_theory.lebesgue_outer_trim
- \- *theorem* measure_theory.lebesgue_to_outer_measure
- \+/\- *lemma* real.volume_Icc
- \+/\- *lemma* real.volume_Ico
- \+/\- *lemma* real.volume_Ioc
- \+/\- *lemma* real.volume_Ioo
- \+/\- *lemma* real.volume_singleton
- \+/\- *theorem* real.volume_val

Added src/measure_theory/measure/stieltjes.lean
- \+ *lemma* stieltjes_function.borel_le_measurable
- \+ *lemma* stieltjes_function.id_left_lim
- \+ *lemma* stieltjes_function.le_left_lim
- \+ *def* stieltjes_function.left_lim
- \+ *lemma* stieltjes_function.left_lim_le
- \+ *lemma* stieltjes_function.left_lim_le_left_lim
- \+ *def* stieltjes_function.length
- \+ *lemma* stieltjes_function.length_Ioc
- \+ *lemma* stieltjes_function.length_empty
- \+ *lemma* stieltjes_function.length_mono
- \+ *lemma* stieltjes_function.length_subadditive_Icc_Ioo
- \+ *lemma* stieltjes_function.measurable_set_Ioi
- \+ *lemma* stieltjes_function.measure_Icc
- \+ *lemma* stieltjes_function.measure_Ico
- \+ *lemma* stieltjes_function.measure_Ioc
- \+ *lemma* stieltjes_function.measure_Ioo
- \+ *lemma* stieltjes_function.measure_singleton
- \+ *lemma* stieltjes_function.mono
- \+ *lemma* stieltjes_function.outer_Ioc
- \+ *lemma* stieltjes_function.outer_le_length
- \+ *theorem* stieltjes_function.outer_trim
- \+ *lemma* stieltjes_function.right_continuous
- \+ *lemma* stieltjes_function.tendsto_left_lim

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* monotone.tendsto_nhds_within_Iio
- \+ *lemma* monotone.tendsto_nhds_within_Ioi



## [2021-08-12 16:55:31](https://github.com/leanprover-community/mathlib/commit/7b27f46)
feat(measure_theory/vector_measure): a signed measure restricted on a positive set is a unsigned measure ([#8597](https://github.com/leanprover-community/mathlib/pull/8597))
This PR defines `signed_measure.to_measure` which is the measure corresponding to a signed measure restricted on some positive set. This definition is useful for the Jordan decomposition theorem.
#### Estimated changes
Modified src/measure_theory/measure/vector_measure.lean
- \+ *lemma* measure_theory.measure.to_signed_measure_to_measure_of_zero_le
- \+ *lemma* measure_theory.measure.zero_le_to_signed_measure
- \+ *def* measure_theory.signed_measure.to_measure_of_le_zero
- \+ *lemma* measure_theory.signed_measure.to_measure_of_le_zero_apply
- \+ *lemma* measure_theory.signed_measure.to_measure_of_le_zero_to_signed_measure
- \+ *def* measure_theory.signed_measure.to_measure_of_zero_le'
- \+ *def* measure_theory.signed_measure.to_measure_of_zero_le
- \+ *lemma* measure_theory.signed_measure.to_measure_of_zero_le_apply
- \+ *lemma* measure_theory.signed_measure.to_measure_of_zero_le_to_signed_measure
- \+ *lemma* measure_theory.vector_measure.le_restrict_univ_iff_le
- \+ *lemma* measure_theory.vector_measure.neg_le_neg
- \+ *lemma* measure_theory.vector_measure.neg_le_neg_iff

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.coe_tsum_of_nonneg
- \+ *lemma* nnreal.summable_coe_of_nonneg



## [2021-08-12 15:02:55](https://github.com/leanprover-community/mathlib/commit/ee18995)
feat(algebra/group_with_zero): `units.mk0` is a "monoid hom" ([#8625](https://github.com/leanprover-community/mathlib/pull/8625))
This PR shows that `units.mk0` sends `1` to `1` and `x * y` to `mk0 x * mk0 y`. So it is a monoid hom, if we ignore the proof fields.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean


Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* units.mk0_mul
- \+ *lemma* units.mk0_one



## [2021-08-12 15:02:54](https://github.com/leanprover-community/mathlib/commit/e17e9ea)
feat(measure_theory/lp_space): add mem_Lp and integrable lemmas for is_R_or_C.re/im and inner product with a constant ([#8615](https://github.com/leanprover-community/mathlib/pull/8615))
#### Estimated changes
Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_im_le_norm
- \+ *lemma* is_R_or_C.norm_re_le_norm

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.const_inner
- \+ *lemma* measure_theory.integrable.im
- \+ *lemma* measure_theory.integrable.inner_const
- \+ *lemma* measure_theory.integrable.re

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.const_inner
- \+ *lemma* measure_theory.mem_ℒp.im
- \+ *lemma* measure_theory.mem_ℒp.inner_const
- \+ *lemma* measure_theory.mem_ℒp.re



## [2021-08-12 13:21:49](https://github.com/leanprover-community/mathlib/commit/f63c27b)
feat(linear_algebra): Smith normal form for submodules over a PID ([#8588](https://github.com/leanprover-community/mathlib/pull/8588))
This PR expands on `submodule.basis_of_pid` by showing that this basis can be chosen in "Smith normal form". That is: if `M` is a free module over a PID `R` and `N ≤ M`, then we can choose a basis `bN` for `N` and `bM` for `M`, such that the inclusion map from `N` to `M` expressed in these bases is a diagonal matrix in Smith normal form.
The rather gnarly induction in the original `submodule.basis_of_pid` has been turned into an even gnarlier auxiliary lemma that does the inductive step (with the induction hypothesis broken into pieces so we can apply it part by part), followed by a re-proven `submodule.basis_of_pid` that picks out part of this inductive step. Then we feed the full induction hypothesis, along with `submodule.basis_of_pid` into the same induction again, to get `submodule.exists_smith_normal_form_of_le`, and from that we conclude our new results `submodule.exists_smith_normal_form` and `ideal.exists_smith_normal_form`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_le_succ

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.coe_mk_fin_cons
- \+ *lemma* basis.coe_mk_fin_cons_of_le

Modified src/linear_algebra/free_module_pid.lean
- \+ *lemma* basis.card_le_card_of_le
- \+ *lemma* basis.card_le_card_of_submodule
- \+ *lemma* dvd_generator_iff
- \+ *lemma* eq_bot_of_generator_maximal_submodule_image_eq_zero
- \+ *lemma* generator_maximal_submodule_image_dvd
- \+ *lemma* generator_submodule_image_dvd_of_mem
- \+ *theorem* ideal.exists_smith_normal_form
- \+ *lemma* ideal.rank_eq
- \+ *lemma* linear_map.mem_submodule_image
- \+ *lemma* linear_map.mem_submodule_image_of_le
- \+ *def* linear_map.submodule_image
- \+ *lemma* linear_map.submodule_image_apply_of_le
- \+ *lemma* submodule.basis_of_pid_aux
- \+ *lemma* submodule.basis_of_pid_bot
- \+ *theorem* submodule.exists_smith_normal_form_of_le
- \+ *lemma* submodule.nonempty_basis_of_pid

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.eq_of_smul_apply_eq_smul_apply



## [2021-08-12 09:52:50](https://github.com/leanprover-community/mathlib/commit/e245b24)
feat(data/nat/prime, number_theory/padics/padic_norm): list of prime_pow_factors, valuation of prime power ([#8473](https://github.com/leanprover-community/mathlib/pull/8473))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.factors_pow

Modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* padic_val_nat_prime_pow
- \+ *lemma* padic_val_nat_self



## [2021-08-12 08:32:26](https://github.com/leanprover-community/mathlib/commit/1b96e97)
feat(data/sym2): card of `sym2 α` ([#8426](https://github.com/leanprover-community/mathlib/pull/8426))
Case `n = 2` of stars and bars
#### Estimated changes
Added src/data/sym/card.lean
- \+ *lemma* sym2.card_image_diag
- \+ *lemma* sym2.card_image_off_diag
- \+ *lemma* sym2.card_subtype_diag
- \+ *lemma* sym2.card_subtype_not_diag
- \+ *lemma* sym2.two_mul_card_image_off_diag

Modified src/data/sym/sym2.lean
- \+ *lemma* sym2.diag_injective
- \+ *lemma* sym2.filter_image_quotient_mk_is_diag
- \+ *lemma* sym2.filter_image_quotient_mk_not_is_diag



## [2021-08-12 07:04:01](https://github.com/leanprover-community/mathlib/commit/c550e3a)
refactor(group_theory/sylow): make new file about actions of p groups and move lemmas there ([#8595](https://github.com/leanprover-community/mathlib/pull/8595))
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.mem_fixed_points_iff_card_orbit_eq_one

Added src/group_theory/p_group.lean
- \+ *lemma* mul_action.card_modeq_card_fixed_points
- \+ *lemma* mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
- \+ *lemma* mul_action.nonempty_fixed_point_of_prime_not_dvd_card

Modified src/group_theory/sylow.lean
- \- *lemma* mul_action.card_modeq_card_fixed_points
- \- *lemma* mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
- \- *lemma* mul_action.mem_fixed_points_iff_card_orbit_eq_one
- \- *lemma* mul_action.nonempty_fixed_point_of_prime_not_dvd_card



## [2021-08-12 07:04:00](https://github.com/leanprover-community/mathlib/commit/0cbab37)
feat(group_theory/subgroup): there are finitely many subgroups of a finite group ([#8593](https://github.com/leanprover-community/mathlib/pull/8593))
#### Estimated changes
Renamed src/data/set_like.lean to src/data/set_like/basic.lean


Added src/data/set_like/fintype.lean


Modified src/group_theory/group_action/sub_mul_action.lean


Modified src/group_theory/submonoid/basic.lean


Modified src/model_theory/basic.lean


Modified src/order/closure.lean




## [2021-08-12 07:03:59](https://github.com/leanprover-community/mathlib/commit/cd2b549)
chore(measure_theory/*): make measurable_space arguments implicit, determined by the measure argument ([#8571](https://github.com/leanprover-community/mathlib/pull/8571))
In the measure theory library, most of the definitions that depend on a measure have that form:
```
def example_def {α} [measurable_space α] (μ : measure α) : some_type := sorry
```
Suppose now that we have two `measurable_space` structures on `α` : `{m m0 : measurable_space α}` and we have the measures `μ : measure α` (which is a measure on `m0`) and `μm : @measure α m`. This will be common for probability theory applications. See for example the `conditional_expectation` file.
Then we can write `example_def μ` but we cannot write `example_def μm` because the `measurable_space` inferred is `m0`, which does not match the measurable space on which `μm` is defined. We have to use `@example_def _ m μm` instead.
This PR implements a simple fix: change `[measurable_space α] (μ : measure α)` into `{m : measurable_space α} (μ : measure α)`.
Advantage: we can now use `example_def μm` since the `measurable_space` argument is deduced from the `measure` argument. This removes many `@` in all places where `measure.trim` is used.
Downsides:
- I have to write `(0 : measure α)` instead of `0` in some lemmas.
- I had to add two `apply_instance` to find `borel_space` instances.
- Whenever a lemma takes an explicit measure argument, we have to write `{m : measurable_space α} (μ : measure α)` instead of simply `(μ : measure α)`.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *def* measure_theory.Lp_meas_to_Lp_trim
- \+/\- *def* measure_theory.Lp_trim_to_Lp_meas
- \+/\- *lemma* measure_theory.Lp_trim_to_Lp_meas_ae_eq
- \+/\- *lemma* measure_theory.mem_Lp_meas_to_Lp_of_trim

Modified src/measure_theory/function/ess_sup.lean
- \+/\- *def* ess_inf
- \+/\- *lemma* ess_inf_antimono_measure
- \+/\- *lemma* ess_inf_measure_zero
- \+/\- *def* ess_sup
- \+/\- *lemma* ess_sup_measure_zero
- \+/\- *lemma* ess_sup_mono_measure
- \+/\- *lemma* order_iso.ess_inf_apply
- \+/\- *lemma* order_iso.ess_sup_apply

Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* integrable_zero_measure
- \+/\- *def* measure_theory.has_finite_integral
- \+/\- *lemma* measure_theory.has_finite_integral_zero_measure
- \+/\- *lemma* measure_theory.integrable.trim
- \+/\- *def* measure_theory.integrable
- \+/\- *lemma* measure_theory.integrable_of_forall_fin_meas_le'
- \+/\- *lemma* measure_theory.integrable_of_integrable_trim

Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* measure_theory.Lp.mem_Lp_const
- \+/\- *def* measure_theory.Lp
- \+/\- *lemma* measure_theory.coe_nnnorm_ae_le_snorm_ess_sup
- \+/\- *lemma* measure_theory.ess_sup_trim
- \+/\- *lemma* measure_theory.limsup_trim
- \+/\- *lemma* measure_theory.mem_ℒp.ae_measurable
- \+/\- *lemma* measure_theory.mem_ℒp.mono_measure
- \+/\- *lemma* measure_theory.mem_ℒp.to_Lp_zero
- \+/\- *def* measure_theory.mem_ℒp
- \+/\- *lemma* measure_theory.mem_ℒp_of_mem_ℒp_trim
- \+/\- *def* measure_theory.snorm'
- \+/\- *lemma* measure_theory.snorm'_le_snorm'_of_exponent_le
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_exponent_zero
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_neg
- \+/\- *lemma* measure_theory.snorm'_measure_zero_of_pos
- \+/\- *lemma* measure_theory.snorm'_mono_measure
- \+/\- *lemma* measure_theory.snorm'_trim
- \+/\- *def* measure_theory.snorm
- \+/\- *def* measure_theory.snorm_ess_sup
- \+/\- *lemma* measure_theory.snorm_ess_sup_measure_zero
- \+/\- *lemma* measure_theory.snorm_ess_sup_mono_measure
- \+/\- *lemma* measure_theory.snorm_ess_sup_trim
- \+/\- *lemma* measure_theory.snorm_measure_zero
- \+/\- *lemma* measure_theory.snorm_mono_measure
- \+/\- *lemma* measure_theory.snorm_trim
- \+/\- *lemma* measure_theory.snorm_trim_ae

Modified src/measure_theory/integral/bochner.lean
- \+/\- *def* measure_theory.integral
- \+/\- *lemma* measure_theory.integral_dirac'
- \+/\- *lemma* measure_theory.integral_dirac
- \+/\- *lemma* measure_theory.integral_trim_ae
- \+/\- *lemma* measure_theory.integral_zero_measure
- \+/\- *def* measure_theory.simple_func.integral
- \+/\- *lemma* measure_theory.simple_func.integral_eq_sum_filter
- \+/\- *lemma* measure_theory.simple_func.integral_eq_sum_of_subset

Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *def* measure_theory.lintegral
- \+/\- *lemma* measure_theory.lintegral_add_measure
- \+/\- *lemma* measure_theory.lintegral_eq_nnreal
- \+/\- *lemma* measure_theory.lintegral_mono'
- \+/\- *lemma* measure_theory.lintegral_mono_set'
- \+/\- *lemma* measure_theory.lintegral_mono_set
- \+/\- *lemma* measure_theory.lintegral_sum_measure
- \+/\- *lemma* measure_theory.lintegral_zero_measure
- \+/\- *def* measure_theory.measure.with_density
- \+/\- *lemma* measure_theory.monotone_lintegral
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.map_iff
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp.of_map
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp_iff
- \+/\- *lemma* measure_theory.simple_func.fin_meas_supp_iff_support
- \+/\- *def* measure_theory.simple_func.lintegral
- \+/\- *theorem* measure_theory.simple_func.lintegral_eq_lintegral
- \+/\- *lemma* measure_theory.simple_func.lintegral_map_equiv
- \+/\- *lemma* measure_theory.simple_func.lintegral_mono
- \+/\- *lemma* measure_theory.simple_func.lintegral_restrict
- \+/\- *lemma* measure_theory.simple_func.lintegral_sum
- \+/\- *lemma* measure_theory.simple_func.lintegral_zero
- \+/\- *def* measure_theory.simple_func.lintegralₗ
- \+/\- *lemma* measure_theory.simple_func.support_eq

Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* ae_measurable_zero_measure
- \+/\- *lemma* measure_theory.ae_map_mem_range
- \+/\- *lemma* measure_theory.ae_mono
- \+/\- *lemma* measure_theory.ae_zero
- \+/\- *lemma* measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure
- \+/\- *lemma* measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure
- \+/\- *lemma* measure_theory.ext_of_generate_finite
- \+/\- *def* measure_theory.measure.absolutely_continuous
- \+/\- *theorem* measure_theory.measure.add_apply
- \+/\- *theorem* measure_theory.measure.add_to_outer_measure
- \+/\- *theorem* measure_theory.measure.coe_add
- \+/\- *theorem* measure_theory.measure.coe_nnreal_smul
- \+/\- *theorem* measure_theory.measure.coe_smul
- \+/\- *theorem* measure_theory.measure.coe_zero
- \+/\- *def* measure_theory.measure.cofinite
- \+/\- *def* measure_theory.measure.comap
- \+/\- *lemma* measure_theory.measure.comap_apply
- \+/\- *lemma* measure_theory.measure.eq_zero_of_not_nonempty
- \+/\- *lemma* measure_theory.measure.finite_at_bot
- \+/\- *lemma* measure_theory.measure.finite_at_filter.exists_mem_basis
- \+/\- *def* measure_theory.measure.finite_at_filter
- \+/\- *lemma* measure_theory.measure.finite_at_filter_of_finite
- \+/\- *lemma* measure_theory.measure.finite_at_nhds_within
- \+/\- *lemma* measure_theory.measure.le_of_add_le_add_left
- \+/\- *lemma* measure_theory.measure.le_sum_apply
- \+/\- *def* measure_theory.measure.lift_linear
- \+/\- *def* measure_theory.measure.map
- \+/\- *lemma* measure_theory.measure.map_comap_subtype_coe
- \+/\- *def* measure_theory.measure.mutually_singular
- \+/\- *def* measure_theory.measure.restrict
- \+/\- *lemma* measure_theory.measure.restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* measure_theory.measure.restrict_add
- \+/\- *lemma* measure_theory.measure.restrict_apply_self
- \+/\- *lemma* measure_theory.measure.restrict_mono'
- \+/\- *lemma* measure_theory.measure.restrict_mono
- \+/\- *lemma* measure_theory.measure.restrict_smul
- \+/\- *lemma* measure_theory.measure.restrict_zero
- \+/\- *def* measure_theory.measure.restrictₗ
- \+/\- *lemma* measure_theory.measure.restrictₗ_apply
- \+/\- *lemma* measure_theory.measure.sigma_finite_of_not_nonempty
- \+/\- *theorem* measure_theory.measure.smul_apply
- \+/\- *lemma* measure_theory.measure.smul_finite
- \+/\- *theorem* measure_theory.measure.smul_to_outer_measure
- \+/\- *lemma* measure_theory.measure.sum_cond
- \+/\- *theorem* measure_theory.measure.zero_to_outer_measure
- \+/\- *lemma* measure_theory.measure_if
- \+/\- *theorem* measure_theory.sigma_finite.out
- \+/\- *theorem* measure_theory.sigma_finite_iff

Modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *def* ae_measurable
- \+/\- *def* measure_theory.measure.ae



## [2021-08-12 05:23:15](https://github.com/leanprover-community/mathlib/commit/9ab4d28)
doc(tactic/cache): fix haveI docs ([#8637](https://github.com/leanprover-community/mathlib/pull/8637))
Applies [Bhavik's suggestion](https://github.com/leanprover-community/mathlib/pull/8631#discussion_r687260852) which missed the train for [#8631](https://github.com/leanprover-community/mathlib/pull/8631).
#### Estimated changes
Modified src/tactic/cache.lean




## [2021-08-12 03:29:23](https://github.com/leanprover-community/mathlib/commit/036c96b)
fix(tactic/lint): _ is not a linter ([#8634](https://github.com/leanprover-community/mathlib/pull/8634))
The `#lint` parser accepts `ident_`, but as far as I can tell, `_` doesn't mean anything in particular, it just tries and fails to resolve the `linter._` linter. This simplifies the parser to only accept `ident`.
#### Estimated changes
Modified src/tactic/lint/frontend.lean




## [2021-08-12 02:18:22](https://github.com/leanprover-community/mathlib/commit/8968739)
chore(scripts): update nolints.txt ([#8638](https://github.com/leanprover-community/mathlib/pull/8638))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-11 23:46:50](https://github.com/leanprover-community/mathlib/commit/f0ae67d)
feat(analysis/normed_space/finite_dimension): asymptotic equivalence preserves summability ([#8596](https://github.com/leanprover-community/mathlib/pull/8596))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *lemma* summable_of_is_O
- \+/\- *lemma* summable_of_is_O_nat

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* is_equivalent.summable_iff
- \+ *lemma* is_equivalent.summable_iff_nat
- \+ *lemma* summable_of_is_O'
- \+ *lemma* summable_of_is_O_nat'
- \+ *lemma* summable_of_is_equivalent
- \+ *lemma* summable_of_is_equivalent_nat

Modified src/analysis/specific_limits.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.trans_sub
- \+ *lemma* summable_iff_of_summable_sub



## [2021-08-11 21:52:56](https://github.com/leanprover-community/mathlib/commit/ea7e3ff)
feat(tactic/cache): allow optional := in haveI ([#8631](https://github.com/leanprover-community/mathlib/pull/8631))
This syntactic restriction was originally added because it was not possible to reset the instance cache only for a given goal. This limitation has since been lifted (a while ago, I think), and so the syntax can be made more like `have` now.
#### Estimated changes
Modified archive/examples/prop_encodable.lean


Modified src/algebra/char_p/exp_char.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/limits/cofinal.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/data/set/countable.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/ess_sup.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/tactic/cache.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-08-11 19:55:20](https://github.com/leanprover-community/mathlib/commit/565fef6)
refactor(tactic/tidy): use @[user_attribute] ([#8630](https://github.com/leanprover-community/mathlib/pull/8630))
This is just a minor change to use the `@[user_attribute]` attribute like all other user attrs instead of calling `attribute.register`. (This came up during the census of mathlib user attrs.)
#### Estimated changes
Modified src/tactic/tidy.lean




## [2021-08-11 15:48:56](https://github.com/leanprover-community/mathlib/commit/7b5c60d)
feat(data/equiv/basic): add a small lemma for simplifying map between equivalent quotient spaces induced by equivalent relations ([#8617](https://github.com/leanprover-community/mathlib/pull/8617))
Just adding a small lemma that allows us to compute the composition of the map given by `quot.congr` with `quot.mk`
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* quot.congr_mk
- \+ *lemma* quotient.congr_mk



## [2021-08-11 15:48:55](https://github.com/leanprover-community/mathlib/commit/3ebf9f0)
chore(group_theory/group_action/defs): add a missing is_scalar_tower instance ([#8604](https://github.com/leanprover-community/mathlib/pull/8604))
#### Estimated changes
Modified src/group_theory/group_action/defs.lean




## [2021-08-11 15:48:53](https://github.com/leanprover-community/mathlib/commit/2489931)
feat(group_theory/perm/cycle_type): purge trunc references ([#8176](https://github.com/leanprover-community/mathlib/pull/8176))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.map_eq_singleton

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.cycle_type_def
- \+ *lemma* equiv.perm.cycle_type_eq'
- \+ *lemma* equiv.perm.cycle_type_le_of_mem_cycle_factors_finset
- \+ *lemma* equiv.perm.cycle_type_mul_mem_cycle_factors_finset_eq_sub
- \+ *lemma* equiv.perm.order_of_cycle_of_dvd_order_of



## [2021-08-11 14:09:54](https://github.com/leanprover-community/mathlib/commit/2db8c79)
chore(group_theory/submonoid/membership): missing rfl lemmas ([#8619](https://github.com/leanprover-community/mathlib/pull/8619))
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* add_submonoid.mem_multiples_iff
- \+ *lemma* submonoid.mem_powers_iff



## [2021-08-11 11:38:30](https://github.com/leanprover-community/mathlib/commit/8d0ed03)
feat(data/rat/basic): Add nat num and denom inv lemmas ([#8581](https://github.com/leanprover-community/mathlib/pull/8581))
Add `inv_coe_nat_num`  and `inv_coe_nat_denom` lemmas.
These lemmas show that the denominator and numerator of `1/ n` given `0 < n`, are equal to `n` and `1` respectively.
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.inv_coe_int_denom
- \+ *lemma* rat.inv_coe_int_num
- \+ *lemma* rat.inv_coe_nat_denom
- \+ *lemma* rat.inv_coe_nat_num



## [2021-08-11 07:34:47](https://github.com/leanprover-community/mathlib/commit/1d4400c)
feat(analysis/normed_space): controlled surjectivity ([#8498](https://github.com/leanprover-community/mathlib/pull/8498))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* controlled_closure_of_complete
- \+ *lemma* controlled_closure_range_of_complete
- \+ *lemma* normed_group_hom.op_norm_eq_of_bounds
- \+ *lemma* normed_group_hom.surjective_on_with.surj_on
- \+ *def* normed_group_hom.surjective_on_with



## [2021-08-11 06:39:10](https://github.com/leanprover-community/mathlib/commit/9c8602b)
refactor(measure_theory): add subfolder ([#8594](https://github.com/leanprover-community/mathlib/pull/8594))
* This PR adds the subfolders `constructions` `function` `group` `integral` and `measure` to `measure_theory`
* File renamings:
```
group -> group.basic
prod_group -> group.prod
bochner_integration -> integral.bochner
integration -> integral.lebesgue
haar_measure -> measure.haar
lebesgue_measure -> measure.lebesgue
hausdorff_measure -> measure.hausdorff
```
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified counterexamples/phillips.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/fourier.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/dynamics/ergodic/measure_preserving.lean


Modified src/measure_theory/category/Meas.lean


Renamed src/measure_theory/borel_space.lean to src/measure_theory/constructions/borel_space.lean


Renamed src/measure_theory/pi.lean to src/measure_theory/constructions/pi.lean


Renamed src/measure_theory/prod.lean to src/measure_theory/constructions/prod.lean


Modified src/measure_theory/decomposition/signed_hahn.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean


Renamed src/measure_theory/ae_eq_fun.lean to src/measure_theory/function/ae_eq_fun.lean


Renamed src/measure_theory/ae_measurable_sequence.lean to src/measure_theory/function/ae_measurable_sequence.lean


Renamed src/measure_theory/conditional_expectation.lean to src/measure_theory/function/conditional_expectation.lean


Renamed src/measure_theory/continuous_map_dense.lean to src/measure_theory/function/continuous_map_dense.lean


Renamed src/measure_theory/ess_sup.lean to src/measure_theory/function/ess_sup.lean


Renamed src/measure_theory/l1_space.lean to src/measure_theory/function/l1_space.lean


Renamed src/measure_theory/l2_space.lean to src/measure_theory/function/l2_space.lean


Renamed src/measure_theory/lp_space.lean to src/measure_theory/function/lp_space.lean


Renamed src/measure_theory/simple_func_dense.lean to src/measure_theory/function/simple_func_dense.lean


Renamed src/measure_theory/special_functions.lean to src/measure_theory/function/special_functions.lean


Renamed src/measure_theory/arithmetic.lean to src/measure_theory/group/arithmetic.lean


Renamed src/measure_theory/group.lean to src/measure_theory/group/basic.lean


Renamed src/measure_theory/prod_group.lean to src/measure_theory/group/prod.lean


Renamed src/measure_theory/bochner_integration.lean to src/measure_theory/integral/bochner.lean


Renamed src/measure_theory/integrable_on.lean to src/measure_theory/integral/integrable_on.lean


Renamed src/measure_theory/integral_eq_improper.lean to src/measure_theory/integral/integral_eq_improper.lean


Renamed src/measure_theory/interval_integral.lean to src/measure_theory/integral/interval_integral.lean


Renamed src/measure_theory/integration.lean to src/measure_theory/integral/lebesgue.lean


Renamed src/measure_theory/mean_inequalities.lean to src/measure_theory/integral/mean_inequalities.lean


Renamed src/measure_theory/set_integral.lean to src/measure_theory/integral/set_integral.lean


Renamed src/measure_theory/vitali_caratheodory.lean to src/measure_theory/integral/vitali_caratheodory.lean


Renamed src/measure_theory/content.lean to src/measure_theory/measure/content.lean


Renamed src/measure_theory/giry_monad.lean to src/measure_theory/measure/giry_monad.lean


Renamed src/measure_theory/haar_measure.lean to src/measure_theory/measure/haar.lean


Renamed src/measure_theory/hausdorff_measure.lean to src/measure_theory/measure/hausdorff.lean


Renamed src/measure_theory/lebesgue_measure.lean to src/measure_theory/measure/lebesgue.lean


Renamed src/measure_theory/measure_space.lean to src/measure_theory/measure/measure_space.lean


Renamed src/measure_theory/measure_space_def.lean to src/measure_theory/measure/measure_space_def.lean


Renamed src/measure_theory/outer_measure.lean to src/measure_theory/measure/outer_measure.lean


Renamed src/measure_theory/regular.lean to src/measure_theory/measure/regular.lean


Renamed src/measure_theory/vector_measure.lean to src/measure_theory/measure/vector_measure.lean


Modified src/measure_theory/tactic.lean


Modified src/probability_theory/independence.lean


Modified src/probability_theory/integration.lean


Modified test/measurability.lean


Modified test/monotonicity.lean




## [2021-08-11 02:38:04](https://github.com/leanprover-community/mathlib/commit/6305769)
chore(scripts): update nolints.txt ([#8614](https://github.com/leanprover-community/mathlib/pull/8614))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-08-11 02:38:03](https://github.com/leanprover-community/mathlib/commit/3c09987)
docs(data/set/lattice): add module docstring ([#8250](https://github.com/leanprover-community/mathlib/pull/8250))
This also cleans up some whitespace and replaces some `assume`s with `λ`s
#### Estimated changes
Modified src/data/qpf/multivariate/basic.lean


Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Inter_const
- \+/\- *lemma* set.Inter_set_of
- \+/\- *lemma* set.Inter_univ
- \+/\- *theorem* set.Union_const
- \+/\- *lemma* set.Union_empty
- \+/\- *lemma* set.Union_of_singleton
- \+/\- *lemma* set.Union_prop_neg
- \+/\- *lemma* set.Union_prop_pos
- \+/\- *lemma* set.Union_subset_Union2
- \+/\- *lemma* set.Union_subset_Union
- \+/\- *lemma* set.Union_subset_Union_const
- \+/\- *lemma* set.bInter_image
- \+/\- *lemma* set.bInter_range
- \+/\- *lemma* set.bUnion_range
- \+/\- *lemma* set.bind_def
- \+/\- *lemma* set.image_Union
- \+/\- *lemma* set.image_eq_Union
- \+/\- *theorem* set.mem_sUnion
- \+/\- *theorem* set.monotone_preimage
- \+/\- *lemma* set.not_disjoint_iff
- \+/\- *lemma* set.pairwise_disjoint.range
- \+/\- *lemma* set.pi_def
- \+/\- *lemma* set.pi_diff_pi_subset
- \+/\- *lemma* set.range_eq_Union
- \+/\- *lemma* set.sInter_bUnion
- \+/\- *lemma* set.sUnion_bUnion
- \+/\- *theorem* set.sUnion_subset
- \+/\- *theorem* set.sUnion_subset_iff
- \+/\- *def* set.seq
- \+/\- *lemma* set.seq_def
- \+/\- *lemma* set.seq_singleton
- \+/\- *def* set.sigma_to_Union
- \+/\- *lemma* set.sigma_to_Union_bijective
- \+/\- *lemma* set.sigma_to_Union_injective
- \+/\- *theorem* set.subset_sInter
- \+/\- *lemma* set.univ_disjoint
- \+/\- *lemma* set.univ_subtype



## [2021-08-11 00:53:34](https://github.com/leanprover-community/mathlib/commit/694dd11)
feat(archive/imo): IMO 2001 Q6 ([#8327](https://github.com/leanprover-community/mathlib/pull/8327))
Formalization of the problem Q6 of 2001.
#### Estimated changes
Added archive/imo/imo2001_q6.lean
- \+ *theorem* imo2001_q6



## [2021-08-10 18:08:28](https://github.com/leanprover-community/mathlib/commit/32735ca)
feat(measure_theory/measure_space): add mutually singular measures ([#8605](https://github.com/leanprover-community/mathlib/pull/8605))
This PR defines `mutually_singular` for measures. This is useful for Jordan and Lebesgue decomposition.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.mutually_singular.add
- \+ *lemma* measure_theory.measure.mutually_singular.smul
- \+ *lemma* measure_theory.measure.mutually_singular.symm
- \+ *lemma* measure_theory.measure.mutually_singular.zero
- \+ *def* measure_theory.measure.mutually_singular



## [2021-08-10 18:08:27](https://github.com/leanprover-community/mathlib/commit/3b279c1)
feat(measure_theory/l2_space): generalize inner_indicator_const_Lp_one from R to is_R_or_C ([#8602](https://github.com/leanprover-community/mathlib/pull/8602))
#### Estimated changes
Modified src/measure_theory/l2_space.lean
- \+/\- *lemma* measure_theory.L2.inner_indicator_const_Lp_one



## [2021-08-10 18:08:26](https://github.com/leanprover-community/mathlib/commit/d1b2a54)
feat(analysis/normed_space/inner_product): add norm_inner_le_norm ([#8601](https://github.com/leanprover-community/mathlib/pull/8601))
add this:
```
lemma norm_inner_le_norm (x y : E) : ∥⟪x, y⟫∥ ≤ ∥x∥ * ∥y∥ :=
(is_R_or_C.norm_eq_abs _).le.trans (abs_inner_le_norm x y)
```
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* norm_inner_le_norm



## [2021-08-10 18:08:24](https://github.com/leanprover-community/mathlib/commit/acab4f9)
feat(algebra/pointwise): add preimage_smul and generalize a couple of assumptions ([#8600](https://github.com/leanprover-community/mathlib/pull/8600))
Some lemmas about smul spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* mem_inv_smul_set_iff
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \+ *lemma* preimage_smul'
- \+ *lemma* preimage_smul



## [2021-08-10 17:22:47](https://github.com/leanprover-community/mathlib/commit/9fb53f9)
chore(analysis/calculus/fderiv_symmetric): Squeeze some simps in a very slow proof ([#8609](https://github.com/leanprover-community/mathlib/pull/8609))
This doesn't seem to help much, but is low-hanging speedup fruit that the next person stuck on a timeout here will inevitably want solved first.
#### Estimated changes
Modified src/analysis/calculus/fderiv_symmetric.lean




## [2021-08-10 17:22:46](https://github.com/leanprover-community/mathlib/commit/ebe0176)
feat(measure_theory/special_functions): add measurability of is_R_or_C.re and is_R_or_C.im ([#8603](https://github.com/leanprover-community/mathlib/pull/8603))
#### Estimated changes
Modified src/measure_theory/special_functions.lean
- \+ *lemma* ae_measurable.im
- \+ *lemma* ae_measurable.re
- \+ *lemma* is_R_or_C.measurable_im
- \+ *lemma* is_R_or_C.measurable_re
- \+ *lemma* measurable.im
- \+ *lemma* measurable.re



## [2021-08-10 16:39:18](https://github.com/leanprover-community/mathlib/commit/5739199)
chore(linear_algebra/quadratic_form): make Sylvester's law of inertia bold in the doc string ([#8610](https://github.com/leanprover-community/mathlib/pull/8610))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean




## [2021-08-10 14:03:54](https://github.com/leanprover-community/mathlib/commit/e2b7f70)
fix(docs/references.bib): add missing comma ([#8585](https://github.com/leanprover-community/mathlib/pull/8585))
* Adds a missing comma to docs/references.bib. Without this the file cannot be parsed by bibtool.
* Normalises docs/references.bib as described in [Citing other works](https://leanprover-community.github.io/contribute/doc.html#citing-other-works).
#### Estimated changes
Modified docs/references.bib




## [2021-08-10 13:22:22](https://github.com/leanprover-community/mathlib/commit/81a47a7)
docs(topology/category/Profinite/as_limit): fix typo ([#8606](https://github.com/leanprover-community/mathlib/pull/8606))
#### Estimated changes
Modified src/topology/category/Profinite/as_limit.lean




## [2021-08-10 10:54:11](https://github.com/leanprover-community/mathlib/commit/5890afb)
feat(data/list/perm): perm.permutations ([#8587](https://github.com/leanprover-community/mathlib/pull/8587))
This proves the theorem from [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/perm.20of.20permutations):
```lean
theorem perm.permutations {s t : list α} (h : s ~ t) : permutations s ~ permutations t := ...
```
It also introduces a `permutations'` function which has simpler equations (and indeed, this function is used to prove the theorem, because it is relatively easier to prove `perm.permutations'` first).
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.bind_assoc
- \+ *theorem* list.bind_singleton'
- \+ *theorem* list.map_eq_bind
- \+ *theorem* list.map_map_permutations'_aux
- \+ *theorem* list.map_permutations'
- \+ *theorem* list.permutations'_aux_eq_permutations_aux2
- \+ *theorem* list.permutations_append
- \+ *theorem* list.permutations_aux_append
- \+ *theorem* list.permutations_nil

Modified src/data/list/defs.lean
- \+ *def* list.permutations'
- \+ *def* list.permutations'_aux

Modified src/data/list/perm.lean
- \+ *theorem* list.bind_append_perm
- \+ *theorem* list.mem_permutations'
- \+/\- *theorem* list.mem_permutations
- \+ *theorem* list.perm.permutations'
- \+ *theorem* list.perm.permutations
- \+ *theorem* list.perm_permutations'_aux_comm
- \+ *theorem* list.perm_permutations'_iff
- \+ *theorem* list.perm_permutations_iff
- \+ *theorem* list.permutations_perm_permutations'



## [2021-08-10 10:54:10](https://github.com/leanprover-community/mathlib/commit/f967cd0)
refactor(group_theory/sylow): extract a lemma from Sylow proof ([#8459](https://github.com/leanprover-community/mathlib/pull/8459))
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.card_normalizer_modeq_card
- \+ *lemma* sylow.card_quotient_normalizer_modeq_card_quotient
- \+ *lemma* sylow.prime_dvd_card_quotient_normalizer
- \+ *lemma* sylow.prime_pow_dvd_card_normalizer



## [2021-08-10 09:12:41](https://github.com/leanprover-community/mathlib/commit/e8fc466)
feat(algebra/group/pi): Add `pi.const_(monoid|add_monoid|ring|alg)_hom` ([#8518](https://github.com/leanprover-community/mathlib/pull/8518))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* pi.const_alg_hom
- \+ *lemma* pi.const_alg_hom_eq_algebra_of_id
- \+ *lemma* pi.const_ring_hom_eq_algebra_map

Modified src/algebra/group/pi.lean
- \+ *def* pi.const_monoid_hom

Modified src/algebra/ring/pi.lean
- \+ *def* pi.const_ring_hom
- \- *lemma* pi.ring_hom_apply
- \+ *lemma* pi.ring_hom_injective



## [2021-08-10 07:07:58](https://github.com/leanprover-community/mathlib/commit/e729ab4)
feat(analysis/specific_limits): limit of nat_floor (a * x) / x ([#8549](https://github.com/leanprover-community/mathlib/pull/8549))
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* floor_lt_ceil_of_lt
- \+ *lemma* nat_floor_lt_nat_ceil_of_lt_of_pos

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_nat_ceil_mul_div_at_top
- \+ *lemma* tendsto_nat_floor_mul_div_at_top



## [2021-08-10 02:16:24](https://github.com/leanprover-community/mathlib/commit/e4cdecd)
chore(scripts): update nolints.txt ([#8599](https://github.com/leanprover-community/mathlib/pull/8599))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-08-09 21:34:22](https://github.com/leanprover-community/mathlib/commit/2ab63a0)
feat(topology/algebra/infinite_sum, analysis/normed_space/basic): product of two tsums, cauchy product ([#8445](https://github.com/leanprover-community/mathlib/pull/8445))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* summable.mul_norm
- \+ *lemma* summable.mul_of_nonneg
- \+ *lemma* summable_mul_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_antidiagonal_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_range_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
- \+ *lemma* tsum_mul_tsum_of_summable_norm

Modified src/data/finset/nat_antidiagonal.lean
- \+ *def* finset.nat.sigma_antidiagonal_equiv_prod

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.mul
- \+ *lemma* has_sum.mul_eq
- \+ *lemma* summable_mul_prod_iff_summable_mul_sigma_antidiagonal
- \+ *lemma* summable_sum_mul_antidiagonal_of_summable_mul
- \+ *lemma* summable_sum_mul_range_of_summable_mul
- \+ *lemma* tsum_mul_tsum
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_range

Modified src/topology/instances/ennreal.lean
- \+ *lemma* summable_of_sum_le



## [2021-08-09 15:47:29](https://github.com/leanprover-community/mathlib/commit/5e59fb4)
feat(algebra/ordered_pointwise): lemmas on smul of intervals ([#8591](https://github.com/leanprover-community/mathlib/pull/8591))
Some lemmas about smul on different types of intervals, spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819)
#### Estimated changes
Added src/algebra/ordered_pointwise.lean
- \+ *lemma* linear_ordered_field.smul_Icc
- \+ *lemma* linear_ordered_field.smul_Ici
- \+ *lemma* linear_ordered_field.smul_Ico
- \+ *lemma* linear_ordered_field.smul_Iic
- \+ *lemma* linear_ordered_field.smul_Iio
- \+ *lemma* linear_ordered_field.smul_Ioc
- \+ *lemma* linear_ordered_field.smul_Ioi
- \+ *lemma* linear_ordered_field.smul_Ioo



## [2021-08-09 15:47:27](https://github.com/leanprover-community/mathlib/commit/847fc12)
feat(algebra): `submodule.restrict_scalars p R` is `S`-isomorphic to `p` ([#8567](https://github.com/leanprover-community/mathlib/pull/8567))
To be more precise, turning `p : submodule S M` into an `R`-submodule gives the same module structure as turning it into a type and adding a module structure.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* submodule.restrict_scalars_equiv

Modified src/ring_theory/noetherian.lean




## [2021-08-09 15:47:26](https://github.com/leanprover-community/mathlib/commit/3ec899a)
chore(topology/algebra): bundled homs in group and ring completion ([#8497](https://github.com/leanprover-community/mathlib/pull/8497))
Also take the opportunity to remove is_Z_bilin (who was scheduled for
removal from the beginning).
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \+ *def* add_monoid_hom.completion
- \+ *lemma* add_monoid_hom.completion_add
- \+ *lemma* add_monoid_hom.completion_coe
- \+ *lemma* add_monoid_hom.completion_zero
- \+ *lemma* add_monoid_hom.continuous_completion
- \+ *lemma* add_monoid_hom.continuous_extension
- \+ *def* add_monoid_hom.extension
- \+ *lemma* add_monoid_hom.extension_coe
- \+ *lemma* uniform_space.completion.continuous_to_compl
- \- *lemma* uniform_space.completion.is_add_group_hom_coe
- \- *lemma* uniform_space.completion.is_add_group_hom_extension
- \- *lemma* uniform_space.completion.is_add_group_hom_map
- \+ *def* uniform_space.completion.to_compl

Modified src/topology/algebra/uniform_group.lean
- \- *lemma* add_comm_group.is_Z_bilin.comp_hom
- \- *lemma* add_comm_group.is_Z_bilin.neg_left
- \- *lemma* add_comm_group.is_Z_bilin.neg_right
- \- *lemma* add_comm_group.is_Z_bilin.sub_left
- \- *lemma* add_comm_group.is_Z_bilin.sub_right
- \- *lemma* add_comm_group.is_Z_bilin.zero
- \- *lemma* add_comm_group.is_Z_bilin.zero_left
- \- *lemma* add_comm_group.is_Z_bilin.zero_right
- \+/\- *theorem* dense_inducing.extend_Z_bilin
- \- *lemma* is_Z_bilin.tendsto_zero_left
- \- *lemma* is_Z_bilin.tendsto_zero_right

Modified src/topology/algebra/uniform_ring.lean
- \+ *lemma* uniform_space.completion.continuous_coe_ring_hom
- \+/\- *def* uniform_space.completion.map_ring_hom



## [2021-08-09 15:47:25](https://github.com/leanprover-community/mathlib/commit/189e90e)
feat(group_theory/subgroup): lemmas relating normalizer and map and comap ([#8458](https://github.com/leanprover-community/mathlib/pull/8458))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.comap_normalizer_eq_of_surjective
- \+ *lemma* subgroup.le_normalizer_comap
- \+ *lemma* subgroup.le_normalizer_map
- \+ *lemma* subgroup.map_equiv_normalizer_eq
- \+ *lemma* subgroup.map_normalizer_eq_of_bijective



## [2021-08-09 15:47:24](https://github.com/leanprover-community/mathlib/commit/3dd8316)
feat(algebra/ring/basic): mul_{left,right}_cancel_of_non_zero_divisor ([#8425](https://github.com/leanprover-community/mathlib/pull/8425))
We also golf the proof that a domain is a cancel_monoid_with_zero.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* is_left_regular_of_non_zero_divisor
- \+ *lemma* is_regular_of_ne_zero'
- \+ *lemma* is_right_regular_of_non_zero_divisor

Modified src/group_theory/group_action/basic.lean
- \+ *lemma* smul_cancel_of_non_zero_divisor



## [2021-08-09 15:47:22](https://github.com/leanprover-community/mathlib/commit/4a15edd)
feat(data/polynomial/monic): monic.not_zero_divisor_iff ([#8417](https://github.com/leanprover-community/mathlib/pull/8417))
We prove that a monic polynomial is not a zero divisor. A helper lemma is proven that the product of a monic polynomial is of lesser degree iff it is nontrivial and the multiplicand is zero.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.degree_mul_X
- \- *lemma* polynomial.degree_mul_monic
- \+ *lemma* polynomial.monic.degree_mul

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.degree_smul_of_non_zero_divisor
- \+ *lemma* polynomial.is_unit_leading_coeff_mul_left_eq_zero_iff
- \+ *lemma* polynomial.is_unit_leading_coeff_mul_right_eq_zero_iff
- \+ *lemma* polynomial.leading_coeff_smul_of_non_zero_divisor
- \- *lemma* polynomial.monic.degree_eq_zero_iff_eq_one
- \+ *lemma* polynomial.monic.degree_le_zero_iff_eq_one
- \+ *lemma* polynomial.monic.degree_mul_comm
- \+ *lemma* polynomial.monic.mul_left_eq_zero_iff
- \+ *lemma* polynomial.monic.mul_left_ne_zero
- \+ *lemma* polynomial.monic.mul_nat_degree_lt_iff
- \+ *lemma* polynomial.monic.mul_right_eq_zero_iff
- \+ *lemma* polynomial.monic.mul_right_ne_zero
- \+ *lemma* polynomial.monic.nat_degree_eq_zero_iff_eq_one
- \+ *lemma* polynomial.monic.nat_degree_mul'
- \+ *lemma* polynomial.monic.nat_degree_mul_comm
- \+ *lemma* polynomial.monic_C_mul_of_mul_leading_coeff_eq_one
- \+ *lemma* polynomial.monic_of_is_unit_leading_coeff_inv_smul
- \+ *lemma* polynomial.nat_degree_smul_of_non_zero_divisor



## [2021-08-09 15:47:21](https://github.com/leanprover-community/mathlib/commit/5e36848)
feat(measure_theory/decomposition/signed_hahn): signed version of the Hahn decomposition theorem ([#8388](https://github.com/leanprover-community/mathlib/pull/8388))
This PR defined positive and negative sets with respect to a vector measure and prove the signed version of the Hahn decomposition theorem.
#### Estimated changes
Added src/measure_theory/decomposition/signed_hahn.lean
- \+ *lemma* measure_theory.signed_measure.bdd_below_measure_of_negatives
- \+ *lemma* measure_theory.signed_measure.exists_compl_positive_negative
- \+ *theorem* measure_theory.signed_measure.exists_is_compl_positive_negative
- \+ *theorem* measure_theory.signed_measure.exists_subset_restrict_nonpos
- \+ *def* measure_theory.signed_measure.measure_of_negatives
- \+ *lemma* measure_theory.signed_measure.of_symm_diff_compl_positive_negative
- \+ *lemma* measure_theory.signed_measure.zero_mem_measure_of_negatives

Modified src/measure_theory/vector_measure.lean
- \+ *lemma* measure_theory.vector_measure.exists_pos_measure_of_not_restrict_le_zero
- \+ *lemma* measure_theory.vector_measure.le_restrict_empty
- \+ *lemma* measure_theory.vector_measure.measurable_of_not_restrict_le_zero
- \+ *lemma* measure_theory.vector_measure.measurable_of_not_zero_le_restrict
- \+ *lemma* measure_theory.vector_measure.nonneg_of_zero_le_restrict
- \+ *lemma* measure_theory.vector_measure.nonpos_of_restrict_le_zero
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_Union
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_encodable_Union
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_iff
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_of_subset_le
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_subset
- \+ *lemma* measure_theory.vector_measure.restrict_le_restrict_union
- \+ *lemma* measure_theory.vector_measure.restrict_le_zero_of_not_measurable
- \+ *lemma* measure_theory.vector_measure.restrict_le_zero_subset
- \+ *lemma* measure_theory.vector_measure.restrict_not_measurable
- \+ *lemma* measure_theory.vector_measure.subset_le_of_restrict_le_restrict
- \+ *lemma* measure_theory.vector_measure.zero_le_restrict_not_measurable
- \+ *lemma* measure_theory.vector_measure.zero_le_restrict_subset

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.tendsto_top_of_pos



## [2021-08-09 15:47:20](https://github.com/leanprover-community/mathlib/commit/f3b70e4)
feat(group_theory/subgroup): saturated subgroups ([#8137](https://github.com/leanprover-community/mathlib/pull/8137))
From LTE
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.ker_saturated
- \+ *def* subgroup.saturated
- \+ *lemma* subgroup.saturated_iff_gpow
- \+ *lemma* subgroup.saturated_iff_npow



## [2021-08-09 13:47:38](https://github.com/leanprover-community/mathlib/commit/77033a0)
chore(algebra/associated): rename div_or_div to dvd_or_dvd ([#8589](https://github.com/leanprover-community/mathlib/pull/8589))
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* prime.div_or_div
- \+ *lemma* prime.dvd_or_dvd

Modified src/ring_theory/prime.lean




## [2021-08-09 13:47:37](https://github.com/leanprover-community/mathlib/commit/65e2411)
feat(order/bounds): `is_lub`/`is_glb` in Pi types and product types ([#8583](https://github.com/leanprover-community/mathlib/pull/8583))
* Add `monotone_fst` and `monotone_snd`.
* Add some trivial lemmas about `upper_bounds` and `lower_bounds`.
* Turn `is_lub_pi` and `is_glb_pi` into `iff` lemmas.
* Add `is_lub_prod` and `is_glb_prod`.
* Fix some header levels in module docs of `order/bounds`.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* monotone_fst
- \+ *lemma* monotone_snd

Modified src/order/bounds.lean
- \+ *lemma* is_glb_iff_le_iff
- \+/\- *lemma* is_glb_pi
- \+ *lemma* is_glb_prod
- \+ *lemma* is_glb_upper_bounds
- \+ *lemma* is_lub_iff_le_iff
- \+ *lemma* is_lub_lower_bounds
- \+/\- *lemma* is_lub_pi
- \+ *lemma* is_lub_prod
- \+ *lemma* set.nonempty.bdd_above_lower_bounds
- \+ *lemma* set.nonempty.bdd_below_upper_bounds
- \+ *lemma* subset_lower_bounds_upper_bounds
- \+ *lemma* subset_upper_bounds_lower_bounds



## [2021-08-09 13:47:36](https://github.com/leanprover-community/mathlib/commit/9ce6b9a)
feat(order/complete_lattice): add `sup_eq_supr` and `inf_eq_infi` ([#8573](https://github.com/leanprover-community/mathlib/pull/8573))
* add `bool.injective_iff`, `bool.univ_eq`, and `bool.range_eq`;
* add `sup_eq_supr` and `inf_eq_infi`;
* golf `filter.comap_sup`.
#### Estimated changes
Modified src/data/bool.lean
- \+ *lemma* bool.injective_iff

Added src/data/set/bool.lean
- \+ *lemma* bool.range_eq
- \+ *lemma* bool.univ_eq

Modified src/data/set/lattice.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* inf_eq_infi
- \+ *lemma* sup_eq_supr

Modified src/order/filter/basic.lean




## [2021-08-09 13:47:35](https://github.com/leanprover-community/mathlib/commit/45aed67)
chore(order/filter/basic): add `filter.sup_prod` and `filter.prod_sup` ([#8572](https://github.com/leanprover-community/mathlib/pull/8572))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.prod_sup
- \+ *lemma* filter.sup_prod



## [2021-08-09 13:47:34](https://github.com/leanprover-community/mathlib/commit/fc694c5)
chore(linear_algebra/special_linear_group): Cleanup and golf ([#8569](https://github.com/leanprover-community/mathlib/pull/8569))
This cleans up a number things in this file:
* Many lemmas were duplicated between `↑A` and `⇑A`. This eliminates the latter spelling from all lemmas, and makes it simplify to the former. Unfortunately the elaborator fights us at every step of the way with `↑A`, so we introduce local notation to take the pain away.
* Some lemma names did not match the convention established elsewhere
* Some definitions can be bundled more heavily than they currently are. In particular, this merges together `to_lin'` and `to_linear_equiv`, as well as `to_GL` and `embedding_GL`.
#### Estimated changes
Modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* matrix.special_linear_group.coe_fn_eq_coe
- \+ *lemma* matrix.special_linear_group.coe_inv
- \+ *lemma* matrix.special_linear_group.coe_mul
- \+ *lemma* matrix.special_linear_group.coe_one
- \+/\- *lemma* matrix.special_linear_group.coe_to_GL
- \+ *lemma* matrix.special_linear_group.det_coe
- \- *lemma* matrix.special_linear_group.det_coe_fun
- \- *lemma* matrix.special_linear_group.det_coe_matrix
- \- *def* matrix.special_linear_group.embedding_GL
- \+/\- *lemma* matrix.special_linear_group.ext
- \+/\- *lemma* matrix.special_linear_group.ext_iff
- \- *lemma* matrix.special_linear_group.inv_apply
- \- *lemma* matrix.special_linear_group.inv_val
- \- *lemma* matrix.special_linear_group.mul_apply
- \- *lemma* matrix.special_linear_group.mul_val
- \- *lemma* matrix.special_linear_group.one_apply
- \- *lemma* matrix.special_linear_group.one_val
- \+/\- *def* matrix.special_linear_group.to_GL
- \- *lemma* matrix.special_linear_group.to_GL_mul
- \- *lemma* matrix.special_linear_group.to_GL_one
- \+/\- *def* matrix.special_linear_group.to_lin'
- \+ *lemma* matrix.special_linear_group.to_lin'_apply
- \+ *lemma* matrix.special_linear_group.to_lin'_injective
- \- *lemma* matrix.special_linear_group.to_lin'_mul
- \- *lemma* matrix.special_linear_group.to_lin'_one
- \+ *lemma* matrix.special_linear_group.to_lin'_symm_apply
- \+ *lemma* matrix.special_linear_group.to_lin'_symm_to_linear_map
- \+ *lemma* matrix.special_linear_group.to_lin'_to_linear_map
- \- *def* matrix.special_linear_group.to_linear_equiv



## [2021-08-09 13:47:33](https://github.com/leanprover-community/mathlib/commit/8196d4a)
chore(algebra/group/units): Make coercion the simp-normal form of units ([#8568](https://github.com/leanprover-community/mathlib/pull/8568))
It's already used as the output for `@[simps]`; this makes `↑u` the simp-normal form of `u.val` and `↑(u⁻¹)` the simp-normal form of `u.inv`.
#### Estimated changes
Modified src/algebra/group/units.lean
- \- *lemma* units.coe_inv''
- \+ *lemma* units.inv_eq_coe_inv
- \- *lemma* units.val_coe
- \+ *lemma* units.val_eq_coe



## [2021-08-09 13:47:32](https://github.com/leanprover-community/mathlib/commit/8edcf90)
feat(ring_theory/noetherian): add noeth ring lemma ([#8566](https://github.com/leanprover-community/mathlib/pull/8566))
I couldn't find this explicit statement in the library -- I feel like it's the way a mathematician would define a Noetherian ring though.
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_def
- \+ *lemma* is_noetherian_ring_iff_ideal_fg



## [2021-08-09 13:47:31](https://github.com/leanprover-community/mathlib/commit/5f2d954)
feat(algebra/ordered_field): add `inv_le_of_inv_le` and `inv_lt_of_inv_lt` ([#8565](https://github.com/leanprover-community/mathlib/pull/8565))
These lemmas need positivity of only one of two variables. Mathlib already had lemmas about ordered multiplicative groups with these names, I appended prime to their names.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* inv_le_of_inv_le
- \+ *lemma* inv_lt_of_inv_lt

Modified src/algebra/ordered_group.lean




## [2021-08-09 13:47:29](https://github.com/leanprover-community/mathlib/commit/f29cc59)
feat(matrix/kronecker): Add the Kronecker product ([#8560](https://github.com/leanprover-community/mathlib/pull/8560))
Largely derived from [#8152](https://github.com/leanprover-community/mathlib/pull/8152), avoiding the complexity of introducing `algebra_map`s.
This introduces an abstraction `kronecker_map`, which is used to support both `mul` and `tmul` without having to redo any proofs.
#### Estimated changes
Added src/data/matrix/kronecker.lean
- \+ *lemma* matrix.add_kronecker
- \+ *lemma* matrix.add_kronecker_tmul
- \+ *lemma* matrix.diagonal_kronecker_diagonal
- \+ *lemma* matrix.diagonal_kronecker_tmul_diagonal
- \+ *def* matrix.kronecker
- \+ *lemma* matrix.kronecker_add
- \+ *lemma* matrix.kronecker_apply
- \+ *def* matrix.kronecker_bilinear
- \+ *def* matrix.kronecker_map
- \+ *lemma* matrix.kronecker_map_add_left
- \+ *lemma* matrix.kronecker_map_add_right
- \+ *lemma* matrix.kronecker_map_diagonal_diagonal
- \+ *def* matrix.kronecker_map_linear
- \+ *lemma* matrix.kronecker_map_linear_mul_mul
- \+ *lemma* matrix.kronecker_map_map
- \+ *lemma* matrix.kronecker_map_map_left
- \+ *lemma* matrix.kronecker_map_map_right
- \+ *lemma* matrix.kronecker_map_one_one
- \+ *lemma* matrix.kronecker_map_smul_left
- \+ *lemma* matrix.kronecker_map_smul_right
- \+ *lemma* matrix.kronecker_map_transpose
- \+ *lemma* matrix.kronecker_map_zero_left
- \+ *lemma* matrix.kronecker_map_zero_right
- \+ *lemma* matrix.kronecker_smul
- \+ *def* matrix.kronecker_tmul
- \+ *lemma* matrix.kronecker_tmul_add
- \+ *lemma* matrix.kronecker_tmul_apply
- \+ *def* matrix.kronecker_tmul_bilinear
- \+ *lemma* matrix.kronecker_tmul_smul
- \+ *lemma* matrix.kronecker_tmul_zero
- \+ *lemma* matrix.kronecker_zero
- \+ *lemma* matrix.mul_kronecker_mul
- \+ *lemma* matrix.mul_kronecker_tmul_mul
- \+ *lemma* matrix.one_kronecker_one
- \+ *lemma* matrix.one_kronecker_tmul_one
- \+ *lemma* matrix.smul_kronecker
- \+ *lemma* matrix.smul_kronecker_tmul
- \+ *lemma* matrix.zero_kronecker
- \+ *lemma* matrix.zero_kronecker_tmul



## [2021-08-09 13:47:28](https://github.com/leanprover-community/mathlib/commit/7b1ce10)
fix(analysis/normed_space/basic): add an alias instance to fix an inference issue ([#8547](https://github.com/leanprover-community/mathlib/pull/8547))
This adds an instance from [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245176934).
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/multilinear.lean




## [2021-08-09 11:59:28](https://github.com/leanprover-community/mathlib/commit/fb63cf3)
chore(data/pfun): rename `roption` to `part`, split `data.part` off `data.pfun`  ([#8544](https://github.com/leanprover-community/mathlib/pull/8544))
#### Estimated changes
Modified src/computability/halting.lean


Modified src/computability/partrec.lean
- \+/\- *theorem* computable.of_option
- \- *theorem* computable.part
- \- *theorem* computable₂.part
- \+/\- *theorem* decidable.partrec.const'
- \+/\- *def* nat.rfind
- \+/\- *def* nat.rfind_opt
- \+/\- *theorem* partrec.const'
- \+/\- *theorem* partrec.none
- \+ *theorem* vector.m_of_fn_part_some
- \- *theorem* vector.m_of_fn_roption_some

Modified src/computability/partrec_code.lean
- \+/\- *theorem* nat.partrec.code.eval_const
- \+/\- *theorem* nat.partrec.code.eval_id

Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean
- \+/\- *def* turing.TM0.eval
- \+/\- *def* turing.TM1.eval
- \+/\- *def* turing.TM2.eval
- \+/\- *def* turing.eval

Modified src/control/fix.lean
- \+ *def* part.fix.approx
- \+ *def* part.fix_aux
- \+ *lemma* part.fix_def'
- \- *def* roption.fix.approx
- \- *def* roption.fix_aux
- \- *lemma* roption.fix_def'

Modified src/control/lawful_fix.lean
- \+ *def* part.fix.approx_chain
- \+ *lemma* part.fix.approx_le_fix
- \+ *lemma* part.fix.approx_mem_approx_chain
- \+ *lemma* part.fix.approx_mono'
- \+ *lemma* part.fix.approx_mono
- \+ *lemma* part.fix.exists_fix_le_approx
- \+ *lemma* part.fix.le_f_of_mem_approx
- \+ *lemma* part.fix.mem_iff
- \+ *lemma* part.fix_eq
- \+ *lemma* part.fix_eq_ωSup
- \+ *lemma* part.fix_le
- \+ *lemma* part.to_unit_cont
- \+ *def* part.to_unit_mono
- \- *def* roption.fix.approx_chain
- \- *lemma* roption.fix.approx_le_fix
- \- *lemma* roption.fix.approx_mem_approx_chain
- \- *lemma* roption.fix.approx_mono'
- \- *lemma* roption.fix.approx_mono
- \- *lemma* roption.fix.exists_fix_le_approx
- \- *lemma* roption.fix.le_f_of_mem_approx
- \- *lemma* roption.fix.mem_iff
- \- *lemma* roption.fix_eq
- \- *lemma* roption.fix_eq_ωSup
- \- *lemma* roption.fix_le
- \- *lemma* roption.to_unit_cont
- \- *def* roption.to_unit_mono

Modified src/data/finmap.lean


Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_inj
- \+/\- *lemma* enat.ne_top_iff
- \+/\- *def* enat

Modified src/data/option/basic.lean


Added src/data/part.lean
- \+ *def* part.assert
- \+ *theorem* part.assert_defined
- \+ *lemma* part.assert_neg
- \+ *lemma* part.assert_pos
- \+ *theorem* part.bind_assoc
- \+ *theorem* part.bind_defined
- \+ *theorem* part.bind_dom
- \+ *theorem* part.bind_eq_bind
- \+ *lemma* part.bind_le
- \+ *theorem* part.bind_map
- \+ *theorem* part.bind_none
- \+ *theorem* part.bind_some
- \+ *theorem* part.bind_some_eq_map
- \+ *theorem* part.bind_some_right
- \+ *theorem* part.coe_none
- \+ *theorem* part.coe_some
- \+ *theorem* part.dom_iff_mem
- \+ *theorem* part.eq_none_iff'
- \+ *theorem* part.eq_none_iff
- \+ *lemma* part.eq_none_or_eq_some
- \+ *theorem* part.eq_some_iff
- \+ *theorem* part.eta
- \+ *theorem* part.ext'
- \+ *theorem* part.ext
- \+ *lemma* part.get_eq_get_of_eq
- \+ *lemma* part.get_eq_iff_eq_some
- \+ *theorem* part.get_eq_of_mem
- \+ *theorem* part.get_mem
- \+ *def* part.get_or_else
- \+ *lemma* part.get_or_else_none
- \+ *lemma* part.get_or_else_some
- \+ *theorem* part.get_some
- \+ *lemma* part.le_total_of_le_of_le
- \+ *def* part.map
- \+ *theorem* part.map_bind
- \+ *theorem* part.map_eq_map
- \+ *theorem* part.map_id'
- \+ *theorem* part.map_map
- \+ *theorem* part.map_none
- \+ *theorem* part.map_some
- \+ *theorem* part.mem.left_unique
- \+ *theorem* part.mem_assert
- \+ *theorem* part.mem_assert_iff
- \+ *theorem* part.mem_bind
- \+ *theorem* part.mem_bind_iff
- \+ *theorem* part.mem_coe
- \+ *theorem* part.mem_eq
- \+ *theorem* part.mem_map
- \+ *theorem* part.mem_map_iff
- \+ *theorem* part.mem_of_option
- \+ *theorem* part.mem_restrict
- \+ *theorem* part.mem_some
- \+ *theorem* part.mem_some_iff
- \+ *theorem* part.mem_to_option
- \+ *theorem* part.mem_unique
- \+ *lemma* part.ne_none_iff
- \+ *def* part.none
- \+ *theorem* part.not_mem_none
- \+ *def* part.of_option
- \+ *theorem* part.of_option_dom
- \+ *theorem* part.of_option_eq_get
- \+ *theorem* part.of_to_option
- \+ *theorem* part.pure_eq_some
- \+ *def* part.restrict
- \+ *theorem* part.ret_eq_some
- \+ *def* part.some
- \+ *lemma* part.some_get
- \+ *lemma* part.some_inj
- \+ *lemma* part.some_ne_none
- \+ *theorem* part.to_of_option
- \+ *def* part.to_option

Modified src/data/pfun.lean
- \+/\- *def* pfun
- \- *def* roption.assert
- \- *theorem* roption.assert_defined
- \- *lemma* roption.assert_neg
- \- *lemma* roption.assert_pos
- \- *theorem* roption.bind_assoc
- \- *theorem* roption.bind_defined
- \- *theorem* roption.bind_dom
- \- *theorem* roption.bind_eq_bind
- \- *lemma* roption.bind_le
- \- *theorem* roption.bind_map
- \- *theorem* roption.bind_none
- \- *theorem* roption.bind_some
- \- *theorem* roption.bind_some_eq_map
- \- *theorem* roption.bind_some_right
- \- *theorem* roption.coe_none
- \- *theorem* roption.coe_some
- \- *theorem* roption.dom_iff_mem
- \- *theorem* roption.eq_none_iff'
- \- *theorem* roption.eq_none_iff
- \- *lemma* roption.eq_none_or_eq_some
- \- *theorem* roption.eq_some_iff
- \- *theorem* roption.eta
- \- *theorem* roption.ext'
- \- *theorem* roption.ext
- \- *lemma* roption.get_eq_get_of_eq
- \- *lemma* roption.get_eq_iff_eq_some
- \- *theorem* roption.get_eq_of_mem
- \- *theorem* roption.get_mem
- \- *def* roption.get_or_else
- \- *lemma* roption.get_or_else_none
- \- *lemma* roption.get_or_else_some
- \- *theorem* roption.get_some
- \- *lemma* roption.le_total_of_le_of_le
- \- *def* roption.map
- \- *theorem* roption.map_bind
- \- *theorem* roption.map_eq_map
- \- *theorem* roption.map_id'
- \- *theorem* roption.map_map
- \- *theorem* roption.map_none
- \- *theorem* roption.map_some
- \- *theorem* roption.mem.left_unique
- \- *theorem* roption.mem_assert
- \- *theorem* roption.mem_assert_iff
- \- *theorem* roption.mem_bind
- \- *theorem* roption.mem_bind_iff
- \- *theorem* roption.mem_coe
- \- *theorem* roption.mem_eq
- \- *theorem* roption.mem_map
- \- *theorem* roption.mem_map_iff
- \- *theorem* roption.mem_of_option
- \- *theorem* roption.mem_restrict
- \- *theorem* roption.mem_some
- \- *theorem* roption.mem_some_iff
- \- *theorem* roption.mem_to_option
- \- *theorem* roption.mem_unique
- \- *lemma* roption.ne_none_iff
- \- *def* roption.none
- \- *theorem* roption.not_mem_none
- \- *def* roption.of_option
- \- *theorem* roption.of_option_dom
- \- *theorem* roption.of_option_eq_get
- \- *theorem* roption.of_to_option
- \- *theorem* roption.pure_eq_some
- \- *def* roption.restrict
- \- *theorem* roption.ret_eq_some
- \- *def* roption.some
- \- *lemma* roption.some_get
- \- *lemma* roption.some_inj
- \- *lemma* roption.some_ne_none
- \- *theorem* roption.to_of_option
- \- *def* roption.to_option

Modified src/data/polynomial/div.lean


Modified src/data/rel.lean


Modified src/order/omega_complete_partial_order.lean
- \+/\- *lemma* omega_complete_partial_order.continuous_hom.bind_continuous'
- \+/\- *lemma* omega_complete_partial_order.continuous_hom.map_continuous'
- \+/\- *lemma* omega_complete_partial_order.continuous_hom.seq_continuous'
- \+/\- *lemma* omega_complete_partial_order.continuous_hom.ωSup_bind
- \+ *lemma* part.eq_of_chain
- \+ *lemma* part.mem_chain_of_mem_ωSup
- \+ *lemma* part.mem_ωSup
- \+ *lemma* part.ωSup_eq_none
- \+ *lemma* part.ωSup_eq_some
- \+/\- *def* preorder_hom.bind
- \- *lemma* roption.eq_of_chain
- \- *lemma* roption.mem_chain_of_mem_ωSup
- \- *lemma* roption.mem_ωSup
- \- *lemma* roption.ωSup_eq_none
- \- *lemma* roption.ωSup_eq_some

Modified src/ring_theory/multiplicity.lean


Modified test/general_recursion.lean
- \+ *theorem* part.examples.div.cont
- \+ *theorem* part.examples.div.equations.eqn_1
- \+ *def* part.examples.div.intl
- \+ *def* part.examples.div
- \+ *theorem* part.examples.easy.cont
- \+ *theorem* part.examples.easy.equations.eqn_1
- \+ *def* part.examples.easy.intl
- \+ *def* part.examples.easy
- \+ *def* part.examples.f91'
- \+ *lemma* part.examples.f91.cont
- \+ *theorem* part.examples.f91.equations.eqn_1
- \+ *def* part.examples.f91.intl
- \+ *def* part.examples.f91
- \+ *lemma* part.examples.f91_dom
- \+ *lemma* part.examples.f91_spec'
- \+ *lemma* part.examples.f91_spec
- \+ *theorem* part.examples.tree_map'.cont
- \+ *theorem* part.examples.tree_map'.equations.eqn_1
- \+ *theorem* part.examples.tree_map'.equations.eqn_2
- \+ *def* part.examples.tree_map'.intl
- \+ *def* part.examples.tree_map'
- \+ *theorem* part.examples.tree_map.cont
- \+ *theorem* part.examples.tree_map.equations.eqn_1
- \+ *theorem* part.examples.tree_map.equations.eqn_2
- \+ *def* part.examples.tree_map.intl
- \+ *def* part.examples.tree_map
- \- *theorem* roption.examples.div.cont
- \- *theorem* roption.examples.div.equations.eqn_1
- \- *def* roption.examples.div.intl
- \- *def* roption.examples.div
- \- *theorem* roption.examples.easy.cont
- \- *theorem* roption.examples.easy.equations.eqn_1
- \- *def* roption.examples.easy.intl
- \- *def* roption.examples.easy
- \- *def* roption.examples.f91'
- \- *lemma* roption.examples.f91.cont
- \- *theorem* roption.examples.f91.equations.eqn_1
- \- *def* roption.examples.f91.intl
- \- *def* roption.examples.f91
- \- *lemma* roption.examples.f91_dom
- \- *lemma* roption.examples.f91_spec'
- \- *lemma* roption.examples.f91_spec
- \- *theorem* roption.examples.tree_map'.cont
- \- *theorem* roption.examples.tree_map'.equations.eqn_1
- \- *theorem* roption.examples.tree_map'.equations.eqn_2
- \- *def* roption.examples.tree_map'.intl
- \- *def* roption.examples.tree_map'
- \- *theorem* roption.examples.tree_map.cont
- \- *theorem* roption.examples.tree_map.equations.eqn_1
- \- *theorem* roption.examples.tree_map.equations.eqn_2
- \- *def* roption.examples.tree_map.intl
- \- *def* roption.examples.tree_map



## [2021-08-09 10:27:32](https://github.com/leanprover-community/mathlib/commit/6728201)
chore(data/finsupp): add missing lemmas ([#8553](https://github.com/leanprover-community/mathlib/pull/8553))
These lemmas are needed by `[simps {simp_rhs := tt}]` when composing equivs, otherwise simp doesn't make progress on `(map_range.add_equiv f).to_equiv.symm x` which should simplify to `map_range f.to_equiv.symm x`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.map_range.add_equiv_to_add_monoid_hom
- \+ *lemma* finsupp.map_range.add_equiv_to_equiv
- \+ *lemma* finsupp.map_range.add_monoid_hom_to_zero_hom
- \+ *def* finsupp.map_range.equiv
- \+ *lemma* finsupp.map_range.equiv_refl
- \+ *lemma* finsupp.map_range.equiv_symm
- \+ *lemma* finsupp.map_range.equiv_trans

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.map_range.linear_equiv_to_add_equiv
- \+ *lemma* finsupp.map_range.linear_equiv_to_linear_map
- \+ *lemma* finsupp.map_range.linear_map_to_add_monoid_hom



## [2021-08-09 08:17:21](https://github.com/leanprover-community/mathlib/commit/3f5a348)
chore(galois_connection): golf some proofs ([#8582](https://github.com/leanprover-community/mathlib/pull/8582))
* golf some proofs
* add `galois_insertion.left_inverse_l_u` and `galois_coinsertion.left_inverse_u_l`;
* drop `galois_insertion.l_supr_of_ul_eq_self` and `galois_coinsertion.u_infi_of_lu_eq_self`: these lemmas are less general than `galois_connection.l_supr` and `galois_connection.u_infi`.
#### Estimated changes
Modified src/order/galois_connection.lean
- \- *lemma* galois_coinsertion.u_infi_of_lu_eq_self
- \+ *lemma* galois_coinsertion.u_l_left_inverse
- \+/\- *lemma* galois_connection.l_bot
- \+/\- *lemma* galois_connection.u_Inf
- \+/\- *lemma* galois_connection.u_inf
- \+/\- *lemma* galois_connection.u_infi
- \+/\- *lemma* galois_connection.u_top
- \- *lemma* galois_insertion.l_supr_of_ul_eq_self
- \+ *lemma* galois_insertion.left_inverse_l_u



## [2021-08-09 08:17:20](https://github.com/leanprover-community/mathlib/commit/24bbbdc)
feat(group_theory/sylow): Generalize proof of first Sylow theorem ([#8383](https://github.com/leanprover-community/mathlib/pull/8383))
Generalize the first proof. There is now a proof that every p-subgroup is contained in a Sylow subgroup.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \- *lemma* add_subgroup.card_bot
- \+/\- *lemma* subgroup.card_bot
- \+ *lemma* subgroup.card_le_one_iff_eq_bot

Modified src/group_theory/sylow.lean
- \+/\- *theorem* sylow.exists_subgroup_card_pow_prime
- \+ *theorem* sylow.exists_subgroup_card_pow_prime_le
- \+ *theorem* sylow.exists_subgroup_card_pow_succ



## [2021-08-09 08:17:19](https://github.com/leanprover-community/mathlib/commit/4813b73)
feat(category_theory/adjunction): general adjoint functor theorem ([#4885](https://github.com/leanprover-community/mathlib/pull/4885))
A proof of the general adjoint functor theorem. This PR also adds an API for wide equalizers (essentially copied from the equalizer API), as well as results relating adjunctions to (co)structured arrow categories and weakly initial objects. I can split this into smaller PRs if necessary?
#### Estimated changes
Added src/category_theory/adjunction/adjoint_functor_theorems.lean
- \+ *def* category_theory.solution_set_condition
- \+ *lemma* category_theory.solution_set_condition_of_is_right_adjoint

Added src/category_theory/adjunction/comma.lean
- \+ *def* category_theory.adjunction_of_costructured_arrow_terminals
- \+ *def* category_theory.adjunction_of_structured_arrow_initials
- \+ *def* category_theory.is_right_adjoint_of_costructured_arrow_terminals
- \+ *def* category_theory.is_right_adjoint_of_structured_arrow_initials
- \+ *def* category_theory.left_adjoint_of_structured_arrow_initials
- \+ *def* category_theory.left_adjoint_of_structured_arrow_initials_aux
- \+ *def* category_theory.mk_initial_of_left_adjoint
- \+ *def* category_theory.mk_terminal_of_right_adjoint
- \+ *def* category_theory.right_adjoint_of_costructured_arrow_terminals
- \+ *def* category_theory.right_adjoint_of_costructured_arrow_terminals_aux

Added src/category_theory/limits/constructions/weakly_initial.lean
- \+ *lemma* category_theory.has_initial_of_weakly_initial_and_has_wide_equalizers
- \+ *lemma* category_theory.has_weakly_initial_of_weakly_initial_set_and_has_products

Added src/category_theory/limits/shapes/wide_equalizers.lean
- \+ *def* category_theory.limits.cocone.of_cotrident
- \+ *lemma* category_theory.limits.cocone.of_cotrident_ι
- \+ *def* category_theory.limits.cone.of_trident
- \+ *lemma* category_theory.limits.cone.of_trident_π
- \+ *lemma* category_theory.limits.cotrident.app_one
- \+ *lemma* category_theory.limits.cotrident.coequalizer_ext
- \+ *lemma* category_theory.limits.cotrident.condition
- \+ *def* category_theory.limits.cotrident.ext
- \+ *def* category_theory.limits.cotrident.is_colimit.desc'
- \+ *lemma* category_theory.limits.cotrident.is_colimit.hom_ext
- \+ *def* category_theory.limits.cotrident.is_colimit.hom_iso
- \+ *lemma* category_theory.limits.cotrident.is_colimit.hom_iso_natural
- \+ *def* category_theory.limits.cotrident.is_colimit.mk'
- \+ *def* category_theory.limits.cotrident.is_colimit.mk
- \+ *def* category_theory.limits.cotrident.mk_hom
- \+ *def* category_theory.limits.cotrident.of_cocone
- \+ *lemma* category_theory.limits.cotrident.of_cocone_ι
- \+ *def* category_theory.limits.cotrident.of_π
- \+ *lemma* category_theory.limits.cotrident.π_eq_app_one
- \+ *lemma* category_theory.limits.cotrident.π_of_π
- \+ *def* category_theory.limits.diagram_iso_parallel_family
- \+ *lemma* category_theory.limits.epi_of_is_colimit_parallel_family
- \+ *lemma* category_theory.limits.has_wide_coequalizers_of_has_colimit_parallel_family
- \+ *lemma* category_theory.limits.has_wide_equalizers_of_has_limit_parallel_family
- \+ *lemma* category_theory.limits.mono_of_is_limit_parallel_family
- \+ *def* category_theory.limits.parallel_family
- \+ *lemma* category_theory.limits.parallel_family_map_left
- \+ *lemma* category_theory.limits.parallel_family_obj_one
- \+ *lemma* category_theory.limits.parallel_family_obj_zero
- \+ *lemma* category_theory.limits.trident.app_zero
- \+ *lemma* category_theory.limits.trident.condition
- \+ *lemma* category_theory.limits.trident.equalizer_ext
- \+ *def* category_theory.limits.trident.ext
- \+ *lemma* category_theory.limits.trident.is_limit.hom_ext
- \+ *def* category_theory.limits.trident.is_limit.hom_iso
- \+ *lemma* category_theory.limits.trident.is_limit.hom_iso_natural
- \+ *def* category_theory.limits.trident.is_limit.lift'
- \+ *def* category_theory.limits.trident.is_limit.mk'
- \+ *def* category_theory.limits.trident.is_limit.mk
- \+ *def* category_theory.limits.trident.mk_hom
- \+ *def* category_theory.limits.trident.of_cone
- \+ *lemma* category_theory.limits.trident.of_cone_π
- \+ *def* category_theory.limits.trident.of_ι
- \+ *lemma* category_theory.limits.trident.ι_eq_app_zero
- \+ *lemma* category_theory.limits.trident.ι_of_ι
- \+ *def* category_theory.limits.walking_parallel_family.hom.comp
- \+ *lemma* category_theory.limits.walking_parallel_family.hom_id
- \+ *def* category_theory.limits.walking_parallel_family_equiv_walking_parallel_pair
- \+ *lemma* category_theory.limits.wide_coequalizer.condition
- \+ *lemma* category_theory.limits.wide_coequalizer.cotrident_ι_app_one
- \+ *lemma* category_theory.limits.wide_coequalizer.cotrident_π
- \+ *def* category_theory.limits.wide_coequalizer.desc'
- \+ *lemma* category_theory.limits.wide_coequalizer.hom_ext
- \+ *lemma* category_theory.limits.wide_coequalizer.π_desc
- \+ *def* category_theory.limits.wide_coequalizer_is_wide_coequalizer
- \+ *lemma* category_theory.limits.wide_equalizer.condition
- \+ *lemma* category_theory.limits.wide_equalizer.hom_ext
- \+ *def* category_theory.limits.wide_equalizer.lift'
- \+ *lemma* category_theory.limits.wide_equalizer.lift_ι
- \+ *lemma* category_theory.limits.wide_equalizer.trident_ι
- \+ *lemma* category_theory.limits.wide_equalizer.trident_π_app_zero
- \+ *def* category_theory.limits.wide_equalizer_is_wide_equalizer



## [2021-08-09 06:49:46](https://github.com/leanprover-community/mathlib/commit/7bb4b27)
feat(group_theory/group_action): Cayley's theorem ([#8552](https://github.com/leanprover-community/mathlib/pull/8552))
#### Estimated changes
Modified src/group_theory/group_action/group.lean
- \+/\- *def* mul_action.to_perm
- \+ *lemma* mul_action.to_perm_injective

Modified src/group_theory/perm/subgroup.lean




## [2021-08-09 01:12:40](https://github.com/leanprover-community/mathlib/commit/9e320a2)
chore(measure_theory/special_functions): add measurability attributes ([#8570](https://github.com/leanprover-community/mathlib/pull/8570))
That attribute makes the `measurability` tactic aware of those lemmas.
#### Estimated changes
Modified src/measure_theory/special_functions.lean
- \+/\- *lemma* complex.measurable_arg
- \+/\- *lemma* complex.measurable_cos
- \+/\- *lemma* complex.measurable_cosh
- \+/\- *lemma* complex.measurable_exp
- \+/\- *lemma* complex.measurable_im
- \+/\- *lemma* complex.measurable_log
- \+/\- *lemma* complex.measurable_of_real
- \+/\- *lemma* complex.measurable_re
- \+/\- *lemma* complex.measurable_sin
- \+/\- *lemma* complex.measurable_sinh
- \+/\- *lemma* measurable.arctan
- \+/\- *lemma* measurable.carg
- \+/\- *lemma* measurable.ccos
- \+/\- *lemma* measurable.ccosh
- \+/\- *lemma* measurable.cexp
- \+/\- *lemma* measurable.clog
- \+/\- *lemma* measurable.cos
- \+/\- *lemma* measurable.cosh
- \+/\- *lemma* measurable.csin
- \+/\- *lemma* measurable.csinh
- \+/\- *lemma* measurable.exp
- \+/\- *lemma* measurable.log
- \+/\- *lemma* measurable.sin
- \+/\- *lemma* measurable.sinh
- \+/\- *lemma* measurable.sqrt
- \+/\- *lemma* real.measurable_arccos
- \+/\- *lemma* real.measurable_arcsin
- \+/\- *lemma* real.measurable_arctan
- \+/\- *lemma* real.measurable_cos
- \+/\- *lemma* real.measurable_cosh
- \+/\- *lemma* real.measurable_exp
- \+/\- *lemma* real.measurable_log
- \+/\- *lemma* real.measurable_sin
- \+/\- *lemma* real.measurable_sinh



## [2021-08-08 19:18:31](https://github.com/leanprover-community/mathlib/commit/ea77271)
chore(analysis/calculus/{f,}deriv): fix, add missing lemmas ([#8574](https://github.com/leanprover-community/mathlib/pull/8574))
* use `prod.fst` and `prod.snd` in lemmas like `has_fderiv_at_fst`;
* add `has_strict_deriv_at.prod`,
  `has_strict_fderiv_at.comp_has_strict_deriv_at`;
* use `set.maps_to` in some lemmas;
* golf some proofs.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *theorem* has_fderiv_at.comp_has_deriv_at
- \+ *lemma* has_strict_deriv_at.prod
- \+ *theorem* has_strict_fderiv_at.comp_has_strict_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_at_fst
- \+/\- *lemma* has_fderiv_at_snd
- \+/\- *lemma* has_strict_fderiv_at_fst
- \+/\- *lemma* has_strict_fderiv_at_snd



## [2021-08-08 17:26:57](https://github.com/leanprover-community/mathlib/commit/3788cbf)
chore(algebra/*, data/polynomial/*): remove unnecessary imports ([#8578](https://github.com/leanprover-community/mathlib/pull/8578))
I cleaned up all of `data.polynomial`, and the files in `algebra` it imports.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/big_operators/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/prod.lean


Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/smul_with_zero.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/mul_add_aut.lean


Modified src/data/equiv/ring_aut.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/identities.lean


Modified src/data/polynomial/inductions.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/mirror.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/group_theory/group_action/group.lean


Modified src/group_theory/group_action/prod.lean


Modified src/linear_algebra/basic.lean


Modified src/order/compactly_generated.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean




## [2021-08-08 11:51:48](https://github.com/leanprover-community/mathlib/commit/87e9bec)
chore(linear_algebra/matrix/trace): relax `comm_ring` to `comm_semiring` in `matrix.trace_mul_comm` ([#8577](https://github.com/leanprover-community/mathlib/pull/8577))
#### Estimated changes
Modified src/linear_algebra/matrix/trace.lean
- \+/\- *lemma* matrix.trace_mul_comm



## [2021-08-07 22:04:03](https://github.com/leanprover-community/mathlib/commit/0a79eec)
fix(order/bounds): remove double space ([#8575](https://github.com/leanprover-community/mathlib/pull/8575))
#### Estimated changes
Modified src/order/bounds.lean
- \+/\- *def* upper_bounds



## [2021-08-07 20:32:48](https://github.com/leanprover-community/mathlib/commit/575fcc6)
refactor(data/nat/choose): reduce assumptions on lemmas ([#8508](https://github.com/leanprover-community/mathlib/pull/8508))
- rename `nat.choose_eq_factorial_div_factorial'` to `nat.cast_choose`
- change the cast from `ℚ` to any `char_zero` field
- get rid of the cast in `nat.choose_mul`. Generalization ensues.
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+ *lemma* nat.choose_mul

Modified src/data/nat/choose/dvd.lean
- \+ *lemma* nat.cast_choose
- \- *lemma* nat.choose_eq_factorial_div_factorial'
- \- *lemma* nat.choose_mul

Modified src/number_theory/bernoulli_polynomials.lean




## [2021-08-07 19:53:42](https://github.com/leanprover-community/mathlib/commit/d757996)
feat(analysis/complex): prove that complex functions are conformal if and only if the functions are holomorphic/antiholomorphic with nonvanishing differential ([#8424](https://github.com/leanprover-community/mathlib/pull/8424))
Complex functions are conformal if and only if the functions are holomorphic/antiholomorphic with nonvanishing differential.
#### Estimated changes
Modified src/analysis/calculus/conformal.lean
- \- *lemma* conformal_at.preserves_angle

Added src/analysis/complex/conformal.lean
- \+ *lemma* is_conformal_map.is_complex_or_conj_linear
- \+ *lemma* is_conformal_map_complex_linear
- \+ *lemma* is_conformal_map_complex_linear_conj
- \+ *lemma* is_conformal_map_conj
- \+ *lemma* is_conformal_map_iff_is_complex_or_conj_linear:

Modified src/analysis/complex/real_deriv.lean
- \+ *lemma* conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj
- \+ *lemma* differentiable_at.conformal_at

Modified src/analysis/normed_space/conformal_linear_map.lean
- \+ *lemma* is_conformal_map.ne_zero
- \- *lemma* is_conformal_map.preserves_angle
- \+ *lemma* linear_isometry.is_conformal_map

Modified src/geometry/euclidean/basic.lean
- \+ *lemma* inner_product_geometry.conformal_at.preserves_angle
- \+ *lemma* inner_product_geometry.is_conformal_map.preserves_angle



## [2021-08-07 00:16:50](https://github.com/leanprover-community/mathlib/commit/b3c1de6)
feat(analysis/complex/basic): add several trivial lemmas for differentiable functions. ([#8418](https://github.com/leanprover-community/mathlib/pull/8418))
This file relates the differentiability of a function to the linearity of its `fderiv`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_at.fderiv_restrict_scalars
- \+ *lemma* differentiable_at_iff_restrict_scalars
- \+ *lemma* differentiable_within_at_iff_restrict_scalars
- \+ *lemma* has_fderiv_at_of_restrict_scalars
- \+ *lemma* has_fderiv_within_at_of_restrict_scalars



## [2021-08-06 21:15:20](https://github.com/leanprover-community/mathlib/commit/2f29e09)
feat(group_action/defs): generalize faithful actions ([#8555](https://github.com/leanprover-community/mathlib/pull/8555))
This generalizes the `faithful_mul_semiring_action` typeclass to a mixin typeclass `has_faithful_scalar`, and provides instances for some simple actions:
* `has_faithful_scalar α α` (on cancellative monoids and monoids with zero)
* `has_faithful_scalar (opposite α) α`
* `has_faithful_scalar α (Π i, f i)`
* `has_faithful_scalar (units A) B`
* `has_faithful_scalar (equiv.perm α) α`
* `has_faithful_scalar M (α × β)`
* `has_faithful_scalar R (α →₀ M)`
* `has_faithful_scalar S (polynomial R)` (generalized from an existing instance)
* `has_faithful_scalar R (mv_polynomial σ S₁)`
* `has_faithful_scalar R (monoid_algebra k G)`
* `has_faithful_scalar R (add_monoid_algebra k G)`
As well as retaining the one other existing instance
* `faithful_mul_semiring_action ↥H E` where `H : subgroup (E ≃ₐ[F] E)`
The lemmas taking `faithful_mul_semiring_action` as a typeclass argument have been converted to use the new typeclass, but no attempt has been made to weaken their other hypotheses.
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \- *theorem* eq_of_smul_eq_smul
- \+/\- *theorem* to_ring_hom_injective

Modified src/algebra/module/pi.lean
- \+ *lemma* pi.has_faithful_scalar_at

Modified src/algebra/monoid_algebra.lean


Modified src/algebra/opposites.lean


Modified src/algebra/polynomial/group_ring_action.lean


Modified src/data/finsupp/basic.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/polynomial/basic.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean


Modified src/group_theory/group_action/defs.lean
- \+ *lemma* smul_left_injective'

Modified src/group_theory/group_action/group.lean


Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/group_action/units.lean




## [2021-08-06 17:42:38](https://github.com/leanprover-community/mathlib/commit/1b876c7)
chore(algebra/ordered_group): fix/add `order_dual` instances, add lemmas ([#8564](https://github.com/leanprover-community/mathlib/pull/8564))
* add `order_dual.has_inv`, `order_dual.group`, `order_dual.comm_group`;
* use new instances in `order_dual.ordered_comm_group` and
  `order_dual.linear_ordered_comm_group` (earlier we had only additive
  versions);
* add `le_of_forall_neg_add_le`, `le_of_forall_pos_sub_le`,
  `le_iff_forall_neg_add_le` and their multiplicative versions.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* le_iff_forall_lt_one_mul_le
- \+ *lemma* le_of_forall_lt_one_mul_le
- \+ *lemma* le_of_forall_one_lt_div_le

Modified src/algebra/ordered_monoid.lean




## [2021-08-06 15:53:55](https://github.com/leanprover-community/mathlib/commit/88f9480)
feat(logic/embedding): subtype_or_{embedding,equiv} ([#8489](https://github.com/leanprover-community/mathlib/pull/8489))
Provide explicit embedding from a subtype of a disjuction into a sum type.
If the disjunction is disjoint, upgrade to an equiv.
Additionally, provide `subtype.imp_embedding`, lowering a subtype
along an implication.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/logic/embedding.lean
- \+ *def* subtype.imp_embedding
- \+ *def* subtype_or_equiv
- \+ *lemma* subtype_or_equiv_symm_inl
- \+ *lemma* subtype_or_equiv_symm_inr
- \+ *def* subtype_or_left_embedding
- \+ *lemma* subtype_or_left_embedding_apply_left
- \+ *lemma* subtype_or_left_embedding_apply_right



## [2021-08-06 10:42:04](https://github.com/leanprover-community/mathlib/commit/a23c47c)
feat(topology/instances/ennreal): ediam of intervals ([#8546](https://github.com/leanprover-community/mathlib/pull/8546))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.zero_eq_of_real

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_finset_prod_of_ne_top
- \+/\- *lemma* real.diam_eq
- \+ *lemma* real.ediam_Icc
- \+ *lemma* real.ediam_Ico
- \+ *lemma* real.ediam_Ioc
- \+ *lemma* real.ediam_Ioo
- \+/\- *lemma* real.ediam_eq

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_pi_le_iff
- \+ *lemma* emetric.diam_pi_le_of_le

Modified src/topology/metric_space/holder.lean




## [2021-08-06 09:28:32](https://github.com/leanprover-community/mathlib/commit/da32780)
chore(data/polynomial/*): create file `data/polynomial/inductions` and move around lemmas ([#8563](https://github.com/leanprover-community/mathlib/pull/8563))
This PR is a precursor to [#8463](https://github.com/leanprover-community/mathlib/pull/8463): it performs the move, without introducing lemmas and squeezes some `simp`s to make some proofs faster.
I added add a doc-string to `lemma degree_pos_induction_on` with a reference to a lemma that will appear in [#8463](https://github.com/leanprover-community/mathlib/pull/8463).
The main reason why there are more added lines than removed ones is that the creation of a new file has a copyright statement, a module documentation and a few variable declarations.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.C_mul_X_pow_eq_self
- \+ *lemma* polynomial.monomial_nat_degree_leading_coeff_eq_self

Modified src/data/polynomial/degree/lemmas.lean
- \- *lemma* polynomial.C_mul_X_pow_eq_self
- \- *lemma* polynomial.degree_map'
- \- *lemma* polynomial.degree_map_eq_of_injective
- \- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \- *lemma* polynomial.leading_coeff_map'
- \- *lemma* polynomial.leading_coeff_map_of_leading_coeff_ne_zero
- \- *lemma* polynomial.monomial_nat_degree_leading_coeff_eq_self
- \- *lemma* polynomial.nat_degree_map'
- \- *lemma* polynomial.nat_degree_map_of_leading_coeff_ne_zero
- \- *lemma* polynomial.next_coeff_map

Modified src/data/polynomial/denoms_clearable.lean


Modified src/data/polynomial/div.lean
- \- *lemma* polynomial.coeff_div_X
- \- *lemma* polynomial.degree_div_X_lt
- \- *lemma* polynomial.degree_pos_induction_on
- \- *def* polynomial.div_X
- \- *lemma* polynomial.div_X_C
- \- *lemma* polynomial.div_X_add
- \- *lemma* polynomial.div_X_eq_zero_iff
- \- *lemma* polynomial.div_X_mul_X_add

Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+ *lemma* polynomial.leading_coeff_map_of_leading_coeff_ne_zero
- \+ *lemma* polynomial.nat_degree_map_of_leading_coeff_ne_zero

Added src/data/polynomial/inductions.lean
- \+ *lemma* polynomial.coeff_div_X
- \+ *lemma* polynomial.degree_div_X_lt
- \+ *lemma* polynomial.degree_pos_induction_on
- \+ *def* polynomial.div_X
- \+ *lemma* polynomial.div_X_C
- \+ *lemma* polynomial.div_X_add
- \+ *lemma* polynomial.div_X_eq_zero_iff
- \+ *lemma* polynomial.div_X_mul_X_add

Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.degree_map'
- \+ *lemma* polynomial.degree_map_eq_of_injective
- \+ *lemma* polynomial.leading_coeff_map'
- \+ *lemma* polynomial.nat_degree_map'
- \+ *lemma* polynomial.next_coeff_map

Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/ring_theory/roots_of_unity.lean




## [2021-08-06 09:28:31](https://github.com/leanprover-community/mathlib/commit/b9e4c08)
refactor(algebra/regular): split out `is_regular` ([#8561](https://github.com/leanprover-community/mathlib/pull/8561))
One would like to import `is_regular` for rings. However, group powers
are too late in the algebra hierarchy,
so the proofs of powers of regular elements are factored
out to a separate file.
#### Estimated changes
Renamed src/algebra/regular.lean to src/algebra/regular/basic.lean
- \- *lemma* is_left_regular.pow
- \- *lemma* is_left_regular.pow_iff
- \- *lemma* is_regular.pow
- \- *lemma* is_regular.pow_iff
- \- *lemma* is_right_regular.pow
- \- *lemma* is_right_regular.pow_iff

Added src/algebra/regular/pow.lean
- \+ *lemma* is_left_regular.pow
- \+ *lemma* is_left_regular.pow_iff
- \+ *lemma* is_regular.pow
- \+ *lemma* is_regular.pow_iff
- \+ *lemma* is_right_regular.pow
- \+ *lemma* is_right_regular.pow_iff

Renamed src/algebra/smul_regular.lean to src/algebra/regular/smul.lean


Modified src/representation_theory/maschke.lean




## [2021-08-06 09:28:30](https://github.com/leanprover-community/mathlib/commit/59c8bef)
feat (order/liminf_limsup): frequently_lt_of_lt_limsup ([#8548](https://github.com/leanprover-community/mathlib/pull/8548))
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.frequently_lt_of_liminf_lt
- \+ *lemma* filter.frequently_lt_of_lt_limsup



## [2021-08-06 09:28:29](https://github.com/leanprover-community/mathlib/commit/f471b89)
feat(topology,geometry/manifold): continuous and smooth partition of unity ([#8281](https://github.com/leanprover-community/mathlib/pull/8281))
Fixes [#6392](https://github.com/leanprover-community/mathlib/pull/6392)
#### Estimated changes
Modified src/geometry/manifold/bump_function.lean


Modified src/geometry/manifold/partition_of_unity.lean
- \+ *lemma* bump_covering.coe_to_smooth_partition_of_unity
- \+ *lemma* bump_covering.is_subordinate.to_smooth_partition_of_unity
- \+ *lemma* bump_covering.smooth_to_partition_of_unity
- \+ *def* bump_covering.to_smooth_partition_of_unity
- \+ *lemma* bump_covering.to_smooth_partition_of_unity_to_partition_of_unity
- \+ *lemma* exists_smooth_zero_one_of_closed
- \- *def* smooth_bump_covering.choice
- \- *def* smooth_bump_covering.choice_set
- \+/\- *lemma* smooth_bump_covering.coe_mk
- \+ *lemma* smooth_bump_covering.exists_finset_to_smooth_partition_of_unity_eventually_eq
- \+/\- *def* smooth_bump_covering.ind
- \+ *lemma* smooth_bump_covering.is_subordinate.support_subset
- \+ *lemma* smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity
- \+/\- *def* smooth_bump_covering.is_subordinate
- \+ *lemma* smooth_bump_covering.is_subordinate_to_bump_covering
- \+/\- *lemma* smooth_bump_covering.mem_chart_at_source_of_eq_one
- \+/\- *lemma* smooth_bump_covering.mem_ext_chart_at_source_of_eq_one
- \+ *lemma* smooth_bump_covering.sum_to_smooth_partition_of_unity_eq
- \+ *lemma* smooth_bump_covering.support_to_smooth_partition_of_unity_subset
- \+ *def* smooth_bump_covering.to_bump_covering
- \+ *def* smooth_bump_covering.to_smooth_partition_of_unity
- \+ *lemma* smooth_bump_covering.to_smooth_partition_of_unity_apply
- \+ *lemma* smooth_bump_covering.to_smooth_partition_of_unity_eq_mul_prod
- \+ *lemma* smooth_bump_covering.to_smooth_partition_of_unity_zero_of_zero
- \+ *lemma* smooth_partition_of_unity.exists_is_subordinate
- \+ *def* smooth_partition_of_unity.is_subordinate
- \+ *lemma* smooth_partition_of_unity.is_subordinate_to_partition_of_unity
- \+ *lemma* smooth_partition_of_unity.le_one
- \+ *lemma* smooth_partition_of_unity.nonneg
- \+ *def* smooth_partition_of_unity.single
- \+ *lemma* smooth_partition_of_unity.smooth_sum
- \+ *lemma* smooth_partition_of_unity.sum_eq_one
- \+ *lemma* smooth_partition_of_unity.sum_le_one
- \+ *lemma* smooth_partition_of_unity.sum_nonneg
- \+ *def* smooth_partition_of_unity.to_partition_of_unity

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth_at_one
- \+ *lemma* smooth_on_one
- \+ *lemma* smooth_one
- \+ *lemma* smooth_within_at_one
- \+ *lemma* times_cont_mdiff_at_one
- \+ *lemma* times_cont_mdiff_on_one
- \+ *lemma* times_cont_mdiff_one
- \+ *lemma* times_cont_mdiff_within_at_one

Modified src/geometry/manifold/times_cont_mdiff_map.lean
- \+ *lemma* times_cont_mdiff_map.coe_fn_mk

Modified src/geometry/manifold/whitney_embedding.lean
- \+ *lemma* exists_embedding_euclidean_of_compact
- \- *lemma* exists_embedding_finrank_of_compact
- \+/\- *def* smooth_bump_covering.embedding_pi_tangent
- \+/\- *lemma* smooth_bump_covering.embedding_pi_tangent_inj_on
- \+/\- *lemma* smooth_bump_covering.embedding_pi_tangent_injective
- \+ *lemma* smooth_bump_covering.exists_immersion_euclidean
- \- *lemma* smooth_bump_covering.exists_immersion_finrank

Modified src/topology/paracompact.lean


Added src/topology/partition_of_unity.lean
- \+ *lemma* bump_covering.coe_single
- \+ *lemma* bump_covering.continuous_to_pou_fun
- \+ *lemma* bump_covering.eventually_eq_one
- \+ *lemma* bump_covering.exists_finset_to_partition_of_unity_eventually_eq
- \+ *lemma* bump_covering.exists_finset_to_pou_fun_eventually_eq
- \+ *lemma* bump_covering.exists_is_subordinate
- \+ *lemma* bump_covering.exists_is_subordinate_of_locally_finite
- \+ *lemma* bump_covering.exists_is_subordinate_of_locally_finite_of_prop
- \+ *lemma* bump_covering.exists_is_subordinate_of_prop
- \+ *def* bump_covering.ind
- \+ *lemma* bump_covering.ind_apply
- \+ *lemma* bump_covering.is_subordinate.mono
- \+ *lemma* bump_covering.is_subordinate.to_partition_of_unity
- \+ *def* bump_covering.is_subordinate
- \+ *lemma* bump_covering.le_one
- \+ *lemma* bump_covering.nonneg
- \+ *lemma* bump_covering.sum_to_partition_of_unity_eq
- \+ *lemma* bump_covering.sum_to_pou_fun_eq
- \+ *lemma* bump_covering.support_to_partition_of_unity_subset
- \+ *lemma* bump_covering.support_to_pou_fun_subset
- \+ *def* bump_covering.to_partition_of_unity
- \+ *lemma* bump_covering.to_partition_of_unity_apply
- \+ *lemma* bump_covering.to_partition_of_unity_eq_mul_prod
- \+ *lemma* bump_covering.to_partition_of_unity_zero_of_zero
- \+ *def* bump_covering.to_pou_fun
- \+ *lemma* bump_covering.to_pou_fun_eq_mul_prod
- \+ *lemma* bump_covering.to_pou_fun_zero_of_zero
- \+ *lemma* partition_of_unity.exists_is_subordinate
- \+ *lemma* partition_of_unity.exists_is_subordinate_of_locally_finite
- \+ *def* partition_of_unity.is_subordinate
- \+ *lemma* partition_of_unity.le_one
- \+ *lemma* partition_of_unity.nonneg
- \+ *lemma* partition_of_unity.sum_eq_one
- \+ *lemma* partition_of_unity.sum_le_one
- \+ *lemma* partition_of_unity.sum_nonneg



## [2021-08-06 06:59:28](https://github.com/leanprover-community/mathlib/commit/dc6adcc)
feat(order/bounded_lattice): define the `distrib_lattice_bot` typeclass ([#8507](https://github.com/leanprover-community/mathlib/pull/8507))
Typeclass for a distributive lattice with a least element.
This typeclass is used to generalize `disjoint_sup_left` and similar.
It inserts itself in the hierarchy between `semilattice_sup_bot, semilattice_inf_bot` and `generalized_boolean_algebra`, `bounded_distrib_lattice`. I am doing it through `extends`.
#### Estimated changes
Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/partial_sups.lean
- \+/\- *lemma* partial_sups_disjoint_of_disjoint

Modified src/order/symm_diff.lean
- \+/\- *lemma* disjoint.disjoint_symm_diff_of_disjoint



## [2021-08-06 02:17:48](https://github.com/leanprover-community/mathlib/commit/e28d945)
chore(scripts): update nolints.txt ([#8562](https://github.com/leanprover-community/mathlib/pull/8562))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-08-06 00:12:02](https://github.com/leanprover-community/mathlib/commit/c2a0532)
feat(logic/unique,data/fintype/basic): unique and fintype of subtype of one element ([#8491](https://github.com/leanprover-community/mathlib/pull/8491))
Additionally, a lemma proving that the cardinality of such a subtype is 1.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_subtype_eq'
- \+ *lemma* fintype.card_subtype_eq

Modified src/logic/unique.lean




## [2021-08-05 20:49:21](https://github.com/leanprover-community/mathlib/commit/eb73c35)
docs(order/complete_boolean_algebra): add module docstring, add whitespaces ([#8525](https://github.com/leanprover-community/mathlib/pull/8525))
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean
- \+/\- *theorem* Inf_sup_Inf
- \+/\- *theorem* Sup_inf_Sup
- \+/\- *theorem* compl_Inf
- \+/\- *theorem* compl_Sup
- \+/\- *theorem* compl_infi
- \+/\- *theorem* compl_supr



## [2021-08-05 19:03:04](https://github.com/leanprover-community/mathlib/commit/c2ed7dc)
feat(logic/basic): `ite p a b` is equal to `a` or `b` ([#8557](https://github.com/leanprover-community/mathlib/pull/8557))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* ite_eq_or_eq



## [2021-08-05 19:03:03](https://github.com/leanprover-community/mathlib/commit/52b6516)
refactor(order/disjointed): generalize `disjointed` to generalized boolean algebras ([#8409](https://github.com/leanprover-community/mathlib/pull/8409))
- Split `data.set.disjointed` into `data.set.pairwise` and `order.disjointed`. Change imports accordingly.
- In `order.disjointed`, change `set α` to `generalized_boolean_algebra α`. Redefine `disjointed` in terms of `partial_sups` to avoid needing completeness. Keep set notation variants of lemmas for easier unification.
- Rename some lemmas and reorder their arguments to make dot notation functional.
- Generalize some (where some = 2) `pairwise` lemmas.
- Delete lemmas which are unused and are a straightforward `rw` away from a simpler one (`Union_disjointed_of_mono`).
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.bInter_lt_succ
- \+ *lemma* set.bUnion_lt_succ

Modified src/data/set/pairwise.lean
- \+/\- *theorem* pairwise.mono
- \+ *theorem* pairwise_disjoint_on
- \- *theorem* pairwise_disjoint_on_nat
- \- *theorem* pairwise_on_nat
- \+ *lemma* symmetric.pairwise_on

Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/pi_system.lean


Modified src/measure_theory/regular.lean


Modified src/order/disjointed.lean
- \+ *lemma* Union_disjointed
- \+ *lemma* disjoint_disjointed
- \+ *def* disjointed
- \+ *lemma* disjointed_eq_inf_compl
- \+ *lemma* disjointed_eq_inter_compl
- \+ *lemma* disjointed_le
- \+ *lemma* disjointed_le_id
- \+ *def* disjointed_rec
- \+ *lemma* disjointed_rec_zero
- \+ *lemma* disjointed_subset
- \+ *lemma* disjointed_succ
- \+ *lemma* disjointed_unique
- \+ *lemma* disjointed_zero
- \+ *lemma* monotone.disjointed_eq
- \+ *lemma* partial_sups_disjointed
- \- *lemma* set.Inter_lt_succ
- \- *lemma* set.Union_disjointed
- \- *lemma* set.Union_disjointed_of_mono
- \- *lemma* set.Union_lt_succ
- \- *lemma* set.disjoint_disjointed'
- \- *lemma* set.disjoint_disjointed
- \- *def* set.disjointed
- \- *lemma* set.disjointed_induct
- \- *lemma* set.disjointed_of_mono
- \- *lemma* set.disjointed_subset
- \- *lemma* set.subset_Union_disjointed
- \+ *lemma* supr_disjointed

Modified src/order/partial_sups.lean




## [2021-08-05 16:28:09](https://github.com/leanprover-community/mathlib/commit/8e79ea5)
feat(data/matrix/basic): add `alg_(hom|equiv).map_matrix` ([#8527](https://github.com/leanprover-community/mathlib/pull/8527))
This also adds a few standalone lemmas about `algebra_map`.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *def* alg_equiv.map_matrix
- \+ *lemma* alg_equiv.map_matrix_refl
- \+ *lemma* alg_equiv.map_matrix_symm
- \+ *lemma* alg_equiv.map_matrix_trans
- \+ *def* alg_hom.map_matrix
- \+ *lemma* alg_hom.map_matrix_comp
- \+ *lemma* alg_hom.map_matrix_id
- \+ *lemma* matrix.algebra_map_eq_diagonal
- \+ *lemma* matrix.algebra_map_eq_diagonal_ring_hom
- \+ *lemma* matrix.map_algebra_map



## [2021-08-05 12:24:03](https://github.com/leanprover-community/mathlib/commit/a0cb45f)
feat(linear_algebra/clifford_algebra): the reals and complex numbers have isomorphic real clifford algebras ([#8165](https://github.com/leanprover-community/mathlib/pull/8165))
#### Estimated changes
Added src/linear_algebra/clifford_algebra/equivs.lean
- \+ *def* clifford_algebra_complex.Q
- \+ *lemma* clifford_algebra_complex.Q_apply
- \+ *def* clifford_algebra_complex.to_complex
- \+ *lemma* clifford_algebra_complex.to_complex_ι
- \+ *lemma* clifford_algebra_ring.ι_eq_zero



## [2021-08-04 21:40:15](https://github.com/leanprover-community/mathlib/commit/ee8e447)
chore(category_theory/whiskering): Fix docstring ([#8533](https://github.com/leanprover-community/mathlib/pull/8533))
#### Estimated changes
Modified src/category_theory/whiskering.lean




## [2021-08-04 19:46:09](https://github.com/leanprover-community/mathlib/commit/d24faea)
chore(data/real/basic): drop some lemmas ([#8523](https://github.com/leanprover-community/mathlib/pull/8523))
Drop `real.Sup_le`, `real.lt_Sup`, `real.le_Sup`, `real.Sup_le_ub`, `real.le_Inf`, `real.Inf_lt`, `real.Inf_le`, `real.lb_le_Inf`. Use lemmas about `conditionally_complete_lattice`s instead.
Also drop unneeded assumptions in `real.lt_Inf_add_pos` and `real.add_neg_lt_Sup`.
#### Estimated changes
Modified archive/imo/imo1972_b2.lean


Modified src/algebra/pointwise.lean
- \+ *lemma* set.inv_empty
- \+ *lemma* set.inv_univ
- \+ *lemma* set.nonempty.inv
- \+ *lemma* set.nonempty_inv

Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/real/basic.lean
- \+/\- *lemma* real.Inf_def
- \- *theorem* real.Inf_le
- \- *theorem* real.Inf_lt
- \- *theorem* real.Sup_le
- \- *theorem* real.Sup_le_ub
- \+/\- *lemma* real.add_neg_lt_Sup
- \- *theorem* real.lb_le_Inf
- \- *theorem* real.le_Inf
- \- *theorem* real.le_Sup
- \+/\- *lemma* real.lt_Inf_add_pos
- \- *theorem* real.lt_Sup

Modified src/data/real/hyperreal.lean


Modified src/data/set/basic.lean
- \+ *lemma* function.surjective.nonempty_preimage

Modified src/topology/metric_space/basic.lean




## [2021-08-04 16:20:15](https://github.com/leanprover-community/mathlib/commit/4e9b18b)
chore(order/basic): rename monotone_of_monotone_nat and strict_mono.nat ([#8550](https://github.com/leanprover-community/mathlib/pull/8550))
For more coherence (and easier discoverability), rename `monotone_of_monotone_nat` to `monotone_nat_of_le_succ`, and `strict_mono.nat` to `strict_mono_nat_of_lt_succ`.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified archive/imo/imo1977_q6.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/pointwise.lean


Modified src/data/equiv/encodable/basic.lean


Modified src/data/list/basic.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/fib.lean


Modified src/data/nat/log.lean


Modified src/linear_algebra/prod.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/regular.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/order/basic.lean
- \+ *lemma* monotone_nat_of_le_succ
- \- *lemma* monotone_of_monotone_nat
- \+ *lemma* strict_mono_nat_of_lt_succ

Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/ideal.lean


Modified src/order/partial_sups.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/subset_properties.lean


Modified src/topology/urysohns_lemma.lean




## [2021-08-04 08:58:37](https://github.com/leanprover-community/mathlib/commit/3a9b25d)
fix(order/lattice): make non-instances reducible ([#8541](https://github.com/leanprover-community/mathlib/pull/8541))
Some early fixes for the new linter in [#8540](https://github.com/leanprover-community/mathlib/pull/8540).
#### Estimated changes
Modified src/order/bounded_lattice.lean


Modified src/order/lattice.lean




## [2021-08-04 08:58:36](https://github.com/leanprover-community/mathlib/commit/1691c6c)
feat(algebra/opposites): {add,mul,ring}_equiv.op ([#8535](https://github.com/leanprover-community/mathlib/pull/8535))
We had the equivalences of homs. Now we have equivalences of isos.
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *def* add_equiv.op
- \+ *def* add_equiv.unop
- \+ *def* mul_equiv.op
- \+ *def* mul_equiv.unop

Modified src/data/equiv/ring.lean




## [2021-08-04 08:58:35](https://github.com/leanprover-community/mathlib/commit/096bdb7)
refactor(group_theory/solvable): move subgroup commutators into new file ([#8534](https://github.com/leanprover-community/mathlib/pull/8534))
The theory of nilpotent subgroups also needs a theory of general commutators (if H,K : subgroup G then so is [H,K]), but I don't really want to import solvable groups to get nilpotent groups, so I am breaking the solvable group file into two, splitting off the API for these commutators.
#### Estimated changes
Added src/group_theory/general_commutator.lean
- \+ *lemma* bot_general_commutator
- \+ *lemma* general_commutator_bot
- \+ *lemma* general_commutator_comm
- \+ *lemma* general_commutator_containment
- \+ *lemma* general_commutator_def'
- \+ *lemma* general_commutator_def
- \+ *lemma* general_commutator_le
- \+ *lemma* general_commutator_le_inf
- \+ *lemma* general_commutator_le_left
- \+ *lemma* general_commutator_le_right
- \+ *lemma* general_commutator_mono

Modified src/group_theory/solvable.lean
- \- *lemma* bot_general_commutator
- \- *lemma* general_commutator_bot
- \- *lemma* general_commutator_comm
- \- *lemma* general_commutator_containment
- \- *lemma* general_commutator_def'
- \- *lemma* general_commutator_def
- \- *lemma* general_commutator_le
- \- *lemma* general_commutator_le_inf
- \- *lemma* general_commutator_le_left
- \- *lemma* general_commutator_le_right
- \- *lemma* general_commutator_mono



## [2021-08-04 07:05:50](https://github.com/leanprover-community/mathlib/commit/292e3fa)
refactor(nat/basic): Move lemma about nat ([#8539](https://github.com/leanprover-community/mathlib/pull/8539))
#### Estimated changes
Modified src/algebra/group/hom_instances.lean


Modified src/algebra/ordered_ring.lean
- \- *lemma* nat.succ_eq_one_add

Modified src/data/nat/basic.lean
- \+ *lemma* nat.succ_eq_one_add



## [2021-08-03 20:19:03](https://github.com/leanprover-community/mathlib/commit/8502571)
feat(topology/discrete_quotient): add two lemmas ([#8464](https://github.com/leanprover-community/mathlib/pull/8464))
Add lemmas `proj_bot_injective` and `proj_bot_bijective`, the former needed for the latter, and the latter needed in LTE.
#### Estimated changes
Modified src/topology/discrete_quotient.lean
- \+ *lemma* discrete_quotient.proj_bot_bijective
- \+ *lemma* discrete_quotient.proj_bot_injective

Modified src/topology/subset_properties.lean
- \+ *lemma* is_clopen_discrete



## [2021-08-03 19:43:28](https://github.com/leanprover-community/mathlib/commit/d366672)
feat(measure_theory/integration): add some `with_density` lemmas ([#8517](https://github.com/leanprover-community/mathlib/pull/8517))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.finite_measure_with_density
- \+ *lemma* measure_theory.lintegral_in_measure_zero
- \+ *lemma* measure_theory.with_density_absolutely_continuous
- \+ *lemma* measure_theory.with_density_add
- \+ *lemma* measure_theory.with_density_smul'
- \+ *lemma* measure_theory.with_density_smul



## [2021-08-03 17:55:51](https://github.com/leanprover-community/mathlib/commit/9d129dc)
feat(algebra/bounds): a few lemmas like `bdd_above (-s) ↔ bdd_below s` ([#8522](https://github.com/leanprover-community/mathlib/pull/8522))
#### Estimated changes
Added src/algebra/bounds.lean
- \+ *lemma* bdd_above.inv
- \+ *lemma* bdd_above.mul
- \+ *lemma* bdd_above_inv
- \+ *lemma* bdd_below.inv
- \+ *lemma* bdd_below.mul
- \+ *lemma* bdd_below_inv
- \+ *lemma* is_glb.inv
- \+ *lemma* is_glb_inv'
- \+ *lemma* is_glb_inv
- \+ *lemma* is_lub.inv
- \+ *lemma* is_lub_inv'
- \+ *lemma* is_lub_inv
- \+ *lemma* mul_mem_lower_bounds_mul
- \+ *lemma* mul_mem_upper_bounds_mul
- \+ *lemma* subset_lower_bounds_mul
- \+ *lemma* subset_upper_bounds_mul

Modified src/algebra/ordered_group.lean


Modified src/order/bounds.lean
- \+ *lemma* order_iso.is_glb_image'
- \+ *lemma* order_iso.is_glb_preimage'
- \+ *lemma* order_iso.is_lub_image'
- \+ *lemma* order_iso.is_lub_preimage'

Modified src/order/galois_connection.lean
- \+ *lemma* order_iso.bdd_above_preimage
- \+ *lemma* order_iso.bdd_below_preimage



## [2021-08-03 16:52:11](https://github.com/leanprover-community/mathlib/commit/c543ec9)
feat(topology/algebra/ordered/basic): sequences tending to Inf/Sup ([#8524](https://github.com/leanprover-community/mathlib/pull/8524))
We show that there exist monotone sequences tending to the Inf/Sup of a set in a conditionally complete linear order, as well as several related lemmas expressed in terms of `is_lub` and `is_glb`.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* exists_seq_strict_antimono_tendsto
- \+ *lemma* exists_seq_strict_mono_tendsto
- \+ *lemma* exists_seq_tendsto_Inf
- \+ *lemma* exists_seq_tendsto_Sup
- \+ *lemma* is_glb.exists_seq_monotone_tendsto'
- \+ *lemma* is_glb.exists_seq_monotone_tendsto
- \+ *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem'
- \+ *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem
- \+ *lemma* is_glb_of_mem_closure
- \+ *lemma* is_lub.exists_seq_monotone_tendsto'
- \+ *lemma* is_lub.exists_seq_monotone_tendsto
- \+ *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem'
- \+ *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem
- \+ *lemma* is_lub_of_mem_closure



## [2021-08-03 15:41:09](https://github.com/leanprover-community/mathlib/commit/2b3cffd)
feat(algebra/floor): notation for nat_floor and nat_ceil ([#8526](https://github.com/leanprover-community/mathlib/pull/8526))
We introduce the notations ` ⌊a⌋₊` for `nat_floor a` and `⌈a⌉₊` for `nat_ceil a`, mimicking the existing notations for `floor` and `ceil` (with the `+` corresponding to the recent notation for `nnnorm`).
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/floor.lean
- \+/\- *lemma* ceil_eq_on_Ioc'
- \+/\- *lemma* ceil_eq_on_Ioc
- \+/\- *lemma* floor_eq_on_Ico'
- \+/\- *lemma* floor_eq_on_Ico
- \+/\- *lemma* int.preimage_Ici
- \+/\- *lemma* int.preimage_Iic
- \+/\- *lemma* int.preimage_Iio
- \+/\- *lemma* int.preimage_Ioi
- \+/\- *theorem* le_nat_ceil
- \+/\- *theorem* le_nat_floor_iff
- \+/\- *lemma* le_nat_floor_of_le
- \+/\- *lemma* le_of_nat_ceil_le
- \+/\- *theorem* lt_nat_ceil
- \+/\- *lemma* lt_nat_floor_add_one
- \+/\- *lemma* lt_of_lt_nat_floor
- \+/\- *lemma* lt_of_nat_ceil_lt
- \+/\- *theorem* nat_ceil_add_nat
- \+/\- *theorem* nat_ceil_coe
- \+/\- *theorem* nat_ceil_le
- \+/\- *theorem* nat_ceil_lt_add_one
- \+/\- *theorem* nat_ceil_mono
- \+/\- *theorem* nat_ceil_zero
- \+/\- *theorem* nat_floor_add_nat
- \+/\- *theorem* nat_floor_coe
- \+/\- *lemma* nat_floor_eq_zero_iff
- \+/\- *lemma* nat_floor_le
- \+/\- *theorem* nat_floor_lt_iff
- \+/\- *theorem* nat_floor_mono
- \+/\- *lemma* nat_floor_of_nonpos
- \+/\- *theorem* nat_floor_zero
- \+/\- *lemma* pos_of_nat_floor_pos

Modified src/analysis/special_functions/exp_log.lean


Modified src/data/real/basic.lean


Modified src/data/real/pi.lean


Modified src/measure_theory/borel_space.lean




## [2021-08-03 11:13:43](https://github.com/leanprover-community/mathlib/commit/1700b3c)
chore(ring_theory/fractional_ideal): make `coe : ideal → fractional_ideal` a `coe_t` ([#8529](https://github.com/leanprover-community/mathlib/pull/8529))
This noticeably speeds up elaboration of `dedekind_domain.lean`, since it discourages the elaborator from going down a (nearly?)-looping path.
See also this Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Priority.20of.20.60coe_sort_trans.60
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean




## [2021-08-03 11:13:41](https://github.com/leanprover-community/mathlib/commit/5afd09a)
chore(data/matrix/basic): move bundled versions of `matrix.map` beneath the algebra structure ([#8528](https://github.com/leanprover-community/mathlib/pull/8528))
This will give us an obvious place to add the bundled alg_hom version in a follow-up PR.
None of the moved lines have been modified.
Note that the git diff shows that instead of `matrix.map` moving down, the `algebra` structure has moved up.
#### Estimated changes
Modified src/data/matrix/basic.lean




## [2021-08-03 11:13:40](https://github.com/leanprover-community/mathlib/commit/3f4b836)
feat(order/bounds): add `is_lub_pi` and `is_glb_pi` ([#8521](https://github.com/leanprover-community/mathlib/pull/8521))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* function.monotone_eval

Modified src/order/bounds.lean
- \+ *lemma* is_glb_pi
- \+ *lemma* is_lub_pi



## [2021-08-03 11:13:39](https://github.com/leanprover-community/mathlib/commit/ad83714)
feat(fractional_ideal): `coe : ideal → fractional_ideal` as ring hom ([#8511](https://github.com/leanprover-community/mathlib/pull/8511))
This PR bundles the coercion from integral ideals to fractional ideals as a ring hom, and proves the missing `simp` lemmas that show the map indeed preserves the ring structure.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *def* fractional_ideal.coe_ideal_hom
- \+ *lemma* fractional_ideal.coe_ideal_mul
- \+ *lemma* fractional_ideal.coe_ideal_sup

Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.coe_submodule_bot
- \+ *lemma* is_localization.coe_submodule_mul
- \+ *lemma* is_localization.coe_submodule_sup



## [2021-08-03 09:27:49](https://github.com/leanprover-community/mathlib/commit/b681b6b)
chore(order/bounds): add `@[simp]` attrs, add `not_bdd_*_univ` ([#8520](https://github.com/leanprover-community/mathlib/pull/8520))
#### Estimated changes
Modified src/order/bounds.lean
- \+/\- *lemma* no_bot_order.lower_bounds_univ
- \+/\- *lemma* no_top_order.upper_bounds_univ
- \+ *lemma* not_bdd_above_univ
- \+ *lemma* not_bdd_below_univ
- \+/\- *lemma* order_bot.lower_bounds_univ
- \+/\- *lemma* order_top.upper_bounds_univ



## [2021-08-03 07:45:29](https://github.com/leanprover-community/mathlib/commit/1021679)
feat(algebra/ordered_monoid): a few more `order_dual` instances ([#8519](https://github.com/leanprover-community/mathlib/pull/8519))
* add `covariant.flip` and `contravariant.flip`;
* add `[to_additive]` to `group.covariant_iff_contravariant` and
  `covconv` (renamed to `group.covconv`);
* use `group.covconv` in
  `group.covariant_class_le.to_contravariant_class_le`;
* add some `order_dual` instances for `covariant_class` and
  `contravariant_class`;
* golf `order_dual.ordered_comm_monoid`.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* contravariant.flip
- \+ *lemma* covariant.flip
- \- *lemma* covconv
- \+ *lemma* group.covconv

Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean




## [2021-08-02 23:06:35](https://github.com/leanprover-community/mathlib/commit/0bef4a0)
feat(algebra/group_with_zero): pullback a `comm_cancel_monoid_with_zero` instance across an injective hom ([#8515](https://github.com/leanprover-community/mathlib/pull/8515))
This generalizes `function.injective.cancel_monoid_with_zero` to the commutative case.
See also: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/A.20submonoid.20of.20a.20.60cancel_monoid_with_zero.60.20also.20cancels
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean




## [2021-08-02 21:14:46](https://github.com/leanprover-community/mathlib/commit/2568d41)
feat(data/matrix/basic): Add bundled versions of matrix.diagonal ([#8510](https://github.com/leanprover-community/mathlib/pull/8510))
Also shows injectivity of `diagonal`.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.diagonal
- \+/\- *theorem* matrix.diagonal_add
- \+ *def* matrix.diagonal_add_monoid_hom
- \+ *def* matrix.diagonal_alg_hom
- \+ *lemma* matrix.diagonal_injective
- \+ *def* matrix.diagonal_linear_map
- \+ *def* matrix.diagonal_ring_hom
- \+ *theorem* matrix.diagonal_smul



## [2021-08-02 21:14:45](https://github.com/leanprover-community/mathlib/commit/77d6c8e)
feat(simps): better name for additivized simps-lemmas ([#8457](https://github.com/leanprover-community/mathlib/pull/8457))
* When using `@[to_additive foo, simps]`, the additivized simp-lemmas will have name `foo` + projection suffix (or prefix)
* Also add an option for `@[to_additive]` to accept the attribute with the correct given name. This is only useful when adding the `@[to_additive]` attribute via metaprogramming, so this option cannot be set by the `to_additive` argument parser.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* some_test1



## [2021-08-02 20:14:32](https://github.com/leanprover-community/mathlib/commit/17f1d28)
chore(data/matrix): delete each of the `matrix.foo_hom_map_zero` ([#8512](https://github.com/leanprover-community/mathlib/pull/8512))
These can already be found by `simp` since `matrix.map_zero` is a `simp` lemma, and we can manually use `foo_hom.map_matrix.map_zero` introduced by [#8468](https://github.com/leanprover-community/mathlib/pull/8468) instead. They also don't seem to be used anywhere in mathlib, given that deleting them with no replacement causes no build errors.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *lemma* matrix.add_equiv_map_zero
- \- *lemma* matrix.add_monoid_hom_map_zero
- \- *lemma* matrix.alg_equiv_map_one
- \- *lemma* matrix.alg_equiv_map_zero
- \- *lemma* matrix.alg_hom_map_one
- \- *lemma* matrix.alg_hom_map_zero
- \- *lemma* matrix.linear_equiv_map_zero
- \- *lemma* matrix.linear_map_map_zero
- \- *lemma* matrix.ring_equiv_map_one
- \- *lemma* matrix.ring_equiv_map_zero
- \- *lemma* matrix.ring_hom_map_one
- \- *lemma* matrix.ring_hom_map_zero
- \- *lemma* matrix.zero_hom_map_zero



## [2021-08-02 17:05:53](https://github.com/leanprover-community/mathlib/commit/17b1e7c)
feat(data/equiv/mul_add): add `equiv.(div,sub)_(left,right)` ([#8385](https://github.com/leanprover-community/mathlib/pull/8385))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* equiv.div_left_eq_inv_trans_mul_left
- \+ *lemma* equiv.div_right_eq_mul_right_inv



## [2021-08-02 14:22:13](https://github.com/leanprover-community/mathlib/commit/9a251f1)
refactor(data/matrix/basic): merge duplicate algebra structures ([#8486](https://github.com/leanprover-community/mathlib/pull/8486))
By putting the algebra instance in the same file as `scalar`, a future patch can probably remove `matrix.scalar` entirely (it's just another spelling of `algebra_map`).
Note that we actually had two instances of `algebra R (matrix n n R)` in different files, and the second one was strictly more general than the first. This removes the less general one.
Moving the imports around like this changes the number of simp lemmas available in downstream files, which can make `simp` slow enough to push a proof into a timeout.
A lot of files were expecting a transitive import of `algebra.algebra.basic` to import `data.fintype.card`, which it no longer does; hence the need to add this import explicitly.
There are no new lemmas or generalizations in this change; the old `matrix_algebra` has been deleted, and everything else has been moved with some variables renamed.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* matrix.alg_equiv_map_one
- \- *lemma* matrix.alg_equiv_map_zero
- \- *lemma* matrix.alg_hom_map_one
- \- *lemma* matrix.alg_hom_map_zero
- \- *lemma* matrix.algebra_map_eq_smul

Modified src/algebra/lie/weights.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.alg_equiv_map_one
- \+ *lemma* matrix.alg_equiv_map_zero
- \+ *lemma* matrix.alg_hom_map_one
- \+ *lemma* matrix.alg_hom_map_zero
- \+ *lemma* matrix.algebra_map_eq_smul
- \+ *lemma* matrix.algebra_map_matrix_apply

Modified src/group_theory/specific_groups/dihedral.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/linear_algebra/matrix/finite_dimensional.lean


Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/multilinear.lean


Modified src/ring_theory/matrix_algebra.lean
- \- *lemma* algebra_map_matrix_apply

Modified src/ring_theory/polynomial/symmetric.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/topology/algebra/infinite_sum.lean




## [2021-08-02 12:31:20](https://github.com/leanprover-community/mathlib/commit/c8b7816)
feat(algebra/ordered_monoid): add_eq_bot_iff ([#8474](https://github.com/leanprover-community/mathlib/pull/8474))
bot addition is saturating on the bottom. On the way, typeclass arguments
were relaxed to just `[add_semigroup α]`, and helper simp lemmas
added for `bot`.
The iff lemma added (`add_eq_bot`) is not exactly according to the naming convention, but matches the top lemma and related ones in the naming style, so the style is kept consistent.
There is an API proof available, but the defeq proof (using the top equivalent) was used based on suggestions.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \+/\- *lemma* with_bot.add_bot
- \+ *lemma* with_bot.add_eq_bot
- \+/\- *lemma* with_bot.bot_add

Modified src/order/bounded_lattice.lean
- \+ *theorem* with_bot.bot_ne_coe
- \+ *theorem* with_bot.coe_ne_bot



## [2021-08-02 12:31:19](https://github.com/leanprover-community/mathlib/commit/f354c1b)
feat(order/bounded_lattice): add some disjoint lemmas ([#8407](https://github.com/leanprover-community/mathlib/pull/8407))
This adds `disjoint.inf_left` and `disjoint.inf_right` (and primed variants) to match the existing `disjoint.sup_left` and `disjoint.sup_right`.
This also duplicates these lemmas to use set notation with `inter` instead of `inf`, matching the existing `disjoint.union_left` and `disjoint.union_right`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.inter_left'
- \+ *lemma* disjoint.inter_left
- \+ *lemma* disjoint.inter_right'
- \+ *lemma* disjoint.inter_right

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.inf_left'
- \+ *lemma* disjoint.inf_left
- \+ *lemma* disjoint.inf_right'
- \+ *lemma* disjoint.inf_right



## [2021-08-02 11:38:23](https://github.com/leanprover-community/mathlib/commit/af8e56a)
docs(overview): add holder continuity ([#8506](https://github.com/leanprover-community/mathlib/pull/8506))
#### Estimated changes
Modified docs/overview.yaml




## [2021-08-02 11:38:22](https://github.com/leanprover-community/mathlib/commit/25a4230)
chore(data/real/basic): cleanup ([#8501](https://github.com/leanprover-community/mathlib/pull/8501))
* use `is_lub` etc in the statement of `real.exists_sup`, rename it to `real.exists_is_lub`;
* move parts of the proof of `real.exists_is_lub` around;
#### Estimated changes
Modified src/data/real/basic.lean
- \+ *theorem* real.exists_is_lub
- \- *theorem* real.exists_sup



## [2021-08-02 10:07:38](https://github.com/leanprover-community/mathlib/commit/69c6adb)
chore(data/int): move some lemmas from `basic` to a new file ([#8495](https://github.com/leanprover-community/mathlib/pull/8495))
Move `least_of_bdd`, `exists_least_of_bdd`, `coe_least_of_bdd_eq`,
`greatest_of_bdd`, `exists_greatest_of_bdd`, and
`coe_greatest_of_bdd_eq` from `data.int.basic` to `data.int.least_greatest`.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/data/int/basic.lean
- \- *lemma* int.coe_greatest_of_bdd_eq
- \- *lemma* int.coe_least_of_bdd_eq
- \- *theorem* int.exists_greatest_of_bdd
- \- *theorem* int.exists_least_of_bdd
- \- *def* int.greatest_of_bdd
- \- *def* int.least_of_bdd

Added src/data/int/least_greatest.lean
- \+ *lemma* int.coe_greatest_of_bdd_eq
- \+ *lemma* int.coe_least_of_bdd_eq
- \+ *theorem* int.exists_greatest_of_bdd
- \+ *theorem* int.exists_least_of_bdd
- \+ *def* int.greatest_of_bdd
- \+ *def* int.least_of_bdd

Modified src/data/int/order.lean




## [2021-08-02 10:07:37](https://github.com/leanprover-community/mathlib/commit/4a9cbdb)
feat(data/matrix/basic): provide equiv versions of `matrix.map`, `linear_map.map_matrix`, and `ring_hom.map_matrix`. ([#8468](https://github.com/leanprover-community/mathlib/pull/8468))
This moves all of these definitions to be adjacent, adds the standard family of functorial simp lemmas, and relaxes some typeclass requirements.
This also renames `matrix.one_map` to `matrix.map_one` to match `matrix.map_zero`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/data/matrix/basic.lean
- \+ *def* add_equiv.map_matrix
- \+ *lemma* add_equiv.map_matrix_refl
- \+ *lemma* add_equiv.map_matrix_symm
- \+ *lemma* add_equiv.map_matrix_trans
- \+/\- *def* add_monoid_hom.map_matrix
- \- *lemma* add_monoid_hom.map_matrix_apply
- \+ *lemma* add_monoid_hom.map_matrix_comp
- \+ *lemma* add_monoid_hom.map_matrix_id
- \+ *def* equiv.map_matrix
- \+ *lemma* equiv.map_matrix_refl
- \+ *lemma* equiv.map_matrix_symm
- \+ *lemma* equiv.map_matrix_trans
- \+ *def* linear_equiv.map_matrix
- \+ *lemma* linear_equiv.map_matrix_refl
- \+ *lemma* linear_equiv.map_matrix_symm
- \+ *lemma* linear_equiv.map_matrix_trans
- \+/\- *def* linear_map.map_matrix
- \+ *lemma* linear_map.map_matrix_comp
- \+ *lemma* linear_map.map_matrix_id
- \+/\- *lemma* matrix.map_add
- \+ *lemma* matrix.map_id
- \+ *lemma* matrix.map_one
- \+/\- *lemma* matrix.map_smul
- \+/\- *lemma* matrix.map_sub
- \+/\- *lemma* matrix.map_zero
- \- *lemma* matrix.one_map
- \+ *def* ring_equiv.map_matrix
- \+ *lemma* ring_equiv.map_matrix_refl
- \+ *lemma* ring_equiv.map_matrix_symm
- \+ *lemma* ring_equiv.map_matrix_trans
- \+/\- *def* ring_hom.map_matrix
- \+ *lemma* ring_hom.map_matrix_comp
- \+ *lemma* ring_hom.map_matrix_id



## [2021-08-02 08:51:21](https://github.com/leanprover-community/mathlib/commit/1b771af)
feat(group_theory/coset): card_dvd_of_injective ([#8485](https://github.com/leanprover-community/mathlib/pull/8485))
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* subgroup.card_comap_dvd_of_injective
- \+ *lemma* subgroup.card_dvd_of_injective
- \+ *lemma* subgroup.card_dvd_of_le



## [2021-08-02 02:56:39](https://github.com/leanprover-community/mathlib/commit/0f168d3)
refactor(data/real/nnreal): use `ord_connected_subset_conditionally_complete_linear_order` ([#8502](https://github.com/leanprover-community/mathlib/pull/8502))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.coe_Inf
- \+/\- *lemma* nnreal.coe_Sup



## [2021-08-02 02:56:38](https://github.com/leanprover-community/mathlib/commit/5994df1)
feat(algebra/group_power/lemmas): is_unit_pos_pow_iff ([#8420](https://github.com/leanprover-community/mathlib/pull/8420))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* is_unit_pos_pow_iff



## [2021-08-02 02:15:39](https://github.com/leanprover-community/mathlib/commit/db0cd4d)
chore(scripts): update nolints.txt ([#8505](https://github.com/leanprover-community/mathlib/pull/8505))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-08-01 22:56:38](https://github.com/leanprover-community/mathlib/commit/bfa6bbb)
doc(algebra/algebra/basic): add a comment to make the similar definition discoverable ([#8500](https://github.com/leanprover-community/mathlib/pull/8500))
I couldn't find this def, but was able to find lmul.
#### Estimated changes
Modified src/algebra/algebra/basic.lean




## [2021-08-01 21:03:45](https://github.com/leanprover-community/mathlib/commit/fdb0369)
feat(algebra/group/semiconj): add `semiconj_by.reflexive` and `semiconj_by.transitive` ([#8493](https://github.com/leanprover-community/mathlib/pull/8493))
#### Estimated changes
Modified src/algebra/group/semiconj.lean




## [2021-08-01 21:03:44](https://github.com/leanprover-community/mathlib/commit/60c378d)
feat(algebra/ordered_group): add `order_iso.inv` ([#8492](https://github.com/leanprover-community/mathlib/pull/8492))
* add `order_iso.inv` and `order_iso.neg`;
* use it to golf a few proofs;
* use `alias` to generate some `imp` lemmas from `iff` lemmas;
* generalize some lemmas about `order_iso` from `preorder` to `has_le`.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \- *lemma* inv_le_of_inv_le
- \- *lemma* inv_lt_of_inv_lt
- \- *lemma* lt_inv_of_lt_inv
- \+ *def* order_iso.inv

Modified src/order/rel_iso.lean




## [2021-08-01 21:03:43](https://github.com/leanprover-community/mathlib/commit/1530d76)
feat(group_theory/congruence): add `con.lift_on_units` etc ([#8488](https://github.com/leanprover-community/mathlib/pull/8488))
Add a helper function that makes it easier to define a function on
`units (con.quotient c)`.
#### Estimated changes
Modified src/group_theory/congruence.lean
- \+ *lemma* con.hrec_on₂_coe
- \+ *lemma* con.induction_on_units
- \+ *def* con.lift_on_units
- \+ *lemma* con.lift_on_units_mk
- \+ *lemma* con.quot_mk_eq_coe
- \+ *lemma* con.rel_mk



## [2021-08-01 21:03:42](https://github.com/leanprover-community/mathlib/commit/9c4dd02)
feat(group_theory/order_of_element): order_of_dvd_iff_gpow_eq_one ([#8487](https://github.com/leanprover-community/mathlib/pull/8487))
Version of `order_of_dvd_iff_pow_eq_one` for integer powers
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_dvd_iff_gpow_eq_one



## [2021-08-01 21:03:41](https://github.com/leanprover-community/mathlib/commit/9194f20)
feat(data/nat/prime): pow_dvd_of_dvd_mul_right ([#8483](https://github.com/leanprover-community/mathlib/pull/8483))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.pow_dvd_of_dvd_mul_left
- \+ *lemma* nat.prime.pow_dvd_of_dvd_mul_right



## [2021-08-01 21:03:40](https://github.com/leanprover-community/mathlib/commit/b099103)
feat(group_theory/subgroup): add `subgroup.forall_gpowers` etc ([#8470](https://github.com/leanprover-community/mathlib/pull/8470))
* add `subgroup.forall_gpowers`, `subgroup.exists_gpowers`,
  `subgroup.forall_mem_gpowers`, and `subgroup.exists_mem_gpowers`;
* add their additive counterparts;
* drop some explicit lemmas about `add_subgroup.gmultiples`:
  `to_additive` can generate them now.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.exists_subtype_range_iff
- \+ *theorem* set.forall_subtype_range_iff

Modified src/group_theory/subgroup.lean
- \- *lemma* add_subgroup.gmultiples_eq_closure
- \- *lemma* add_subgroup.mem_gmultiples
- \- *lemma* add_subgroup.mem_gmultiples_iff
- \+ *lemma* subgroup.exists_gpowers
- \+ *lemma* subgroup.exists_mem_gpowers
- \+ *lemma* subgroup.forall_gpowers
- \+ *lemma* subgroup.forall_mem_gpowers



## [2021-08-01 21:03:39](https://github.com/leanprover-community/mathlib/commit/52a2e8b)
chore(algebra/group/hom_instances): add monoid_hom versions of linear_map lemmas ([#8461](https://github.com/leanprover-community/mathlib/pull/8461))
I mainly want the additive versions, but we may as well get the multiplicative ones too.
This also adds the missing `monoid_hom.map_div` and some other division versions of subtraction lemmas.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \- *lemma* add_monoid_hom.coe_of_map_sub
- \- *theorem* add_monoid_hom.map_sub
- \- *def* add_monoid_hom.of_map_sub
- \+ *lemma* monoid_hom.coe_of_map_div
- \+ *theorem* monoid_hom.map_div
- \+ *def* monoid_hom.of_map_div

Modified src/algebra/group/hom_instances.lean
- \+ *lemma* monoid_hom.map_div₂
- \+ *lemma* monoid_hom.map_inv₂
- \+ *lemma* monoid_hom.map_mul₂
- \+ *lemma* monoid_hom.map_one₂



## [2021-08-01 21:03:36](https://github.com/leanprover-community/mathlib/commit/894fb0c)
feat(data/nat/totient): totient_prime_pow ([#8353](https://github.com/leanprover-community/mathlib/pull/8353))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.coprime_pow_left_iff
- \+ *lemma* nat.coprime_pow_right_iff

Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_eq_card_coprime
- \+ *theorem* nat.totient_one
- \+ *lemma* nat.totient_prime
- \+ *lemma* nat.totient_prime_pow
- \+ *lemma* nat.totient_prime_pow_succ
- \+ *lemma* nat.totient_two



## [2021-08-01 19:11:26](https://github.com/leanprover-community/mathlib/commit/7249afb)
feat(measure_theory/[integrable_on, set_integral]): integrals on two ae-eq sets are equal ([#8440](https://github.com/leanprover-community/mathlib/pull/8440))
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* measure_theory.integrable_on.congr_set_ae

Modified src/measure_theory/measure_space.lean
- \+ *lemma* indicator_ae_eq_of_ae_eq_set
- \+ *lemma* piecewise_ae_eq_of_ae_eq_set

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.set_integral_congr_set_ae



## [2021-08-01 19:11:25](https://github.com/leanprover-community/mathlib/commit/d3c943b)
refactor(data/set/lattice): add congr lemmas for `Prop`-indexed `Union` and `Inter` ([#8260](https://github.com/leanprover-community/mathlib/pull/8260))
Thanks to new `@[congr]` lemmas `Union_congr_Prop` and `Inter_congr_Prop`, `simp` can simplify `p y` in `⋃ y (h : p y), f y`. As a result, LHS of many lemmas (e.g., `Union_image`) is no longer in `simp` normal form. E.g.,
```lean
lemma bUnion_range {f : ι → α} {g : α → set β} : (⋃x ∈ range f, g x) = (⋃y, g (f y)) :=
```
can no longer be a `@[simp]` lemma because `simp` simplifies `⋃x ∈ range f, g x` to `⋃ (x : α) (h : ∃ i, f i = x), g x`, then to `⋃ (x : α) (i : α) (h : f i = x), g x`. So, we add
```lean
@[simp] lemma Union_Union_eq' {f : ι → α} {g : α → set β} :
  (⋃ x y (h : f y = x), g x) = ⋃ y, g (f y) :=
```
Also, `Union` and `Inter` are semireducible, so one has to explicitly convert between these operations and `supr`/`infi`.
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.set_bInter_bUnion
- \+/\- *theorem* finset.set_bInter_coe
- \+/\- *lemma* finset.set_bInter_finset_image
- \+/\- *lemma* finset.set_bInter_insert
- \+/\- *lemma* finset.set_bInter_option_to_finset
- \+/\- *theorem* finset.set_bInter_singleton
- \+/\- *lemma* finset.set_bUnion_bUnion
- \+/\- *theorem* finset.set_bUnion_coe
- \+/\- *lemma* finset.set_bUnion_finset_image
- \+/\- *lemma* finset.set_bUnion_insert
- \+/\- *lemma* finset.set_bUnion_option_to_finset
- \+/\- *theorem* finset.set_bUnion_singleton

Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.Inf_eq_sInter
- \+/\- *def* set.Inter
- \+ *lemma* set.Inter_Inter_eq'
- \+ *theorem* set.Inter_Inter_eq_left
- \+ *theorem* set.Inter_Inter_eq_or_left
- \+ *theorem* set.Inter_Inter_eq_right
- \+ *theorem* set.Inter_and
- \+ *theorem* set.Inter_comm
- \+ *theorem* set.Inter_congr_Prop
- \+ *theorem* set.Inter_exists
- \+ *theorem* set.Inter_false
- \- *lemma* set.Inter_neg
- \+ *theorem* set.Inter_or
- \- *lemma* set.Inter_pos
- \+ *theorem* set.Inter_true
- \+ *lemma* set.Sup_eq_sUnion
- \+/\- *def* set.Union
- \+ *lemma* set.Union_Union_eq'
- \+ *theorem* set.Union_Union_eq_left
- \+ *theorem* set.Union_Union_eq_or_left
- \+ *theorem* set.Union_Union_eq_right
- \+ *theorem* set.Union_and
- \+ *theorem* set.Union_comm
- \+ *theorem* set.Union_congr_Prop
- \+ *theorem* set.Union_exists
- \+ *theorem* set.Union_false
- \- *lemma* set.Union_neg
- \+/\- *lemma* set.Union_of_singleton
- \+ *theorem* set.Union_or
- \- *lemma* set.Union_pos
- \+ *theorem* set.Union_true
- \+ *theorem* set.bInter_and'
- \+ *theorem* set.bInter_and
- \+/\- *lemma* set.bInter_image
- \+/\- *theorem* set.bInter_insert
- \+/\- *lemma* set.bInter_range
- \+/\- *theorem* set.bInter_singleton
- \+ *theorem* set.bUnion_and'
- \+ *theorem* set.bUnion_and
- \+/\- *lemma* set.bUnion_image
- \+/\- *theorem* set.bUnion_insert
- \+/\- *lemma* set.bUnion_range
- \+/\- *theorem* set.bUnion_singleton
- \+/\- *theorem* set.compl_Inter
- \+/\- *theorem* set.compl_Union
- \+ *lemma* set.infi_eq_Inter
- \+/\- *def* set.sInter
- \+ *lemma* set.supr_eq_Union

Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/content.lean


Modified src/measure_theory/measure_space.lean


Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.closed_under_univ

Modified src/order/complete_lattice.lean
- \+/\- *theorem* supr_sup_eq

Modified src/order/filter/at_top_bot.lean


Modified src/topology/basic.lean


Modified src/topology/opens.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/separation.lean




## [2021-08-01 17:17:28](https://github.com/leanprover-community/mathlib/commit/f961b28)
chore(deprecated/*): Make deprecated classes into structures ([#8178](https://github.com/leanprover-community/mathlib/pull/8178))
I make the deprecated classes `is_group_hom`, `is_subgroup`, ... into structures, and delete some deprecated constructions which become inconvenient or essentially unusable after these changes. I do not completely remove all deprecated imports in undeprecated files, however I push these imports much further towards the edges of the hierarchy. 
More detailed comments about what is going on here:
In the `src/deprecated/` directory, classes such as `is_ring_hom` and `is_subring` are defined (and the same for groups, fields, monoids...). These are predicate classes on functions and sets respectively, formerly used to handle ring morphisms and subrings before both were bundled. Amongst other things, this PR changes all the relevant definitions from classes to structures and then picks up the pieces (I will say more about what this means later). Before I started on this refactor, my opinion was that these classes should be turned into structures, but should be left in mathlib. After this refactor, I am now moving towards the opinion that it would be no great loss if these structures were removed completely -- I do not see any time when we really need them.
The situation I previously had in mind where the substructures could be useful is if one is (in the middle of a long tactic proof) defining an explicit subring of a ring by first defining it as a subset, or `add_subgroup` or whatever, and then doing some mathematics to prove that this subset is closed under multiplication, and hence proving that it was a subring after all. With the old approach this just involves some `S : set R` with more and more properties being proved of it and added to the type class search as the proof progresses. With the bundled set-up, we might have `S : set R` and then later on we get `S_subring : subring R` whose underlying subset equals S, and then all our hypotheses about `S` built up during the proof can no longer be used as rewrites, we need to keep rewriting or `change`ing `x \in S_subring` to `x \in S` and back again. This issue showed up only once in the refactor, in `src/ring_theory/integral_closure.lean`, around line 230, where I refactored a proof to avoid the deprecated structures and it seemed to get a bit longer. I can definitely live with this.
One could imagine a similar situation with morphisms (define f as a map between rings, and only later on prove that it's a ring homomorphism) but actually I did not see this situation arise at all. In fact the main issue I ran into with morphism classes was the following (which showed up 10 or so times): there are many constructions in mathlib which actually turn out to be, or (even worse) turn out under some extra assumptions to be, maps which preserve some structure. For example `multiset.map (f : X -> Y) : multiset X -> multiset Y` (which was in mathlib since it was born IIRC) turns out to be an add_group_hom, once the add_group structure is defined on multisets. So here I had a big choice to make: should I actually rename `multiset.map` to be `private multiset.map_aux` and then redefine `multiset.map` to be the `add_monoid_hom`? In retrospect I think that there's a case for this. In fact `data.multiset.basic` is the biggest source of these issues -- `map` and `sum` and `countp` and `count` are all `add_monoid_hom`s. I did not feel confident about ripping out these fundamental definitions so I made four new ones, `map_add_monoid_hom`, `sum_add_monoid_hom` etc. The disadvantage with this approach is that again rewrites get a bit more painful: some lemma which involves `map` may need to be rewritten so that it involves `map_add_monoid_hom` so that one can apply `add_monoid_hom.map_add`, and then perhaps rewritten back so that one can apply other rewrites. Random example: line 43 of `linear_algebra.lagrange`, where I have to rewrite `coe_eval_ring_hom` in both directions. Let me say that I am most definitely open to the idea of renaming `multiset.map_add_monoid_hom` to `multiset.map` and just nuking our current `multiset.map` or making it private or `map_aux` or whatever but we're already at 92 files changed so it might be best to get this over with and come up with a TODO list for future tidy-ups. Another example: should the fields of `complex` be `re'` and `im'`, and `complex.re` be redefined as the R-linear map? Right now in mathlib we only use the fact that it's an `add_group_hom`, and I define `re_add_group_hom` for this. Note however one can not always get away with this renaming trick, for example there are instances when a certain fundamental construction only preserves some structure under additional conditions -- for example `has_inv.inv` on groups is only a group homomorphism when the underlying group is abelian (and the same for `pow` and `gpow`). In the past this was dealt with by a typeclass `is_group_hom` on `inv` which fired in the presence of a `comm_group` but not otherwise; now this has to be dealt with by a second definition `inv_monoid_hom` whose underlying function is `inv`. You can't just get away with applying the proof of `inv (a * b) = inv a * inv b` when you need it, because sometimes you want to apply things like `monoid_hom.map_prod` which needs a `monoid_hom` as input, so won't work with `inv`: you need to rewrite one way, apply `monoid_hom.map_prod` and then rewrite back the other way now :-/ I would say that this was ultimately the main disadvantage of this approach, but it seems minor really and only shows up a few times, and if we go ahead with the renaming plan it will happen even fewer times.
I had initially played with the idea of just completely removing all deprecated imports in non-deprecated files, but there were times near the end when I just didn't feel like it (I just wanted it to be over, I was scared to mess around in `control` or `test`), so I removed most of them but added some deprecated imports higher up the tree (or lower down the tree, I never understand which way up this tree is, I mean nearer the leaves -- am I right in that computer scientists for some reason think the root of a tree is at the top?). It will not be too hard for an expert to remove those last few deprecated imports in src outside the `deprecated` directory in subsequent PR's, indeed I could do it myself but I might I might need some Zulip help. Note: it used to be the case that `subring` imported `deprecated.subring`; this is now the other way around, which is much more sensible (and matches with submonoid). Outside the deprecated directory, there are only a few deprecated imports: `control.fold` (which I don't really want to mess with),`group_theory.free_abelian_group` (there is a bunch of `seq` stuff which I am not sure is ever used but I just couldn't be bothered, it might be the sort of refactor which someone finds interesting or fun though), `ring_theory.free_comm_ring` (this file involves some definitional abuse which either needs to be redone "mathematically" or rewritten to work with bundled morphisms) and `topology.algebra.uniform_group` (which I think Patrick is refactoring?) and a test file.
If you look at the diffs you see that various things are deleted (lots of `is_add_monoid_hom foo` proofs), but many of these deletions come with corresponding additions (e.g. a new `foo_group_hom` definition if it was not there already, plus corresponding `simp` lemma, which is randomly either a `coe` or an `apply` depending on what mood I was in; this could all be done with `@[simps]` trickery apparently but I didn't read the thread carefully yet). Once nice achievement was that I refactored a bunch of basic ring and field theory to avoid the `is_` classes completely, which I think is a step in the right direction (people were occasionally being forced to use deprecated stuff when doing stuff like Galois theory because some fundamental things used to use them; this is no longer the case -- in particular I think Abel-Ruffini might now be deprecated-free, or very nearly so). 
`finset.sum_hom` and `finset.prod_hom` are gone. It is very funny to do a search for these files in mathlib current master as I write -- 98% of the time they're used, they're used backwards (with `.symm` or `\l` with a rewrite). The bundled versions (`monoid_hom.map_prod` etc) are written the other way around. I could have just left them and not bothered, but it seemed easier just to get rid of them if we're moving to bundled morphisms. One funny observation was that unary `-` seemed to be a special case: we
seem to prefer `-\sum i, f i` to `\sum i, -(f i)` . For almost every other function, we want it to go the other way.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/algebra/basic.lean
- \- *lemma* algebra.is_subring_algebra_map_apply
- \- *lemma* algebra.is_subring_coe_algebra_map
- \- *lemma* algebra.is_subring_coe_algebra_map_hom
- \- *def* algebra.of_is_subring
- \- *lemma* algebra.set_range_subset

Modified src/algebra/algebra/subalgebra.lean
- \- *lemma* mem_subalgebra_of_is_subring
- \+ *def* subalgebra.to_add_submonoid
- \+ *def* subalgebra.to_submonoid
- \- *def* subalgebra_of_is_subring

Modified src/algebra/algebra/tower.lean


Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.gsmul_sum
- \- *lemma* finset.prod_hom

Modified src/algebra/big_operators/finsupp.lean


Modified src/algebra/big_operators/ring.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/group/hom.lean
- \+ *def* comm_group.inv_monoid_hom

Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_power/basic.lean
- \+ *def* gpow_group_hom
- \- *theorem* is_monoid_hom.map_pow
- \+ *def* pow_monoid_hom

Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_ring_action.lean
- \+ *def* mul_semiring_action.to_ring_hom
- \- *def* mul_semiring_action.to_semiring_hom
- \+ *theorem* to_ring_hom_injective
- \- *theorem* to_semiring_hom_injective

Modified src/algebra/module/linear_map.lean


Modified src/algebra/pointwise.lean
- \- *lemma* set.singleton.is_mul_hom
- \+ *def* set.singleton_mul_hom

Modified src/algebra/polynomial/group_ring_action.lean


Modified src/algebra/ring/basic.lean
- \+ *theorem* ring_hom.injective_iff'

Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/analysis/normed_space/pi_Lp.lean


Modified src/control/fold.lean
- \+ *lemma* traversable.fold_foldl
- \+ *lemma* traversable.fold_foldr
- \+ *lemma* traversable.fold_mfoldl
- \+ *lemma* traversable.fold_mfoldr
- \+ *lemma* traversable.free.map.is_monoid_hom
- \+/\- *def* traversable.map_fold

Modified src/data/complex/basic.lean
- \+ *lemma* complex.coe_im_add_group_hom
- \+ *lemma* complex.coe_re_add_group_hom
- \+ *def* complex.im_add_group_hom
- \+ *def* complex.re_add_group_hom

Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean
- \+ *def* dfinsupp.mk_add_group_hom
- \+ *def* dfinsupp.subtype_domain_add_monoid_hom
- \+/\- *lemma* dfinsupp.zip_with_def

Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.subtype_domain_add_monoid_hom

Modified src/data/matrix/basic.lean
- \+ *def* matrix.add_monoid_hom_mul_left
- \+ *def* matrix.add_monoid_hom_mul_right
- \- *lemma* matrix.is_add_monoid_hom_mul_left
- \- *lemma* matrix.is_add_monoid_hom_mul_right
- \+ *def* matrix.mul_vec.add_monoid_hom_left

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.coe_count_add_monoid_hom
- \+ *lemma* multiset.coe_countp_add_monoid_hom
- \+ *lemma* multiset.coe_inv_monoid_hom
- \+ *lemma* multiset.coe_map_add_monoid_hom
- \+ *lemma* multiset.coe_sum_add_monoid_hom
- \+ *def* multiset.count_add_monoid_hom
- \+ *def* multiset.countp_add_monoid_hom
- \+ *def* multiset.map_add_monoid_hom
- \+ *def* multiset.sum_add_monoid_hom

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.coe_eval₂_hom
- \+ *def* mv_polynomial.coeff_add_monoid_hom
- \+/\- *def* mv_polynomial.eval₂_hom

Modified src/data/mv_polynomial/comm_ring.lean
- \+/\- *lemma* mv_polynomial.C_neg
- \+/\- *lemma* mv_polynomial.C_sub
- \+/\- *lemma* mv_polynomial.hom_C

Modified src/data/mv_polynomial/equiv.lean


Modified src/data/mv_polynomial/rename.lean


Modified src/data/pnat/basic.lean
- \+ *def* pnat.coe_add_hom
- \+ *lemma* pnat.coe_coe_monoid_hom
- \+ *def* pnat.coe_monoid_hom

Modified src/data/pnat/factors.lean
- \+ *lemma* prime_multiset.coe_coe_nat_monoid_hom
- \+ *lemma* prime_multiset.coe_coe_pnat_monoid_hom
- \+ *def* prime_multiset.coe_nat_monoid_hom
- \+ *def* prime_multiset.coe_pnat_monoid_hom

Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/lemmas.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.coe_eval_ring_hom
- \+ *def* polynomial.comp_ring_hom
- \+ *def* polynomial.eval_ring_hom
- \+ *def* polynomial.eval₂_add_monoid_hom
- \+/\- *def* polynomial.eval₂_ring_hom
- \+/\- *lemma* polynomial.map_pow
- \+/\- *lemma* polynomial.mem_map_range
- \+ *lemma* polynomial.mem_map_srange

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/lifts.lean
- \+/\- *def* polynomial.lifts
- \+ *lemma* polynomial.lifts_iff_ring_hom_srange
- \+/\- *def* polynomial.lifts_ring

Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/ring_division.lean


Modified src/deprecated/group.lean
- \+/\- *lemma* additive.is_add_group_hom
- \+/\- *lemma* additive.is_add_hom
- \+/\- *lemma* additive.is_add_monoid_hom
- \+ *lemma* is_add_monoid_hom.is_add_monoid_hom_mul_left
- \+ *lemma* is_add_monoid_hom.is_add_monoid_hom_mul_right
- \+/\- *lemma* is_group_hom.comp
- \+ *lemma* is_group_hom.id
- \+/\- *lemma* is_group_hom.injective_iff
- \+/\- *lemma* is_group_hom.inv
- \+/\- *theorem* is_group_hom.map_inv
- \+ *lemma* is_group_hom.map_mul
- \+/\- *lemma* is_group_hom.map_one
- \+ *lemma* is_group_hom.to_is_monoid_hom
- \+/\- *lemma* is_monoid_hom.comp
- \+ *lemma* is_monoid_hom.id
- \+ *lemma* is_monoid_hom.inv
- \- *theorem* is_monoid_hom.of_mul
- \+/\- *lemma* is_mul_hom.comp
- \+ *lemma* is_mul_hom.id
- \+/\- *lemma* is_mul_hom.inv
- \+ *theorem* is_mul_hom.to_is_monoid_hom
- \+/\- *lemma* is_unit.map'
- \+/\- *lemma* monoid_hom.coe_of
- \+ *lemma* monoid_hom.is_group_hom
- \+ *lemma* monoid_hom.is_monoid_hom_coe
- \+/\- *def* monoid_hom.of
- \+ *lemma* mul_equiv.is_group_hom
- \+ *lemma* mul_equiv.is_monoid_hom
- \+ *theorem* mul_equiv.is_mul_hom
- \+/\- *lemma* multiplicative.is_group_hom
- \+/\- *lemma* multiplicative.is_mul_hom
- \+ *lemma* ring_hom.to_is_add_group_hom
- \+ *lemma* ring_hom.to_is_add_monoid_hom
- \+ *lemma* ring_hom.to_is_monoid_hom
- \+ *lemma* units.coe_is_monoid_hom
- \+/\- *lemma* units.coe_map'
- \+/\- *def* units.map'

Modified src/deprecated/ring.lean
- \+/\- *lemma* is_ring_hom.comp
- \+ *lemma* is_ring_hom.id
- \+/\- *lemma* is_ring_hom.map_neg
- \+/\- *lemma* is_ring_hom.map_sub
- \+/\- *lemma* is_ring_hom.map_zero
- \+/\- *lemma* is_ring_hom.of_semiring
- \+ *lemma* is_ring_hom.to_is_add_group_hom
- \+ *lemma* is_ring_hom.to_is_semiring_hom
- \+/\- *lemma* is_semiring_hom.comp
- \+ *lemma* is_semiring_hom.id
- \+ *lemma* is_semiring_hom.to_is_add_monoid_hom
- \+ *lemma* is_semiring_hom.to_is_monoid_hom
- \+/\- *lemma* ring_hom.coe_of
- \+/\- *def* ring_hom.of
- \+ *lemma* ring_hom.to_is_ring_hom
- \+ *lemma* ring_hom.to_is_semiring_hom

Modified src/deprecated/subfield.lean
- \+ *lemma* field.closure.is_subfield
- \+ *lemma* field.closure.is_submonoid
- \+/\- *theorem* field.closure_subset
- \+/\- *theorem* field.closure_subset_iff
- \+ *lemma* image.is_subfield
- \+ *lemma* is_subfield.Inter
- \+/\- *lemma* is_subfield.div_mem
- \+ *lemma* is_subfield.inter
- \+/\- *lemma* is_subfield.pow_mem
- \+ *lemma* preimage.is_subfield
- \+ *lemma* range.is_subfield
- \+ *lemma* univ.is_subfield

Modified src/deprecated/subgroup.lean
- \+ *lemma* additive.is_normal_add_subgroup
- \+ *theorem* additive.is_normal_add_subgroup_iff
- \- *lemma* additive.normal_add_subgroup
- \- *theorem* additive.normal_add_subgroup_iff
- \+ *lemma* group.closure.is_subgroup
- \+/\- *lemma* group.closure_subgroup
- \+/\- *theorem* group.closure_subset
- \+/\- *lemma* group.closure_subset_iff
- \+/\- *theorem* group.conjugates_of_set_subset'
- \+/\- *lemma* group.conjugates_of_subset
- \+/\- *lemma* group.image_closure
- \+ *lemma* group.normal_closure.is_normal
- \+ *lemma* group.normal_closure.is_subgroup
- \+/\- *theorem* group.normal_closure_subset
- \+/\- *lemma* group.normal_closure_subset_iff
- \- *lemma* is_add_subgroup.gsmul_coe
- \+ *lemma* is_group_hom.image_subgroup
- \+/\- *lemma* is_group_hom.injective_iff_trivial_ker
- \+/\- *lemma* is_group_hom.injective_of_trivial_ker
- \+/\- *lemma* is_group_hom.inv_iff_ker'
- \+/\- *lemma* is_group_hom.inv_iff_ker
- \+/\- *lemma* is_group_hom.inv_ker_one'
- \+/\- *lemma* is_group_hom.inv_ker_one
- \+ *lemma* is_group_hom.is_normal_subgroup_ker
- \+/\- *lemma* is_group_hom.one_iff_ker_inv'
- \+/\- *lemma* is_group_hom.one_iff_ker_inv
- \+/\- *lemma* is_group_hom.one_ker_inv'
- \+/\- *lemma* is_group_hom.one_ker_inv
- \+ *lemma* is_group_hom.preimage
- \+ *lemma* is_group_hom.preimage_normal
- \+ *lemma* is_group_hom.range_subgroup
- \+/\- *lemma* is_group_hom.trivial_ker_iff_eq_one
- \+/\- *lemma* is_group_hom.trivial_ker_of_injective
- \+ *lemma* is_normal_subgroup_of_comm_group
- \+ *lemma* is_subgroup.Inter
- \+ *lemma* is_subgroup.center_normal
- \- *lemma* is_subgroup.coe_gpow
- \- *lemma* is_subgroup.coe_inv
- \+/\- *lemma* is_subgroup.div_mem
- \+/\- *lemma* is_subgroup.eq_trivial_iff
- \+ *lemma* is_subgroup.inter
- \+/\- *lemma* is_subgroup.mem_norm_comm
- \+/\- *lemma* is_subgroup.mem_norm_comm_iff
- \+ *lemma* is_subgroup.normalizer_is_subgroup
- \+/\- *lemma* is_subgroup.subset_normalizer
- \+ *lemma* is_subgroup.trivial_normal
- \+ *lemma* is_subgroup.univ_subgroup
- \- *def* monoid_hom.range_factorization
- \- *def* monoid_hom.range_subtype_val
- \+ *lemma* multiplicative.is_normal_subgroup
- \+ *theorem* multiplicative.is_normal_subgroup_iff
- \- *lemma* multiplicative.normal_subgroup
- \- *theorem* multiplicative.normal_subgroup_iff
- \- *lemma* normal_subgroup_of_comm_group
- \+ *lemma* subgroup.is_subgroup
- \+/\- *def* subgroup.of
- \+ *lemma* subgroup.of_normal
- \- *def* subtype.comm_group
- \- *def* subtype.group

Modified src/deprecated/submonoid.lean
- \- *lemma* image.is_submonoid
- \+/\- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* is_add_submonoid.smul_mem
- \+ *lemma* is_submonoid.Inter
- \- *lemma* is_submonoid.coe_mul
- \- *lemma* is_submonoid.coe_one
- \- *lemma* is_submonoid.coe_pow
- \+/\- *lemma* is_submonoid.finset_prod_mem
- \+ *lemma* is_submonoid.image
- \+ *lemma* is_submonoid.inter
- \+/\- *lemma* is_submonoid.list_prod_mem
- \+/\- *lemma* is_submonoid.multiset_prod_mem
- \+/\- *lemma* is_submonoid.pow_mem
- \+/\- *lemma* is_submonoid.power_subset
- \+ *lemma* is_submonoid.preimage
- \+ *lemma* monoid.closure.is_submonoid
- \+/\- *theorem* monoid.closure_subset
- \+/\- *lemma* monoid.image_closure
- \+ *lemma* powers.is_submonoid
- \+ *lemma* range.is_submonoid
- \+ *lemma* submonoid.is_submonoid
- \+/\- *def* submonoid.of
- \- *def* subtype.comm_monoid
- \- *def* subtype.monoid
- \+ *lemma* univ.is_submonoid

Modified src/deprecated/subring.lean
- \+ *lemma* is_subring.Inter
- \- *lemma* is_subring.coe_subtype
- \+ *lemma* is_subring.inter
- \+ *def* is_subring.subring
- \- *def* is_subring.subtype
- \+ *lemma* ring.closure.is_subring
- \+/\- *theorem* ring.closure_subset
- \+/\- *theorem* ring.closure_subset_iff
- \- *def* ring_hom.cod_restrict
- \+ *lemma* ring_hom.is_subring_image
- \+ *lemma* ring_hom.is_subring_preimage
- \+ *lemma* ring_hom.is_subring_set_range
- \- *def* subring.domain
- \- *def* subset.comm_ring
- \- *def* subset.ring
- \- *def* subtype.comm_ring
- \- *def* subtype.ring

Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/fixed.lean
- \+ *def* fixed_by.subfield
- \+/\- *lemma* fixed_points.dim_le_card
- \+/\- *lemma* fixed_points.finrank_le_card
- \+/\- *theorem* fixed_points.is_integral
- \+ *theorem* fixed_points.minpoly.eval₂'
- \+/\- *theorem* fixed_points.minpoly.eval₂
- \+/\- *theorem* fixed_points.minpoly.irreducible_aux
- \+/\- *theorem* fixed_points.minpoly.of_eval₂
- \+/\- *def* fixed_points.minpoly
- \+/\- *theorem* fixed_points.smul
- \+/\- *theorem* fixed_points.smul_polynomial
- \+ *def* fixed_points.subfield

Modified src/field_theory/galois.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.to_subring.subtype_eq_subtype

Modified src/group_theory/complement.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.is_add_group_hom_lift'
- \+ *lemma* free_abelian_group.is_add_group_hom_seq
- \+ *def* free_abelian_group.lift_add_group_hom

Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.automorphism_group.to_linear_map_monoid_hom
- \+ *def* linear_map.eval_add_monoid_hom
- \+ *def* linear_map.to_add_monoid_hom'

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.coe_det_monoid_hom
- \+ *def* matrix.det_monoid_hom

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *def* sesq_form.add_monoid_hom_right
- \- *lemma* sesq_form.is_add_monoid_hom_left
- \- *lemma* sesq_form.is_add_monoid_hom_right
- \+ *def* sesq_form.linear_map_left

Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/order/filter/pointwise.lean
- \+/\- *lemma* filter.comap_mul_comap_le
- \- *lemma* filter.map.is_monoid_hom
- \+ *def* filter.map_monoid_hom
- \+/\- *lemma* filter.tendsto.mul_mul

Modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* algebra.adjoin_int
- \- *theorem* is_noetherian_ring_closure
- \+ *theorem* is_noetherian_subring_closure

Modified src/ring_theory/adjoin_root.lean
- \+/\- *def* adjoin_root.of

Modified src/ring_theory/derivation.lean
- \+/\- *lemma* derivation.map_add
- \+/\- *lemma* derivation.map_zero

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/free_comm_ring.lean
- \+ *def* free_ring.coe_ring_hom
- \+/\- *def* free_ring.of'

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ring_hom.ker_eq

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *theorem* is_integral_of_subring

Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* polynomial.map_to_subring
- \+/\- *def* polynomial.restriction
- \+/\- *def* polynomial.to_subring

Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/subring.lean
- \- *def* set.to_subring

Modified src/topology/algebra/group.lean
- \- *lemma* nhds_is_mul_hom
- \+ *def* nhds_mul_hom

Modified src/topology/algebra/group_completion.lean
- \+ *lemma* uniform_space.completion.is_add_group_hom_coe

Modified src/topology/algebra/nonarchimedean/basic.lean


Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* add_comm_group.is_Z_bilin.comp_hom

Modified src/topology/algebra/uniform_ring.lean




## [2021-08-01 11:40:51](https://github.com/leanprover-community/mathlib/commit/9ed4380)
feat(measure_theory/vector_measure): define the pullback and restriction of a vector measure ([#8408](https://github.com/leanprover-community/mathlib/pull/8408))
#### Estimated changes
Modified src/measure_theory/vector_measure.lean
- \+ *def* measure_theory.vector_measure.map
- \+ *lemma* measure_theory.vector_measure.map_add
- \+ *lemma* measure_theory.vector_measure.map_apply
- \+ *def* measure_theory.vector_measure.map_gm
- \+ *lemma* measure_theory.vector_measure.map_id
- \+ *lemma* measure_theory.vector_measure.map_smul
- \+ *lemma* measure_theory.vector_measure.map_zero
- \+ *def* measure_theory.vector_measure.mapₗ
- \+ *def* measure_theory.vector_measure.restrict
- \+ *lemma* measure_theory.vector_measure.restrict_add
- \+ *lemma* measure_theory.vector_measure.restrict_apply
- \+ *lemma* measure_theory.vector_measure.restrict_empty
- \+ *lemma* measure_theory.vector_measure.restrict_eq_self
- \+ *def* measure_theory.vector_measure.restrict_gm
- \+ *lemma* measure_theory.vector_measure.restrict_smul
- \+ *lemma* measure_theory.vector_measure.restrict_univ
- \+ *lemma* measure_theory.vector_measure.restrict_zero
- \+ *def* measure_theory.vector_measure.restrictₗ



## [2021-08-01 09:36:34](https://github.com/leanprover-community/mathlib/commit/5b9b455)
chore(order/complete_lattice): generalize `Sup_eq_supr'`, add lemmas ([#8484](https://github.com/leanprover-community/mathlib/pull/8484))
* `Sup_eq_supr'` only needs `[has_Sup α]`, add `Inf_eq_infi'`;
* add `supr_range'`, `infi_range'`, `Sup_image'`, `Inf_image'`
  lemmas that use supremum/infimum over subtypes and only require
  `[has_Sup]`/`[has_Inf]`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *theorem* Inf_eq_infi'
- \+ *theorem* Inf_image'
- \+/\- *lemma* Sup_eq_supr'
- \+ *theorem* Sup_image'
- \+ *lemma* infi_range'
- \+ *lemma* supr_range'



## [2021-08-01 09:36:33](https://github.com/leanprover-community/mathlib/commit/de78d42)
feat(order/rel_iso): add `equiv.to_order_iso` ([#8482](https://github.com/leanprover-community/mathlib/pull/8482))
Sometimes it's easier to show `monotone e` and `monotone e.symm` than
`e x ≤ e y ↔ x ≤ y`.
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* equiv.coe_to_order_iso
- \+ *def* equiv.to_order_iso
- \+ *lemma* equiv.to_order_iso_to_equiv
- \+ *lemma* order_iso.symm_apply_le



## [2021-08-01 09:36:33](https://github.com/leanprover-community/mathlib/commit/4f2006e)
chore(order/iterate): slightly generalize 2 lemmas ([#8481](https://github.com/leanprover-community/mathlib/pull/8481))
#### Estimated changes
Modified src/order/iterate.lean
- \+ *lemma* monotone.iterate_comp_le_of_le
- \+ *lemma* monotone.le_iterate_comp_of_le



## [2021-08-01 08:34:12](https://github.com/leanprover-community/mathlib/commit/2063a52)
feat(order/partial_sups): complete lattice lemmas ([#8480](https://github.com/leanprover-community/mathlib/pull/8480))
#### Estimated changes
Modified src/order/partial_sups.lean
- \+/\- *lemma* le_partial_sups
- \+ *lemma* le_partial_sups_of_le
- \+ *lemma* monotone.partial_sups_eq
- \+ *def* partial_sups.gi
- \+/\- *def* partial_sups
- \- *lemma* partial_sups_eq
- \+ *lemma* partial_sups_eq_bsupr
- \+ *lemma* partial_sups_eq_sup'_range
- \+ *lemma* partial_sups_eq_sup_range
- \+/\- *lemma* partial_sups_le
- \+ *lemma* partial_sups_mono
- \+/\- *lemma* partial_sups_succ
- \+/\- *lemma* partial_sups_zero
- \+ *lemma* supr_eq_supr_of_partial_sups_eq_partial_sups
- \+ *lemma* supr_le_supr_of_partial_sups_le_partial_sups
- \+ *lemma* supr_partial_sups_eq



## [2021-08-01 03:28:41](https://github.com/leanprover-community/mathlib/commit/79bc732)
feat(order/galois_connection): formula for `upper_bounds (l '' s)` ([#8478](https://github.com/leanprover-community/mathlib/pull/8478))
* upgrade `galois_connection.upper_bounds_l_image_subset` and
  `galois_connection.lower_bounds_u_image` to equalities;
* prove `bdd_above (l '' s) ↔ bdd_above s` and
  `bdd_below (u '' s) ↔ bdd_below s`;
* move `galois_connection.dual` to the top and use it in some proofs;
* use `order_iso.to_galois_connection` to transfer some of these
  results to `order_iso`s;
* rename `rel_iso.to_galois_insertion` to `order_iso.to_galois_insertion`.
#### Estimated changes
Modified src/data/setoid/partition.lean
- \- *def* setoid.partition.rel_iso

Modified src/order/galois_connection.lean
- \+ *lemma* galois_connection.bdd_above_l_image
- \+ *lemma* galois_connection.bdd_below_u_image
- \+ *lemma* galois_connection.lower_bounds_u_image
- \- *lemma* galois_connection.lower_bounds_u_image_subset
- \+ *lemma* galois_connection.upper_bounds_l_image
- \- *lemma* galois_connection.upper_bounds_l_image_subset
- \+ *lemma* order_iso.bdd_above_image
- \+ *lemma* order_iso.bdd_below_image
- \+ *lemma* order_iso.lower_bounds_image
- \+ *lemma* order_iso.upper_bounds_image

