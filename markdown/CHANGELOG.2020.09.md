## [2020-09-30 20:29:32](https://github.com/leanprover-community/mathlib/commit/bcc7c02)
feat(geometry/manifold): smooth bundled maps ([#3641](https://github.com/leanprover-community/mathlib/pull/3641))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff.mul
- \+ *lemma* times_cont_diff.smul
- \+/\- *lemma* times_cont_diff_add
- \+ *lemma* times_cont_diff_at.mul
- \+ *lemma* times_cont_diff_at.smul
- \+ *lemma* times_cont_diff_mul
- \+/\- *lemma* times_cont_diff_neg
- \+ *lemma* times_cont_diff_on.mul
- \+ *lemma* times_cont_diff_on.smul
- \+ *lemma* times_cont_diff_smul
- \+ *lemma* times_cont_diff_within_at.mul
- \+ *lemma* times_cont_diff_within_at.smul

Renamed src/geometry/algebra/lie_group.lean to src/geometry/manifold/algebra/lie_group.lean
- \- *lemma* smooth.mul
- \- *lemma* smooth_left_mul
- \- *lemma* smooth_mul
- \- *lemma* smooth_on.mul
- \- *lemma* smooth_right_mul

Added src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* smooth.mul
- \+ *lemma* smooth_mul
- \+ *lemma* smooth_mul_left
- \+ *lemma* smooth_mul_right
- \+ *lemma* smooth_on.mul

Added src/geometry/manifold/algebra/smooth_functions.lean
- \+ *def* smooth_map.C

Added src/geometry/manifold/algebra/structures.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean


Renamed src/geometry/manifold/real_instances.lean to src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \- *lemma* smooth_manifold_with_corners.compatible
- \+ *lemma* smooth_manifold_with_corners_of_times_cont_diff_on

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth.smul
- \+ *lemma* smooth_smul

Modified src/geometry/manifold/times_cont_mdiff_map.lean
- \+/\- *lemma* times_cont_mdiff_map.coe_inj
- \+/\- *def* times_cont_mdiff_map.comp
- \+/\- *lemma* times_cont_mdiff_map.comp_apply
- \+/\- *def* times_cont_mdiff_map.const
- \+/\- *def* times_cont_mdiff_map.id

Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/continuous_map.lean
- \+/\- *def* continuous_map.comp
- \+/\- *def* continuous_map.const

Modified src/topology/instances/real.lean


Modified src/topology/path_connected.lean




## [2020-09-30 19:43:08](https://github.com/leanprover-community/mathlib/commit/c04e339)
feat(archive/imo): formalize IMO 1959 problem 1 ([#4340](https://github.com/leanprover-community/mathlib/pull/4340))
This is a formalization of the problem and solution for the first problem on the 1959 IMO:
Prove that the fraction (21n+4)/(14n+3) is irreducible for every natural number n.
#### Estimated changes
Added archive/imo/imo1959_q1.lean
- \+ *lemma* calculation
- \+ *theorem* imo1959_q1



## [2020-09-30 18:14:45](https://github.com/leanprover-community/mathlib/commit/23b04b0)
chore(ring_theory/algebra): Mark algebra.mem_top as simp ([#4339](https://github.com/leanprover-community/mathlib/pull/4339))
This is consistent with `subsemiring.mem_top` and `submonoid.mem_top`, both of which are marked simp.
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+/\- *theorem* algebra.mem_top



## [2020-09-30 18:14:43](https://github.com/leanprover-community/mathlib/commit/decd67c)
feat(analysis/convex): slope_mono_adjacent ([#4307](https://github.com/leanprover-community/mathlib/pull/4307))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* concave_on.slope_mono_adjacent
- \+ *lemma* concave_on_real_iff_slope_mono_adjacent
- \+ *lemma* convex_on.slope_mono_adjacent
- \+ *lemma* convex_on_real_iff_slope_mono_adjacent



## [2020-09-30 16:47:25](https://github.com/leanprover-community/mathlib/commit/a06c87e)
chore(*): Tidy some proofs and variables ([#4338](https://github.com/leanprover-community/mathlib/pull/4338))
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+/\- *theorem* free_algebra.hom_ext
- \+/\- *def* free_algebra.lift
- \+/\- *theorem* free_algebra.lift_comp_ι
- \+/\- *theorem* free_algebra.lift_unique
- \+/\- *theorem* free_algebra.lift_ι_apply
- \+/\- *theorem* free_algebra.ι_comp_lift

Modified src/data/monoid_algebra.lean




## [2020-09-30 16:47:23](https://github.com/leanprover-community/mathlib/commit/9921fe7)
fix(ring_theory/algebra): Fix typo "algbera" ([#4337](https://github.com/leanprover-community/mathlib/pull/4337))
Introduced in e57fc3d6c142835dc8566aa28e812f7688f14512
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebra.lean
- \- *theorem* algebra.bijective_algbera_map_iff
- \+ *theorem* algebra.bijective_algebra_map_iff
- \- *theorem* algebra.surjective_algbera_map_iff
- \+ *theorem* algebra.surjective_algebra_map_iff



## [2020-09-30 14:42:25](https://github.com/leanprover-community/mathlib/commit/05038da)
feat(ring_theory/algebra): some lemmas about numerals in algebras ([#4327](https://github.com/leanprover-community/mathlib/pull/4327))
#### Estimated changes
Modified src/algebra/group_power/basic.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.bit0_smul_bit0
- \+ *lemma* algebra.bit0_smul_bit1
- \+ *lemma* algebra.bit0_smul_one
- \+ *lemma* algebra.bit1_smul_bit0
- \+ *lemma* algebra.bit1_smul_bit1
- \+ *lemma* algebra.bit1_smul_one



## [2020-09-30 09:51:53](https://github.com/leanprover-community/mathlib/commit/5fd2037)
chore(*): rename is_unit_pow to is_unit.pow ([#4329](https://github.com/leanprover-community/mathlib/pull/4329))
enable dot notation by renaming
is_unit_pow to is_unit.pow
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* is_unit.pow
- \- *lemma* is_unit_pow

Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/rational_root.lean




## [2020-09-30 09:51:51](https://github.com/leanprover-community/mathlib/commit/ac797ad)
feat(topology/bounded_continuous_function): normed_comm_ring structure on bounded continuous functions ([#4326](https://github.com/leanprover-community/mathlib/pull/4326))
An instance of the new ([#4291](https://github.com/leanprover-community/mathlib/pull/4291)) class `normed_comm_ring`.
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean




## [2020-09-30 09:51:49](https://github.com/leanprover-community/mathlib/commit/e53aa87)
feat(order/basic): lemmas about `strict_mono_incr_on` ([#4313](https://github.com/leanprover-community/mathlib/pull/4313))
Also move the section about `order_dual` up to use it in the proofs.
Non-BC API changes:
* Now `strict_mono_incr_on` and `strict_mono_decr_on` take `x` and `y` as `⦃⦄` args.
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/data/set/function.lean
- \+ *lemma* strict_mono_decr_on.inj_on
- \+ *lemma* strict_mono_incr_on.inj_on

Modified src/order/basic.lean
- \+ *lemma* order_dual.dual_compares
- \- *theorem* strict_mono.compares
- \+/\- *lemma* strict_mono.injective
- \+/\- *lemma* strict_mono.le_iff_le
- \+/\- *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_mono_decr_on.le_iff_le
- \+ *lemma* strict_mono_decr_on.lt_iff_lt
- \+ *lemma* strict_mono_incr_on.le_iff_le
- \+ *lemma* strict_mono_incr_on.lt_iff_lt
- \+ *lemma* subtype.coe_le_coe
- \+ *lemma* subtype.coe_lt_coe
- \+ *lemma* subtype.mk_le_mk
- \+ *lemma* subtype.mk_lt_mk

Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.coe_to_order_embedding
- \+ *def* order_iso.to_order_embedding



## [2020-09-30 09:51:46](https://github.com/leanprover-community/mathlib/commit/e1c0b0a)
feat(ring_theory/jacobson): Integral extension of Jacobson rings are Jacobson ([#4304](https://github.com/leanprover-community/mathlib/pull/4304))
Main statement given by `is_jacobson_of_is_integral `
#### Estimated changes
Modified src/ring_theory/ideal/over.lean
- \+ *lemma* ideal.eq_bot_of_comap_eq_bot
- \+ *lemma* ideal.exists_ideal_over_maximal_of_is_integral

Modified src/ring_theory/jacobson.lean
- \+ *lemma* ideal.is_jacobson_of_is_integral

Modified src/ring_theory/jacobson_ideal.lean
- \+ *lemma* ideal.comap_jacobson



## [2020-09-30 09:51:44](https://github.com/leanprover-community/mathlib/commit/ff66d92)
chore(category_theory/limits): facts about opposites of limit cones ([#4250](https://github.com/leanprover-community/mathlib/pull/4250))
Simple facts about limit cones and opposite categories.
#### Estimated changes
Modified src/category_theory/adjunction/opposites.lean


Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.functor.map_cocone_op
- \+ *def* category_theory.functor.map_cone_op
- \+ *def* category_theory.limits.cocone.op
- \+ *def* category_theory.limits.cocone.unop
- \+ *def* category_theory.limits.cocone_equivalence_op_cone_op
- \+ *def* category_theory.limits.cone.op
- \+ *def* category_theory.limits.cone.unop

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.op
- \+ *def* category_theory.limits.is_colimit.unop
- \+ *def* category_theory.limits.is_colimit_equiv_is_limit_op
- \+ *def* category_theory.limits.is_limit.op
- \+ *def* category_theory.limits.is_limit.unop
- \+ *def* category_theory.limits.is_limit_equiv_is_colimit_op

Modified src/category_theory/monad/equiv_mon.lean
- \+ *def* category_theory.Monad.Monad_Mon_equiv.counit_iso
- \+ *def* category_theory.Monad.Monad_Mon_equiv.unit_iso
- \+ *def* category_theory.Monad.Monad_Mon_equiv.unit_iso_hom
- \+ *def* category_theory.Monad.Monad_Mon_equiv.unit_iso_inv
- \- *def* category_theory.Monad.of_to_mon_end_iso
- \- *def* category_theory.Monad.to_of_mon_end_iso

Modified src/category_theory/opposites.lean
- \+ *def* category_theory.equivalence.op
- \+ *def* category_theory.equivalence.unop
- \+ *def* category_theory.functor.op_hom
- \+ *def* category_theory.functor.op_inv
- \+ *lemma* category_theory.nat_iso.remove_op_hom
- \+ *lemma* category_theory.nat_iso.remove_op_inv
- \+/\- *lemma* category_theory.nat_iso.unop_hom
- \+/\- *lemma* category_theory.nat_iso.unop_inv
- \+ *lemma* category_theory.nat_trans.remove_left_op_app
- \+ *lemma* category_theory.nat_trans.remove_op_id
- \- *lemma* category_theory.nat_trans.right_op_app
- \+/\- *lemma* category_theory.nat_trans.unop_id

Modified src/data/opposite.lean




## [2020-09-30 07:56:48](https://github.com/leanprover-community/mathlib/commit/da66bb8)
feat(*): preparations for roots of unity ([#4322](https://github.com/leanprover-community/mathlib/pull/4322))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* is_unit_of_pow_eq_one

Modified src/data/int/gcd.lean
- \+ *lemma* pow_gcd_eq_one

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.card_nth_roots
- \+/\- *lemma* polynomial.mem_nth_roots
- \+/\- *def* polynomial.nth_roots
- \+ *lemma* polynomial.nth_roots_zero

Modified src/group_theory/order_of_element.lean




## [2020-09-29 14:16:59](https://github.com/leanprover-community/mathlib/commit/743f82c)
feat(algebra/pointwise): Add missing to_additive on finset lemmas ([#4306](https://github.com/leanprover-community/mathlib/pull/4306))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* finset.add_card_le



## [2020-09-29 12:11:48](https://github.com/leanprover-community/mathlib/commit/669a349)
feat(data/prod): mk injective lemmas ([#4319](https://github.com/leanprover-community/mathlib/pull/4319))
More scattered lemmmas from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* prod.mk.inj_left
- \+ *lemma* prod.mk.inj_right



## [2020-09-29 12:11:45](https://github.com/leanprover-community/mathlib/commit/d301d43)
feat(algebra/invertible): invertible.copy ([#4318](https://github.com/leanprover-community/mathlib/pull/4318))
A useful gadget from the Witt vector project.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *def* invertible.copy



## [2020-09-29 12:11:43](https://github.com/leanprover-community/mathlib/commit/fa09f49)
feat(analysis/special_functions/*): prove that `exp` etc are measurable ([#4314](https://github.com/leanprover-community/mathlib/pull/4314))
The modifications in `measure_theory/borel_space` are a part of the
proof of measurability of `x^y`, `x : ennreal`, `y : ℝ`, but this
proof depends on a refactoring of `arcsin` I'm going to PR soon.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.measurable_exp
- \+ *lemma* measurable.cexp
- \+ *lemma* measurable.exp
- \+ *lemma* measurable.log
- \+/\- *lemma* real.continuous_log'
- \+ *lemma* real.measurable_exp
- \+ *lemma* real.measurable_log

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.measurable_cos
- \+ *lemma* complex.measurable_cosh
- \+ *lemma* complex.measurable_sin
- \+ *lemma* complex.measurable_sinh
- \+ *lemma* measurable.ccos
- \+ *lemma* measurable.ccosh
- \+ *lemma* measurable.cos
- \+ *lemma* measurable.cosh
- \+ *lemma* measurable.csin
- \+ *lemma* measurable.csinh
- \+ *lemma* measurable.sin
- \+ *lemma* measurable.sinh
- \+ *lemma* real.measurable_cos
- \+ *lemma* real.measurable_cosh
- \+ *lemma* real.measurable_sin
- \+ *lemma* real.measurable_sinh

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ennreal.measurable_mul
- \+ *lemma* ennreal.measurable_of_measurable_nnreal_prod
- \+ *lemma* ennreal.measurable_sub
- \+ *lemma* ennreal.measurable_to_nnreal
- \+ *lemma* ennreal.measurable_to_real
- \+/\- *lemma* measurable.ennreal_mul
- \+/\- *lemma* measurable.ennreal_sub
- \- *lemma* measurable_ennreal_to_real
- \- *lemma* measurable_to_nnreal

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_const



## [2020-09-29 12:11:41](https://github.com/leanprover-community/mathlib/commit/744e067)
feat(linear_algebra/dual): transpose of linear maps ([#4302](https://github.com/leanprover-community/mathlib/pull/4302))
This is filling an easy hole from the undergrad curriculum page: the transpose of a linear map. We don't prove much about it but at least we make contact with matrix transpose.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.arrow_congr_symm_apply

Modified src/linear_algebra/dual.lean
- \+ *lemma* is_basis.dual_basis_apply
- \+ *lemma* is_basis.dual_basis_apply_self
- \+ *lemma* is_basis.dual_basis_equiv_fun
- \+ *lemma* is_basis.dual_basis_repr
- \+ *lemma* is_basis.to_dual_apply_left
- \+ *lemma* is_basis.to_dual_apply_right
- \+ *lemma* is_basis.to_dual_eq_equiv_fun
- \+ *lemma* is_basis.to_dual_total_left
- \+ *lemma* is_basis.to_dual_total_right
- \+ *lemma* is_basis.total_dual_basis
- \+ *def* module.dual.transpose
- \+ *lemma* module.dual.transpose_apply
- \+ *lemma* module.dual.transpose_comp

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_equiv_matrix'_symm_apply
- \+ *lemma* linear_equiv_matrix_symm_apply
- \+ *lemma* linear_equiv_matrix_symm_transpose
- \+ *lemma* linear_equiv_matrix_transpose



## [2020-09-29 10:59:46](https://github.com/leanprover-community/mathlib/commit/a5a7a75)
feat(analysis/normed_space): define `normed_comm_ring` ([#4291](https://github.com/leanprover-community/mathlib/pull/4291))
Also use section `variables`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+/\- *lemma* ring_hom.map_fpow

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* monoid_hom.map_fpow

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* normed_field.continuous_on_inv
- \+/\- *lemma* normed_field.exists_lt_norm
- \+/\- *lemma* normed_field.exists_norm_lt
- \+/\- *lemma* normed_field.exists_norm_lt_one
- \+/\- *lemma* normed_field.exists_one_lt_norm
- \+/\- *lemma* normed_field.nhds_within_is_unit_ne_bot
- \+/\- *lemma* normed_field.nnnorm_inv
- \+/\- *lemma* normed_field.nnnorm_one
- \+/\- *lemma* normed_field.norm_div
- \+/\- *lemma* normed_field.norm_fpow
- \+ *def* normed_field.norm_hom
- \+/\- *lemma* normed_field.norm_inv
- \+/\- *lemma* normed_field.norm_mul
- \+/\- *lemma* normed_field.norm_one
- \+/\- *lemma* normed_field.norm_pow
- \+/\- *lemma* normed_field.norm_prod
- \+/\- *lemma* normed_field.punctured_nhds_ne_bot
- \+/\- *lemma* normed_field.tendsto_inv



## [2020-09-29 09:53:22](https://github.com/leanprover-community/mathlib/commit/9962bfa)
doc(data/monoid_algebra): fix typo ([#4317](https://github.com/leanprover-community/mathlib/pull/4317))
#### Estimated changes
Modified src/data/monoid_algebra.lean




## [2020-09-29 07:37:23](https://github.com/leanprover-community/mathlib/commit/22d034c)
feat(algebra/quandle): racks and quandles ([#4247](https://github.com/leanprover-community/mathlib/pull/4247))
This adds the algebraic structures of racks and quandles, defines a few examples, and provides the universal enveloping group of a rack.
A rack is a set that acts on itself bijectively, and sort of the point is that the action `act : α → (α ≃ α)` satisfies
```
act (x ◃ y) = act x * act y * (act x)⁻¹
```
where `x ◃ y` is the usual rack/quandle notation for `act x y`.  (Note: racks do not use `has_scalar` because it's convenient having `x ◃⁻¹ y` for the inverse action of `x` on `y`.  Plus, associative racks have a trivial action.)
In knot theory, the universal enveloping group of the fundamental quandle is isomorphic to the fundamental group of the knot complement.  For oriented knots up to orientation-reversed mirror image, the fundamental quandle is a complete invariant, unlike the fundamental group, which fails to distinguish non-prime knots with chiral summands.
#### Estimated changes
Modified docs/references.bib


Added src/algebra/quandle.lean
- \+ *def* quandle.conj.map
- \+ *def* quandle.conj
- \+ *lemma* quandle.conj_act_eq_conj
- \+ *lemma* quandle.conj_swap
- \+ *def* quandle.dihedral
- \+ *lemma* quandle.dihedral_act.inv
- \+ *def* quandle.dihedral_act
- \+ *lemma* quandle.fix_inv
- \+ *def* rack.act
- \+ *lemma* rack.act_apply
- \+ *lemma* rack.act_inv_act_eq
- \+ *lemma* rack.act_symm_apply
- \+ *lemma* rack.ad_conj
- \+ *lemma* rack.assoc_iff_id
- \+ *def* rack.envel_action
- \+ *lemma* rack.envel_action_prop
- \+ *def* rack.envel_group
- \+ *lemma* rack.inv_act_act_eq
- \+ *lemma* rack.inv_act_apply
- \+ *lemma* rack.involutory_inv_act_eq_act
- \+ *def* rack.is_abelian
- \+ *def* rack.is_involutory
- \+ *lemma* rack.left_cancel
- \+ *lemma* rack.left_cancel_inv
- \+ *lemma* rack.op_act_op_eq
- \+ *lemma* rack.op_inv_act_op_eq
- \+ *lemma* rack.pre_envel_group_rel'.rel
- \+ *lemma* rack.pre_envel_group_rel.refl
- \+ *lemma* rack.pre_envel_group_rel.symm
- \+ *lemma* rack.pre_envel_group_rel.trans
- \+ *lemma* rack.self_act_act_eq
- \+ *lemma* rack.self_act_eq_iff_eq
- \+ *lemma* rack.self_act_inv_act_eq
- \+ *def* rack.self_apply_equiv
- \+ *lemma* rack.self_distrib
- \+ *lemma* rack.self_distrib_inv
- \+ *lemma* rack.self_inv_act_act_eq
- \+ *lemma* rack.self_inv_act_eq_iff_eq
- \+ *lemma* rack.self_inv_act_inv_act_eq
- \+ *def* rack.to_conj
- \+ *def* rack.to_envel_group.map
- \+ *lemma* rack.to_envel_group.map_aux.well_def
- \+ *def* rack.to_envel_group.map_aux
- \+ *lemma* rack.to_envel_group.univ
- \+ *lemma* rack.to_envel_group.univ_uniq
- \+ *def* rack.to_envel_group
- \+ *def* shelf_hom.comp
- \+ *lemma* shelf_hom.comp_apply
- \+ *def* shelf_hom.id
- \+ *lemma* shelf_hom.map_act
- \+ *lemma* shelf_hom.to_fun_eq_coe

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_aut.conj_inv_apply
- \+ *lemma* mul_equiv.to_equiv_apply



## [2020-09-29 04:58:27](https://github.com/leanprover-community/mathlib/commit/0bb5e5d)
feat(ring_theory/algebra_tower): Artin--Tate lemma ([#4282](https://github.com/leanprover-community/mathlib/pull/4282))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.map_span

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* mem_span_finset

Modified src/ring_theory/adjoin.lean
- \+ *lemma* algebra.adjoin_image
- \+ *lemma* subalgebra.fg_adjoin_finset
- \+ *lemma* subalgebra.fg_map
- \+ *lemma* subalgebra.fg_of_fg_map
- \+ *lemma* subalgebra.fg_of_submodule_fg
- \+ *lemma* subalgebra.fg_top

Modified src/ring_theory/algebra.lean
- \+ *lemma* subalgebra.coe_val
- \+ *lemma* subalgebra.map_injective
- \+ *lemma* subalgebra.map_mono
- \+ *lemma* subalgebra.range_val

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* algebra.fg_trans'
- \+ *lemma* exists_subalgebra_of_fg
- \+ *theorem* fg_of_fg_of_fg
- \+/\- *theorem* is_scalar_tower.aeval_apply
- \+/\- *theorem* is_scalar_tower.of_algebra_map_eq

Modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_of_injective
- \+ *lemma* is_noetherian_of_fg_of_noetherian'
- \+ *lemma* is_noetherian_of_injective
- \+ *lemma* submodule.fg_of_fg_map
- \+/\- *theorem* submodule.fg_of_fg_map_of_fg_inf_ker
- \+ *lemma* submodule.fg_of_linear_equiv
- \+ *lemma* submodule.fg_top



## [2020-09-29 03:32:06](https://github.com/leanprover-community/mathlib/commit/88187ba)
chore(topology/algebra/ordered): golf a proof ([#4311](https://github.com/leanprover-community/mathlib/pull/4311))
* generalize `continuous_within_at_Ioi_iff_Ici` from `linear_order α`
  to `partial_order α`;
* base the proof on a more general fact:
  `continuous_within_at f (s \ {x}) x ↔ continuous_within_at f s x`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* continuous_within_at_Ioi_iff_Ici

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.diff_iff
- \+ *lemma* continuous_within_at_diff_self
- \+ *lemma* continuous_within_at_singleton



## [2020-09-28 17:22:18](https://github.com/leanprover-community/mathlib/commit/89d8cc3)
refactor(data/nat/basic): review API of `nat.find_greatest` ([#4274](https://github.com/leanprover-community/mathlib/pull/4274))
Other changes:
* add `nat.find_eq_iff`;
* use weaker assumptions in `measurable_to_encodable` and `measurable_to_nat`;
* add `measurable_find`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.find_eq_iff
- \+ *lemma* nat.find_greatest_eq_iff
- \- *lemma* nat.find_greatest_eq_zero
- \+ *lemma* nat.find_greatest_eq_zero_iff
- \+/\- *lemma* nat.find_greatest_is_greatest
- \+/\- *lemma* nat.find_greatest_le
- \+/\- *lemma* nat.find_greatest_of_ne_zero
- \+/\- *lemma* nat.find_greatest_spec
- \- *lemma* nat.find_greatest_spec_and_le

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_find
- \+ *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest



## [2020-09-28 15:25:45](https://github.com/leanprover-community/mathlib/commit/50dbce9)
fix(data/list/basic): Ensure that ball_cons actually works as a simp lemma ([#4281](https://github.com/leanprover-community/mathlib/pull/4281))
The LHS of the simp lemma `list.ball_cons` (aka `list.forall_mem_cons`) is not in simp-normal form, as `list.mem_cons_iff` rewrites it.
This adds a new simp lemma which is the form that `list.mem_cons_iff` rewrites it to.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *theorem* list.forall_mem_cons'

Modified src/data/list/chain.lean


Modified src/logic/basic.lean
- \+ *theorem* forall_eq_or_imp

Modified src/set_theory/ordinal_arithmetic.lean




## [2020-09-28 15:25:43](https://github.com/leanprover-community/mathlib/commit/40fb701)
feat(data/mv_polynomial): some lemmas on constant_coeff and rename ([#4231](https://github.com/leanprover-community/mathlib/pull/4231))
Snippet from the Witt project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.constant_coeff_comp_C
- \+ *lemma* mv_polynomial.constant_coeff_comp_algebra_map

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* mv_polynomial.constant_coeff_rename



## [2020-09-28 14:08:44](https://github.com/leanprover-community/mathlib/commit/8461a7d)
feat(geometry/euclidean/monge_point): lemmas on altitudes and orthocenter ([#4179](https://github.com/leanprover-community/mathlib/pull/4179))
Add more lemmas about altitudes of a simplex and the orthocenter of a
triangle.  Some of these are just building out basic API that's
mathematically trivial (e.g. showing that the altitude as defined is a
one-dimensional affine subspace and providing an explicit form of its
direction), while the results on the orthocenter have some geometrical
content that's part of the preparation for defining and proving basic
properties of orthocentric systems.
#### Estimated changes
Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* affine.simplex.affine_span_insert_singleton_eq_altitude_iff
- \+ *lemma* affine.simplex.direction_altitude
- \+ *lemma* affine.simplex.findim_direction_altitude
- \+ *lemma* affine.simplex.mem_altitude
- \+ *lemma* affine.simplex.vector_span_le_altitude_direction_orthogonal
- \+ *lemma* affine.triangle.affine_span_orthocenter_point_le_altitude
- \+ *lemma* affine.triangle.altitude_replace_orthocenter_eq_affine_span
- \+ *lemma* affine.triangle.orthocenter_replace_orthocenter_eq_point



## [2020-09-28 11:21:24](https://github.com/leanprover-community/mathlib/commit/7bbb759)
chore(algebra/free_algebra): Make the second type argument to lift and ι implicit ([#4299](https://github.com/leanprover-community/mathlib/pull/4299))
These can always be inferred by the context, and just make things longer.
This is consistent with how the type argument for `id` is implicit.
The changes are applied to downstream uses too.
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+/\- *lemma* free_algebra.quot_mk_eq_ι

Modified src/algebra/lie/universal_enveloping.lean
- \+/\- *lemma* universal_enveloping_algebra.lift_ι_apply
- \+/\- *lemma* universal_enveloping_algebra.ι_comp_lift

Modified src/linear_algebra/tensor_algebra.lean




## [2020-09-28 11:21:22](https://github.com/leanprover-community/mathlib/commit/ad680c2)
chore(algebra/ordered_ring): remove duplicate lemma ([#4295](https://github.com/leanprover-community/mathlib/pull/4295))
`ordered_ring.two_pos` and `ordered_ring.zero_lt_two` had ended up identical. I kept `zero_lt_two`.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean


Modified src/algebra/ordered_field.lean
- \+/\- *lemma* half_pos

Modified src/algebra/ordered_ring.lean
- \- *lemma* four_pos
- \- *lemma* two_pos
- \+ *lemma* zero_lt_four
- \+/\- *lemma* zero_lt_two

Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* real.norm_two

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.two_ne_zero
- \- *lemma* ennreal.two_pos
- \+ *lemma* ennreal.zero_lt_two

Modified src/data/real/hyperreal.lean


Modified src/data/real/pi.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/uniform_space/absolute_value.lean




## [2020-09-28 05:25:33](https://github.com/leanprover-community/mathlib/commit/3986e97)
chore(algebra/lie): group Lie algebra files together in their own directory ([#4288](https://github.com/leanprover-community/mathlib/pull/4288))
#### Estimated changes
Renamed src/algebra/lie_algebra.lean to src/algebra/lie/basic.lean
- \+/\- *def* lie_ideal_subalgebra
- \+/\- *def* lie_module.of_endo_morphism

Renamed src/algebra/classical_lie_algebras.lean to src/algebra/lie/classical.lean


Renamed src/algebra/universal_enveloping_algebra.lean to src/algebra/lie/universal_enveloping.lean


Modified src/ring_theory/derivation.lean


Modified test/transport/basic.lean




## [2020-09-28 05:25:30](https://github.com/leanprover-community/mathlib/commit/d77ac51)
chore(data/fintype/card): review API ([#4287](https://github.com/leanprover-community/mathlib/pull/4287))
API changes:
* `finset.filter_mem_eq_inter` now takes `[Π i, decidable (i ∈ t)]`; this way it works better
  with `classical`;
* add `finset.mem_compl` and `finset.coe_compl`;
* [DRY] drop `finset.prod_range_eq_prod_fin` and `finset.sum_range_eq_sum_fin`:
  use `fin.prod_univ_eq_prod_range` and `fin.sum_univ_eq_sum_range` instead;
* rename `finset.prod_equiv` to `equiv.prod_comp` to enable dot notation;
* add `fintype.prod_dite`: a specialized version of `finset.prod_dite`.
Also golf a proof in `analysis/normed_space/multilinear`
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.filter_mem_eq_inter

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.coe_compl
- \+ *lemma* finset.mem_compl

Modified src/data/fintype/card.lean
- \+ *lemma* equiv.prod_comp
- \- *lemma* finset.prod_equiv
- \- *lemma* finset.prod_range_eq_prod_fin
- \+ *lemma* fintype.prod_dite

Modified src/field_theory/chevalley_warning.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2020-09-28 05:25:28](https://github.com/leanprover-community/mathlib/commit/66c87c0)
feat(data/*/gcd): adds gcd, lcm of finsets and multisets ([#4217](https://github.com/leanprover-community/mathlib/pull/4217))
Defines `finset.gcd`, `finset.lcm`, `multiset.gcd`, `multiset.lcm`
Proves some basic facts about those, analogous to those in `data.multiset.lattice` and `data.finset.lattice`
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *theorem* gcd_eq_of_associated_left
- \+ *theorem* gcd_eq_of_associated_right
- \+ *theorem* lcm_eq_of_associated_left
- \+ *theorem* lcm_eq_of_associated_right

Added src/data/finset/gcd.lean
- \+ *lemma* finset.dvd_gcd
- \+ *lemma* finset.dvd_gcd_iff
- \+ *lemma* finset.dvd_lcm
- \+ *def* finset.gcd
- \+ *theorem* finset.gcd_congr
- \+ *lemma* finset.gcd_def
- \+ *lemma* finset.gcd_dvd
- \+ *lemma* finset.gcd_empty
- \+ *lemma* finset.gcd_insert
- \+ *lemma* finset.gcd_mono
- \+ *lemma* finset.gcd_mono_fun
- \+ *lemma* finset.gcd_singleton
- \+ *lemma* finset.gcd_union
- \+ *def* finset.lcm
- \+ *theorem* finset.lcm_congr
- \+ *lemma* finset.lcm_def
- \+ *lemma* finset.lcm_dvd
- \+ *lemma* finset.lcm_dvd_iff
- \+ *lemma* finset.lcm_empty
- \+ *lemma* finset.lcm_insert
- \+ *lemma* finset.lcm_mono
- \+ *lemma* finset.lcm_mono_fun
- \+ *lemma* finset.lcm_singleton
- \+ *lemma* finset.lcm_union
- \+ *lemma* finset.normalize_gcd
- \+ *lemma* finset.normalize_lcm

Modified src/data/finset/lattice.lean


Added src/data/multiset/gcd.lean
- \+ *lemma* multiset.dvd_gcd
- \+ *lemma* multiset.dvd_lcm
- \+ *def* multiset.gcd
- \+ *lemma* multiset.gcd_add
- \+ *lemma* multiset.gcd_cons
- \+ *lemma* multiset.gcd_dvd
- \+ *lemma* multiset.gcd_erase_dup
- \+ *lemma* multiset.gcd_mono
- \+ *lemma* multiset.gcd_ndinsert
- \+ *lemma* multiset.gcd_ndunion
- \+ *lemma* multiset.gcd_singleton
- \+ *lemma* multiset.gcd_union
- \+ *lemma* multiset.gcd_zero
- \+ *def* multiset.lcm
- \+ *lemma* multiset.lcm_add
- \+ *lemma* multiset.lcm_cons
- \+ *lemma* multiset.lcm_dvd
- \+ *lemma* multiset.lcm_erase_dup
- \+ *lemma* multiset.lcm_mono
- \+ *lemma* multiset.lcm_ndinsert
- \+ *lemma* multiset.lcm_ndunion
- \+ *lemma* multiset.lcm_singleton
- \+ *lemma* multiset.lcm_union
- \+ *lemma* multiset.lcm_zero
- \+ *lemma* multiset.normalize_gcd
- \+ *lemma* multiset.normalize_lcm



## [2020-09-28 04:20:18](https://github.com/leanprover-community/mathlib/commit/1761822)
chore(category_theory/limits): some limit lemmas ([#4238](https://github.com/leanprover-community/mathlib/pull/4238))
A couple of lemmas characterising definitions which are already there (the first part of [#4163](https://github.com/leanprover-community/mathlib/pull/4163))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_hom_desc
- \+ *lemma* category_theory.limits.has_limit.lift_iso_of_nat_iso_hom
- \+ *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_hom_desc
- \+ *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_inv_desc
- \+ *lemma* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso_hom_desc
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_hom
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_inv
- \+ *def* category_theory.limits.is_colimit.equiv_iso_colimit
- \+ *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_apply
- \+ *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_symm_apply
- \+/\- *def* category_theory.limits.is_colimit.map
- \+ *lemma* category_theory.limits.is_colimit.of_iso_colimit_desc
- \+ *lemma* category_theory.limits.is_colimit.ι_map
- \+ *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_hom_comp
- \+ *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_inv_comp
- \+ *def* category_theory.limits.is_limit.equiv_iso_limit
- \+ *lemma* category_theory.limits.is_limit.equiv_iso_limit_apply
- \+ *lemma* category_theory.limits.is_limit.equiv_iso_limit_symm_apply
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_inv
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_points_iso_of_nat_iso_hom
- \+/\- *def* category_theory.limits.is_limit.map
- \+ *lemma* category_theory.limits.is_limit.map_π
- \+ *lemma* category_theory.limits.is_limit.of_iso_limit_lift
- \- *lemma* category_theory.limits.is_limit_map_π
- \- *lemma* category_theory.limits.ι_is_colimit_map

Modified src/category_theory/limits/preserves/shapes.lean


Modified src/category_theory/limits/shapes/biproducts.lean




## [2020-09-28 01:45:45](https://github.com/leanprover-community/mathlib/commit/d8726bf)
feat(ring_theory/integral_closure): Explicitly define integral extensions ([#4164](https://github.com/leanprover-community/mathlib/pull/4164))
* Defined `ring_hom.is_integral_elem` as a generalization of `is_integral` that takes a ring homomorphism rather than an algebra. The old version is is redefined to be `(algebra_map R A).is_integral_elem x`.
* Create predicates `ring_hom.is_integral` and `algebra.is_integral` representing when the entire extension is integral over the base ring.
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* ideal.exists_ideal_over_prime_of_is_integral'
- \+/\- *theorem* ideal.exists_ideal_over_prime_of_is_integral
- \+/\- *lemma* ideal.is_maximal_comap_of_is_integral_of_is_maximal

Modified src/ring_theory/integral_closure.lean
- \+ *def* algebra.is_integral
- \+/\- *lemma* algebra.is_integral_trans
- \+/\- *lemma* is_integral_of_surjective
- \+/\- *lemma* is_integral_quotient_of_is_integral
- \+/\- *lemma* is_integral_trans
- \+ *def* ring_hom.is_integral
- \+ *def* ring_hom.is_integral_elem

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \+/\- *theorem* is_integral_localization



## [2020-09-28 00:59:38](https://github.com/leanprover-community/mathlib/commit/2fa1bc6)
chore(scripts): update nolints.txt ([#4293](https://github.com/leanprover-community/mathlib/pull/4293))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-27 20:45:01](https://github.com/leanprover-community/mathlib/commit/3897758)
feat(measure_theory): prove that more functions are measurable ([#4266](https://github.com/leanprover-community/mathlib/pull/4266))
Mostly additions to `borel_space`.
Generalize `measurable_bsupr` and `measurable_binfi` to countable sets (instead of encodable underlying types). Use the lemma `countable_encodable` to get the original behavior.
Some cleanup in `borel_space`: more instances are in `variables`, and lemmas with the same instances a bit more.
One downside: there is a big import bump in `borel_space`, it currently imports `hahn_banach`. This is (only) used in `measurable_smul_const`. If someone has a proof sketch (in math) of `measurable_smul_const` that doesn't involve Hahn Banach (and that maybe generalizes `real` to a topological field or something), please let me know.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* closed_embedding_smul_left
- \+ *lemma* is_closed_map_smul_left

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.ker_to_span_singleton

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* borel_eq_generate_Iio
- \+/\- *lemma* borel_eq_generate_Ioi
- \+/\- *lemma* ennreal.measurable_of_measurable_nnreal
- \+/\- *lemma* ennreal.measurable_of_measurable_nnreal_nnreal
- \+/\- *lemma* is_measurable_interval
- \+/\- *lemma* is_measurable_le'
- \+/\- *lemma* is_measurable_le
- \+/\- *lemma* is_measurable_lt'
- \+/\- *lemma* is_measurable_lt
- \+ *lemma* is_pi_system_is_open
- \+/\- *lemma* measurable.dist
- \+/\- *lemma* measurable.edist
- \+/\- *lemma* measurable.ennreal_add
- \+/\- *lemma* measurable.ennreal_coe
- \+/\- *lemma* measurable.ennreal_mul
- \+/\- *lemma* measurable.ennreal_of_real
- \+/\- *lemma* measurable.ennreal_sub
- \+ *lemma* measurable.ennreal_tsum
- \+ *lemma* measurable.inf_dist
- \+ *lemma* measurable.inf_edist
- \+/\- *lemma* measurable.is_glb
- \+/\- *lemma* measurable.is_lub
- \+/\- *lemma* measurable.max
- \+/\- *lemma* measurable.min
- \+ *lemma* measurable.mul'
- \+/\- *lemma* measurable.nndist
- \+/\- *lemma* measurable.nnreal_coe
- \+/\- *lemma* measurable.nnreal_of_real
- \+/\- *lemma* measurable.sub_nnreal
- \+ *lemma* measurable.to_nnreal
- \+ *lemma* measurable.to_real
- \+/\- *lemma* measurable_binfi
- \+/\- *lemma* measurable_bsupr
- \+ *lemma* measurable_cSup
- \+ *lemma* measurable_comp_iff_of_closed_embedding
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable_edist
- \+ *lemma* measurable_ennnorm
- \+ *lemma* measurable_ennreal_coe_iff
- \+ *lemma* measurable_ennreal_to_real
- \+ *lemma* measurable_inf_dist
- \+ *lemma* measurable_inf_edist
- \+/\- *lemma* measurable_infi
- \+/\- *lemma* measurable_nndist
- \+ *lemma* measurable_of_Ici
- \+ *lemma* measurable_of_Iic
- \+ *lemma* measurable_of_Iio
- \+ *lemma* measurable_of_Ioi
- \+ *lemma* measurable_of_is_closed'
- \+ *lemma* measurable_of_is_closed
- \+ *lemma* measurable_of_is_open
- \+ *lemma* measurable_smul_const
- \+/\- *lemma* measurable_supr
- \+ *lemma* measurable_to_nnreal
- \+ *lemma* nnreal.measurable_coe

Modified src/measure_theory/giry_monad.lean
- \+ *lemma* measure_theory.measure.measurable_measure

Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable_swap_iff
- \+ *lemma* measurable.of_uncurry_left
- \+ *lemma* measurable.of_uncurry_right
- \+ *lemma* measurable_prod
- \+ *lemma* measurable_prod_mk_left
- \+ *lemma* measurable_prod_mk_right
- \+ *lemma* measurable_swap
- \+ *lemma* measurable_swap_iff

Modified src/measure_theory/set_integral.lean


Modified src/topology/algebra/module.lean


Modified src/topology/homeomorph.lean


Modified src/topology/maps.lean
- \+ *lemma* is_closed_map.of_nonempty

Modified src/topology/separation.lean
- \+ *lemma* is_closed_map_const



## [2020-09-27 18:31:22](https://github.com/leanprover-community/mathlib/commit/c322471)
feat(undergrad.yaml): missing items ([#4290](https://github.com/leanprover-community/mathlib/pull/4290))
#### Estimated changes
Modified docs/undergrad.yaml




## [2020-09-27 16:34:03](https://github.com/leanprover-community/mathlib/commit/2516d7d)
feat(topology): various additions ([#4264](https://github.com/leanprover-community/mathlib/pull/4264))
Some if it is used for Fubini, but some of the results were rabbit holes I went into, which I never ended up using, but that still seem useful.
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *theorem* filter.has_basis.Liminf_eq_supr_Inf
- \+ *theorem* filter.has_basis.liminf_eq_supr_infi
- \+ *theorem* filter.has_basis.limsup_eq_infi_supr
- \+/\- *lemma* filter.liminf_eq_supr_infi_of_nat'
- \+/\- *lemma* filter.liminf_eq_supr_infi_of_nat
- \+/\- *lemma* filter.limsup_eq_infi_supr_of_nat'
- \+/\- *lemma* filter.limsup_eq_infi_supr_of_nat

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* pi.has_sum
- \+ *lemma* pi.summable
- \+ *lemma* tsum_apply

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_closed_le_prod
- \+ *lemma* is_open_lt_prod

Modified src/topology/constructions.lean
- \+ *lemma* tendsto_pi

Modified src/topology/instances/ennreal.lean


Modified src/topology/list.lean
- \+ *lemma* filter.tendsto.cons
- \+ *lemma* list.continuous_cons
- \+ *lemma* list.continuous_prod
- \- *lemma* list.tendsto_cons'
- \+/\- *lemma* list.tendsto_cons
- \+/\- *lemma* list.tendsto_insert_nth
- \+ *lemma* list.tendsto_prod
- \+/\- *lemma* nhds_cons
- \+/\- *lemma* nhds_list
- \+/\- *lemma* nhds_nil
- \+/\- *lemma* vector.continuous_at_remove_nth
- \+/\- *lemma* vector.continuous_insert_nth'
- \+/\- *lemma* vector.continuous_insert_nth
- \+/\- *lemma* vector.continuous_remove_nth
- \+/\- *lemma* vector.tendsto_cons

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* metric.coe_inf_nndist
- \+ *lemma* metric.continuous_inf_nndist_pt
- \+ *def* metric.inf_nndist
- \+ *lemma* metric.lipschitz_inf_nndist_pt
- \+ *lemma* metric.uniform_continuous_inf_nndist_pt



## [2020-09-27 08:58:36](https://github.com/leanprover-community/mathlib/commit/b6ce982)
refactor(*): create directory field_theory/finite ([#4212](https://github.com/leanprover-community/mathlib/pull/4212))
facts on finite fields needed facts on polynomials
facts on polynomials wanted to use things about finite fields
this PR reorganises some of the imports
at the moment it also contributes a bit of new stuff,
and depends on two other PRs that add new stuff.
#### Estimated changes
Modified src/data/zmod/basic.lean


Deleted src/data/zmod/polynomial.lean
- \- *lemma* mv_polynomial.C_dvd_iff_zmod

Modified src/field_theory/chevalley_warning.lean


Renamed src/field_theory/finite.lean to src/field_theory/finite/basic.lean
- \+ *lemma* zmod.frobenius_zmod

Added src/field_theory/finite/polynomial.lean
- \+ *lemma* mv_polynomial.C_dvd_iff_zmod
- \+ *def* mv_polynomial.R
- \+ *lemma* mv_polynomial.degrees_indicator
- \+ *lemma* mv_polynomial.dim_R
- \+ *lemma* mv_polynomial.eq_zero_of_eval_eq_zero
- \+ *lemma* mv_polynomial.eval_indicator_apply_eq_one
- \+ *lemma* mv_polynomial.eval_indicator_apply_eq_zero
- \+ *def* mv_polynomial.evalᵢ
- \+ *def* mv_polynomial.evalₗ
- \+ *lemma* mv_polynomial.evalₗ_apply
- \+ *lemma* mv_polynomial.expand_zmod
- \+ *lemma* mv_polynomial.frobenius_zmod
- \+ *def* mv_polynomial.indicator
- \+ *lemma* mv_polynomial.indicator_mem_restrict_degree
- \+ *lemma* mv_polynomial.ker_evalₗ
- \+ *lemma* mv_polynomial.map_restrict_dom_evalₗ
- \+ *lemma* mv_polynomial.range_evalᵢ

Modified src/field_theory/mv_polynomial.lean
- \- *def* mv_polynomial.R
- \- *lemma* mv_polynomial.degrees_indicator
- \- *lemma* mv_polynomial.dim_R
- \- *lemma* mv_polynomial.eq_zero_of_eval_eq_zero
- \- *lemma* mv_polynomial.eval_indicator_apply_eq_one
- \- *lemma* mv_polynomial.eval_indicator_apply_eq_zero
- \- *def* mv_polynomial.evalᵢ
- \- *def* mv_polynomial.evalₗ
- \- *lemma* mv_polynomial.evalₗ_apply
- \- *def* mv_polynomial.indicator
- \- *lemma* mv_polynomial.indicator_mem_restrict_degree
- \- *lemma* mv_polynomial.ker_evalₗ
- \- *lemma* mv_polynomial.map_restrict_dom_evalₗ
- \- *lemma* mv_polynomial.range_evalᵢ

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean




## [2020-09-27 07:48:56](https://github.com/leanprover-community/mathlib/commit/95ab6ac)
docs(overview): expand analysis ([#4284](https://github.com/leanprover-community/mathlib/pull/4284))
A few additions to the "normed spaces", "convexity", "special functions" and "manifolds" sections of the overview.
#### Estimated changes
Modified docs/overview.yaml




## [2020-09-27 05:22:34](https://github.com/leanprover-community/mathlib/commit/a7e3435)
chore(data/option): swap sides in `ne_none_iff_exists` ([#4285](https://github.com/leanprover-community/mathlib/pull/4285))
* swap lhs and rhs of the equality in `option.ne_none_iff_exists`; the new order matches, e.g., the definition of `set.range` and `can_lift.prf`;
* the same in `with_one.ne_one_iff_exists` and `with_zero.ne_zero_iff_exists`;
* remove `option.ne_none_iff_exists'`;
* restore the original `option.ne_none_iff_exists` as `option.ne_none_iff_exists'`
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_one.ne_one_iff_exists

Modified src/data/option/basic.lean
- \+/\- *lemma* option.ne_none_iff_exists'
- \+/\- *lemma* option.ne_none_iff_exists

Modified src/data/seq/seq.lean




## [2020-09-27 01:39:14](https://github.com/leanprover-community/mathlib/commit/5f6b07f)
chore(scripts): update nolints.txt ([#4283](https://github.com/leanprover-community/mathlib/pull/4283))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-27 00:33:40](https://github.com/leanprover-community/mathlib/commit/5c957ec)
feat(analysis/convex/integral): Jensen's inequality for integrals ([#4225](https://github.com/leanprover-community/mathlib/pull/4225))
#### Estimated changes
Added src/analysis/convex/integral.lean
- \+ *lemma* convex.integral_mem
- \+ *lemma* convex.smul_integral_mem
- \+ *lemma* convex_on.map_integral_le
- \+ *lemma* convex_on.map_smul_integral_le

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* prod.nnnorm_def

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.simple_func.sum_range_measure_preimage_singleton

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.prod_mk

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.probability_measure.ne_zero

Modified src/measure_theory/set_integral.lean
- \+ *lemma* fst_integral
- \+ *lemma* integral_pair
- \+ *lemma* snd_integral



## [2020-09-26 20:43:15](https://github.com/leanprover-community/mathlib/commit/8600cb0)
feat(measure_space): define sigma finite measures ([#4265](https://github.com/leanprover-community/mathlib/pull/4265))
They are defined as a `Prop`. The noncomputable "eliminator" is called `spanning_sets`, and satisfies monotonicity, even though that is not required to give a `sigma_finite` instance.
I define a helper function `accumulate s := ⋃ y ≤ x, s y`. This is helpful, to separate out some monotonicity proofs. It is in its own file purely for import reasons (there is no good file to put it that imports both `set.lattice` and `finset.basic`, the latter is used in 1 lemma).
#### Estimated changes
Added src/data/set/accumulate.lean
- \+ *lemma* set.Union_accumulate
- \+ *def* set.accumulate
- \+ *lemma* set.accumulate_def
- \+ *lemma* set.bUnion_accumulate
- \+ *lemma* set.mem_accumulate
- \+ *lemma* set.monotone_accumulate
- \+ *lemma* set.subset_accumulate

Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_prod_of_monotone
- \+ *lemma* set.image2_eq_seq

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.Union_spanning_sets
- \+ *lemma* measure_theory.exists_finite_spanning_sets
- \+ *lemma* measure_theory.is_measurable_spanning_sets
- \+ *lemma* measure_theory.measure.supr_restrict_spanning_sets
- \+ *lemma* measure_theory.measure_bUnion_lt_top
- \+ *lemma* measure_theory.measure_spanning_sets_lt_top
- \+ *lemma* measure_theory.monotone_spanning_sets
- \+ *def* measure_theory.spanning_sets



## [2020-09-26 19:15:53](https://github.com/leanprover-community/mathlib/commit/253b120)
feat(field_theory): prove primitive element theorem ([#4153](https://github.com/leanprover-community/mathlib/pull/4153))
Proof of the primitive element theorem. The main proof is in `field_theory/primitive_element.lean`. Some lemmas we used have been added to other files. We have also changed the notation for adjoining an element to a field to be easier to use.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.eval_gcd_eq_zero
- \+ *lemma* polynomial.eval₂_gcd_eq_zero
- \+ *lemma* polynomial.is_root_gcd_iff_is_root_left_right
- \+ *lemma* polynomial.mem_roots_map
- \+ *lemma* polynomial.root_gcd_iff_root_left_right
- \+ *lemma* polynomial.root_left_of_root_gcd
- \+ *lemma* polynomial.root_right_of_root_gcd

Modified src/deprecated/subfield.lean
- \+ *lemma* is_subfield.pow_mem

Modified src/field_theory/adjoin.lean
- \+ *lemma* field.adjoin_adjoin_comm
- \+ *lemma* field.adjoin_dim_eq_one_iff
- \+ *lemma* field.adjoin_dim_eq_one_of_sub_bot
- \+ *lemma* field.adjoin_eq_bot
- \+ *lemma* field.adjoin_eq_bot_iff
- \+ *lemma* field.adjoin_eq_range_algebra_map_adjoin
- \+ *lemma* field.adjoin_findim_eq_one_iff
- \+ *lemma* field.adjoin_one
- \+/\- *lemma* field.adjoin_simple.algebra_map_gen
- \+/\- *lemma* field.adjoin_simple_adjoin_simple
- \+ *lemma* field.adjoin_simple_comm
- \+ *lemma* field.adjoin_simple_dim_eq_one_iff
- \+ *lemma* field.adjoin_simple_dim_eq_one_of_mem_bot
- \+ *lemma* field.adjoin_simple_eq_bot
- \+ *lemma* field.adjoin_simple_eq_bot_iff
- \+ *lemma* field.adjoin_simple_findim_eq_one_iff
- \- *lemma* field.adjoin_singleton
- \+ *lemma* field.adjoin_zero
- \+ *lemma* field.bot_eq_top_of_dim_adjoin_eq_one
- \+ *lemma* field.bot_eq_top_of_findim_adjoin_eq_one
- \+ *lemma* field.bot_eq_top_of_findim_adjoin_le_one
- \+ *lemma* field.mem_bot_of_adjoin_simple_dim_eq_one
- \+ *lemma* field.mem_bot_of_adjoin_simple_sub_bot
- \+ *lemma* field.sub_bot_of_adjoin_dim_eq_one
- \+ *lemma* field.sub_bot_of_adjoin_sub_bot

Modified src/field_theory/minimal_polynomial.lean
- \+ *lemma* minimal_polynomial.dvd_map_of_is_scalar_tower

Added src/field_theory/primitive_element.lean
- \+ *theorem* field.exists_primitive_element
- \+ *theorem* field.exists_primitive_element_aux
- \+ *theorem* field.exists_primitive_element_inf
- \+ *theorem* field.exists_primitive_element_of_fintype_bot
- \+ *lemma* field.exists_primitive_element_of_fintype_top
- \+ *lemma* field.primitive_element_inf_aux
- \+ *lemma* field.primitive_element_inf_aux_exists_c

Modified src/field_theory/separable.lean
- \+ *lemma* is_separable_tower_bot_of_is_separable
- \+ *lemma* is_separable_tower_top_of_is_separable
- \+ *lemma* polynomial.eq_X_sub_C_of_separable_of_root_eq
- \+ *lemma* polynomial.separable_gcd_left
- \+ *lemma* polynomial.separable_gcd_right

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.eq_X_sub_C_of_splits_of_single_root
- \+ *lemma* polynomial.splits_of_splits_gcd_left
- \+ *lemma* polynomial.splits_of_splits_gcd_right

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *theorem* findim_top
- \+ *lemma* finite_dimensional_of_dim_eq_one
- \+ *lemma* subalgebra.bot_eq_top_of_dim_eq_one
- \+ *lemma* subalgebra.bot_eq_top_of_findim_eq_one
- \+ *lemma* subalgebra.dim_bot
- \+ *theorem* subalgebra.dim_eq_one_iff
- \+ *lemma* subalgebra.dim_eq_one_of_eq_bot
- \+ *lemma* subalgebra.dim_top
- \+ *lemma* subalgebra.eq_bot_of_dim_one
- \+ *lemma* subalgebra.eq_bot_of_findim_one
- \+ *lemma* subalgebra.findim_bot
- \+ *theorem* subalgebra.findim_eq_one_iff
- \+ *lemma* subalgebra.findim_eq_one_of_eq_bot
- \+ *lemma* subalgebra.finite_dimensional_bot
- \+ *lemma* subalgebra_top_dim_eq_submodule_top_dim
- \+ *lemma* subalgebra_top_findim_eq_submodule_top_findim

Modified src/ring_theory/algebra.lean
- \+ *theorem* algebra.coe_bot

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+ *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field
- \+ *lemma* is_scalar_tower.algebra_map_aeval

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_tower_bot_of_is_integral_field



## [2020-09-26 19:15:50](https://github.com/leanprover-community/mathlib/commit/d0b5947)
feat(algebra/universal_enveloping_algebra): construction of universal enveloping algebra and its universal property ([#4041](https://github.com/leanprover-community/mathlib/pull/4041))
## Main definitions
  * `universal_enveloping_algebra`
  * `universal_enveloping_algebra.algebra`
  * `universal_enveloping_algebra.lift`
  * `universal_enveloping_algebra.ι_comp_lift`
  * `universal_enveloping_algebra.lift_unique`
  * `universal_enveloping_algebra.hom_ext`
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *lemma* lie_algebra.coe_to_linear_map
- \+ *lemma* lie_algebra.morphism.ext

Added src/algebra/universal_enveloping_algebra.lean
- \+ *lemma* universal_enveloping_algebra.hom_ext
- \+ *def* universal_enveloping_algebra.lift
- \+ *lemma* universal_enveloping_algebra.lift_unique
- \+ *lemma* universal_enveloping_algebra.lift_ι_apply
- \+ *def* universal_enveloping_algebra.mk_alg_hom
- \+ *def* universal_enveloping_algebra.ι
- \+ *lemma* universal_enveloping_algebra.ι_comp_lift
- \+ *def* universal_enveloping_algebra

Modified src/linear_algebra/tensor_algebra.lean


Modified src/ring_theory/algebra.lean




## [2020-09-26 17:53:17](https://github.com/leanprover-community/mathlib/commit/3ebee15)
feat(src/data/polynomial/ring_division.lean): eq_zero_of_infinite_is_root ([#4280](https://github.com/leanprover-community/mathlib/pull/4280))
add a lemma stating that a polynomial is zero if it has infinitely many roots.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.eq_of_infinite_eval_eq
- \+ *lemma* polynomial.eq_zero_of_infinite_is_root



## [2020-09-26 17:53:15](https://github.com/leanprover-community/mathlib/commit/376ab30)
feat(data/nat/unique_factorization): a `unique_factorization_monoid` instance on N ([#4194](https://github.com/leanprover-community/mathlib/pull/4194))
Provides a `unique_factorization_monoid` instance on `nat`
Shows its equivalence to `nat.factors`, which is list-valued
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* associated_eq_eq
- \+ *theorem* associated_iff_eq

Added src/data/nat/associated.lean
- \+ *theorem* nat.irreducible_iff_prime
- \+ *theorem* nat.prime_iff

Added src/data/nat/unique_factorization.lean
- \+ *theorem* nat.factors_eq



## [2020-09-26 15:49:19](https://github.com/leanprover-community/mathlib/commit/88e198a)
feat(data/multiset): count repeat lemma ([#4278](https://github.com/leanprover-community/mathlib/pull/4278))
A small lemma and renaming (of `count_repeat` to `count_repeat_self`) to count elements in a `multiset.repeat`. One part of [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.count_repeat
- \+ *theorem* multiset.count_repeat_self



## [2020-09-26 15:49:16](https://github.com/leanprover-community/mathlib/commit/8e83805)
chore(analysis/special_functions/pow): +2 lemmas about `nnreal.rpow` ([#4272](https://github.com/leanprover-community/mathlib/pull/4272))
`λ x, x^y` is continuous in more cases than `λ p, p.1^p.2`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* nnreal.continuous_at_rpow_const
- \+ *lemma* nnreal.continuous_rpow_const



## [2020-09-26 15:49:14](https://github.com/leanprover-community/mathlib/commit/3177493)
feat(ring_theory/algebra, algebra/module): Add add_comm_monoid_to_add_comm_group and semiring_to_ring ([#4252](https://github.com/leanprover-community/mathlib/pull/4252))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *def* semimodule.add_comm_monoid_to_add_comm_group

Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/algebra.lean
- \+/\- *lemma* algebra.mul_sub_algebra_map_commutes
- \+/\- *lemma* algebra.mul_sub_algebra_map_pow_commutes
- \+ *def* algebra.semiring_to_ring



## [2020-09-26 15:49:13](https://github.com/leanprover-community/mathlib/commit/7c0c16c)
feat(data/list/basic): Add lemmas about inits and tails ([#4222](https://github.com/leanprover-community/mathlib/pull/4222))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.inits_append
- \+ *lemma* list.inits_cons
- \+ *lemma* list.inits_eq_tails
- \+ *lemma* list.inits_reverse
- \+ *lemma* list.map_reverse_inits
- \+ *lemma* list.map_reverse_tails
- \+ *theorem* list.reverse_involutive
- \+ *lemma* list.tails_append
- \+ *lemma* list.tails_cons
- \+ *lemma* list.tails_eq_inits
- \+ *lemma* list.tails_reverse

Modified src/data/list/zip.lean
- \+ *lemma* list.mem_zip_inits_tails

Modified src/logic/function/basic.lean
- \+ *lemma* function.involutive.comp_self



## [2020-09-26 13:57:50](https://github.com/leanprover-community/mathlib/commit/bc3a6cf)
chore(data/list/basic): Make it clear that `forall_mem_cons` and `ball_cons` are synonyms ([#4279](https://github.com/leanprover-community/mathlib/pull/4279))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.forall_mem_cons



## [2020-09-26 12:12:06](https://github.com/leanprover-community/mathlib/commit/9b09f90)
feat(ennreal): some lemmas about ennreal ([#4262](https://github.com/leanprover-community/mathlib/pull/4262))
Also some lemmas about norms in (e)nnreal.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *def* nnnorm
- \+ *lemma* real.ennnorm_eq_of_real
- \+ *lemma* real.nnnorm_coe_eq_self
- \+ *lemma* real.nnnorm_of_nonneg
- \+ *lemma* real.norm_of_nonneg

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.mul_lt_top_iff
- \+ *lemma* ennreal.of_real_le_of_le_to_real

Modified src/measure_theory/borel_space.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.continuous_coe
- \+ *lemma* ennreal.continuous_coe_iff



## [2020-09-26 10:16:14](https://github.com/leanprover-community/mathlib/commit/280a42e)
chore(topology/instances/nnreal): reuse `order_topology_of_ord_connected` ([#4277](https://github.com/leanprover-community/mathlib/pull/4277))
#### Estimated changes
Modified src/topology/instances/nnreal.lean




## [2020-09-26 10:16:12](https://github.com/leanprover-community/mathlib/commit/b8b6f5d)
chore(order/filter/archimedean): move&generalize a few lemmas ([#4275](https://github.com/leanprover-community/mathlib/pull/4275))
* `tendsto_coe_nat_real_at_top_iff`: `tendsto_coe_nat_at_top_iff`,
  generalize to a linear ordered archimedean semiring;
* `tendsto_coe_nat_real_at_top_at_top`: `tendsto_coe_nat_at_top_at_top`,
  generalize to a linear ordered archimedean semiring;
* `tendsto_coe_int_real_at_top_iff`: `tendsto_coe_int_at_top_iff`,
  generalize to a linear ordered archimedean ring;
* `tendsto_coe_int_real_at_top_at_top`: `tendsto_coe_int_at_top_at_top`,
  generalize to a linear ordered archimedean ring;
* add versions for `ℚ`;
* golf the proof of `tendsto_at_top_embedding`.
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *theorem* exists_nat_ge

Modified src/analysis/specific_limits.lean


Modified src/data/real/ennreal.lean


Added src/order/filter/archimedean.lean
- \+ *lemma* tendsto_coe_int_at_top_at_top
- \+ *lemma* tendsto_coe_int_at_top_iff
- \+ *lemma* tendsto_coe_nat_at_top_at_top
- \+ *lemma* tendsto_coe_nat_at_top_iff
- \+ *lemma* tendsto_coe_rat_at_top_iff

Modified src/order/filter/at_top_bot.lean


Modified src/topology/instances/real.lean
- \- *lemma* tendsto_coe_int_real_at_top_at_top
- \- *lemma* tendsto_coe_int_real_at_top_iff
- \- *lemma* tendsto_coe_nat_real_at_top_at_top
- \- *lemma* tendsto_coe_nat_real_at_top_iff



## [2020-09-26 10:16:10](https://github.com/leanprover-community/mathlib/commit/aa11589)
feat(algebra/homology, category_theory/abelian): expand API on exactness ([#4256](https://github.com/leanprover-community/mathlib/pull/4256))
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \- *lemma* category_theory.exact.w_assoc
- \+ *lemma* category_theory.exact_comp_hom_inv_comp
- \+ *lemma* category_theory.exact_comp_hom_inv_comp_iff
- \+ *lemma* category_theory.exact_comp_mono
- \+ *lemma* category_theory.exact_epi_comp
- \+ *lemma* category_theory.exact_kernel
- \+ *lemma* category_theory.exact_zero_left_of_mono
- \+ *lemma* category_theory.kernel_ι_eq_zero_of_exact_zero_left

Modified src/algebra/homology/image_to_kernel_map.lean
- \+ *lemma* category_theory.image_to_kernel_map_comp_hom_inv_comp
- \+ *lemma* category_theory.image_to_kernel_map_comp_left
- \+ *lemma* category_theory.image_to_kernel_map_comp_right
- \+/\- *lemma* category_theory.image_to_kernel_map_epi_of_epi_of_zero
- \+/\- *lemma* category_theory.image_to_kernel_map_epi_of_zero_of_mono

Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.epi_of_cokernel_π_eq_zero
- \+ *lemma* category_theory.abelian.epi_of_zero_cokernel
- \+ *lemma* category_theory.abelian.mono_of_kernel_ι_eq_zero
- \+ *lemma* category_theory.abelian.mono_of_zero_kernel

Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.epi_iff_cokernel_π_eq_zero
- \+ *lemma* category_theory.abelian.epi_iff_exact_zero_right
- \+ *lemma* category_theory.abelian.exact_cokernel
- \+ *lemma* category_theory.abelian.mono_iff_exact_zero_left
- \+ *lemma* category_theory.abelian.mono_iff_kernel_ι_eq_zero
- \+ *lemma* category_theory.abelian.tfae_epi
- \+ *lemma* category_theory.abelian.tfae_mono

Modified src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.image.post_comp_is_iso
- \+ *lemma* category_theory.limits.image.post_comp_is_iso_hom_comp_image_ι
- \+ *lemma* category_theory.limits.image.post_comp_is_iso_inv_comp_image_ι

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-09-26 10:16:08](https://github.com/leanprover-community/mathlib/commit/61897ae)
feat(data/set/intervals/infinite): intervals are infinite ([#4241](https://github.com/leanprover-community/mathlib/pull/4241))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.exists_maximal
- \+ *lemma* finset.exists_minimal

Modified src/data/set/finite.lean
- \+ *theorem* set.finite.to_finset.nonempty
- \+ *theorem* set.infinite_mono

Added src/data/set/intervals/infinite.lean
- \+ *lemma* set.Icc.infinite
- \+ *lemma* set.Ici.infinite
- \+ *lemma* set.Ico.infinite
- \+ *lemma* set.Iic.infinite
- \+ *lemma* set.Iio.infinite
- \+ *lemma* set.Ioc.infinite
- \+ *lemma* set.Ioi.infinite
- \+ *lemma* set.Ioo.infinite



## [2020-09-26 10:16:06](https://github.com/leanprover-community/mathlib/commit/e3cc06e)
feat(algebraic_geometry/presheafed_space): gluing presheaves ([#4198](https://github.com/leanprover-community/mathlib/pull/4198))
#### `PresheafedSpace C` has colimits.
If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.
When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.
Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.
Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)
The limit of this diagram then constitutes the colimit presheaf.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.comp
- \+ *lemma* algebraic_geometry.PresheafedSpace.congr_app

Added src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+ *def* algebraic_geometry.PresheafedSpace.colimit
- \+ *def* algebraic_geometry.PresheafedSpace.colimit_cocone
- \+ *def* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app
- \+ *lemma* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality
- \+ *def* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit
- \+ *lemma* algebraic_geometry.PresheafedSpace.map_comp_c_app
- \+ *lemma* algebraic_geometry.PresheafedSpace.map_id_c_app
- \+ *def* algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit

Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.eq_to_hom_unop
- \+ *lemma* category_theory.nat_trans.congr

Modified src/category_theory/grothendieck.lean
- \+ *lemma* category_theory.grothendieck.congr
- \+ *lemma* category_theory.grothendieck.id_fiber'

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/functor_category.lean
- \+ *lemma* category_theory.limits.colimit.ι_desc_app
- \+ *lemma* category_theory.limits.colimit_obj_ext
- \+ *def* category_theory.limits.colimit_obj_iso_colimit_comp_evaluation
- \+ *lemma* category_theory.limits.colimit_obj_iso_colimit_comp_evaluation_ι_app_hom
- \+ *lemma* category_theory.limits.colimit_obj_iso_colimit_comp_evaluation_ι_inv
- \+ *lemma* category_theory.limits.limit.lift_π_app
- \+ *lemma* category_theory.limits.limit_obj_ext
- \+ *def* category_theory.limits.limit_obj_iso_limit_comp_evaluation
- \+ *lemma* category_theory.limits.limit_obj_iso_limit_comp_evaluation_hom_π
- \+ *lemma* category_theory.limits.limit_obj_iso_limit_comp_evaluation_inv_π_app

Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colimit.desc_cocone
- \+ *lemma* category_theory.limits.limit.lift_cone

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.colimit.w_apply
- \+ *lemma* category_theory.limits.types.colimit.ι_desc_apply
- \+ *lemma* category_theory.limits.types.colimit.ι_map_apply
- \- *lemma* category_theory.limits.types.colimit_w_apply
- \- *lemma* category_theory.limits.types.lift_π_apply
- \+ *lemma* category_theory.limits.types.limit.lift_π_apply
- \+ *lemma* category_theory.limits.types.limit.map_π_apply
- \+ *lemma* category_theory.limits.types.limit.w_apply
- \- *lemma* category_theory.limits.types.limit_w_apply
- \- *lemma* category_theory.limits.types.map_π_apply
- \- *lemma* category_theory.limits.types.ι_desc_apply
- \- *lemma* category_theory.limits.types.ι_map_apply

Modified src/topology/category/Top/opens.lean
- \+ *lemma* topological_space.opens.map_comp_map

Added src/topology/sheaves/limits.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/presheaf.lean
- \- *def* Top.presheaf.pushforward
- \+ *lemma* Top.presheaf.pushforward_eq_hom_app
- \+ *lemma* Top.presheaf.pushforward_eq_rfl
- \+ *def* Top.presheaf.pushforward_map
- \+ *def* Top.presheaf.pushforward_obj
- \+ *lemma* Top.presheaf.pushforward_obj_map
- \+ *lemma* Top.presheaf.pushforward_obj_obj

Modified src/topology/sheaves/stalks.lean




## [2020-09-26 07:58:50](https://github.com/leanprover-community/mathlib/commit/c2f896f)
feat(data/set): add some lemmas ([#4263](https://github.com/leanprover-community/mathlib/pull/4263))
Some lemmas about sets, mostly involving disjointness
I also sneaked in the lemma `(λ x : α, y) = const α y` which is useful to rewrite with.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.preimage_swap_prod

Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.preimage
- \+ *theorem* disjoint.union_left
- \+ *theorem* disjoint.union_right
- \- *lemma* set.disjoint.preimage
- \- *theorem* set.disjoint.union_left
- \- *theorem* set.disjoint.union_right
- \+/\- *theorem* set.disjoint_iff_inter_eq_empty
- \+/\- *lemma* set.disjoint_left
- \+/\- *theorem* set.disjoint_of_subset_left
- \+/\- *theorem* set.disjoint_of_subset_right
- \+/\- *theorem* set.disjoint_right
- \+/\- *theorem* set.disjoint_singleton_left
- \+/\- *theorem* set.disjoint_singleton_right
- \+/\- *theorem* set.disjoint_union_left
- \+/\- *theorem* set.disjoint_union_right
- \+ *lemma* set.disjoint_univ
- \+/\- *lemma* set.not_disjoint_iff
- \+ *lemma* set.preimage_eq_empty
- \+ *lemma* set.preimage_eq_empty_iff
- \+ *lemma* set.univ_disjoint

Modified src/logic/function/basic.lean
- \+ *lemma* function.const_def



## [2020-09-26 07:58:48](https://github.com/leanprover-community/mathlib/commit/1892724)
feat(data/matrix): definition of `block_diagonal` ([#4257](https://github.com/leanprover-community/mathlib/pull/4257))
This PR defines `matrix.block_diagonal : (o -> matrix m n R) -> matrix (m × o) (n × o) R`. The choice to put `o` on the right hand side of the product will help with relating this to `is_basis.smul`, but it won't be a huge hassle to write `matrix (o × m) (o × m) R` instead if you prefer.
I also tried making `m` and `n` depend on `o`, giving `block_diagonal M : matrix (Σ k : o, m k) (Σ k : o, n k) R`, but that turned out to be a shotcut to `eq.rec` hell.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_product_univ

Modified src/data/matrix/basic.lean
- \+ *def* matrix.block_diagonal
- \+ *lemma* matrix.block_diagonal_add
- \+ *lemma* matrix.block_diagonal_apply
- \+ *lemma* matrix.block_diagonal_apply_eq
- \+ *lemma* matrix.block_diagonal_apply_ne
- \+ *lemma* matrix.block_diagonal_diagonal
- \+ *lemma* matrix.block_diagonal_mul
- \+ *lemma* matrix.block_diagonal_neg
- \+ *lemma* matrix.block_diagonal_one
- \+ *lemma* matrix.block_diagonal_smul
- \+ *lemma* matrix.block_diagonal_sub
- \+ *lemma* matrix.block_diagonal_transpose
- \+ *lemma* matrix.block_diagonal_zero



## [2020-09-26 06:09:45](https://github.com/leanprover-community/mathlib/commit/7aef150)
feat(category_theory): sieves ([#3909](https://github.com/leanprover-community/mathlib/pull/3909))
Define sieves, from my topos project. Co-authored by @EdAyers. 
These definitions and lemmas have been battle-tested quite a bit so I'm reasonably confident they're workable.
#### Estimated changes
Added src/category_theory/sites/sieves.lean
- \+ *lemma* category_theory.sieve.arrows_ext
- \+ *def* category_theory.sieve.functor
- \+ *def* category_theory.sieve.functor_inclusion
- \+ *def* category_theory.sieve.galois_coinsertion_of_mono
- \+ *lemma* category_theory.sieve.galois_connection
- \+ *def* category_theory.sieve.galois_insertion_of_split_epi
- \+ *def* category_theory.sieve.generate
- \+ *def* category_theory.sieve.gi_generate
- \+ *lemma* category_theory.sieve.id_mem_iff_eq_top
- \+ *lemma* category_theory.sieve.le_pushforward_pullback
- \+ *lemma* category_theory.sieve.mem_Inf
- \+ *lemma* category_theory.sieve.mem_Sup
- \+ *lemma* category_theory.sieve.mem_inter
- \+ *lemma* category_theory.sieve.mem_pullback
- \+ *lemma* category_theory.sieve.mem_pushforward_of_comp
- \+ *lemma* category_theory.sieve.mem_top
- \+ *lemma* category_theory.sieve.mem_union
- \+ *def* category_theory.sieve.nat_trans_of_le
- \+ *lemma* category_theory.sieve.nat_trans_of_le_comm
- \+ *def* category_theory.sieve.pullback
- \+ *lemma* category_theory.sieve.pullback_comp
- \+ *lemma* category_theory.sieve.pullback_eq_top_iff_mem
- \+ *lemma* category_theory.sieve.pullback_inter
- \+ *lemma* category_theory.sieve.pullback_monotone
- \+ *lemma* category_theory.sieve.pullback_pushforward_le
- \+ *lemma* category_theory.sieve.pullback_top
- \+ *def* category_theory.sieve.pushforward
- \+ *lemma* category_theory.sieve.pushforward_comp
- \+ *lemma* category_theory.sieve.pushforward_monotone
- \+ *lemma* category_theory.sieve.pushforward_union
- \+ *def* category_theory.sieve.set_over
- \+ *lemma* category_theory.sieve.sets_iff_generate



## [2020-09-26 02:31:08](https://github.com/leanprover-community/mathlib/commit/6289adf)
fix(order/bounded_lattice): fix some misleading theorem names ([#4271](https://github.com/leanprover-community/mathlib/pull/4271))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+/\- *lemma* with_top.coe_lt_top
- \+ *theorem* with_top.le_none
- \- *theorem* with_top.none_le
- \- *theorem* with_top.none_lt_some
- \+ *theorem* with_top.some_lt_none



## [2020-09-26 01:49:24](https://github.com/leanprover-community/mathlib/commit/d76f19f)
feat(overview): expand measure theory ([#4258](https://github.com/leanprover-community/mathlib/pull/4258))
#### Estimated changes
Modified docs/overview.yaml




## [2020-09-26 00:58:04](https://github.com/leanprover-community/mathlib/commit/4b3570f)
chore(scripts): update nolints.txt ([#4270](https://github.com/leanprover-community/mathlib/pull/4270))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-25 19:15:25](https://github.com/leanprover-community/mathlib/commit/85bbf8a)
feat(data/fin): `zero_eq_one_iff` and `one_eq_zero_iff` ([#4255](https://github.com/leanprover-community/mathlib/pull/4255))
Just a pair of little lemmas that were handy to me. The main benefit is that `simp` can now prove `if (0 : fin 2) = 1 then 1 else 0 = 0`, which should help with calculations using `data.matrix.notation`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.one_eq_zero_iff
- \+ *lemma* fin.zero_eq_one_iff



## [2020-09-25 16:57:57](https://github.com/leanprover-community/mathlib/commit/3a591e8)
chore(data/list/defs): mark pairwise.nil simp to match chain.nil ([#4254](https://github.com/leanprover-community/mathlib/pull/4254))
#### Estimated changes
Modified src/data/list/defs.lean




## [2020-09-25 16:57:55](https://github.com/leanprover-community/mathlib/commit/5e8d527)
feat(ring_theory/witt_vector/witt_polynomial): definition and basic properties ([#4236](https://github.com/leanprover-community/mathlib/pull/4236))
From the Witt vector project
This is the first of a dozen of files on Witt vectors. This file contains
the definition of the so-called Witt polynomials.
Follow-up PRs will contain:
* An important structural result on the Witt polynomials
* The definition of the ring of Witt vectors (including the ring structure)
* Several common operations on Witt vectors
* Identities between thes operations
* A comparison isomorphism between the ring of Witt vectors over F_p and
the ring of p-adic integers Z_p.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* commute_inv_of
- \- *def* invertible_inv_of

Modified src/data/mv_polynomial/variables.lean
- \+/\- *lemma* mv_polynomial.vars_X

Added src/ring_theory/witt_vector/witt_polynomial.lean
- \+ *lemma* X_in_terms_of_W_aux
- \+ *lemma* X_in_terms_of_W_eq
- \+ *lemma* X_in_terms_of_W_vars_aux
- \+ *lemma* X_in_terms_of_W_vars_subset
- \+ *lemma* X_in_terms_of_W_zero
- \+ *lemma* aeval_witt_polynomial
- \+ *lemma* bind₁_X_in_terms_of_W_witt_polynomial
- \+ *lemma* bind₁_witt_polynomial_X_in_terms_of_W
- \+ *lemma* constant_coeff_X_in_terms_of_W
- \+ *lemma* constant_coeff_witt_polynomial
- \+ *lemma* map_witt_polynomial
- \+ *lemma* witt_polynomial_eq_sum_C_mul_X_pow
- \+ *lemma* witt_polynomial_one
- \+ *lemma* witt_polynomial_vars
- \+ *lemma* witt_polynomial_vars_subset
- \+ *lemma* witt_polynomial_zero
- \+ *lemma* witt_polynomial_zmod_self



## [2020-09-25 14:53:58](https://github.com/leanprover-community/mathlib/commit/565efec)
chore(data/real/ennreal): 3 lemmas stating `∞ / b = ∞` ([#4248](https://github.com/leanprover-community/mathlib/pull/4248))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.top_div_coe
- \+ *lemma* ennreal.top_div_of_lt_top
- \+ *lemma* ennreal.top_div_of_ne_top



## [2020-09-25 14:53:56](https://github.com/leanprover-community/mathlib/commit/1029974)
feat(*): finite rings with char = card = n are isomorphic to zmod n ([#4234](https://github.com/leanprover-community/mathlib/pull/4234))
From the Witt vector project
I've made use of the opportunity to remove some unused arguments,
and to clean up some code by using namespacing and such.
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.cast_card_eq_zero
- \+ *lemma* char_p_of_ne_zero
- \+ *lemma* char_p_of_prime_pow_injective

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_ring_hom_inj_iff

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.eq_univ_of_card
- \+ *lemma* fintype.bijective_iff_injective_and_card
- \+ *lemma* fintype.bijective_iff_surjective_and_card
- \+/\- *lemma* fintype.card_eq_one_iff
- \+/\- *def* fintype.card_eq_zero_equiv_equiv_pempty
- \+/\- *lemma* fintype.card_eq_zero_iff
- \+/\- *lemma* fintype.card_le_of_injective
- \+/\- *lemma* fintype.card_le_one_iff
- \+/\- *lemma* fintype.card_le_one_iff_subsingleton
- \+/\- *lemma* fintype.card_pos_iff
- \+/\- *lemma* fintype.exists_ne_of_one_lt_card
- \+/\- *lemma* fintype.exists_pair_of_one_lt_card
- \+/\- *lemma* fintype.injective_iff_bijective
- \+/\- *lemma* fintype.injective_iff_surjective
- \+/\- *lemma* fintype.injective_iff_surjective_of_equiv
- \+ *lemma* fintype.nonempty_equiv_of_card_eq
- \+/\- *lemma* fintype.one_lt_card_iff_nontrivial
- \+/\- *lemma* fintype.surjective_iff_bijective

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_hom_bijective
- \+ *lemma* zmod.cast_hom_injective
- \+/\- *lemma* zmod.ring_hom_eq_of_ker_eq
- \+/\- *lemma* zmod.ring_hom_surjective



## [2020-09-25 14:53:54](https://github.com/leanprover-community/mathlib/commit/aee16bd)
feat(data/mv_polynomial/basic): counit ([#4205](https://github.com/leanprover-community/mathlib/pull/4205))
From the Witt vector project
#### Estimated changes
Added src/data/mv_polynomial/counit.lean
- \+ *lemma* mv_polynomial.acounit_C
- \+ *lemma* mv_polynomial.acounit_X
- \+ *lemma* mv_polynomial.acounit_surjective
- \+ *lemma* mv_polynomial.counit_C
- \+ *lemma* mv_polynomial.counit_X
- \+ *lemma* mv_polynomial.counit_nat_C
- \+ *lemma* mv_polynomial.counit_nat_X
- \+ *lemma* mv_polynomial.counit_nat_surjective
- \+ *lemma* mv_polynomial.counit_surjective



## [2020-09-25 14:53:52](https://github.com/leanprover-community/mathlib/commit/5deb96d)
feat(data/mv_polynomial/funext): function extensionality for polynomials ([#4196](https://github.com/leanprover-community/mathlib/pull/4196))
over infinite integral domains
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.trans_apply

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.C_inj
- \+/\- *lemma* mv_polynomial.C_injective

Modified src/data/mv_polynomial/equiv.lean
- \+ *lemma* mv_polynomial.fin_succ_equiv_apply
- \+ *lemma* mv_polynomial.fin_succ_equiv_eq

Added src/data/mv_polynomial/funext.lean
- \+ *lemma* mv_polynomial.funext
- \+ *lemma* mv_polynomial.funext_iff

Modified src/data/polynomial/monomial.lean


Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.funext
- \+ *lemma* polynomial.zero_of_eval_zero

Modified src/logic/function/basic.lean
- \+ *def* function.extend
- \+ *lemma* function.extend_apply
- \+ *lemma* function.extend_comp
- \+ *lemma* function.extend_def



## [2020-09-25 12:54:20](https://github.com/leanprover-community/mathlib/commit/680f877)
feat(data/rat/basic): coe_int_div, coe_nat_div ([#4233](https://github.com/leanprover-community/mathlib/pull/4233))
Snippet from the Witt project
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.coe_int_div
- \+ *lemma* rat.coe_int_div_self
- \+ *lemma* rat.coe_nat_div
- \+ *lemma* rat.coe_nat_div_self



## [2020-09-25 12:54:18](https://github.com/leanprover-community/mathlib/commit/9591d43)
feat(data/*): lemmas on division of polynomials by constant polynomials ([#4206](https://github.com/leanprover-community/mathlib/pull/4206))
From the Witt vector project
We provide a specialized version for polynomials over zmod n,
which turns out to be convenient in practice.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.C_dvd_iff_dvd_coeff
- \+ *lemma* mv_polynomial.C_dvd_iff_map_hom_eq_zero

Added src/data/zmod/polynomial.lean
- \+ *lemma* mv_polynomial.C_dvd_iff_zmod



## [2020-09-25 12:54:16](https://github.com/leanprover-community/mathlib/commit/c7d818c)
feat(data/mv_polynomial/variables): vars_bind₁ and friends ([#4204](https://github.com/leanprover-community/mathlib/pull/4204))
From the Witt vector project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/rename.lean
- \- *lemma* mv_polynomial.total_degree_rename_le

Modified src/data/mv_polynomial/variables.lean
- \+/\- *lemma* mv_polynomial.aeval_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.degrees_rename
- \+ *lemma* mv_polynomial.eval₂_hom_congr'
- \+/\- *lemma* mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.total_degree_rename_le
- \+/\- *lemma* mv_polynomial.vars_C
- \+ *lemma* mv_polynomial.vars_bind₁
- \+/\- *lemma* mv_polynomial.vars_monomial
- \+ *lemma* mv_polynomial.vars_rename



## [2020-09-25 10:07:16](https://github.com/leanprover-community/mathlib/commit/2313602)
feat(order/bounded_lattice): custom recursors for with_bot/with_top ([#4245](https://github.com/leanprover-community/mathlib/pull/4245))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *def* with_bot.rec_bot_coe
- \+ *def* with_top.rec_top_coe



## [2020-09-25 10:07:14](https://github.com/leanprover-community/mathlib/commit/f43bd45)
fix(tactic/lint/simp): only head-beta reduce, don't whnf ([#4237](https://github.com/leanprover-community/mathlib/pull/4237))
This is necessary to accept simp lemmas like `injective reverse`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *theorem* finset.ne_empty_of_mem

Modified src/data/list/basic.lean
- \+/\- *theorem* list.cons_injective
- \+/\- *lemma* list.length_injective
- \+/\- *lemma* list.length_injective_iff
- \+/\- *theorem* list.reverse_injective

Modified src/tactic/lint/simp.lean


Modified test/lint_simp_var_head.lean




## [2020-09-25 10:07:12](https://github.com/leanprover-community/mathlib/commit/5da451b)
feat(data/mv_polynomial/expand): replace variables by a power ([#4197](https://github.com/leanprover-community/mathlib/pull/4197))
From the Witt vectors project.
#### Estimated changes
Added src/data/mv_polynomial/expand.lean
- \+ *lemma* mv_polynomial.expand_C
- \+ *lemma* mv_polynomial.expand_X
- \+ *lemma* mv_polynomial.expand_bind₁
- \+ *lemma* mv_polynomial.expand_comp_bind₁
- \+ *lemma* mv_polynomial.expand_monomial
- \+ *lemma* mv_polynomial.expand_one
- \+ *lemma* mv_polynomial.expand_one_apply
- \+ *lemma* mv_polynomial.map_expand
- \+ *lemma* mv_polynomial.rename_comp_expand
- \+ *lemma* mv_polynomial.rename_expand



## [2020-09-25 09:07:07](https://github.com/leanprover-community/mathlib/commit/b6154d9)
feat(category_theory/limits): small lemmas ([#4251](https://github.com/leanprover-community/mathlib/pull/4251))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.limit.iso_limit_cone
- \+ *lemma* category_theory.limits.limit.iso_limit_cone_hom_π
- \+ *lemma* category_theory.limits.limit.iso_limit_cone_inv_π
- \+ *lemma* category_theory.limits.limit.pre_eq



## [2020-09-25 08:21:16](https://github.com/leanprover-community/mathlib/commit/40f1370)
chore(measure_theory/bochner_integration): rename/add lemmas, fix docstring ([#4249](https://github.com/leanprover-community/mathlib/pull/4249))
* add `integral_nonneg` assuming `0 ≤ f`;
* rename `integral_nonpos_of_nonpos_ae` to `integral_nonpos_of_ae`;
* add `integral_nonpos` assuming `f ≤ 0`;
* rename `integral_mono` to `integral_mono_ae`;
* add `integral_mono` assuming `f ≤ g`;
* (partially?) fix module docstring.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_mono
- \+ *lemma* measure_theory.integral_mono_ae
- \+ *lemma* measure_theory.integral_nonneg
- \+ *lemma* measure_theory.integral_nonpos
- \+ *lemma* measure_theory.integral_nonpos_of_ae
- \- *lemma* measure_theory.integral_nonpos_of_nonpos_ae

Modified src/measure_theory/set_integral.lean




## [2020-09-25 06:57:20](https://github.com/leanprover-community/mathlib/commit/143c074)
feat(category_theory/cofinal): cofinal functors ([#4218](https://github.com/leanprover-community/mathlib/pull/4218))
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+ *lemma* category_theory.is_preconnected_induction

Modified src/category_theory/isomorphism.lean


Added src/category_theory/limits/cofinal.lean
- \+ *def* category_theory.cofinal.cocones_equiv
- \+ *def* category_theory.cofinal.colimit_cocone_comp
- \+ *lemma* category_theory.cofinal.colimit_cocone_comp_aux
- \+ *def* category_theory.cofinal.colimit_cocone_of_comp
- \+ *def* category_theory.cofinal.colimit_iso'
- \+ *def* category_theory.cofinal.colimit_iso
- \+ *lemma* category_theory.cofinal.colimit_pre_is_iso_aux
- \+ *def* category_theory.cofinal.extend_cocone
- \+ *lemma* category_theory.cofinal.has_colimit_of_comp
- \+ *def* category_theory.cofinal.hom_to_lift
- \+ *lemma* category_theory.cofinal.induction
- \+ *def* category_theory.cofinal.is_colimit_extend_cocone_equiv
- \+ *def* category_theory.cofinal.is_colimit_whisker_equiv
- \+ *def* category_theory.cofinal.lift
- \+ *def* category_theory.cofinal

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.colimit.iso_colimit_cocone
- \+ *lemma* category_theory.limits.colimit.iso_colimit_cocone_ι_hom
- \+ *lemma* category_theory.limits.colimit.iso_colimit_cocone_ι_inv
- \+ *lemma* category_theory.limits.colimit.pre_eq
- \+ *lemma* category_theory.limits.is_colimit.of_cocone_equiv_apply_desc
- \+ *lemma* category_theory.limits.is_colimit.of_cocone_equiv_symm_apply_desc

Modified src/category_theory/over.lean
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under

Modified src/category_theory/punit.lean




## [2020-09-25 05:46:05](https://github.com/leanprover-community/mathlib/commit/dda82fc)
chore(*): add missing copyright, cleanup imports ([#4229](https://github.com/leanprover-community/mathlib/pull/4229))
Add missing copyright, avoid use of `import tactic`, and put each `import` statement on a separate line, for easier analysis via grep.
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean


Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/imo/imo1988_q6.lean


Modified src/data/holor.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/group_theory/semidirect_product.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/multiplicity.lean


Modified src/tactic/derive_fintype.lean


Modified test/tauto.lean


Modified test/unfold_cases.lean




## [2020-09-25 00:12:04](https://github.com/leanprover-community/mathlib/commit/f9a667d)
refactor(algebra/group_power, data/nat/basic): remove redundant lemmas ([#4243](https://github.com/leanprover-community/mathlib/pull/4243))
This removes lemmas about `pow` on `nat` which are redundant
with more general versions in the root namespace.
One notable removal is `nat.pow_succ`; use `pow_succ'` instead.
In order that the general versions are available already in `data.nat.basic`,
many lemmas from `algebra.group_power.lemmas` have been moved to
`algebra.group_power.basic` (basically as many as possible without adding imports).
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified archive/miu_language/decision_suf.lean


Modified archive/sensitivity.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.prod_nat_pow

Modified src/algebra/char_p.lean


Modified src/algebra/group_power/basic.lean
- \+ *lemma* abs_neg_one_pow
- \+ *theorem* add_monoid_hom.map_nsmul
- \+ *theorem* bit0_nsmul
- \+ *theorem* bit1_nsmul
- \+ *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \+ *theorem* canonically_ordered_semiring.pow_le_one
- \+ *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \+ *theorem* canonically_ordered_semiring.pow_pos
- \+ *lemma* commute.gpow_gpow
- \+ *theorem* commute.gpow_gpow_self
- \+ *lemma* commute.gpow_left
- \+ *lemma* commute.gpow_right
- \+ *theorem* commute.gpow_self
- \+ *theorem* commute.mul_gpow
- \+ *lemma* commute.mul_pow
- \+ *theorem* commute.self_gpow
- \+ *lemma* dvd_pow
- \+ *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \+ *theorem* gpow_coe_nat
- \+ *theorem* gpow_neg
- \+ *theorem* gpow_neg_one
- \+ *theorem* gpow_neg_succ_of_nat
- \+ *theorem* gpow_of_nat
- \+ *theorem* gpow_one
- \+ *theorem* gpow_zero
- \+ *theorem* gsmul_add
- \+ *theorem* gsmul_coe_nat
- \+ *theorem* gsmul_neg
- \+ *theorem* gsmul_neg_succ_of_nat
- \+ *theorem* gsmul_of_nat
- \+ *theorem* gsmul_sub
- \+ *theorem* gsmul_zero
- \+ *theorem* inv_gpow
- \+ *theorem* inv_pow
- \+ *theorem* is_add_monoid_hom.map_nsmul
- \+ *theorem* is_monoid_hom.map_pow
- \+ *lemma* ite_pow
- \+ *lemma* lt_of_pow_lt_pow
- \+ *theorem* monoid_hom.map_pow
- \+ *theorem* mul_gpow
- \+ *lemma* mul_gpow_neg_one
- \+ *theorem* mul_nsmul'
- \+ *theorem* mul_nsmul
- \+ *theorem* mul_pow
- \+ *theorem* neg_gsmul
- \+ *theorem* neg_nsmul
- \+ *theorem* neg_one_gsmul
- \+ *theorem* neg_one_pow_eq_or
- \+ *theorem* neg_pow
- \+ *lemma* neg_square
- \+ *theorem* nsmul_add
- \+ *theorem* nsmul_add_comm
- \+ *theorem* nsmul_add_sub_nsmul
- \+ *theorem* nsmul_le_nsmul
- \+ *lemma* nsmul_le_nsmul_of_le_right
- \+ *theorem* nsmul_neg_comm
- \+ *theorem* nsmul_nonneg
- \+ *theorem* nsmul_sub
- \+ *theorem* nsmul_zero
- \+ *lemma* of_add_gsmul
- \+ *lemma* of_add_nsmul
- \+ *theorem* one_gpow
- \+ *theorem* one_gsmul
- \+ *theorem* one_le_pow_of_one_le
- \+ *theorem* one_nsmul
- \+ *theorem* one_pow
- \+ *lemma* pow_abs
- \+ *theorem* pow_bit0
- \+ *theorem* pow_bit1
- \+ *lemma* pow_boole
- \+ *lemma* pow_dvd_pow
- \+ *theorem* pow_dvd_pow_of_dvd
- \+ *theorem* pow_eq_zero
- \+ *theorem* pow_inv_comm
- \+ *lemma* pow_ite
- \+ *theorem* pow_le_pow
- \+ *lemma* pow_le_pow_of_le_left
- \+ *theorem* pow_left_inj
- \+ *lemma* pow_lt_pow
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_mul'
- \+ *theorem* pow_mul
- \+ *theorem* pow_mul_comm
- \+ *theorem* pow_mul_pow_sub
- \+ *theorem* pow_ne_zero
- \+ *theorem* pow_nonneg
- \+ *theorem* pow_one
- \+ *theorem* pow_pos
- \+ *theorem* pow_sub
- \+ *theorem* pow_sub_mul_pow
- \+ *theorem* pow_two_nonneg
- \+ *theorem* pow_two_pos_of_ne_zero
- \+ *lemma* pow_two_sub_pow_two
- \+ *lemma* ring_hom.map_pow
- \+ *lemma* semiconj_by.gpow_right
- \+ *theorem* sq_sub_sq
- \+ *theorem* sub_nsmul_nsmul_add
- \+ *theorem* zero_gsmul
- \+ *lemma* zero_pow

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* abs_neg_one_pow
- \- *theorem* add_monoid_hom.map_nsmul
- \- *theorem* bit0_nsmul
- \- *theorem* bit1_nsmul
- \- *theorem* canonically_ordered_semiring.one_le_pow_of_one_le
- \- *theorem* canonically_ordered_semiring.pow_le_one
- \- *lemma* canonically_ordered_semiring.pow_le_pow_of_le_left
- \- *theorem* canonically_ordered_semiring.pow_pos
- \- *lemma* commute.gpow_gpow
- \- *theorem* commute.gpow_gpow_self
- \- *lemma* commute.gpow_left
- \- *lemma* commute.gpow_right
- \- *theorem* commute.gpow_self
- \- *theorem* commute.mul_gpow
- \- *lemma* commute.mul_pow
- \- *theorem* commute.self_gpow
- \- *lemma* dvd_pow
- \- *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \- *theorem* gpow_coe_nat
- \- *theorem* gpow_neg
- \- *theorem* gpow_neg_one
- \- *theorem* gpow_neg_succ_of_nat
- \- *theorem* gpow_of_nat
- \- *theorem* gpow_one
- \- *theorem* gpow_zero
- \- *theorem* gsmul_add
- \- *theorem* gsmul_coe_nat
- \- *theorem* gsmul_neg
- \- *theorem* gsmul_neg_succ_of_nat
- \- *theorem* gsmul_of_nat
- \- *theorem* gsmul_sub
- \- *theorem* gsmul_zero
- \- *theorem* inv_gpow
- \- *theorem* inv_pow
- \- *theorem* is_add_monoid_hom.map_nsmul
- \- *theorem* is_monoid_hom.map_pow
- \- *lemma* ite_pow
- \- *lemma* lt_of_pow_lt_pow
- \- *theorem* monoid_hom.map_pow
- \- *theorem* mul_gpow
- \- *lemma* mul_gpow_neg_one
- \- *theorem* mul_nsmul'
- \- *theorem* mul_nsmul
- \- *theorem* mul_pow
- \- *theorem* neg_gsmul
- \- *theorem* neg_nsmul
- \- *theorem* neg_one_gsmul
- \- *theorem* neg_one_pow_eq_or
- \- *theorem* neg_pow
- \- *lemma* neg_square
- \- *theorem* nsmul_add
- \- *theorem* nsmul_add_comm
- \- *theorem* nsmul_add_sub_nsmul
- \- *theorem* nsmul_le_nsmul
- \- *lemma* nsmul_le_nsmul_of_le_right
- \- *theorem* nsmul_neg_comm
- \- *theorem* nsmul_nonneg
- \- *theorem* nsmul_sub
- \- *theorem* nsmul_zero
- \- *lemma* of_add_gsmul
- \- *lemma* of_add_nsmul
- \- *theorem* one_gpow
- \- *theorem* one_gsmul
- \- *theorem* one_le_pow_of_one_le
- \- *theorem* one_nsmul
- \- *theorem* one_pow
- \- *lemma* pow_abs
- \- *theorem* pow_bit0
- \- *theorem* pow_bit1
- \- *lemma* pow_boole
- \- *lemma* pow_dvd_pow
- \- *theorem* pow_dvd_pow_of_dvd
- \- *theorem* pow_eq_zero
- \- *theorem* pow_inv_comm
- \- *lemma* pow_ite
- \- *theorem* pow_le_pow
- \- *lemma* pow_le_pow_of_le_left
- \- *theorem* pow_left_inj
- \- *lemma* pow_lt_pow
- \- *theorem* pow_lt_pow_of_lt_left
- \- *theorem* pow_mul'
- \- *theorem* pow_mul
- \- *theorem* pow_mul_comm
- \- *theorem* pow_mul_pow_sub
- \- *theorem* pow_ne_zero
- \- *theorem* pow_nonneg
- \- *theorem* pow_one
- \- *theorem* pow_pos
- \- *theorem* pow_sub
- \- *theorem* pow_sub_mul_pow
- \- *theorem* pow_two_nonneg
- \- *theorem* pow_two_pos_of_ne_zero
- \- *lemma* pow_two_sub_pow_two
- \- *lemma* ring_hom.map_pow
- \- *lemma* semiconj_by.gpow_right
- \- *theorem* sq_sub_sq
- \- *theorem* sub_nsmul_nsmul_add
- \- *theorem* zero_gsmul
- \- *lemma* zero_pow

Modified src/analysis/specific_limits.lean


Modified src/computability/primrec.lean


Modified src/data/bitvec/basic.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean
- \- *theorem* nat.mul_pow
- \- *lemma* nat.one_pow
- \- *theorem* nat.pos_pow_of_pos
- \- *theorem* nat.pow_add
- \- *theorem* nat.pow_dvd_pow
- \- *theorem* nat.pow_dvd_pow_of_dvd
- \- *lemma* nat.pow_eq_mul_pow_sub
- \- *theorem* nat.pow_le_pow_of_le_left
- \- *theorem* nat.pow_one
- \- *theorem* nat.pow_pos
- \- *lemma* nat.pow_succ
- \- *theorem* nat.pow_two
- \- *lemma* nat.pow_zero
- \- *theorem* nat.zero_pow

Modified src/data/nat/choose/sum.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/fact.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/log.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/pnat/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/separable.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/basic.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/multiplicity.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/tactic/ring_exp.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-09-24 22:51:18](https://github.com/leanprover-community/mathlib/commit/46bf8ca)
fix(topology/path_connected): avoid a slow use of `continuity` ([#4244](https://github.com/leanprover-community/mathlib/pull/4244))
This corrects the timeout experienced by @Nicknamen in [#3641](https://github.com/leanprover-community/mathlib/pull/3641). See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.233641/near/211107487
#### Estimated changes
Modified src/topology/path_connected.lean




## [2020-09-24 20:51:05](https://github.com/leanprover-community/mathlib/commit/675f5d4)
feat(algebra/char_p): nontrivial_of_char_ne_one ([#4232](https://github.com/leanprover-community/mathlib/pull/4232))
Also renames `false_of_nonzero_of_char_one` to `false_of_nontrivial_of_char_one`
Snippet from the Witt project
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.false_of_nontrivial_of_char_one
- \- *lemma* char_p.false_of_nonzero_of_char_one
- \+ *lemma* char_p.nontrivial_of_char_ne_one

Modified src/logic/nontrivial.lean
- \+ *lemma* false_of_nontrivial_of_subsingleton



## [2020-09-24 19:43:34](https://github.com/leanprover-community/mathlib/commit/5eedf32)
docs(data/complex/exponential): docstring for de Moivre ([#4242](https://github.com/leanprover-community/mathlib/pull/4242))
#### Estimated changes
Modified src/data/complex/exponential.lean




## [2020-09-24 17:38:37](https://github.com/leanprover-community/mathlib/commit/02ca5e2)
fix(.github/workflows/add_label_from_review.yml): fix label removal ([#4240](https://github.com/leanprover-community/mathlib/pull/4240))
The API calls were referencing the wrong field, see for example https://github.com/leanprover-community/mathlib/runs/1161014126?check_suite_focus=true#step:7:3
#### Estimated changes
Modified .github/workflows/add_label_from_review.yml




## [2020-09-24 17:38:35](https://github.com/leanprover-community/mathlib/commit/d670746)
feat(category_theory/monad/algebra): Add faithful instances.  ([#4227](https://github.com/leanprover-community/mathlib/pull/4227))
Adds a `faithful` instance for the forgetful functors from the Eilenberg Moore category associated to a (co)monad.
#### Estimated changes
Modified src/category_theory/monad/algebra.lean




## [2020-09-24 17:38:32](https://github.com/leanprover-community/mathlib/commit/5c31dea)
feat(field_theory): intermediate fields ([#4181](https://github.com/leanprover-community/mathlib/pull/4181))
Define `intermediate_field K L` as a structure extending `subalgebra K L` and `subfield L`.
This definition required some changes in `subalgebra`, which I added in [#4180](https://github.com/leanprover-community/mathlib/pull/4180).
#### Estimated changes
Added src/field_theory/intermediate_field.lean
- \+ *theorem* intermediate_field.add_mem
- \+ *theorem* intermediate_field.algebra_map_mem
- \+ *lemma* intermediate_field.coe_add
- \+ *lemma* intermediate_field.coe_int_mem
- \+ *lemma* intermediate_field.coe_inv
- \+ *lemma* intermediate_field.coe_mul
- \+ *lemma* intermediate_field.coe_neg
- \+ *lemma* intermediate_field.coe_one
- \+ *lemma* intermediate_field.coe_to_subalgebra
- \+ *lemma* intermediate_field.coe_to_subfield
- \+ *theorem* intermediate_field.coe_val
- \+ *lemma* intermediate_field.coe_zero
- \+ *theorem* intermediate_field.div_mem
- \+ *theorem* intermediate_field.ext'
- \+ *theorem* intermediate_field.ext
- \+ *lemma* intermediate_field.field_range_le
- \+ *lemma* intermediate_field.gsmul_mem
- \+ *theorem* intermediate_field.inv_mem
- \+ *lemma* intermediate_field.list_prod_mem
- \+ *lemma* intermediate_field.list_sum_mem
- \+ *def* intermediate_field.map
- \+ *lemma* intermediate_field.mem_coe
- \+ *lemma* intermediate_field.mem_mk
- \+ *lemma* intermediate_field.mem_to_subalgebra
- \+ *lemma* intermediate_field.mem_to_subfield
- \+ *theorem* intermediate_field.mul_mem
- \+ *lemma* intermediate_field.multiset_prod_mem
- \+ *lemma* intermediate_field.multiset_sum_mem
- \+ *theorem* intermediate_field.neg_mem
- \+ *theorem* intermediate_field.one_mem
- \+ *lemma* intermediate_field.pow_mem
- \+ *lemma* intermediate_field.prod_mem
- \+ *lemma* intermediate_field.set_range_subset
- \+ *theorem* intermediate_field.smul_mem
- \+ *theorem* intermediate_field.sub_mem
- \+ *lemma* intermediate_field.sum_mem
- \+ *lemma* intermediate_field.to_subalgebra_injective
- \+ *def* intermediate_field.val
- \+ *lemma* intermediate_field.val_mk
- \+ *theorem* intermediate_field.zero_mem
- \+ *def* subalgebra.to_intermediate_field
- \+ *def* subfield.to_intermediate_field

Modified src/field_theory/subfield.lean
- \+ *theorem* subfield.sub_mem

Modified src/ring_theory/algebra_tower.lean




## [2020-09-24 17:38:30](https://github.com/leanprover-community/mathlib/commit/e23b97e)
feat(ring_theory/polynomial): decomposing the kernel of an endomorphism polynomial ([#4174](https://github.com/leanprover-community/mathlib/pull/4174))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.map_bit0
- \+ *lemma* ring_hom.map_bit1

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.aeval_X_pow
- \+ *lemma* polynomial.aeval_add
- \+ *lemma* polynomial.aeval_bit0
- \+ *lemma* polynomial.aeval_bit1
- \+ *lemma* polynomial.aeval_monomial
- \+ *lemma* polynomial.aeval_mul
- \+ *lemma* polynomial.aeval_nat_cast
- \+ *lemma* polynomial.aeval_one
- \+ *lemma* polynomial.aeval_zero

Modified src/data/polynomial/eval.lean
- \- *lemma* polynomial.eval₂_endomorphism_algebra_map

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.mul_apply

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_hom.map_bit0
- \+ *lemma* alg_hom.map_bit1

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial.disjoint_ker_aeval_of_coprime
- \+ *lemma* polynomial.sup_aeval_range_eq_top_of_coprime
- \+ *lemma* polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
- \+ *lemma* polynomial.sup_ker_aeval_le_ker_aeval_mul



## [2020-09-24 16:49:35](https://github.com/leanprover-community/mathlib/commit/03894df)
feat(category_theory/limits/creates): Add has_(co)limit defs ([#4239](https://github.com/leanprover-community/mathlib/pull/4239))
This PR adds four `def`s:
1. `has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape` 
2. `has_limits_of_has_limits_creates_limits`
3. `has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape`
4. `has_colimits_of_has_colimits_creates_colimits`
These show that a category `C` has (co)limits (of a given shape) given a functor `F : C ⥤ D` which creates (co)limits (of the given shape) where `D` has (co)limits (of the given shape).
See the associated zulip discussion: 
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/has_limits.20of.20has_limits.20and.20creates_limits/near/211083395
#### Estimated changes
Modified src/category_theory/limits/creates.lean
- \+ *lemma* category_theory.has_colimits_of_has_colimits_creates_colimits
- \+ *lemma* category_theory.has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape
- \+ *lemma* category_theory.has_limits_of_has_limits_creates_limits
- \+ *lemma* category_theory.has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape



## [2020-09-24 14:02:39](https://github.com/leanprover-community/mathlib/commit/03775fb)
chore(data/mv_polynomial): aeval_rename -> aeval_id_rename ([#4230](https://github.com/leanprover-community/mathlib/pull/4230))
`aeval_rename` was not general enough, so it is renamed to
`aeval_id_rename`.
Also: state and prove the more general version of `aeval_rename`.
#### Estimated changes
Modified src/data/mv_polynomial/monad.lean
- \+ *lemma* mv_polynomial.aeval_id_rename
- \- *lemma* mv_polynomial.aeval_rename

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* mv_polynomial.aeval_rename



## [2020-09-24 10:39:14](https://github.com/leanprover-community/mathlib/commit/3484e8b)
fix(data/mv_polynomial): fix doc strings ([#4219](https://github.com/leanprover-community/mathlib/pull/4219))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/comap.lean


Modified src/data/mv_polynomial/comm_ring.lean


Modified src/data/mv_polynomial/equiv.lean


Modified src/data/mv_polynomial/pderivative.lean


Modified src/data/mv_polynomial/rename.lean


Modified src/data/mv_polynomial/variables.lean




## [2020-09-24 10:39:13](https://github.com/leanprover-community/mathlib/commit/f0713cb)
refactor(measure_theory/simple_func_dense): split monolithic proof ([#4199](https://github.com/leanprover-community/mathlib/pull/4199))
In the new proof the sequence of approximating functions has a simpler description: `N`-th function
sends `x` to the point `e k` which is the nearest to `f x` among the points `e 0`, ..., `e N`, where `e n`
is a dense sequence such that `e 0 = 0`.
#### Estimated changes
Modified src/data/list/min_max.lean


Modified src/data/nat/basic.lean
- \+ *theorem* nat.range_cases_on
- \+ *theorem* nat.range_of_succ
- \+ *theorem* nat.range_rec
- \+ *theorem* nat.zero_union_range_succ

Modified src/data/set/basic.lean
- \+/\- *lemma* set.sep_set_of
- \+ *lemma* set.set_of_and
- \+ *lemma* set.set_of_or

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.tendsto_integral_approx_on_univ

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_lt'
- \+ *lemma* is_measurable_lt
- \+/\- *lemma* measurable.const_mul
- \+/\- *lemma* measurable.const_smul
- \+/\- *lemma* measurable.mul_const
- \+ *lemma* measurable_edist_left
- \+ *lemma* measurable_edist_right

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.simple_func.measurable_bind

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.add'
- \+ *lemma* measure_theory.integrable.sub'

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.ae_eq_bot

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func.approx_on_comp
- \+ *lemma* measure_theory.simple_func.approx_on_mem
- \+ *lemma* measure_theory.simple_func.approx_on_zero
- \+ *lemma* measure_theory.simple_func.edist_approx_on_le
- \+ *lemma* measure_theory.simple_func.edist_approx_on_y0_le
- \+ *lemma* measure_theory.simple_func.edist_nearest_pt_le
- \+ *lemma* measure_theory.simple_func.integrable_approx_on
- \+ *lemma* measure_theory.simple_func.integrable_approx_on_univ
- \+ *lemma* measure_theory.simple_func.nearest_pt_ind_le
- \+ *lemma* measure_theory.simple_func.nearest_pt_ind_succ
- \+ *lemma* measure_theory.simple_func.nearest_pt_ind_zero
- \+ *lemma* measure_theory.simple_func.nearest_pt_zero
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_l1_edist
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1_edist
- \+ *lemma* measure_theory.simple_func.tendsto_nearest_pt
- \- *lemma* measure_theory.simple_func_sequence_tendsto'
- \- *lemma* measure_theory.simple_func_sequence_tendsto

Modified src/topology/bases.lean
- \+/\- *lemma* topological_space.dense_seq_dense



## [2020-09-24 08:37:51](https://github.com/leanprover-community/mathlib/commit/ba8fa0f)
feat(logic/embedding): use simps ([#4169](https://github.com/leanprover-community/mathlib/pull/4169))
Some lemmas are slightly reformulated, and have a worse name. But they are (almost) never typed explicitly, since they are simp lemmas (even the occurrences in other files probably came from `squeeze_simp`).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/nat_antidiagonal.lean


Modified src/data/finset/nat_antidiagonal.lean


Modified src/logic/embedding.lean
- \+/\- *lemma* equiv.refl_to_embedding
- \- *theorem* equiv.to_embedding_coe_fn
- \- *lemma* function.embedding.coe_image
- \- *lemma* function.embedding.coe_sigma_map
- \- *lemma* function.embedding.coe_sigma_mk
- \- *theorem* function.embedding.refl_apply
- \+/\- *def* function.embedding.sigma_map
- \+/\- *def* function.embedding.sigma_mk
- \- *theorem* function.embedding.trans_apply
- \- *lemma* mul_left_embedding_apply
- \- *lemma* mul_right_embedding_apply
- \- *lemma* set.coe_embedding_of_subset_apply
- \+/\- *def* set.embedding_of_subset
- \- *lemma* set.embedding_of_subset_apply_mk

Modified src/measure_theory/haar_measure.lean




## [2020-09-24 06:54:53](https://github.com/leanprover-community/mathlib/commit/5e934cd)
chore(*): cleanup imports, split off data/finset/preimage from data/set/finite ([#4221](https://github.com/leanprover-community/mathlib/pull/4221))
Mostly this consists of moving some content from `data.set.finite` to `data.finset.preimage`, in order to reduce imports in `data.set.finite`.
#### Estimated changes
Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/data/finset/default.lean


Added src/data/finset/preimage.lean
- \+ *lemma* finset.coe_preimage
- \+ *lemma* finset.image_preimage
- \+ *lemma* finset.image_preimage_of_bij
- \+ *lemma* finset.image_subset_iff_subset_preimage
- \+ *lemma* finset.map_subset_iff_subset_preimage
- \+ *lemma* finset.mem_preimage
- \+ *lemma* finset.monotone_preimage
- \+ *lemma* finset.prod_preimage'
- \+ *lemma* finset.prod_preimage
- \+ *lemma* finset.prod_preimage_of_bij
- \+ *lemma* finset.sigma_image_fst_preimage_mk
- \+ *lemma* finset.sigma_preimage_mk
- \+ *lemma* finset.sigma_preimage_mk_of_subset

Modified src/data/finsupp/basic.lean


Modified src/data/set/finite.lean
- \- *lemma* finset.coe_preimage
- \- *lemma* finset.image_preimage
- \- *lemma* finset.image_preimage_of_bij
- \- *lemma* finset.image_subset_iff_subset_preimage
- \- *lemma* finset.map_subset_iff_subset_preimage
- \- *lemma* finset.mem_preimage
- \- *lemma* finset.monotone_preimage
- \- *lemma* finset.prod_preimage'
- \- *lemma* finset.prod_preimage
- \- *lemma* finset.prod_preimage_of_bij
- \- *lemma* finset.sigma_image_fst_preimage_mk
- \- *lemma* finset.sigma_preimage_mk
- \- *lemma* finset.sigma_preimage_mk_of_subset

Modified src/order/filter/at_top_bot.lean


Modified src/topology/bases.lean




## [2020-09-24 05:52:22](https://github.com/leanprover-community/mathlib/commit/ed07cac)
feat(data/mv_polynomial/rename): coeff_rename ([#4203](https://github.com/leanprover-community/mathlib/pull/4203))
Also, use the opportunity to use R as variable for the coefficient ring
throughout the file.
#### Estimated changes
Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* mv_polynomial.coeff_rename_eq_zero
- \+ *lemma* mv_polynomial.coeff_rename_map_domain
- \+ *lemma* mv_polynomial.coeff_rename_ne_zero
- \+/\- *lemma* mv_polynomial.eval_rename_prodmk
- \+/\- *lemma* mv_polynomial.eval₂_cast_comp
- \+/\- *lemma* mv_polynomial.eval₂_rename_prodmk
- \+/\- *theorem* mv_polynomial.exists_fin_rename
- \+/\- *theorem* mv_polynomial.exists_finset_rename
- \+/\- *lemma* mv_polynomial.map_rename
- \+/\- *def* mv_polynomial.rename
- \+/\- *lemma* mv_polynomial.rename_C
- \+/\- *lemma* mv_polynomial.rename_X
- \+/\- *lemma* mv_polynomial.rename_eq
- \+/\- *lemma* mv_polynomial.rename_eval₂
- \+/\- *lemma* mv_polynomial.rename_id
- \+/\- *lemma* mv_polynomial.rename_injective
- \+/\- *lemma* mv_polynomial.rename_monomial
- \+/\- *lemma* mv_polynomial.rename_prodmk_eval₂
- \+/\- *lemma* mv_polynomial.rename_rename
- \+/\- *lemma* mv_polynomial.total_degree_rename_le



## [2020-09-24 03:33:52](https://github.com/leanprover-community/mathlib/commit/ef18740)
feat(linear_algebra/eigenspace): generalized eigenvectors span the entire space ([#4111](https://github.com/leanprover-community/mathlib/pull/4111))
#### Estimated changes
Modified docs/references.bib


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.ker_restrict

Modified src/linear_algebra/eigenspace.lean
- \+/\- *theorem* module.End.aeval_apply_of_has_eigenvector
- \+/\- *def* module.End.eigenspace
- \+/\- *lemma* module.End.eigenspace_aeval_polynomial_degree_1
- \+/\- *lemma* module.End.eigenspace_div
- \+/\- *lemma* module.End.eigenspace_le_generalized_eigenspace
- \+/\- *lemma* module.End.eigenvectors_linear_independent
- \+/\- *lemma* module.End.exists_eigenvalue
- \+/\- *lemma* module.End.exp_ne_zero_of_has_generalized_eigenvalue
- \+ *def* module.End.generalized_eigenrange
- \+/\- *def* module.End.generalized_eigenspace
- \+/\- *lemma* module.End.generalized_eigenspace_eq_generalized_eigenspace_findim_of_le
- \+/\- *lemma* module.End.generalized_eigenspace_mono
- \+/\- *lemma* module.End.generalized_eigenspace_restrict
- \+ *lemma* module.End.generalized_eigenvec_disjoint_range_ker
- \+/\- *def* module.End.has_eigenvalue
- \+/\- *def* module.End.has_eigenvector
- \+/\- *def* module.End.has_generalized_eigenvalue
- \+/\- *lemma* module.End.has_generalized_eigenvalue_of_has_eigenvalue
- \+/\- *lemma* module.End.has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le
- \+/\- *def* module.End.has_generalized_eigenvector
- \+/\- *lemma* module.End.ker_aeval_ring_hom'_unit_polynomial
- \+ *lemma* module.End.map_generalized_eigenrange_le
- \+/\- *lemma* module.End.mem_eigenspace_iff
- \+ *lemma* module.End.pos_findim_generalized_eigenspace_of_has_eigenvalue
- \+ *lemma* module.End.supr_generalized_eigenspace_eq_top

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.mul_sub_algebra_map_commutes
- \+ *lemma* algebra.mul_sub_algebra_map_pow_commutes



## [2020-09-24 02:35:58](https://github.com/leanprover-community/mathlib/commit/4e41445)
chore(scripts): update nolints.txt ([#4226](https://github.com/leanprover-community/mathlib/pull/4226))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-24 02:35:57](https://github.com/leanprover-community/mathlib/commit/6b35819)
refactor(category_theory): make `has_image` and friends a Prop ([#4195](https://github.com/leanprover-community/mathlib/pull/4195))
This is an obious follow-up to [#3995](https://github.com/leanprover-community/mathlib/pull/3995). It changes the following declarations to a `Prop`:
* `arrow.has_lift`
* `strong_epi`
* `has_image`/`has_images`
* `has_strong_epi_mono_factorisations`
* `has_image_map`/`has_image_maps`
The big win is that there is now precisely one notion of exactness in every category with kernels and images, not a (different but provably equal) notion of exactness per `has_kernels` and `has_images` instance like in the pre-[#3995](https://github.com/leanprover-community/mathlib/pull/3995) era.
#### Estimated changes
Modified src/algebra/category/Group/images.lean
- \- *def* AddCommGroup.image_iso_range
- \- *lemma* AddCommGroup.image_map

Modified src/category_theory/abelian/basic.lean
- \- *lemma* category_theory.abelian.image_eq_image
- \- *lemma* category_theory.abelian.image_ι_eq_image_ι
- \+ *lemma* category_theory.abelian.images.image_ι_comp_eq_zero
- \- *lemma* category_theory.abelian.kernel_cokernel_eq_image_ι
- \+ *lemma* category_theory.abelian.strong_epi_of_epi
- \- *def* category_theory.abelian.strong_epi_of_epi

Modified src/category_theory/abelian/exact.lean
- \+ *def* category_theory.abelian.is_limit_image'

Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* category_theory.non_preadditive_abelian.strong_epi_of_epi
- \- *def* category_theory.non_preadditive_abelian.strong_epi_of_epi

Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.has_lift.mk

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.has_image.mk
- \- *lemma* category_theory.limits.has_image_map.factor_map
- \+ *def* category_theory.limits.has_image_map.image_map
- \+ *lemma* category_theory.limits.has_image_map.mk
- \+ *lemma* category_theory.limits.has_image_map.transport
- \- *def* category_theory.limits.has_image_map_comp
- \- *def* category_theory.limits.has_image_map_id
- \+ *lemma* category_theory.limits.has_strong_epi_mono_factorisations.mk
- \+/\- *def* category_theory.limits.image.is_image
- \+/\- *def* category_theory.limits.image.mono_factorisation
- \+ *lemma* category_theory.limits.image_map.factor_map
- \+ *def* category_theory.limits.image_map.transport
- \+ *def* category_theory.limits.image_map_comp
- \+ *def* category_theory.limits.image_map_id
- \+ *lemma* category_theory.limits.is_image.e_iso_ext_hom
- \+ *lemma* category_theory.limits.is_image.e_iso_ext_inv
- \+ *lemma* category_theory.limits.is_image.iso_ext_hom_m
- \+ *lemma* category_theory.limits.is_image.iso_ext_inv_m
- \+ *lemma* category_theory.limits.is_image.lift_ι
- \+ *lemma* category_theory.limits.strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
- \+ *lemma* category_theory.limits.strong_epi_of_strong_epi_mono_factorisation

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/strong_epi.lean
- \- *def* category_theory.is_iso_of_mono_of_strong_epi
- \+ *lemma* category_theory.strong_epi_comp
- \- *def* category_theory.strong_epi_comp
- \+ *lemma* category_theory.strong_epi_of_strong_epi
- \- *def* category_theory.strong_epi_of_strong_epi

Modified src/category_theory/limits/shapes/zero.lean
- \- *def* category_theory.limits.has_image.zero
- \+ *def* category_theory.limits.image_factorisation_zero
- \+/\- *def* category_theory.limits.image_zero

Modified src/category_theory/limits/types.lean
- \- *lemma* category_theory.limits.types.image_map

Modified src/category_theory/simple.lean




## [2020-09-24 00:15:43](https://github.com/leanprover-community/mathlib/commit/96e81fa)
feat(data/(lazy_)list): various lemmas and definitions ([#4172](https://github.com/leanprover-community/mathlib/pull/4172))
#### Estimated changes
Modified src/data/lazy_list/basic.lean
- \+ *def* lazy_list.attach
- \+ *theorem* lazy_list.forall_mem_cons
- \+ *lemma* lazy_list.mem_cons
- \+ *lemma* lazy_list.mem_nil
- \+ *def* lazy_list.pmap

Modified src/data/list/basic.lean
- \+ *theorem* list.disjoint_take_drop
- \+ *lemma* list.inter_reverse
- \+ *theorem* list.mem_map_swap
- \+ *lemma* list.mem_of_mem_drop
- \+ *theorem* list.nth_eq_none_iff
- \+ *lemma* list.nth_injective
- \+ *lemma* list.reverse_take
- \+ *lemma* list.sizeof_slice_lt
- \+ *lemma* list.slice_eq

Modified src/data/list/defs.lean
- \+ *def* list.slice

Modified src/data/list/perm.lean
- \+ *lemma* list.perm.drop_inter
- \+ *theorem* list.perm.inter_append
- \+ *lemma* list.perm.slice_inter
- \+ *lemma* list.perm.take_inter

Modified src/data/list/sigma.lean
- \+ *lemma* list.sizeof_erase_dupkeys
- \+ *lemma* list.sizeof_kerase

Modified src/data/list/zip.lean
- \+ *lemma* list.nth_zip_eq_some
- \+ *lemma* list.nth_zip_with
- \+ *lemma* list.nth_zip_with_eq_some

Modified src/data/sigma/basic.lean
- \+ *lemma* prod.fst_to_sigma
- \+ *lemma* prod.snd_to_sigma
- \+ *def* prod.to_sigma

Modified src/tactic/interactive.lean




## [2020-09-23 20:55:39](https://github.com/leanprover-community/mathlib/commit/6927958)
feat(data/real/irrational): add a different formulation for irrationality ([#4213](https://github.com/leanprover-community/mathlib/pull/4213))
#### Estimated changes
Modified src/data/rat/basic.lean


Modified src/data/real/irrational.lean
- \+ *lemma* irrational_iff_ne_rational



## [2020-09-23 20:55:36](https://github.com/leanprover-community/mathlib/commit/9aeffa8)
feat(geometry/manifold): bundled smooth map ([#3904](https://github.com/leanprover-community/mathlib/pull/3904))
#### Estimated changes
Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* continuous_linear_map.times_cont_mdiff

Added src/geometry/manifold/times_cont_mdiff_map.lean
- \+ *def* smooth_map
- \+ *lemma* times_cont_mdiff_map.coe_inj
- \+ *def* times_cont_mdiff_map.comp
- \+ *lemma* times_cont_mdiff_map.comp_apply
- \+ *def* times_cont_mdiff_map.const
- \+ *theorem* times_cont_mdiff_map.ext
- \+ *def* times_cont_mdiff_map.id



## [2020-09-23 18:48:10](https://github.com/leanprover-community/mathlib/commit/72e5b9f)
feat(measure_theory): ext lemmas for measures ([#3895](https://github.com/leanprover-community/mathlib/pull/3895))
Add class `sigma_finite`.
Also some cleanup.
Rename `measurable_space.is_measurable` -> `measurable_space.is_measurable'`. This is to avoid name clash with `_root_.is_measurable`, which should almost always be used instead.
define `is_pi_system`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.diff_eq_compl_inter
- \+ *theorem* set.diff_inter_self_eq_diff
- \+ *theorem* set.diff_self_inter

Modified src/logic/basic.lean
- \+ *lemma* fact.elim

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable.ennreal_add

Modified src/measure_theory/content.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *def* is_measurable
- \+ *def* is_pi_system
- \+/\- *lemma* measurable_space.dynkin_system.generate_from_eq
- \+ *lemma* measurable_space.dynkin_system.generate_has_compl
- \+ *lemma* measurable_space.dynkin_system.generate_has_def
- \+ *lemma* measurable_space.dynkin_system.generate_has_subset_generate_measurable
- \+ *lemma* measurable_space.ext_iff
- \+/\- *lemma* measurable_space.generate_from_le
- \+/\- *lemma* measurable_space.generate_from_le_iff
- \+/\- *lemma* measurable_space.induction_on_inter

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ext_of_generate_finite
- \+ *lemma* measure_theory.measure.ext_of_generate_from_of_Union
- \+/\- *def* measure_theory.measure.is_complete
- \+ *lemma* measure_theory.measure_compl

Modified src/measure_theory/outer_measure.lean




## [2020-09-23 16:56:11](https://github.com/leanprover-community/mathlib/commit/7cf8fa6)
fix(archive/100-thms): update link to 100.yaml in README ([#4224](https://github.com/leanprover-community/mathlib/pull/4224))
#### Estimated changes
Modified archive/100-theorems-list/README.md




## [2020-09-23 11:10:37](https://github.com/leanprover-community/mathlib/commit/ecd889a)
feat(data/polynomial/*): higher order derivative ([#4187](https://github.com/leanprover-community/mathlib/pull/4187))
#### Estimated changes
Added src/data/polynomial/iterated_deriv.lean
- \+ *lemma* polynomial.coeff_iterated_deriv_as_prod_Ico
- \+ *lemma* polynomial.coeff_iterated_deriv_as_prod_range
- \+ *def* polynomial.iterated_deriv
- \+ *lemma* polynomial.iterated_deriv_C
- \+ *lemma* polynomial.iterated_deriv_C_zero
- \+ *lemma* polynomial.iterated_deriv_X
- \+ *lemma* polynomial.iterated_deriv_X_one
- \+ *lemma* polynomial.iterated_deriv_X_zero
- \+ *lemma* polynomial.iterated_deriv_add
- \+ *lemma* polynomial.iterated_deriv_eq_zero_of_nat_degree_lt
- \+ *lemma* polynomial.iterated_deriv_mul
- \+ *lemma* polynomial.iterated_deriv_neg
- \+ *lemma* polynomial.iterated_deriv_one
- \+ *lemma* polynomial.iterated_deriv_one_zero
- \+ *lemma* polynomial.iterated_deriv_smul
- \+ *lemma* polynomial.iterated_deriv_sub
- \+ *lemma* polynomial.iterated_deriv_succ
- \+ *lemma* polynomial.iterated_deriv_zero_left
- \+ *lemma* polynomial.iterated_deriv_zero_right



## [2020-09-23 09:47:01](https://github.com/leanprover-community/mathlib/commit/5ab7eb0)
feat(analysis/special_functions/trigonometric): continuity and differentiability of arctan ([#4138](https://github.com/leanprover-community/mathlib/pull/4138))
Added lemmas for continuity and differentiability of arctan, as well as various supporting limit lemmas.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* deriv_arctan
- \+ *lemma* deriv_within_arctan
- \+ *lemma* differentiable.arctan
- \+ *lemma* differentiable_at.arctan
- \+ *lemma* differentiable_on.arctan
- \+ *lemma* differentiable_within_at.arctan
- \+ *lemma* has_deriv_at.arctan
- \+ *lemma* has_deriv_within_at.arctan
- \+ *lemma* real.arctan_mem_Ioo
- \+ *lemma* real.continuous_arctan
- \+ *lemma* real.continuous_on_tan_Ioo
- \+ *lemma* real.deriv_arctan
- \+/\- *lemma* real.deriv_tan_of_mem_Ioo
- \+ *lemma* real.differentiable_at_arctan
- \+/\- *lemma* real.differentiable_at_tan_of_mem_Ioo
- \+/\- *lemma* real.exists_cos_eq
- \+/\- *lemma* real.exists_cos_eq_zero
- \+/\- *lemma* real.exists_sin_eq
- \+ *lemma* real.has_deriv_at_arctan
- \+/\- *lemma* real.has_deriv_at_tan_of_mem_Ioo
- \+/\- *lemma* real.range_cos
- \+/\- *lemma* real.range_sin
- \+ *def* real.tan_homeomorph
- \+ *lemma* real.tan_homeomorph_inv_fun_eq_arctan
- \+ *lemma* real.tendsto_cos_neg_pi_div_two
- \+ *lemma* real.tendsto_cos_pi_div_two
- \+ *lemma* real.tendsto_sin_neg_pi_div_two
- \+ *lemma* real.tendsto_sin_pi_div_two
- \+ *lemma* real.tendsto_tan_neg_pi_div_two
- \+ *lemma* real.tendsto_tan_pi_div_two

Modified src/analysis/specific_limits.lean
- \- *lemma* tendsto_at_top_div
- \- *lemma* tendsto_at_top_mul_left'
- \- *lemma* tendsto_at_top_mul_left
- \- *lemma* tendsto_at_top_mul_right'
- \- *lemma* tendsto_at_top_mul_right
- \- *lemma* tendsto_inv_at_top_zero'
- \- *lemma* tendsto_inv_at_top_zero
- \- *lemma* tendsto_inv_zero_at_top

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto.inv_tendsto_at_top
- \+ *lemma* tendsto.inv_tendsto_zero
- \+ *lemma* tendsto_at_top_div
- \+ *lemma* tendsto_at_top_mul_left'
- \+ *lemma* tendsto_at_top_mul_left
- \+ *lemma* tendsto_at_top_mul_right'
- \+ *lemma* tendsto_at_top_mul_right
- \+ *lemma* tendsto_inv_at_top_zero'
- \+ *lemma* tendsto_inv_at_top_zero
- \+ *lemma* tendsto_inv_zero_at_top
- \+ *lemma* tendsto_mul_at_bot
- \+ *lemma* tendsto_mul_at_top

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.change_inv



## [2020-09-23 07:33:15](https://github.com/leanprover-community/mathlib/commit/d7aada1)
doc(data/list/tfae): Add skeletal docstring ([#4220](https://github.com/leanprover-community/mathlib/pull/4220))
#### Estimated changes
Modified src/data/list/tfae.lean




## [2020-09-23 01:02:05](https://github.com/leanprover-community/mathlib/commit/937199a)
chore(scripts): update nolints.txt ([#4216](https://github.com/leanprover-community/mathlib/pull/4216))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-22 19:08:32](https://github.com/leanprover-community/mathlib/commit/392d3e3)
feat(archive/imo/*): add IMO 1972 B2, move IMOs to a subdirectory ([#4209](https://github.com/leanprover-community/mathlib/pull/4209))
#### Estimated changes
Added archive/imo/imo1972_b2.lean


Renamed archive/imo1988_q6.lean to archive/imo/imo1988_q6.lean




## [2020-09-22 17:01:30](https://github.com/leanprover-community/mathlib/commit/994c31d)
feat(ring_theory/ideal/basic): mem_bot ([#4211](https://github.com/leanprover-community/mathlib/pull/4211))
Snippet from the Witt project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.mem_bot

Modified src/ring_theory/ideal/over.lean




## [2020-09-22 14:52:30](https://github.com/leanprover-community/mathlib/commit/f2458d6)
chore(data/mv_polynomial): Rename variables ([#4208](https://github.com/leanprover-community/mathlib/pull/4208))
I renamed `α` to `R` throughout. I also changed the `\sigma` to `σ` in `basic.lean`, see leanprover-community/doc-gen[#62](https://github.com/leanprover-community/mathlib/pull/62)
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *def* mv_polynomial.C
- \+/\- *lemma* mv_polynomial.C_0
- \+/\- *lemma* mv_polynomial.C_1
- \+/\- *lemma* mv_polynomial.C_add
- \+/\- *lemma* mv_polynomial.C_eq_coe_nat
- \+/\- *lemma* mv_polynomial.C_mul
- \+/\- *lemma* mv_polynomial.C_pow
- \+/\- *def* mv_polynomial.X
- \+/\- *lemma* mv_polynomial.X_pow_eq_single
- \+/\- *def* mv_polynomial.aeval
- \+/\- *lemma* mv_polynomial.aeval_C
- \+/\- *theorem* mv_polynomial.aeval_def
- \+/\- *lemma* mv_polynomial.aeval_eq_zero
- \+/\- *lemma* mv_polynomial.aeval_monomial
- \+/\- *lemma* mv_polynomial.alg_hom_C
- \+/\- *lemma* mv_polynomial.alg_hom_ext
- \+/\- *theorem* mv_polynomial.algebra_map_eq
- \+/\- *lemma* mv_polynomial.as_sum
- \+/\- *lemma* mv_polynomial.coe_eval₂_hom
- \+/\- *def* mv_polynomial.coeff
- \+/\- *lemma* mv_polynomial.coeff_C_mul
- \+/\- *lemma* mv_polynomial.coeff_add
- \+/\- *def* mv_polynomial.coeff_coe_to_fun
- \+/\- *lemma* mv_polynomial.coeff_map
- \+/\- *lemma* mv_polynomial.coeff_mul
- \+/\- *lemma* mv_polynomial.coeff_mul_X'
- \+/\- *lemma* mv_polynomial.coeff_mul_X
- \+/\- *lemma* mv_polynomial.coeff_sum
- \+/\- *lemma* mv_polynomial.coeff_zero_X
- \+/\- *lemma* mv_polynomial.comp_eval₂_hom
- \+/\- *def* mv_polynomial.constant_coeff
- \+/\- *lemma* mv_polynomial.constant_coeff_C
- \+/\- *lemma* mv_polynomial.constant_coeff_comp_map
- \+/\- *lemma* mv_polynomial.constant_coeff_eq
- \+/\- *lemma* mv_polynomial.constant_coeff_map
- \+/\- *lemma* mv_polynomial.constant_coeff_monomial
- \+/\- *lemma* mv_polynomial.eq_zero_iff
- \+/\- *def* mv_polynomial.eval
- \+/\- *lemma* mv_polynomial.eval_eq'
- \+/\- *lemma* mv_polynomial.eval_eq
- \+/\- *lemma* mv_polynomial.eval_map
- \+/\- *lemma* mv_polynomial.eval_prod
- \+/\- *lemma* mv_polynomial.eval_sum
- \+/\- *theorem* mv_polynomial.eval_unique
- \+/\- *def* mv_polynomial.eval₂
- \+/\- *lemma* mv_polynomial.eval₂_assoc
- \+/\- *lemma* mv_polynomial.eval₂_comp_left
- \+/\- *lemma* mv_polynomial.eval₂_comp_right
- \+/\- *lemma* mv_polynomial.eval₂_congr
- \+/\- *lemma* mv_polynomial.eval₂_eq'
- \+/\- *lemma* mv_polynomial.eval₂_eq
- \+/\- *theorem* mv_polynomial.eval₂_eq_eval_map
- \+/\- *lemma* mv_polynomial.eval₂_eta
- \+/\- *def* mv_polynomial.eval₂_hom
- \+/\- *lemma* mv_polynomial.eval₂_hom_C
- \+/\- *lemma* mv_polynomial.eval₂_hom_X'
- \+/\- *lemma* mv_polynomial.eval₂_hom_congr
- \+/\- *lemma* mv_polynomial.eval₂_hom_eq_zero
- \+/\- *lemma* mv_polynomial.eval₂_hom_map_hom
- \+/\- *lemma* mv_polynomial.eval₂_hom_monomial
- \+/\- *lemma* mv_polynomial.eval₂_map
- \+/\- *lemma* mv_polynomial.eval₂_one
- \+/\- *lemma* mv_polynomial.eval₂_pow
- \+/\- *lemma* mv_polynomial.eval₂_prod
- \+/\- *lemma* mv_polynomial.eval₂_sum
- \+/\- *lemma* mv_polynomial.eval₂_zero
- \+/\- *lemma* mv_polynomial.exists_coeff_ne_zero
- \+/\- *lemma* mv_polynomial.ext
- \+/\- *lemma* mv_polynomial.ext_iff
- \+/\- *lemma* mv_polynomial.hom_eq_hom
- \+/\- *theorem* mv_polynomial.induction_on'
- \+/\- *lemma* mv_polynomial.induction_on
- \+/\- *lemma* mv_polynomial.is_id
- \+/\- *def* mv_polynomial.map
- \+/\- *theorem* mv_polynomial.map_C
- \+/\- *theorem* mv_polynomial.map_X
- \+/\- *lemma* mv_polynomial.map_eval₂
- \+/\- *lemma* mv_polynomial.map_eval₂_hom
- \+/\- *theorem* mv_polynomial.map_id
- \+/\- *theorem* mv_polynomial.map_map
- \+/\- *theorem* mv_polynomial.map_monomial
- \+/\- *lemma* mv_polynomial.monic_monomial_eq
- \+/\- *def* mv_polynomial.monomial
- \+/\- *lemma* mv_polynomial.monomial_add
- \+/\- *lemma* mv_polynomial.monomial_eq
- \+/\- *lemma* mv_polynomial.monomial_mul
- \+/\- *lemma* mv_polynomial.monomial_zero
- \+/\- *lemma* mv_polynomial.ne_zero_iff
- \+/\- *lemma* mv_polynomial.ring_hom_ext
- \+/\- *lemma* mv_polynomial.single_eq_C_mul_X
- \+/\- *lemma* mv_polynomial.smul_eq_C_mul
- \+/\- *lemma* mv_polynomial.smul_eval
- \+/\- *lemma* mv_polynomial.support_map_of_injective
- \+/\- *lemma* mv_polynomial.support_map_subset
- \+/\- *lemma* mv_polynomial.support_sum_monomial_coeff
- \+/\- *def* mv_polynomial

Modified src/data/mv_polynomial/comm_ring.lean
- \+/\- *lemma* mv_polynomial.C_neg
- \+/\- *lemma* mv_polynomial.C_sub
- \+/\- *lemma* mv_polynomial.coeff_neg
- \+/\- *lemma* mv_polynomial.coeff_sub
- \+/\- *lemma* mv_polynomial.degrees_neg
- \+/\- *lemma* mv_polynomial.degrees_sub
- \+/\- *lemma* mv_polynomial.eval₂_hom_X
- \+/\- *lemma* mv_polynomial.hom_C
- \+/\- *def* mv_polynomial.hom_equiv
- \+/\- *lemma* mv_polynomial.total_degree_neg
- \+/\- *lemma* mv_polynomial.total_degree_sub

Modified src/data/mv_polynomial/equiv.lean
- \+/\- *def* mv_polynomial.iter_to_sum
- \+/\- *lemma* mv_polynomial.iter_to_sum_C_C
- \+/\- *lemma* mv_polynomial.iter_to_sum_C_X
- \+/\- *lemma* mv_polynomial.iter_to_sum_X
- \+/\- *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \+/\- *def* mv_polynomial.option_equiv_left
- \+/\- *def* mv_polynomial.option_equiv_right
- \+/\- *def* mv_polynomial.pempty_ring_equiv
- \+/\- *def* mv_polynomial.punit_ring_equiv
- \+/\- *def* mv_polynomial.ring_equiv_congr
- \+/\- *def* mv_polynomial.ring_equiv_of_equiv
- \+/\- *def* mv_polynomial.sum_ring_equiv
- \+/\- *def* mv_polynomial.sum_to_iter
- \+/\- *lemma* mv_polynomial.sum_to_iter_C
- \+/\- *lemma* mv_polynomial.sum_to_iter_Xl
- \+/\- *lemma* mv_polynomial.sum_to_iter_Xr

Modified src/data/mv_polynomial/monad.lean


Modified src/data/mv_polynomial/variables.lean
- \+/\- *lemma* mv_polynomial.aeval_eq_constant_coeff_of_vars
- \+/\- *lemma* mv_polynomial.coeff_eq_zero_of_total_degree_lt
- \+/\- *def* mv_polynomial.degree_of
- \+/\- *def* mv_polynomial.degrees
- \+/\- *lemma* mv_polynomial.degrees_C
- \+/\- *lemma* mv_polynomial.degrees_X
- \+/\- *lemma* mv_polynomial.degrees_add
- \+/\- *lemma* mv_polynomial.degrees_add_of_disjoint
- \+/\- *lemma* mv_polynomial.degrees_map
- \+/\- *lemma* mv_polynomial.degrees_map_of_injective
- \+/\- *lemma* mv_polynomial.degrees_monomial
- \+/\- *lemma* mv_polynomial.degrees_monomial_eq
- \+/\- *lemma* mv_polynomial.degrees_mul
- \+/\- *lemma* mv_polynomial.degrees_one
- \+/\- *lemma* mv_polynomial.degrees_pow
- \+/\- *lemma* mv_polynomial.degrees_prod
- \+/\- *lemma* mv_polynomial.degrees_sum
- \+/\- *lemma* mv_polynomial.degrees_zero
- \+/\- *lemma* mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars
- \+/\- *lemma* mv_polynomial.exists_degree_lt
- \+/\- *lemma* mv_polynomial.le_degrees_add
- \+/\- *lemma* mv_polynomial.mem_degrees
- \+/\- *lemma* mv_polynomial.mem_support_not_mem_vars_zero
- \+/\- *def* mv_polynomial.total_degree
- \+/\- *lemma* mv_polynomial.total_degree_C
- \+/\- *lemma* mv_polynomial.total_degree_X
- \+/\- *lemma* mv_polynomial.total_degree_add
- \+/\- *lemma* mv_polynomial.total_degree_eq
- \+/\- *lemma* mv_polynomial.total_degree_le_degrees_card
- \+/\- *lemma* mv_polynomial.total_degree_mul
- \+/\- *lemma* mv_polynomial.total_degree_multiset_prod
- \+/\- *lemma* mv_polynomial.total_degree_one
- \+/\- *lemma* mv_polynomial.total_degree_pow
- \+/\- *lemma* mv_polynomial.total_degree_zero
- \+/\- *def* mv_polynomial.vars
- \+/\- *lemma* mv_polynomial.vars_0
- \+/\- *lemma* mv_polynomial.vars_C
- \+/\- *lemma* mv_polynomial.vars_X
- \+/\- *lemma* mv_polynomial.vars_add_subset
- \+/\- *lemma* mv_polynomial.vars_monomial_single
- \+/\- *lemma* mv_polynomial.vars_mul
- \+/\- *lemma* mv_polynomial.vars_one
- \+/\- *lemma* mv_polynomial.vars_pow
- \+/\- *lemma* mv_polynomial.vars_prod



## [2020-09-22 12:57:23](https://github.com/leanprover-community/mathlib/commit/516b0df)
refactor(ring_theory/algebra): re-bundle `subalgebra` ([#4180](https://github.com/leanprover-community/mathlib/pull/4180))
This PR makes `subalgebra` extend `subsemiring` instead of using `subsemiring` as a field in its definition. The refactor is needed because `intermediate_field` should simultaneously extend `subalgebra` and `subfield`, and so the type of the `carrier` fields should match.
I added some copies of definitions that use `subring` instead of `is_subring` if I needed to change these definitions anyway.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean


Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* algebra.adjoin_int

Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_hom.coe_range
- \+ *lemma* alg_hom.map_div
- \+ *lemma* alg_hom.map_inv
- \+ *lemma* alg_hom.mem_range
- \+ *lemma* algebra.algebra_map_of_subring
- \+ *lemma* algebra.algebra_map_of_subring_apply
- \+ *lemma* algebra.coe_algebra_map_of_subring
- \+ *lemma* algebra.is_subring_algebra_map_apply
- \+ *lemma* algebra.is_subring_coe_algebra_map
- \+ *lemma* algebra.is_subring_coe_algebra_map_hom
- \- *lemma* algebra.subring_algebra_map_apply
- \- *lemma* algebra.subring_coe_algebra_map
- \- *lemma* algebra.subring_coe_algebra_map_hom
- \+ *lemma* mem_subalgebra_of_is_subring
- \+/\- *lemma* mem_subalgebra_of_subring
- \+ *def* subalgebra.to_subring
- \+ *def* subalgebra_of_is_subring
- \+/\- *def* subalgebra_of_subring

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/subring.lean
- \+ *lemma* ring_hom.mem_range_self
- \+ *lemma* ring_hom.surjective_onto_range
- \+ *def* set.to_subring
- \+ *theorem* subring.sub_mem
- \- *def* subring.to_comm_ring



## [2020-09-22 11:28:53](https://github.com/leanprover-community/mathlib/commit/d09ef4a)
feat(category_theory/monoidal): transport monoidal structure along an equivalence ([#4123](https://github.com/leanprover-community/mathlib/pull/4123))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+/\- *lemma* category_theory.equivalence.functor_unit_comp

Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* category_theory.monoidal_category.id_tensor_comp_tensor_id
- \+/\- *lemma* category_theory.monoidal_category.tensor_id_comp_id_tensor

Modified src/category_theory/monoidal/functor.lean
- \+ *def* category_theory.lax_monoidal_functor.id

Added src/category_theory/monoidal/transport.lean
- \+ *def* category_theory.monoidal.from_transported
- \+ *def* category_theory.monoidal.lax_from_transported
- \+ *def* category_theory.monoidal.lax_to_transported
- \+ *def* category_theory.monoidal.to_transported
- \+ *def* category_theory.monoidal.transport
- \+ *def* category_theory.monoidal.transported
- \+ *def* category_theory.monoidal.transported_monoidal_counit_iso
- \+ *def* category_theory.monoidal.transported_monoidal_unit_iso



## [2020-09-22 11:28:51](https://github.com/leanprover-community/mathlib/commit/caffd02)
feat(data/polynomial/degree/trailing_degree): basic definitions and properties ([#4113](https://github.com/leanprover-community/mathlib/pull/4113))
Adds trailing_degree, trailing_nat_degree, trailing_coeff and various lemmas add functionality to work with trailing coefficients
#### Estimated changes
Added src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.coeff_eq_zero_of_lt_nat_trailing_degree
- \+ *lemma* polynomial.coeff_eq_zero_of_trailing_degree_lt
- \+ *lemma* polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
- \+ *lemma* polynomial.coeff_nat_trailing_degree_pred_eq_zero
- \+ *lemma* polynomial.le_trailing_degree_C
- \+ *theorem* polynomial.le_trailing_degree_C_mul_X_pow
- \+ *theorem* polynomial.le_trailing_degree_X
- \+ *theorem* polynomial.le_trailing_degree_X_pow
- \+ *lemma* polynomial.le_trailing_degree_of_ne_zero
- \+ *lemma* polynomial.monomial_le_trailing_degree
- \+ *def* polynomial.nat_trailing_degree
- \+ *lemma* polynomial.nat_trailing_degree_C
- \+ *lemma* polynomial.nat_trailing_degree_X
- \+ *lemma* polynomial.nat_trailing_degree_X_le
- \+ *lemma* polynomial.nat_trailing_degree_eq_of_trailing_degree_eq
- \+ *lemma* polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some
- \+ *lemma* polynomial.nat_trailing_degree_int_cast
- \+ *lemma* polynomial.nat_trailing_degree_le_nat_trailing_degree
- \+ *lemma* polynomial.nat_trailing_degree_le_of_ne_zero
- \+ *theorem* polynomial.nat_trailing_degree_le_of_trailing_degree_le
- \+ *lemma* polynomial.nat_trailing_degree_le_trailing_degree
- \+ *lemma* polynomial.nat_trailing_degree_nat_cast
- \+ *lemma* polynomial.nat_trailing_degree_neg
- \+ *lemma* polynomial.nat_trailing_degree_one
- \+ *lemma* polynomial.nat_trailing_degree_zero
- \+ *lemma* polynomial.ne_zero_of_trailing_degree_lt
- \+ *def* polynomial.next_coeff_up
- \+ *lemma* polynomial.next_coeff_up_C_eq_zero
- \+ *lemma* polynomial.next_coeff_up_of_pos_nat_trailing_degree
- \+ *def* polynomial.trailing_coeff
- \+ *def* polynomial.trailing_degree
- \+ *lemma* polynomial.trailing_degree_C
- \+ *lemma* polynomial.trailing_degree_X
- \+ *lemma* polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq
- \+ *lemma* polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos
- \+ *lemma* polynomial.trailing_degree_eq_nat_trailing_degree
- \+ *lemma* polynomial.trailing_degree_eq_top
- \+ *lemma* polynomial.trailing_degree_le_trailing_degree
- \+ *lemma* polynomial.trailing_degree_lt_wf
- \+ *lemma* polynomial.trailing_degree_monomial
- \+ *lemma* polynomial.trailing_degree_ne_of_nat_trailing_degree_ne
- \+ *lemma* polynomial.trailing_degree_neg
- \+ *lemma* polynomial.trailing_degree_one
- \+ *lemma* polynomial.trailing_degree_one_le
- \+ *lemma* polynomial.trailing_degree_zero
- \+ *lemma* polynomial.trailing_monic.def
- \+ *lemma* polynomial.trailing_monic.trailing_coeff
- \+ *def* polynomial.trailing_monic



## [2020-09-22 10:04:16](https://github.com/leanprover-community/mathlib/commit/58d0bfc)
feat(topology/sheaves): alternate formulation of the sheaf condition ([#4190](https://github.com/leanprover-community/mathlib/pull/4190))
Currently the sheaf condition is stated as it often is in textbooks, e.g. 
https://stacks.math.columbia.edu/tag/0072. That is, it is about an equalizer of the two maps `∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
This PR adds an equivalent formulation, saying that `F.obj (supr U)` (with its natural projection maps) is the limit of the diagram consisting of the `F.obj (U i)` and the `F.obj (U i ⊓ U j)`. 
I'd like to add further reformulations in subsequent PRs, in particular the nice one I saw in Lurie's SAG, just saying that `F.obj (supr U)` is the limit over the diagram of all `F.obj V` where `V` is an open subset of *some* `U i`. This version is actually much nicer to formalise, and I'm hoping we can translate over quite a lot of what we've already done about the sheaf condition to that version
#### Estimated changes
Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Added src/category_theory/category/pairwise.lean
- \+ *def* category_theory.pairwise.comp
- \+ *def* category_theory.pairwise.cone
- \+ *def* category_theory.pairwise.cone_is_limit
- \+ *def* category_theory.pairwise.cone_π_app
- \+ *def* category_theory.pairwise.diagram
- \+ *def* category_theory.pairwise.diagram_map
- \+ *def* category_theory.pairwise.diagram_obj
- \+ *def* category_theory.pairwise.id

Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.le_of_op_hom
- \+ *def* category_theory.op_hom_of_le

Modified src/topology/sheaves/forget.lean
- \+ *def* Top.presheaf.sheaf_condition.diagram_comp_preserves_limits
- \+ *def* Top.presheaf.sheaf_condition.map_cone_fork
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_comp
- \- *def* Top.sheaf_condition.diagram_comp_preserves_limits
- \- *def* Top.sheaf_condition.map_cone_fork
- \- *def* Top.sheaf_condition_equiv_sheaf_condition_comp

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf.lean
- \+ *def* Top.presheaf.sheaf_condition
- \+ *def* Top.presheaf.sheaf_condition_equiv_of_iso
- \+ *def* Top.presheaf.sheaf_condition_punit
- \- *def* Top.sheaf_condition.cover.of_open_embedding
- \- *def* Top.sheaf_condition.diagram.iso_of_iso
- \- *def* Top.sheaf_condition.diagram.iso_of_open_embedding
- \- *def* Top.sheaf_condition.diagram
- \- *def* Top.sheaf_condition.fork.iso_of_iso
- \- *def* Top.sheaf_condition.fork.iso_of_open_embedding
- \- *def* Top.sheaf_condition.fork
- \- *lemma* Top.sheaf_condition.fork_X
- \- *lemma* Top.sheaf_condition.fork_ι
- \- *lemma* Top.sheaf_condition.fork_π_app_walking_parallel_pair_one
- \- *lemma* Top.sheaf_condition.fork_π_app_walking_parallel_pair_zero
- \- *def* Top.sheaf_condition.left_res
- \- *def* Top.sheaf_condition.pi_inters.iso_of_iso
- \- *def* Top.sheaf_condition.pi_inters.iso_of_open_embedding
- \- *def* Top.sheaf_condition.pi_inters
- \- *def* Top.sheaf_condition.pi_opens.iso_of_iso
- \- *def* Top.sheaf_condition.pi_opens.iso_of_open_embedding
- \- *def* Top.sheaf_condition.pi_opens
- \- *def* Top.sheaf_condition.res
- \- *def* Top.sheaf_condition.right_res
- \- *lemma* Top.sheaf_condition.w
- \- *def* Top.sheaf_condition
- \- *def* Top.sheaf_condition_equiv_of_iso
- \- *def* Top.sheaf_condition_punit

Added src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.cover.of_open_embedding
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_iso
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_open_embedding
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.diagram
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_iso
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_open_embedding
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.fork
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.fork_X
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.fork_ι
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_one
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.left_res
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_iso
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_open_embedding
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_inters
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_iso
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_open_embedding
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.pi_opens
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.res
- \+ *def* Top.presheaf.sheaf_condition_equalizer_products.right_res
- \+ *lemma* Top.presheaf.sheaf_condition_equalizer_products.w

Added src/topology/sheaves/sheaf_condition/pairwise_intersections.lean
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_pairwise_intersections
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_counit_iso
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor_obj
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse_obj
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso_app
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone
- \+ *def* Top.presheaf.sheaf_condition_pairwise_intersections
- \+ *def* Top.presheaf.sheaf_condition_preserves_limit_pairwise_intersections

Modified src/topology/sheaves/sheaf_of_functions.lean
- \+ *def* Top.presheaf.to_Type
- \+ *def* Top.presheaf.to_Types
- \- *def* Top.sheaf_condition.to_Type
- \- *def* Top.sheaf_condition.to_Types



## [2020-09-22 08:41:20](https://github.com/leanprover-community/mathlib/commit/b4641ef)
feat(l1_space): add measurability to integrable ([#4170](https://github.com/leanprover-community/mathlib/pull/4170))
This PR defines `integrable` such that `integrable` implies `measurable`. The old version is called `has_finite_integral`.
This allows us to drop *many* measurability conditions from lemmas that also require integrability.
There are some lemmas that have extra measurability conditions, if it has `integrable` as conclusion without corresponding `measurable` hypothesis.
There are many results that require an additional `[measurable_space E]` hypothesis, and some that require `[borel_space E]` or `[second_countable_space E]` (usually when using that addition is measurable).
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_add
- \+ *lemma* measure_theory.integral_add_measure'
- \+/\- *lemma* measure_theory.integral_eq
- \+/\- *lemma* measure_theory.integral_eq_lintegral_max_sub_lintegral_min
- \+/\- *lemma* measure_theory.integral_finset_sum
- \+/\- *lemma* measure_theory.integral_mono
- \+/\- *lemma* measure_theory.integral_mono_of_nonneg
- \- *lemma* measure_theory.integral_non_integrable
- \+/\- *lemma* measure_theory.integral_sub
- \+/\- *lemma* measure_theory.integral_undef
- \+/\- *lemma* measure_theory.l1.integral_of_fun_eq_integral
- \+/\- *lemma* measure_theory.l1.norm_of_fun_eq_integral_norm
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_add
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_sub
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_zero
- \+/\- *lemma* measure_theory.norm_integral_le_of_norm_le
- \+/\- *lemma* measure_theory.simple_func.integrable_pair
- \+/\- *lemma* measure_theory.simple_func.integral_sub
- \+/\- *lemma* measure_theory.tendsto_integral_of_l1

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* interval_integrable.add
- \+/\- *lemma* interval_integrable.neg
- \+/\- *lemma* interval_integrable.refl
- \+/\- *lemma* interval_integrable.sub
- \+/\- *lemma* interval_integral.deriv_integral_left
- \+/\- *lemma* interval_integral.deriv_integral_of_tendsto_ae_left
- \+/\- *lemma* interval_integral.deriv_integral_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.deriv_integral_right
- \+/\- *lemma* interval_integral.deriv_within_integral_left
- \+/\- *lemma* interval_integral.deriv_within_integral_of_tendsto_ae_left
- \+/\- *lemma* interval_integral.deriv_within_integral_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.deriv_within_integral_right
- \+/\- *lemma* interval_integral.fderiv_integral
- \+/\- *lemma* interval_integral.fderiv_integral_of_tendsto_ae
- \+/\- *lemma* interval_integral.fderiv_within_integral_of_tendsto_ae
- \+/\- *lemma* interval_integral.integral_add
- \+/\- *lemma* interval_integral.integral_has_deriv_at_left
- \+/\- *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.integral_has_deriv_at_right
- \+/\- *lemma* interval_integral.integral_has_deriv_within_at_left
- \+/\- *lemma* interval_integral.integral_has_deriv_within_at_of_tendsto_ae_left
- \+/\- *lemma* interval_integral.integral_has_deriv_within_at_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.integral_has_deriv_within_at_right
- \+/\- *lemma* interval_integral.integral_has_fderiv_at
- \+/\- *lemma* interval_integral.integral_has_fderiv_at_of_tendsto_ae
- \+/\- *lemma* interval_integral.integral_has_fderiv_within_at
- \+/\- *lemma* interval_integral.integral_has_fderiv_within_at_of_tendsto_ae
- \+/\- *lemma* interval_integral.integral_has_strict_deriv_at_left
- \+/\- *lemma* interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.integral_has_strict_deriv_at_right
- \+/\- *lemma* interval_integral.integral_has_strict_fderiv_at
- \+/\- *lemma* interval_integral.integral_has_strict_fderiv_at_of_tendsto_ae
- \+/\- *lemma* interval_integral.integral_sub

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measurable.integrable_zero
- \+ *lemma* measure_theory.has_finite_integral.add_measure
- \+ *lemma* measure_theory.has_finite_integral.congr'
- \+ *lemma* measure_theory.has_finite_integral.congr
- \+ *lemma* measure_theory.has_finite_integral.const_mul
- \+ *lemma* measure_theory.has_finite_integral.left_of_add_measure
- \+ *lemma* measure_theory.has_finite_integral.max_zero
- \+ *lemma* measure_theory.has_finite_integral.min_zero
- \+ *lemma* measure_theory.has_finite_integral.mono'
- \+ *lemma* measure_theory.has_finite_integral.mono
- \+ *lemma* measure_theory.has_finite_integral.mono_measure
- \+ *lemma* measure_theory.has_finite_integral.mul_const
- \+ *lemma* measure_theory.has_finite_integral.neg
- \+ *lemma* measure_theory.has_finite_integral.norm
- \+ *lemma* measure_theory.has_finite_integral.right_of_add_measure
- \+ *lemma* measure_theory.has_finite_integral.smul
- \+ *lemma* measure_theory.has_finite_integral.smul_measure
- \+ *def* measure_theory.has_finite_integral
- \+ *lemma* measure_theory.has_finite_integral_add_measure
- \+ *lemma* measure_theory.has_finite_integral_congr'
- \+ *lemma* measure_theory.has_finite_integral_congr
- \+ *lemma* measure_theory.has_finite_integral_const
- \+ *lemma* measure_theory.has_finite_integral_const_iff
- \+ *lemma* measure_theory.has_finite_integral_iff_edist
- \+ *lemma* measure_theory.has_finite_integral_iff_norm
- \+ *lemma* measure_theory.has_finite_integral_iff_of_real
- \+ *lemma* measure_theory.has_finite_integral_neg_iff
- \+ *lemma* measure_theory.has_finite_integral_norm_iff
- \+ *lemma* measure_theory.has_finite_integral_of_bounded
- \+ *lemma* measure_theory.has_finite_integral_of_dominated_convergence
- \+ *lemma* measure_theory.has_finite_integral_smul_iff
- \+ *lemma* measure_theory.has_finite_integral_zero
- \+ *lemma* measure_theory.has_finite_integral_zero_measure
- \+/\- *lemma* measure_theory.integrable.add
- \+/\- *lemma* measure_theory.integrable.congr'
- \+/\- *lemma* measure_theory.integrable.congr
- \+ *lemma* measure_theory.integrable.has_finite_integral
- \+/\- *lemma* measure_theory.integrable.left_of_add_measure
- \+ *lemma* measure_theory.integrable.measurable
- \+/\- *lemma* measure_theory.integrable.mono'
- \+/\- *lemma* measure_theory.integrable.mono
- \+/\- *lemma* measure_theory.integrable.mono_measure
- \+/\- *lemma* measure_theory.integrable.neg
- \+/\- *lemma* measure_theory.integrable.norm
- \+/\- *lemma* measure_theory.integrable.right_of_add_measure
- \+/\- *lemma* measure_theory.integrable.smul
- \+/\- *lemma* measure_theory.integrable.sub
- \+/\- *def* measure_theory.integrable
- \+/\- *lemma* measure_theory.integrable_congr'
- \+/\- *lemma* measure_theory.integrable_congr
- \+/\- *lemma* measure_theory.integrable_finset_sum
- \- *lemma* measure_theory.integrable_iff_edist
- \- *lemma* measure_theory.integrable_iff_norm
- \- *lemma* measure_theory.integrable_iff_of_real
- \+/\- *lemma* measure_theory.integrable_map_measure
- \+/\- *lemma* measure_theory.integrable_neg_iff
- \+/\- *lemma* measure_theory.integrable_norm_iff
- \- *lemma* measure_theory.integrable_of_bounded
- \- *lemma* measure_theory.integrable_of_dominated_convergence
- \+/\- *lemma* measure_theory.integrable_smul_iff
- \+/\- *lemma* measure_theory.integrable_zero
- \- *lemma* measure_theory.integrable_zero_measure
- \+/\- *lemma* measure_theory.l1.dist_to_fun
- \+/\- *lemma* measure_theory.l1.norm_of_fun
- \+/\- *lemma* measure_theory.l1.norm_of_fun_eq_lintegral_norm
- \+/\- *def* measure_theory.l1.of_fun
- \+/\- *lemma* measure_theory.l1.of_fun_add
- \+/\- *lemma* measure_theory.l1.of_fun_eq_mk
- \+/\- *lemma* measure_theory.l1.of_fun_eq_of_fun
- \+/\- *lemma* measure_theory.l1.of_fun_neg
- \+/\- *lemma* measure_theory.l1.of_fun_smul
- \+/\- *lemma* measure_theory.l1.of_fun_sub
- \+/\- *lemma* measure_theory.l1.of_fun_to_fun
- \+/\- *lemma* measure_theory.l1.of_fun_zero
- \+/\- *lemma* measure_theory.l1.to_fun_of_fun
- \+/\- *def* measure_theory.l1
- \+/\- *lemma* measure_theory.lintegral_edist_lt_top

Modified src/measure_theory/set_integral.lean
- \+/\- *def* continuous_linear_map.comp_l1
- \+/\- *lemma* continuous_linear_map.comp_l1_apply
- \+/\- *lemma* continuous_linear_map.integrable_comp
- \+/\- *lemma* continuous_linear_map.integral_comp_comm
- \+/\- *lemma* continuous_linear_map.integral_comp_l1_comm
- \+/\- *lemma* continuous_linear_map.measurable_comp_l1
- \+/\- *lemma* continuous_linear_map.norm_comp_l1_apply_le
- \+/\- *lemma* continuous_on.integrable_on_compact
- \+/\- *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* measure_theory.has_finite_integral_restrict_of_bounded
- \+/\- *lemma* measure_theory.integrable_indicator_iff
- \+/\- *lemma* measure_theory.integrable_on_empty
- \+/\- *lemma* measure_theory.integrable_on_finite_union
- \+/\- *lemma* measure_theory.integrable_on_finset_union
- \- *lemma* measure_theory.integrable_on_of_bounded
- \+/\- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter
- \+/\- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+/\- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto_ae

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* measure_theory.simple_func_sequence_tendsto'



## [2020-09-22 06:16:42](https://github.com/leanprover-community/mathlib/commit/2ae199f)
refactor(ring_theory/unique_factorization_domain): completes the refactor of `unique_factorization_domain` ([#4156](https://github.com/leanprover-community/mathlib/pull/4156))
Refactors `unique_factorization_domain` to `unique_factorization_monoid`
`unique_factorization_monoid` is a predicate
`unique_factorization_monoid` now requires no additive/subtractive structure
#### Estimated changes
Modified docs/100.yaml


Modified docs/overview.yaml


Modified scripts/nolints.txt


Modified src/algebra/associated.lean
- \- *theorem* associates.prod_eq_zero_iff

Modified src/algebra/gcd_monoid.lean
- \+ *lemma* associates.mk_normalize

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.prod_eq_zero_iff

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible
- \+ *theorem* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.ufd
- \+/\- *lemma* discrete_valuation_ring.of_ufd_of_unique_irreducible

Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/rational_root.lean
- \- *lemma* unique_factorization_domain.integer_of_integral
- \- *lemma* unique_factorization_domain.integrally_closed
- \+ *lemma* unique_factorization_monoid.integer_of_integral
- \+ *lemma* unique_factorization_monoid.integrally_closed

Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \- *lemma* associates.associates_irreducible_iff_prime
- \- *def* associates.factors'
- \- *def* associates.factors
- \+/\- *theorem* associates.factors_mk
- \+/\- *theorem* associates.map_subtype_coe_factors'
- \+/\- *def* associates.{u}
- \- *theorem* coprime_iff_gcd_eq_one
- \- *lemma* exists_prime_dvd_of_gcd_ne_one
- \+ *lemma* irreducible_iff_prime_of_exists_prime_of_factor
- \+ *theorem* irreducible_iff_prime_of_exists_unique_irreducible_of_factor
- \+ *lemma* prime_factors_irreducible
- \+ *lemma* prime_factors_unique
- \- *lemma* unique_factorization_domain.dvd_of_dvd_mul_left_of_no_prime_factors
- \- *lemma* unique_factorization_domain.dvd_of_dvd_mul_right_of_no_prime_factors
- \- *lemma* unique_factorization_domain.exists_mem_factors_of_dvd
- \- *lemma* unique_factorization_domain.exists_reduced_factors'
- \- *lemma* unique_factorization_domain.exists_reduced_factors
- \- *lemma* unique_factorization_domain.factors_irreducible
- \- *lemma* unique_factorization_domain.induction_on_prime
- \- *lemma* unique_factorization_domain.irreducible_factors
- \- *lemma* unique_factorization_domain.irreducible_iff_prime
- \- *lemma* unique_factorization_domain.no_factors_of_no_prime_factors
- \- *def* unique_factorization_domain.of_unique_irreducible_factorization
- \- *def* unique_factorization_domain.to_gcd_monoid
- \- *lemma* unique_factorization_domain.unique
- \+ *lemma* unique_factorization_monoid.dvd_of_dvd_mul_left_of_no_prime_of_factor
- \+ *lemma* unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_of_factor
- \+ *lemma* unique_factorization_monoid.exists_mem_factors_of_dvd
- \+ *theorem* unique_factorization_monoid.exists_prime_of_factor
- \+ *lemma* unique_factorization_monoid.exists_reduced_factors'
- \+ *lemma* unique_factorization_monoid.exists_reduced_factors
- \+ *lemma* unique_factorization_monoid.factors_irreducible
- \+ *theorem* unique_factorization_monoid.factors_prod
- \+ *lemma* unique_factorization_monoid.factors_unique
- \+ *lemma* unique_factorization_monoid.induction_on_prime
- \+ *theorem* unique_factorization_monoid.irreducible_of_factor
- \+ *lemma* unique_factorization_monoid.no_factors_of_no_prime_of_factor
- \+ *theorem* unique_factorization_monoid.normalize_factor
- \+ *theorem* unique_factorization_monoid.of_exists_unique_irreducible_of_factor
- \+ *theorem* unique_factorization_monoid.prime_of_factor
- \+ *theorem* unique_factorization_monoid_iff_exists_prime_of_factor
- \+ *theorem* unique_factorization_monoid_of_exists_prime_of_factor
- \+ *lemma* wf_dvd_monoid_of_exists_prime_of_factor



## [2020-09-22 00:54:05](https://github.com/leanprover-community/mathlib/commit/480c92c)
chore(scripts): update nolints.txt ([#4207](https://github.com/leanprover-community/mathlib/pull/4207))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-21 18:45:31](https://github.com/leanprover-community/mathlib/commit/b91df55)
chore(topology/algebra/module): make `topological_module` an abbreviation ([#4200](https://github.com/leanprover-community/mathlib/pull/4200))
Also prove that a `topological_semiring` is a `topological_semimodule`.
#### Estimated changes
Modified src/topology/algebra/module.lean




## [2020-09-21 16:27:12](https://github.com/leanprover-community/mathlib/commit/92c0125)
chore(data/nat/digits): use nat namespace ([#4201](https://github.com/leanprover-community/mathlib/pull/4201))
#### Estimated changes
Modified docs/100.yaml


Modified src/data/nat/digits.lean
- \- *lemma* base_pow_length_digits_le'
- \- *lemma* base_pow_length_digits_le
- \- *lemma* coe_int_of_digits
- \- *lemma* coe_of_digits
- \- *def* digits
- \- *lemma* digits_add
- \- *lemma* digits_add_two_add_one
- \- *def* digits_aux
- \- *def* digits_aux_0
- \- *def* digits_aux_1
- \- *lemma* digits_aux_def
- \- *lemma* digits_aux_zero
- \- *lemma* digits_eq_nil_iff_eq_zero
- \- *lemma* digits_last
- \- *lemma* digits_len_le_digits_len_succ
- \- *lemma* digits_lt_base'
- \- *lemma* digits_lt_base
- \- *lemma* digits_ne_nil_iff_ne_zero
- \- *lemma* digits_of_digits
- \- *lemma* digits_of_lt
- \- *lemma* digits_one
- \- *lemma* digits_one_succ
- \- *lemma* digits_zero
- \- *lemma* digits_zero_of_eq_zero
- \- *lemma* digits_zero_succ
- \- *lemma* digits_zero_zero
- \- *lemma* dvd_iff_dvd_digits_sum
- \- *lemma* dvd_iff_dvd_of_digits
- \- *lemma* dvd_of_digits_sub_of_digits
- \- *lemma* eleven_dvd_iff
- \- *lemma* last_digit_ne_zero
- \- *lemma* le_digits_len_le
- \- *lemma* lt_base_pow_length_digits'
- \- *lemma* lt_base_pow_length_digits
- \- *lemma* modeq_digits_sum
- \- *lemma* modeq_eleven_digits_sum
- \- *lemma* modeq_nine_digits_sum
- \- *lemma* modeq_three_digits_sum
- \+ *lemma* nat.base_pow_length_digits_le'
- \+ *lemma* nat.base_pow_length_digits_le
- \+ *lemma* nat.coe_int_of_digits
- \+ *lemma* nat.coe_of_digits
- \+ *def* nat.digits
- \+ *lemma* nat.digits_add
- \+ *lemma* nat.digits_add_two_add_one
- \+ *def* nat.digits_aux
- \+ *def* nat.digits_aux_0
- \+ *def* nat.digits_aux_1
- \+ *lemma* nat.digits_aux_def
- \+ *lemma* nat.digits_aux_zero
- \+ *lemma* nat.digits_eq_nil_iff_eq_zero
- \+ *lemma* nat.digits_last
- \+ *lemma* nat.digits_len_le_digits_len_succ
- \+ *lemma* nat.digits_lt_base'
- \+ *lemma* nat.digits_lt_base
- \+ *lemma* nat.digits_ne_nil_iff_ne_zero
- \+ *lemma* nat.digits_of_digits
- \+ *lemma* nat.digits_of_lt
- \+ *lemma* nat.digits_one
- \+ *lemma* nat.digits_one_succ
- \+ *lemma* nat.digits_zero
- \+ *lemma* nat.digits_zero_of_eq_zero
- \+ *lemma* nat.digits_zero_succ
- \+ *lemma* nat.digits_zero_zero
- \+ *lemma* nat.dvd_iff_dvd_digits_sum
- \+ *lemma* nat.dvd_iff_dvd_of_digits
- \+ *lemma* nat.dvd_of_digits_sub_of_digits
- \+ *lemma* nat.eleven_dvd_iff
- \+ *lemma* nat.last_digit_ne_zero
- \+ *lemma* nat.le_digits_len_le
- \+ *lemma* nat.lt_base_pow_length_digits'
- \+ *lemma* nat.lt_base_pow_length_digits
- \+ *lemma* nat.modeq_digits_sum
- \+ *lemma* nat.modeq_eleven_digits_sum
- \+ *lemma* nat.modeq_nine_digits_sum
- \+ *lemma* nat.modeq_three_digits_sum
- \+ *lemma* nat.nine_dvd_iff
- \+ *def* nat.of_digits
- \+ *lemma* nat.of_digits_append
- \+ *lemma* nat.of_digits_digits
- \+ *lemma* nat.of_digits_digits_append_digits
- \+ *lemma* nat.of_digits_eq_foldr
- \+ *lemma* nat.of_digits_lt_base_pow_length'
- \+ *lemma* nat.of_digits_lt_base_pow_length
- \+ *lemma* nat.of_digits_mod
- \+ *lemma* nat.of_digits_modeq'
- \+ *lemma* nat.of_digits_modeq
- \+ *lemma* nat.of_digits_neg_one
- \+ *lemma* nat.of_digits_one
- \+ *lemma* nat.of_digits_one_cons
- \+ *lemma* nat.of_digits_singleton
- \+ *lemma* nat.of_digits_zmod
- \+ *lemma* nat.of_digits_zmodeq'
- \+ *lemma* nat.of_digits_zmodeq
- \+ *lemma* nat.pow_length_le_mul_of_digits
- \+ *lemma* nat.three_dvd_iff
- \+ *lemma* nat.zmodeq_of_digits_digits
- \- *lemma* nine_dvd_iff
- \- *def* of_digits
- \- *lemma* of_digits_append
- \- *lemma* of_digits_digits
- \- *lemma* of_digits_digits_append_digits
- \- *lemma* of_digits_eq_foldr
- \- *lemma* of_digits_lt_base_pow_length'
- \- *lemma* of_digits_lt_base_pow_length
- \- *lemma* of_digits_mod
- \- *lemma* of_digits_modeq'
- \- *lemma* of_digits_modeq
- \- *lemma* of_digits_neg_one
- \- *lemma* of_digits_one
- \- *lemma* of_digits_one_cons
- \- *lemma* of_digits_singleton
- \- *lemma* of_digits_zmod
- \- *lemma* of_digits_zmodeq'
- \- *lemma* of_digits_zmodeq
- \- *lemma* pow_length_le_mul_of_digits
- \- *lemma* three_dvd_iff
- \- *lemma* zmodeq_of_digits_digits



## [2020-09-21 13:06:58](https://github.com/leanprover-community/mathlib/commit/4a8c38e)
chore(category_theory/limits/lattice): cleanup ([#4191](https://github.com/leanprover-community/mathlib/pull/4191))
#### Estimated changes
Modified src/category_theory/limits/lattice.lean
- \+ *def* category_theory.limits.complete_lattice.colimit_cocone
- \+ *def* category_theory.limits.complete_lattice.colimit_iso_supr
- \+ *lemma* category_theory.limits.complete_lattice.colimit_iso_supr_hom
- \+ *lemma* category_theory.limits.complete_lattice.colimit_iso_supr_inv
- \+ *def* category_theory.limits.complete_lattice.limit_cone
- \+ *def* category_theory.limits.complete_lattice.limit_iso_infi
- \+ *lemma* category_theory.limits.complete_lattice.limit_iso_infi_hom
- \+ *lemma* category_theory.limits.complete_lattice.limit_iso_infi_inv



## [2020-09-21 10:21:23](https://github.com/leanprover-community/mathlib/commit/cd4a91f)
fix(scripts/mk_all): macOS compatibility fix ([#4148](https://github.com/leanprover-community/mathlib/pull/4148))
`readlink -f` doesn't work macOS unfortunately - there are alternatives but I think it's probably safe to remove it altogether? This assumes `mk_all.sh` isn't a symlink but I can't think of a reason why it should be - and `rm_all.sh` uses `dirname "${BASH_SOURCE[0]}"` directly 🙂
#### Estimated changes
Modified scripts/mk_all.sh




## [2020-09-21 08:37:54](https://github.com/leanprover-community/mathlib/commit/e483298)
feat(ring_theory/unique_factorization_domain): API for coprime, coprime factor of a power is a power ([#4049](https://github.com/leanprover-community/mathlib/pull/4049))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.exists_non_zero_rep
- \+ *lemma* associates.exists_rep

Modified src/algebra/big_operators/basic.lean
- \+ *lemma* multiset.count_sum'
- \+ *theorem* multiset.exists_smul_of_dvd_count
- \+ *lemma* multiset.to_finset_sum_count_smul_eq

Modified src/algebra/group_with_zero_power.lean
- \+/\- *theorem* pow_eq_zero'
- \+/\- *theorem* pow_ne_zero'

Modified src/data/list/basic.lean
- \+/\- *lemma* list.dvd_prod

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.count_sum
- \+/\- *lemma* multiset.dvd_prod
- \+ *theorem* multiset.map_repeat

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* associates.associates_irreducible_iff_prime
- \+ *def* associates.bcount
- \+ *def* associates.bfactor_set_mem
- \+ *theorem* associates.coprime_iff_inf_one
- \+ *def* associates.count
- \+ *theorem* associates.count_mul
- \+ *theorem* associates.count_mul_of_coprime'
- \+ *theorem* associates.count_mul_of_coprime
- \+ *theorem* associates.count_of_coprime
- \+ *lemma* associates.count_pow
- \+ *lemma* associates.count_reducible
- \+ *lemma* associates.count_some
- \+ *lemma* associates.count_zero
- \+ *theorem* associates.dvd_count_of_dvd_count_mul
- \+ *theorem* associates.dvd_count_pow
- \+ *lemma* associates.dvd_of_mem_factors'
- \+ *lemma* associates.dvd_of_mem_factors
- \+ *theorem* associates.eq_pow_of_mul_eq_pow
- \+ *lemma* associates.exists_prime_dvd_of_not_inf_one
- \+ *def* associates.factor_set_mem
- \+ *lemma* associates.factor_set_mem_eq_mem
- \+ *lemma* associates.factors_one
- \+ *theorem* associates.factors_prime_pow
- \+ *theorem* associates.is_pow_of_dvd_count
- \+ *theorem* associates.le_of_count_ne_zero
- \+ *lemma* associates.mem_factor_set_some
- \+ *lemma* associates.mem_factor_set_top
- \+ *lemma* associates.mem_factors'_iff_dvd
- \+ *lemma* associates.mem_factors'_of_dvd
- \+ *lemma* associates.mem_factors_iff_dvd
- \+ *lemma* associates.mem_factors_of_dvd
- \+ *theorem* associates.pow_factors
- \+ *theorem* associates.prime_pow_dvd_iff_le
- \+ *lemma* associates.reducible_not_mem_factor_set
- \+ *theorem* coprime_iff_gcd_eq_one
- \+ *lemma* exists_prime_dvd_of_gcd_ne_one



## [2020-09-21 06:08:33](https://github.com/leanprover-community/mathlib/commit/40f582b)
feat(data/*/nat_antidiagonal): induction lemmas about antidiagonals ([#4193](https://github.com/leanprover-community/mathlib/pull/4193))
Adds a `nat.antidiagonal_succ` lemma for `list`, `multiset`, and `finset`, useful for proving facts about power series derivatives
#### Estimated changes
Modified src/algebra/big_operators/default.lean


Added src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* finset.nat.sum_antidiagonal_succ

Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* finset.nat.antidiagonal_succ
- \+ *lemma* finset.nat.map_swap_antidiagonal

Modified src/data/list/nat_antidiagonal.lean
- \+ *lemma* list.nat.antidiagonal_succ

Modified src/data/multiset/nat_antidiagonal.lean
- \+ *lemma* multiset.nat.antidiagonal_succ



## [2020-09-21 03:23:12](https://github.com/leanprover-community/mathlib/commit/d8e7bb5)
feat(tactic/tauto): optional closer tactic for `tauto` ([#4189](https://github.com/leanprover-community/mathlib/pull/4189))
`tauto` sometimes fails on easy subgoals; instead of backtracking
and discarding the work, the user can now supply a closer tactic
to the remaining goals, such as `cc`, `simp`, or `linarith`.
this also wraps `tauto` in a `focus1`, which allows for better
error messages.
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/tactic/tauto.lean


Modified src/tactic/wlog.lean


Modified test/tauto.lean




## [2020-09-20 23:55:02](https://github.com/leanprover-community/mathlib/commit/f77d5d6)
feat(data/finset): add lemma for empty filter ([#4188](https://github.com/leanprover-community/mathlib/pull/4188))
A little lemma, analogous to `filter_true_of_mem` to make it convenient to reduce a filter which always fails.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.filter_false_of_mem

Modified src/data/monoid_algebra.lean




## [2020-09-20 21:53:36](https://github.com/leanprover-community/mathlib/commit/db9842c)
feat(analysis/calculus/times_cont_diff): inversion of continuous linear maps is smooth ([#4185](https://github.com/leanprover-community/mathlib/pull/4185))
- Introduce an `inverse` function on the space of continuous linear maps between two Banach spaces, which is the inverse if the map is a continuous linear equivalence and zero otherwise.
- Prove that this function is `times_cont_diff_at` each `continuous_linear_equiv`.
- Some of the constructions used had been introduced in [#3282](https://github.com/leanprover-community/mathlib/pull/3282) and placed in `analysis.normed_space.operator_norm` (normed spaces); they are moved to the earlier file `topology.algebra.module` (topological vector spaces).
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring.inverse_non_unit
- \+/\- *lemma* ring.inverse_unit

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable_at_inverse
- \- *lemma* has_fderiv_at_inverse
- \+ *lemma* has_fderiv_at_ring_inverse

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at.prod
- \- *lemma* times_cont_diff_at_inverse
- \+ *lemma* times_cont_diff_at_map_inverse
- \+ *lemma* times_cont_diff_at_ring_inverse

Modified src/analysis/normed_space/operator_norm.lean
- \- *def* continuous_linear_equiv.of_unit
- \- *def* continuous_linear_equiv.to_unit
- \- *def* continuous_linear_equiv.units_equiv
- \- *lemma* continuous_linear_equiv.units_equiv_to_continuous_linear_map

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.comp_coe
- \+ *def* continuous_linear_equiv.of_unit
- \+ *lemma* continuous_linear_equiv.refl_symm
- \+ *theorem* continuous_linear_equiv.symm_trans_apply
- \+ *def* continuous_linear_equiv.to_unit
- \+ *theorem* continuous_linear_equiv.trans_apply
- \+ *def* continuous_linear_equiv.units_equiv
- \+ *lemma* continuous_linear_equiv.units_equiv_apply
- \+ *lemma* continuous_linear_map.inverse_equiv
- \+ *lemma* continuous_linear_map.inverse_non_equiv
- \+ *lemma* continuous_linear_map.ring_inverse_eq_map_inverse
- \+ *lemma* continuous_linear_map.ring_inverse_equiv
- \+ *lemma* continuous_linear_map.to_ring_inverse



## [2020-09-20 21:53:34](https://github.com/leanprover-community/mathlib/commit/d774ef6)
feat(topology/path_connected): add lemmas about paths and continuous families of paths ([#4063](https://github.com/leanprover-community/mathlib/pull/4063))
From the sphere eversion project (see https://github.com/leanprover-community/sphere-eversion/pull/12)
#### Estimated changes
Modified src/topology/path_connected.lean
- \+ *lemma* is_path_connected.exists_path_through_family'
- \+ *lemma* is_path_connected.exists_path_through_family
- \+ *lemma* path.continuous_uncurry_extend_of_continuous_family
- \+ *lemma* path.extend_extends'
- \+ *lemma* path.extend_extends
- \+ *lemma* path.extend_le_zero
- \+ *lemma* path.extend_one_le
- \+ *lemma* path.extend_range
- \+ *lemma* path.refl_extend
- \+ *lemma* path.refl_range
- \+ *lemma* path.refl_symm
- \+ *lemma* path.refl_trans_refl
- \+ *lemma* path.symm_cast
- \+ *lemma* path.symm_continuous_family
- \+ *lemma* path.symm_range
- \+ *lemma* path.trans_cast
- \+ *lemma* path.trans_continuous_family
- \+ *lemma* path.trans_range
- \+ *def* path.truncate
- \+ *lemma* path.truncate_const_continuous_family
- \+ *lemma* path.truncate_continuous_family
- \+ *def* path.truncate_of_le
- \+ *lemma* path.truncate_one_one
- \+ *lemma* path.truncate_range
- \+ *lemma* path.truncate_self
- \+ *lemma* path.truncate_zero_one
- \+ *lemma* path.truncate_zero_zero
- \+ *lemma* path_connected_space.exists_path_through_family'
- \+ *lemma* path_connected_space.exists_path_through_family
- \+ *lemma* proj_I_one
- \+ *lemma* proj_I_zero



## [2020-09-20 20:05:32](https://github.com/leanprover-community/mathlib/commit/884e90b)
feat(measure_theory): Borel-Cantelli ([#4166](https://github.com/leanprover-community/mathlib/pull/4166))
```lean
lemma measure_limsup_eq_zero {s : ℕ → set α} (hs : ∀ i, is_measurable (s i))
  (hs' : (∑' i, μ (s i)) ≠ ⊤) : μ (limsup at_top s) = 0
```
There is a converse statement that is also called Borel-Cantelli, but we can't state it yet, because we don't know what independent events are.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.sub_eq_iff_eq_add
- \+ *lemma* nnreal.sub_lt_iff_lt_add

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_eventually_not_mem
- \+ *lemma* measure_theory.measure_limsup_eq_zero

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_ge_eq_infi_nat_add
- \+ *lemma* supr_ge_eq_supr_nat_add

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.liminf_eq_supr_infi_of_nat'
- \+ *lemma* filter.limsup_eq_infi_supr_of_nat'

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_zero_iff
- \+ *lemma* le_has_sum'
- \+ *lemma* le_has_sum
- \+ *lemma* le_tsum'
- \+ *lemma* le_tsum
- \+ *lemma* tsum_eq_zero_iff

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.summable_to_nnreal_of_tsum_ne_top
- \+ *lemma* ennreal.tendsto_sum_nat_add
- \+ *lemma* ennreal.to_nnreal_apply_of_tsum_ne_top
- \+ *lemma* nnreal.tendsto_sum_nat_add

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.sum_add_tsum_nat_add
- \+ *lemma* nnreal.summable_nat_add



## [2020-09-20 16:28:24](https://github.com/leanprover-community/mathlib/commit/2c9b063)
feat(algebra/big_operators): add prod boole lemma ([#4192](https://github.com/leanprover-community/mathlib/pull/4192))
A small lemma to simplify products of indicator functions
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_boole



## [2020-09-20 00:47:20](https://github.com/leanprover-community/mathlib/commit/44667ba)
feat(ring_theory/power_series): power series lemmas ([#4171](https://github.com/leanprover-community/mathlib/pull/4171))
A couple of little lemmas for multiplication and coefficients
#### Estimated changes
Modified src/ring_theory/power_series.lean
- \+ *lemma* mv_power_series.coeff_C_mul
- \+ *lemma* mv_power_series.coeff_smul
- \+ *lemma* power_series.coeff_C_mul
- \+ *lemma* power_series.coeff_smul



## [2020-09-20 00:00:33](https://github.com/leanprover-community/mathlib/commit/9232032)
refactor(linear_algebra/tensor_algebra): build as a quotient of a free algebra ([#4079](https://github.com/leanprover-community/mathlib/pull/4079))
#### Estimated changes
Modified src/linear_algebra/tensor_algebra.lean
- \+/\- *theorem* tensor_algebra.hom_ext
- \- *def* tensor_algebra.lift_fun
- \+ *theorem* tensor_algebra.lift_ι_apply
- \- *def* tensor_algebra.pre.has_add
- \- *def* tensor_algebra.pre.has_coe_module
- \- *def* tensor_algebra.pre.has_coe_semiring
- \- *def* tensor_algebra.pre.has_mul
- \- *def* tensor_algebra.pre.has_one
- \- *def* tensor_algebra.pre.has_scalar
- \- *def* tensor_algebra.pre.has_zero
- \+ *lemma* tensor_algebra.ring_quot_mk_alg_hom_free_algebra_ι_eq_ι
- \+/\- *def* tensor_algebra



## [2020-09-19 23:11:09](https://github.com/leanprover-community/mathlib/commit/7013e5b)
feat(category_theory/internal): commutative monoid objects ([#4186](https://github.com/leanprover-community/mathlib/pull/4186))
This reprises a series of our recent PRs on monoid objects in monoidal categories, developing the same material for commutative monoid objects in braided categories.
#### Estimated changes
Modified src/category_theory/monad/equiv_mon.lean


Added src/category_theory/monoidal/CommMon_.lean
- \+ *lemma* CommMon_.comp_hom
- \+ *def* CommMon_.equiv_lax_braided_functor_punit.CommMon_to_lax_braided
- \+ *def* CommMon_.equiv_lax_braided_functor_punit.counit_iso
- \+ *def* CommMon_.equiv_lax_braided_functor_punit.lax_braided_to_CommMon
- \+ *def* CommMon_.equiv_lax_braided_functor_punit.unit_iso
- \+ *def* CommMon_.equiv_lax_braided_functor_punit
- \+ *def* CommMon_.forget₂_Mon_
- \+ *lemma* CommMon_.forget₂_Mon_map_hom
- \+ *lemma* CommMon_.forget₂_Mon_obj_mul
- \+ *lemma* CommMon_.forget₂_Mon_obj_one
- \+ *lemma* CommMon_.id_hom
- \+ *def* CommMon_.trivial
- \+ *def* category_theory.lax_braided_functor.map_CommMon
- \+ *def* category_theory.lax_braided_functor.map_CommMon_functor

Added src/category_theory/monoidal/Mod.lean
- \+ *lemma* Mod.assoc_flip
- \+ *def* Mod.comap
- \+ *def* Mod.comp
- \+ *lemma* Mod.comp_hom'
- \+ *def* Mod.forget
- \+ *def* Mod.id
- \+ *lemma* Mod.id_hom'
- \+ *def* Mod.regular

Renamed src/category_theory/monoidal/internal.lean to src/category_theory/monoidal/Mon_.lean
- \- *lemma* Mod.assoc_flip
- \- *def* Mod.comap
- \- *def* Mod.comp
- \- *lemma* Mod.comp_hom'
- \- *def* Mod.forget
- \- *def* Mod.id
- \- *lemma* Mod.id_hom'
- \- *def* Mod.regular

Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* category_theory.braided_functor.comp_to_nat_trans
- \+ *def* category_theory.braided_functor.mk_iso
- \+ *def* category_theory.braided_functor.to_lax_braided_functor
- \+ *def* category_theory.discrete.braided_functor
- \+ *def* category_theory.lax_braided_functor.comp
- \+ *lemma* category_theory.lax_braided_functor.comp_to_nat_trans
- \+ *def* category_theory.lax_braided_functor.id
- \+ *def* category_theory.lax_braided_functor.mk_iso

Modified src/category_theory/monoidal/discrete.lean


Modified src/category_theory/monoidal/functor_category.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/monoidal/internal/functor_category.lean
- \+ *def* category_theory.monoidal.CommMon_functor_category_equivalence.counit_iso
- \+ *def* category_theory.monoidal.CommMon_functor_category_equivalence.functor
- \+ *def* category_theory.monoidal.CommMon_functor_category_equivalence.inverse
- \+ *def* category_theory.monoidal.CommMon_functor_category_equivalence.unit_iso
- \+ *def* category_theory.monoidal.CommMon_functor_category_equivalence

Modified src/category_theory/monoidal/internal/types.lean
- \+ *def* CommMon_Type_equivalence_CommMon.functor
- \+ *def* CommMon_Type_equivalence_CommMon.inverse
- \+ *def* CommMon_Type_equivalence_CommMon
- \+ *def* CommMon_Type_equivalence_CommMon_forget

Modified src/category_theory/monoidal/types.lean
- \+ *lemma* category_theory.monoidal.braiding_hom_apply
- \+ *lemma* category_theory.monoidal.braiding_inv_apply



## [2020-09-19 20:26:57](https://github.com/leanprover-community/mathlib/commit/5b143ff)
feat(data/set/basic): a few lemmas ([#4184](https://github.com/leanprover-community/mathlib/pull/4184))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.image_union_image_compl_eq_range
- \+ *theorem* set.inter_union_compl



## [2020-09-19 19:45:22](https://github.com/leanprover-community/mathlib/commit/640ba6c)
feat(geometry/euclidean): cospherical points ([#4178](https://github.com/leanprover-community/mathlib/pull/4178))
Define cospherical points in a Euclidean space (the general-dimension
version of the two-dimensional concept of a set of points being
concyclic) and prove some very basic lemmas about them.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *def* euclidean_geometry.cospherical
- \+ *lemma* euclidean_geometry.cospherical_def
- \+ *lemma* euclidean_geometry.cospherical_empty
- \+ *lemma* euclidean_geometry.cospherical_insert_singleton
- \+ *lemma* euclidean_geometry.cospherical_singleton
- \+ *lemma* euclidean_geometry.cospherical_subset

Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* euclidean_geometry.circumcenter_eq_of_cospherical
- \+ *lemma* euclidean_geometry.circumcenter_eq_of_cospherical_subset
- \+ *lemma* euclidean_geometry.circumradius_eq_of_cospherical
- \+ *lemma* euclidean_geometry.circumradius_eq_of_cospherical_subset
- \+ *lemma* euclidean_geometry.cospherical_iff_exists_mem_of_complete
- \+ *lemma* euclidean_geometry.cospherical_iff_exists_mem_of_finite_dimensional
- \+ *lemma* euclidean_geometry.exists_circumcenter_eq_of_cospherical
- \+ *lemma* euclidean_geometry.exists_circumcenter_eq_of_cospherical_subset
- \+ *lemma* euclidean_geometry.exists_circumradius_eq_of_cospherical
- \+ *lemma* euclidean_geometry.exists_circumradius_eq_of_cospherical_subset



## [2020-09-19 19:03:21](https://github.com/leanprover-community/mathlib/commit/02b492a)
feat(category_theory/Mon): Mon_ C has limits when C does ([#4133](https://github.com/leanprover-community/mathlib/pull/4133))
If `C` has limits, so does `Mon_ C`.
(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)
#### Estimated changes
Modified src/category_theory/functorial.lean
- \+ *lemma* category_theory.functorial.map_comp
- \+ *lemma* category_theory.functorial.map_id
- \+ *lemma* category_theory.map_as_map

Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/internal.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/monoidal/internal/functor_category.lean


Added src/category_theory/monoidal/internal/limits.lean
- \+ *def* Mon_.forget_map_cone_limit_cone_iso
- \+ *def* Mon_.limit
- \+ *def* Mon_.limit_cone
- \+ *def* Mon_.limit_cone_is_limit

Modified src/category_theory/monoidal/limits.lean
- \+ *lemma* category_theory.limits.lim_lax_ε
- \+ *lemma* category_theory.limits.lim_lax_μ



## [2020-09-19 04:51:22](https://github.com/leanprover-community/mathlib/commit/567954f)
feat(category_theory): `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is monoidal ([#4132](https://github.com/leanprover-community/mathlib/pull/4132))
A step towards constructing limits in `Mon_ C` (and thence towards sheaves of modules as internal objects).
#### Estimated changes
Added src/category_theory/monoidal/limits.lean
- \+ *def* category_theory.limits.lim_lax
- \+ *lemma* category_theory.limits.lim_lax_map
- \+ *lemma* category_theory.limits.lim_lax_obj'
- \+ *lemma* category_theory.limits.lim_lax_obj
- \+ *lemma* category_theory.limits.limit_functorial_map



## [2020-09-19 03:33:07](https://github.com/leanprover-community/mathlib/commit/04fe4b6)
feat(algebra/ring_quot): quotients of noncommutative rings ([#4078](https://github.com/leanprover-community/mathlib/pull/4078))
#### Estimated changes
Added src/algebra/ring_quot.lean
- \+ *lemma* ring_quot.eq_lift_alg_hom_comp_mk_alg_hom
- \+ *lemma* ring_quot.eq_lift_comp_mk_ring_hom
- \+ *def* ring_quot.ideal_quotient_to_ring_quot
- \+ *lemma* ring_quot.ideal_quotient_to_ring_quot_apply
- \+ *def* ring_quot.lift
- \+ *def* ring_quot.lift_alg_hom
- \+ *lemma* ring_quot.lift_alg_hom_mk_alg_hom_apply
- \+ *lemma* ring_quot.lift_alg_hom_unique
- \+ *lemma* ring_quot.lift_mk_ring_hom_apply
- \+ *lemma* ring_quot.lift_unique
- \+ *def* ring_quot.mk_alg_hom
- \+ *lemma* ring_quot.mk_alg_hom_coe
- \+ *lemma* ring_quot.mk_alg_hom_rel
- \+ *lemma* ring_quot.mk_alg_hom_surjective
- \+ *def* ring_quot.mk_ring_hom
- \+ *lemma* ring_quot.mk_ring_hom_rel
- \+ *lemma* ring_quot.mk_ring_hom_surjective
- \+ *theorem* ring_quot.rel.add_right
- \+ *theorem* ring_quot.rel.neg
- \+ *theorem* ring_quot.rel.smul
- \+ *def* ring_quot.ring_quot_equiv_ideal_quotient
- \+ *lemma* ring_quot.ring_quot_ext'
- \+ *lemma* ring_quot.ring_quot_ext
- \+ *def* ring_quot.ring_quot_to_ideal_quotient
- \+ *lemma* ring_quot.ring_quot_to_ideal_quotient_apply
- \+ *def* ring_quot

Modified src/data/equiv/ring.lean
- \+ *def* ring_equiv.of_hom_inv
- \+ *lemma* ring_equiv.of_hom_inv_apply
- \+ *lemma* ring_equiv.of_hom_inv_symm_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.mem_Inf

Modified src/ring_theory/ideal/basic.lean
- \+ *def* ideal.of_rel



## [2020-09-18 21:57:43](https://github.com/leanprover-community/mathlib/commit/bf7a2ed)
fix(conditionally_complete_lattice): add instance ([#4183](https://github.com/leanprover-community/mathlib/pull/4183))
there was no instance from `conditionally_complete_linear_order_bot` to `conditionally_complete_linear_order`. It is added by this change.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean




## [2020-09-18 21:57:41](https://github.com/leanprover-community/mathlib/commit/c2ae6c0)
doc(simps): explain short_name ([#4182](https://github.com/leanprover-community/mathlib/pull/4182))
#### Estimated changes
Modified src/tactic/simps.lean




## [2020-09-18 21:57:39](https://github.com/leanprover-community/mathlib/commit/0269a76)
feat(integration): integral commutes with continuous linear maps ([#4167](https://github.com/leanprover-community/mathlib/pull/4167))
from the sphere eversion project. Main result:
```lean
continuous_linear_map.integral_apply_comm {α : Type*} [measurable_space α] {μ : measure α} 
  {E : Type*} [normed_group E]  [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E] {F : Type*} [normed_group F]
  [second_countable_topology F] [normed_space ℝ F] [complete_space F]
  [measurable_space F] [borel_space F] 
  {φ : α → E} (L : E →L[ℝ] F) (φ_meas : measurable φ) (φ_int : integrable φ μ) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ)
```
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \- *lemma* continuous_linear_map.measurable
- \+ *lemma* continuous_linear_map.measurable_comp
- \- *lemma* measurable.clm_apply

Modified src/measure_theory/set_integral.lean
- \+ *def* continuous_linear_map.comp_l1
- \+ *def* continuous_linear_map.comp_l1L
- \+ *lemma* continuous_linear_map.comp_l1_apply
- \+ *def* continuous_linear_map.comp_l1ₗ
- \+ *lemma* continuous_linear_map.continuous_integral_comp_l1
- \+ *lemma* continuous_linear_map.integrable_comp
- \+ *lemma* continuous_linear_map.integrable_comp_l1
- \+ *lemma* continuous_linear_map.integral_comp_comm
- \+ *lemma* continuous_linear_map.integral_comp_l1
- \+ *lemma* continuous_linear_map.integral_comp_l1_comm
- \+ *lemma* continuous_linear_map.measurable_comp_l1
- \+ *lemma* continuous_linear_map.norm_comp_l1_apply_le
- \+ *lemma* continuous_linear_map.norm_comp_l1_le
- \+ *lemma* continuous_linear_map.norm_compl1L_le
- \+/\- *lemma* measure_theory.integrable.induction



## [2020-09-18 20:21:39](https://github.com/leanprover-community/mathlib/commit/4e3729b)
feat(geometry/euclidean/basic): intersections of circles ([#4088](https://github.com/leanprover-community/mathlib/pull/4088))
Add two versions of the statement that two circles in two-dimensional
space intersect in at most two points, along with some lemmas involved
in the proof (some of which can be interpreted in terms of
intersections of circles or spheres and lines).
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.dist_smul_vadd_eq_dist
- \+ *lemma* euclidean_geometry.dist_smul_vadd_square
- \+ *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_findim_eq_two
- \+ *lemma* euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two
- \+ *lemma* euclidean_geometry.inner_vsub_vsub_of_dist_eq_of_dist_eq



## [2020-09-18 17:25:27](https://github.com/leanprover-community/mathlib/commit/9051aa7)
feat(polynomial): prepare for transcendence of e by adding small lemmas ([#4175](https://github.com/leanprover-community/mathlib/pull/4175))
This will be a series of pull request to prepare for the proof of transcendence of e by adding lots of small lemmas.
#### Estimated changes
Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.not_mem_support_iff_coeff_zero

Modified src/data/polynomial/degree.lean
- \+ *lemma* polynomial.eq_C_of_nat_degree_eq_zero

Modified src/data/polynomial/derivative.lean
- \+ *theorem* polynomial.nat_degree_eq_zero_of_derivative_eq_zero



## [2020-09-18 11:37:08](https://github.com/leanprover-community/mathlib/commit/ae72826)
feat(data/mv_polynomial): define comap ([#4161](https://github.com/leanprover-community/mathlib/pull/4161))
More from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/category/CommRing/adjunctions.lean


Added src/data/mv_polynomial/comap.lean
- \+ *lemma* mv_polynomial.comap_apply
- \+ *lemma* mv_polynomial.comap_comp
- \+ *lemma* mv_polynomial.comap_comp_apply
- \+ *lemma* mv_polynomial.comap_eq_id_of_eq_id
- \+ *lemma* mv_polynomial.comap_equiv_coe
- \+ *lemma* mv_polynomial.comap_equiv_symm_coe
- \+ *lemma* mv_polynomial.comap_id
- \+ *lemma* mv_polynomial.comap_id_apply
- \+ *lemma* mv_polynomial.comap_rename

Modified src/data/mv_polynomial/rename.lean
- \+/\- *def* mv_polynomial.rename



## [2020-09-18 09:43:35](https://github.com/leanprover-community/mathlib/commit/953a5dc)
feat(category_theory/monoidal): monoid objects are just lax monoidal functors from punit ([#4121](https://github.com/leanprover-community/mathlib/pull/4121))
#### Estimated changes
Modified src/category_theory/monoidal/internal.lean
- \+ *def* Mon_.equiv_lax_monoidal_functor_punit.Mon_to_lax_monoidal
- \+ *def* Mon_.equiv_lax_monoidal_functor_punit.counit_iso
- \+ *def* Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon
- \+ *def* Mon_.equiv_lax_monoidal_functor_punit.unit_iso
- \+ *def* Mon_.equiv_lax_monoidal_functor_punit

Modified src/category_theory/monoidal/natural_transformation.lean
- \+ *lemma* category_theory.monoidal_nat_iso.of_components.hom_app
- \+ *lemma* category_theory.monoidal_nat_iso.of_components.inv_app
- \+ *def* category_theory.monoidal_nat_iso.of_components
- \+ *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans''
- \+ *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans'

Modified src/category_theory/natural_isomorphism.lean




## [2020-09-18 08:44:32](https://github.com/leanprover-community/mathlib/commit/c158ce8)
feat(analysis/calculus): converse mean value inequality  ([#4173](https://github.com/leanprover-community/mathlib/pull/4173))
Also restate mean value inequality in terms of `lipschitz_on_with`.
From the sphere eversion project.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_at.le_of_lip
- \+ *lemma* has_fderiv_at.le_of_lip

Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.lipschitz_on_with_of_norm_deriv_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_fderiv_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_has_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_has_fderiv_within_le

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_on_with_empty



## [2020-09-18 08:44:30](https://github.com/leanprover-community/mathlib/commit/f68c936)
feat(analysis/normed_space/real_inner_product): orthogonal subspace lemmas ([#4152](https://github.com/leanprover-community/mathlib/pull/4152))
Add a few more lemmas about `submodule.orthogonal`.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* submodule.findim_add_inf_findim_orthogonal
- \+ *lemma* submodule.orthogonal_le
- \+ *lemma* submodule.sup_orthogonal_inf_of_is_complete



## [2020-09-18 08:44:28](https://github.com/leanprover-community/mathlib/commit/b00b01f)
feat(linear_algebra/affine_space): more lemmas ([#4127](https://github.com/leanprover-community/mathlib/pull/4127))
Add another batch of lemmas relating to affine spaces.  These include
factoring out `vector_span_mono` as a combination of two other lemmas
that's used several times, and additional variants of lemmas relating
to finite-dimensional subspaces.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_subspace.eq_iff_direction_eq_of_mem
- \+ *lemma* affine_subspace.eq_of_direction_eq_of_nonempty_of_le
- \+ *lemma* vector_span_mono

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* findim_vector_span_image_finset_of_affine_independent
- \+ *lemma* vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one



## [2020-09-18 07:44:06](https://github.com/leanprover-community/mathlib/commit/43ff7dc)
feat(topology/algebra/ordered): generalize two lemmas ([#4177](https://github.com/leanprover-community/mathlib/pull/4177))
they hold for conditionally complete linear orders, not just for complete linear orders
#### Estimated changes
Modified src/topology/algebra/ordered.lean




## [2020-09-18 05:39:35](https://github.com/leanprover-community/mathlib/commit/58883e3)
feat(topology/ωCPO): define Scott topology in connection with ω-complete partial orders ([#4037](https://github.com/leanprover-community/mathlib/pull/4037))
#### Estimated changes
Modified src/control/lawful_fix.lean


Modified src/order/basic.lean
- \+ *def* as_linear_order

Modified src/order/bounded_lattice.lean
- \+ *lemma* le_iff_imp

Modified src/order/complete_lattice.lean
- \+ *theorem* Inf_le_Inf_of_forall_exists_le
- \+ *theorem* Sup_le_Sup_of_forall_exists_le

Modified src/order/lattice.lean
- \+ *lemma* inf_le_iff
- \+ *lemma* le_sup_iff

Modified src/order/omega_complete_partial_order.lean
- \+ *theorem* complete_lattice.Sup_continuous'
- \+ *lemma* complete_lattice.Sup_continuous
- \+ *lemma* complete_lattice.bot_continuous
- \+ *lemma* complete_lattice.inf_continuous
- \+ *lemma* complete_lattice.sup_continuous
- \+ *lemma* complete_lattice.top_continuous
- \+ *lemma* omega_complete_partial_order.continuous_hom.monotone

Modified src/order/preorder_hom.lean
- \+ *lemma* preorder_hom.monotone

Modified src/tactic/monotonicity/basic.lean


Added src/topology/omega_complete_partial_order.lean
- \+ *def* Scott.is_open
- \+ *theorem* Scott.is_open_inter
- \+ *theorem* Scott.is_open_sUnion
- \+ *theorem* Scott.is_open_univ
- \+ *def* Scott.is_ωSup
- \+ *def* Scott
- \+ *lemma* Scott_continuous_of_continuous
- \+ *lemma* continuous_of_Scott_continuous
- \+ *lemma* is_ωSup_ωSup
- \+ *def* not_below
- \+ *lemma* not_below_is_open



## [2020-09-18 00:57:16](https://github.com/leanprover-community/mathlib/commit/52d4b92)
chore(scripts): update nolints.txt ([#4176](https://github.com/leanprover-community/mathlib/pull/4176))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-17 15:33:38](https://github.com/leanprover-community/mathlib/commit/5a2e7d7)
refactor(field-theory/subfield): bundled subfields ([#4159](https://github.com/leanprover-community/mathlib/pull/4159))
Define bundled subfields. The contents of the new `subfield` file are basically a copy of `subring.lean` with the replacement `subring` -> `subfield`, and the proofs repaired as necessary.
As with the other bundled subobject refactors, other files depending on unbundled subfields now import `deprecated.subfield`.
#### Estimated changes
Added src/deprecated/subfield.lean
- \+ *def* field.closure
- \+ *theorem* field.closure_mono
- \+ *theorem* field.closure_subset
- \+ *theorem* field.closure_subset_iff
- \+ *theorem* field.mem_closure
- \+ *theorem* field.ring_closure_subset
- \+ *theorem* field.subset_closure
- \+ *lemma* is_subfield_Union_of_directed

Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/subfield.lean
- \- *def* field.closure
- \- *theorem* field.closure_mono
- \- *theorem* field.closure_subset
- \- *theorem* field.closure_subset_iff
- \- *theorem* field.mem_closure
- \- *theorem* field.ring_closure_subset
- \- *theorem* field.subset_closure
- \- *lemma* is_subfield_Union_of_directed
- \+ *def* ring_equiv.subfield_congr
- \+ *def* ring_hom.cod_restrict_field
- \+ *lemma* ring_hom.coe_field_range
- \+ *lemma* ring_hom.coe_range_restrict_field
- \+ *def* ring_hom.eq_locus_field
- \+ *lemma* ring_hom.eq_of_eq_on_of_field_closure_eq_top
- \+ *lemma* ring_hom.eq_of_eq_on_subfield_top
- \+ *lemma* ring_hom.eq_on_field_closure
- \+ *lemma* ring_hom.field_closure_preimage_le
- \+ *def* ring_hom.field_range
- \+ *lemma* ring_hom.map_field_closure
- \+ *lemma* ring_hom.map_field_range
- \+ *lemma* ring_hom.mem_field_range
- \+ *def* ring_hom.range_restrict_field
- \+ *def* ring_hom.restrict_field
- \+ *lemma* ring_hom.restrict_field_apply
- \+ *lemma* subfield.Inf_to_subring
- \+ *theorem* subfield.add_mem
- \+ *def* subfield.closure
- \+ *lemma* subfield.closure_Union
- \+ *lemma* subfield.closure_empty
- \+ *lemma* subfield.closure_eq
- \+ *lemma* subfield.closure_eq_of_le
- \+ *lemma* subfield.closure_induction
- \+ *lemma* subfield.closure_le
- \+ *lemma* subfield.closure_mono
- \+ *lemma* subfield.closure_preimage_le
- \+ *lemma* subfield.closure_sUnion
- \+ *lemma* subfield.closure_union
- \+ *lemma* subfield.closure_univ
- \+ *lemma* subfield.coe_Inf
- \+ *lemma* subfield.coe_Sup_of_directed_on
- \+ *lemma* subfield.coe_add
- \+ *lemma* subfield.coe_coe
- \+ *lemma* subfield.coe_comap
- \+ *lemma* subfield.coe_inf
- \+ *lemma* subfield.coe_int_mem
- \+ *lemma* subfield.coe_inv
- \+ *lemma* subfield.coe_map
- \+ *lemma* subfield.coe_mul
- \+ *lemma* subfield.coe_neg
- \+ *lemma* subfield.coe_one
- \+ *lemma* subfield.coe_ssubset_coe
- \+ *lemma* subfield.coe_subset_coe
- \+ *theorem* subfield.coe_subtype
- \+ *lemma* subfield.coe_supr_of_directed
- \+ *lemma* subfield.coe_to_add_subgroup
- \+ *lemma* subfield.coe_to_submonoid
- \+ *lemma* subfield.coe_to_subring
- \+ *lemma* subfield.coe_top
- \+ *lemma* subfield.coe_zero
- \+ *def* subfield.comap
- \+ *lemma* subfield.comap_comap
- \+ *lemma* subfield.comap_inf
- \+ *lemma* subfield.comap_infi
- \+ *lemma* subfield.comap_top
- \+ *theorem* subfield.div_mem
- \+ *theorem* subfield.ext'
- \+ *theorem* subfield.ext
- \+ *lemma* subfield.field_range_subtype
- \+ *lemma* subfield.gc_map_comap
- \+ *lemma* subfield.gsmul_mem
- \+ *def* subfield.inclusion
- \+ *theorem* subfield.inv_mem
- \+ *lemma* subfield.is_glb_Inf
- \+ *lemma* subfield.le_def
- \+ *lemma* subfield.list_prod_mem
- \+ *lemma* subfield.list_sum_mem
- \+ *def* subfield.map
- \+ *lemma* subfield.map_bot
- \+ *lemma* subfield.map_le_iff_le_comap
- \+ *lemma* subfield.map_map
- \+ *lemma* subfield.map_sup
- \+ *lemma* subfield.map_supr
- \+ *lemma* subfield.mem_Inf
- \+ *lemma* subfield.mem_Sup_of_directed_on
- \+ *lemma* subfield.mem_closure
- \+ *lemma* subfield.mem_closure_iff
- \+ *lemma* subfield.mem_coe
- \+ *lemma* subfield.mem_comap
- \+ *lemma* subfield.mem_inf
- \+ *lemma* subfield.mem_map
- \+ *lemma* subfield.mem_mk
- \+ *lemma* subfield.mem_supr_of_directed
- \+ *lemma* subfield.mem_to_add_subgroup
- \+ *lemma* subfield.mem_to_submonoid
- \+ *lemma* subfield.mem_to_subring
- \+ *lemma* subfield.mem_top
- \+ *theorem* subfield.mul_mem
- \+ *lemma* subfield.multiset_prod_mem
- \+ *lemma* subfield.multiset_sum_mem
- \+ *theorem* subfield.neg_mem
- \+ *theorem* subfield.one_mem
- \+ *lemma* subfield.pow_mem
- \+ *lemma* subfield.prod_mem
- \+ *lemma* subfield.subring_closure_le
- \+ *lemma* subfield.subset_closure
- \+ *def* subfield.subtype
- \+ *lemma* subfield.sum_mem
- \+ *def* subfield.to_add_subgroup
- \+ *def* subfield.to_submonoid
- \+ *theorem* subfield.zero_mem
- \+ *def* subring.to_subfield

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.coe_eq_zero_iff



## [2020-09-17 15:33:35](https://github.com/leanprover-community/mathlib/commit/34ebade)
feat(algebra/free_algebra): free (noncommutative) algebras ([#4077](https://github.com/leanprover-community/mathlib/pull/4077))
Previously, @adamtopaz constructed the tensor algebra of an `R`-module via a direct construction of a quotient of a free algebra.
This uses essentially the same construction to build a free algebra (on a type) directly. In a PR coming shortly, I'll refactor his development of the tensor algebra to use this construction.
#### Estimated changes
Added src/algebra/free_algebra.lean
- \+ *def* free_algebra.equiv_monoid_algebra_free_monoid
- \+ *theorem* free_algebra.hom_ext
- \+ *def* free_algebra.lift
- \+ *theorem* free_algebra.lift_comp_ι
- \+ *def* free_algebra.lift_fun
- \+ *theorem* free_algebra.lift_unique
- \+ *theorem* free_algebra.lift_ι_apply
- \+ *def* free_algebra.pre.has_add
- \+ *def* free_algebra.pre.has_coe_generator
- \+ *def* free_algebra.pre.has_coe_semiring
- \+ *def* free_algebra.pre.has_mul
- \+ *def* free_algebra.pre.has_one
- \+ *def* free_algebra.pre.has_scalar
- \+ *def* free_algebra.pre.has_zero
- \+ *lemma* free_algebra.quot_mk_eq_ι
- \+ *def* free_algebra.ι
- \+ *theorem* free_algebra.ι_comp_lift
- \+ *def* free_algebra

Modified src/data/monoid_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean




## [2020-09-17 14:29:36](https://github.com/leanprover-community/mathlib/commit/b62dd28)
feat(linear_algebra/eigenspace): beginning to relate minimal polynomials to eigenvalues ([#4165](https://github.com/leanprover-community/mathlib/pull/4165))
rephrases some lemmas in `linear_algebra` to use `aeval` instead of `eval2` and `algebra_map`
shows that an eigenvalue of a linear transformation is a root of its minimal polynomial, and vice versa
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.aeval_endomorphism

Modified src/linear_algebra/eigenspace.lean
- \+ *theorem* module.End.aeval_apply_of_has_eigenvector
- \+ *lemma* module.End.eigenspace_aeval_polynomial_degree_1
- \- *lemma* module.End.eigenspace_eval₂_polynomial_degree_1
- \+ *theorem* module.End.has_eigenvalue_iff_is_root
- \+ *theorem* module.End.has_eigenvalue_of_is_root
- \+ *theorem* module.End.is_root_of_has_eigenvalue
- \+ *lemma* module.End.ker_aeval_ring_hom'_unit_polynomial
- \- *lemma* module.End.ker_eval₂_ring_hom'_unit_polynomial

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_map.findim_linear_map

Modified src/ring_theory/polynomial/basic.lean




## [2020-09-17 05:26:28](https://github.com/leanprover-community/mathlib/commit/265c587)
doc(meta/converter/interactive): Add tactic documentation for a subset of `conv` tactics ([#4144](https://github.com/leanprover-community/mathlib/pull/4144))
#### Estimated changes
Modified src/tactic/lean_core_docs.lean




## [2020-09-16 18:50:15](https://github.com/leanprover-community/mathlib/commit/7db9e13)
feat(data/monoid_algebra): ext lemma ([#4162](https://github.com/leanprover-community/mathlib/pull/4162))
A small lemma that was useful in the Witt vector project.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.alg_hom_ext
- \+ *lemma* add_monoid_algebra.alg_hom_ext_iff



## [2020-09-16 15:49:12](https://github.com/leanprover-community/mathlib/commit/9f9a8c0)
feat(readme): add @hrmacbeth to maintainers list ([#4168](https://github.com/leanprover-community/mathlib/pull/4168))
#### Estimated changes
Modified README.md




## [2020-09-16 11:42:42](https://github.com/leanprover-community/mathlib/commit/623c846)
feat(data/mv_polynomial/variables): add facts about vars and mul ([#4149](https://github.com/leanprover-community/mathlib/pull/4149))
More from the Witt vectors branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.vars_C_mul
- \+ *lemma* mv_polynomial.vars_mul
- \+ *lemma* mv_polynomial.vars_one
- \+ *lemma* mv_polynomial.vars_pow
- \+ *lemma* mv_polynomial.vars_prod



## [2020-09-16 09:39:46](https://github.com/leanprover-community/mathlib/commit/6603c6d)
fix(simps): use coercion for algebra morphisms ([#4155](https://github.com/leanprover-community/mathlib/pull/4155))
Previously it tried to apply whnf on an open expression, which failed, so it wouldn't find the coercion. Now it applied whnf before opening the expression.
Also use `simps` for `fixed_points.to_alg_hom`. The generated lemmas are
```lean
fixed_points.to_alg_hom_to_fun : ∀ (G : Type u) (F : Type v) [_inst_4 : group G] [_inst_5 : field F]
[_inst_6 : faithful_mul_semiring_action G F],
  ⇑(to_alg_hom G F) =
    λ (g : G),
      {to_fun := (mul_semiring_action.to_semiring_hom G F g).to_fun,
       map_one' := _,
       map_mul' := _,
       map_zero' := _,
       map_add' := _,
       commutes' := _}
```
#### Estimated changes
Modified src/field_theory/fixed.lean
- \- *lemma* fixed_points.coe_to_alg_hom

Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* my_alg_hom
- \+ *def* my_ring_hom



## [2020-09-16 08:03:28](https://github.com/leanprover-community/mathlib/commit/9a11efb)
feat(metric_space): add lipschitz_on_with ([#4151](https://github.com/leanprover-community/mathlib/pull/4151))
The order of the explicit arguments in this definition is open for negotiation.
From the sphere eversion project.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* lipschitz_on_with.norm_sub_le
- \+ *lemma* lipschitz_on_with_iff_norm_sub_le

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.uniform_continuous_on_iff

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_on_univ
- \+ *lemma* lipschitz_on_with.mono
- \+ *def* lipschitz_on_with
- \+ *lemma* lipschitz_on_with_iff_dist_le_mul
- \+ *lemma* lipschitz_on_with_iff_restrict

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.has_basis.uniform_continuous_on_iff
- \+ *lemma* uniform_continuous_on.continuous_on
- \+/\- *lemma* uniform_continuous_on_iff_restrict



## [2020-09-16 08:03:26](https://github.com/leanprover-community/mathlib/commit/4c9d3a5)
feat(operator_norm): smul_right lemmas ([#4150](https://github.com/leanprover-community/mathlib/pull/4150))
from the sphere eversion project
We need a version of `continuous_linear_map.smul_right` that is itself a continuous linear map from a normed space to a space of continuous linear maps. 
breaking changes:
* rename `smul_right_norm` to `norm_smul_right_apply`
* in `homothety_norm` remove useless sign assumption and switch from assuming positive dimension to `nontrivial`
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* continuous_linear_map.apply
- \+ *def* continuous_linear_map.applyₗ
- \+ *lemma* continuous_linear_map.continuous_applyₗ
- \+/\- *lemma* continuous_linear_map.homothety_norm
- \+ *lemma* continuous_linear_map.norm_smul_rightL
- \+ *lemma* continuous_linear_map.norm_smul_rightL_apply
- \+ *lemma* continuous_linear_map.norm_smul_right_apply
- \+ *def* continuous_linear_map.smul_rightL
- \- *lemma* continuous_linear_map.smul_right_norm

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.nontrivial_span_singleton

Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_map.smul_rightₗ



## [2020-09-16 06:06:09](https://github.com/leanprover-community/mathlib/commit/f585ce5)
feat(category_theory): monoidal natural transformations and discrete monoidal categories ([#4112](https://github.com/leanprover-community/mathlib/pull/4112))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *theorem* monoid_hom.congr_arg
- \+ *theorem* monoid_hom.congr_fun

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* monoid_hom.map_div

Modified src/algebra/ring/basic.lean
- \+ *theorem* ring_hom.congr_arg
- \+ *theorem* ring_hom.congr_fun

Modified src/category_theory/discrete_category.lean
- \+ *lemma* category_theory.discrete.eq_of_hom

Modified src/category_theory/limits/lattice.lean


Added src/category_theory/monoidal/discrete.lean
- \+ *def* category_theory.discrete.monoidal_functor
- \+ *def* category_theory.discrete.monoidal_functor_comp

Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *def* category_theory.lax_monoidal_functor.map_Mon_functor

Added src/category_theory/monoidal/natural_transformation.lean
- \+ *def* category_theory.monoidal_nat_trans.hcomp
- \+ *def* category_theory.monoidal_nat_trans.id
- \+ *def* category_theory.monoidal_nat_trans.vcomp

Modified src/topology/instances/real_vector_space.lean




## [2020-09-15 20:10:38](https://github.com/leanprover-community/mathlib/commit/4c896c5)
chore(undergrad.yaml): updates ([#4160](https://github.com/leanprover-community/mathlib/pull/4160))
Added a bunch of things to `undergrad.yaml`: generalized eigenspaces, conjugacy classes in a group, the orthogonal complement, continuity of monotone functions and their inverses, inverse hyperbolic trig functions, radius of convergence.  Also changed (hopefully improved) some translations.
#### Estimated changes
Modified docs/undergrad.yaml




## [2020-09-15 12:59:56](https://github.com/leanprover-community/mathlib/commit/d3a1719)
feat(category_theory/is_connected): make `is_connected` a Prop ([#4136](https://github.com/leanprover-community/mathlib/pull/4136))
Also renames `connected` to `is_connected`, and relies on `classical.arbitrary` slightly less.
#### Estimated changes
Renamed src/category_theory/connected.lean to src/category_theory/is_connected.lean
- \+/\- *lemma* category_theory.any_functor_const_on_obj
- \- *def* category_theory.connected.of_any_functor_const_on_obj
- \- *def* category_theory.connected.of_constant_of_preserves_morphisms
- \- *def* category_theory.connected.of_induct
- \- *def* category_theory.connected_of_zigzag
- \- *lemma* category_theory.connected_zigzag
- \+/\- *lemma* category_theory.constant_of_preserves_morphisms
- \- *def* category_theory.discrete_connected_equiv_punit
- \+ *def* category_theory.discrete_is_connected_equiv_punit
- \+/\- *lemma* category_theory.equiv_relation
- \+/\- *lemma* category_theory.exists_zigzag'
- \+/\- *lemma* category_theory.induct_on_objects
- \+ *lemma* category_theory.is_connected.of_any_functor_const_on_obj
- \+ *lemma* category_theory.is_connected.of_constant_of_preserves_morphisms
- \+ *lemma* category_theory.is_connected.of_induct
- \+ *lemma* category_theory.is_connected_of_zigzag
- \+ *lemma* category_theory.is_connected_zigzag
- \+ *def* category_theory.iso_constant
- \- *lemma* category_theory.nat_trans_from_connected
- \+ *lemma* category_theory.nat_trans_from_is_connected
- \- *def* category_theory.zigzag_connected
- \+ *lemma* category_theory.zigzag_is_connected

Modified src/category_theory/limits/connected.lean
- \+/\- *def* category_theory.prod_preserves_connected_limits

Modified src/category_theory/limits/shapes/constructions/over/connected.lean
- \+/\- *def* category_theory.over.creates_connected.raise_cone
- \+/\- *def* category_theory.over.creates_connected.raised_cone_is_limit
- \+/\- *lemma* category_theory.over.creates_connected.raised_cone_lowers_to_original



## [2020-09-15 11:43:08](https://github.com/leanprover-community/mathlib/commit/427d414)
feat(data/enat): some API and a module docstring ([#4103](https://github.com/leanprover-community/mathlib/pull/4103))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* enat.to_with_top_add



## [2020-09-15 01:03:57](https://github.com/leanprover-community/mathlib/commit/7c321f8)
chore(scripts): update nolints.txt ([#4157](https://github.com/leanprover-community/mathlib/pull/4157))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-14 23:27:33](https://github.com/leanprover-community/mathlib/commit/b83362e)
fix(order/ocpo): remove trace option ([#4154](https://github.com/leanprover-community/mathlib/pull/4154))
(it did not produce any output)
#### Estimated changes
Modified src/order/omega_complete_partial_order.lean




## [2020-09-14 23:27:32](https://github.com/leanprover-community/mathlib/commit/a0adcc0)
chore(category_theory/zero): lemmas for has_zero_morphisms.comp_zero|zero_comp ([#4142](https://github.com/leanprover-community/mathlib/pull/4142))
The axioms of `has_zero_morphisms` never had lemmas written for them, so everyone has been using the typeclass fields directly.
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/algebra/homology/homology.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.comp_zero
- \+ *lemma* category_theory.limits.zero_comp

Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/preadditive/schur.lean




## [2020-09-14 23:27:30](https://github.com/leanprover-community/mathlib/commit/3d73bd8)
feat(topology/algebra/ordered): monotone continuous function is homeomorphism, relative version ([#4043](https://github.com/leanprover-community/mathlib/pull/4043))
A function `f : α → β` restricts to a homeomorphism `(Ioo a b) → β`, if it (1) is order-preserving within the interval; (2) is `continuous_on` the interval; (3) tends to positive infinity at the right endpoint; and (4) tends to negative infinity at the left endpoint. The orders `α`, `β` are required to be conditionally complete, and the order on `α` must also be dense.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.nonempty_Icc_subtype
- \+ *lemma* set.nonempty_Ico_subtype
- \+ *lemma* set.nonempty_Ioc_subtype
- \+ *lemma* set.nonempty_Ioo_subtype

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Ioo_at_bot_eq_nhds_within
- \+ *lemma* Ioo_at_top_eq_nhds_within
- \+ *lemma* coe_homeomorph_of_strict_mono_continuous_Ioo



## [2020-09-14 21:25:17](https://github.com/leanprover-community/mathlib/commit/ff2639d)
feat(tactic/pretty_cases): provide a skeleton for a proof by induction / cases ([#4093](https://github.com/leanprover-community/mathlib/pull/4093))
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Added src/tactic/pretty_cases.lean


Added test/pretty_cases.lean




## [2020-09-14 19:35:47](https://github.com/leanprover-community/mathlib/commit/218ef40)
feat(measure_theory): image of Lebesgue measure under shift/rescale ([#3760](https://github.com/leanprover-community/mathlib/pull/3760))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.bInter_bind
- \+ *lemma* finset.bInter_option_to_finset
- \+ *lemma* finset.bUnion_bind
- \+ *lemma* finset.bUnion_option_to_finset
- \+ *lemma* finset.infi_bind
- \+ *lemma* finset.infi_option_to_finset
- \+ *lemma* finset.supr_bind
- \+ *lemma* finset.supr_option_to_finset

Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_Union_apply

Modified src/data/set/basic.lean
- \+ *theorem* set_coe.forall'

Modified src/data/set/disjointed.lean
- \+/\- *lemma* set.Union_disjointed_of_mono
- \+ *lemma* set.subset_Union_disjointed

Modified src/measure_theory/borel_space.lean
- \+ *lemma* real.measure_ext_Ioo_rat

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.set_lintegral_congr
- \+ *lemma* measure_theory.set_lintegral_map
- \+ *lemma* measure_theory.set_lintegral_one

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_comp_add_right
- \+ *lemma* interval_integral.integral_comp_mul_right
- \+ *lemma* interval_integral.integral_comp_neg
- \+ *lemma* interval_integral.integral_smul_measure

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* real.map_volume_add_left
- \+ *lemma* real.map_volume_add_right
- \+ *lemma* real.map_volume_mul_left
- \+ *lemma* real.map_volume_mul_right
- \+ *lemma* real.map_volume_neg
- \+ *lemma* real.smul_map_volume_mul_left
- \+ *lemma* real.smul_map_volume_mul_right
- \+/\- *lemma* real.volume_Icc
- \+/\- *lemma* real.volume_Ico
- \+/\- *lemma* real.volume_Ioc
- \+/\- *lemma* real.volume_Ioo
- \+/\- *lemma* real.volume_interval
- \+/\- *lemma* real.volume_singleton
- \+/\- *theorem* real.volume_val

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.Union
- \+ *lemma* is_measurable.bUnion_decode2
- \+/\- *lemma* is_measurable.const
- \+/\- *lemma* is_measurable.diff
- \+/\- *lemma* is_measurable.disjointed
- \+/\- *lemma* is_measurable.inter
- \+/\- *lemma* is_measurable.union

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.Ico_ae_eq_Icc
- \+ *lemma* measure_theory.Ico_ae_eq_Ioc
- \+ *lemma* measure_theory.Iio_ae_eq_Iic
- \+ *lemma* measure_theory.Ioc_ae_eq_Icc
- \+ *lemma* measure_theory.Ioi_ae_eq_Ici
- \+ *lemma* measure_theory.Ioo_ae_eq_Icc
- \+ *lemma* measure_theory.Ioo_ae_eq_Ico
- \+ *lemma* measure_theory.Ioo_ae_eq_Ioc
- \+ *lemma* measure_theory.ae_eq_empty
- \+ *lemma* measure_theory.ae_le_set
- \+ *lemma* measure_theory.diff_ae_eq_self
- \+ *lemma* measure_theory.insert_ae_eq_self
- \+ *lemma* measure_theory.measure.ext_iff_of_Union_eq_univ
- \+ *lemma* measure_theory.measure.ext_iff_of_bUnion_eq_univ
- \+ *lemma* measure_theory.measure.ext_iff_of_sUnion_eq_univ
- \+ *lemma* measure_theory.measure.ext_of_generate_from_of_cover
- \+ *lemma* measure_theory.measure.ext_of_generate_from_of_cover_subset
- \+ *lemma* measure_theory.measure.restrict_Union_apply_eq_supr
- \+ *lemma* measure_theory.measure.restrict_Union_congr
- \+ *lemma* measure_theory.measure.restrict_bUnion_congr
- \+ *lemma* measure_theory.measure.restrict_congr_meas
- \+ *lemma* measure_theory.measure.restrict_congr_mono
- \+ *lemma* measure_theory.measure.restrict_finset_bUnion_congr
- \+ *lemma* measure_theory.measure.restrict_map
- \+ *lemma* measure_theory.measure.restrict_restrict
- \+ *lemma* measure_theory.measure.restrict_sUnion_congr
- \+ *lemma* measure_theory.measure.restrict_union_add_inter
- \+ *lemma* measure_theory.measure.restrict_union_congr
- \+ *lemma* measure_theory.measure_Inter_eq_infi
- \- *lemma* measure_theory.measure_Inter_eq_infi_nat
- \+ *lemma* measure_theory.measure_Union_eq_supr
- \- *lemma* measure_theory.measure_Union_eq_supr_nat
- \+ *lemma* measure_theory.measure_bUnion_eq_supr
- \+ *lemma* measure_theory.measure_countable
- \+/\- *lemma* measure_theory.measure_diff
- \+/\- *lemma* measure_theory.measure_eq_inter_diff
- \+ *lemma* measure_theory.measure_finite
- \+ *lemma* measure_theory.measure_finset
- \+ *lemma* measure_theory.measure_mono_top
- \+ *lemma* measure_theory.measure_union_add_inter
- \- *lemma* measure_theory.restrict_congr
- \+ *lemma* measure_theory.restrict_congr_set
- \+ *lemma* measure_theory.union_ae_eq_right

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.set_integral_map

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.compl
- \+ *lemma* filter.eventually_eq.diff
- \+ *lemma* filter.eventually_eq.inter
- \+ *lemma* filter.eventually_eq.union
- \+ *lemma* filter.eventually_eq_empty
- \+ *lemma* filter.eventually_le_antisymm_iff



## [2020-09-14 16:35:45](https://github.com/leanprover-community/mathlib/commit/a18be37)
feat(ring_theory/ideal/over): Going up theorem for integral extensions ([#4064](https://github.com/leanprover-community/mathlib/pull/4064))
The main statement is `exists_ideal_over_prime_of_is_integral` which shows that for an integral extension, every prime ideal of the original ring lies under some prime ideal of the extension ring.
`is_field_of_is_integral_of_is_field` is a brute force proof that if `R → S` is an integral extension, and `S` is a field, then `R` is also a field (using the somewhat new `is_field` proposition). `is_maximal_comap_of_is_integral_of_is_maximal` Gives essentially the same statement in terms of maximal ideals.
`disjoint_compl` has also been replaced with `disjoint_compl_left` and `disjoint_compl_right` variants.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval₂_eq_sum_range

Modified src/data/set/lattice.lean
- \- *theorem* set.disjoint_compl
- \+ *theorem* set.disjoint_compl_left
- \+ *theorem* set.disjoint_compl_right

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/matrix.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/set_integral.lean


Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.algebra_map_quotient_injective
- \+ *def* ideal.quotient_map

Modified src/ring_theory/ideal/over.lean
- \+ *lemma* ideal.exists_ideal_over_prime_of_is_integral'
- \+ *theorem* ideal.exists_ideal_over_prime_of_is_integral
- \+ *lemma* ideal.is_maximal_comap_of_is_integral_of_is_maximal

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_field_of_is_integral_of_is_field
- \+ *lemma* is_integral_quotient_of_is_integral

Modified src/ring_theory/localization.lean
- \+ *lemma* algebra_map_mk'
- \+ *lemma* localization.at_prime.comap_maximal_ideal
- \+ *lemma* localization.at_prime.map_eq_maximal_ideal
- \+ *lemma* localization_algebra_injective



## [2020-09-14 15:36:04](https://github.com/leanprover-community/mathlib/commit/6babb55)
fix(normed_space): fixed a typo from [#4099](https://github.com/leanprover-community/mathlib/pull/4099) ([#4147](https://github.com/leanprover-community/mathlib/pull/4147))
This lemma was less general that it should be because migrating it to its
mathlib place messed up the typeclass assumptions.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_smul_of_nonneg



## [2020-09-14 15:36:02](https://github.com/leanprover-community/mathlib/commit/8877606)
chore(ci): teach bors and GitHub about new labels ([#4146](https://github.com/leanprover-community/mathlib/pull/4146))
#### Estimated changes
Modified .github/workflows/add_label_from_comment.yml


Modified .github/workflows/add_label_from_review.yml


Modified bors.toml




## [2020-09-14 15:35:59](https://github.com/leanprover-community/mathlib/commit/49fc7ed)
feat(measure_theory): assorted integration lemmas ([#4145](https://github.com/leanprover-community/mathlib/pull/4145))
from the sphere eversion project
This is still preparations for differentiation of integals depending on a parameter.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.continuous_integral
- \+ *lemma* measure_theory.l1.continuous_integral
- \+ *lemma* measure_theory.l1.integral_eq_integral
- \+ *lemma* measure_theory.l1.integral_of_fun_eq_integral
- \+ *lemma* measure_theory.l1.norm_eq_integral_norm
- \+ *lemma* measure_theory.l1.norm_of_fun_eq_integral_norm

Modified src/measure_theory/borel_space.lean
- \+ *lemma* continuous_linear_map.measurable
- \+ *lemma* measurable.clm_apply
- \+ *lemma* measurable.const_mul
- \+ *lemma* measurable.mul_const

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.const_mul
- \+ *lemma* measure_theory.integrable.mul_const
- \+ *lemma* measure_theory.l1.integrable_norm
- \+ *lemma* measure_theory.l1.measurable_norm

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.integral_indicator_const



## [2020-09-14 15:35:57](https://github.com/leanprover-community/mathlib/commit/5f45c0c)
feat(linear_algebra/finite_dimensional): finite-dimensional submodule lemmas / instances ([#4128](https://github.com/leanprover-community/mathlib/pull/4128))
Add the lemma that a submodule contained in a finite-dimensional
submodule is finite-dimensional, and instances that allow type class
inference to show some infs and sups involving finite-dimensional
submodules are finite-dimensional.  These are all useful when working
with finite-dimensional submodules in a space that may not be
finite-dimensional itself.
Given the new instances, `dim_sup_add_dim_inf_eq` gets its type class
requirements relaxed to require only the submodules to be
finite-dimensional rather than the whole space.
`linear_independent_iff_card_eq_findim_span` is added as a variant of
`linear_independent_of_span_eq_top_of_card_eq_findim` for vectors not
necessarily spanning the whole space (implemented as an `iff` lemma
using `findim_span_eq_card` for the other direction).
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* linear_independent_iff_card_eq_findim_span
- \+/\- *theorem* submodule.dim_sup_add_dim_inf_eq
- \+ *lemma* submodule.finite_dimensional_of_le



## [2020-09-14 14:48:27](https://github.com/leanprover-community/mathlib/commit/d5c58eb)
chore(category_theory/*): make all forgetful functors use explicit arguments ([#4139](https://github.com/leanprover-community/mathlib/pull/4139))
As suggested as https://github.com/leanprover-community/mathlib/pull/4131#discussion_r487527599, for the sake of more uniform API.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/grothendieck.lean


Modified src/category_theory/limits/over.lean
- \+/\- *def* category_theory.functor.to_cocone
- \+/\- *def* category_theory.functor.to_cone
- \+/\- *def* category_theory.over.colimit
- \+/\- *def* category_theory.over.forget_colimit_is_colimit
- \+/\- *def* category_theory.under.forget_limit_is_limit
- \+/\- *def* category_theory.under.limit

Modified src/category_theory/limits/shapes/constructions/over/connected.lean
- \+/\- *def* category_theory.over.creates_connected.raise_cone
- \+/\- *def* category_theory.over.creates_connected.raised_cone_is_limit

Modified src/category_theory/monad/bundled.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *def* Mod.forget

Modified src/category_theory/over.lean
- \+/\- *lemma* category_theory.over.forget_map
- \+/\- *lemma* category_theory.over.forget_obj
- \+/\- *lemma* category_theory.under.forget_map
- \+/\- *lemma* category_theory.under.forget_obj



## [2020-09-14 12:41:02](https://github.com/leanprover-community/mathlib/commit/a998fd1)
feat(algebra/category/Module): the monoidal category of R-modules is symmetric ([#4140](https://github.com/leanprover-community/mathlib/pull/4140))
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+ *def* Module.braiding
- \+ *lemma* Module.braiding_naturality
- \+ *lemma* Module.hexagon_forward
- \+ *lemma* Module.hexagon_reverse
- \+ *lemma* Module.monoidal_category.braiding_hom_apply
- \+ *lemma* Module.monoidal_category.braiding_inv_apply



## [2020-09-14 12:41:00](https://github.com/leanprover-community/mathlib/commit/e35e287)
refactor(data/nat/*): cleanup data.nat.basic, split data.nat.choose ([#4135](https://github.com/leanprover-community/mathlib/pull/4135))
This PR rearranges `data.nat.basic` so the lemmas are now in (hopefully appropriately-named) markdown sections. It also moves several sections (mostly ones that introduced new `def`s) into new files:
- `data.nat.fact`
- `data.nat.psub` (maybe this could be named `data.nat.partial`?)
- `data.nat.log`
- `data.nat.with_bot`
`data.nat.choose` has been split into a directory:
- The definition of `nat.choose` and basic lemmas about it have been moved from `data.nat.basic` into `data.nat.choose.basic`
- The binomial theorem and related lemmas involving sums are now in `data.nat.choose.sum`; the following lemmas are now in the `nat` namespace:
  - `sum_range_choose`
  - `sum_range_choose_halfway`
  - `choose_middle_le_pow`
- Divisibility properties of binomial coefficients are now in `data.nat.choose.dvd`.
Other changes:
- added `nat.pow_two_sub_pow_two` to `data.nat.basic`.
- module docs & doc strings for `data.nat.sqrt`
#### Estimated changes
Modified src/computability/partrec.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/basic.lean


Modified src/data/list/perm.lean


Modified src/data/nat/basic.lean
- \- *def* nat.choose
- \- *theorem* nat.choose_eq_fact_div_fact
- \- *lemma* nat.choose_eq_zero_of_lt
- \- *lemma* nat.choose_mul_fact_mul_fact
- \- *lemma* nat.choose_mul_succ_eq
- \- *lemma* nat.choose_one_right
- \- *lemma* nat.choose_pos
- \- *lemma* nat.choose_self
- \- *lemma* nat.choose_succ_right_eq
- \- *lemma* nat.choose_succ_self
- \- *lemma* nat.choose_succ_self_right
- \- *lemma* nat.choose_succ_succ
- \- *lemma* nat.choose_symm
- \- *lemma* nat.choose_symm_add
- \- *lemma* nat.choose_symm_half
- \- *lemma* nat.choose_symm_of_eq_add
- \- *lemma* nat.choose_two_right
- \- *lemma* nat.choose_zero_right
- \- *lemma* nat.choose_zero_succ
- \- *theorem* nat.dvd_fact
- \+/\- *theorem* nat.eq_of_mul_eq_mul_right
- \+/\- *lemma* nat.eq_zero_of_dvd_of_div_eq_zero
- \- *def* nat.fact
- \- *theorem* nat.fact_dvd_fact
- \- *lemma* nat.fact_eq_one
- \- *lemma* nat.fact_inj
- \- *theorem* nat.fact_le
- \- *lemma* nat.fact_lt
- \- *theorem* nat.fact_mul_fact_dvd_fact
- \- *lemma* nat.fact_mul_pow_le_fact
- \- *theorem* nat.fact_ne_zero
- \- *theorem* nat.fact_one
- \- *theorem* nat.fact_pos
- \- *theorem* nat.fact_succ
- \- *theorem* nat.fact_zero
- \+/\- *lemma* nat.le_induction
- \+/\- *theorem* nat.le_rec_on_self
- \- *def* nat.log
- \- *lemma* nat.log_pow
- \- *lemma* nat.monotone_fact
- \- *lemma* nat.one_lt_fact
- \- *lemma* nat.pow_le_iff_le_log
- \- *lemma* nat.pow_log_le_self
- \- *lemma* nat.pow_succ_log_gt_self
- \- *def* nat.ppred
- \- *theorem* nat.ppred_eq_none
- \- *theorem* nat.ppred_eq_pred
- \- *theorem* nat.ppred_eq_some
- \- *theorem* nat.pred_eq_ppred
- \- *def* nat.psub
- \- *theorem* nat.psub_add
- \- *theorem* nat.psub_eq_none
- \- *theorem* nat.psub_eq_some
- \- *theorem* nat.psub_eq_sub
- \- *theorem* nat.sub_eq_psub
- \- *lemma* nat.succ_mul_choose_eq
- \- *lemma* nat.triangle_succ
- \- *lemma* nat.with_bot.add_eq_one_iff
- \- *lemma* nat.with_bot.add_eq_zero_iff
- \- *lemma* nat.with_bot.coe_nonneg
- \- *lemma* nat.with_bot.lt_zero_iff

Deleted src/data/nat/choose.lean
- \- *theorem* add_pow
- \- *lemma* choose_le_middle
- \- *lemma* choose_le_succ_of_lt_half_left
- \- *lemma* choose_middle_le_pow
- \- *theorem* commute.add_pow
- \- *lemma* nat.prime.dvd_choose_add
- \- *lemma* nat.prime.dvd_choose_self
- \- *theorem* sum_range_choose
- \- *lemma* sum_range_choose_halfway

Added src/data/nat/choose/basic.lean
- \+ *def* nat.choose
- \+ *theorem* nat.choose_eq_fact_div_fact
- \+ *lemma* nat.choose_eq_zero_of_lt
- \+ *lemma* nat.choose_le_middle
- \+ *lemma* nat.choose_le_succ_of_lt_half_left
- \+ *lemma* nat.choose_mul_fact_mul_fact
- \+ *lemma* nat.choose_mul_succ_eq
- \+ *lemma* nat.choose_one_right
- \+ *lemma* nat.choose_pos
- \+ *lemma* nat.choose_self
- \+ *lemma* nat.choose_succ_right_eq
- \+ *lemma* nat.choose_succ_self
- \+ *lemma* nat.choose_succ_self_right
- \+ *lemma* nat.choose_succ_succ
- \+ *lemma* nat.choose_symm
- \+ *lemma* nat.choose_symm_add
- \+ *lemma* nat.choose_symm_half
- \+ *lemma* nat.choose_symm_of_eq_add
- \+ *lemma* nat.choose_two_right
- \+ *lemma* nat.choose_zero_right
- \+ *lemma* nat.choose_zero_succ
- \+ *theorem* nat.fact_mul_fact_dvd_fact
- \+ *lemma* nat.succ_mul_choose_eq
- \+ *lemma* nat.triangle_succ

Added src/data/nat/choose/default.lean


Added src/data/nat/choose/dvd.lean
- \+ *lemma* nat.prime.dvd_choose_add
- \+ *lemma* nat.prime.dvd_choose_self

Added src/data/nat/choose/sum.lean
- \+ *theorem* add_pow
- \+ *theorem* commute.add_pow
- \+ *lemma* nat.choose_middle_le_pow
- \+ *theorem* nat.sum_range_choose
- \+ *lemma* nat.sum_range_choose_halfway

Added src/data/nat/fact.lean
- \+ *theorem* nat.dvd_fact
- \+ *def* nat.fact
- \+ *theorem* nat.fact_dvd_fact
- \+ *lemma* nat.fact_eq_one
- \+ *lemma* nat.fact_inj
- \+ *theorem* nat.fact_le
- \+ *lemma* nat.fact_lt
- \+ *lemma* nat.fact_mul_pow_le_fact
- \+ *theorem* nat.fact_ne_zero
- \+ *theorem* nat.fact_one
- \+ *theorem* nat.fact_pos
- \+ *theorem* nat.fact_succ
- \+ *theorem* nat.fact_zero
- \+ *lemma* nat.monotone_fact
- \+ *lemma* nat.one_lt_fact

Modified src/data/nat/gcd.lean


Added src/data/nat/log.lean
- \+ *def* nat.log
- \+ *lemma* nat.log_pow
- \+ *lemma* nat.pow_le_iff_le_log
- \+ *lemma* nat.pow_log_le_self
- \+ *lemma* nat.pow_succ_log_gt_self

Modified src/data/nat/multiplicity.lean


Added src/data/nat/psub.lean
- \+ *def* nat.ppred
- \+ *theorem* nat.ppred_eq_none
- \+ *theorem* nat.ppred_eq_pred
- \+ *theorem* nat.ppred_eq_some
- \+ *theorem* nat.pred_eq_ppred
- \+ *def* nat.psub
- \+ *theorem* nat.psub_add
- \+ *theorem* nat.psub_eq_none
- \+ *theorem* nat.psub_eq_some
- \+ *theorem* nat.psub_eq_sub
- \+ *theorem* nat.sub_eq_psub

Modified src/data/nat/sqrt.lean


Added src/data/nat/with_bot.lean
- \+ *lemma* nat.with_bot.add_eq_one_iff
- \+ *lemma* nat.with_bot.add_eq_zero_iff
- \+ *lemma* nat.with_bot.coe_nonneg
- \+ *lemma* nat.with_bot.lt_zero_iff

Modified src/data/num/lemmas.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/number_theory/primorial.lean


Modified src/ring_theory/ideal/operations.lean




## [2020-09-14 11:13:26](https://github.com/leanprover-community/mathlib/commit/39962b7)
chore(data/polynomial/derivative): golf proof of mem_support_derivative ([#4134](https://github.com/leanprover-community/mathlib/pull/4134))
Golfed proof to be similar to what it was like prior to the refactor.
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.mem_support_iff_coeff_ne_zero

Modified src/data/polynomial/derivative.lean




## [2020-09-14 10:24:38](https://github.com/leanprover-community/mathlib/commit/6756d47)
feat(category_theory): Mon_.forget reflects isos ([#4131](https://github.com/leanprover-community/mathlib/pull/4131))
A step along the way to `sheaf X (Mon_ C) ~ Mon_ (sheaf X C)`.
#### Estimated changes
Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/internal.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/monoidal/internal/types.lean




## [2020-09-14 09:42:31](https://github.com/leanprover-community/mathlib/commit/bbfeff3)
feat(data/mv_polynomial/monad): mv_polynomial is a monad in two different ways ([#4080](https://github.com/leanprover-community/mathlib/pull/4080))
These definitions and lemmas significantly decrease the pain in several computations in the Witt project.
#### Estimated changes
Added src/data/mv_polynomial/monad.lean
- \+ *lemma* mv_polynomial.aeval_X_left
- \+ *lemma* mv_polynomial.aeval_X_left_apply
- \+ *lemma* mv_polynomial.aeval_bind₁
- \+ *lemma* mv_polynomial.aeval_bind₂
- \+ *lemma* mv_polynomial.aeval_comp_bind₁
- \+ *lemma* mv_polynomial.aeval_eq_bind₁
- \+ *lemma* mv_polynomial.aeval_id_eq_join₁
- \+ *lemma* mv_polynomial.aeval_rename
- \+ *def* mv_polynomial.bind₁
- \+ *lemma* mv_polynomial.bind₁_C_right
- \+ *lemma* mv_polynomial.bind₁_X_left
- \+ *lemma* mv_polynomial.bind₁_X_right
- \+ *lemma* mv_polynomial.bind₁_bind₁
- \+ *lemma* mv_polynomial.bind₁_comp_bind₁
- \+ *lemma* mv_polynomial.bind₁_id
- \+ *lemma* mv_polynomial.bind₁_monomial
- \+ *lemma* mv_polynomial.bind₁_rename
- \+ *def* mv_polynomial.bind₂
- \+ *lemma* mv_polynomial.bind₂_C_left
- \+ *lemma* mv_polynomial.bind₂_C_right
- \+ *lemma* mv_polynomial.bind₂_X_right
- \+ *lemma* mv_polynomial.bind₂_bind₂
- \+ *lemma* mv_polynomial.bind₂_comp_C
- \+ *lemma* mv_polynomial.bind₂_comp_bind₂
- \+ *lemma* mv_polynomial.bind₂_id
- \+ *lemma* mv_polynomial.bind₂_map
- \+ *lemma* mv_polynomial.bind₂_monomial
- \+ *lemma* mv_polynomial.bind₂_monomial_one
- \+ *lemma* mv_polynomial.eval₂_hom_C_eq_bind₁
- \+ *lemma* mv_polynomial.eval₂_hom_C_id_eq_join₁
- \+ *lemma* mv_polynomial.eval₂_hom_C_left
- \+ *lemma* mv_polynomial.eval₂_hom_bind₁
- \+ *lemma* mv_polynomial.eval₂_hom_bind₂
- \+ *lemma* mv_polynomial.eval₂_hom_comp_C
- \+ *lemma* mv_polynomial.eval₂_hom_comp_bind₂
- \+ *lemma* mv_polynomial.eval₂_hom_eq_bind₂
- \+ *lemma* mv_polynomial.eval₂_hom_id_X_eq_join₂
- \+ *lemma* mv_polynomial.hom_bind₁
- \+ *def* mv_polynomial.join₁
- \+ *lemma* mv_polynomial.join₁_rename
- \+ *def* mv_polynomial.join₂
- \+ *lemma* mv_polynomial.join₂_comp_map
- \+ *lemma* mv_polynomial.join₂_map
- \+ *lemma* mv_polynomial.map_bind₁
- \+ *lemma* mv_polynomial.map_bind₂
- \+ *lemma* mv_polynomial.map_comp_C
- \+ *lemma* mv_polynomial.rename_bind₁



## [2020-09-14 09:42:28](https://github.com/leanprover-community/mathlib/commit/ed71b2d)
feat(computability/tm_computable): define computable (in polytime) for TMs, prove id is computable in constant time  ([#4048](https://github.com/leanprover-community/mathlib/pull/4048))
We define computability in polynomial time to be used in our future PR on P and NP.
We also prove that id is computable in constant time.
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Added src/computability/tm_computable.lean
- \+ *def* turing.evals_to.refl
- \+ *def* turing.evals_to.trans
- \+ *def* turing.evals_to_in_time.refl
- \+ *def* turing.evals_to_in_time.trans
- \+ *def* turing.fin_tm2.cfg
- \+ *def* turing.fin_tm2.step
- \+ *def* turing.fin_tm2.stmt
- \+ *def* turing.halt_list
- \+ *def* turing.id_computable
- \+ *def* turing.id_computable_in_poly_time
- \+ *def* turing.id_computable_in_time
- \+ *def* turing.id_computer
- \+ *def* turing.init_list
- \+ *def* turing.tm2_computable_in_poly_time.to_tm2_computable_in_time
- \+ *def* turing.tm2_computable_in_time.to_tm2_computable
- \+ *def* turing.tm2_outputs
- \+ *def* turing.tm2_outputs_in_time.to_tm2_outputs
- \+ *def* turing.tm2_outputs_in_time



## [2020-09-14 08:03:38](https://github.com/leanprover-community/mathlib/commit/dce6b37)
chore(algebra/homology): cleanup instances post [#3995](https://github.com/leanprover-community/mathlib/pull/3995) ([#4137](https://github.com/leanprover-community/mathlib/pull/4137))
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/algebra/homology/image_to_kernel_map.lean




## [2020-09-14 08:03:36](https://github.com/leanprover-community/mathlib/commit/1c2ddbc)
feat(field_theory/fixed): dimension over fixed field is order of group ([#4125](https://github.com/leanprover-community/mathlib/pull/4125))
```lean
theorem dim_fixed_points (G : Type u) (F : Type v) [group G] [field F]
  [fintype G] [faithful_mul_semiring_action G F] :
  findim (fixed_points G F) F = fintype.card G
````
#### Estimated changes
Added src/algebra/big_operators/finsupp.lean
- \+ *theorem* finset.sum_apply'
- \+ *theorem* finsupp.sum_apply'
- \+ *theorem* finsupp.sum_sum_index'

Modified src/algebra/group_ring_action.lean
- \+ *theorem* eq_of_smul_eq_smul
- \+ *theorem* injective_to_semiring_hom

Modified src/data/set/function.lean
- \+ *theorem* set.inj_on_insert

Modified src/field_theory/fixed.lean
- \+ *lemma* cardinal_mk_alg_hom
- \+ *lemma* findim_alg_hom
- \+/\- *theorem* fixed_points.coe_algebra_map
- \+ *lemma* fixed_points.coe_to_alg_hom
- \+ *lemma* fixed_points.dim_le_card
- \+ *theorem* fixed_points.findim_eq_card
- \+ *lemma* fixed_points.findim_le_card
- \+/\- *theorem* fixed_points.is_integral
- \+ *lemma* fixed_points.linear_independent_smul_of_linear_independent
- \+/\- *theorem* fixed_points.minpoly.eval₂
- \+/\- *theorem* fixed_points.minpoly.irreducible
- \+/\- *theorem* fixed_points.minpoly.irreducible_aux
- \+/\- *theorem* fixed_points.minpoly.minimal_polynomial
- \+/\- *theorem* fixed_points.minpoly.monic
- \+/\- *theorem* fixed_points.minpoly.ne_one
- \+ *theorem* fixed_points.minpoly.of_eval₂
- \+/\- *def* fixed_points.minpoly
- \- *theorem* fixed_points.of_eval₂
- \+/\- *theorem* fixed_points.smul
- \+/\- *theorem* fixed_points.smul_polynomial
- \+ *def* fixed_points.to_alg_hom
- \+ *lemma* fixed_points.to_alg_hom_apply
- \+ *lemma* linear_independent_to_linear_map

Modified src/field_theory/tower.lean
- \+ *lemma* finite_dimensional.findim_linear_map'
- \+ *lemma* finite_dimensional.findim_linear_map
- \+ *lemma* finite_dimensional.right

Modified src/group_theory/group_action.lean
- \+ *def* mul_action.to_fun
- \+ *lemma* mul_action.to_fun_apply

Modified src/linear_algebra/basis.lean
- \+ *theorem* linear_independent.image'
- \+ *theorem* linear_independent_equiv'
- \+ *theorem* linear_independent_equiv
- \+ *theorem* linear_independent_image
- \+ *theorem* linear_independent_insert'
- \+ *theorem* linear_independent_insert
- \+ *lemma* linear_independent_of_comp

Modified src/linear_algebra/dimension.lean
- \+ *theorem* dim_le
- \+ *theorem* is_basis.mk_eq_dim''
- \+ *theorem* {u₁}

Modified src/linear_algebra/finsupp.lean
- \+ *theorem* finsupp.total_apply_of_mem_supported

Modified src/ring_theory/algebra.lean
- \+ *def* linear_map.lto_fun

Modified src/ring_theory/algebra_tower.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.card_le_of



## [2020-09-14 08:03:35](https://github.com/leanprover-community/mathlib/commit/b1e5a6b)
doc(measure_theory): docstrings for continuity from above and below ([#4122](https://github.com/leanprover-community/mathlib/pull/4122))
#### Estimated changes
Modified src/measure_theory/measure_space.lean




## [2020-09-14 08:03:33](https://github.com/leanprover-community/mathlib/commit/5a478f0)
doc(category_theory/natural_isomorphism): documentation and cleanup ([#4120](https://github.com/leanprover-community/mathlib/pull/4120))
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.iso.app
- \- *def* category_theory.nat_iso.is_iso_app_of_is_iso



## [2020-09-14 08:03:31](https://github.com/leanprover-community/mathlib/commit/51608f4)
feat(linear_algebra/affine_space,geometry/euclidean): simplex centers and order of points ([#4116](https://github.com/leanprover-community/mathlib/pull/4116))
Add lemmas that the centroid of an injective indexed family of points
does not depend on the indices of those points, only on the set of
points in their image, and likewise that the centroid, circumcenter
and Monge point of a simplex and thus the orthocenter of a triangle do
not depend on the order in which the vertices are indexed by `fin (n + 1)`,
only on the set of vertices.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.circumcenter_eq_of_range_eq

Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* affine.simplex.monge_point_eq_of_range_eq
- \+ *lemma* affine.triangle.orthocenter_eq_of_range_eq

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.centroid_eq_centroid_image_of_inj_on
- \+ *lemma* finset.centroid_eq_of_inj_on_of_image_eq

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine.simplex.centroid_eq_of_range_eq



## [2020-09-14 08:03:29](https://github.com/leanprover-community/mathlib/commit/b19fbd7)
feat(ring_theory/algebra_tower): coefficients for a basis in an algebra tower ([#4114](https://github.com/leanprover-community/mathlib/pull/4114))
This PR gives an expression for `(is_basis.smul hb hc).repr` in terms of `hb.repr` and `hc.repr`, useful if you have a field extension `L / K`, and `x y : L`, and want to write `y` in terms of the power basis of `K(x)`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.linear_map.ext_on

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.repr_apply_eq
- \+ *lemma* is_basis.repr_eq_iff

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* is_basis.smul
- \+ *theorem* is_basis.smul_repr
- \+ *theorem* is_basis.smul_repr_mk
- \+/\- *theorem* linear_independent_smul



## [2020-09-14 06:53:07](https://github.com/leanprover-community/mathlib/commit/e355933)
chore(category_theory/limits): remove unnecessary typeclass arguments ([#4141](https://github.com/leanprover-community/mathlib/pull/4141))
Ongoing cleanup post [#3995](https://github.com/leanprover-community/mathlib/pull/3995).
Previously we couldn't construct things like `instance : has_kernel (0 : X \hom Y)`, because it wouldn't have agreed definitionally with more general instances. Now we can.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* category_theory.limits.coequalizer.iso_target_of_self
- \+/\- *lemma* category_theory.limits.coequalizer.iso_target_of_self_hom
- \+/\- *lemma* category_theory.limits.coequalizer.iso_target_of_self_inv
- \+/\- *def* category_theory.limits.equalizer.iso_source_of_self
- \+/\- *lemma* category_theory.limits.equalizer.iso_source_of_self_hom
- \+/\- *lemma* category_theory.limits.equalizer.iso_source_of_self_inv

Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.cokernel.π_of_zero
- \+/\- *def* category_theory.limits.cokernel_zero_iso_target
- \+/\- *lemma* category_theory.limits.cokernel_zero_iso_target_hom
- \+/\- *lemma* category_theory.limits.cokernel_zero_iso_target_inv
- \+/\- *def* category_theory.limits.kernel.ι_of_zero
- \+/\- *def* category_theory.limits.kernel_zero_iso_source
- \+/\- *lemma* category_theory.limits.kernel_zero_iso_source_hom
- \+/\- *lemma* category_theory.limits.kernel_zero_iso_source_inv



## [2020-09-14 00:14:59](https://github.com/leanprover-community/mathlib/commit/bd385fb)
chore(category_theory/limits/functor_category): shuffle limits in functor cats ([#4124](https://github.com/leanprover-community/mathlib/pull/4124))
Give `is_limit` versions for statements about limits in the functor category, and write the `has_limit` versions in terms of those.
This also generalises the universes a little.
As usual, suggestions for better docstrings or better names appreciated!
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* category_theory.limits.cocone.w
- \+/\- *lemma* category_theory.limits.cone.w

Modified src/category_theory/limits/functor_category.lean
- \- *lemma* category_theory.limits.cocone.functor_w
- \+ *def* category_theory.limits.combine_cocones
- \+ *def* category_theory.limits.combine_cones
- \+ *def* category_theory.limits.combined_is_colimit
- \+ *def* category_theory.limits.combined_is_limit
- \- *lemma* category_theory.limits.cone.functor_w
- \+ *def* category_theory.limits.evaluate_combined_cocones
- \+ *def* category_theory.limits.evaluate_combined_cones
- \- *def* category_theory.limits.evaluate_functor_category_colimit_cocone
- \- *def* category_theory.limits.evaluate_functor_category_limit_cone
- \+ *def* category_theory.limits.evaluation_jointly_reflects_colimits
- \+ *def* category_theory.limits.evaluation_jointly_reflects_limits
- \- *def* category_theory.limits.functor_category_colimit_cocone
- \- *def* category_theory.limits.functor_category_is_colimit_cocone
- \- *def* category_theory.limits.functor_category_is_limit_cone
- \- *def* category_theory.limits.functor_category_limit_cone



## [2020-09-13 08:21:22](https://github.com/leanprover-community/mathlib/commit/5d35e62)
feat(algebraic_geometry/*): Gamma the global sections functor ([#4126](https://github.com/leanprover-community/mathlib/pull/4126))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *def* algebraic_geometry.Scheme.Γ
- \+ *lemma* algebraic_geometry.Scheme.Γ_def
- \+ *lemma* algebraic_geometry.Scheme.Γ_map
- \+ *lemma* algebraic_geometry.Scheme.Γ_map_op
- \+ *lemma* algebraic_geometry.Scheme.Γ_obj
- \+ *lemma* algebraic_geometry.Scheme.Γ_obj_op

Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.Γ
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_def
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_map
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_map_op
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_obj
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_obj_op

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *def* algebraic_geometry.PresheafedSpace.Γ
- \+ *lemma* algebraic_geometry.PresheafedSpace.Γ_map_op
- \+ *lemma* algebraic_geometry.PresheafedSpace.Γ_obj_op

Modified src/algebraic_geometry/sheafed_space.lean
- \+ *def* algebraic_geometry.SheafedSpace.Γ
- \+ *lemma* algebraic_geometry.SheafedSpace.Γ_def
- \+ *lemma* algebraic_geometry.SheafedSpace.Γ_map
- \+ *lemma* algebraic_geometry.SheafedSpace.Γ_map_op
- \+ *lemma* algebraic_geometry.SheafedSpace.Γ_obj
- \+ *lemma* algebraic_geometry.SheafedSpace.Γ_obj_op

Modified src/topology/category/Top/opens.lean
- \+ *def* topological_space.opens.bot_le
- \+ *def* topological_space.opens.le_map_top
- \+ *def* topological_space.opens.le_top



## [2020-09-13 03:55:56](https://github.com/leanprover-community/mathlib/commit/f403a8b)
feat(category_theory/limits/types): is_limit versions of limits in type ([#4130](https://github.com/leanprover-community/mathlib/pull/4130))
`is_limit` versions for definitions and lemmas about limits in `Type u`.
#### Estimated changes
Modified src/category_theory/limits/types.lean
- \+ *def* category_theory.limits.types.is_limit_equiv_sections
- \+ *lemma* category_theory.limits.types.is_limit_equiv_sections_apply
- \+ *lemma* category_theory.limits.types.is_limit_equiv_sections_symm_apply



## [2020-09-13 01:01:54](https://github.com/leanprover-community/mathlib/commit/dd43823)
chore(scripts): update nolints.txt ([#4129](https://github.com/leanprover-community/mathlib/pull/4129))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-12 18:30:15](https://github.com/leanprover-community/mathlib/commit/f3326db)
feat(normed_space): second countability for linear maps ([#4099](https://github.com/leanprover-community/mathlib/pull/4099))
From the sphere eversion project, various lemmas about continuous linear maps and a theorem: if E is finite dimensional and F is second countable then the space of continuous linear maps from E to F is second countable.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* eq_of_norm_sub_eq_zero
- \+ *lemma* norm_le_insert
- \+ *lemma* norm_smul_of_nonneg
- \+ *lemma* normed_group.tendsto_nhds_nhds

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* is_basis.coe_constrL
- \+ *def* is_basis.constrL
- \+ *lemma* is_basis.constrL_apply
- \+ *lemma* is_basis.constrL_basis
- \+ *def* is_basis.equiv_funL
- \+ *lemma* is_basis.op_norm_le
- \+ *lemma* is_basis.sup_norm_le_norm

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_norm_eq_of_bounds
- \+ *lemma* continuous_linear_map.op_norm_le_of_ball
- \+ *lemma* continuous_of_linear_of_bound

Modified src/linear_algebra/basis.lean
- \+ *theorem* is_basis.constr_apply_fintype

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.map_sum



## [2020-09-12 16:34:13](https://github.com/leanprover-community/mathlib/commit/c8771b6)
fix(algebra/ring/basic): delete mul_self_sub_mul_self_eq ([#4119](https://github.com/leanprover-community/mathlib/pull/4119))
It's redundant with `mul_self_sub_mul_self`.
Also renamed `mul_self_sub_one_eq` to `mul_self_sub_one`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \- *lemma* mul_self_sub_mul_self_eq
- \+ *lemma* mul_self_sub_one
- \- *lemma* mul_self_sub_one_eq



## [2020-09-12 15:49:53](https://github.com/leanprover-community/mathlib/commit/169384a)
feat(slim_check): add test cases ([#4100](https://github.com/leanprover-community/mathlib/pull/4100))
#### Estimated changes
Modified src/system/random/basic.lean
- \+ *def* io.run_rand_with

Modified src/tactic/slim_check.lean


Modified src/testing/slim_check/testable.lean
- \+/\- *def* slim_check.testable.check

Added test/random.lean
- \+ *def* find_prime
- \+ *def* find_prime_aux
- \+ *def* iterated_primality_test
- \+ *def* iterated_primality_test_aux
- \+ *def* primality_test

Modified test/slim_check.lean
- \- *def* find_prime
- \- *def* find_prime_aux
- \- *def* iterated_primality_test
- \- *def* iterated_primality_test_aux
- \- *def* primality_test



## [2020-09-12 09:38:07](https://github.com/leanprover-community/mathlib/commit/c3a6a69)
doc(group_theory/subgroup): fix links in module doc ([#4115](https://github.com/leanprover-community/mathlib/pull/4115))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2020-09-12 09:38:05](https://github.com/leanprover-community/mathlib/commit/88dd01b)
chore(category_theory): minor cleanups ([#4110](https://github.com/leanprover-community/mathlib/pull/4110))
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean
- \+ *def* AddCommGroup.colimits.colimit_cocone_is_colimit
- \- *def* AddCommGroup.colimits.colimit_is_colimit

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.map
- \- *def* category_theory.limits.is_colimit_map
- \+ *def* category_theory.limits.is_limit.map
- \- *def* category_theory.limits.is_limit_map

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/types.lean
- \+ *lemma* category_theory.hom_inv_id_apply
- \+ *lemma* category_theory.inv_hom_id_apply



## [2020-09-12 07:45:55](https://github.com/leanprover-community/mathlib/commit/b1a210e)
feat(logic/basic): Add more simp lemmas for forall ([#4117](https://github.com/leanprover-community/mathlib/pull/4117))
#### Estimated changes
Modified src/computability/partrec_code.lean


Modified src/logic/basic.lean
- \+ *theorem* forall_eq_apply_imp_iff'
- \+ *theorem* forall_eq_apply_imp_iff



## [2020-09-12 06:00:57](https://github.com/leanprover-community/mathlib/commit/3419986)
feat(category_theory/limits): make has_limit a Prop ([#3995](https://github.com/leanprover-community/mathlib/pull/3995))
We change `has_limit` so that it is only an existential statement that limit data exists, and in particular lives in `Prop`.
This means we can safely have multiple `has_limit` classes for the same functor, because proof irrelevance ensures Lean sees them all as the same.
We still have access to the API which lets us pretend we have consistently chosen limits, but now these limits are provided by the axiom of choice and hence are definitionally opaque.
#### Estimated changes
Modified docs/tutorial/category_theory/Ab.lean


Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean


Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/biproducts.lean
- \+ *def* AddCommGroup.binary_product_limit_cone
- \+ *def* AddCommGroup.biprod_iso_prod
- \+ *def* AddCommGroup.biproduct_iso_pi
- \+ *def* AddCommGroup.has_limit.product_limit_cone

Modified src/algebra/category/Group/colimits.lean
- \- *def* AddCommGroup.cokernel_iso_quotient

Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Module/kernels.lean
- \+ *lemma* Module.has_cokernels_Module
- \- *def* Module.has_cokernels_Module
- \+ *lemma* Module.has_kernels_Module
- \- *def* Module.has_kernels_Module

Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/homology/homology.lean


Modified src/algebra/homology/image_to_kernel_map.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.has_finite_biproducts
- \- *def* category_theory.abelian.has_finite_biproducts
- \+ *lemma* category_theory.abelian.has_pullbacks
- \- *def* category_theory.abelian.has_pullbacks
- \+ *lemma* category_theory.abelian.has_pushouts
- \- *def* category_theory.abelian.has_pushouts

Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* category_theory.non_preadditive_abelian.has_colimit_parallel_pair
- \- *def* category_theory.non_preadditive_abelian.has_colimit_parallel_pair
- \+ *lemma* category_theory.non_preadditive_abelian.has_limit_parallel_pair
- \- *def* category_theory.non_preadditive_abelian.has_limit_parallel_pair
- \+ *lemma* category_theory.non_preadditive_abelian.pullback_of_mono
- \- *def* category_theory.non_preadditive_abelian.pullback_of_mono
- \+ *lemma* category_theory.non_preadditive_abelian.pushout_of_epi
- \- *def* category_theory.non_preadditive_abelian.pushout_of_epi

Modified src/category_theory/adjunction/limits.lean
- \+ *lemma* category_theory.adjunction.has_colimit_of_comp_equivalence
- \- *def* category_theory.adjunction.has_colimit_of_comp_equivalence
- \+ *lemma* category_theory.adjunction.has_limit_of_comp_equivalence
- \- *def* category_theory.adjunction.has_limit_of_comp_equivalence

Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/graded_object.lean
- \- *def* category_theory.graded_object.total

Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean
- \+ *lemma* category_theory.has_colimit_of_created
- \- *def* category_theory.has_colimit_of_created
- \+ *lemma* category_theory.has_limit_of_created
- \- *def* category_theory.has_limit_of_created

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/fubini.lean
- \- *def* category_theory.limits.diagram_of_cones.mk_of_has_limits
- \- *def* category_theory.limits.limit_iso_limit_curry_comp_lim
- \- *def* category_theory.limits.limit_uncurry_iso_limit_comp_lim

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *def* category_theory.limits.colimit.cocone
- \+ *lemma* category_theory.limits.colimit.cocone_X
- \+ *def* category_theory.limits.get_colimit_cocone
- \+ *def* category_theory.limits.get_limit_cone
- \+ *lemma* category_theory.limits.has_colimit.mk
- \+ *lemma* category_theory.limits.has_colimit.of_cocones_iso
- \- *def* category_theory.limits.has_colimit.of_cocones_iso
- \+ *lemma* category_theory.limits.has_colimit_of_equivalence_comp
- \- *def* category_theory.limits.has_colimit_of_equivalence_comp
- \+ *lemma* category_theory.limits.has_colimit_of_iso
- \- *def* category_theory.limits.has_colimit_of_iso
- \+ *lemma* category_theory.limits.has_colimits_of_shape_of_equivalence
- \- *def* category_theory.limits.has_colimits_of_shape_of_equivalence
- \+ *lemma* category_theory.limits.has_limit.mk
- \+ *lemma* category_theory.limits.has_limit.of_cones_iso
- \- *def* category_theory.limits.has_limit.of_cones_iso
- \+ *lemma* category_theory.limits.has_limit_of_equivalence_comp
- \- *def* category_theory.limits.has_limit_of_equivalence_comp
- \+ *lemma* category_theory.limits.has_limit_of_iso
- \- *def* category_theory.limits.has_limit_of_iso
- \+ *lemma* category_theory.limits.has_limits_of_shape_of_equivalence
- \- *def* category_theory.limits.has_limits_of_shape_of_equivalence
- \+ *def* category_theory.limits.is_colimit_map
- \+ *def* category_theory.limits.is_limit_map
- \+ *lemma* category_theory.limits.is_limit_map_π
- \+/\- *def* category_theory.limits.limit.cone
- \+ *lemma* category_theory.limits.limit.cone_X
- \+ *lemma* category_theory.limits.ι_is_colimit_map

Modified src/category_theory/limits/opposites.lean
- \+ *lemma* category_theory.limits.has_colimit_of_has_limit_left_op
- \- *def* category_theory.limits.has_colimit_of_has_limit_left_op
- \+ *lemma* category_theory.limits.has_colimits_of_shape_op_of_has_limits_of_shape
- \- *def* category_theory.limits.has_colimits_of_shape_op_of_has_limits_of_shape
- \+ *lemma* category_theory.limits.has_colimits_op_of_has_limits
- \- *def* category_theory.limits.has_colimits_op_of_has_limits
- \+ *lemma* category_theory.limits.has_coproducts_opposite
- \- *def* category_theory.limits.has_coproducts_opposite
- \+ *lemma* category_theory.limits.has_limit_of_has_colimit_left_op
- \- *def* category_theory.limits.has_limit_of_has_colimit_left_op
- \+ *lemma* category_theory.limits.has_limits_of_shape_op_of_has_colimits_of_shape
- \- *def* category_theory.limits.has_limits_of_shape_op_of_has_colimits_of_shape
- \+ *lemma* category_theory.limits.has_limits_op_of_has_colimits
- \- *def* category_theory.limits.has_limits_op_of_has_colimits
- \+ *lemma* category_theory.limits.has_products_opposite
- \- *def* category_theory.limits.has_products_opposite

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/pi.lean
- \+ *lemma* category_theory.pi.has_colimit_of_has_colimit_comp_eval
- \- *def* category_theory.pi.has_colimit_of_has_colimit_comp_eval
- \+ *lemma* category_theory.pi.has_limit_of_has_limit_comp_eval
- \- *def* category_theory.pi.has_limit_of_has_limit_comp_eval

Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/preserves/shapes.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.has_binary_coproducts_of_has_colimit_pair
- \- *def* category_theory.limits.has_binary_coproducts_of_has_colimit_pair
- \+ *lemma* category_theory.limits.has_binary_products_of_has_limit_pair
- \- *def* category_theory.limits.has_binary_products_of_has_limit_pair

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.binary_biproduct.bicone
- \+ *lemma* category_theory.limits.binary_biproduct.bicone_fst
- \+ *lemma* category_theory.limits.binary_biproduct.bicone_inl
- \+ *lemma* category_theory.limits.binary_biproduct.bicone_inr
- \+ *lemma* category_theory.limits.binary_biproduct.bicone_snd
- \+ *def* category_theory.limits.binary_biproduct.is_colimit
- \+ *def* category_theory.limits.binary_biproduct.is_limit
- \+ *lemma* category_theory.limits.biprod.inl_desc
- \+ *lemma* category_theory.limits.biprod.inr_desc
- \+ *lemma* category_theory.limits.biprod.lift_fst
- \+ *lemma* category_theory.limits.biprod.lift_snd
- \+ *def* category_theory.limits.biproduct.bicone
- \+ *lemma* category_theory.limits.biproduct.bicone_ι
- \+ *lemma* category_theory.limits.biproduct.bicone_π
- \- *lemma* category_theory.limits.biproduct.inl_map
- \+ *def* category_theory.limits.biproduct.is_colimit
- \+ *def* category_theory.limits.biproduct.is_limit
- \+ *lemma* category_theory.limits.biproduct.lift_π
- \+ *lemma* category_theory.limits.biproduct.map_π
- \+ *lemma* category_theory.limits.biproduct.ι_desc
- \+ *lemma* category_theory.limits.biproduct.ι_map
- \+ *def* category_theory.limits.get_binary_biproduct_data
- \+ *def* category_theory.limits.get_biproduct_data
- \+ *lemma* category_theory.limits.has_binary_biproduct.mk
- \+ *lemma* category_theory.limits.has_binary_biproduct.of_has_binary_coproduct
- \- *def* category_theory.limits.has_binary_biproduct.of_has_binary_coproduct
- \+ *lemma* category_theory.limits.has_binary_biproduct.of_has_binary_product
- \- *def* category_theory.limits.has_binary_biproduct.of_has_binary_product
- \+ *lemma* category_theory.limits.has_binary_biproduct_of_total
- \- *def* category_theory.limits.has_binary_biproduct_of_total
- \+ *lemma* category_theory.limits.has_binary_biproducts.of_has_binary_coproducts
- \- *def* category_theory.limits.has_binary_biproducts.of_has_binary_coproducts
- \+ *lemma* category_theory.limits.has_binary_biproducts.of_has_binary_products
- \- *def* category_theory.limits.has_binary_biproducts.of_has_binary_products
- \+ *lemma* category_theory.limits.has_binary_biproducts_of_finite_biproducts
- \- *def* category_theory.limits.has_binary_biproducts_of_finite_biproducts
- \+ *lemma* category_theory.limits.has_biproduct.mk
- \+ *lemma* category_theory.limits.has_biproduct.of_has_coproduct
- \- *def* category_theory.limits.has_biproduct.of_has_coproduct
- \+ *lemma* category_theory.limits.has_biproduct.of_has_product
- \- *def* category_theory.limits.has_biproduct.of_has_product
- \+ *lemma* category_theory.limits.has_biproduct_of_total
- \- *def* category_theory.limits.has_biproduct_of_total
- \+ *lemma* category_theory.limits.has_finite_biproducts.of_has_finite_coproducts
- \- *def* category_theory.limits.has_finite_biproducts.of_has_finite_coproducts
- \+ *lemma* category_theory.limits.has_finite_biproducts.of_has_finite_products
- \- *def* category_theory.limits.has_finite_biproducts.of_has_finite_products

Modified src/category_theory/limits/shapes/constructions/binary_products.lean
- \+ *lemma* has_binary_products_of_terminal_and_pullbacks
- \- *def* has_binary_products_of_terminal_and_pullbacks

Modified src/category_theory/limits/shapes/constructions/equalizers.lean
- \+ *lemma* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products
- \- *def* category_theory.limits.has_equalizers_of_pullbacks_and_binary_products

Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* category_theory.limits.finite_limits_from_equalizers_and_finite_products
- \- *def* category_theory.limits.finite_limits_from_equalizers_and_finite_products
- \+ *lemma* category_theory.limits.limits_from_equalizers_and_products
- \- *def* category_theory.limits.limits_from_equalizers_and_products

Modified src/category_theory/limits/shapes/constructions/over/default.lean


Modified src/category_theory/limits/shapes/constructions/over/products.lean
- \+ *lemma* category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit
- \- *def* category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit
- \+ *lemma* category_theory.over.construct_products.over_binary_product_of_pullback
- \- *def* category_theory.over.construct_products.over_binary_product_of_pullback
- \+ *lemma* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \- *def* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \+ *lemma* category_theory.over.construct_products.over_product_of_wide_pullback
- \- *def* category_theory.over.construct_products.over_product_of_wide_pullback
- \+ *lemma* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \- *def* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \+ *lemma* category_theory.over.over_has_terminal
- \- *def* category_theory.over.over_has_terminal

Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean
- \+ *lemma* category_theory.limits.has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \- *def* category_theory.limits.has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \+ *lemma* category_theory.limits.has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \- *def* category_theory.limits.has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \+ *lemma* category_theory.limits.has_pullbacks_of_has_binary_products_of_has_equalizers
- \- *def* category_theory.limits.has_pullbacks_of_has_binary_products_of_has_equalizers
- \+ *lemma* category_theory.limits.has_pushouts_of_has_binary_coproducts_of_has_coequalizers
- \- *def* category_theory.limits.has_pushouts_of_has_binary_coproducts_of_has_coequalizers

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.has_coequalizers_of_has_colimit_parallel_pair
- \- *def* category_theory.limits.has_coequalizers_of_has_colimit_parallel_pair
- \+ *lemma* category_theory.limits.has_equalizers_of_has_limit_parallel_pair
- \- *def* category_theory.limits.has_equalizers_of_has_limit_parallel_pair

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+/\- *def* category_theory.limits.has_finite_colimits
- \+ *lemma* category_theory.limits.has_finite_colimits_of_has_colimits
- \- *def* category_theory.limits.has_finite_colimits_of_has_colimits
- \+/\- *def* category_theory.limits.has_finite_limits
- \+ *lemma* category_theory.limits.has_finite_limits_of_has_limits
- \- *def* category_theory.limits.has_finite_limits_of_has_limits
- \+/\- *def* category_theory.limits.has_finite_wide_pullbacks
- \+ *lemma* category_theory.limits.has_finite_wide_pullbacks_of_has_finite_limits
- \- *def* category_theory.limits.has_finite_wide_pullbacks_of_has_finite_limits
- \+/\- *def* category_theory.limits.has_finite_wide_pushouts
- \+ *lemma* category_theory.limits.has_finite_wide_pushouts_of_has_finite_limits
- \- *def* category_theory.limits.has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+/\- *def* category_theory.limits.has_finite_coproducts
- \+ *lemma* category_theory.limits.has_finite_coproducts_of_has_coproducts
- \- *def* category_theory.limits.has_finite_coproducts_of_has_coproducts
- \+ *lemma* category_theory.limits.has_finite_coproducts_of_has_finite_colimits
- \- *def* category_theory.limits.has_finite_coproducts_of_has_finite_colimits
- \+/\- *def* category_theory.limits.has_finite_products
- \+ *lemma* category_theory.limits.has_finite_products_of_has_finite_limits
- \- *def* category_theory.limits.has_finite_products_of_has_finite_limits
- \+ *lemma* category_theory.limits.has_finite_products_of_has_products
- \- *def* category_theory.limits.has_finite_products_of_has_products

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.has_pullbacks_of_has_limit_cospan
- \- *def* category_theory.limits.has_pullbacks_of_has_limit_cospan
- \+ *lemma* category_theory.limits.has_pushouts_of_has_colimit_span
- \- *def* category_theory.limits.has_pushouts_of_has_colimit_span

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* category_theory.limits.has_initial_of_unique
- \- *def* category_theory.limits.has_initial_of_unique
- \+ *lemma* category_theory.limits.has_terminal_of_unique
- \- *def* category_theory.limits.has_terminal_of_unique

Modified src/category_theory/limits/shapes/types.lean
- \+ *def* category_theory.limits.types.binary_coproduct_limit_cone
- \+ *def* category_theory.limits.types.binary_product_limit_cone
- \- *lemma* category_theory.limits.types.coprod
- \- *lemma* category_theory.limits.types.coprod_desc
- \- *lemma* category_theory.limits.types.coprod_inl
- \- *lemma* category_theory.limits.types.coprod_inr
- \- *lemma* category_theory.limits.types.coprod_map
- \+ *def* category_theory.limits.types.coproduct_limit_cone
- \- *lemma* category_theory.limits.types.initial
- \+ *def* category_theory.limits.types.initial_limit_cone
- \- *lemma* category_theory.limits.types.pi
- \- *lemma* category_theory.limits.types.pi_lift
- \- *lemma* category_theory.limits.types.pi_map
- \- *lemma* category_theory.limits.types.pi_π
- \- *lemma* category_theory.limits.types.prod
- \- *lemma* category_theory.limits.types.prod_fst
- \- *lemma* category_theory.limits.types.prod_lift
- \- *lemma* category_theory.limits.types.prod_map
- \- *lemma* category_theory.limits.types.prod_snd
- \+ *def* category_theory.limits.types.product_limit_cone
- \- *lemma* category_theory.limits.types.sigma
- \- *lemma* category_theory.limits.types.sigma_desc
- \- *lemma* category_theory.limits.types.sigma_map
- \- *lemma* category_theory.limits.types.sigma_ι
- \- *lemma* category_theory.limits.types.terminal
- \- *lemma* category_theory.limits.types.terminal_from
- \+ *def* category_theory.limits.types.terminal_limit_cone
- \- *def* category_theory.limits.types.types_has_binary_coproducts
- \- *def* category_theory.limits.types.types_has_binary_products
- \- *def* category_theory.limits.types.types_has_coproducts
- \- *def* category_theory.limits.types.types_has_initial
- \- *def* category_theory.limits.types.types_has_products
- \- *def* category_theory.limits.types.types_has_terminal

Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.has_zero_object.has_initial
- \- *def* category_theory.limits.has_zero_object.has_initial
- \+ *lemma* category_theory.limits.has_zero_object.has_terminal
- \- *def* category_theory.limits.has_zero_object.has_terminal

Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/limits.lean
- \+ *lemma* category_theory.has_limits_of_reflective
- \- *def* category_theory.has_limits_of_reflective
- \+ *lemma* category_theory.monad.forget_creates_colimits_of_monad_preserves
- \- *def* category_theory.monad.forget_creates_colimits_of_monad_preserves
- \+ *lemma* category_theory.monad.has_limit_of_comp_forget_has_limit
- \- *def* category_theory.monad.has_limit_of_comp_forget_has_limit
- \+ *lemma* category_theory.monadic_creates_limits
- \- *def* category_theory.monadic_creates_limits

Added src/category_theory/monoidal/of_chosen_finite_products.lean
- \+ *def* category_theory.limits.binary_fan.assoc
- \+ *lemma* category_theory.limits.binary_fan.assoc_fst
- \+ *def* category_theory.limits.binary_fan.assoc_inv
- \+ *lemma* category_theory.limits.binary_fan.assoc_inv_fst
- \+ *lemma* category_theory.limits.binary_fan.assoc_inv_snd
- \+ *lemma* category_theory.limits.binary_fan.assoc_snd
- \+ *def* category_theory.limits.binary_fan.associator
- \+ *def* category_theory.limits.binary_fan.associator_of_limit_cone
- \+ *def* category_theory.limits.binary_fan.braiding
- \+ *def* category_theory.limits.binary_fan.left_unitor
- \+ *def* category_theory.limits.binary_fan.right_unitor
- \+ *def* category_theory.limits.binary_fan.swap
- \+ *lemma* category_theory.limits.binary_fan.swap_fst
- \+ *lemma* category_theory.limits.binary_fan.swap_snd
- \+ *lemma* category_theory.limits.has_binary_product.swap
- \+ *def* category_theory.limits.is_limit.assoc
- \+ *def* category_theory.limits.is_limit.swap_binary_fan
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.associator_naturality
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.braiding_naturality
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.hexagon_forward
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.hexagon_reverse
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.left_unitor_naturality
- \+ *def* category_theory.monoidal_of_chosen_finite_products.monoidal_of_chosen_finite_products_synonym
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.pentagon
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.right_unitor_naturality
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.symmetry
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.tensor_comp
- \+ *def* category_theory.monoidal_of_chosen_finite_products.tensor_hom
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.tensor_id
- \+ *def* category_theory.monoidal_of_chosen_finite_products.tensor_obj
- \+ *lemma* category_theory.monoidal_of_chosen_finite_products.triangle
- \+ *def* category_theory.monoidal_of_chosen_finite_products
- \+ *def* category_theory.symmetric_of_chosen_finite_products

Modified src/category_theory/monoidal/of_has_finite_products.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/over.lean
- \+/\- *def* category_theory.over.iso_mk
- \- *lemma* category_theory.over.iso_mk_hom_left
- \- *lemma* category_theory.over.iso_mk_inv_left

Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.has_coequalizers_of_has_cokernels
- \- *def* category_theory.preadditive.has_coequalizers_of_has_cokernels
- \+ *lemma* category_theory.preadditive.has_colimit_parallel_pair
- \- *def* category_theory.preadditive.has_colimit_parallel_pair
- \+ *lemma* category_theory.preadditive.has_equalizers_of_has_kernels
- \- *def* category_theory.preadditive.has_equalizers_of_has_kernels
- \+ *lemma* category_theory.preadditive.has_limit_parallel_pair
- \- *def* category_theory.preadditive.has_limit_parallel_pair

Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.lift_quot_mk

Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* topological_space.opens.inf_le_left_apply
- \+ *lemma* topological_space.opens.inf_le_left_apply_mk
- \+ *lemma* topological_space.opens.le_supr_apply_mk

Modified src/topology/category/UniformSpace.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* Top.subpresheaf_to_Types.sheaf_condition_fac
- \+ *lemma* Top.subpresheaf_to_Types.sheaf_condition_uniq

Modified src/topology/sheaves/sheaf.lean


Modified src/topology/sheaves/sheaf_of_functions.lean


Modified src/topology/sheaves/sheafify.lean


Modified src/topology/sheaves/stalks.lean




## [2020-09-12 01:05:19](https://github.com/leanprover-community/mathlib/commit/f6a65cf)
chore(scripts): update nolints.txt ([#4118](https://github.com/leanprover-community/mathlib/pull/4118))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-11 17:48:45](https://github.com/leanprover-community/mathlib/commit/7bade58)
feat(logic/basic): Add forall_apply_eq_imp_iff ([#4109](https://github.com/leanprover-community/mathlib/pull/4109))
Also adds forall_apply_eq_imp_iff' for swapped forall arguments
This means that `forall_range_iff` can now be solved by `simp`.
This requires changes in data/pfun and measure_theory/borel_space, where non-terminal `simp`s broke.
#### Estimated changes
Modified src/data/pfun.lean


Modified src/data/set/basic.lean


Modified src/logic/basic.lean
- \+ *theorem* forall_apply_eq_imp_iff'
- \+ *theorem* forall_apply_eq_imp_iff

Modified src/measure_theory/borel_space.lean




## [2020-09-11 17:48:43](https://github.com/leanprover-community/mathlib/commit/17a5807)
feat(category_theory/limits/fubini): another formulation for limits commuting ([#4034](https://github.com/leanprover-community/mathlib/pull/4034))
The statement that you can swap limits, rather than just combine into a single limit as we had before.
(This just uses two copies of the previous isomorphism.)
#### Estimated changes
Modified src/category_theory/limits/fubini.lean
- \+ *def* category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim
- \+ *lemma* category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_hom_π_π
- \+ *lemma* category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_inv_π_π

Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.has_colimit.iso_of_equivalence_hom_π
- \+ *lemma* category_theory.limits.has_colimit.iso_of_equivalence_inv_π
- \- *lemma* category_theory.limits.has_colimit.iso_of_equivalence_π
- \+ *lemma* category_theory.limits.has_limit.iso_of_equivalence_hom_π
- \+ *lemma* category_theory.limits.has_limit.iso_of_equivalence_inv_π
- \- *lemma* category_theory.limits.has_limit.iso_of_equivalence_π

Modified src/category_theory/products/basic.lean




## [2020-09-11 17:48:40](https://github.com/leanprover-community/mathlib/commit/045619e)
feat(topology/sheaves): sheafification ([#3937](https://github.com/leanprover-community/mathlib/pull/3937))
# Sheafification of `Type` valued presheaves
We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.
We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.
We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.
## Future work
Show that the map induced on stalks by `to_sheafify` is the inverse of `stalk_to_fiber`.
Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor.
#### Estimated changes
Modified src/topology/category/Top/open_nhds.lean
- \+ *def* topological_space.open_nhds.inf_le_left
- \+ *def* topological_space.open_nhds.inf_le_right

Modified src/topology/sheaves/local_predicate.lean


Added src/topology/sheaves/sheafify.lean
- \+ *def* Top.presheaf.sheafify.is_germ
- \+ *def* Top.presheaf.sheafify.is_locally_germ
- \+ *def* Top.presheaf.sheafify
- \+ *def* Top.presheaf.sheafify_stalk_iso
- \+ *def* Top.presheaf.stalk_to_fiber
- \+ *lemma* Top.presheaf.stalk_to_fiber_injective
- \+ *lemma* Top.presheaf.stalk_to_fiber_surjective
- \+ *def* Top.presheaf.to_sheafify

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.germ_eq
- \+ *lemma* Top.presheaf.germ_res_apply'



## [2020-09-11 17:48:37](https://github.com/leanprover-community/mathlib/commit/5509a30)
feat(category_theory/skeleton): add skeletal categories and construct a special case ([#3929](https://github.com/leanprover-community/mathlib/pull/3929))
I'm interested in the quotient construction of the skeleton for a thin category in particular for topos and sheafification PRs, but of course the general construction is useful too, so I've marked that as TODO and I'll make a followup PR so that this one doesn't get too big.
The advantage of handling this special case separately is that the skeleton of a thin category is a partial order, and so lattice constructions can be used (which is needed for my application), and also there are nice definitional equalities.
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Added src/category_theory/skeletal.lean
- \+ *lemma* category_theory.functor.eq_of_iso
- \+ *lemma* category_theory.functor_skeletal
- \+ *def* category_theory.skeletal
- \+ *lemma* category_theory.thin_skeleton.comp_to_thin_skeleton
- \+ *lemma* category_theory.thin_skeleton.equiv_of_both_ways
- \+ *def* category_theory.thin_skeleton.map
- \+ *lemma* category_theory.thin_skeleton.map_comp_eq
- \+ *lemma* category_theory.thin_skeleton.map_id_eq
- \+ *lemma* category_theory.thin_skeleton.map_iso_eq
- \+ *def* category_theory.thin_skeleton.map_nat_trans
- \+ *def* category_theory.thin_skeleton.map₂
- \+ *lemma* category_theory.thin_skeleton.skeletal
- \+ *def* category_theory.thin_skeleton
- \+ *def* category_theory.to_thin_skeleton

Deleted src/category_theory/sparse.lean
- \- *def* category_theory.sparse_category

Added src/category_theory/thin.lean
- \+ *def* category_theory.iso_of_both_ways
- \+ *def* category_theory.thin_category



## [2020-09-11 15:53:17](https://github.com/leanprover-community/mathlib/commit/847f87e)
feat(geometry/euclidean/circumcenter): lemmas on orthogonal projection and reflection ([#4087](https://github.com/leanprover-community/mathlib/pull/4087))
Add more lemmas about orthogonal projection and the circumcenter of a
simplex (so substantially simplifying the proof of
`orthogonal_projection_circumcenter`).  Then prove a lemma
`eq_or_eq_reflection_of_dist_eq` that if we fix a distance a point has
to all the vertices of a simplex, any two possible positions of that
point in one dimension higher than the simplex are equal or
reflections of each other in the subspace of the simplex.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.orthogonal_projection_eq_circumcenter_of_dist_eq
- \+ *lemma* affine.simplex.orthogonal_projection_eq_circumcenter_of_exists_dist_eq
- \+ *lemma* euclidean_geometry.eq_or_eq_reflection_of_dist_eq



## [2020-09-11 15:53:15](https://github.com/leanprover-community/mathlib/commit/872a37e)
cleanup(group_theory/presented_group): () -> [], and remove some FIXMEs ([#4076](https://github.com/leanprover-community/mathlib/pull/4076))
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/presented_group.lean
- \- *lemma* presented_group.to_group.inv
- \- *lemma* presented_group.to_group.mul
- \- *lemma* presented_group.to_group.one

Modified src/group_theory/subgroup.lean
- \+/\- *theorem* group.conjugates_of_set_subset
- \+/\- *lemma* group.conjugates_subset_normal
- \- *lemma* monoid_hom.normal_ker
- \- *lemma* subgroup.bot_normal
- \- *lemma* subgroup.center_normal
- \+/\- *lemma* subgroup.le_normalizer_of_normal
- \+/\- *theorem* subgroup.normal_closure_le_normal
- \- *lemma* subgroup.normal_closure_normal
- \+/\- *lemma* subgroup.normal_closure_subset_iff
- \- *lemma* subgroup.normal_comap
- \- *lemma* subgroup.normal_in_normalizer
- \- *lemma* subgroup.normal_of_comm



## [2020-09-11 15:53:13](https://github.com/leanprover-community/mathlib/commit/377c7c9)
feat(category_theory/braided): braiding and unitors ([#4075](https://github.com/leanprover-community/mathlib/pull/4075))
The interaction between braidings and unitors in a braided category.
Requested by @cipher1024 for some work he's doing on monads.
I've changed the statements of some `@[simp]` lemmas, in particular `left_unitor_tensor`, `left_unitor_tensor_inv`, `right_unitor_tensor`, `right_unitor_tensor_inv`. The new theory is that the components of a unitor indexed by a tensor product object are "more complicated" than other unitors. (We already follow the same principle for simplifying associators using the pentagon equation.)
#### Estimated changes
Modified src/category_theory/monoidal/End.lean


Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* category_theory.braiding_left_unitor
- \+ *lemma* category_theory.braiding_left_unitor_aux₁
- \+ *lemma* category_theory.braiding_left_unitor_aux₂
- \+ *lemma* category_theory.braiding_right_unitor
- \+ *lemma* category_theory.braiding_right_unitor_aux₁
- \+ *lemma* category_theory.braiding_right_unitor_aux₂

Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor'
- \+/\- *lemma* category_theory.monoidal_category.left_unitor_tensor
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor_inv'
- \+/\- *lemma* category_theory.monoidal_category.left_unitor_tensor_inv
- \+/\- *lemma* category_theory.monoidal_category.right_unitor_tensor
- \+/\- *lemma* category_theory.monoidal_category.right_unitor_tensor_inv

Modified src/category_theory/monoidal/unitors.lean




## [2020-09-11 15:53:11](https://github.com/leanprover-community/mathlib/commit/a1cbe88)
feat(logic/basic, logic/function/basic): involute ite  ([#4074](https://github.com/leanprover-community/mathlib/pull/4074))
Some lemmas about `ite`:
- `(d)ite_not`: exchanges the branches of an `(d)ite`
  when negating the given prop.
- `involutive.ite_not`: applying an involutive function to an `ite`
  negates the prop
Other changes:
Generalize the arguments for `(d)ite_apply` and `apply_(d)ite(2)`
to `Sort*` over `Type*`.
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* apply_dite2
- \+/\- *lemma* apply_dite
- \+/\- *lemma* apply_ite2
- \+/\- *lemma* apply_ite
- \+/\- *lemma* dite_apply
- \+ *lemma* dite_not
- \+/\- *lemma* ite_apply
- \+ *lemma* ite_not

Modified src/logic/function/basic.lean




## [2020-09-11 15:53:09](https://github.com/leanprover-community/mathlib/commit/832acd6)
feat(data/{sym2,sym}) decidable version of sym2.mem.other, filling out some of sym API ([#4008](https://github.com/leanprover-community/mathlib/pull/4008))
Removes `sym2.vmem` and replaces it with `sym2.mem.other'`, which can get the other element of a pair in the presence of decidable equality. Writing `sym2.mem.other'` was beyond my abilities when I created `sym2.vmem`, and seeing that vmem is extremely specialized and has no immediate use, it's probably best to remove it.
Adds some assorted simp lemmas, and also an additional lemma that `sym2.mem.other` is, in some sense, an involution.
Adds to the API for `sym`.  This is from taking some of the interface for multisets.  (I was exploring whether `sym2 α` should be re-implemented as `sym α 2` and trying to add enough to `sym` to pull it off, but it doesn't seem to be worth it in the end.)
(I'm not committing a recursor for `sym α n`, which lets you represent elements by vectors of length `n`.  It needs some cleanup.)
#### Estimated changes
Modified src/data/sym.lean
- \+ *def* sym.cons'
- \+ *def* sym.cons
- \+ *lemma* sym.cons_equiv_eq_equiv_cons
- \+ *lemma* sym.cons_inj_left
- \+ *lemma* sym.cons_inj_right
- \+ *lemma* sym.cons_of_coe_eq
- \+ *lemma* sym.cons_swap
- \+ *def* sym.mem
- \+ *lemma* sym.mem_cons
- \+ *lemma* sym.mem_cons_of_mem
- \+ *lemma* sym.mem_cons_self
- \+ *def* sym.nil
- \+ *def* sym.of_vector
- \+ *lemma* sym.sound
- \+/\- *def* sym.sym'
- \+/\- *def* sym.sym_equiv_sym'
- \+/\- *def* sym
- \+/\- *def* vector.perm.is_setoid

Modified src/data/sym2.lean
- \+ *lemma* sym2.congr_left
- \+/\- *lemma* sym2.congr_right
- \+ *lemma* sym2.diag_is_diag
- \+ *lemma* sym2.map_pair_eq
- \+ *def* sym2.mem.other'
- \+ *lemma* sym2.mem_from_rel_irrefl_other_ne
- \+ *lemma* sym2.mem_other_mem'
- \+ *lemma* sym2.mem_other_mem
- \+ *lemma* sym2.mem_other_ne
- \+ *lemma* sym2.mem_other_spec'
- \+/\- *lemma* sym2.mem_other_spec
- \- *def* sym2.mk_has_vmem
- \+ *lemma* sym2.other_eq_other'
- \+ *lemma* sym2.other_invol'
- \+ *lemma* sym2.other_invol
- \- *lemma* sym2.other_is_mem_other
- \+ *lemma* sym2.sym2_ext
- \- *def* sym2.vmem.other
- \- *def* sym2.vmem
- \- *lemma* sym2.vmem_other_spec



## [2020-09-11 14:46:51](https://github.com/leanprover-community/mathlib/commit/7886c27)
feat(category_theory/monoidal): lax monoidal functors take monoids to monoids ([#4108](https://github.com/leanprover-community/mathlib/pull/4108))
#### Estimated changes
Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *lemma* Mon_.mul_one_hom
- \+ *lemma* Mon_.one_mul_hom
- \+ *def* Mon_.trivial
- \+ *def* category_theory.lax_monoidal_functor.map_Mon



## [2020-09-11 14:46:48](https://github.com/leanprover-community/mathlib/commit/bd74baa)
feat(algebra/homology/exact): lemmas about exactness ([#4106](https://github.com/leanprover-community/mathlib/pull/4106))
These are a few lemmas on the way to showing how `exact` changes under isomorphisms applied to the objects. It's not everthing one might want; I'm salvaging this from an old branch and unlikely to do more in the near future, but hopefully this is mergeable progress as is.
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.exact.w_assoc
- \+ *lemma* category_theory.exact_of_zero

Modified src/algebra/homology/image_to_kernel_map.lean
- \+ *lemma* category_theory.image_to_kernel_map_comp_iso
- \+ *lemma* category_theory.image_to_kernel_map_iso_comp

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.image.factor_thru_image_pre_comp

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.coequalizer_as_cokernel
- \+ *lemma* category_theory.limits.equalizer_as_kernel



## [2020-09-11 14:46:45](https://github.com/leanprover-community/mathlib/commit/233a802)
feat(algebraic_geometry/Scheme): Spec as Scheme ([#4104](https://github.com/leanprover-community/mathlib/pull/4104))
```lean
def Spec (R : CommRing) : Scheme
```
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *def* algebraic_geometry.Scheme.Spec

Modified src/algebraic_geometry/Spec.lean
- \+ *def* algebraic_geometry.Spec.LocallyRingedSpace

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *def* algebraic_geometry.PresheafedSpace.of_restrict
- \+ *def* algebraic_geometry.PresheafedSpace.restrict_top_iso
- \+ *def* algebraic_geometry.PresheafedSpace.to_restrict_top

Modified src/topology/category/Top/opens.lean
- \+ *def* is_open_map.adjunction



## [2020-09-11 14:46:44](https://github.com/leanprover-community/mathlib/commit/34e0f31)
feat(nnreal): absolute value ([#4098](https://github.com/leanprover-community/mathlib/pull/4098))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.nnreal.norm_eq

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.abs_eq
- \+ *lemma* nnreal.coe_nnabs
- \+ *def* real.nnabs



## [2020-09-11 13:30:01](https://github.com/leanprover-community/mathlib/commit/842a324)
feat(category_theory): the Grothendieck construction ([#3896](https://github.com/leanprover-community/mathlib/pull/3896))
Given a functor `F : C ⥤ Cat`, 
the objects of `grothendieck F` consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`.
(This is only a special case of the real thing: we should treat `Cat` as a 2-category and allow `F` to be a 2-functor / pseudofunctor.)
#### Estimated changes
Modified src/category_theory/category/Cat.lean
- \+ *def* category_theory.Type_to_Cat

Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.eq_to_hom_op
- \+/\- *lemma* category_theory.eq_to_iso_refl
- \+ *lemma* category_theory.inv_eq_to_hom

Added src/category_theory/grothendieck.lean
- \+ *def* category_theory.grothendieck.comp
- \+ *lemma* category_theory.grothendieck.ext
- \+ *def* category_theory.grothendieck.forget
- \+ *def* category_theory.grothendieck.grothendieck_Type_to_Cat
- \+ *def* category_theory.grothendieck.id

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.is_iso.comp_inv_eq
- \+ *lemma* category_theory.is_iso.comp_is_iso_eq
- \+ *lemma* category_theory.is_iso.eq_inv_comp
- \+ *lemma* category_theory.is_iso.inv_comp_eq



## [2020-09-11 11:35:29](https://github.com/leanprover-community/mathlib/commit/0c57b2d)
doc(category_theory): add doc-strings and links to the stacks project ([#4107](https://github.com/leanprover-community/mathlib/pull/4107))
We'd been discussing adding a `@[stacks "007B"]` tag to add cross-references to the stacks project (and possibly include links back again -- they say they're keen).
I'm not certain that we actually have the documentation maintenance enthusiasm to make this viable, so this PR is a more lightweight solution: adding lots of links to the stacks project from doc-strings. I'd be very happy to switch back to the attribute approach later.
This is pretty close to exhaustive for the "category theory preliminaries" chapter of the stacks project, but doesn't attempt to go beyond that. I've only included links where we formalise all, or almost all (in which case I've usually left a note), of the corresponding tag.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/fubini.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/over/connected.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/over.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.yoneda

Modified src/topology/sheaves/forget.lean




## [2020-09-11 11:35:27](https://github.com/leanprover-community/mathlib/commit/3965e06)
chore(*): use new `extends_priority` default of 100, part 2 ([#4101](https://github.com/leanprover-community/mathlib/pull/4101))
This completes the changes started in [#4066](https://github.com/leanprover-community/mathlib/pull/4066).
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/directed.lean


Modified src/order/lattice.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/rel_classes.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/tactic/lint/type_classes.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/premetric_space.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified test/simps.lean




## [2020-09-11 11:35:25](https://github.com/leanprover-community/mathlib/commit/bc78621)
feat(geometry/euclidean/monge_point): reflection of circumcenter ([#4062](https://github.com/leanprover-community/mathlib/pull/4062))
Show that the distance from the orthocenter of a triangle to the
reflection of the circumcenter in a side equals the circumradius (a
key fact for proving various standard properties of orthocentric
systems).
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.reflection_circumcenter_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_reflection_circumcenter_weights_with_circumcenter

Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* affine.triangle.dist_orthocenter_reflection_circumcenter
- \+ *lemma* affine.triangle.dist_orthocenter_reflection_circumcenter_finset



## [2020-09-11 11:35:23](https://github.com/leanprover-community/mathlib/commit/4ce27a5)
feat(category_theory/limits): filtered colimits commute with finite limits (in Type) ([#4046](https://github.com/leanprover-community/mathlib/pull/4046))
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean


Modified src/category_theory/filtered.lean
- \+/\- *def* category_theory.is_filtered.sup
- \- *lemma* category_theory.is_filtered.sup_exists'
- \+/\- *lemma* category_theory.is_filtered.sup_exists
- \+/\- *def* category_theory.is_filtered.to_sup
- \+/\- *lemma* category_theory.is_filtered.to_sup_commutes

Added src/category_theory/limits/colimit_limit.lean
- \+ *def* category_theory.limits.colimit_limit_to_limit_colimit
- \+ *lemma* category_theory.limits.map_id_left_eq_curry_map
- \+ *lemma* category_theory.limits.map_id_right_eq_curry_swap_map
- \+ *lemma* category_theory.limits.ι_colimit_limit_to_limit_colimit_π
- \+ *lemma* category_theory.limits.ι_colimit_limit_to_limit_colimit_π_apply

Added src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean
- \+ *lemma* category_theory.limits.colimit_limit_to_limit_colimit_injective
- \+ *lemma* category_theory.limits.colimit_limit_to_limit_colimit_surjective

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.w
- \+/\- *lemma* category_theory.limits.limit.w

Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.colimit_sound'
- \+ *def* category_theory.limits.types.limit.mk
- \+ *lemma* category_theory.limits.types.limit.π_mk

Modified src/category_theory/types.lean
- \+ *def* category_theory.is_iso_equiv_bijective



## [2020-09-11 06:18:46](https://github.com/leanprover-community/mathlib/commit/80a9e4f)
refactor(data/mv_polynomial/pderivative): make pderivative a linear map ([#4095](https://github.com/leanprover-community/mathlib/pull/4095))
Make `pderivative i` a linear map as suggested at https://github.com/leanprover-community/mathlib/pull/4083#issuecomment-689712833
#### Estimated changes
Modified src/data/mv_polynomial/pderivative.lean
- \- *def* mv_polynomial.pderivative.add_monoid_hom
- \- *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \+/\- *def* mv_polynomial.pderivative
- \- *lemma* mv_polynomial.pderivative_add
- \- *lemma* mv_polynomial.pderivative_zero



## [2020-09-11 00:47:31](https://github.com/leanprover-community/mathlib/commit/9a24f68)
chore(scripts): update nolints.txt ([#4105](https://github.com/leanprover-community/mathlib/pull/4105))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-10 18:33:51](https://github.com/leanprover-community/mathlib/commit/7d88b31)
feat(ring_theory/algebra_operations): add le_div_iff_mul_le ([#4102](https://github.com/leanprover-community/mathlib/pull/4102))
#### Estimated changes
Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* submodule.le_div_iff_mul_le



## [2020-09-10 16:46:37](https://github.com/leanprover-community/mathlib/commit/e33a777)
feat(data/fin): iffs about succ_above ordering ([#4092](https://github.com/leanprover-community/mathlib/pull/4092))
New lemmas:
`succ_above_lt_iff`
`lt_succ_above_iff`
These help avoid needing to do case analysis when faced with
inequalities about `succ_above`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.lt_succ_above_iff
- \+ *lemma* fin.succ_above_lt_iff



## [2020-09-10 14:56:55](https://github.com/leanprover-community/mathlib/commit/38d1715)
chore(*): update to Lean 3.20.0c, account for nat.pow removal from core ([#3985](https://github.com/leanprover-community/mathlib/pull/3985))
Outline:
* `nat.pow` has been removed from the core library.
  We now use the instance `monoid.pow` to provide `has_pow ℕ ℕ`.
* To accomodate this, `algebra.group_power` has been split into a directory.
  `algebra.group_power.basic` contains the definitions of `monoid.pow` and `nsmul`
  and whatever lemmas can be stated with very few imports. It is imported in `data.nat.basic`.
  The rest of `algebra.group_power` has moved to `algebra.group_power.lemmas`.
* The new `has_pow ℕ ℕ` now satisfies a different definitional equality:
  `a^(n+1) = a * a^n` (rather than `a^(n+1) = a^n * a`).
  As a temporary measure, the lemma `nat.pow_succ` provides the old equality
  but I plan to deprecate it in favor of the more general `pow_succ'`.
  The lemma `nat.pow_eq_pow` is gone--the two sides are now the same in all respects
  so it can be deleted wherever it was used.
* The lemmas from core that mention `nat.pow` have been moved into `data.nat.lemmas`
  and their proofs adjusted as needed to take into account the new definition.
* The module `data.bitvec` from core has moved to `data.bitvec.core` in mathlib.
Future plans:
* Remove `nat.` lemmas redundant with general `group_power` ones, like `nat.pow_add`.
  This will be easier after further shuffling of modules.
#### Estimated changes
Modified leanpkg.toml


Added src/algebra/group_power/basic.lean
- \+ *theorem* add_nsmul
- \+ *theorem* commute.pow_left
- \+ *theorem* commute.pow_pow
- \+ *theorem* commute.pow_pow_self
- \+ *theorem* commute.pow_right
- \+ *theorem* commute.pow_self
- \+ *theorem* commute.self_pow
- \+ *def* gpow
- \+ *def* gsmul
- \+ *def* monoid.pow
- \+ *def* nsmul
- \+ *theorem* nsmul_add_comm'
- \+ *theorem* pow_add
- \+ *theorem* pow_mul_comm'
- \+ *theorem* pow_succ'
- \+ *theorem* pow_succ
- \+ *theorem* pow_two
- \+ *theorem* pow_zero
- \+ *lemma* semiconj_by.pow_right
- \+ *theorem* succ_nsmul'
- \+ *theorem* succ_nsmul
- \+ *theorem* two_nsmul
- \+ *theorem* zero_nsmul

Added src/algebra/group_power/default.lean


Renamed src/algebra/group_power.lean to src/algebra/group_power/lemmas.lean
- \- *theorem* add_nsmul
- \- *theorem* commute.pow_left
- \- *theorem* commute.pow_pow
- \- *theorem* commute.pow_pow_self
- \- *theorem* commute.pow_right
- \- *theorem* commute.pow_self
- \- *theorem* commute.self_pow
- \- *def* gpow
- \- *def* gsmul
- \- *def* monoid.pow
- \- *theorem* nat.pow_eq_pow
- \- *def* nsmul
- \- *theorem* nsmul_add_comm'
- \- *theorem* pow_add
- \- *theorem* pow_mul_comm'
- \- *theorem* pow_succ'
- \- *theorem* pow_succ
- \- *theorem* pow_two
- \- *theorem* pow_zero
- \- *lemma* semiconj_by.pow_right
- \- *theorem* succ_nsmul'
- \- *theorem* succ_nsmul
- \- *theorem* two_nsmul
- \- *theorem* zero_nsmul

Modified src/analysis/specific_limits.lean


Modified src/data/bitvec/basic.lean


Added src/data/bitvec/core.lean
- \+ *def* bitvec.adc
- \+ *def* bitvec.add_lsb
- \+ *def* bitvec.and
- \+ *def* bitvec.append
- \+ *def* bitvec.bits_to_nat
- \+ *theorem* bitvec.bits_to_nat_to_bool
- \+ *theorem* bitvec.bits_to_nat_to_list
- \+ *def* bitvec.fill_shr
- \+ *def* bitvec.not
- \+ *theorem* bitvec.of_nat_succ
- \+ *def* bitvec.or
- \+ *def* bitvec.sbb
- \+ *def* bitvec.sborrow
- \+ *def* bitvec.sge
- \+ *def* bitvec.sgt
- \+ *def* bitvec.shl
- \+ *def* bitvec.sle
- \+ *def* bitvec.slt
- \+ *def* bitvec.sshr
- \+ *theorem* bitvec.to_nat_append
- \+ *theorem* bitvec.to_nat_of_nat
- \+ *def* bitvec.uborrow
- \+ *def* bitvec.uge
- \+ *def* bitvec.ugt
- \+ *def* bitvec.ule
- \+ *def* bitvec.ult
- \+ *def* bitvec.ushr
- \+ *def* bitvec.xor
- \+ *def* bitvec

Modified src/data/fintype/card.lean


Modified src/data/nat/basic.lean
- \+ *theorem* nat.mod_pow_succ
- \+/\- *lemma* nat.one_pow
- \+ *lemma* nat.one_shiftl
- \+ *theorem* nat.pos_pow_of_pos
- \+ *theorem* nat.pow_le_pow_of_le_left
- \+ *theorem* nat.pow_le_pow_of_le_right
- \+ *theorem* nat.pow_lt_pow_of_lt_left
- \+ *theorem* nat.pow_lt_pow_of_lt_right
- \+ *theorem* nat.pow_one
- \+/\- *lemma* nat.pow_right_injective
- \+/\- *lemma* nat.pow_right_strict_mono
- \+ *lemma* nat.pow_succ
- \+/\- *theorem* nat.pow_two
- \+ *lemma* nat.pow_zero
- \+ *lemma* nat.shiftl'_tt_eq_mul_pow
- \+ *lemma* nat.shiftl_eq_mul_pow
- \+ *lemma* nat.shiftr_eq_div_pow
- \+ *theorem* nat.zero_pow
- \+ *lemma* nat.zero_shiftl
- \+ *lemma* nat.zero_shiftr

Modified src/data/nat/gcd.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/prime.lean


Modified src/data/num/bitwise.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/ring_homs.lean
- \+/\- *lemma* padic_int.lim_nth_hom_add
- \+/\- *lemma* padic_int.lim_nth_hom_mul

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/separable.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/primorial.lean


Modified src/ring_theory/multiplicity.lean


Modified src/tactic/norm_num.lean
- \- *lemma* norm_num.from_nat_pow

Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified test/localized/localized.lean




## [2020-09-10 13:02:29](https://github.com/leanprover-community/mathlib/commit/d5be9f3)
refactor(data/mv_polynomial): move `smul` lemmas into basic.lean ([#4097](https://github.com/leanprover-community/mathlib/pull/4097))
`C_mul'`, `smul_eq_C_mul` and `smul_eval` seemed a bit out of place in `comm_ring.lean`, since they only need `comm_semiring α`. So I moved them to `basic.lean` where they probably fit in a bit better?
I've also golfed the proof of `smul_eq_C_mul`.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *theorem* mv_polynomial.C_mul'
- \+ *lemma* mv_polynomial.smul_eq_C_mul
- \+ *lemma* mv_polynomial.smul_eval

Modified src/data/mv_polynomial/comm_ring.lean
- \- *theorem* mv_polynomial.C_mul'
- \- *lemma* mv_polynomial.smul_eq_C_mul
- \- *lemma* mv_polynomial.smul_eval



## [2020-09-10 13:02:28](https://github.com/leanprover-community/mathlib/commit/19b9ae6)
feat(data/mv_polynomial): a few facts about `constant_coeff` and `aeval` ([#4085](https://github.com/leanprover-community/mathlib/pull/4085))
A few additional facts about `constant_coeff_map` and `aeval` from the witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.aeval_eq_zero
- \+ *lemma* mv_polynomial.constant_coeff_comp_map
- \+ *lemma* mv_polynomial.constant_coeff_map
- \+ *lemma* mv_polynomial.eval₂_hom_eq_zero



## [2020-09-10 13:02:25](https://github.com/leanprover-community/mathlib/commit/d857def)
feat(slim_check): make `shrink` recursive ([#4038](https://github.com/leanprover-community/mathlib/pull/4038))
Make example shrinking recursive to make it faster and more reliable. It now acts more like a binary search and less like a linear search.
#### Estimated changes
Renamed src/data/lazy_list2.lean to src/data/lazy_list/basic.lean
- \+ *lemma* lazy_list.append_assoc
- \+ *lemma* lazy_list.append_bind
- \+ *lemma* lazy_list.append_nil
- \+ *def* lazy_list.find
- \+ *def* lazy_list.mfirst
- \+ *def* lazy_list.reverse

Modified src/data/pnat/basic.lean
- \+ *def* pnat.nat_pred

Modified src/tactic/interactive.lean


Modified src/testing/slim_check/sampleable.lean
- \- *def* slim_check.int.shrink'
- \- *def* slim_check.int.shrink
- \+ *def* slim_check.iterate_shrink
- \- *def* slim_check.lazy_list.lseq
- \+ *lemma* slim_check.list.one_le_sizeof
- \- *def* slim_check.list.shrink'
- \+ *def* slim_check.list.shrink_one
- \+ *def* slim_check.list.shrink_removes
- \+/\- *def* slim_check.list.shrink_with
- \+ *lemma* slim_check.list.sizeof_append_lt_left
- \+ *lemma* slim_check.list.sizeof_cons_lt_left
- \+ *lemma* slim_check.list.sizeof_cons_lt_right
- \+ *lemma* slim_check.list.sizeof_drop_lt_sizeof_of_lt_length
- \+/\- *def* slim_check.nat.shrink'
- \+/\- *def* slim_check.nat.shrink
- \+ *def* slim_check.no_shrink.get
- \+ *def* slim_check.no_shrink.mk
- \+ *def* slim_check.no_shrink
- \+ *def* slim_check.prod.shrink
- \+ *def* slim_check.rec_shrink
- \+/\- *def* slim_check.sampleable.lift
- \+ *def* slim_check.shrink_fn
- \+ *def* slim_check.sizeof_lt
- \+/\- *def* slim_check.sum.shrink
- \+ *lemma* slim_check.tree.one_le_sizeof
- \+/\- *def* slim_check.tree.shrink_with

Modified src/testing/slim_check/testable.lean
- \+/\- *def* slim_check.minimize
- \+ *def* slim_check.minimize_aux



## [2020-09-10 11:22:25](https://github.com/leanprover-community/mathlib/commit/55cab6c)
feat(data/{int,nat}/cast): dvd cast lemmas ([#4086](https://github.com/leanprover-community/mathlib/pull/4086))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* int.coe_int_dvd

Modified src/data/nat/cast.lean
- \+ *lemma* nat.coe_nat_dvd



## [2020-09-10 08:56:58](https://github.com/leanprover-community/mathlib/commit/49bb92d)
feat(ring_theory/dedekind_domain): definitions ([#4000](https://github.com/leanprover-community/mathlib/pull/4000))
Defines `is_dedekind_domain` in three variants:
1.  `is_dedekind_domain`: Noetherian, Integrally closed, Krull dimension 1, thanks to @Vierkantor 
2. `is_dedekind_domain_dvr`: Noetherian, localization at every nonzero prime is a DVR
3. `is_dedekind_domain_inv`: Every nonzero ideal is invertible.
TODO: prove that these definitions are equivalent.
This PR also includes some misc. lemmas required to show the definitions are independent of choice of fraction field.
Co-Authored-By: mushokunosora <knaka3435@gmail.com>
Co-Authored-By: faenuccio <filippo.nuccio@univ-st-etienne.fr>
Co-Authored-By: Vierkantor <vierkantor@vierkantor.com>
#### Estimated changes
Modified docs/references.bib


Modified src/ring_theory/algebra.lean
- \+/\- *lemma* alg_equiv.bijective
- \+/\- *lemma* alg_equiv.coe_alg_hom
- \+/\- *lemma* alg_equiv.coe_ring_equiv
- \+/\- *lemma* alg_equiv.commutes
- \+/\- *lemma* alg_equiv.injective
- \+/\- *lemma* alg_equiv.map_add
- \+/\- *lemma* alg_equiv.map_mul
- \+/\- *lemma* alg_equiv.map_one
- \+/\- *lemma* alg_equiv.map_sum
- \+/\- *lemma* alg_equiv.map_zero
- \+/\- *lemma* alg_equiv.surjective
- \+ *def* alg_equiv.to_alg_hom
- \+ *lemma* alg_equiv.to_alg_hom_eq_coe
- \+ *lemma* alg_equiv.to_alg_hom_to_linear_map
- \+ *theorem* alg_equiv.to_linear_equiv_inj
- \+ *lemma* alg_equiv.to_linear_equiv_to_linear_map
- \+ *def* alg_equiv.to_linear_map
- \+ *lemma* alg_equiv.to_linear_map_apply
- \+ *theorem* alg_equiv.to_linear_map_inj
- \+ *lemma* alg_equiv.trans_to_linear_map
- \+ *lemma* subalgebra.mem_map

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* submodule.map_div

Added src/ring_theory/dedekind_domain.lean
- \+ *lemma* is_dedekind_domain_iff
- \+ *lemma* is_dedekind_domain_inv_iff
- \+ *lemma* ring.dimension_le_one.integral_closure
- \+ *lemma* ring.dimension_le_one.principal_ideal_ring
- \+ *def* ring.dimension_le_one

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.coe_mk
- \+ *lemma* ring.fractional_ideal.div_zero
- \+ *lemma* ring.fractional_ideal.exists_ne_zero_mem_is_integer
- \+ *lemma* ring.fractional_ideal.inv_eq
- \+ *lemma* ring.fractional_ideal.inv_zero
- \+/\- *lemma* ring.fractional_ideal.map_add
- \+ *lemma* ring.fractional_ideal.map_coe_ideal
- \+/\- *lemma* ring.fractional_ideal.map_comp
- \+ *lemma* ring.fractional_ideal.map_div
- \+ *lemma* ring.fractional_ideal.map_eq_zero_iff
- \+/\- *lemma* ring.fractional_ideal.map_equiv_apply
- \+/\- *lemma* ring.fractional_ideal.map_id
- \+ *lemma* ring.fractional_ideal.map_inv
- \+ *lemma* ring.fractional_ideal.map_map_symm
- \+/\- *lemma* ring.fractional_ideal.map_mul
- \+ *lemma* ring.fractional_ideal.map_ne_zero
- \+ *lemma* ring.fractional_ideal.map_one
- \+ *lemma* ring.fractional_ideal.map_symm_map
- \+ *lemma* ring.fractional_ideal.map_zero
- \+ *lemma* ring.fractional_ideal.mem_map

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.bot_lt_of_maximal
- \+ *lemma* ring.exists_not_is_unit_of_not_is_field
- \+ *lemma* ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top
- \+ *lemma* ring.not_is_field_iff_exists_prime
- \+ *lemma* ring.not_is_field_of_subsingleton

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.span_mul_span'
- \+ *lemma* ideal.span_singleton_mul_span_singleton

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* integral_closure_map_alg_equiv

Modified src/ring_theory/localization.lean
- \+ *def* fraction_ring.of
- \+ *lemma* localization.alg_equiv_of_quotient_apply
- \+ *lemma* localization.alg_equiv_of_quotient_symm_apply
- \- *def* of



## [2020-09-10 07:43:56](https://github.com/leanprover-community/mathlib/commit/8e9b1f0)
feat(linear_algebra): add `restrict` for endomorphisms ([#4053](https://github.com/leanprover-community/mathlib/pull/4053))
Add a `restrict` function for endomorphisms. Add some lemmas about the new function, including one about generalized eigenspaces. Add some additional lemmas about `linear_map.comp` that I do not use in the final proof, but still consider useful.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.add_comp
- \+ *lemma* linear_map.comp_add
- \+ *lemma* linear_map.comp_neg
- \+ *lemma* linear_map.comp_sub
- \+ *def* linear_map.restrict
- \+ *lemma* linear_map.restrict_apply
- \+ *lemma* linear_map.restrict_eq_cod_restrict_dom_restrict
- \+ *lemma* linear_map.restrict_eq_dom_restrict_cod_restrict
- \+ *lemma* linear_map.sub_comp
- \+ *lemma* linear_map.subtype_comp_restrict

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.generalized_eigenspace_restrict



## [2020-09-10 05:42:47](https://github.com/leanprover-community/mathlib/commit/47264da)
feat(linear_algebra): tiny missing pieces ([#4089](https://github.com/leanprover-community/mathlib/pull/4089))
From the sphere eversion project.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.applyₗ

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.equiv_fin
- \+ *lemma* finite_dimensional.fin_basis



## [2020-09-10 01:34:24](https://github.com/leanprover-community/mathlib/commit/9f55ed7)
feat(data/polynomial/ring_division): make `polynomial.roots` a multiset ([#4061](https://github.com/leanprover-community/mathlib/pull/4061))
The original definition of `polynomial.roots` was basically "while ∃ x, p.is_root x { finset.insert x polynomial.roots }", so it was not
too hard to replace this with `multiset.cons`.
I tried to refactor most usages of `polynomial.roots` to talk about the multiset instead of coercing it to a finset, since that should give a bit more power to the results.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.count_roots
- \- *lemma* polynomial.exists_finset_roots
- \+ *lemma* polynomial.exists_multiset_roots
- \+/\- *def* polynomial.nth_roots
- \+ *lemma* polynomial.root_multiplicity_X_sub_C
- \+ *lemma* polynomial.root_multiplicity_X_sub_C_self
- \+ *lemma* polynomial.root_multiplicity_eq_zero
- \+ *lemma* polynomial.root_multiplicity_mul
- \+ *lemma* polynomial.root_multiplicity_pos
- \+ *lemma* polynomial.root_multiplicity_zero
- \+/\- *lemma* polynomial.roots_C
- \+/\- *lemma* polynomial.roots_X_sub_C
- \+/\- *lemma* polynomial.roots_mul
- \+/\- *lemma* polynomial.roots_zero

Modified src/field_theory/finite.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.count_roots_le_one
- \- *lemma* polynomial.degree_separable_eq_card_roots
- \- *lemma* polynomial.eq_prod_roots_of_separable
- \+ *lemma* polynomial.multiplicity_le_one_of_seperable
- \- *lemma* polynomial.nat_degree_separable_eq_card_roots
- \+ *lemma* polynomial.nodup_roots
- \+ *lemma* polynomial.root_multiplicity_le_one_of_seperable

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.degree_eq_card_roots
- \+ *lemma* polynomial.eq_prod_roots_of_splits
- \+ *lemma* polynomial.nat_degree_eq_card_roots
- \+ *lemma* polynomial.nat_degree_multiset_prod

Modified src/linear_algebra/lagrange.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.dvd_iff_multiplicity_pos



## [2020-09-09 23:56:32](https://github.com/leanprover-community/mathlib/commit/660a6c4)
feat(topology): misc topological lemmas ([#4091](https://github.com/leanprover-community/mathlib/pull/4091))
From the sphere eversion project.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.is_countably_generated.inf
- \+ *lemma* filter.is_countably_generated.inf_principal
- \+ *lemma* filter.is_countably_generated_principal

Modified src/order/filter/basic.lean
- \+ *lemma* filter.diff_mem_inf_principal_compl

Modified src/topology/bases.lean
- \+ *def* topological_space.dense_seq
- \+ *lemma* topological_space.dense_seq_dense
- \+ *lemma* topological_space.exists_dense_seq
- \+ *lemma* topological_space.is_countably_generated_nhds
- \+ *lemma* topological_space.is_countably_generated_nhds_within

Modified src/topology/continuous_on.lean
- \+ *lemma* diff_mem_nhds_within_compl



## [2020-09-09 23:56:30](https://github.com/leanprover-community/mathlib/commit/9da39cf)
feat(ordered_field): missing inequality lemmas ([#4090](https://github.com/leanprover-community/mathlib/pull/4090))
From the sphere eversion project.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* inv_mul_le_iff'
- \+ *lemma* inv_mul_le_iff
- \+ *lemma* inv_mul_lt_iff'
- \+ *lemma* inv_mul_lt_iff
- \+ *lemma* mul_inv_le_iff'
- \+ *lemma* mul_inv_le_iff
- \+ *lemma* mul_inv_lt_iff'
- \+ *lemma* mul_inv_lt_iff



## [2020-09-09 22:00:53](https://github.com/leanprover-community/mathlib/commit/0967f84)
doc(*): add some docstrings ([#4073](https://github.com/leanprover-community/mathlib/pull/4073))
#### Estimated changes
Modified src/data/nat/parity.lean


Modified src/logic/basic.lean




## [2020-09-09 16:00:30](https://github.com/leanprover-community/mathlib/commit/44d356c)
feat(tactic/explode): correctly indent long statements ([#4084](https://github.com/leanprover-community/mathlib/pull/4084))
`#explode` didn't indent long statements in the proof, such as in this lemma:
```lean
import tactic.explode
variables (p q r : ℕ → Prop)
lemma ex (h : ∃ x, ∀ y, ∃ z, p x ∧ q y ∧ r z) :
              ∃ z, ∀ y, ∃ x, p x ∧ q y ∧ r z :=
Exists.rec_on h $ λ x h',
Exists.rec_on (h' 0) $ λ z h'',
⟨z, λ y,
  Exists.rec_on (h' y) $ λ w h''',
  ⟨x, h''.1, h'''.2.1, h''.2.2⟩⟩
#explode ex
```
#### Estimated changes
Modified src/tactic/explode.lean




## [2020-09-09 16:00:28](https://github.com/leanprover-community/mathlib/commit/11e62b0)
fix(data/mv_polynomial/pderivative): rename variables and file, make it universe polymorphic ([#4083](https://github.com/leanprover-community/mathlib/pull/4083))
This file originally used different variable names to the rest of `mv_polynomial`. I've changed it to now use the same conventions as the other files.
I also renamed the file to `pderivative.lean` to be consistent with `derivative.lean` for polynomials.
The types of the coefficient ring and the indexing variables are now universe polymorphic.
The diff shows it as new files, but the only changes are fixing the statements and proofs.
#### Estimated changes
Deleted src/data/mv_polynomial/pderiv.lean
- \- *def* mv_polynomial.pderivative.add_monoid_hom
- \- *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \- *def* mv_polynomial.pderivative
- \- *lemma* mv_polynomial.pderivative_C
- \- *lemma* mv_polynomial.pderivative_C_mul
- \- *lemma* mv_polynomial.pderivative_add
- \- *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \- *lemma* mv_polynomial.pderivative_monomial
- \- *lemma* mv_polynomial.pderivative_monomial_mul
- \- *lemma* mv_polynomial.pderivative_monomial_single
- \- *lemma* mv_polynomial.pderivative_mul
- \- *lemma* mv_polynomial.pderivative_zero

Added src/data/mv_polynomial/pderivative.lean
- \+ *def* mv_polynomial.pderivative.add_monoid_hom
- \+ *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \+ *def* mv_polynomial.pderivative
- \+ *lemma* mv_polynomial.pderivative_C
- \+ *lemma* mv_polynomial.pderivative_C_mul
- \+ *lemma* mv_polynomial.pderivative_add
- \+ *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \+ *lemma* mv_polynomial.pderivative_monomial
- \+ *lemma* mv_polynomial.pderivative_monomial_mul
- \+ *lemma* mv_polynomial.pderivative_monomial_single
- \+ *lemma* mv_polynomial.pderivative_mul
- \+ *lemma* mv_polynomial.pderivative_zero



## [2020-09-09 14:54:02](https://github.com/leanprover-community/mathlib/commit/98061d1)
fix(tactic/linarith): treat powers like multiplication ([#4082](https://github.com/leanprover-community/mathlib/pull/4082))
`ring` understands that natural number exponents are repeated multiplication, so it's safe for `linarith` to do the same. This is unlikely to affect anything except `nlinarith` calls, which are now slightly more powerful.
#### Estimated changes
Modified src/tactic/linarith/parsing.lean


Modified test/linarith.lean




## [2020-09-09 13:02:22](https://github.com/leanprover-community/mathlib/commit/d6e7ee0)
doc(ring_theory/localization): fix docstring typo ([#4081](https://github.com/leanprover-community/mathlib/pull/4081))
#### Estimated changes
Modified src/ring_theory/localization.lean




## [2020-09-09 13:02:19](https://github.com/leanprover-community/mathlib/commit/297a14e)
feat(linear_algebra/affine_space): more lemmas ([#4055](https://github.com/leanprover-community/mathlib/pull/4055))
Add some more lemmas about affine spaces.  One,
`affine_span_insert_affine_span`, is extracted from the proof of
`exists_unique_dist_eq_of_affine_independent` as it turned out to be
useful elsewhere.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean


Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_span_insert_affine_span
- \+ *lemma* affine_span_insert_eq_affine_span
- \+ *lemma* affine_span_mono
- \+ *lemma* subset_affine_span

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_def
- \+ *lemma* affine_independent_iff_of_fintype
- \+ *lemma* affine_independent_of_affine_independent_set_of_injective
- \+ *lemma* affine_independent_of_subset_affine_independent



## [2020-09-09 13:02:17](https://github.com/leanprover-community/mathlib/commit/40de35a)
feat(order/conditionally_complete_lattice, topology/algebra/ordered): inherited order properties for `ord_connected` subset ([#3991](https://github.com/leanprover-community/mathlib/pull/3991))
If `α` is `densely_ordered`, then so is the subtype `s`, for any `ord_connected` subset `s` of `α`.
Same result for `order_topology`.
Same result for `conditionally_complete_linear_order`, under the hypothesis `inhabited s`.
#### Estimated changes
Modified src/data/set/intervals/ord_connected.lean


Modified src/order/basic.lean
- \+ *lemma* strict_mono_coe

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* Inf_within_of_ord_connected
- \+ *lemma* Sup_within_of_ord_connected
- \+ *lemma* monotone.cInf_image_le
- \+ *lemma* monotone.cSup_image_le
- \+ *lemma* monotone.le_cInf_image
- \+ *lemma* monotone.le_cSup_image
- \+ *lemma* subset_Inf_def
- \+ *lemma* subset_Inf_of_within
- \+ *lemma* subset_Sup_def
- \+ *lemma* subset_Sup_of_within

Modified src/topology/algebra/ordered.lean




## [2020-09-09 11:11:47](https://github.com/leanprover-community/mathlib/commit/2ab31f9)
chore(*): use new `extends_priority` default of 100 ([#4066](https://github.com/leanprover-community/mathlib/pull/4066))
This is the first of (most likely) two PRs which remove the use of
`set_option default_priority 100` in favor of per-instance priority
attributes, taking advantage of Lean 3.19c's new default priority
of 100 on instances produced by `extends`.
#### Estimated changes
Modified src/algebra/add_torsor.lean


Modified src/algebra/char_p.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/gcd_monoid.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group_ring_action.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/ordered.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring/basic.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/computability/primrec.lean


Modified src/control/basic.lean


Modified src/control/bitraversable/basic.lean


Modified src/control/lawful_fix.lean


Modified src/control/monad/cont.lean


Modified src/control/traversable/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/equiv/denumerable.lean


Modified src/deprecated/group.lean


Modified src/deprecated/subgroup.lean


Modified src/deprecated/subring.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/algebra/lie_group.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/group_theory/group_action.lean


Modified src/linear_algebra/linear_action.lean


Modified src/logic/nontrivial.lean




## [2020-09-09 08:45:23](https://github.com/leanprover-community/mathlib/commit/77c8415)
refactor(data/mv_polynomial): split into multiple files ([#4070](https://github.com/leanprover-community/mathlib/pull/4070))
`mv_polynomial.lean` was getting massive and hard to explore. This breaks it into (somewhat arbitrary) pieces. While `basic.lean` is still fairly long, there are a lot of basics about multivariate polynomials, and I think it's reasonable.
#### Estimated changes
Deleted src/data/mv_polynomial.lean
- \- *def* mv_polynomial.C
- \- *lemma* mv_polynomial.C_0
- \- *lemma* mv_polynomial.C_1
- \- *lemma* mv_polynomial.C_add
- \- *lemma* mv_polynomial.C_eq_coe_nat
- \- *lemma* mv_polynomial.C_inj
- \- *lemma* mv_polynomial.C_injective
- \- *theorem* mv_polynomial.C_mul'
- \- *lemma* mv_polynomial.C_mul
- \- *lemma* mv_polynomial.C_mul_monomial
- \- *lemma* mv_polynomial.C_neg
- \- *lemma* mv_polynomial.C_pow
- \- *lemma* mv_polynomial.C_sub
- \- *def* mv_polynomial.X
- \- *lemma* mv_polynomial.X_pow_eq_single
- \- *def* mv_polynomial.aeval
- \- *lemma* mv_polynomial.aeval_C
- \- *lemma* mv_polynomial.aeval_X
- \- *theorem* mv_polynomial.aeval_def
- \- *lemma* mv_polynomial.aeval_eq_constant_coeff_of_vars
- \- *lemma* mv_polynomial.aeval_eq_eval₂_hom
- \- *lemma* mv_polynomial.aeval_monomial
- \- *lemma* mv_polynomial.aeval_zero'
- \- *lemma* mv_polynomial.aeval_zero
- \- *lemma* mv_polynomial.alg_hom_C
- \- *lemma* mv_polynomial.alg_hom_ext
- \- *theorem* mv_polynomial.algebra_map_eq
- \- *lemma* mv_polynomial.as_sum
- \- *lemma* mv_polynomial.coe_eval₂_hom
- \- *def* mv_polynomial.coeff
- \- *lemma* mv_polynomial.coeff_C
- \- *lemma* mv_polynomial.coeff_C_mul
- \- *lemma* mv_polynomial.coeff_X'
- \- *lemma* mv_polynomial.coeff_X
- \- *lemma* mv_polynomial.coeff_X_pow
- \- *lemma* mv_polynomial.coeff_add
- \- *def* mv_polynomial.coeff_coe_to_fun
- \- *lemma* mv_polynomial.coeff_eq_zero_of_total_degree_lt
- \- *lemma* mv_polynomial.coeff_map
- \- *lemma* mv_polynomial.coeff_monomial
- \- *lemma* mv_polynomial.coeff_mul
- \- *lemma* mv_polynomial.coeff_mul_X'
- \- *lemma* mv_polynomial.coeff_mul_X
- \- *lemma* mv_polynomial.coeff_neg
- \- *lemma* mv_polynomial.coeff_sub
- \- *lemma* mv_polynomial.coeff_sum
- \- *lemma* mv_polynomial.coeff_zero
- \- *lemma* mv_polynomial.coeff_zero_X
- \- *lemma* mv_polynomial.comp_aeval
- \- *lemma* mv_polynomial.comp_eval₂_hom
- \- *def* mv_polynomial.constant_coeff
- \- *lemma* mv_polynomial.constant_coeff_C
- \- *lemma* mv_polynomial.constant_coeff_X
- \- *lemma* mv_polynomial.constant_coeff_eq
- \- *lemma* mv_polynomial.constant_coeff_monomial
- \- *def* mv_polynomial.degree_of
- \- *def* mv_polynomial.degrees
- \- *lemma* mv_polynomial.degrees_C
- \- *lemma* mv_polynomial.degrees_X
- \- *lemma* mv_polynomial.degrees_add
- \- *lemma* mv_polynomial.degrees_add_of_disjoint
- \- *lemma* mv_polynomial.degrees_map
- \- *lemma* mv_polynomial.degrees_map_of_injective
- \- *lemma* mv_polynomial.degrees_monomial
- \- *lemma* mv_polynomial.degrees_monomial_eq
- \- *lemma* mv_polynomial.degrees_mul
- \- *lemma* mv_polynomial.degrees_neg
- \- *lemma* mv_polynomial.degrees_one
- \- *lemma* mv_polynomial.degrees_pow
- \- *lemma* mv_polynomial.degrees_prod
- \- *lemma* mv_polynomial.degrees_sub
- \- *lemma* mv_polynomial.degrees_sum
- \- *lemma* mv_polynomial.degrees_zero
- \- *lemma* mv_polynomial.eq_zero_iff
- \- *def* mv_polynomial.eval
- \- *lemma* mv_polynomial.eval_C
- \- *lemma* mv_polynomial.eval_X
- \- *theorem* mv_polynomial.eval_assoc
- \- *lemma* mv_polynomial.eval_eq'
- \- *lemma* mv_polynomial.eval_eq
- \- *lemma* mv_polynomial.eval_map
- \- *lemma* mv_polynomial.eval_monomial
- \- *lemma* mv_polynomial.eval_prod
- \- *lemma* mv_polynomial.eval_rename_prodmk
- \- *lemma* mv_polynomial.eval_sum
- \- *theorem* mv_polynomial.eval_unique
- \- *def* mv_polynomial.eval₂
- \- *lemma* mv_polynomial.eval₂_C
- \- *lemma* mv_polynomial.eval₂_X
- \- *lemma* mv_polynomial.eval₂_add
- \- *lemma* mv_polynomial.eval₂_assoc
- \- *lemma* mv_polynomial.eval₂_cast_comp
- \- *lemma* mv_polynomial.eval₂_comp_left
- \- *lemma* mv_polynomial.eval₂_comp_right
- \- *lemma* mv_polynomial.eval₂_congr
- \- *lemma* mv_polynomial.eval₂_eq'
- \- *lemma* mv_polynomial.eval₂_eq
- \- *theorem* mv_polynomial.eval₂_eq_eval_map
- \- *lemma* mv_polynomial.eval₂_eta
- \- *def* mv_polynomial.eval₂_hom
- \- *lemma* mv_polynomial.eval₂_hom_C
- \- *lemma* mv_polynomial.eval₂_hom_X'
- \- *lemma* mv_polynomial.eval₂_hom_X
- \- *lemma* mv_polynomial.eval₂_hom_congr
- \- *lemma* mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars
- \- *lemma* mv_polynomial.eval₂_hom_map_hom
- \- *lemma* mv_polynomial.eval₂_hom_monomial
- \- *lemma* mv_polynomial.eval₂_hom_rename
- \- *lemma* mv_polynomial.eval₂_map
- \- *lemma* mv_polynomial.eval₂_monomial
- \- *lemma* mv_polynomial.eval₂_mul
- \- *lemma* mv_polynomial.eval₂_mul_monomial
- \- *lemma* mv_polynomial.eval₂_neg
- \- *lemma* mv_polynomial.eval₂_one
- \- *lemma* mv_polynomial.eval₂_pow
- \- *lemma* mv_polynomial.eval₂_prod
- \- *lemma* mv_polynomial.eval₂_rename
- \- *lemma* mv_polynomial.eval₂_rename_prodmk
- \- *lemma* mv_polynomial.eval₂_sub
- \- *lemma* mv_polynomial.eval₂_sum
- \- *lemma* mv_polynomial.eval₂_zero
- \- *lemma* mv_polynomial.exists_coeff_ne_zero
- \- *lemma* mv_polynomial.exists_degree_lt
- \- *theorem* mv_polynomial.exists_fin_rename
- \- *theorem* mv_polynomial.exists_finset_rename
- \- *lemma* mv_polynomial.ext
- \- *lemma* mv_polynomial.ext_iff
- \- *def* mv_polynomial.fin_succ_equiv
- \- *lemma* mv_polynomial.hom_C
- \- *lemma* mv_polynomial.hom_eq_hom
- \- *def* mv_polynomial.hom_equiv
- \- *theorem* mv_polynomial.induction_on'
- \- *lemma* mv_polynomial.induction_on
- \- *lemma* mv_polynomial.is_id
- \- *def* mv_polynomial.iter_to_sum
- \- *lemma* mv_polynomial.iter_to_sum_C_C
- \- *lemma* mv_polynomial.iter_to_sum_C_X
- \- *lemma* mv_polynomial.iter_to_sum_X
- \- *lemma* mv_polynomial.le_degrees_add
- \- *def* mv_polynomial.map
- \- *theorem* mv_polynomial.map_C
- \- *theorem* mv_polynomial.map_X
- \- *lemma* mv_polynomial.map_aeval
- \- *lemma* mv_polynomial.map_eval₂
- \- *lemma* mv_polynomial.map_eval₂_hom
- \- *theorem* mv_polynomial.map_id
- \- *lemma* mv_polynomial.map_injective
- \- *theorem* mv_polynomial.map_map
- \- *theorem* mv_polynomial.map_monomial
- \- *lemma* mv_polynomial.map_rename
- \- *lemma* mv_polynomial.mem_degrees
- \- *lemma* mv_polynomial.mem_support_not_mem_vars_zero
- \- *lemma* mv_polynomial.mem_vars
- \- *lemma* mv_polynomial.monic_monomial_eq
- \- *def* mv_polynomial.monomial
- \- *lemma* mv_polynomial.monomial_add
- \- *lemma* mv_polynomial.monomial_add_single
- \- *lemma* mv_polynomial.monomial_eq
- \- *lemma* mv_polynomial.monomial_mul
- \- *lemma* mv_polynomial.monomial_single_add
- \- *lemma* mv_polynomial.monomial_zero
- \- *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \- *lemma* mv_polynomial.ne_zero_iff
- \- *def* mv_polynomial.option_equiv_left
- \- *def* mv_polynomial.option_equiv_right
- \- *def* mv_polynomial.pderivative.add_monoid_hom
- \- *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \- *def* mv_polynomial.pderivative
- \- *lemma* mv_polynomial.pderivative_C
- \- *lemma* mv_polynomial.pderivative_C_mul
- \- *lemma* mv_polynomial.pderivative_add
- \- *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \- *lemma* mv_polynomial.pderivative_monomial
- \- *lemma* mv_polynomial.pderivative_monomial_mul
- \- *lemma* mv_polynomial.pderivative_monomial_single
- \- *lemma* mv_polynomial.pderivative_mul
- \- *lemma* mv_polynomial.pderivative_zero
- \- *def* mv_polynomial.pempty_ring_equiv
- \- *def* mv_polynomial.punit_ring_equiv
- \- *def* mv_polynomial.rename
- \- *lemma* mv_polynomial.rename_C
- \- *lemma* mv_polynomial.rename_X
- \- *lemma* mv_polynomial.rename_eq
- \- *lemma* mv_polynomial.rename_eval₂
- \- *lemma* mv_polynomial.rename_id
- \- *lemma* mv_polynomial.rename_injective
- \- *lemma* mv_polynomial.rename_monomial
- \- *lemma* mv_polynomial.rename_prodmk_eval₂
- \- *lemma* mv_polynomial.rename_rename
- \- *def* mv_polynomial.ring_equiv_congr
- \- *def* mv_polynomial.ring_equiv_of_equiv
- \- *lemma* mv_polynomial.ring_hom_ext
- \- *lemma* mv_polynomial.single_eq_C_mul_X
- \- *lemma* mv_polynomial.smul_eq_C_mul
- \- *lemma* mv_polynomial.smul_eval
- \- *lemma* mv_polynomial.sum_monomial
- \- *def* mv_polynomial.sum_ring_equiv
- \- *def* mv_polynomial.sum_to_iter
- \- *lemma* mv_polynomial.sum_to_iter_C
- \- *lemma* mv_polynomial.sum_to_iter_Xl
- \- *lemma* mv_polynomial.sum_to_iter_Xr
- \- *lemma* mv_polynomial.support_map_of_injective
- \- *lemma* mv_polynomial.support_map_subset
- \- *lemma* mv_polynomial.support_sum_monomial_coeff
- \- *def* mv_polynomial.total_degree
- \- *lemma* mv_polynomial.total_degree_C
- \- *lemma* mv_polynomial.total_degree_X
- \- *lemma* mv_polynomial.total_degree_add
- \- *lemma* mv_polynomial.total_degree_eq
- \- *lemma* mv_polynomial.total_degree_finset_prod
- \- *lemma* mv_polynomial.total_degree_le_degrees_card
- \- *lemma* mv_polynomial.total_degree_list_prod
- \- *lemma* mv_polynomial.total_degree_mul
- \- *lemma* mv_polynomial.total_degree_multiset_prod
- \- *lemma* mv_polynomial.total_degree_neg
- \- *lemma* mv_polynomial.total_degree_one
- \- *lemma* mv_polynomial.total_degree_pow
- \- *lemma* mv_polynomial.total_degree_rename_le
- \- *lemma* mv_polynomial.total_degree_sub
- \- *lemma* mv_polynomial.total_degree_zero
- \- *def* mv_polynomial.vars
- \- *lemma* mv_polynomial.vars_0
- \- *lemma* mv_polynomial.vars_C
- \- *lemma* mv_polynomial.vars_X
- \- *lemma* mv_polynomial.vars_add_of_disjoint
- \- *lemma* mv_polynomial.vars_add_subset
- \- *lemma* mv_polynomial.vars_eq_support_bind_support
- \- *lemma* mv_polynomial.vars_map
- \- *lemma* mv_polynomial.vars_map_of_injective
- \- *lemma* mv_polynomial.vars_monomial
- \- *lemma* mv_polynomial.vars_monomial_single
- \- *lemma* mv_polynomial.vars_neg
- \- *lemma* mv_polynomial.vars_sub_of_disjoint
- \- *lemma* mv_polynomial.vars_sub_subset
- \- *lemma* mv_polynomial.vars_sum_of_disjoint
- \- *lemma* mv_polynomial.vars_sum_subset
- \- *def* mv_polynomial

Added src/data/mv_polynomial/basic.lean
- \+ *def* mv_polynomial.C
- \+ *lemma* mv_polynomial.C_0
- \+ *lemma* mv_polynomial.C_1
- \+ *lemma* mv_polynomial.C_add
- \+ *lemma* mv_polynomial.C_eq_coe_nat
- \+ *lemma* mv_polynomial.C_inj
- \+ *lemma* mv_polynomial.C_injective
- \+ *lemma* mv_polynomial.C_mul
- \+ *lemma* mv_polynomial.C_mul_monomial
- \+ *lemma* mv_polynomial.C_pow
- \+ *def* mv_polynomial.X
- \+ *lemma* mv_polynomial.X_pow_eq_single
- \+ *def* mv_polynomial.aeval
- \+ *lemma* mv_polynomial.aeval_C
- \+ *lemma* mv_polynomial.aeval_X
- \+ *theorem* mv_polynomial.aeval_def
- \+ *lemma* mv_polynomial.aeval_eq_eval₂_hom
- \+ *lemma* mv_polynomial.aeval_monomial
- \+ *lemma* mv_polynomial.aeval_zero'
- \+ *lemma* mv_polynomial.aeval_zero
- \+ *lemma* mv_polynomial.alg_hom_C
- \+ *lemma* mv_polynomial.alg_hom_ext
- \+ *theorem* mv_polynomial.algebra_map_eq
- \+ *lemma* mv_polynomial.as_sum
- \+ *lemma* mv_polynomial.coe_eval₂_hom
- \+ *def* mv_polynomial.coeff
- \+ *lemma* mv_polynomial.coeff_C
- \+ *lemma* mv_polynomial.coeff_C_mul
- \+ *lemma* mv_polynomial.coeff_X'
- \+ *lemma* mv_polynomial.coeff_X
- \+ *lemma* mv_polynomial.coeff_X_pow
- \+ *lemma* mv_polynomial.coeff_add
- \+ *def* mv_polynomial.coeff_coe_to_fun
- \+ *lemma* mv_polynomial.coeff_map
- \+ *lemma* mv_polynomial.coeff_monomial
- \+ *lemma* mv_polynomial.coeff_mul
- \+ *lemma* mv_polynomial.coeff_mul_X'
- \+ *lemma* mv_polynomial.coeff_mul_X
- \+ *lemma* mv_polynomial.coeff_sum
- \+ *lemma* mv_polynomial.coeff_zero
- \+ *lemma* mv_polynomial.coeff_zero_X
- \+ *lemma* mv_polynomial.comp_aeval
- \+ *lemma* mv_polynomial.comp_eval₂_hom
- \+ *def* mv_polynomial.constant_coeff
- \+ *lemma* mv_polynomial.constant_coeff_C
- \+ *lemma* mv_polynomial.constant_coeff_X
- \+ *lemma* mv_polynomial.constant_coeff_eq
- \+ *lemma* mv_polynomial.constant_coeff_monomial
- \+ *lemma* mv_polynomial.eq_zero_iff
- \+ *def* mv_polynomial.eval
- \+ *lemma* mv_polynomial.eval_C
- \+ *lemma* mv_polynomial.eval_X
- \+ *theorem* mv_polynomial.eval_assoc
- \+ *lemma* mv_polynomial.eval_eq'
- \+ *lemma* mv_polynomial.eval_eq
- \+ *lemma* mv_polynomial.eval_map
- \+ *lemma* mv_polynomial.eval_monomial
- \+ *lemma* mv_polynomial.eval_prod
- \+ *lemma* mv_polynomial.eval_sum
- \+ *theorem* mv_polynomial.eval_unique
- \+ *def* mv_polynomial.eval₂
- \+ *lemma* mv_polynomial.eval₂_C
- \+ *lemma* mv_polynomial.eval₂_X
- \+ *lemma* mv_polynomial.eval₂_add
- \+ *lemma* mv_polynomial.eval₂_assoc
- \+ *lemma* mv_polynomial.eval₂_comp_left
- \+ *lemma* mv_polynomial.eval₂_comp_right
- \+ *lemma* mv_polynomial.eval₂_congr
- \+ *lemma* mv_polynomial.eval₂_eq'
- \+ *lemma* mv_polynomial.eval₂_eq
- \+ *theorem* mv_polynomial.eval₂_eq_eval_map
- \+ *lemma* mv_polynomial.eval₂_eta
- \+ *def* mv_polynomial.eval₂_hom
- \+ *lemma* mv_polynomial.eval₂_hom_C
- \+ *lemma* mv_polynomial.eval₂_hom_X'
- \+ *lemma* mv_polynomial.eval₂_hom_congr
- \+ *lemma* mv_polynomial.eval₂_hom_map_hom
- \+ *lemma* mv_polynomial.eval₂_hom_monomial
- \+ *lemma* mv_polynomial.eval₂_map
- \+ *lemma* mv_polynomial.eval₂_monomial
- \+ *lemma* mv_polynomial.eval₂_mul
- \+ *lemma* mv_polynomial.eval₂_mul_monomial
- \+ *lemma* mv_polynomial.eval₂_one
- \+ *lemma* mv_polynomial.eval₂_pow
- \+ *lemma* mv_polynomial.eval₂_prod
- \+ *lemma* mv_polynomial.eval₂_sum
- \+ *lemma* mv_polynomial.eval₂_zero
- \+ *lemma* mv_polynomial.exists_coeff_ne_zero
- \+ *lemma* mv_polynomial.ext
- \+ *lemma* mv_polynomial.ext_iff
- \+ *lemma* mv_polynomial.hom_eq_hom
- \+ *theorem* mv_polynomial.induction_on'
- \+ *lemma* mv_polynomial.induction_on
- \+ *lemma* mv_polynomial.is_id
- \+ *def* mv_polynomial.map
- \+ *theorem* mv_polynomial.map_C
- \+ *theorem* mv_polynomial.map_X
- \+ *lemma* mv_polynomial.map_aeval
- \+ *lemma* mv_polynomial.map_eval₂
- \+ *lemma* mv_polynomial.map_eval₂_hom
- \+ *theorem* mv_polynomial.map_id
- \+ *lemma* mv_polynomial.map_injective
- \+ *theorem* mv_polynomial.map_map
- \+ *theorem* mv_polynomial.map_monomial
- \+ *lemma* mv_polynomial.monic_monomial_eq
- \+ *def* mv_polynomial.monomial
- \+ *lemma* mv_polynomial.monomial_add
- \+ *lemma* mv_polynomial.monomial_add_single
- \+ *lemma* mv_polynomial.monomial_eq
- \+ *lemma* mv_polynomial.monomial_mul
- \+ *lemma* mv_polynomial.monomial_single_add
- \+ *lemma* mv_polynomial.monomial_zero
- \+ *lemma* mv_polynomial.ne_zero_iff
- \+ *lemma* mv_polynomial.ring_hom_ext
- \+ *lemma* mv_polynomial.single_eq_C_mul_X
- \+ *lemma* mv_polynomial.sum_monomial
- \+ *lemma* mv_polynomial.support_map_of_injective
- \+ *lemma* mv_polynomial.support_map_subset
- \+ *lemma* mv_polynomial.support_sum_monomial_coeff
- \+ *def* mv_polynomial

Added src/data/mv_polynomial/comm_ring.lean
- \+ *theorem* mv_polynomial.C_mul'
- \+ *lemma* mv_polynomial.C_neg
- \+ *lemma* mv_polynomial.C_sub
- \+ *lemma* mv_polynomial.coeff_neg
- \+ *lemma* mv_polynomial.coeff_sub
- \+ *lemma* mv_polynomial.degrees_neg
- \+ *lemma* mv_polynomial.degrees_sub
- \+ *lemma* mv_polynomial.eval₂_hom_X
- \+ *lemma* mv_polynomial.eval₂_neg
- \+ *lemma* mv_polynomial.eval₂_sub
- \+ *lemma* mv_polynomial.hom_C
- \+ *def* mv_polynomial.hom_equiv
- \+ *lemma* mv_polynomial.smul_eq_C_mul
- \+ *lemma* mv_polynomial.smul_eval
- \+ *lemma* mv_polynomial.total_degree_neg
- \+ *lemma* mv_polynomial.total_degree_sub
- \+ *lemma* mv_polynomial.vars_neg
- \+ *lemma* mv_polynomial.vars_sub_of_disjoint
- \+ *lemma* mv_polynomial.vars_sub_subset

Added src/data/mv_polynomial/default.lean


Added src/data/mv_polynomial/equiv.lean
- \+ *def* mv_polynomial.fin_succ_equiv
- \+ *def* mv_polynomial.iter_to_sum
- \+ *lemma* mv_polynomial.iter_to_sum_C_C
- \+ *lemma* mv_polynomial.iter_to_sum_C_X
- \+ *lemma* mv_polynomial.iter_to_sum_X
- \+ *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \+ *def* mv_polynomial.option_equiv_left
- \+ *def* mv_polynomial.option_equiv_right
- \+ *def* mv_polynomial.pempty_ring_equiv
- \+ *def* mv_polynomial.punit_ring_equiv
- \+ *def* mv_polynomial.ring_equiv_congr
- \+ *def* mv_polynomial.ring_equiv_of_equiv
- \+ *def* mv_polynomial.sum_ring_equiv
- \+ *def* mv_polynomial.sum_to_iter
- \+ *lemma* mv_polynomial.sum_to_iter_C
- \+ *lemma* mv_polynomial.sum_to_iter_Xl
- \+ *lemma* mv_polynomial.sum_to_iter_Xr

Added src/data/mv_polynomial/pderiv.lean
- \+ *def* mv_polynomial.pderivative.add_monoid_hom
- \+ *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \+ *def* mv_polynomial.pderivative
- \+ *lemma* mv_polynomial.pderivative_C
- \+ *lemma* mv_polynomial.pderivative_C_mul
- \+ *lemma* mv_polynomial.pderivative_add
- \+ *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \+ *lemma* mv_polynomial.pderivative_monomial
- \+ *lemma* mv_polynomial.pderivative_monomial_mul
- \+ *lemma* mv_polynomial.pderivative_monomial_single
- \+ *lemma* mv_polynomial.pderivative_mul
- \+ *lemma* mv_polynomial.pderivative_zero

Added src/data/mv_polynomial/rename.lean
- \+ *lemma* mv_polynomial.eval_rename_prodmk
- \+ *lemma* mv_polynomial.eval₂_cast_comp
- \+ *lemma* mv_polynomial.eval₂_hom_rename
- \+ *lemma* mv_polynomial.eval₂_rename
- \+ *lemma* mv_polynomial.eval₂_rename_prodmk
- \+ *theorem* mv_polynomial.exists_fin_rename
- \+ *theorem* mv_polynomial.exists_finset_rename
- \+ *lemma* mv_polynomial.map_rename
- \+ *def* mv_polynomial.rename
- \+ *lemma* mv_polynomial.rename_C
- \+ *lemma* mv_polynomial.rename_X
- \+ *lemma* mv_polynomial.rename_eq
- \+ *lemma* mv_polynomial.rename_eval₂
- \+ *lemma* mv_polynomial.rename_id
- \+ *lemma* mv_polynomial.rename_injective
- \+ *lemma* mv_polynomial.rename_monomial
- \+ *lemma* mv_polynomial.rename_prodmk_eval₂
- \+ *lemma* mv_polynomial.rename_rename
- \+ *lemma* mv_polynomial.total_degree_rename_le

Added src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.aeval_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.coeff_eq_zero_of_total_degree_lt
- \+ *def* mv_polynomial.degree_of
- \+ *def* mv_polynomial.degrees
- \+ *lemma* mv_polynomial.degrees_C
- \+ *lemma* mv_polynomial.degrees_X
- \+ *lemma* mv_polynomial.degrees_add
- \+ *lemma* mv_polynomial.degrees_add_of_disjoint
- \+ *lemma* mv_polynomial.degrees_map
- \+ *lemma* mv_polynomial.degrees_map_of_injective
- \+ *lemma* mv_polynomial.degrees_monomial
- \+ *lemma* mv_polynomial.degrees_monomial_eq
- \+ *lemma* mv_polynomial.degrees_mul
- \+ *lemma* mv_polynomial.degrees_one
- \+ *lemma* mv_polynomial.degrees_pow
- \+ *lemma* mv_polynomial.degrees_prod
- \+ *lemma* mv_polynomial.degrees_sum
- \+ *lemma* mv_polynomial.degrees_zero
- \+ *lemma* mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.exists_degree_lt
- \+ *lemma* mv_polynomial.le_degrees_add
- \+ *lemma* mv_polynomial.mem_degrees
- \+ *lemma* mv_polynomial.mem_support_not_mem_vars_zero
- \+ *lemma* mv_polynomial.mem_vars
- \+ *def* mv_polynomial.total_degree
- \+ *lemma* mv_polynomial.total_degree_C
- \+ *lemma* mv_polynomial.total_degree_X
- \+ *lemma* mv_polynomial.total_degree_add
- \+ *lemma* mv_polynomial.total_degree_eq
- \+ *lemma* mv_polynomial.total_degree_finset_prod
- \+ *lemma* mv_polynomial.total_degree_le_degrees_card
- \+ *lemma* mv_polynomial.total_degree_list_prod
- \+ *lemma* mv_polynomial.total_degree_mul
- \+ *lemma* mv_polynomial.total_degree_multiset_prod
- \+ *lemma* mv_polynomial.total_degree_one
- \+ *lemma* mv_polynomial.total_degree_pow
- \+ *lemma* mv_polynomial.total_degree_zero
- \+ *def* mv_polynomial.vars
- \+ *lemma* mv_polynomial.vars_0
- \+ *lemma* mv_polynomial.vars_C
- \+ *lemma* mv_polynomial.vars_X
- \+ *lemma* mv_polynomial.vars_add_of_disjoint
- \+ *lemma* mv_polynomial.vars_add_subset
- \+ *lemma* mv_polynomial.vars_eq_support_bind_support
- \+ *lemma* mv_polynomial.vars_map
- \+ *lemma* mv_polynomial.vars_map_of_injective
- \+ *lemma* mv_polynomial.vars_monomial
- \+ *lemma* mv_polynomial.vars_monomial_single
- \+ *lemma* mv_polynomial.vars_sum_of_disjoint
- \+ *lemma* mv_polynomial.vars_sum_subset

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-09-09 04:32:30](https://github.com/leanprover-community/mathlib/commit/d5580f4)
feat(data/equiv/basic): add ext_iff for perm ([#4067](https://github.com/leanprover-community/mathlib/pull/4067))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.ext_iff
- \+ *lemma* equiv.perm.ext_iff



## [2020-09-08 21:33:25](https://github.com/leanprover-community/mathlib/commit/f5ee84c)
feat(analysis/special_functions/pow): Added lemmas bounding rpow in ennreal ([#4039](https://github.com/leanprover-community/mathlib/pull/4039))
Continuation of [#3715](https://github.com/leanprover-community/mathlib/pull/3715). Added lemmas in `ennreal` corresponding to the `real` and `nnreal` lemmas added in that PR
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* ennreal.one_le_rpow
- \+ *lemma* ennreal.one_le_rpow_of_pos_of_le_one_of_neg
- \+ *lemma* ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg
- \+/\- *lemma* ennreal.rpow_le_one
- \+ *lemma* ennreal.rpow_le_one_of_one_le_of_neg
- \+/\- *lemma* ennreal.rpow_lt_one
- \+ *lemma* ennreal.rpow_lt_one_of_one_lt_of_neg



## [2020-09-08 20:35:35](https://github.com/leanprover-community/mathlib/commit/7354042)
fix(topology/metric_space): free universe ([#4072](https://github.com/leanprover-community/mathlib/pull/4072))
Removes an unneeded and painful universe restriction
#### Estimated changes
Modified src/topology/metric_space/basic.lean




## [2020-09-08 18:11:23](https://github.com/leanprover-community/mathlib/commit/dde8bad)
doc(*): add docstrings ([#4071](https://github.com/leanprover-community/mathlib/pull/4071))
Minor docstring fixes
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/ring_theory/principal_ideal_domain.lean




## [2020-09-08 12:40:23](https://github.com/leanprover-community/mathlib/commit/b2ec2b0)
chore(data/padics): fix bad markdown in doc string ([#4068](https://github.com/leanprover-community/mathlib/pull/4068))
Just noticed this in the docs
#### Estimated changes
Modified src/data/padics/ring_homs.lean




## [2020-09-08 12:40:21](https://github.com/leanprover-community/mathlib/commit/4f1399d)
feat(geometry/euclidean/basic): reflection lemmas ([#4056](https://github.com/leanprover-community/mathlib/pull/4056))
Add more lemmas about reflections of points in subspaces.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.reflection_mem_of_le_of_mem
- \+ *lemma* euclidean_geometry.reflection_orthogonal_vadd
- \+ *lemma* euclidean_geometry.reflection_vadd_smul_vsub_orthogonal_projection



## [2020-09-08 12:40:19](https://github.com/leanprover-community/mathlib/commit/445e883)
feat(function): has_uncurry ([#3694](https://github.com/leanprover-community/mathlib/pull/3694))
By Gabriel Ebner, from the sphere eversion project. See discussion at 
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/recursive.20uncurry
#### Estimated changes
Modified src/logic/function/basic.lean




## [2020-09-08 10:47:42](https://github.com/leanprover-community/mathlib/commit/1c53f91)
doc(tactic/lean_core_docs): congr understands subsingletons ([#4060](https://github.com/leanprover-community/mathlib/pull/4060))
#### Estimated changes
Modified src/tactic/congr.lean


Modified src/tactic/lean_core_docs.lean




## [2020-09-08 00:47:47](https://github.com/leanprover-community/mathlib/commit/a16112d)
doc(algebra/group/to_additive): order of to_additive relative to other attributes ([#4065](https://github.com/leanprover-community/mathlib/pull/4065))
#### Estimated changes
Modified src/algebra/group/to_additive.lean




## [2020-09-07 19:41:48](https://github.com/leanprover-community/mathlib/commit/c7d6a8e)
feat(ring_theory/unique_factorization_domain): descending chain condition for divisibility ([#4031](https://github.com/leanprover-community/mathlib/pull/4031))
Defines the strict divisibility relation `dvd_not_unit`
Defines class `wf_dvd_monoid`, indicating that `dvd_not_unit` is well-founded
Provides instances of `wf_dvd_monoid`
Prepares to refactor `unique_factorization_domain` as a predicate extending `wf_dvd_monoid`
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* associates.dvd_not_unit_iff_lt
- \+ *theorem* associates.dvd_not_unit_of_lt
- \+ *theorem* associates.irreducible_mk
- \- *theorem* associates.irreducible_mk_iff
- \- *lemma* associates.le_of_mul_le_mul_right
- \+ *theorem* associates.mk_dvd_not_unit_mk_iff
- \+ *theorem* associates.mk_surjective

Modified src/algebra/divisibility.lean
- \+ *def* dvd_not_unit
- \+ *lemma* dvd_not_unit_of_dvd_of_not_dvd

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/noetherian.lean
- \- *lemma* is_noetherian_ring.exists_factors
- \- *lemma* is_noetherian_ring.exists_irreducible_factor
- \- *lemma* is_noetherian_ring.irreducible_induction_on
- \- *lemma* is_noetherian_ring.well_founded_dvd_not_unit

Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* wf_dvd_monoid.exists_factors
- \+ *lemma* wf_dvd_monoid.exists_irreducible_factor
- \+ *theorem* wf_dvd_monoid.iff_well_founded_associates
- \+ *lemma* wf_dvd_monoid.induction_on_irreducible
- \+ *theorem* wf_dvd_monoid.of_well_founded_associates
- \+ *theorem* wf_dvd_monoid.of_wf_dvd_monoid_associates
- \+ *theorem* wf_dvd_monoid.well_founded_associates



## [2020-09-07 17:54:54](https://github.com/leanprover-community/mathlib/commit/851e83e)
feat(category_theory): colimits for pi categories ([#4054](https://github.com/leanprover-community/mathlib/pull/4054))
#### Estimated changes
Modified src/category_theory/limits/pi.lean
- \+ *def* category_theory.pi.cocone_comp_eval
- \+ *def* category_theory.pi.cocone_of_cocone_comp_eval
- \+ *def* category_theory.pi.cocone_of_cocone_eval_is_colimit
- \+ *def* category_theory.pi.has_colimit_of_has_colimit_comp_eval



## [2020-09-07 13:36:36](https://github.com/leanprover-community/mathlib/commit/c259305)
feat(topology/algebra/floor_ring): add basic topological facts about `floor`, `ceil` and `fract` ([#4042](https://github.com/leanprover-community/mathlib/pull/4042))
From the sphere eversion project
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* ceil_eq_iff
- \+ *lemma* ceil_eq_on_Ioc'
- \+ *lemma* ceil_eq_on_Ioc
- \+ *lemma* floor_eq_on_Ico'
- \+ *lemma* floor_eq_on_Ico

Added src/topology/algebra/floor_ring.lean
- \+ *lemma* continuous_on.comp_fract'
- \+ *lemma* continuous_on.comp_fract
- \+ *lemma* continuous_on_ceil
- \+ *lemma* continuous_on_floor
- \+ *lemma* continuous_on_fract
- \+ *lemma* tendsto_ceil_at_bot
- \+ *lemma* tendsto_ceil_at_top
- \+ *lemma* tendsto_ceil_left'
- \+ *lemma* tendsto_ceil_left
- \+ *lemma* tendsto_ceil_right'
- \+ *lemma* tendsto_ceil_right
- \+ *lemma* tendsto_floor_at_bot
- \+ *lemma* tendsto_floor_at_top
- \+ *lemma* tendsto_floor_left'
- \+ *lemma* tendsto_floor_left
- \+ *lemma* tendsto_floor_right'
- \+ *lemma* tendsto_floor_right
- \+ *lemma* tendsto_fract_left'
- \+ *lemma* tendsto_fract_left
- \+ *lemma* tendsto_fract_right'
- \+ *lemma* tendsto_fract_right

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_inv_nhds_within_Ici
- \+ *lemma* tendsto_inv_nhds_within_Ici_inv
- \+ *lemma* tendsto_inv_nhds_within_Iic
- \+ *lemma* tendsto_inv_nhds_within_Iic_inv



## [2020-09-07 07:49:55](https://github.com/leanprover-community/mathlib/commit/f253fa0)
feat(logic/basic): apply_dite2, apply_ite2 ([#4050](https://github.com/leanprover-community/mathlib/pull/4050))
Add variants of `apply_dite` and `apply_ite` for two-argument
functions (in the case where I wanted `apply_ite`, the function was
addition).  I don't think there is any need for corresponding versions
of `dite_apply` or `ite_apply`, as two-argument versions of those
would be exactly the same as applying the one-argument version twice,
whereas that's not the case with `apply_dite2` and `apply_ite2`.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* apply_dite2
- \+ *lemma* apply_ite2



## [2020-09-07 05:46:33](https://github.com/leanprover-community/mathlib/commit/94b96cf)
feat(algebraic_geometry/structure_sheaf): stalk_iso ([#4047](https://github.com/leanprover-community/mathlib/pull/4047))
Given a ring `R` and a prime ideal `p`, construct an isomorphism of rings between the stalk of the structure sheaf of `R` at `p` and the localization of `R` at `p`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+/\- *def* prime_spectrum.basic_open
- \- *lemma* prime_spectrum.basic_open_open

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* algebraic_geometry.coe_open_to_localization
- \+ *def* algebraic_geometry.const
- \+ *lemma* algebraic_geometry.const_add
- \+ *lemma* algebraic_geometry.const_apply'
- \+ *lemma* algebraic_geometry.const_apply
- \+ *lemma* algebraic_geometry.const_congr
- \+ *lemma* algebraic_geometry.const_ext
- \+ *lemma* algebraic_geometry.const_mul
- \+ *lemma* algebraic_geometry.const_mul_cancel'
- \+ *lemma* algebraic_geometry.const_mul_cancel
- \+ *lemma* algebraic_geometry.const_mul_rev
- \+ *lemma* algebraic_geometry.const_one
- \+ *lemma* algebraic_geometry.const_self
- \+ *lemma* algebraic_geometry.const_zero
- \+ *lemma* algebraic_geometry.exists_const
- \+ *lemma* algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.germ_to_open
- \+ *lemma* algebraic_geometry.germ_to_top
- \+ *lemma* algebraic_geometry.is_unit_to_basic_open_self
- \+ *lemma* algebraic_geometry.is_unit_to_stalk
- \+ *lemma* algebraic_geometry.localization_to_basic_open
- \+ *def* algebraic_geometry.localization_to_stalk
- \+ *lemma* algebraic_geometry.localization_to_stalk_mk'
- \+ *lemma* algebraic_geometry.localization_to_stalk_of
- \+ *def* algebraic_geometry.open_to_localization
- \+ *lemma* algebraic_geometry.open_to_localization_apply
- \+ *lemma* algebraic_geometry.res_apply
- \+ *lemma* algebraic_geometry.res_const'
- \+ *lemma* algebraic_geometry.res_const
- \+/\- *def* algebraic_geometry.stalk_iso
- \+/\- *def* algebraic_geometry.stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ'
- \+ *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ
- \+ *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_to_stalk
- \+ *def* algebraic_geometry.to_basic_open
- \+ *lemma* algebraic_geometry.to_basic_open_mk'
- \+ *lemma* algebraic_geometry.to_basic_open_to_map
- \+ *def* algebraic_geometry.to_open
- \+ *lemma* algebraic_geometry.to_open_apply
- \+ *lemma* algebraic_geometry.to_open_eq_const
- \+ *lemma* algebraic_geometry.to_open_germ
- \+ *lemma* algebraic_geometry.to_open_res
- \+ *def* algebraic_geometry.to_stalk
- \+ *lemma* algebraic_geometry.to_stalk_comp_stalk_to_fiber_ring_hom

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.germ_ext
- \+ *lemma* Top.presheaf.stalk_hom_ext



## [2020-09-07 00:51:55](https://github.com/leanprover-community/mathlib/commit/2e198b4)
chore(scripts): update nolints.txt ([#4058](https://github.com/leanprover-community/mathlib/pull/4058))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-06 23:47:49](https://github.com/leanprover-community/mathlib/commit/4662b20)
feat(category_theory): definition of `diag` in `binary_products` ([#4051](https://github.com/leanprover-community/mathlib/pull/4051))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.map_codiag
- \+ *lemma* category_theory.limits.coprod.map_comp_codiag
- \+ *lemma* category_theory.limits.coprod.map_comp_inl_inr_codiag
- \+ *lemma* category_theory.limits.coprod.map_inl_inr_codiag
- \+ *lemma* category_theory.limits.prod.diag_map
- \+ *lemma* category_theory.limits.prod.diag_map_comp
- \+ *lemma* category_theory.limits.prod.diag_map_fst_snd
- \+ *lemma* category_theory.limits.prod.diag_map_fst_snd_comp



## [2020-09-06 23:08:44](https://github.com/leanprover-community/mathlib/commit/4945c77)
cleanup(ring_theory/ring_invo): update old module doc, add ring_invo.involution with cleaner statement ([#4052](https://github.com/leanprover-community/mathlib/pull/4052))
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean


Renamed src/ring_theory/maps.lean to src/ring_theory/ring_invo.lean
- \+ *lemma* ring_invo.involution



## [2020-09-06 12:14:42](https://github.com/leanprover-community/mathlib/commit/de03e19)
feat(analysis/normed_space/real_inner_product): linear independence of orthogonal vectors ([#4045](https://github.com/leanprover-community/mathlib/pull/4045))
Add the lemma that an indexed family of nonzero, pairwise orthogonal
vectors is linearly independent.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* linear_independent_of_ne_zero_of_inner_eq_zero



## [2020-09-06 12:14:40](https://github.com/leanprover-community/mathlib/commit/1117ae7)
feat(linear_algebra): Add lemmas about powers of endomorphisms ([#4036](https://github.com/leanprover-community/mathlib/pull/4036))
Add lemmas about powers of endomorphisms and the corollary that every generalized eigenvector is a generalized eigenvector for exponent `findim K V`.
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.generalized_eigenspace_eq_generalized_eigenspace_findim_of_le
- \+ *lemma* module.End.generalized_eigenspace_le_generalized_eigenspace_findim

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* module.End.exists_ker_pow_eq_ker_pow_succ
- \+ *lemma* module.End.ker_pow_constant
- \+ *lemma* module.End.ker_pow_eq_ker_pow_findim_of_le
- \+ *lemma* module.End.ker_pow_le_ker_pow_findim
- \+ *lemma* submodule.findim_lt_findim_of_lt



## [2020-09-06 11:28:33](https://github.com/leanprover-community/mathlib/commit/fabf34f)
feat(analysis/special_functions/trigonometric): Added lemmas for deriv of tan ([#3746](https://github.com/leanprover-community/mathlib/pull/3746))
I added lemmas for the derivative of the tangent function in both the complex and real namespaces. I also corrected two typos in comment lines.
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.continuous_on_tan
- \+/\- *lemma* complex.continuous_tan
- \+ *theorem* complex.cos_eq_zero_iff
- \+ *theorem* complex.cos_ne_zero_iff
- \+ *lemma* complex.deriv_tan
- \+ *lemma* complex.differentiable_at_tan
- \+ *lemma* complex.exp_pi_mul_I
- \+ *lemma* complex.has_deriv_at_tan
- \+ *lemma* real.continuous_on_tan
- \+/\- *lemma* real.continuous_tan
- \+/\- *theorem* real.cos_eq_zero_iff
- \+/\- *theorem* real.cos_ne_zero_iff
- \+ *lemma* real.cos_nonneg_of_mem_Icc
- \- *lemma* real.cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
- \+ *lemma* real.cos_pos_of_mem_Ioo
- \- *lemma* real.cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
- \+ *lemma* real.deriv_tan
- \+ *lemma* real.deriv_tan_of_mem_Ioo
- \+ *lemma* real.differentiable_at_tan
- \+ *lemma* real.differentiable_at_tan_of_mem_Ioo
- \+ *lemma* real.has_deriv_at_tan
- \+ *lemma* real.has_deriv_at_tan_of_mem_Ioo



## [2020-09-06 06:48:30](https://github.com/leanprover-community/mathlib/commit/6296386)
feat(data/mv_polynomial): fill in API for vars ([#4018](https://github.com/leanprover-community/mathlib/pull/4018))
`mv_polynomial.vars` was missing a lot of API. This doesn't cover everything, but it fleshes out the theory quite a bit. There's probably more coming eventually -- this is what we have now.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.aeval_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.degrees_add_of_disjoint
- \+ *lemma* mv_polynomial.degrees_map
- \+ *lemma* mv_polynomial.degrees_map_of_injective
- \+ *lemma* mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars
- \+ *lemma* mv_polynomial.le_degrees_add
- \+ *lemma* mv_polynomial.mem_degrees
- \+ *lemma* mv_polynomial.mem_vars
- \+ *lemma* mv_polynomial.support_map_of_injective
- \+ *lemma* mv_polynomial.support_map_subset
- \+ *lemma* mv_polynomial.vars_add_of_disjoint
- \+ *lemma* mv_polynomial.vars_add_subset
- \+ *lemma* mv_polynomial.vars_eq_support_bind_support
- \+ *lemma* mv_polynomial.vars_map
- \+ *lemma* mv_polynomial.vars_map_of_injective
- \+ *lemma* mv_polynomial.vars_monomial_single
- \+ *lemma* mv_polynomial.vars_neg
- \+ *lemma* mv_polynomial.vars_sub_of_disjoint
- \+ *lemma* mv_polynomial.vars_sub_subset
- \+ *lemma* mv_polynomial.vars_sum_of_disjoint
- \+ *lemma* mv_polynomial.vars_sum_subset



## [2020-09-06 05:07:42](https://github.com/leanprover-community/mathlib/commit/7b3c653)
chore(data/finset/lattice): remove unneeded assumptions ([#4020](https://github.com/leanprover-community/mathlib/pull/4020))
#### Estimated changes
Modified src/combinatorics/composition.lean


Modified src/data/finset/lattice.lean
- \+/\- *theorem* finset.le_max'
- \+/\- *lemma* finset.max'_singleton
- \+/\- *theorem* finset.min'_le
- \+/\- *theorem* finset.min'_lt_max'
- \+/\- *lemma* finset.min'_lt_max'_of_card
- \+/\- *lemma* finset.min'_singleton

Modified src/data/finset/sort.lean
- \+ *lemma* finset.max'_eq_sorted_last
- \+ *lemma* finset.min'_eq_sorted_zero
- \+/\- *lemma* finset.mono_of_fin_last
- \+/\- *lemma* finset.mono_of_fin_zero
- \+/\- *lemma* finset.sorted_last_eq_max'
- \+ *lemma* finset.sorted_last_eq_max'_aux
- \+/\- *lemma* finset.sorted_zero_eq_min'
- \+ *lemma* finset.sorted_zero_eq_min'_aux

Modified src/order/filter/at_top_bot.lean




## [2020-09-05 13:51:33](https://github.com/leanprover-community/mathlib/commit/815a2f9)
feat(computability/encoding): define encoding of basic data types ([#3976](https://github.com/leanprover-community/mathlib/pull/3976))
We define the encoding of natural numbers and booleans to strings for Turing machines to be used in our future PR on polynomial time computation on Turing machines.
#### Estimated changes
Added src/computability/encoding.lean
- \+ *def* computability.decode_bool
- \+ *lemma* computability.decode_encode_bool
- \+ *lemma* computability.decode_encode_nat
- \+ *lemma* computability.decode_encode_num
- \+ *lemma* computability.decode_encode_pos_num
- \+ *def* computability.decode_nat
- \+ *def* computability.decode_num
- \+ *def* computability.decode_pos_num
- \+ *def* computability.encode_bool
- \+ *def* computability.encode_nat
- \+ *def* computability.encode_num
- \+ *def* computability.encode_pos_num
- \+ *lemma* computability.encode_pos_num_nonempty
- \+ *def* computability.encoding_nat_bool
- \+ *def* computability.encoding_nat_Γ'
- \+ *def* computability.fin_encoding_bool_bool
- \+ *def* computability.fin_encoding_nat_bool
- \+ *def* computability.fin_encoding_nat_Γ'
- \+ *def* computability.inclusion_bool_Γ'
- \+ *lemma* computability.inclusion_bool_Γ'_injective
- \+ *lemma* computability.left_inverse_section_inclusion
- \+ *def* computability.section_Γ'_bool
- \+ *lemma* computability.unary_decode_encode_nat
- \+ *def* computability.unary_decode_nat
- \+ *def* computability.unary_encode_nat
- \+ *def* computability.unary_fin_encoding_nat



## [2020-09-05 09:19:56](https://github.com/leanprover-community/mathlib/commit/364d5d4)
feat(linear_algebra/char_poly): rephrase Cayley-Hamilton with `aeval', define `matrix.min_poly` ([#4040](https://github.com/leanprover-community/mathlib/pull/4040))
Rephrases the Cayley-Hamilton theorem to use `aeval`, renames it `aeval_self_char_poly`
Defines `matrix.min_poly`, the minimal polynomial of a matrix, which divides `char_poly`
#### Estimated changes
Modified docs/100.yaml


Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/linear_algebra/char_poly.lean
- \+ *theorem* aeval_self_char_poly
- \- *theorem* char_poly_map_eval_self

Modified src/linear_algebra/char_poly/coeff.lean
- \+ *theorem* matrix.is_integral
- \+ *theorem* matrix.min_poly_dvd_char_poly



## [2020-09-05 00:55:56](https://github.com/leanprover-community/mathlib/commit/ccd502a)
chore(scripts): update nolints.txt ([#4044](https://github.com/leanprover-community/mathlib/pull/4044))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-04 11:49:24](https://github.com/leanprover-community/mathlib/commit/7c9a86d)
refactor(geometry/manifold): use a sigma type for the total space of the tangent bundle ([#3966](https://github.com/leanprover-community/mathlib/pull/3966))
Redefine the total space of the tangent bundle to be a sigma type instead of a product type. Before
```
have p : tangent_bundle I M := sorry,
rcases p with ⟨x, v⟩,
-- x: M
-- v: E
```
After
```
have p : tangent_bundle I M := sorry,
rcases p with ⟨x, v⟩,
-- x: M
-- v: tangent_space I x
```
This seems more natural, and is probably needed to do Riemannian manifolds right. The drawback is that we can not abuse identifications any more between the tangent bundle to a vector space and a product space (but we can still identify the tangent space with the vector space itself, which is the most important thing).
#### Estimated changes
Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.inv_fun_as_coe
- \+/\- *lemma* equiv.to_fun_as_coe

Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* basic_smooth_bundle_core.coe_chart_at_symm_fst
- \+/\- *lemma* basic_smooth_bundle_core.mem_atlas_iff
- \+/\- *lemma* basic_smooth_bundle_core.mem_chart_target_iff
- \+ *lemma* tangent_bundle.proj_apply
- \+/\- *def* tangent_bundle
- \+ *def* tangent_bundle_model_space_homeomorph
- \+ *lemma* tangent_bundle_model_space_homeomorph_coe
- \+ *lemma* tangent_bundle_model_space_homeomorph_coe_symm
- \- *lemma* tangent_bundle_model_space_topology_eq_prod
- \+/\- *def* tangent_space

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* tangent_map_chart_symm

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* topological_fiber_bundle_core.total_space



## [2020-09-04 00:52:11](https://github.com/leanprover-community/mathlib/commit/ecf18c6)
refactor(field_theory/minimal_polynomial, *): make `aeval`, `is_integral`, and `minimal_polynomial` noncommutative ([#4001](https://github.com/leanprover-community/mathlib/pull/4001))
Makes `aeval`, `is_integral`, and `minimal_polynomial` compatible with noncommutative algebras
Renames `eval₂_ring_hom_noncomm` to `eval₂_ring_hom'`
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.eval₂_list_prod_noncomm
- \+/\- *lemma* polynomial.eval₂_mul_noncomm
- \+ *def* polynomial.eval₂_ring_hom'
- \- *def* polynomial.eval₂_ring_hom_noncomm

Modified src/field_theory/minimal_polynomial.lean


Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.ker_eval₂_ring_hom'_unit_polynomial
- \- *lemma* module.End.ker_eval₂_ring_hom_noncomm_unit_polynomial

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \- *theorem* is_integral_of_noetherian'
- \+/\- *theorem* is_integral_of_noetherian
- \+ *theorem* is_integral_of_submodule_noetherian



## [2020-09-03 21:00:06](https://github.com/leanprover-community/mathlib/commit/e3057ba)
doc(slim_check): add suggestion ([#4024](https://github.com/leanprover-community/mathlib/pull/4024))
#### Estimated changes
Modified src/tactic/slim_check.lean




## [2020-09-03 19:18:55](https://github.com/leanprover-community/mathlib/commit/a056ccb)
feat(slim_check): subtype instances for `le` `lt` and `list.perm` ([#4027](https://github.com/leanprover-community/mathlib/pull/4027))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* list.perm_insert_nth

Modified src/data/list/sort.lean


Modified src/testing/slim_check/gen.lean
- \+ *def* slim_check.gen.permutation_of

Modified src/testing/slim_check/sampleable.lean


Modified src/testing/slim_check/testable.lean




## [2020-09-03 17:36:08](https://github.com/leanprover-community/mathlib/commit/2d40d9c)
feat(data/padics): universal property of Z_p ([#3950](https://github.com/leanprover-community/mathlib/pull/3950))
We establish the universal property of $\mathbb{Z}_p$ as a projective limit. Given a family of compatible ring homs $f_k : R \to \mathbb{Z}/p^n\mathbb{Z}$, there is a unique limit $R \to \mathbb{Z}_p$.
In addition, we:
* split `padic_integers.lean` into two files, creating `ring_homs.lean`
* renamings: `padic_norm_z.*` -> `padic_int.norm_*`
#### Estimated changes
Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \- *lemma* padic_int.appr_lt
- \- *lemma* padic_int.appr_spec
- \+/\- *lemma* padic_int.coe_sub
- \- *lemma* padic_int.exists_mem_range
- \+ *lemma* padic_int.exists_pow_neg_lt
- \+ *lemma* padic_int.exists_pow_neg_lt_rat
- \+/\- *lemma* padic_int.ext
- \- *lemma* padic_int.is_unit_denom
- \- *lemma* padic_int.ker_to_zmod
- \- *lemma* padic_int.ker_to_zmod_pow
- \+ *lemma* padic_int.mem_span_pow_iff_le_valuation
- \- *def* padic_int.mod_part
- \- *lemma* padic_int.mod_part_lt_p
- \- *lemma* padic_int.mod_part_nonneg
- \+ *theorem* padic_int.nonarchimedean
- \+ *theorem* padic_int.norm_add_eq_max_of_ne
- \+ *lemma* padic_int.norm_def
- \+ *lemma* padic_int.norm_eq_of_norm_add_lt_left
- \+ *lemma* padic_int.norm_eq_of_norm_add_lt_right
- \+ *lemma* padic_int.norm_eq_padic_norm
- \+ *lemma* padic_int.norm_int_cast_eq_padic_norm
- \+ *lemma* padic_int.norm_int_le_pow_iff_dvd
- \+ *lemma* padic_int.norm_le_one
- \+ *lemma* padic_int.norm_le_pow_iff_le_valuation
- \+ *lemma* padic_int.norm_le_pow_iff_mem_span_pow
- \+ *lemma* padic_int.norm_le_pow_iff_norm_lt_pow_add_one
- \+ *lemma* padic_int.norm_lt_pow_iff_norm_le_pow_sub_one
- \+ *lemma* padic_int.norm_mul
- \+ *lemma* padic_int.norm_one
- \+ *lemma* padic_int.norm_p
- \+ *lemma* padic_int.norm_p_pow
- \+ *lemma* padic_int.norm_pow
- \- *lemma* padic_int.norm_sub_mod_part
- \- *lemma* padic_int.norm_sub_mod_part_aux
- \+ *def* padic_int.of_int_seq
- \- *lemma* padic_int.p_dvd_of_norm_lt_one
- \+ *lemma* padic_int.padic_norm_e_of_padic_int
- \+/\- *lemma* padic_int.pow_p_dvd_int_iff
- \- *lemma* padic_int.sub_zmod_repr_mem
- \- *def* padic_int.to_zmod
- \- *def* padic_int.to_zmod_hom
- \- *def* padic_int.to_zmod_pow
- \- *lemma* padic_int.to_zmod_spec
- \- *lemma* padic_int.zmod_congr_of_sub_mem_max_ideal
- \- *lemma* padic_int.zmod_congr_of_sub_mem_span
- \- *lemma* padic_int.zmod_congr_of_sub_mem_span_aux
- \- *def* padic_int.zmod_repr
- \- *lemma* padic_int.zmod_repr_lt_p
- \- *lemma* padic_int.zmod_repr_spec
- \- *theorem* padic_norm_z.add_eq_max_of_ne
- \- *lemma* padic_norm_z.eq_of_norm_add_lt_left
- \- *lemma* padic_norm_z.eq_of_norm_add_lt_right
- \- *lemma* padic_norm_z.le_one
- \- *lemma* padic_norm_z.mul
- \- *theorem* padic_norm_z.nonarchimedean
- \- *lemma* padic_norm_z.norm_one
- \- *lemma* padic_norm_z.norm_p
- \- *lemma* padic_norm_z.norm_p_pow
- \- *lemma* padic_norm_z.one
- \- *lemma* padic_norm_z.padic_norm_e_of_padic_int
- \- *lemma* padic_norm_z.padic_norm_z_eq_padic_norm_e
- \- *lemma* padic_norm_z.padic_norm_z_of_int
- \- *lemma* padic_norm_z.padic_val_of_cong_pow_p
- \- *lemma* padic_norm_z.pow
- \- *lemma* padic_norm_z

Modified src/data/padics/padic_numbers.lean
- \+ *lemma* padic_norm_e.norm_int_le_pow_iff_dvd
- \- *lemma* padic_norm_e.norm_int_lt_pow_iff_dvd

Added src/data/padics/ring_homs.lean
- \+ *lemma* padic_int.appr_lt
- \+ *lemma* padic_int.appr_mono
- \+ *lemma* padic_int.appr_spec
- \+ *lemma* padic_int.cast_to_zmod_pow
- \+ *lemma* padic_int.dense_range_int_cast
- \+ *lemma* padic_int.dense_range_nat_cast
- \+ *lemma* padic_int.dvd_appr_sub_appr
- \+ *lemma* padic_int.exists_mem_range
- \+ *lemma* padic_int.exists_mem_range_of_norm_rat_le_one
- \+ *lemma* padic_int.ext_of_to_zmod_pow
- \+ *lemma* padic_int.is_cau_seq_nth_hom
- \+ *lemma* padic_int.is_unit_denom
- \+ *lemma* padic_int.ker_to_zmod
- \+ *lemma* padic_int.ker_to_zmod_pow
- \+ *def* padic_int.lift
- \+ *lemma* padic_int.lift_self
- \+ *lemma* padic_int.lift_spec
- \+ *lemma* padic_int.lift_sub_val_mem_span
- \+ *lemma* padic_int.lift_unique
- \+ *def* padic_int.lim_nth_hom
- \+ *lemma* padic_int.lim_nth_hom_add
- \+ *lemma* padic_int.lim_nth_hom_mul
- \+ *lemma* padic_int.lim_nth_hom_one
- \+ *lemma* padic_int.lim_nth_hom_spec
- \+ *lemma* padic_int.lim_nth_hom_zero
- \+ *def* padic_int.mod_part
- \+ *lemma* padic_int.mod_part_lt_p
- \+ *lemma* padic_int.mod_part_nonneg
- \+ *lemma* padic_int.norm_sub_mod_part
- \+ *lemma* padic_int.norm_sub_mod_part_aux
- \+ *def* padic_int.nth_hom
- \+ *def* padic_int.nth_hom_seq
- \+ *lemma* padic_int.nth_hom_seq_add
- \+ *lemma* padic_int.nth_hom_seq_mul
- \+ *lemma* padic_int.nth_hom_seq_one
- \+ *lemma* padic_int.nth_hom_zero
- \+ *lemma* padic_int.pow_dvd_nth_hom_sub
- \+ *lemma* padic_int.sub_zmod_repr_mem
- \+ *def* padic_int.to_zmod
- \+ *def* padic_int.to_zmod_hom
- \+ *def* padic_int.to_zmod_pow
- \+ *lemma* padic_int.to_zmod_pow_eq_iff_ext
- \+ *lemma* padic_int.to_zmod_spec
- \+ *lemma* padic_int.zmod_cast_comp_to_zmod_pow
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_max_ideal
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_span
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_span_aux
- \+ *def* padic_int.zmod_repr
- \+ *lemma* padic_int.zmod_repr_lt_p
- \+ *lemma* padic_int.zmod_repr_spec

Modified src/data/real/cau_seq.lean
- \+ *lemma* cau_seq.add_equiv_add
- \+ *lemma* cau_seq.neg_equiv_neg

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_neg



## [2020-09-03 16:43:52](https://github.com/leanprover-community/mathlib/commit/49173c0)
ci(scripts/detect_errors.py): enforce silent builds ([#4025](https://github.com/leanprover-community/mathlib/pull/4025))
Refactor of [#3989](https://github.com/leanprover-community/mathlib/pull/3989). 
This changes the GitHub Actions workflow so that the main build step and the test step run `lean` with `--json`. The JSON output is piped to `detect_errors.py` which now exits at the end of the build if there is any output and also writes a file `src/.noisy_files` with the names of the noisy Lean files. This file is now included in the olean caches uploaded to Azure.
The "try to find olean cache" step now uses `src/.noisy_files` to delete all of the `.olean` files corresponding to the noisy Lean files, thus making the results of CI idempotent (hopefully).
#### Estimated changes
Modified .github/workflows/build.yml


Modified .gitignore


Modified scripts/detect_errors.py


Modified scripts/fetch_olean_cache.sh


Modified src/analysis/specific_limits.lean




## [2020-09-03 14:47:30](https://github.com/leanprover-community/mathlib/commit/8b277a9)
feat(category_theory/filtered): finite diagrams in filtered categories admit cocones ([#4026](https://github.com/leanprover-community/mathlib/pull/4026))
This is only step towards eventual results about filtered colimits commuting with finite limits, `forget CommRing` preserving filtered colimits, and applications to `Scheme`.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* category_theory.is_filtered.cocone_nonempty
- \+ *lemma* category_theory.is_filtered.coeq_condition
- \+ *def* category_theory.is_filtered.sup
- \+ *lemma* category_theory.is_filtered.sup_exists'
- \+ *lemma* category_theory.is_filtered.sup_exists
- \+ *lemma* category_theory.is_filtered.sup_objs_exists
- \+ *def* category_theory.is_filtered.to_sup
- \+ *lemma* category_theory.is_filtered.to_sup_commutes

Added src/category_theory/fin_category.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/linear_algebra/basic.lean


Modified src/logic/basic.lean
- \+ *theorem* exists_apply_eq_apply'
- \+ *theorem* exists_apply_eq_apply
- \+/\- *theorem* exists_eq'



## [2020-09-03 11:22:52](https://github.com/leanprover-community/mathlib/commit/fa6485a)
feat(category_theory/limits/concrete): simp lemmas ([#3973](https://github.com/leanprover-community/mathlib/pull/3973))
Some specialisations of simp lemmas about (co)limits for concrete categories, where the equation in morphisms has been applied to an element.
This isn't exhaustive; just the things I've wanted recently.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean
- \- *lemma* AddCommGroup.lift_π_apply

Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/limits/concrete_category.lean
- \- *lemma* category_theory.limits.cocone.naturality_concrete
- \+ *lemma* category_theory.limits.cocone.w_apply
- \+ *lemma* category_theory.limits.cocone.w_forget_apply
- \+ *lemma* category_theory.limits.colimit.w_apply
- \+ *lemma* category_theory.limits.colimit.ι_desc_apply
- \- *lemma* category_theory.limits.cone.naturality_concrete
- \+ *lemma* category_theory.limits.cone.w_apply
- \+ *lemma* category_theory.limits.cone.w_forget_apply
- \+ *lemma* category_theory.limits.limit.lift_π_apply
- \+ *lemma* category_theory.limits.limit.w_apply



## [2020-09-03 04:04:29](https://github.com/leanprover-community/mathlib/commit/dd633c2)
feat(geometry/euclidean/circumcenter): more lemmas ([#4028](https://github.com/leanprover-community/mathlib/pull/4028))
Add some more basic lemmas about `circumcenter` and `circumradius`.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.circumcenter_eq_centroid
- \+ *lemma* affine.simplex.circumcenter_eq_point
- \+ *lemma* affine.simplex.circumradius_nonneg
- \+ *lemma* affine.simplex.circumradius_pos
- \+ *lemma* affine.simplex.orthogonal_projection_circumcenter



## [2020-09-03 01:52:48](https://github.com/leanprover-community/mathlib/commit/c86359f)
chore(scripts): update nolints.txt ([#4030](https://github.com/leanprover-community/mathlib/pull/4030))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-03 01:52:46](https://github.com/leanprover-community/mathlib/commit/ca5703d)
fix(docs/100.yaml): fix indentation in 100 list ([#4029](https://github.com/leanprover-community/mathlib/pull/4029))
#### Estimated changes
Modified docs/100.yaml




## [2020-09-03 00:15:49](https://github.com/leanprover-community/mathlib/commit/7b9db99)
fix(test/*): make sure tests produce no output ([#3947](https://github.com/leanprover-community/mathlib/pull/3947))
Modify tests so that they produce no output. This also means removing all uses of `sorry`/`admit`.
Replace `#eval` by `run_cmd` consistently.
Tests that produced output before are modified so that it is checked that they roughly produce the right output
Add a trace option to the `#simp` command that turns the message of only if the expression is simplified to `true`. All tests are modified so that they simplify to `true`.
The randomized tests can produce output when they find a false positive, but that should basically never happen.
Add some docstings to `src/tactic/interactive`.
#### Estimated changes
Modified src/tactic/interactive.lean


Modified src/tactic/simp_command.lean


Modified src/tactic/squeeze.lean


Added test/README.md


Modified test/continuity.lean


Modified test/doc_commands.lean


Modified test/general_recursion.lean


Modified test/library_search/exp_le_exp.lean


Modified test/library_search/filter.lean


Modified test/library_search/nat.lean


Modified test/linarith.lean
- \+/\- *lemma* T.zero_lt_one
- \+/\- *lemma* abs_nonneg'

Modified test/lint_coe_t.lean


Modified test/lint_coe_to_fun.lean


Modified test/lint_simp_comm.lean


Modified test/lint_simp_nf.lean


Modified test/lint_simp_var_head.lean


Modified test/logic_inline.lean


Modified test/norm_cast_int.lean


Modified test/norm_cast_lemma_order.lean


Modified test/norm_cast_sum_lambda.lean


Modified test/norm_num.lean


Modified test/packaged_goal.lean


Modified test/protec_proj.lean


Modified test/refine_struct.lean


Modified test/simp_command.lean


Modified test/slim_check.lean


Modified test/squeeze.lean


Modified test/zify.lean




## [2020-09-02 19:38:06](https://github.com/leanprover-community/mathlib/commit/9d42f6c)
feat(order/rel_iso): define `rel_hom` (relation-preserving maps) ([#3946](https://github.com/leanprover-community/mathlib/pull/3946))
Creates a typeclass for (unidirectionally) relation-preserving maps that are not necessarily injective
(In the case of <= relations, this is essentially a bundled monotone map)
Proves that these transfer well-foundedness between relations
#### Estimated changes
Modified src/order/ord_continuous.lean


Modified src/order/order_iso_nat.lean


Modified src/order/rel_iso.lean
- \- *def* order_embedding.osymm
- \- *def* order_iso.osymm
- \+ *lemma* rel_embedding.coe_coe_fn
- \+ *theorem* rel_embedding.ext
- \+ *theorem* rel_embedding.ext_iff
- \- *def* rel_embedding.rsymm
- \+ *def* rel_embedding.to_rel_hom
- \+ *lemma* rel_embedding.to_rel_hom_eq_coe
- \+ *theorem* rel_hom.coe_fn_inj
- \+ *theorem* rel_hom.coe_fn_mk
- \+ *theorem* rel_hom.coe_fn_to_fun
- \+ *theorem* rel_hom.comp_apply
- \+ *theorem* rel_hom.ext
- \+ *theorem* rel_hom.ext_iff
- \+ *theorem* rel_hom.id_apply
- \+ *lemma* rel_hom.injective_of_increasing
- \+ *theorem* rel_hom.map_rel
- \+ *def* rel_hom.preimage
- \+/\- *theorem* rel_iso.coe_fn_mk
- \+/\- *theorem* rel_iso.ext
- \+ *theorem* rel_iso.ext_iff
- \- *def* rel_iso.rsymm
- \+ *theorem* surjective.well_founded_iff

Modified src/ring_theory/noetherian.lean




## [2020-09-02 15:51:17](https://github.com/leanprover-community/mathlib/commit/57463fa)
feat(linear_algebra/affine_space): more lemmas ([#3990](https://github.com/leanprover-community/mathlib/pull/3990))
Add another batch of lemmas about affine spaces.  These lemmas mostly
relate to manipulating centroids and the relations between centroids
of points given by different subsets of the index type.
#### Estimated changes
Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.affine_combination_map
- \+ *lemma* finset.centroid_eq_affine_combination_fintype
- \+ *lemma* finset.centroid_insert_singleton
- \+ *lemma* finset.centroid_insert_singleton_fin
- \+ *lemma* finset.centroid_map
- \+ *def* finset.centroid_weights_indicator
- \+ *lemma* finset.centroid_weights_indicator_def
- \+ *lemma* finset.sum_centroid_weights_indicator
- \+ *lemma* finset.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one
- \+ *lemma* finset.sum_centroid_weights_indicator_eq_one_of_card_ne_zero
- \+ *lemma* finset.sum_centroid_weights_indicator_eq_one_of_nonempty
- \+ *lemma* finset.weighted_vsub_map
- \+ *lemma* finset.weighted_vsub_of_point_map

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine.simplex.centroid_eq_iff
- \+ *lemma* affine.simplex.face_centroid_eq_centroid
- \+ *lemma* affine.simplex.face_centroid_eq_iff
- \+ *lemma* affine.simplex.range_face_points
- \+ *lemma* affine_independent_of_ne



## [2020-09-02 15:11:55](https://github.com/leanprover-community/mathlib/commit/71ef45e)
chore(topology/sheaves): depend less on rfl ([#3994](https://github.com/leanprover-community/mathlib/pull/3994))
Another backport from the `prop_limits` branch.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \- *lemma* category_theory.limits.types.lift_π_apply'
- \+ *lemma* category_theory.limits.types.pi_lift_π_apply
- \+ *lemma* category_theory.limits.types.pi_map_π_apply

Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.colimit_sound
- \+ *lemma* category_theory.limits.types.colimit_w_apply
- \+ *lemma* category_theory.limits.types.filtered_colimit.colimit_eq_iff_aux
- \+ *lemma* category_theory.limits.types.limit_w_apply
- \+ *lemma* category_theory.limits.types.map_π_apply
- \+ *lemma* category_theory.limits.types.ι_map_apply

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/stalks.lean




## [2020-09-02 13:19:05](https://github.com/leanprover-community/mathlib/commit/895f6ee)
chore(algebra/category/CommRing/limits): don't use deprecated.subring ([#4010](https://github.com/leanprover-community/mathlib/pull/4010))
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean
- \+ *def* Ring.sections_subring



## [2020-09-02 13:19:01](https://github.com/leanprover-community/mathlib/commit/ddbdfeb)
chore(data/fin): succ_above defn compares fin terms instead of values ([#3999](https://github.com/leanprover-community/mathlib/pull/3999))
`fin.succ_above` is redefined to use a comparison between two `fin (n + 1)` instead of their coerced values in `nat`. This should delay any "escape" from `fin` into `nat` until necessary. Lemmas are added regarding `fin.succ_above`. Some proofs for existing lemmas reworked for new definition and simplified. Additionally, docstrings are added for related lemmas.
New lemmas:
Comparison after embedding:
`succ_above_lt_ge`
`succ_above_lt_gt`
Injectivity lemmas:
`succ_above_right_inj`
`succ_above_right_injective`
`succ_above_left_inj`
`succ_above_left_injective`
finset lemma:
`fin.univ_succ_above`
prod and sum lemmas:
`fin.prod_univ_succ_above`
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_succ_pos
- \+/\- *lemma* fin.pred_above_succ_above
- \+/\- *def* fin.succ_above
- \+/\- *lemma* fin.succ_above_above
- \+/\- *lemma* fin.succ_above_below
- \+/\- *lemma* fin.succ_above_descend
- \+ *lemma* fin.succ_above_left_inj
- \+ *lemma* fin.succ_above_left_injective
- \+ *lemma* fin.succ_above_lt_ge
- \+ *lemma* fin.succ_above_lt_gt
- \+/\- *theorem* fin.succ_above_ne
- \+ *lemma* fin.succ_above_right_inj
- \+ *lemma* fin.succ_above_right_injective

Modified src/data/fintype/basic.lean
- \+ *lemma* fin.univ_succ_above

Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.prod_univ_cast_succ
- \+/\- *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_succ_above
- \+/\- *theorem* fin.prod_univ_zero
- \+/\- *theorem* fin.sum_univ_cast_succ
- \+/\- *theorem* fin.sum_univ_succ
- \+ *theorem* fin.sum_univ_succ_above



## [2020-09-02 13:18:59](https://github.com/leanprover-community/mathlib/commit/96c80e2)
feat(ring_theory/localization): Localizations of integral extensions ([#3942](https://github.com/leanprover-community/mathlib/pull/3942))
The main definition is the algebra induced by localization at an algebra. Given an algebra `R → S` and a submonoid `M` of `R`, as well as localization maps `f : R → Rₘ` and `g : S → Sₘ`, there is a natural algebra `Rₘ → Sₘ` that makes the entire square commute, and this is defined as `localization_algebra`. 
The two main theorems are similar but distinct statements about integral elements and localizations:
* `is_integral_localization_at_leading_coeff` says that if an element `x` is algebraic over `algebra R S`, then if we localize to a submonoid containing the leading coefficient the image of `x` will be integral.
* `is_integral_localization` says that if `R → S` is an integral extension, then the algebra induced by localizing at any particular submonoid will be an integral extension.
#### Estimated changes
Modified src/data/finsupp/basic.lean


Modified src/data/monoid_algebra.lean


Modified src/data/polynomial/degree.lean
- \+ *lemma* polynomial.leading_coeff_map'
- \+ *lemma* polynomial.leading_coeff_map_of_leading_coeff_ne_zero
- \+ *lemma* polynomial.nat_degree_map_of_leading_coeff_ne_zero

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval₂_mul_eq_zero_of_left
- \+ *lemma* polynomial.eval₂_mul_eq_zero_of_right

Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic_mul_C_of_leading_coeff_mul_eq_one

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.mem_map_of_mem

Modified src/ring_theory/algebra.lean
- \+ *def* algebra.algebra_map_submonoid
- \+ *lemma* algebra.mem_algebra_map_submonoid_of_mem

Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_integral_mul_unit

Modified src/ring_theory/localization.lean
- \- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *theorem* is_integral_localization
- \+ *theorem* is_integral_localization_at_leading_coeff
- \- *lemma* le_non_zero_divisors_of_domain
- \- *lemma* map_mem_non_zero_divisors
- \- *lemma* map_ne_zero_of_mem_non_zero_divisors
- \- *lemma* mem_non_zero_divisors_iff_ne_zero
- \- *lemma* mul_mem_non_zero_divisors
- \- *def* non_zero_divisors

Added src/ring_theory/non_zero_divisors.lean
- \+ *lemma* eq_zero_of_ne_zero_of_mul_left_eq_zero
- \+ *lemma* eq_zero_of_ne_zero_of_mul_right_eq_zero
- \+ *lemma* le_non_zero_divisors_of_domain
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* mul_mem_non_zero_divisors
- \+ *def* non_zero_divisors

Modified src/ring_theory/polynomial/rational_root.lean
- \- *lemma* coeff_scale_roots
- \- *lemma* coeff_scale_roots_nat_degree
- \- *lemma* degree_scale_roots
- \- *lemma* monic_scale_roots_iff
- \- *lemma* nat_degree_scale_roots
- \- *lemma* scale_roots_aeval_eq_zero
- \- *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero
- \- *lemma* scale_roots_eval₂_eq_zero
- \- *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \- *lemma* scale_roots_ne_zero
- \- *lemma* support_scale_roots_eq
- \- *lemma* support_scale_roots_le
- \- *lemma* zero_scale_roots

Added src/ring_theory/polynomial/scale_roots.lean
- \+ *lemma* coeff_scale_roots
- \+ *lemma* coeff_scale_roots_nat_degree
- \+ *lemma* degree_scale_roots
- \+ *lemma* monic_scale_roots_iff
- \+ *lemma* nat_degree_scale_roots
- \+ *lemma* scale_roots_aeval_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \+ *lemma* scale_roots_ne_zero
- \+ *lemma* support_scale_roots_eq
- \+ *lemma* support_scale_roots_le
- \+ *lemma* zero_scale_roots



## [2020-09-02 11:43:54](https://github.com/leanprover-community/mathlib/commit/cd36773)
feat(linear_algebra/eigenspace): add generalized eigenspaces ([#4015](https://github.com/leanprover-community/mathlib/pull/4015))
Add the definition of generalized eigenspaces, eigenvectors and eigenvalues. Add some basic lemmas about them.
Another step towards [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* nsmul_add_sub_nsmul
- \+ *theorem* pow_mul_pow_sub
- \+ *theorem* pow_sub_mul_pow
- \+ *theorem* sub_nsmul_nsmul_add

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.eigenspace_le_generalized_eigenspace
- \+ *lemma* module.End.exp_ne_zero_of_has_generalized_eigenvalue
- \+ *def* module.End.generalized_eigenspace
- \+ *lemma* module.End.generalized_eigenspace_mono
- \+ *def* module.End.has_generalized_eigenvalue
- \+ *lemma* module.End.has_generalized_eigenvalue_of_has_eigenvalue
- \+ *lemma* module.End.has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le
- \+ *def* module.End.has_generalized_eigenvector



## [2020-09-02 08:30:45](https://github.com/leanprover-community/mathlib/commit/7310eab)
feat(field_theory/adjoin): adjoining elements to fields ([#3913](https://github.com/leanprover-community/mathlib/pull/3913))
Defines adjoining elements to fields
#### Estimated changes
Added src/field_theory/adjoin.lean
- \+ *lemma* field.adjoin.algebra_map_mem
- \+ *lemma* field.adjoin.mono
- \+ *lemma* field.adjoin.range_algebra_map_subset
- \+ *def* field.adjoin
- \+ *lemma* field.adjoin_adjoin_left
- \+ *lemma* field.adjoin_contains_field_as_subfield
- \+ *lemma* field.adjoin_simple.algebra_map_gen
- \+ *def* field.adjoin_simple.gen
- \+ *lemma* field.adjoin_simple_adjoin_simple
- \+ *lemma* field.adjoin_singleton
- \+ *lemma* field.adjoin_subset_adjoin_iff
- \+ *lemma* field.adjoin_subset_iff
- \+ *lemma* field.adjoin_subset_subfield
- \+ *lemma* field.mem_adjoin_simple_self
- \+ *lemma* field.subfield_subset_adjoin_self
- \+ *lemma* field.subset_adjoin
- \+ *lemma* field.subset_adjoin_of_subset_left
- \+ *lemma* field.subset_adjoin_of_subset_right

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.set_range_subset



## [2020-09-02 06:01:22](https://github.com/leanprover-community/mathlib/commit/8026ea8)
feat(ring_theory/localization): localization away from an element ([#4019](https://github.com/leanprover-community/mathlib/pull/4019))
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *lemma* add_submonoid.localization_map.away_map.lift_comp
- \+ *lemma* add_submonoid.localization_map.away_map.lift_eq
- \+ *def* localization.away.inv_self
- \+ *lemma* localization.away.mk_eq_monoid_of_mk'
- \+ *def* localization.away.monoid_of
- \+ *def* localization.away
- \+ *lemma* submonoid.localization_map.away_map.lift_comp
- \+ *lemma* submonoid.localization_map.away_map.lift_eq
- \+ *def* submonoid.localization_map.away_map
- \+/\- *lemma* submonoid.localization_map.mk'_self'
- \+/\- *lemma* submonoid.localization_map.mk'_self

Modified src/ring_theory/jacobson.lean
- \- *lemma* ideal.disjoint_closure_singleton_iff_not_mem
- \+ *lemma* ideal.disjoint_powers_iff_not_mem

Modified src/ring_theory/localization.lean
- \+ *lemma* localization.away.mk_eq_mk'
- \+ *def* localization.away.of
- \+ *lemma* localization_map.away_map.lift_comp
- \+ *lemma* localization_map.away_map.lift_eq
- \+ *def* localization_map.away_map



## [2020-09-02 00:37:30](https://github.com/leanprover-community/mathlib/commit/0b4444c)
feat(pfun/recursion): unbounded recursion ([#3778](https://github.com/leanprover-community/mathlib/pull/3778))
#### Estimated changes
Added src/control/fix.lean
- \+ *def* roption.fix.approx
- \+ *def* roption.fix_aux
- \+ *lemma* roption.fix_def'

Added src/control/lawful_fix.lean
- \+ *lemma* lawful_fix.fix_eq'
- \+ *lemma* pi.continuous_curry
- \+ *lemma* pi.continuous_uncurry
- \+ *def* pi.monotone_curry
- \+ *def* pi.monotone_uncurry
- \+ *lemma* pi.uncurry_curry_continuous
- \+ *def* roption.fix.approx_chain
- \+ *lemma* roption.fix.approx_le_fix
- \+ *lemma* roption.fix.approx_mem_approx_chain
- \+ *lemma* roption.fix.approx_mono'
- \+ *lemma* roption.fix.approx_mono
- \+ *lemma* roption.fix.exists_fix_le_approx
- \+ *lemma* roption.fix.le_f_of_mem_approx
- \+ *lemma* roption.fix.mem_iff
- \+ *lemma* roption.fix_eq
- \+ *lemma* roption.fix_eq_ωSup
- \+ *lemma* roption.fix_le
- \+ *lemma* roption.to_unit_cont
- \+ *def* roption.to_unit_mono

Added src/data/nat/upto.lean
- \+ *def* nat.upto.succ
- \+ *def* nat.upto.zero
- \+ *def* nat.upto

Modified src/data/pfun.lean
- \+ *lemma* roption.assert_neg
- \+ *lemma* roption.assert_pos
- \+ *lemma* roption.bind_le
- \+ *lemma* roption.eq_none_or_eq_some
- \+ *lemma* roption.le_total_of_le_of_le

Modified src/data/sigma/basic.lean
- \+ *def* sigma.curry
- \+ *def* sigma.uncurry

Modified src/order/bounded_lattice.lean


Modified src/order/category/Preorder.lean
- \- *lemma* preorder_hom.coe_id
- \- *lemma* preorder_hom.coe_inj
- \- *def* preorder_hom.comp
- \- *lemma* preorder_hom.comp_id
- \- *lemma* preorder_hom.ext
- \- *def* preorder_hom.id
- \- *lemma* preorder_hom.id_comp

Added src/order/category/omega_complete_partial_order.lean
- \+ *def* ωCPO.of
- \+ *def* ωCPO

Added src/order/omega_complete_partial_order.lean
- \+ *lemma* omega_complete_partial_order.chain.exists_of_mem_map
- \+ *def* omega_complete_partial_order.chain.map
- \+ *lemma* omega_complete_partial_order.chain.map_comp
- \+ *lemma* omega_complete_partial_order.chain.map_id
- \+ *lemma* omega_complete_partial_order.chain.map_le_map
- \+ *lemma* omega_complete_partial_order.chain.mem_map
- \+ *lemma* omega_complete_partial_order.chain.mem_map_iff
- \+ *def* omega_complete_partial_order.chain.zip
- \+ *def* omega_complete_partial_order.chain
- \+ *lemma* omega_complete_partial_order.const_continuous'
- \+ *def* omega_complete_partial_order.continuous'
- \+ *lemma* omega_complete_partial_order.continuous.of_bundled'
- \+ *lemma* omega_complete_partial_order.continuous.of_bundled
- \+ *lemma* omega_complete_partial_order.continuous.to_bundled
- \+ *lemma* omega_complete_partial_order.continuous.to_monotone
- \+ *def* omega_complete_partial_order.continuous
- \+ *lemma* omega_complete_partial_order.continuous_comp
- \+ *lemma* omega_complete_partial_order.continuous_hom.bind_continuous'
- \+ *lemma* omega_complete_partial_order.continuous_hom.coe_apply
- \+ *def* omega_complete_partial_order.continuous_hom.comp
- \+ *lemma* omega_complete_partial_order.continuous_hom.comp_assoc
- \+ *lemma* omega_complete_partial_order.continuous_hom.comp_id
- \+ *def* omega_complete_partial_order.continuous_hom.const
- \+ *theorem* omega_complete_partial_order.continuous_hom.const_apply
- \+ *lemma* omega_complete_partial_order.continuous_hom.continuous
- \+ *def* omega_complete_partial_order.continuous_hom.flip
- \+ *lemma* omega_complete_partial_order.continuous_hom.forall_forall_merge'
- \+ *lemma* omega_complete_partial_order.continuous_hom.forall_forall_merge
- \+ *def* omega_complete_partial_order.continuous_hom.id
- \+ *lemma* omega_complete_partial_order.continuous_hom.id_comp
- \+ *lemma* omega_complete_partial_order.continuous_hom.ite_continuous'
- \+ *lemma* omega_complete_partial_order.continuous_hom.map_continuous'
- \+ *def* omega_complete_partial_order.continuous_hom.of_fun
- \+ *def* omega_complete_partial_order.continuous_hom.of_mono
- \+ *def* omega_complete_partial_order.continuous_hom.prod.apply
- \+ *lemma* omega_complete_partial_order.continuous_hom.seq_continuous'
- \+ *def* omega_complete_partial_order.continuous_hom.to_mono
- \+ *lemma* omega_complete_partial_order.continuous_hom.ωSup_bind
- \+ *lemma* omega_complete_partial_order.continuous_hom.ωSup_def
- \+ *lemma* omega_complete_partial_order.continuous_hom.ωSup_ωSup
- \+ *lemma* omega_complete_partial_order.continuous_id
- \+ *lemma* omega_complete_partial_order.id_continuous'
- \+ *lemma* omega_complete_partial_order.le_ωSup_of_le
- \+ *def* omega_complete_partial_order.preorder_hom.monotone_apply
- \+ *def* omega_complete_partial_order.preorder_hom.to_fun_hom
- \+ *lemma* omega_complete_partial_order.ωSup_le_iff
- \+ *lemma* omega_complete_partial_order.ωSup_le_ωSup_of_le
- \+ *lemma* omega_complete_partial_order.ωSup_total
- \+ *def* pi.monotone_apply
- \+ *lemma* pi.omega_complete_partial_order.flip₁_continuous'
- \+ *lemma* pi.omega_complete_partial_order.flip₂_continuous'
- \+ *def* preorder_hom.bind
- \+ *def* preorder_hom.const
- \+ *def* preorder_hom.prod.diag
- \+ *def* preorder_hom.prod.fst
- \+ *def* preorder_hom.prod.map
- \+ *def* preorder_hom.prod.snd
- \+ *def* preorder_hom.prod.zip
- \+ *lemma* roption.eq_of_chain
- \+ *lemma* roption.mem_chain_of_mem_ωSup
- \+ *lemma* roption.mem_ωSup
- \+ *lemma* roption.ωSup_eq_none
- \+ *lemma* roption.ωSup_eq_some

Added src/order/preorder_hom.lean
- \+ *lemma* preorder_hom.coe_fun_mk
- \+ *lemma* preorder_hom.coe_id
- \+ *lemma* preorder_hom.coe_inj
- \+ *def* preorder_hom.comp
- \+ *lemma* preorder_hom.comp_id
- \+ *lemma* preorder_hom.ext
- \+ *def* preorder_hom.id
- \+ *lemma* preorder_hom.id_comp

Added test/general_recursion.lean
- \+ *theorem* roption.examples.div.cont
- \+ *theorem* roption.examples.div.equations.eqn_1
- \+ *def* roption.examples.div.intl
- \+ *def* roption.examples.div
- \+ *theorem* roption.examples.easy.cont
- \+ *theorem* roption.examples.easy.equations.eqn_1
- \+ *def* roption.examples.easy.intl
- \+ *def* roption.examples.easy
- \+ *def* roption.examples.f91'
- \+ *lemma* roption.examples.f91.cont
- \+ *theorem* roption.examples.f91.equations.eqn_1
- \+ *def* roption.examples.f91.intl
- \+ *def* roption.examples.f91
- \+ *lemma* roption.examples.f91_dom
- \+ *lemma* roption.examples.f91_spec'
- \+ *lemma* roption.examples.f91_spec
- \+ *theorem* roption.examples.tree_map'.cont
- \+ *theorem* roption.examples.tree_map'.equations.eqn_1
- \+ *theorem* roption.examples.tree_map'.equations.eqn_2
- \+ *def* roption.examples.tree_map'.intl
- \+ *def* roption.examples.tree_map'
- \+ *theorem* roption.examples.tree_map.cont
- \+ *theorem* roption.examples.tree_map.equations.eqn_1
- \+ *theorem* roption.examples.tree_map.equations.eqn_2
- \+ *def* roption.examples.tree_map.intl
- \+ *def* roption.examples.tree_map



## [2020-09-01 23:53:35](https://github.com/leanprover-community/mathlib/commit/d94643c)
doc(slim_check): improve documentation, swap instances ([#4023](https://github.com/leanprover-community/mathlib/pull/4023))
#### Estimated changes
Modified src/tactic/slim_check.lean


Modified src/testing/slim_check/testable.lean




## [2020-09-01 23:53:33](https://github.com/leanprover-community/mathlib/commit/ef22a33)
feat(slim_check/errors): improve error messages and add useful instances ([#4022](https://github.com/leanprover-community/mathlib/pull/4022))
#### Estimated changes
Modified src/tactic/slim_check.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/testing/slim_check/testable.lean




## [2020-09-01 18:54:03](https://github.com/leanprover-community/mathlib/commit/0c2e77c)
feat(testing): property based testing (basics) ([#3915](https://github.com/leanprover-community/mathlib/pull/3915))
Add `gen` monad, `sampleable` and `testable` type classes
#### Estimated changes
Modified src/data/lazy_list2.lean
- \+ *def* lazy_list.init
- \+ *def* lazy_list.interleave
- \+ *def* lazy_list.interleave_all

Added src/tactic/slim_check.lean


Added src/testing/slim_check/gen.lean
- \+ *def* slim_check.gen.choose
- \+ *def* slim_check.gen.choose_any
- \+ *def* slim_check.gen.choose_nat
- \+ *def* slim_check.gen.list_of
- \+ *def* slim_check.gen.one_of
- \+ *def* slim_check.gen.one_of_aux
- \+ *def* slim_check.gen.sized
- \+ *def* slim_check.gen.vector_of
- \+ *def* slim_check.gen
- \+ *def* slim_check.io.run_gen

Added src/testing/slim_check/sampleable.lean
- \+ *def* slim_check.int.shrink'
- \+ *def* slim_check.int.shrink
- \+ *def* slim_check.lazy_list.lseq
- \+ *def* slim_check.list.shrink'
- \+ *def* slim_check.list.shrink_with
- \+ *def* slim_check.nat.shrink'
- \+ *def* slim_check.nat.shrink
- \+ *def* slim_check.print_samples
- \+ *def* slim_check.sampleable.lift
- \+ *def* slim_check.sampleable_char
- \+ *def* slim_check.sum.shrink
- \+ *def* slim_check.tree.sample
- \+ *def* slim_check.tree.shrink_with

Added src/testing/slim_check/testable.lean
- \+ *def* slim_check.add_to_counter_example
- \+ *def* slim_check.add_var_to_counter_example
- \+ *def* slim_check.and_counter_example
- \+ *def* slim_check.combine
- \+ *def* slim_check.combine_testable
- \+ *def* slim_check.convert_counter_example'
- \+ *def* slim_check.convert_counter_example
- \+ *def* slim_check.give_up
- \+ *def* slim_check.is_failure
- \+ *def* slim_check.minimize
- \+ *def* slim_check.named_binder
- \+ *def* slim_check.or_counter_example
- \+ *def* slim_check.retry
- \+ *def* slim_check.tactic.decorations_of
- \+ *def* slim_check.test_result.to_string
- \+ *def* slim_check.testable.check'
- \+ *def* slim_check.testable.check
- \+ *def* slim_check.testable.run_suite
- \+ *def* slim_check.testable.run_suite_aux
- \+ *def* slim_check.trace_if_giveup



## [2020-09-01 12:58:32](https://github.com/leanprover-community/mathlib/commit/329393a)
feat(analysis/calculus/times_cont_diff): iterated smoothness in terms of deriv ([#4017](https://github.com/leanprover-community/mathlib/pull/4017))
Currently, iterated smoothness is only formulated in terms of the Fréchet derivative. For one-dimensional functions, it is more handy to use the one-dimensional derivative `deriv`. This PR provides a basic interface in this direction.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_within_of_open

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_of_open

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on.continuous_on_deriv_of_open
- \+ *lemma* times_cont_diff_on.continuous_on_deriv_within
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_of_open
- \+ *lemma* times_cont_diff_on.deriv_of_open
- \+ *lemma* times_cont_diff_on.deriv_within
- \+ *lemma* times_cont_diff_on.fderiv_of_open
- \+ *theorem* times_cont_diff_on_succ_iff_deriv_of_open
- \+ *theorem* times_cont_diff_on_succ_iff_deriv_within
- \+ *theorem* times_cont_diff_on_succ_iff_fderiv_of_open
- \+ *theorem* times_cont_diff_on_top_iff_deriv_of_open
- \+ *theorem* times_cont_diff_on_top_iff_deriv_within
- \+ *theorem* times_cont_diff_on_top_iff_fderiv_of_open



## [2020-09-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/849a5f9)
feat(docs,ci): move overview, undergrad, and 100 theorems lists from website ([#4016](https://github.com/leanprover-community/mathlib/pull/4016))
See conversation at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/website.20overview/near/208659351
We'll store these lists in mathlib so that we can catch breakage as soon as it happens, rather than continually repairing the website build. This PR adds the lists and a CI step that checks that every declaration name appearing in the lists actually exists in the library.
#### Estimated changes
Modified .github/workflows/build.yml


Added docs/100.yaml


Added docs/overview.yaml


Added docs/undergrad.yaml


Added scripts/yaml_check.lean
- \+ *def* databases
- \+ *def* fails

Added scripts/yaml_check.py




## [2020-09-01 12:18:06](https://github.com/leanprover-community/mathlib/commit/6a5241f)
refactor(algebra/category/*, category_theory/concrete_category): generalize universes for concrete categories ([#3687](https://github.com/leanprover-community/mathlib/pull/3687))
Currently, concrete categories need to be `large_category`s. In particular, if objects live in `Type u`, then morphisms live in `Type (u + 1)`. For the category of modules over some ring R, this is not necessarily true, because we have to take the universe of R into account. One way to deal with this problem is to just force the universe of the ring to be the same as the universe of the module. This [sounds like it shouldn't be much of an issue](https://github.com/leanprover-community/mathlib/pull/1420#discussion_r322607455), but unfortunately, [it is](https://github.com/leanprover-community/mathlib/pull/3621#issue-458293664).
This PR
* removes the constraint that a concrete category must be a `large_category`,
* generalizes `Module R` and `Algebra R` to accept a universe parameter for the module/algebra and
* adds a ton of universe annotations which become neccesary because of the change
As a reward, we get `abelian AddCommGroup.{u}` for arbitrary `u` without any (additional) work.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+/\- *def* Algebra.of

Modified src/algebra/category/Algebra/limits.lean
- \+/\- *def* Algebra.limit_π_alg_hom

Modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* SemiRing.limit_π_ring_hom

Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* Module.of
- \+/\- *def* linear_equiv.to_Module_iso'

Modified src/algebra/category/Module/kernels.lean


Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Module/monoidal.lean
- \+/\- *lemma* Module.monoidal_category.associator_hom_apply
- \+/\- *lemma* Module.monoidal_category.hom_apply
- \+/\- *def* Module.monoidal_category.left_unitor
- \+/\- *lemma* Module.monoidal_category.left_unitor_hom_apply
- \+/\- *def* Module.monoidal_category.right_unitor
- \+/\- *lemma* Module.monoidal_category.right_unitor_hom_apply
- \+/\- *lemma* Module.monoidal_category.triangle

Modified src/algebra/category/Mon/limits.lean
- \+/\- *def* Mon.limit_π_monoid_hom

Modified src/category_theory/concrete_category/basic.lean
- \+/\- *def* category_theory.concrete_category.has_coe_to_sort
- \+/\- *def* category_theory.forget
- \+/\- *def* category_theory.forget₂
- \+/\- *def* category_theory.has_forget₂.mk'

Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/concrete_category/reflects_isomorphisms.lean


Modified src/category_theory/monoidal/internal/Module.lean
- \+/\- *lemma* Module.Mon_Module_equivalence_Algebra.algebra_map
- \+/\- *def* Module.Mon_Module_equivalence_Algebra.functor
- \+/\- *def* Module.Mon_Module_equivalence_Algebra



## [2020-09-01 09:54:45](https://github.com/leanprover-community/mathlib/commit/a97d71b)
feat(data/mv_polynomial): assorted lemmas ([#4002](https://github.com/leanprover-community/mathlib/pull/4002))
Assorted additions to `mv_polynomial`. This is more from the Witt vector development. Nothing too deep here, just scattered lemmas and the `constant_coeff` ring hom.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->
Hopefully this builds -- it's split off from a branch with a lot of other changes. I think it shouldn't have dependencies!
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.aeval_eq_eval₂_hom
- \+ *lemma* mv_polynomial.aeval_monomial
- \+ *lemma* mv_polynomial.aeval_zero'
- \+ *lemma* mv_polynomial.aeval_zero
- \+ *lemma* mv_polynomial.alg_hom_C
- \+ *lemma* mv_polynomial.alg_hom_ext
- \+ *lemma* mv_polynomial.comp_aeval
- \+ *lemma* mv_polynomial.comp_eval₂_hom
- \+ *def* mv_polynomial.constant_coeff
- \+ *lemma* mv_polynomial.constant_coeff_C
- \+ *lemma* mv_polynomial.constant_coeff_X
- \+ *lemma* mv_polynomial.constant_coeff_eq
- \+ *lemma* mv_polynomial.constant_coeff_monomial
- \+ *lemma* mv_polynomial.eval_map
- \+ *lemma* mv_polynomial.eval₂_hom_C
- \+ *lemma* mv_polynomial.eval₂_hom_X'
- \+ *lemma* mv_polynomial.eval₂_hom_map_hom
- \+ *lemma* mv_polynomial.eval₂_hom_monomial
- \+ *lemma* mv_polynomial.eval₂_hom_rename
- \+ *lemma* mv_polynomial.eval₂_map
- \+ *lemma* mv_polynomial.map_aeval
- \+ *lemma* mv_polynomial.map_eval₂_hom
- \+ *lemma* mv_polynomial.ring_hom_ext



## [2020-09-01 06:48:21](https://github.com/leanprover-community/mathlib/commit/2688d42)
feat(archive/100-theorems-list): friendship theorem (nr 83) ([#3970](https://github.com/leanprover-community/mathlib/pull/3970))
defines friendship graphs
proves the friendship theorem (freek [#83](https://github.com/leanprover-community/mathlib/pull/83))
#### Estimated changes
Added archive/100-theorems-list/83_friendship_graphs.lean
- \+ *def* common_friends
- \+ *def* exists_politician
- \+ *lemma* friendship.adj_matrix_mul_const_one_mod_p_of_regular
- \+ *lemma* friendship.adj_matrix_pow_mod_p_of_regular
- \+ *lemma* friendship.adj_matrix_pow_three_of_not_adj
- \+ *lemma* friendship.adj_matrix_sq_mod_p_of_regular
- \+ *lemma* friendship.adj_matrix_sq_mul_const_one_of_regular
- \+ *theorem* friendship.adj_matrix_sq_of_ne
- \+ *theorem* friendship.adj_matrix_sq_of_regular
- \+ *lemma* friendship.card_mod_p_of_regular
- \+ *lemma* friendship.card_of_regular
- \+ *lemma* friendship.degree_eq_of_not_adj
- \+ *lemma* friendship.exists_politician_of_degree_eq_two
- \+ *lemma* friendship.exists_politician_of_degree_le_one
- \+ *lemma* friendship.exists_politician_of_degree_le_two
- \+ *lemma* friendship.false_of_three_le_degree
- \+ *theorem* friendship.is_regular_of_not_exists_politician
- \+ *lemma* friendship.neighbor_finset_eq_of_degree_eq_two
- \+ *def* friendship
- \+ *theorem* friendship_theorem
- \+ *lemma* mem_common_friends

Modified docs/references.bib




## [2020-09-01 04:51:03](https://github.com/leanprover-community/mathlib/commit/12763ec)
chore(*): more use of bundled ring homs ([#4012](https://github.com/leanprover-community/mathlib/pull/4012))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.prod_hom

Modified src/data/multiset/basic.lean
- \+/\- *lemma* multiset.prod_hom

Modified src/data/polynomial/eval.lean


Modified src/ring_theory/ideal/operations.lean




## [2020-09-01 04:51:01](https://github.com/leanprover-community/mathlib/commit/51546d2)
chore(ring_theory/free_ring): use bundled ring homs ([#4011](https://github.com/leanprover-community/mathlib/pull/4011))
Use bundled ring homs in `free_ring` and `free_comm_ring`.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/ring_theory/free_comm_ring.lean
- \- *lemma* free_comm_ring.coe_lift_hom
- \+/\- *def* free_comm_ring.lift
- \- *lemma* free_comm_ring.lift_add
- \+/\- *lemma* free_comm_ring.lift_comp_of
- \- *def* free_comm_ring.lift_hom
- \- *lemma* free_comm_ring.lift_hom_comp_of
- \- *lemma* free_comm_ring.lift_mul
- \- *lemma* free_comm_ring.lift_neg
- \- *lemma* free_comm_ring.lift_one
- \- *lemma* free_comm_ring.lift_pow
- \- *lemma* free_comm_ring.lift_sub
- \- *lemma* free_comm_ring.lift_zero
- \- *lemma* free_comm_ring.map_add
- \- *lemma* free_comm_ring.map_mul
- \- *lemma* free_comm_ring.map_neg
- \- *lemma* free_comm_ring.map_one
- \- *lemma* free_comm_ring.map_pow
- \- *lemma* free_comm_ring.map_sub
- \- *lemma* free_comm_ring.map_zero
- \- *lemma* free_comm_ring.restriction_add
- \- *lemma* free_comm_ring.restriction_mul
- \- *lemma* free_comm_ring.restriction_neg
- \- *lemma* free_comm_ring.restriction_one
- \- *lemma* free_comm_ring.restriction_sub
- \- *lemma* free_comm_ring.restriction_zero

Modified src/ring_theory/free_ring.lean
- \+/\- *def* free_ring.lift
- \- *lemma* free_ring.lift_add
- \- *def* free_ring.lift_hom
- \- *lemma* free_ring.lift_mul
- \- *lemma* free_ring.lift_neg
- \- *lemma* free_ring.lift_one
- \- *lemma* free_ring.lift_pow
- \- *lemma* free_ring.lift_sub
- \- *lemma* free_ring.lift_zero
- \+/\- *def* free_ring.map
- \- *lemma* free_ring.map_add
- \- *def* free_ring.map_hom
- \- *lemma* free_ring.map_mul
- \- *lemma* free_ring.map_neg
- \+/\- *lemma* free_ring.map_of
- \- *lemma* free_ring.map_one
- \- *lemma* free_ring.map_pow
- \- *lemma* free_ring.map_sub
- \- *lemma* free_ring.map_zero



## [2020-09-01 04:50:59](https://github.com/leanprover-community/mathlib/commit/93468fe)
chore(algebraic_geometry/Spec): reduce imports ([#4007](https://github.com/leanprover-community/mathlib/pull/4007))
The main change is to remove some `example`s from `topology.category.TopCommRing`, so that we don't need to know about the real and complex numbers on the way to defining a `Scheme`.
While I was staring at `leanproject import-graph --to algebraic_geometry.Scheme`, I also removed a bunch of redundant or unused imports elsewhere.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean


Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/limits/types.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/localization.lean


Modified src/topology/basic.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/sheaves/presheaf_of_functions.lean


Modified src/topology/sheaves/sheaf.lean




## [2020-09-01 04:50:57](https://github.com/leanprover-community/mathlib/commit/551cf8e)
refactor(algebra/associates): unite `associates.prime` with `prime` ([#3988](https://github.com/leanprover-community/mathlib/pull/3988))
deletes `associates.prime`, replaces it with the existing `prime`
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.eq_of_mul_eq_mul_right
- \+ *theorem* associates.irreducible_iff_prime_iff
- \+ *lemma* associates.le_of_mul_le_mul_right
- \+ *theorem* associates.mk_dvd_mk
- \- *lemma* associates.prime.ne_one
- \- *lemma* associates.prime.ne_zero
- \- *def* associates.prime
- \+/\- *lemma* dvd_iff_dvd_of_rel_right
- \+/\- *lemma* eq_zero_iff_of_associated
- \+/\- *lemma* irreducible_iff_of_associated
- \+/\- *lemma* irreducible_of_associated
- \+ *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul
- \+/\- *lemma* ne_zero_iff_of_associated
- \+ *lemma* prime.ne_one
- \+/\- *lemma* prime_iff_of_associated
- \+/\- *lemma* prime_of_associated

Modified src/ring_theory/integral_domain.lean
- \- *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul

Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* principal_ideal_ring.associates_irreducible_iff_prime



## [2020-09-01 04:50:54](https://github.com/leanprover-community/mathlib/commit/7cd67b5)
feat(category_theory/limits/shapes/terminal): is_terminal object ([#3957](https://github.com/leanprover-community/mathlib/pull/3957))
Add language to talk about when an object is terminal, and generalise some results to use this
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* category_theory.initial_mono
- \+/\- *def* category_theory.mul_zero
- \+/\- *def* category_theory.pow_zero
- \+ *def* category_theory.strict_initial
- \+/\- *def* category_theory.zero_mul

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.as_empty_cocone
- \+ *def* category_theory.limits.as_empty_cone
- \+ *def* category_theory.limits.initial_is_initial
- \+ *lemma* category_theory.limits.is_initial.epi_to
- \+ *lemma* category_theory.limits.is_initial.hom_ext
- \+ *def* category_theory.limits.is_initial.to
- \+ *def* category_theory.limits.is_terminal.from
- \+ *lemma* category_theory.limits.is_terminal.hom_ext
- \+ *lemma* category_theory.limits.is_terminal.mono_from
- \+ *def* category_theory.limits.terminal_is_terminal



## [2020-09-01 03:18:29](https://github.com/leanprover-community/mathlib/commit/fc57cf4)
feat(data/{finset,finsupp,multiset}): more assorted lemmas ([#4006](https://github.com/leanprover-community/mathlib/pull/4006))
Another grab bag of facts from the Witt vector branch.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.union_subset_union
- \+ *lemma* multiset.disjoint_to_finset
- \+ *lemma* multiset.to_finset_subset
- \+ *lemma* multiset.to_finset_union

Modified src/data/finset/fold.lean
- \+ *lemma* finset.fold_sup_bot_singleton
- \+ *lemma* finset.fold_union_empty_singleton

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.mem_sup
- \+ *lemma* finset.sup_subset

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.mem_to_multiset

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.count_ne_zero



## [2020-09-01 01:12:55](https://github.com/leanprover-community/mathlib/commit/c33b41b)
chore(scripts): update nolints.txt ([#4009](https://github.com/leanprover-community/mathlib/pull/4009))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-01 00:04:06](https://github.com/leanprover-community/mathlib/commit/e053bda)
feat(category_theory/monoidal/internal): Mon_ (Module R) ≌ Algebra R ([#3695](https://github.com/leanprover-community/mathlib/pull/3695))
The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
Moreover, this equivalence is compatible with the forgetful functors to `Module R`.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \- *lemma* Module.monoidal_category.associator_hom
- \+ *lemma* Module.monoidal_category.associator_hom_apply
- \+ *lemma* Module.monoidal_category.hom_apply
- \- *lemma* Module.monoidal_category.left_unitor_hom
- \+ *lemma* Module.monoidal_category.left_unitor_hom_apply
- \- *lemma* Module.monoidal_category.right_unitor_hom
- \+ *lemma* Module.monoidal_category.right_unitor_hom_apply

Modified src/algebra/module/basic.lean
- \+ *lemma* linear_map.lcongr_fun

Added src/category_theory/monoidal/internal/Module.lean
- \+ *lemma* Module.Mon_Module_equivalence_Algebra.algebra_map
- \+ *def* Module.Mon_Module_equivalence_Algebra.functor
- \+ *def* Module.Mon_Module_equivalence_Algebra.inverse
- \+ *def* Module.Mon_Module_equivalence_Algebra.inverse_obj
- \+ *def* Module.Mon_Module_equivalence_Algebra
- \+ *def* Module.Mon_Module_equivalence_Algebra_forget

Modified src/category_theory/monoidal/types.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra.linear_map_apply
- \+ *def* algebra.lmul'
- \+ *lemma* algebra.lmul'_apply

