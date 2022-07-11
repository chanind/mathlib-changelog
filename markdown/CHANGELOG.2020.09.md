## [2020-09-30 20:29:32](https://github.com/leanprover-community/mathlib/commit/bcc7c02)
feat(geometry/manifold): smooth bundled maps ([#3641](https://github.com/leanprover-community/mathlib/pull/3641))
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_add
- \+/\- *lemma* times_cont_diff_neg
- \+ *lemma* times_cont_diff_mul
- \+ *lemma* times_cont_diff_within_at.mul
- \+ *lemma* times_cont_diff_at.mul
- \+ *lemma* times_cont_diff.mul
- \+ *lemma* times_cont_diff_on.mul
- \+ *lemma* times_cont_diff_smul
- \+ *lemma* times_cont_diff_within_at.smul
- \+ *lemma* times_cont_diff_at.smul
- \+ *lemma* times_cont_diff.smul
- \+ *lemma* times_cont_diff_on.smul

Renamed src/geometry/algebra/lie_group.lean to src/geometry/manifold/algebra/lie_group.lean
- \- *lemma* smooth_mul
- \- *lemma* smooth.mul
- \- *lemma* smooth_left_mul
- \- *lemma* smooth_right_mul
- \- *lemma* smooth_on.mul

Created src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* smooth_mul
- \+ *lemma* smooth.mul
- \+ *lemma* smooth_mul_left
- \+ *lemma* smooth_mul_right
- \+ *lemma* smooth_on.mul

Created src/geometry/manifold/algebra/smooth_functions.lean
- \+ *def* smooth_map.C

Created src/geometry/manifold/algebra/structures.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean


Renamed src/geometry/manifold/real_instances.lean to src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* smooth_manifold_with_corners_of_times_cont_diff_on
- \- *lemma* compatible

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth_smul
- \+ *lemma* smooth.smul

Modified src/geometry/manifold/times_cont_mdiff_map.lean
- \+/\- *lemma* coe_inj
- \+/\- *lemma* comp_apply
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* const

Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/continuous_map.lean
- \+/\- *def* comp
- \+/\- *def* const

Modified src/topology/instances/real.lean


Modified src/topology/path_connected.lean




## [2020-09-30 19:43:08](https://github.com/leanprover-community/mathlib/commit/c04e339)
feat(archive/imo): formalize IMO 1959 problem 1 ([#4340](https://github.com/leanprover-community/mathlib/pull/4340))
This is a formalization of the problem and solution for the first problem on the 1959 IMO:
Prove that the fraction (21n+4)/(14n+3) is irreducible for every natural number n.
#### Estimated changes
Created archive/imo/imo1959_q1.lean
- \+ *lemma* calculation
- \+ *theorem* imo1959_q1



## [2020-09-30 18:14:45](https://github.com/leanprover-community/mathlib/commit/23b04b0)
chore(ring_theory/algebra): Mark algebra.mem_top as simp ([#4339](https://github.com/leanprover-community/mathlib/pull/4339))
This is consistent with `subsemiring.mem_top` and `submonoid.mem_top`, both of which are marked simp.
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+/\- *theorem* mem_top



## [2020-09-30 18:14:43](https://github.com/leanprover-community/mathlib/commit/decd67c)
feat(analysis/convex): slope_mono_adjacent ([#4307](https://github.com/leanprover-community/mathlib/pull/4307))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_on.slope_mono_adjacent
- \+ *lemma* convex_on_real_iff_slope_mono_adjacent
- \+ *lemma* concave_on.slope_mono_adjacent
- \+ *lemma* concave_on_real_iff_slope_mono_adjacent



## [2020-09-30 16:47:25](https://github.com/leanprover-community/mathlib/commit/a06c87e)
chore(*): Tidy some proofs and variables ([#4338](https://github.com/leanprover-community/mathlib/pull/4338))
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+/\- *theorem* ι_comp_lift
- \+/\- *theorem* lift_ι_apply
- \+/\- *theorem* lift_unique
- \+/\- *theorem* lift_comp_ι
- \+/\- *theorem* hom_ext
- \+/\- *def* lift

Modified src/data/monoid_algebra.lean




## [2020-09-30 16:47:23](https://github.com/leanprover-community/mathlib/commit/9921fe7)
fix(ring_theory/algebra): Fix typo "algbera" ([#4337](https://github.com/leanprover-community/mathlib/pull/4337))
Introduced in e57fc3d6c142835dc8566aa28e812f7688f14512
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebra.lean
- \+ *theorem* surjective_algebra_map_iff
- \+ *theorem* bijective_algebra_map_iff
- \- *theorem* surjective_algbera_map_iff
- \- *theorem* bijective_algbera_map_iff



## [2020-09-30 14:42:25](https://github.com/leanprover-community/mathlib/commit/05038da)
feat(ring_theory/algebra): some lemmas about numerals in algebras ([#4327](https://github.com/leanprover-community/mathlib/pull/4327))
#### Estimated changes
Modified src/algebra/group_power/basic.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* bit0_smul_one
- \+ *lemma* bit0_smul_bit0
- \+ *lemma* bit0_smul_bit1
- \+ *lemma* bit1_smul_one
- \+ *lemma* bit1_smul_bit0
- \+ *lemma* bit1_smul_bit1



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
- \+ *lemma* strict_mono_incr_on.inj_on
- \+ *lemma* strict_mono_decr_on.inj_on

Modified src/order/basic.lean
- \+/\- *lemma* dual_le
- \+/\- *lemma* dual_lt
- \+ *lemma* dual_compares
- \+/\- *lemma* le_iff_le
- \+/\- *lemma* lt_iff_lt
- \+/\- *lemma* injective
- \+ *lemma* subtype.mk_le_mk
- \+ *lemma* subtype.mk_lt_mk
- \+ *lemma* subtype.coe_le_coe
- \+ *lemma* subtype.coe_lt_coe
- \- *theorem* compares
- \+/\- *def* order_dual

Modified src/order/rel_iso.lean
- \+ *lemma* coe_to_order_embedding
- \+ *def* to_order_embedding



## [2020-09-30 09:51:46](https://github.com/leanprover-community/mathlib/commit/e1c0b0a)
feat(ring_theory/jacobson): Integral extension of Jacobson rings are Jacobson ([#4304](https://github.com/leanprover-community/mathlib/pull/4304))
Main statement given by `is_jacobson_of_is_integral `
#### Estimated changes
Modified src/ring_theory/ideal/over.lean
- \+ *lemma* eq_bot_of_comap_eq_bot
- \+ *lemma* exists_ideal_over_maximal_of_is_integral

Modified src/ring_theory/jacobson.lean
- \+ *lemma* is_jacobson_of_is_integral

Modified src/ring_theory/jacobson_ideal.lean
- \+ *lemma* comap_jacobson



## [2020-09-30 09:51:44](https://github.com/leanprover-community/mathlib/commit/ff66d92)
chore(category_theory/limits): facts about opposites of limit cones ([#4250](https://github.com/leanprover-community/mathlib/pull/4250))
Simple facts about limit cones and opposite categories.
#### Estimated changes
Modified src/category_theory/adjunction/opposites.lean


Modified src/category_theory/limits/cones.lean
- \+ *def* cocone.op
- \+ *def* cone.op
- \+ *def* cocone.unop
- \+ *def* cone.unop
- \+ *def* cocone_equivalence_op_cone_op
- \+ *def* map_cone_op
- \+ *def* map_cocone_op

Modified src/category_theory/limits/limits.lean
- \+ *def* is_limit.op
- \+ *def* is_colimit.op
- \+ *def* is_limit.unop
- \+ *def* is_colimit.unop
- \+ *def* is_limit_equiv_is_colimit_op
- \+ *def* is_colimit_equiv_is_limit_op

Modified src/category_theory/monad/equiv_mon.lean
- \+ *def* counit_iso
- \+ *def* unit_iso_hom
- \+ *def* unit_iso_inv
- \+ *def* unit_iso
- \- *def* of_to_mon_end_iso
- \- *def* to_of_mon_end_iso

Modified src/category_theory/opposites.lean
- \+/\- *lemma* unop_id
- \+ *lemma* remove_op_id
- \+ *lemma* remove_left_op_app
- \+ *lemma* remove_op_hom
- \+ *lemma* remove_op_inv
- \+/\- *lemma* unop_hom
- \+/\- *lemma* unop_inv
- \- *lemma* right_op_app
- \+ *def* op_hom
- \+ *def* op_inv
- \+ *def* op
- \+ *def* unop

Modified src/data/opposite.lean




## [2020-09-30 07:56:48](https://github.com/leanprover-community/mathlib/commit/da66bb8)
feat(*): preparations for roots of unity ([#4322](https://github.com/leanprover-community/mathlib/pull/4322))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* is_unit_of_pow_eq_one

Modified src/data/int/gcd.lean
- \+ *lemma* pow_gcd_eq_one

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* mem_nth_roots
- \+ *lemma* nth_roots_zero
- \+/\- *lemma* card_nth_roots
- \+/\- *def* nth_roots

Modified src/group_theory/order_of_element.lean




## [2020-09-29 14:16:59](https://github.com/leanprover-community/mathlib/commit/743f82c)
feat(algebra/pointwise): Add missing to_additive on finset lemmas ([#4306](https://github.com/leanprover-community/mathlib/pull/4306))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* add_card_le



## [2020-09-29 12:11:48](https://github.com/leanprover-community/mathlib/commit/669a349)
feat(data/prod): mk injective lemmas ([#4319](https://github.com/leanprover-community/mathlib/pull/4319))
More scattered lemmmas from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* mk.inj_left
- \+ *lemma* mk.inj_right



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
- \+ *lemma* measurable_exp
- \+ *lemma* measurable.cexp
- \+ *lemma* measurable.exp
- \+/\- *lemma* continuous_log'
- \+ *lemma* measurable_log
- \+ *lemma* measurable.log

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* measurable_sin
- \+ *lemma* measurable_cos
- \+ *lemma* measurable_sinh
- \+ *lemma* measurable_cosh
- \+ *lemma* measurable.ccos
- \+ *lemma* measurable.csin
- \+ *lemma* measurable.ccosh
- \+ *lemma* measurable.csinh
- \+ *lemma* measurable.cos
- \+ *lemma* measurable.sin
- \+ *lemma* measurable.cosh
- \+ *lemma* measurable.sinh

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable_of_measurable_nnreal_prod
- \+ *lemma* measurable_to_real
- \+ *lemma* measurable_mul
- \+ *lemma* measurable_sub
- \+/\- *lemma* measurable.ennreal_mul
- \+/\- *lemma* measurable.ennreal_sub
- \- *lemma* measurable_ennreal_to_real

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_const



## [2020-09-29 12:11:41](https://github.com/leanprover-community/mathlib/commit/744e067)
feat(linear_algebra/dual): transpose of linear maps ([#4302](https://github.com/leanprover-community/mathlib/pull/4302))
This is filling an easy hole from the undergrad curriculum page: the transpose of a linear map. We don't prove much about it but at least we make contact with matrix transpose.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/basic.lean
- \+ *lemma* arrow_congr_symm_apply

Modified src/linear_algebra/dual.lean
- \+ *lemma* transpose_apply
- \+ *lemma* transpose_comp
- \+ *lemma* to_dual_total_left
- \+ *lemma* to_dual_total_right
- \+ *lemma* to_dual_apply_left
- \+ *lemma* to_dual_apply_right
- \+ *lemma* to_dual_eq_equiv_fun
- \+ *lemma* dual_basis_apply_self
- \+ *lemma* total_dual_basis
- \+ *lemma* dual_basis_repr
- \+ *lemma* dual_basis_equiv_fun
- \+ *lemma* dual_basis_apply
- \+ *def* transpose

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_equiv_matrix'_symm_apply
- \+ *lemma* linear_equiv_matrix_symm_apply
- \+ *lemma* linear_equiv_matrix_transpose
- \+ *lemma* linear_equiv_matrix_symm_transpose



## [2020-09-29 10:59:46](https://github.com/leanprover-community/mathlib/commit/a5a7a75)
feat(analysis/normed_space): define `normed_comm_ring` ([#4291](https://github.com/leanprover-community/mathlib/pull/4291))
Also use section `variables`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+/\- *lemma* ring_hom.map_fpow

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* monoid_hom.map_fpow

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_mul
- \+/\- *lemma* norm_one
- \+/\- *lemma* nnnorm_one
- \+/\- *lemma* norm_pow
- \+/\- *lemma* norm_prod
- \+/\- *lemma* norm_div
- \+/\- *lemma* norm_inv
- \+/\- *lemma* nnnorm_inv
- \+/\- *lemma* norm_fpow
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* continuous_on_inv
- \+/\- *lemma* exists_one_lt_norm
- \+/\- *lemma* exists_norm_lt_one
- \+/\- *lemma* exists_lt_norm
- \+/\- *lemma* exists_norm_lt
- \+/\- *lemma* punctured_nhds_ne_bot
- \+/\- *lemma* nhds_within_is_unit_ne_bot
- \+ *def* norm_hom



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


Created src/algebra/quandle.lean
- \+ *lemma* self_distrib
- \+ *lemma* act_apply
- \+ *lemma* act_symm_apply
- \+ *lemma* inv_act_apply
- \+ *lemma* inv_act_act_eq
- \+ *lemma* act_inv_act_eq
- \+ *lemma* left_cancel
- \+ *lemma* left_cancel_inv
- \+ *lemma* self_distrib_inv
- \+ *lemma* ad_conj
- \+ *lemma* op_act_op_eq
- \+ *lemma* op_inv_act_op_eq
- \+ *lemma* self_act_act_eq
- \+ *lemma* self_inv_act_inv_act_eq
- \+ *lemma* self_act_inv_act_eq
- \+ *lemma* self_inv_act_act_eq
- \+ *lemma* self_act_eq_iff_eq
- \+ *lemma* self_inv_act_eq_iff_eq
- \+ *lemma* involutory_inv_act_eq_act
- \+ *lemma* assoc_iff_id
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_act
- \+ *lemma* comp_apply
- \+ *lemma* fix_inv
- \+ *lemma* conj_act_eq_conj
- \+ *lemma* conj_swap
- \+ *lemma* dihedral_act.inv
- \+ *lemma* pre_envel_group_rel'.rel
- \+ *lemma* pre_envel_group_rel.refl
- \+ *lemma* pre_envel_group_rel.symm
- \+ *lemma* pre_envel_group_rel.trans
- \+ *lemma* well_def
- \+ *lemma* to_envel_group.univ
- \+ *lemma* to_envel_group.univ_uniq
- \+ *lemma* envel_action_prop
- \+ *def* act
- \+ *def* self_apply_equiv
- \+ *def* is_involutory
- \+ *def* is_abelian
- \+ *def* id
- \+ *def* comp
- \+ *def* conj
- \+ *def* conj.map
- \+ *def* dihedral
- \+ *def* dihedral_act
- \+ *def* to_conj
- \+ *def* envel_group
- \+ *def* to_envel_group
- \+ *def* to_envel_group.map_aux
- \+ *def* to_envel_group.map
- \+ *def* envel_action

Modified src/data/equiv/mul_add.lean
- \+ *lemma* to_equiv_apply
- \+ *lemma* conj_inv_apply



## [2020-09-29 04:58:27](https://github.com/leanprover-community/mathlib/commit/0bb5e5d)
feat(ring_theory/algebra_tower): Artin--Tate lemma ([#4282](https://github.com/leanprover-community/mathlib/pull/4282))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* map_span

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* mem_span_finset

Modified src/ring_theory/adjoin.lean
- \+ *lemma* adjoin_image
- \+ *lemma* fg_adjoin_finset
- \+ *lemma* fg_of_submodule_fg
- \+ *lemma* fg_map
- \+ *lemma* fg_of_fg_map
- \+ *lemma* fg_top

Modified src/ring_theory/algebra.lean
- \+ *lemma* coe_val
- \+ *lemma* map_mono
- \+ *lemma* map_injective
- \+ *lemma* range_val

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* algebra.fg_trans'
- \+ *lemma* exists_subalgebra_of_fg
- \+/\- *theorem* of_algebra_map_eq
- \+/\- *theorem* aeval_apply
- \+ *theorem* fg_of_fg_of_fg

Modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_of_fg_map
- \+ *lemma* fg_top
- \+ *lemma* fg_of_linear_equiv
- \+ *lemma* is_noetherian_of_injective
- \+ *lemma* fg_of_injective
- \+ *lemma* is_noetherian_of_fg_of_noetherian'
- \+/\- *theorem* fg_of_fg_map_of_fg_inf_ker



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
- \+ *lemma* continuous_within_at_singleton
- \+ *lemma* continuous_within_at.diff_iff
- \+ *lemma* continuous_within_at_diff_self



## [2020-09-28 17:22:18](https://github.com/leanprover-community/mathlib/commit/89d8cc3)
refactor(data/nat/basic): review API of `nat.find_greatest` ([#4274](https://github.com/leanprover-community/mathlib/pull/4274))
Other changes:
* add `nat.find_eq_iff`;
* use weaker assumptions in `measurable_to_encodable` and `measurable_to_nat`;
* add `measurable_find`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* find_eq_iff
- \+/\- *lemma* find_eq_zero
- \+ *lemma* find_greatest_eq_iff
- \+ *lemma* find_greatest_eq_zero_iff
- \+/\- *lemma* find_greatest_spec
- \+/\- *lemma* find_greatest_le
- \+/\- *lemma* le_find_greatest
- \+/\- *lemma* find_greatest_is_greatest
- \+/\- *lemma* find_greatest_of_ne_zero
- \- *lemma* find_greatest_spec_and_le
- \- *lemma* find_greatest_eq_zero

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+ *lemma* measurable_find



## [2020-09-28 15:25:45](https://github.com/leanprover-community/mathlib/commit/50dbce9)
fix(data/list/basic): Ensure that ball_cons actually works as a simp lemma ([#4281](https://github.com/leanprover-community/mathlib/pull/4281))
The LHS of the simp lemma `list.ball_cons` (aka `list.forall_mem_cons`) is not in simp-normal form, as `list.mem_cons_iff` rewrites it.
This adds a new simp lemma which is the form that `list.mem_cons_iff` rewrites it to.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *theorem* forall_mem_cons'

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
- \+ *lemma* constant_coeff_comp_C
- \+ *lemma* constant_coeff_comp_algebra_map

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* constant_coeff_rename



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
- \+ *lemma* mem_altitude
- \+ *lemma* direction_altitude
- \+ *lemma* vector_span_le_altitude_direction_orthogonal
- \+ *lemma* findim_direction_altitude
- \+ *lemma* affine_span_insert_singleton_eq_altitude_iff
- \+ *lemma* affine_span_orthocenter_point_le_altitude
- \+ *lemma* altitude_replace_orthocenter_eq_affine_span
- \+ *lemma* orthocenter_replace_orthocenter_eq_point



## [2020-09-28 11:21:24](https://github.com/leanprover-community/mathlib/commit/7bbb759)
chore(algebra/free_algebra): Make the second type argument to lift and ι implicit ([#4299](https://github.com/leanprover-community/mathlib/pull/4299))
These can always be inferred by the context, and just make things longer.
This is consistent with how the type argument for `id` is implicit.
The changes are applied to downstream uses too.
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+/\- *lemma* quot_mk_eq_ι

Modified src/algebra/lie/universal_enveloping.lean
- \+/\- *lemma* lift_ι_apply
- \+/\- *lemma* ι_comp_lift

Modified src/linear_algebra/tensor_algebra.lean




## [2020-09-28 11:21:22](https://github.com/leanprover-community/mathlib/commit/ad680c2)
chore(algebra/ordered_ring): remove duplicate lemma ([#4295](https://github.com/leanprover-community/mathlib/pull/4295))
`ordered_ring.two_pos` and `ordered_ring.zero_lt_two` had ended up identical. I kept `zero_lt_two`.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean


Modified src/algebra/ordered_field.lean
- \+/\- *lemma* half_pos

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* zero_lt_two
- \+ *lemma* zero_lt_four
- \- *lemma* two_pos
- \- *lemma* four_pos

Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_two

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* zero_lt_two
- \+/\- *lemma* two_ne_zero
- \- *lemma* two_pos

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
- \+/\- *def* lie_module.of_endo_morphism
- \+/\- *def* lie_ideal_subalgebra

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
- \+/\- *lemma* filter_mem_eq_inter

Modified src/data/fintype/basic.lean
- \+ *lemma* mem_compl
- \+ *lemma* coe_compl

Modified src/data/fintype/card.lean
- \+ *lemma* equiv.prod_comp
- \+/\- *lemma* fin.prod_univ_eq_prod_range
- \+/\- *lemma* finset.prod_fin_eq_prod_range
- \+ *lemma* fintype.prod_dite
- \- *lemma* finset.prod_range_eq_prod_fin
- \- *lemma* finset.prod_equiv

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

Created src/data/finset/gcd.lean
- \+ *lemma* lcm_def
- \+ *lemma* lcm_empty
- \+ *lemma* lcm_dvd_iff
- \+ *lemma* lcm_dvd
- \+ *lemma* dvd_lcm
- \+ *lemma* lcm_insert
- \+ *lemma* lcm_singleton
- \+ *lemma* normalize_lcm
- \+ *lemma* lcm_union
- \+ *lemma* lcm_mono_fun
- \+ *lemma* lcm_mono
- \+ *lemma* gcd_def
- \+ *lemma* gcd_empty
- \+ *lemma* dvd_gcd_iff
- \+ *lemma* gcd_dvd
- \+ *lemma* dvd_gcd
- \+ *lemma* gcd_insert
- \+ *lemma* gcd_singleton
- \+ *lemma* normalize_gcd
- \+ *lemma* gcd_union
- \+ *lemma* gcd_mono_fun
- \+ *lemma* gcd_mono
- \+ *theorem* lcm_congr
- \+ *theorem* gcd_congr
- \+ *def* lcm
- \+ *def* gcd

Modified src/data/finset/lattice.lean


Created src/data/multiset/gcd.lean
- \+ *lemma* lcm_zero
- \+ *lemma* lcm_cons
- \+ *lemma* lcm_singleton
- \+ *lemma* lcm_add
- \+ *lemma* lcm_dvd
- \+ *lemma* dvd_lcm
- \+ *lemma* lcm_mono
- \+ *lemma* normalize_lcm
- \+ *lemma* lcm_erase_dup
- \+ *lemma* lcm_ndunion
- \+ *lemma* lcm_union
- \+ *lemma* lcm_ndinsert
- \+ *lemma* gcd_zero
- \+ *lemma* gcd_cons
- \+ *lemma* gcd_singleton
- \+ *lemma* gcd_add
- \+ *lemma* dvd_gcd
- \+ *lemma* gcd_dvd
- \+ *lemma* gcd_mono
- \+ *lemma* normalize_gcd
- \+ *lemma* gcd_erase_dup
- \+ *lemma* gcd_ndunion
- \+ *lemma* gcd_union
- \+ *lemma* gcd_ndinsert
- \+ *def* lcm
- \+ *def* gcd



## [2020-09-28 04:20:18](https://github.com/leanprover-community/mathlib/commit/1761822)
chore(category_theory/limits): some limit lemmas ([#4238](https://github.com/leanprover-community/mathlib/pull/4238))
A couple of lemmas characterising definitions which are already there (the first part of [#4163](https://github.com/leanprover-community/mathlib/pull/4163))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* map_π
- \+ *lemma* lift_comp_cone_point_unique_up_to_iso_hom
- \+ *lemma* lift_comp_cone_point_unique_up_to_iso_inv
- \+ *lemma* of_iso_limit_lift
- \+ *lemma* equiv_iso_limit_apply
- \+ *lemma* equiv_iso_limit_symm_apply
- \+ *lemma* cone_points_iso_of_nat_iso_hom_comp
- \+ *lemma* cone_points_iso_of_nat_iso_inv_comp
- \+ *lemma* lift_comp_cone_points_iso_of_nat_iso_hom
- \+ *lemma* ι_map
- \+ *lemma* cocone_point_unique_up_to_iso_hom_desc
- \+ *lemma* cocone_point_unique_up_to_iso_inv_desc
- \+ *lemma* of_iso_colimit_desc
- \+ *lemma* equiv_iso_colimit_apply
- \+ *lemma* equiv_iso_colimit_symm_apply
- \+ *lemma* comp_cocone_points_iso_of_nat_iso_hom
- \+ *lemma* comp_cocone_points_iso_of_nat_iso_inv
- \+ *lemma* cocone_points_iso_of_nat_iso_hom_desc
- \+/\- *lemma* lim_map_π
- \+ *lemma* has_limit.lift_iso_of_nat_iso_hom
- \+/\- *lemma* ι_colim_map
- \+ *lemma* has_colimit.iso_of_nat_iso_hom_desc
- \- *lemma* is_limit_map_π
- \- *lemma* ι_is_colimit_map
- \+ *def* map
- \+ *def* equiv_iso_limit
- \+ *def* equiv_iso_colimit
- \+/\- *def* lim_map
- \+/\- *def* colim_map
- \- *def* is_limit.map
- \- *def* is_colimit.map

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
- \+/\- *lemma* is_maximal_comap_of_is_integral_of_is_maximal
- \+/\- *lemma* exists_ideal_over_prime_of_is_integral'
- \+/\- *theorem* exists_ideal_over_prime_of_is_integral

Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_integral_trans
- \+/\- *lemma* algebra.is_integral_trans
- \+/\- *lemma* is_integral_of_surjective
- \+/\- *lemma* is_integral_quotient_of_is_integral
- \+ *def* ring_hom.is_integral_elem
- \+ *def* ring_hom.is_integral
- \+ *def* algebra.is_integral

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
- \+ *lemma* ker_to_span_singleton

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_pi_system_is_open
- \+/\- *lemma* borel_eq_generate_Iio
- \+/\- *lemma* borel_eq_generate_Ioi
- \+ *lemma* measurable_of_is_open
- \+ *lemma* measurable_of_is_closed
- \+ *lemma* measurable_of_is_closed'
- \+/\- *lemma* is_measurable_le'
- \+/\- *lemma* is_measurable_le
- \+/\- *lemma* is_measurable_lt'
- \+/\- *lemma* is_measurable_lt
- \+/\- *lemma* is_measurable_interval
- \+/\- *lemma* measurable.max
- \+/\- *lemma* measurable.min
- \+ *lemma* measurable.mul'
- \+ *lemma* measurable_comp_iff_of_closed_embedding
- \+ *lemma* measurable_of_Iio
- \+ *lemma* measurable_of_Ioi
- \+ *lemma* measurable_of_Iic
- \+ *lemma* measurable_of_Ici
- \+/\- *lemma* measurable.is_lub
- \+/\- *lemma* measurable.is_glb
- \+/\- *lemma* measurable_supr
- \+/\- *lemma* measurable_infi
- \+/\- *lemma* measurable_bsupr
- \+/\- *lemma* measurable_binfi
- \+ *lemma* measurable_cSup
- \+ *lemma* measurable_inf_dist
- \+ *lemma* measurable.inf_dist
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable.dist
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable.nndist
- \+ *lemma* measurable_inf_edist
- \+ *lemma* measurable.inf_edist
- \+/\- *lemma* measurable_edist
- \+/\- *lemma* measurable.edist
- \+/\- *lemma* measurable.sub_nnreal
- \+/\- *lemma* measurable.nnreal_of_real
- \+ *lemma* nnreal.measurable_coe
- \+/\- *lemma* measurable.nnreal_coe
- \+/\- *lemma* measurable.ennreal_coe
- \+/\- *lemma* measurable.ennreal_of_real
- \+/\- *lemma* measurable_of_measurable_nnreal
- \+/\- *lemma* measurable_of_measurable_nnreal_nnreal
- \+ *lemma* measurable_to_nnreal
- \+ *lemma* measurable.to_nnreal
- \+ *lemma* measurable_ennreal_coe_iff
- \+ *lemma* measurable_ennreal_to_real
- \+ *lemma* measurable.to_real
- \+/\- *lemma* measurable.ennreal_mul
- \+/\- *lemma* measurable.ennreal_add
- \+/\- *lemma* measurable.ennreal_sub
- \+ *lemma* measurable.ennreal_tsum
- \+ *lemma* measurable_ennnorm
- \+ *lemma* measurable_smul_const

Modified src/measure_theory/giry_monad.lean
- \+ *lemma* measurable_measure

Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_prod
- \+ *lemma* measurable_prod_mk_left
- \+ *lemma* measurable_prod_mk_right
- \+ *lemma* measurable.of_uncurry_left
- \+ *lemma* measurable.of_uncurry_right
- \+ *lemma* measurable_swap
- \+ *lemma* measurable_swap_iff
- \+ *lemma* is_measurable_swap_iff

Modified src/measure_theory/set_integral.lean


Modified src/topology/algebra/module.lean


Modified src/topology/homeomorph.lean


Modified src/topology/maps.lean
- \+ *lemma* of_nonempty

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
- \+/\- *lemma* limsup_eq_infi_supr_of_nat
- \+/\- *lemma* limsup_eq_infi_supr_of_nat'
- \+/\- *lemma* liminf_eq_supr_infi_of_nat
- \+/\- *lemma* liminf_eq_supr_infi_of_nat'
- \+ *theorem* has_basis.Liminf_eq_supr_Inf
- \+/\- *theorem* Liminf_eq_supr_Inf
- \+ *theorem* has_basis.limsup_eq_infi_supr
- \+ *theorem* has_basis.liminf_eq_supr_infi

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
- \+/\- *lemma* nhds_list
- \+/\- *lemma* nhds_nil
- \+/\- *lemma* nhds_cons
- \+ *lemma* list.tendsto_cons
- \+ *lemma* filter.tendsto.cons
- \+ *lemma* continuous_cons
- \+/\- *lemma* tendsto_insert_nth
- \+ *lemma* tendsto_prod
- \+ *lemma* continuous_prod
- \+/\- *lemma* tendsto_cons
- \+/\- *lemma* continuous_insert_nth'
- \+/\- *lemma* continuous_insert_nth
- \+/\- *lemma* continuous_at_remove_nth
- \+/\- *lemma* continuous_remove_nth
- \- *lemma* tendsto_cons'

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* coe_inf_nndist
- \+ *lemma* lipschitz_inf_nndist_pt
- \+ *lemma* uniform_continuous_inf_nndist_pt
- \+ *lemma* continuous_inf_nndist_pt
- \+ *def* inf_nndist



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
- \- *lemma* C_dvd_iff_zmod

Modified src/field_theory/chevalley_warning.lean


Renamed src/field_theory/finite.lean to src/field_theory/finite/basic.lean
- \+ *lemma* frobenius_zmod

Created src/field_theory/finite/polynomial.lean
- \+ *lemma* C_dvd_iff_zmod
- \+ *lemma* frobenius_zmod
- \+ *lemma* expand_zmod
- \+ *lemma* eval_indicator_apply_eq_one
- \+ *lemma* eval_indicator_apply_eq_zero
- \+ *lemma* degrees_indicator
- \+ *lemma* indicator_mem_restrict_degree
- \+ *lemma* evalₗ_apply
- \+ *lemma* map_restrict_dom_evalₗ
- \+ *lemma* dim_R
- \+ *lemma* range_evalᵢ
- \+ *lemma* ker_evalₗ
- \+ *lemma* eq_zero_of_eval_eq_zero
- \+ *def* indicator
- \+ *def* evalₗ
- \+ *def* R
- \+ *def* evalᵢ

Modified src/field_theory/mv_polynomial.lean
- \- *lemma* eval_indicator_apply_eq_one
- \- *lemma* eval_indicator_apply_eq_zero
- \- *lemma* degrees_indicator
- \- *lemma* indicator_mem_restrict_degree
- \- *lemma* evalₗ_apply
- \- *lemma* map_restrict_dom_evalₗ
- \- *lemma* dim_R
- \- *lemma* range_evalᵢ
- \- *lemma* ker_evalₗ
- \- *lemma* eq_zero_of_eval_eq_zero
- \- *def* indicator
- \- *def* evalₗ
- \- *def* R
- \- *def* evalᵢ

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
- \+/\- *lemma* coe_ne_one
- \+/\- *lemma* one_ne_coe
- \+/\- *lemma* ne_one_iff_exists

Modified src/data/option/basic.lean
- \+/\- *lemma* ne_none_iff_exists
- \+/\- *lemma* ne_none_iff_exists'

Modified src/data/seq/seq.lean




## [2020-09-27 01:39:14](https://github.com/leanprover-community/mathlib/commit/5f6b07f)
chore(scripts): update nolints.txt ([#4283](https://github.com/leanprover-community/mathlib/pull/4283))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-27 00:33:40](https://github.com/leanprover-community/mathlib/commit/5c957ec)
feat(analysis/convex/integral): Jensen's inequality for integrals ([#4225](https://github.com/leanprover-community/mathlib/pull/4225))
#### Estimated changes
Created src/analysis/convex/integral.lean
- \+ *lemma* convex.smul_integral_mem
- \+ *lemma* convex.integral_mem
- \+ *lemma* convex_on.map_smul_integral_le
- \+ *lemma* convex_on.map_integral_le

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* prod.nnnorm_def

Modified src/measure_theory/integration.lean
- \+ *lemma* sum_range_measure_preimage_singleton

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.prod_mk

Modified src/measure_theory/measure_space.lean
- \+ *lemma* probability_measure.ne_zero

Modified src/measure_theory/set_integral.lean
- \+ *lemma* fst_integral
- \+ *lemma* snd_integral
- \+ *lemma* integral_pair



## [2020-09-26 20:43:15](https://github.com/leanprover-community/mathlib/commit/8600cb0)
feat(measure_space): define sigma finite measures ([#4265](https://github.com/leanprover-community/mathlib/pull/4265))
They are defined as a `Prop`. The noncomputable "eliminator" is called `spanning_sets`, and satisfies monotonicity, even though that is not required to give a `sigma_finite` instance.
I define a helper function `accumulate s := ⋃ y ≤ x, s y`. This is helpful, to separate out some monotonicity proofs. It is in its own file purely for import reasons (there is no good file to put it that imports both `set.lattice` and `finset.basic`, the latter is used in 1 lemma).
#### Estimated changes
Created src/data/set/accumulate.lean
- \+ *lemma* accumulate_def
- \+ *lemma* mem_accumulate
- \+ *lemma* subset_accumulate
- \+ *lemma* monotone_accumulate
- \+ *lemma* bUnion_accumulate
- \+ *lemma* Union_accumulate
- \+ *def* accumulate

Modified src/data/set/lattice.lean
- \+ *lemma* Union_prod_of_monotone
- \+ *lemma* image2_eq_seq
- \+/\- *theorem* monotone_prod

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_bUnion_lt_top
- \+ *lemma* exists_finite_spanning_sets
- \+ *lemma* monotone_spanning_sets
- \+ *lemma* is_measurable_spanning_sets
- \+ *lemma* measure_spanning_sets_lt_top
- \+ *lemma* Union_spanning_sets
- \+ *lemma* supr_restrict_spanning_sets
- \+ *def* spanning_sets



## [2020-09-26 19:15:53](https://github.com/leanprover-community/mathlib/commit/253b120)
feat(field_theory): prove primitive element theorem ([#4153](https://github.com/leanprover-community/mathlib/pull/4153))
Proof of the primitive element theorem. The main proof is in `field_theory/primitive_element.lean`. Some lemmas we used have been added to other files. We have also changed the notation for adjoining an element to a field to be easier to use.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* eval₂_gcd_eq_zero
- \+ *lemma* eval_gcd_eq_zero
- \+ *lemma* root_left_of_root_gcd
- \+ *lemma* root_right_of_root_gcd
- \+ *lemma* root_gcd_iff_root_left_right
- \+ *lemma* is_root_gcd_iff_is_root_left_right
- \+ *lemma* mem_roots_map

Modified src/deprecated/subfield.lean
- \+ *lemma* is_subfield.pow_mem

Modified src/field_theory/adjoin.lean
- \+ *lemma* adjoin_eq_range_algebra_map_adjoin
- \+ *lemma* adjoin_adjoin_comm
- \+/\- *lemma* adjoin_simple.algebra_map_gen
- \+/\- *lemma* adjoin_simple_adjoin_simple
- \+ *lemma* adjoin_simple_comm
- \+ *lemma* adjoin_eq_bot
- \+ *lemma* adjoin_simple_eq_bot
- \+ *lemma* adjoin_zero
- \+ *lemma* adjoin_one
- \+ *lemma* sub_bot_of_adjoin_sub_bot
- \+ *lemma* mem_bot_of_adjoin_simple_sub_bot
- \+ *lemma* adjoin_eq_bot_iff
- \+ *lemma* adjoin_simple_eq_bot_iff
- \+ *lemma* sub_bot_of_adjoin_dim_eq_one
- \+ *lemma* mem_bot_of_adjoin_simple_dim_eq_one
- \+ *lemma* adjoin_dim_eq_one_of_sub_bot
- \+ *lemma* adjoin_simple_dim_eq_one_of_mem_bot
- \+ *lemma* adjoin_dim_eq_one_iff
- \+ *lemma* adjoin_simple_dim_eq_one_iff
- \+ *lemma* adjoin_findim_eq_one_iff
- \+ *lemma* adjoin_simple_findim_eq_one_iff
- \+ *lemma* bot_eq_top_of_dim_adjoin_eq_one
- \+ *lemma* bot_eq_top_of_findim_adjoin_eq_one
- \+ *lemma* bot_eq_top_of_findim_adjoin_le_one
- \- *lemma* adjoin_singleton

Modified src/field_theory/minimal_polynomial.lean
- \+ *lemma* dvd_map_of_is_scalar_tower

Created src/field_theory/primitive_element.lean
- \+ *lemma* exists_primitive_element_of_fintype_top
- \+ *lemma* primitive_element_inf_aux_exists_c
- \+ *lemma* primitive_element_inf_aux
- \+ *theorem* exists_primitive_element_of_fintype_bot
- \+ *theorem* exists_primitive_element_inf
- \+ *theorem* exists_primitive_element_aux
- \+ *theorem* exists_primitive_element

Modified src/field_theory/separable.lean
- \+ *lemma* separable_gcd_left
- \+ *lemma* separable_gcd_right
- \+ *lemma* eq_X_sub_C_of_separable_of_root_eq
- \+ *lemma* is_separable_tower_top_of_is_separable
- \+ *lemma* is_separable_tower_bot_of_is_separable

Modified src/field_theory/splitting_field.lean
- \+ *lemma* splits_of_splits_gcd_left
- \+ *lemma* splits_of_splits_gcd_right
- \+ *lemma* eq_X_sub_C_of_splits_of_single_root

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional_of_dim_eq_one
- \+ *lemma* subalgebra.dim_eq_one_of_eq_bot
- \+ *lemma* subalgebra.dim_bot
- \+ *lemma* subalgebra_top_dim_eq_submodule_top_dim
- \+ *lemma* subalgebra_top_findim_eq_submodule_top_findim
- \+ *lemma* subalgebra.dim_top
- \+ *lemma* subalgebra.finite_dimensional_bot
- \+ *lemma* subalgebra.findim_bot
- \+ *lemma* subalgebra.findim_eq_one_of_eq_bot
- \+ *lemma* subalgebra.eq_bot_of_findim_one
- \+ *lemma* subalgebra.eq_bot_of_dim_one
- \+ *lemma* subalgebra.bot_eq_top_of_dim_eq_one
- \+ *lemma* subalgebra.bot_eq_top_of_findim_eq_one
- \+/\- *theorem* findim_top
- \+ *theorem* subalgebra.dim_eq_one_iff
- \+ *theorem* subalgebra.findim_eq_one_iff

Modified src/ring_theory/algebra.lean
- \+ *theorem* coe_bot

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* algebra_map_aeval
- \+ *lemma* aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+ *lemma* aeval_eq_zero_of_aeval_algebra_map_eq_zero_field

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
- \+ *lemma* coe_to_linear_map
- \+ *lemma* morphism.ext

Created src/algebra/universal_enveloping_algebra.lean
- \+ *lemma* lift_ι_apply
- \+ *lemma* ι_comp_lift
- \+ *lemma* lift_unique
- \+ *lemma* hom_ext
- \+ *def* universal_enveloping_algebra
- \+ *def* mk_alg_hom
- \+ *def* ι
- \+ *def* lift

Modified src/linear_algebra/tensor_algebra.lean


Modified src/ring_theory/algebra.lean




## [2020-09-26 17:53:17](https://github.com/leanprover-community/mathlib/commit/3ebee15)
feat(src/data/polynomial/ring_division.lean): eq_zero_of_infinite_is_root ([#4280](https://github.com/leanprover-community/mathlib/pull/4280))
add a lemma stating that a polynomial is zero if it has infinitely many roots.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* eq_zero_of_infinite_is_root
- \+ *lemma* eq_of_infinite_eval_eq



## [2020-09-26 17:53:15](https://github.com/leanprover-community/mathlib/commit/376ab30)
feat(data/nat/unique_factorization): a `unique_factorization_monoid` instance on N ([#4194](https://github.com/leanprover-community/mathlib/pull/4194))
Provides a `unique_factorization_monoid` instance on `nat`
Shows its equivalence to `nat.factors`, which is list-valued
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* associated_iff_eq
- \+ *theorem* associated_eq_eq

Created src/data/nat/associated.lean
- \+ *theorem* nat.prime_iff
- \+ *theorem* nat.irreducible_iff_prime

Created src/data/nat/unique_factorization.lean
- \+ *theorem* nat.factors_eq



## [2020-09-26 15:49:19](https://github.com/leanprover-community/mathlib/commit/88e198a)
feat(data/multiset): count repeat lemma ([#4278](https://github.com/leanprover-community/mathlib/pull/4278))
A small lemma and renaming (of `count_repeat` to `count_repeat_self`) to count elements in a `multiset.repeat`. One part of [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* count_repeat_self
- \+/\- *theorem* count_repeat



## [2020-09-26 15:49:16](https://github.com/leanprover-community/mathlib/commit/8e83805)
chore(analysis/special_functions/pow): +2 lemmas about `nnreal.rpow` ([#4272](https://github.com/leanprover-community/mathlib/pull/4272))
`λ x, x^y` is continuous in more cases than `λ p, p.1^p.2`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* continuous_at_rpow_const
- \+ *lemma* continuous_rpow_const



## [2020-09-26 15:49:14](https://github.com/leanprover-community/mathlib/commit/3177493)
feat(ring_theory/algebra, algebra/module): Add add_comm_monoid_to_add_comm_group and semiring_to_ring ([#4252](https://github.com/leanprover-community/mathlib/pull/4252))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *def* semimodule.add_comm_monoid_to_add_comm_group

Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/algebra.lean
- \+/\- *lemma* mul_sub_algebra_map_commutes
- \+/\- *lemma* mul_sub_algebra_map_pow_commutes
- \+ *def* semiring_to_ring



## [2020-09-26 15:49:13](https://github.com/leanprover-community/mathlib/commit/7c0c16c)
feat(data/list/basic): Add lemmas about inits and tails ([#4222](https://github.com/leanprover-community/mathlib/pull/4222))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* inits_cons
- \+ *lemma* tails_cons
- \+ *lemma* inits_append
- \+ *lemma* tails_append
- \+ *lemma* inits_eq_tails
- \+ *lemma* tails_eq_inits
- \+ *lemma* inits_reverse
- \+ *lemma* tails_reverse
- \+ *lemma* map_reverse_inits
- \+ *lemma* map_reverse_tails
- \+ *theorem* reverse_involutive

Modified src/data/list/zip.lean
- \+ *lemma* mem_zip_inits_tails

Modified src/logic/function/basic.lean
- \+ *lemma* comp_self



## [2020-09-26 13:57:50](https://github.com/leanprover-community/mathlib/commit/bc3a6cf)
chore(data/list/basic): Make it clear that `forall_mem_cons` and `ball_cons` are synonyms ([#4279](https://github.com/leanprover-community/mathlib/pull/4279))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* forall_mem_cons



## [2020-09-26 12:12:06](https://github.com/leanprover-community/mathlib/commit/9b09f90)
feat(ennreal): some lemmas about ennreal ([#4262](https://github.com/leanprover-community/mathlib/pull/4262))
Also some lemmas about norms in (e)nnreal.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_of_nonneg
- \+ *lemma* nnnorm_coe_eq_self
- \+ *lemma* nnnorm_of_nonneg
- \+ *lemma* ennnorm_eq_of_real
- \+/\- *def* nnnorm

Modified src/data/real/ennreal.lean
- \+ *lemma* mul_lt_top_iff
- \+ *lemma* of_real_le_of_le_to_real

Modified src/measure_theory/borel_space.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* continuous_coe
- \+ *lemma* continuous_coe_iff



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


Created src/order/filter/archimedean.lean
- \+ *lemma* tendsto_coe_nat_at_top_iff
- \+ *lemma* tendsto_coe_nat_at_top_at_top
- \+ *lemma* tendsto_coe_int_at_top_iff
- \+ *lemma* tendsto_coe_int_at_top_at_top
- \+ *lemma* tendsto_coe_rat_at_top_iff

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* tendsto_at_top_embedding
- \+/\- *lemma* tendsto_at_bot_embedding

Modified src/topology/instances/real.lean
- \- *lemma* tendsto_coe_nat_real_at_top_iff
- \- *lemma* tendsto_coe_nat_real_at_top_at_top
- \- *lemma* tendsto_coe_int_real_at_top_iff
- \- *lemma* tendsto_coe_int_real_at_top_at_top



## [2020-09-26 10:16:10](https://github.com/leanprover-community/mathlib/commit/aa11589)
feat(algebra/homology, category_theory/abelian): expand API on exactness ([#4256](https://github.com/leanprover-community/mathlib/pull/4256))
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* exact_comp_hom_inv_comp
- \+ *lemma* exact_comp_hom_inv_comp_iff
- \+ *lemma* exact_epi_comp
- \+ *lemma* exact_comp_mono
- \+ *lemma* exact_kernel
- \+ *lemma* kernel_ι_eq_zero_of_exact_zero_left
- \+ *lemma* exact_zero_left_of_mono
- \- *lemma* exact.w_assoc

Modified src/algebra/homology/image_to_kernel_map.lean
- \+ *lemma* image_to_kernel_map_comp_right
- \+ *lemma* image_to_kernel_map_comp_left
- \+ *lemma* image_to_kernel_map_comp_hom_inv_comp
- \+/\- *lemma* image_to_kernel_map_epi_of_zero_of_mono
- \+/\- *lemma* image_to_kernel_map_epi_of_epi_of_zero

Modified src/category_theory/abelian/basic.lean
- \+ *lemma* mono_of_zero_kernel
- \+ *lemma* mono_of_kernel_ι_eq_zero
- \+ *lemma* epi_of_zero_cokernel
- \+ *lemma* epi_of_cokernel_π_eq_zero

Modified src/category_theory/abelian/exact.lean
- \+ *lemma* exact_cokernel
- \+ *lemma* tfae_mono
- \+ *lemma* mono_iff_exact_zero_left
- \+ *lemma* mono_iff_kernel_ι_eq_zero
- \+ *lemma* tfae_epi
- \+ *lemma* epi_iff_exact_zero_right
- \+ *lemma* epi_iff_cokernel_π_eq_zero

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.post_comp_is_iso_hom_comp_image_ι
- \+ *lemma* image.post_comp_is_iso_inv_comp_image_ι
- \+ *def* image.post_comp_is_iso

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-09-26 10:16:08](https://github.com/leanprover-community/mathlib/commit/61897ae)
feat(data/set/intervals/infinite): intervals are infinite ([#4241](https://github.com/leanprover-community/mathlib/pull/4241))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.exists_minimal
- \+ *lemma* finset.exists_maximal

Modified src/data/set/finite.lean
- \+ *theorem* finite.to_finset.nonempty
- \+ *theorem* infinite_mono

Created src/data/set/intervals/infinite.lean
- \+ *lemma* Ioo.infinite
- \+ *lemma* Ico.infinite
- \+ *lemma* Ioc.infinite
- \+ *lemma* Icc.infinite
- \+ *lemma* Iio.infinite
- \+ *lemma* Iic.infinite
- \+ *lemma* Ioi.infinite
- \+ *lemma* Ici.infinite



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
- \+ *lemma* congr_app
- \+/\- *def* comp

Created src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+ *lemma* map_id_c_app
- \+ *lemma* map_comp_c_app
- \+ *lemma* desc_c_naturality
- \+ *def* pushforward_diagram_to_colimit
- \+ *def* colimit
- \+ *def* colimit_cocone
- \+ *def* desc_c_app
- \+ *def* colimit_cocone_is_colimit

Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* eq_to_hom_unop
- \+ *lemma* nat_trans.congr

Modified src/category_theory/grothendieck.lean
- \+ *lemma* id_fiber'
- \+ *lemma* congr

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/functor_category.lean
- \+ *lemma* limit.lift_π_app
- \+ *lemma* colimit.ι_desc_app
- \+ *lemma* limit_obj_iso_limit_comp_evaluation_hom_π
- \+ *lemma* limit_obj_iso_limit_comp_evaluation_inv_π_app
- \+ *lemma* limit_obj_ext
- \+ *lemma* colimit_obj_iso_colimit_comp_evaluation_ι_inv
- \+ *lemma* colimit_obj_iso_colimit_comp_evaluation_ι_app_hom
- \+ *lemma* colimit_obj_ext
- \+ *def* limit_obj_iso_limit_comp_evaluation
- \+ *def* colimit_obj_iso_colimit_comp_evaluation

Modified src/category_theory/limits/limits.lean
- \+ *lemma* limit.lift_cone
- \+ *lemma* colimit.desc_cocone

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* limit.w_apply
- \+ *lemma* limit.lift_π_apply
- \+ *lemma* limit.map_π_apply
- \+ *lemma* colimit.w_apply
- \+ *lemma* colimit.ι_desc_apply
- \+ *lemma* colimit.ι_map_apply
- \- *lemma* limit_w_apply
- \- *lemma* lift_π_apply
- \- *lemma* map_π_apply
- \- *lemma* colimit_w_apply
- \- *lemma* ι_desc_apply
- \- *lemma* ι_map_apply

Modified src/topology/category/Top/opens.lean
- \+ *lemma* map_comp_map
- \+/\- *def* map_id

Created src/topology/sheaves/limits.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/presheaf.lean
- \+ *lemma* pushforward_obj_obj
- \+ *lemma* pushforward_obj_map
- \+ *lemma* pushforward_eq_hom_app
- \+ *lemma* pushforward_eq_rfl
- \+ *def* pushforward_obj
- \+ *def* pushforward_map
- \- *def* pushforward

Modified src/topology/sheaves/stalks.lean




## [2020-09-26 07:58:50](https://github.com/leanprover-community/mathlib/commit/c2f896f)
feat(data/set): add some lemmas ([#4263](https://github.com/leanprover-community/mathlib/pull/4263))
Some lemmas about sets, mostly involving disjointness
I also sneaked in the lemma `(λ x : α, y) = const α y` which is useful to rewrite with.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* preimage_swap_prod

Modified src/data/set/lattice.lean
- \+ *lemma* preimage
- \+/\- *lemma* not_disjoint_iff
- \+/\- *lemma* disjoint_left
- \+ *lemma* univ_disjoint
- \+ *lemma* disjoint_univ
- \+ *lemma* preimage_eq_empty
- \+ *lemma* preimage_eq_empty_iff
- \- *lemma* disjoint.preimage
- \+ *theorem* union_left
- \+ *theorem* union_right
- \+/\- *theorem* disjoint_iff_inter_eq_empty
- \+/\- *theorem* disjoint_right
- \+/\- *theorem* disjoint_of_subset_left
- \+/\- *theorem* disjoint_of_subset_right
- \+/\- *theorem* disjoint_union_left
- \+/\- *theorem* disjoint_union_right
- \+/\- *theorem* disjoint_singleton_left
- \+/\- *theorem* disjoint_singleton_right
- \- *theorem* disjoint.union_left
- \- *theorem* disjoint.union_right

Modified src/logic/function/basic.lean
- \+ *lemma* const_def



## [2020-09-26 07:58:48](https://github.com/leanprover-community/mathlib/commit/1892724)
feat(data/matrix): definition of `block_diagonal` ([#4257](https://github.com/leanprover-community/mathlib/pull/4257))
This PR defines `matrix.block_diagonal : (o -> matrix m n R) -> matrix (m × o) (n × o) R`. The choice to put `o` on the right hand side of the product will help with relating this to `is_basis.smul`, but it won't be a huge hassle to write `matrix (o × m) (o × m) R` instead if you prefer.
I also tried making `m` and `n` depend on `o`, giving `block_diagonal M : matrix (Σ k : o, m k) (Σ k : o, n k) R`, but that turned out to be a shotcut to `eq.rec` hell.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_product_univ

Modified src/data/matrix/basic.lean
- \+ *lemma* block_diagonal_apply
- \+ *lemma* block_diagonal_apply_eq
- \+ *lemma* block_diagonal_apply_ne
- \+ *lemma* block_diagonal_transpose
- \+ *lemma* block_diagonal_zero
- \+ *lemma* block_diagonal_diagonal
- \+ *lemma* block_diagonal_one
- \+ *lemma* block_diagonal_add
- \+ *lemma* block_diagonal_neg
- \+ *lemma* block_diagonal_sub
- \+ *lemma* block_diagonal_mul
- \+ *lemma* block_diagonal_smul
- \+ *def* block_diagonal



## [2020-09-26 06:09:45](https://github.com/leanprover-community/mathlib/commit/7aef150)
feat(category_theory): sieves ([#3909](https://github.com/leanprover-community/mathlib/pull/3909))
Define sieves, from my topos project. Co-authored by @EdAyers. 
These definitions and lemmas have been battle-tested quite a bit so I'm reasonably confident they're workable.
#### Estimated changes
Created src/category_theory/sites/sieves.lean
- \+ *lemma* arrows_ext
- \+ *lemma* mem_Inf
- \+ *lemma* mem_Sup
- \+ *lemma* mem_inter
- \+ *lemma* mem_union
- \+ *lemma* mem_top
- \+ *lemma* sets_iff_generate
- \+ *lemma* mem_pullback
- \+ *lemma* pullback_top
- \+ *lemma* pullback_comp
- \+ *lemma* pullback_inter
- \+ *lemma* id_mem_iff_eq_top
- \+ *lemma* pullback_eq_top_iff_mem
- \+ *lemma* mem_pushforward_of_comp
- \+ *lemma* pushforward_comp
- \+ *lemma* galois_connection
- \+ *lemma* pullback_monotone
- \+ *lemma* pushforward_monotone
- \+ *lemma* le_pushforward_pullback
- \+ *lemma* pullback_pushforward_le
- \+ *lemma* pushforward_union
- \+ *lemma* nat_trans_of_le_comm
- \+ *def* set_over
- \+ *def* generate
- \+ *def* gi_generate
- \+ *def* pullback
- \+ *def* pushforward
- \+ *def* galois_coinsertion_of_mono
- \+ *def* galois_insertion_of_split_epi
- \+ *def* functor
- \+ *def* nat_trans_of_le
- \+ *def* functor_inclusion



## [2020-09-26 02:31:08](https://github.com/leanprover-community/mathlib/commit/6289adf)
fix(order/bounded_lattice): fix some misleading theorem names ([#4271](https://github.com/leanprover-community/mathlib/pull/4271))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+/\- *lemma* coe_lt_top
- \+ *theorem* le_none
- \+ *theorem* some_lt_none
- \- *theorem* none_le
- \- *theorem* none_lt_some



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
- \+ *lemma* zero_eq_one_iff
- \+ *lemma* one_eq_zero_iff



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
- \+/\- *lemma* vars_X

Created src/ring_theory/witt_vector/witt_polynomial.lean
- \+ *lemma* witt_polynomial_eq_sum_C_mul_X_pow
- \+ *lemma* map_witt_polynomial
- \+ *lemma* constant_coeff_witt_polynomial
- \+ *lemma* witt_polynomial_zero
- \+ *lemma* witt_polynomial_one
- \+ *lemma* aeval_witt_polynomial
- \+ *lemma* witt_polynomial_zmod_self
- \+ *lemma* witt_polynomial_vars
- \+ *lemma* witt_polynomial_vars_subset
- \+ *lemma* X_in_terms_of_W_eq
- \+ *lemma* constant_coeff_X_in_terms_of_W
- \+ *lemma* X_in_terms_of_W_zero
- \+ *lemma* X_in_terms_of_W_vars_aux
- \+ *lemma* X_in_terms_of_W_vars_subset
- \+ *lemma* X_in_terms_of_W_aux
- \+ *lemma* bind₁_X_in_terms_of_W_witt_polynomial
- \+ *lemma* bind₁_witt_polynomial_X_in_terms_of_W



## [2020-09-25 14:53:58](https://github.com/leanprover-community/mathlib/commit/565efec)
chore(data/real/ennreal): 3 lemmas stating `∞ / b = ∞` ([#4248](https://github.com/leanprover-community/mathlib/pull/4248))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* top_div_coe
- \+ *lemma* top_div_of_ne_top
- \+ *lemma* top_div_of_lt_top
- \+/\- *lemma* top_div



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
- \+/\- *lemma* ext
- \+ *lemma* coe_ring_hom_inj_iff

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.eq_univ_of_card
- \+ *lemma* card_le_of_injective
- \+ *lemma* card_eq_one_iff
- \+ *lemma* card_eq_zero_iff
- \+ *lemma* card_pos_iff
- \+ *lemma* card_le_one_iff
- \+ *lemma* card_le_one_iff_subsingleton
- \+ *lemma* one_lt_card_iff_nontrivial
- \+ *lemma* exists_ne_of_one_lt_card
- \+ *lemma* exists_pair_of_one_lt_card
- \+ *lemma* injective_iff_surjective
- \+ *lemma* injective_iff_bijective
- \+ *lemma* surjective_iff_bijective
- \+ *lemma* injective_iff_surjective_of_equiv
- \+ *lemma* nonempty_equiv_of_card_eq
- \+ *lemma* bijective_iff_injective_and_card
- \+ *lemma* bijective_iff_surjective_and_card
- \- *lemma* fintype.card_le_of_injective
- \- *lemma* fintype.card_eq_one_iff
- \- *lemma* fintype.card_eq_zero_iff
- \- *lemma* fintype.card_pos_iff
- \- *lemma* fintype.card_le_one_iff
- \- *lemma* fintype.card_le_one_iff_subsingleton
- \- *lemma* fintype.one_lt_card_iff_nontrivial
- \- *lemma* fintype.exists_ne_of_one_lt_card
- \- *lemma* fintype.exists_pair_of_one_lt_card
- \- *lemma* fintype.injective_iff_surjective
- \- *lemma* fintype.injective_iff_bijective
- \- *lemma* fintype.surjective_iff_bijective
- \- *lemma* fintype.injective_iff_surjective_of_equiv
- \+ *def* card_eq_zero_equiv_equiv_pempty
- \- *def* fintype.card_eq_zero_equiv_equiv_pempty

Modified src/data/zmod/basic.lean
- \+ *lemma* cast_hom_injective
- \+ *lemma* cast_hom_bijective
- \+ *lemma* ring_hom_surjective
- \+ *lemma* ring_hom_eq_of_ker_eq
- \- *lemma* zmod.ring_hom_surjective
- \- *lemma* zmod.ring_hom_eq_of_ker_eq



## [2020-09-25 14:53:54](https://github.com/leanprover-community/mathlib/commit/aee16bd)
feat(data/mv_polynomial/basic): counit ([#4205](https://github.com/leanprover-community/mathlib/pull/4205))
From the Witt vector project
#### Estimated changes
Created src/data/mv_polynomial/counit.lean
- \+ *lemma* acounit_X
- \+ *lemma* acounit_C
- \+ *lemma* acounit_surjective
- \+ *lemma* counit_surjective
- \+ *lemma* counit_nat_surjective
- \+ *lemma* counit_C
- \+ *lemma* counit_nat_C
- \+ *lemma* counit_X
- \+ *lemma* counit_nat_X



## [2020-09-25 14:53:52](https://github.com/leanprover-community/mathlib/commit/5deb96d)
feat(data/mv_polynomial/funext): function extensionality for polynomials ([#4196](https://github.com/leanprover-community/mathlib/pull/4196))
over infinite integral domains
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* trans_apply

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* C_injective
- \+/\- *lemma* C_inj

Modified src/data/mv_polynomial/equiv.lean
- \+ *lemma* fin_succ_equiv_eq
- \+ *lemma* fin_succ_equiv_apply

Created src/data/mv_polynomial/funext.lean
- \+ *lemma* funext
- \+ *lemma* funext_iff

Modified src/data/polynomial/monomial.lean


Modified src/data/polynomial/ring_division.lean
- \+ *lemma* zero_of_eval_zero
- \+ *lemma* funext

Modified src/logic/function/basic.lean
- \+ *lemma* extend_def
- \+ *lemma* extend_apply
- \+ *lemma* extend_comp
- \+ *def* extend



## [2020-09-25 12:54:20](https://github.com/leanprover-community/mathlib/commit/680f877)
feat(data/rat/basic): coe_int_div, coe_nat_div ([#4233](https://github.com/leanprover-community/mathlib/pull/4233))
Snippet from the Witt project
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* coe_int_div_self
- \+ *lemma* coe_nat_div_self
- \+ *lemma* coe_int_div
- \+ *lemma* coe_nat_div



## [2020-09-25 12:54:18](https://github.com/leanprover-community/mathlib/commit/9591d43)
feat(data/*): lemmas on division of polynomials by constant polynomials ([#4206](https://github.com/leanprover-community/mathlib/pull/4206))
From the Witt vector project
We provide a specialized version for polynomials over zmod n,
which turns out to be convenient in practice.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* C_dvd_iff_dvd_coeff
- \+ *lemma* C_dvd_iff_map_hom_eq_zero

Created src/data/zmod/polynomial.lean
- \+ *lemma* C_dvd_iff_zmod



## [2020-09-25 12:54:16](https://github.com/leanprover-community/mathlib/commit/c7d818c)
feat(data/mv_polynomial/variables): vars_bind₁ and friends ([#4204](https://github.com/leanprover-community/mathlib/pull/4204))
From the Witt vector project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/rename.lean
- \- *lemma* total_degree_rename_le

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* degrees_rename
- \+/\- *lemma* vars_monomial
- \+/\- *lemma* vars_C
- \+ *lemma* total_degree_rename_le
- \+/\- *lemma* eval₂_hom_eq_constant_coeff_of_vars
- \+/\- *lemma* aeval_eq_constant_coeff_of_vars
- \+ *lemma* eval₂_hom_congr'
- \+ *lemma* vars_bind₁
- \+ *lemma* vars_rename



## [2020-09-25 10:07:16](https://github.com/leanprover-community/mathlib/commit/2313602)
feat(order/bounded_lattice): custom recursors for with_bot/with_top ([#4245](https://github.com/leanprover-community/mathlib/pull/4245))
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *def* rec_bot_coe
- \+ *def* rec_top_coe



## [2020-09-25 10:07:14](https://github.com/leanprover-community/mathlib/commit/f43bd45)
fix(tactic/lint/simp): only head-beta reduce, don't whnf ([#4237](https://github.com/leanprover-community/mathlib/pull/4237))
This is necessary to accept simp lemmas like `injective reverse`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *theorem* ne_empty_of_mem

Modified src/data/list/basic.lean
- \+/\- *lemma* length_injective_iff
- \+/\- *lemma* length_injective
- \+/\- *theorem* cons_injective
- \+/\- *theorem* reverse_injective

Modified src/tactic/lint/simp.lean


Modified test/lint_simp_var_head.lean




## [2020-09-25 10:07:12](https://github.com/leanprover-community/mathlib/commit/5da451b)
feat(data/mv_polynomial/expand): replace variables by a power ([#4197](https://github.com/leanprover-community/mathlib/pull/4197))
From the Witt vectors project.
#### Estimated changes
Created src/data/mv_polynomial/expand.lean
- \+ *lemma* expand_C
- \+ *lemma* expand_X
- \+ *lemma* expand_monomial
- \+ *lemma* expand_one_apply
- \+ *lemma* expand_one
- \+ *lemma* expand_comp_bind₁
- \+ *lemma* expand_bind₁
- \+ *lemma* map_expand
- \+ *lemma* rename_expand
- \+ *lemma* rename_comp_expand



## [2020-09-25 09:07:07](https://github.com/leanprover-community/mathlib/commit/b6154d9)
feat(category_theory/limits): small lemmas ([#4251](https://github.com/leanprover-community/mathlib/pull/4251))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* limit.iso_limit_cone_hom_π
- \+ *lemma* limit.iso_limit_cone_inv_π
- \+ *lemma* limit.pre_eq
- \+ *def* limit.iso_limit_cone



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
- \+ *lemma* integral_nonneg
- \+ *lemma* integral_nonpos_of_ae
- \+ *lemma* integral_nonpos
- \+ *lemma* integral_mono_ae
- \+/\- *lemma* integral_mono
- \- *lemma* integral_nonpos_of_nonpos_ae

Modified src/measure_theory/set_integral.lean




## [2020-09-25 06:57:20](https://github.com/leanprover-community/mathlib/commit/143c074)
feat(category_theory/cofinal): cofinal functors ([#4218](https://github.com/leanprover-community/mathlib/pull/4218))
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+ *lemma* is_preconnected_induction

Modified src/category_theory/isomorphism.lean


Created src/category_theory/limits/cofinal.lean
- \+ *lemma* induction
- \+ *lemma* colimit_cocone_comp_aux
- \+ *lemma* colimit_pre_is_iso_aux
- \+ *lemma* has_colimit_of_comp
- \+ *def* cofinal
- \+ *def* lift
- \+ *def* hom_to_lift
- \+ *def* extend_cocone
- \+ *def* cocones_equiv
- \+ *def* is_colimit_whisker_equiv
- \+ *def* is_colimit_extend_cocone_equiv
- \+ *def* colimit_cocone_comp
- \+ *def* colimit_iso
- \+ *def* colimit_cocone_of_comp
- \+ *def* colimit_iso'

Modified src/category_theory/limits/limits.lean
- \+ *lemma* of_cocone_equiv_apply_desc
- \+ *lemma* of_cocone_equiv_symm_apply_desc
- \+ *lemma* colimit.iso_colimit_cocone_ι_hom
- \+ *lemma* colimit.iso_colimit_cocone_ι_inv
- \+ *lemma* colimit.pre_eq
- \+ *def* colimit.iso_colimit_cocone

Modified src/category_theory/over.lean
- \+/\- *def* over
- \+/\- *def* under

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
- \- *lemma* prod_nat_pow

Modified src/algebra/char_p.lean


Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_ite
- \+ *lemma* ite_pow
- \+ *lemma* pow_boole
- \+ *lemma* commute.mul_pow
- \+ *lemma* dvd_pow
- \+ *lemma* mul_gpow_neg_one
- \+ *lemma* zero_pow
- \+ *lemma* map_pow
- \+ *lemma* pow_dvd_pow
- \+ *lemma* pow_two_sub_pow_two
- \+ *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \+ *lemma* pow_abs
- \+ *lemma* abs_neg_one_pow
- \+ *lemma* nsmul_le_nsmul_of_le_right
- \+ *lemma* pow_le_pow_of_le_left
- \+ *lemma* pow_lt_pow
- \+ *lemma* lt_of_pow_lt_pow
- \+ *lemma* neg_square
- \+ *lemma* of_add_nsmul
- \+ *lemma* of_add_gsmul
- \+ *lemma* semiconj_by.gpow_right
- \+ *lemma* gpow_right
- \+ *lemma* gpow_left
- \+ *lemma* gpow_gpow
- \+ *theorem* pow_one
- \+ *theorem* one_nsmul
- \+ *theorem* one_pow
- \+ *theorem* nsmul_zero
- \+ *theorem* pow_mul
- \+ *theorem* mul_nsmul'
- \+ *theorem* pow_mul'
- \+ *theorem* mul_nsmul
- \+ *theorem* pow_mul_pow_sub
- \+ *theorem* nsmul_add_sub_nsmul
- \+ *theorem* pow_sub_mul_pow
- \+ *theorem* sub_nsmul_nsmul_add
- \+ *theorem* pow_bit0
- \+ *theorem* bit0_nsmul
- \+ *theorem* pow_bit1
- \+ *theorem* bit1_nsmul
- \+ *theorem* pow_mul_comm
- \+ *theorem* nsmul_add_comm
- \+ *theorem* monoid_hom.map_pow
- \+ *theorem* add_monoid_hom.map_nsmul
- \+ *theorem* is_monoid_hom.map_pow
- \+ *theorem* is_add_monoid_hom.map_nsmul
- \+ *theorem* neg_pow
- \+ *theorem* mul_pow
- \+ *theorem* nsmul_add
- \+ *theorem* inv_pow
- \+ *theorem* neg_nsmul
- \+ *theorem* pow_sub
- \+ *theorem* nsmul_sub
- \+ *theorem* pow_inv_comm
- \+ *theorem* nsmul_neg_comm
- \+ *theorem* gpow_coe_nat
- \+ *theorem* gsmul_coe_nat
- \+ *theorem* gpow_of_nat
- \+ *theorem* gsmul_of_nat
- \+ *theorem* gpow_neg_succ_of_nat
- \+ *theorem* gsmul_neg_succ_of_nat
- \+ *theorem* gpow_zero
- \+ *theorem* zero_gsmul
- \+ *theorem* gpow_one
- \+ *theorem* one_gsmul
- \+ *theorem* one_gpow
- \+ *theorem* gsmul_zero
- \+ *theorem* gpow_neg
- \+ *theorem* neg_gsmul
- \+ *theorem* gpow_neg_one
- \+ *theorem* neg_one_gsmul
- \+ *theorem* inv_gpow
- \+ *theorem* gsmul_neg
- \+ *theorem* commute.mul_gpow
- \+ *theorem* mul_gpow
- \+ *theorem* gsmul_add
- \+ *theorem* gsmul_sub
- \+ *theorem* neg_one_pow_eq_or
- \+ *theorem* pow_dvd_pow_of_dvd
- \+ *theorem* sq_sub_sq
- \+ *theorem* pow_eq_zero
- \+ *theorem* pow_ne_zero
- \+ *theorem* nsmul_nonneg
- \+ *theorem* nsmul_le_nsmul
- \+ *theorem* pow_pos
- \+ *theorem* one_le_pow_of_one_le
- \+ *theorem* pow_le_one
- \+ *theorem* pow_nonneg
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_left_inj
- \+ *theorem* pow_le_pow
- \+ *theorem* pow_two_nonneg
- \+ *theorem* pow_two_pos_of_ne_zero
- \+ *theorem* self_gpow
- \+ *theorem* gpow_self
- \+ *theorem* gpow_gpow_self

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* pow_ite
- \- *lemma* ite_pow
- \- *lemma* pow_boole
- \- *lemma* commute.mul_pow
- \- *lemma* dvd_pow
- \- *lemma* mul_gpow_neg_one
- \- *lemma* zero_pow
- \- *lemma* map_pow
- \- *lemma* pow_dvd_pow
- \- *lemma* pow_two_sub_pow_two
- \- *lemma* eq_or_eq_neg_of_pow_two_eq_pow_two
- \- *lemma* pow_abs
- \- *lemma* abs_neg_one_pow
- \- *lemma* nsmul_le_nsmul_of_le_right
- \- *lemma* pow_le_pow_of_le_left
- \- *lemma* pow_lt_pow
- \- *lemma* lt_of_pow_lt_pow
- \- *lemma* neg_square
- \- *lemma* of_add_nsmul
- \- *lemma* of_add_gsmul
- \- *lemma* gpow_right
- \- *lemma* gpow_left
- \- *lemma* gpow_gpow
- \- *theorem* pow_one
- \- *theorem* one_nsmul
- \- *theorem* one_pow
- \- *theorem* nsmul_zero
- \- *theorem* pow_mul
- \- *theorem* mul_nsmul'
- \- *theorem* pow_mul'
- \- *theorem* mul_nsmul
- \- *theorem* pow_mul_pow_sub
- \- *theorem* nsmul_add_sub_nsmul
- \- *theorem* pow_sub_mul_pow
- \- *theorem* sub_nsmul_nsmul_add
- \- *theorem* pow_bit0
- \- *theorem* bit0_nsmul
- \- *theorem* pow_bit1
- \- *theorem* bit1_nsmul
- \- *theorem* pow_mul_comm
- \- *theorem* nsmul_add_comm
- \- *theorem* monoid_hom.map_pow
- \- *theorem* add_monoid_hom.map_nsmul
- \- *theorem* is_monoid_hom.map_pow
- \- *theorem* is_add_monoid_hom.map_nsmul
- \- *theorem* neg_pow
- \- *theorem* mul_pow
- \- *theorem* nsmul_add
- \- *theorem* inv_pow
- \- *theorem* neg_nsmul
- \- *theorem* pow_sub
- \- *theorem* nsmul_sub
- \- *theorem* pow_inv_comm
- \- *theorem* nsmul_neg_comm
- \- *theorem* gpow_coe_nat
- \- *theorem* gsmul_coe_nat
- \- *theorem* gpow_of_nat
- \- *theorem* gsmul_of_nat
- \- *theorem* gpow_neg_succ_of_nat
- \- *theorem* gsmul_neg_succ_of_nat
- \- *theorem* gpow_zero
- \- *theorem* zero_gsmul
- \- *theorem* gpow_one
- \- *theorem* one_gsmul
- \- *theorem* one_gpow
- \- *theorem* gsmul_zero
- \- *theorem* gpow_neg
- \- *theorem* neg_gsmul
- \- *theorem* gpow_neg_one
- \- *theorem* neg_one_gsmul
- \- *theorem* inv_gpow
- \- *theorem* gsmul_neg
- \- *theorem* commute.mul_gpow
- \- *theorem* mul_gpow
- \- *theorem* gsmul_add
- \- *theorem* gsmul_sub
- \- *theorem* neg_one_pow_eq_or
- \- *theorem* pow_dvd_pow_of_dvd
- \- *theorem* sq_sub_sq
- \- *theorem* pow_eq_zero
- \- *theorem* pow_ne_zero
- \- *theorem* nsmul_nonneg
- \- *theorem* nsmul_le_nsmul
- \- *theorem* pow_pos
- \- *theorem* one_le_pow_of_one_le
- \- *theorem* pow_le_one
- \- *theorem* pow_nonneg
- \- *theorem* pow_lt_pow_of_lt_left
- \- *theorem* pow_left_inj
- \- *theorem* pow_le_pow
- \- *theorem* pow_two_nonneg
- \- *theorem* pow_two_pos_of_ne_zero
- \- *theorem* self_gpow
- \- *theorem* gpow_self
- \- *theorem* gpow_gpow_self

Modified src/analysis/specific_limits.lean


Modified src/computability/primrec.lean


Modified src/data/bitvec/basic.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/list/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean
- \- *lemma* pow_succ
- \- *lemma* pow_zero
- \- *lemma* one_pow
- \- *lemma* pow_eq_mul_pow_sub
- \- *theorem* pow_one
- \- *theorem* pow_le_pow_of_le_left
- \- *theorem* pos_pow_of_pos
- \- *theorem* zero_pow
- \- *theorem* pow_add
- \- *theorem* pow_two
- \- *theorem* mul_pow
- \- *theorem* pow_pos
- \- *theorem* pow_dvd_pow
- \- *theorem* pow_dvd_pow_of_dvd

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
- \+ *lemma* false_of_nontrivial_of_char_one
- \+ *lemma* nontrivial_of_char_ne_one
- \- *lemma* false_of_nonzero_of_char_one

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
Created src/field_theory/intermediate_field.lean
- \+ *lemma* coe_to_subalgebra
- \+ *lemma* coe_to_subfield
- \+ *lemma* mem_mk
- \+ *lemma* mem_coe
- \+ *lemma* mem_to_subalgebra
- \+ *lemma* mem_to_subfield
- \+ *lemma* list_prod_mem
- \+ *lemma* list_sum_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* multiset_sum_mem
- \+ *lemma* prod_mem
- \+ *lemma* sum_mem
- \+ *lemma* pow_mem
- \+ *lemma* gsmul_mem
- \+ *lemma* coe_int_mem
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* val_mk
- \+ *lemma* to_subalgebra_injective
- \+ *lemma* set_range_subset
- \+ *lemma* field_range_le
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* algebra_map_mem
- \+ *theorem* one_mem
- \+ *theorem* zero_mem
- \+ *theorem* mul_mem
- \+ *theorem* smul_mem
- \+ *theorem* add_mem
- \+ *theorem* sub_mem
- \+ *theorem* neg_mem
- \+ *theorem* inv_mem
- \+ *theorem* div_mem
- \+ *theorem* coe_val
- \+ *def* subalgebra.to_intermediate_field
- \+ *def* subfield.to_intermediate_field
- \+ *def* map
- \+ *def* val

Modified src/field_theory/subfield.lean
- \+ *theorem* sub_mem

Modified src/ring_theory/algebra_tower.lean




## [2020-09-24 17:38:30](https://github.com/leanprover-community/mathlib/commit/e23b97e)
feat(ring_theory/polynomial): decomposing the kernel of an endomorphism polynomial ([#4174](https://github.com/leanprover-community/mathlib/pull/4174))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* map_bit0
- \+ *lemma* map_bit1

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_zero
- \+ *lemma* aeval_monomial
- \+ *lemma* aeval_X_pow
- \+ *lemma* aeval_add
- \+ *lemma* aeval_one
- \+ *lemma* aeval_bit0
- \+ *lemma* aeval_bit1
- \+ *lemma* aeval_nat_cast
- \+ *lemma* aeval_mul

Modified src/data/polynomial/eval.lean
- \- *lemma* eval₂_endomorphism_algebra_map

Modified src/linear_algebra/basic.lean
- \+ *lemma* mul_apply

Modified src/ring_theory/algebra.lean
- \+ *lemma* map_bit0
- \+ *lemma* map_bit1

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* disjoint_ker_aeval_of_coprime
- \+ *lemma* sup_aeval_range_eq_top_of_coprime
- \+ *lemma* sup_ker_aeval_le_ker_aeval_mul
- \+ *lemma* sup_ker_aeval_eq_ker_aeval_mul_of_coprime



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
- \+ *lemma* has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape
- \+ *lemma* has_limits_of_has_limits_creates_limits
- \+ *lemma* has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape
- \+ *lemma* has_colimits_of_has_colimits_creates_colimits



## [2020-09-24 14:02:39](https://github.com/leanprover-community/mathlib/commit/03775fb)
chore(data/mv_polynomial): aeval_rename -> aeval_id_rename ([#4230](https://github.com/leanprover-community/mathlib/pull/4230))
`aeval_rename` was not general enough, so it is renamed to
`aeval_id_rename`.
Also: state and prove the more general version of `aeval_rename`.
#### Estimated changes
Modified src/data/mv_polynomial/monad.lean
- \+ *lemma* aeval_id_rename
- \- *lemma* aeval_rename

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* aeval_rename



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
- \+ *theorem* zero_union_range_succ
- \+ *theorem* range_of_succ
- \+ *theorem* range_rec
- \+ *theorem* range_cases_on

Modified src/data/set/basic.lean
- \+/\- *lemma* sep_set_of
- \+ *lemma* set_of_and
- \+ *lemma* set_of_or

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* tendsto_integral_approx_on_univ
- \+/\- *lemma* integral_add_measure
- \+/\- *lemma* integral_add_measure'

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable.const_smul
- \+/\- *lemma* measurable.const_mul
- \+/\- *lemma* measurable.mul_const
- \+ *lemma* is_measurable_lt'
- \+ *lemma* is_measurable_lt
- \+ *lemma* measurable_edist_right
- \+ *lemma* measurable_edist_left

Modified src/measure_theory/integration.lean
- \+ *lemma* measurable_bind

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.add'
- \+ *lemma* integrable.sub'

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ae_eq_bot

Modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* nearest_pt_ind_zero
- \+ *lemma* nearest_pt_zero
- \+ *lemma* nearest_pt_ind_succ
- \+ *lemma* nearest_pt_ind_le
- \+ *lemma* edist_nearest_pt_le
- \+ *lemma* tendsto_nearest_pt
- \+ *lemma* approx_on_zero
- \+ *lemma* approx_on_mem
- \+ *lemma* approx_on_comp
- \+ *lemma* tendsto_approx_on
- \+ *lemma* edist_approx_on_le
- \+ *lemma* edist_approx_on_y0_le
- \+ *lemma* tendsto_approx_on_l1_edist
- \+ *lemma* integrable_approx_on
- \+ *lemma* tendsto_approx_on_univ_l1_edist
- \+ *lemma* integrable_approx_on_univ
- \+ *lemma* tendsto_approx_on_univ_l1
- \- *lemma* simple_func_sequence_tendsto
- \- *lemma* simple_func_sequence_tendsto'

Modified src/topology/bases.lean
- \+/\- *lemma* dense_seq_dense



## [2020-09-24 08:37:51](https://github.com/leanprover-community/mathlib/commit/ba8fa0f)
feat(logic/embedding): use simps ([#4169](https://github.com/leanprover-community/mathlib/pull/4169))
Some lemmas are slightly reformulated, and have a worse name. But they are (almost) never typed explicitly, since they are simp lemmas (even the occurrences in other files probably came from `squeeze_simp`).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/nat_antidiagonal.lean


Modified src/data/finset/nat_antidiagonal.lean


Modified src/logic/embedding.lean
- \+/\- *lemma* refl_to_embedding
- \- *lemma* coe_sigma_mk
- \- *lemma* coe_sigma_map
- \- *lemma* coe_image
- \- *lemma* embedding_of_subset_apply_mk
- \- *lemma* coe_embedding_of_subset_apply
- \- *lemma* mul_left_embedding_apply
- \- *lemma* mul_right_embedding_apply
- \- *theorem* equiv.to_embedding_coe_fn
- \- *theorem* refl_apply
- \- *theorem* trans_apply
- \+/\- *def* sigma_mk
- \+/\- *def* sigma_map
- \+/\- *def* embedding_of_subset

Modified src/measure_theory/haar_measure.lean




## [2020-09-24 06:54:53](https://github.com/leanprover-community/mathlib/commit/5e934cd)
chore(*): cleanup imports, split off data/finset/preimage from data/set/finite ([#4221](https://github.com/leanprover-community/mathlib/pull/4221))
Mostly this consists of moving some content from `data.set.finite` to `data.finset.preimage`, in order to reduce imports in `data.set.finite`.
#### Estimated changes
Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/data/finset/default.lean


Created src/data/finset/preimage.lean
- \+ *lemma* mem_preimage
- \+ *lemma* coe_preimage
- \+ *lemma* monotone_preimage
- \+ *lemma* image_subset_iff_subset_preimage
- \+ *lemma* map_subset_iff_subset_preimage
- \+ *lemma* image_preimage
- \+ *lemma* image_preimage_of_bij
- \+ *lemma* sigma_preimage_mk
- \+ *lemma* sigma_preimage_mk_of_subset
- \+ *lemma* sigma_image_fst_preimage_mk
- \+ *lemma* prod_preimage'
- \+ *lemma* prod_preimage
- \+ *lemma* prod_preimage_of_bij

Modified src/data/finsupp/basic.lean


Modified src/data/set/finite.lean
- \- *lemma* mem_preimage
- \- *lemma* coe_preimage
- \- *lemma* monotone_preimage
- \- *lemma* image_subset_iff_subset_preimage
- \- *lemma* map_subset_iff_subset_preimage
- \- *lemma* image_preimage
- \- *lemma* image_preimage_of_bij
- \- *lemma* sigma_preimage_mk
- \- *lemma* sigma_preimage_mk_of_subset
- \- *lemma* sigma_image_fst_preimage_mk
- \- *lemma* prod_preimage'
- \- *lemma* prod_preimage
- \- *lemma* prod_preimage_of_bij

Modified src/order/filter/at_top_bot.lean


Modified src/topology/bases.lean




## [2020-09-24 05:52:22](https://github.com/leanprover-community/mathlib/commit/ed07cac)
feat(data/mv_polynomial/rename): coeff_rename ([#4203](https://github.com/leanprover-community/mathlib/pull/4203))
Also, use the opportunity to use R as variable for the coefficient ring
throughout the file.
#### Estimated changes
Modified src/data/mv_polynomial/rename.lean
- \+/\- *lemma* rename_C
- \+/\- *lemma* rename_X
- \+/\- *lemma* map_rename
- \+/\- *lemma* rename_rename
- \+/\- *lemma* rename_id
- \+/\- *lemma* rename_monomial
- \+/\- *lemma* rename_eq
- \+/\- *lemma* rename_injective
- \+/\- *lemma* total_degree_rename_le
- \+/\- *lemma* rename_eval₂
- \+/\- *lemma* rename_prodmk_eval₂
- \+/\- *lemma* eval₂_rename_prodmk
- \+/\- *lemma* eval_rename_prodmk
- \+/\- *lemma* eval₂_cast_comp
- \+ *lemma* coeff_rename_map_domain
- \+ *lemma* coeff_rename_eq_zero
- \+ *lemma* coeff_rename_ne_zero
- \+/\- *theorem* exists_finset_rename
- \+/\- *theorem* exists_fin_rename
- \+/\- *def* rename



## [2020-09-24 03:33:52](https://github.com/leanprover-community/mathlib/commit/ef18740)
feat(linear_algebra/eigenspace): generalized eigenvectors span the entire space ([#4111](https://github.com/leanprover-community/mathlib/pull/4111))
#### Estimated changes
Modified docs/references.bib


Modified src/linear_algebra/basic.lean
- \+ *lemma* ker_restrict

Modified src/linear_algebra/eigenspace.lean
- \+/\- *lemma* mem_eigenspace_iff
- \+/\- *lemma* eigenspace_div
- \+/\- *lemma* eigenspace_aeval_polynomial_degree_1
- \+/\- *lemma* ker_aeval_ring_hom'_unit_polynomial
- \+/\- *lemma* exists_eigenvalue
- \+/\- *lemma* eigenvectors_linear_independent
- \+/\- *lemma* exp_ne_zero_of_has_generalized_eigenvalue
- \+/\- *lemma* generalized_eigenspace_mono
- \+/\- *lemma* has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le
- \+/\- *lemma* eigenspace_le_generalized_eigenspace
- \+/\- *lemma* has_generalized_eigenvalue_of_has_eigenvalue
- \+/\- *lemma* generalized_eigenspace_eq_generalized_eigenspace_findim_of_le
- \+/\- *lemma* generalized_eigenspace_restrict
- \+ *lemma* generalized_eigenvec_disjoint_range_ker
- \+ *lemma* pos_findim_generalized_eigenspace_of_has_eigenvalue
- \+ *lemma* map_generalized_eigenrange_le
- \+ *lemma* supr_generalized_eigenspace_eq_top
- \+/\- *theorem* aeval_apply_of_has_eigenvector
- \+/\- *def* eigenspace
- \+/\- *def* has_eigenvector
- \+/\- *def* has_eigenvalue
- \+/\- *def* generalized_eigenspace
- \+/\- *def* has_generalized_eigenvector
- \+/\- *def* has_generalized_eigenvalue
- \+ *def* generalized_eigenrange

Modified src/ring_theory/algebra.lean
- \+ *lemma* mul_sub_algebra_map_commutes
- \+ *lemma* mul_sub_algebra_map_pow_commutes



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
- \- *lemma* image_map
- \- *def* image_iso_range

Modified src/category_theory/abelian/basic.lean
- \+ *lemma* strong_epi_of_epi
- \+ *lemma* image_ι_comp_eq_zero
- \- *lemma* image_eq_image
- \- *lemma* image_ι_eq_image_ι
- \- *lemma* kernel_cokernel_eq_image_ι
- \- *def* strong_epi_of_epi

Modified src/category_theory/abelian/exact.lean
- \+ *def* is_limit_image'

Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* strong_epi_of_epi
- \- *def* strong_epi_of_epi

Modified src/category_theory/abelian/pseudoelements.lean


Modified src/category_theory/arrow.lean
- \+ *lemma* has_lift.mk

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* iso_ext_hom_m
- \+ *lemma* iso_ext_inv_m
- \+ *lemma* e_iso_ext_hom
- \+ *lemma* e_iso_ext_inv
- \+ *lemma* has_image.mk
- \+ *lemma* is_image.lift_ι
- \+ *lemma* image_map.factor_map
- \+ *lemma* has_image_map.mk
- \+ *lemma* has_image_map.transport
- \+ *lemma* has_strong_epi_mono_factorisations.mk
- \+ *lemma* strong_epi_of_strong_epi_mono_factorisation
- \+ *lemma* strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
- \- *lemma* has_image_map.factor_map
- \+/\- *def* image.mono_factorisation
- \+/\- *def* image.is_image
- \+ *def* image_map.transport
- \+ *def* has_image_map.image_map
- \+ *def* image_map_comp
- \+ *def* image_map_id
- \- *def* has_image_map_comp
- \- *def* has_image_map_id

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* strong_epi_comp
- \+ *lemma* strong_epi_of_strong_epi
- \- *def* strong_epi_comp
- \- *def* strong_epi_of_strong_epi
- \- *def* is_iso_of_mono_of_strong_epi

Modified src/category_theory/limits/shapes/zero.lean
- \+ *def* image_factorisation_zero
- \+/\- *def* image_zero
- \- *def* has_image.zero

Modified src/category_theory/limits/types.lean
- \- *lemma* image_map

Modified src/category_theory/simple.lean




## [2020-09-24 00:15:43](https://github.com/leanprover-community/mathlib/commit/96e81fa)
feat(data/(lazy_)list): various lemmas and definitions ([#4172](https://github.com/leanprover-community/mathlib/pull/4172))
#### Estimated changes
Modified src/data/lazy_list/basic.lean
- \+ *lemma* mem_nil
- \+ *lemma* mem_cons
- \+ *theorem* forall_mem_cons
- \+ *def* pmap
- \+ *def* attach

Modified src/data/list/basic.lean
- \+ *lemma* nth_injective
- \+ *lemma* mem_of_mem_drop
- \+ *lemma* reverse_take
- \+ *lemma* inter_reverse
- \+ *lemma* slice_eq
- \+ *lemma* sizeof_slice_lt
- \+ *theorem* nth_eq_none_iff
- \+ *theorem* disjoint_take_drop
- \+ *theorem* mem_map_swap

Modified src/data/list/defs.lean
- \+ *def* slice

Modified src/data/list/perm.lean
- \+ *lemma* perm.take_inter
- \+ *lemma* perm.drop_inter
- \+ *lemma* perm.slice_inter
- \+ *theorem* perm.inter_append

Modified src/data/list/sigma.lean
- \+ *lemma* sizeof_kerase
- \+ *lemma* sizeof_erase_dupkeys

Modified src/data/list/zip.lean
- \+ *lemma* nth_zip_with
- \+ *lemma* nth_zip_with_eq_some
- \+ *lemma* nth_zip_eq_some

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

Created src/geometry/manifold/times_cont_mdiff_map.lean
- \+ *lemma* coe_inj
- \+ *lemma* comp_apply
- \+ *theorem* ext
- \+ *def* smooth_map
- \+ *def* id
- \+ *def* comp
- \+ *def* const



## [2020-09-23 18:48:10](https://github.com/leanprover-community/mathlib/commit/72e5b9f)
feat(measure_theory): ext lemmas for measures ([#3895](https://github.com/leanprover-community/mathlib/pull/3895))
Add class `sigma_finite`.
Also some cleanup.
Rename `measurable_space.is_measurable` -> `measurable_space.is_measurable'`. This is to avoid name clash with `_root_.is_measurable`, which should almost always be used instead.
define `is_pi_system`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* diff_eq_compl_inter
- \+ *theorem* diff_inter_self_eq_diff
- \+ *theorem* diff_self_inter

Modified src/logic/basic.lean
- \+ *lemma* fact.elim

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable.ennreal_add

Modified src/measure_theory/content.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_space.ext_iff
- \+/\- *lemma* generate_from_le
- \+/\- *lemma* generate_from_le_iff
- \+ *lemma* generate_has_compl
- \+ *lemma* generate_has_def
- \+ *lemma* generate_has_subset_generate_measurable
- \+/\- *lemma* generate_from_eq
- \+/\- *lemma* induction_on_inter
- \+/\- *def* is_measurable
- \+ *def* is_pi_system

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_compl
- \+ *lemma* ext_of_generate_from_of_Union
- \+ *lemma* ext_of_generate_finite
- \+ *def* measure_theory.measure.is_complete
- \- *def* is_complete

Modified src/measure_theory/outer_measure.lean




## [2020-09-23 16:56:11](https://github.com/leanprover-community/mathlib/commit/7cf8fa6)
fix(archive/100-thms): update link to 100.yaml in README ([#4224](https://github.com/leanprover-community/mathlib/pull/4224))
#### Estimated changes
Modified archive/100-theorems-list/README.md




## [2020-09-23 11:10:37](https://github.com/leanprover-community/mathlib/commit/ecd889a)
feat(data/polynomial/*): higher order derivative ([#4187](https://github.com/leanprover-community/mathlib/pull/4187))
#### Estimated changes
Created src/data/polynomial/iterated_deriv.lean
- \+ *lemma* iterated_deriv_zero_right
- \+ *lemma* iterated_deriv_succ
- \+ *lemma* iterated_deriv_zero_left
- \+ *lemma* iterated_deriv_add
- \+ *lemma* iterated_deriv_smul
- \+ *lemma* iterated_deriv_X_zero
- \+ *lemma* iterated_deriv_X_one
- \+ *lemma* iterated_deriv_X
- \+ *lemma* iterated_deriv_C_zero
- \+ *lemma* iterated_deriv_C
- \+ *lemma* iterated_deriv_one_zero
- \+ *lemma* iterated_deriv_one
- \+ *lemma* iterated_deriv_neg
- \+ *lemma* iterated_deriv_sub
- \+ *lemma* coeff_iterated_deriv_as_prod_Ico
- \+ *lemma* coeff_iterated_deriv_as_prod_range
- \+ *lemma* iterated_deriv_eq_zero_of_nat_degree_lt
- \+ *lemma* iterated_deriv_mul
- \+ *def* iterated_deriv



## [2020-09-23 09:47:01](https://github.com/leanprover-community/mathlib/commit/5ab7eb0)
feat(analysis/special_functions/trigonometric): continuity and differentiability of arctan ([#4138](https://github.com/leanprover-community/mathlib/pull/4138))
Added lemmas for continuity and differentiability of arctan, as well as various supporting limit lemmas.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* exists_cos_eq_zero
- \+/\- *lemma* exists_sin_eq
- \+/\- *lemma* exists_cos_eq
- \+/\- *lemma* range_cos
- \+/\- *lemma* range_sin
- \+ *lemma* arctan_mem_Ioo
- \+/\- *lemma* has_deriv_at_tan_of_mem_Ioo
- \+/\- *lemma* differentiable_at_tan_of_mem_Ioo
- \+/\- *lemma* deriv_tan_of_mem_Ioo
- \+ *lemma* continuous_on_tan_Ioo
- \+ *lemma* tendsto_sin_pi_div_two
- \+ *lemma* tendsto_cos_pi_div_two
- \+ *lemma* tendsto_tan_pi_div_two
- \+ *lemma* tendsto_sin_neg_pi_div_two
- \+ *lemma* tendsto_cos_neg_pi_div_two
- \+ *lemma* tendsto_tan_neg_pi_div_two
- \+ *lemma* tan_homeomorph_inv_fun_eq_arctan
- \+ *lemma* continuous_arctan
- \+ *lemma* has_deriv_at_arctan
- \+ *lemma* differentiable_at_arctan
- \+ *lemma* deriv_arctan
- \+ *lemma* has_deriv_at.arctan
- \+ *lemma* has_deriv_within_at.arctan
- \+ *lemma* differentiable_within_at.arctan
- \+ *lemma* differentiable_at.arctan
- \+ *lemma* differentiable_on.arctan
- \+ *lemma* differentiable.arctan
- \+ *lemma* deriv_within_arctan
- \+ *def* tan_homeomorph

Modified src/analysis/specific_limits.lean
- \- *lemma* tendsto_at_top_mul_left
- \- *lemma* tendsto_at_top_mul_right
- \- *lemma* tendsto_at_top_mul_left'
- \- *lemma* tendsto_at_top_mul_right'
- \- *lemma* tendsto_at_top_div
- \- *lemma* tendsto_inv_zero_at_top
- \- *lemma* tendsto_inv_at_top_zero'
- \- *lemma* tendsto_inv_at_top_zero

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_top_mul_left
- \+ *lemma* tendsto_at_top_mul_right
- \+ *lemma* tendsto_at_top_mul_left'
- \+ *lemma* tendsto_at_top_mul_right'
- \+ *lemma* tendsto_at_top_div
- \+ *lemma* tendsto_mul_at_top
- \+ *lemma* tendsto_mul_at_bot
- \+ *lemma* tendsto_inv_zero_at_top
- \+ *lemma* tendsto_inv_at_top_zero'
- \+ *lemma* tendsto_inv_at_top_zero
- \+ *lemma* tendsto.inv_tendsto_at_top
- \+ *lemma* tendsto.inv_tendsto_zero

Modified src/topology/homeomorph.lean
- \+ *def* change_inv



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
Created archive/imo/imo1972_b2.lean


Renamed archive/imo1988_q6.lean to archive/imo/imo1988_q6.lean




## [2020-09-22 17:01:30](https://github.com/leanprover-community/mathlib/commit/994c31d)
feat(ring_theory/ideal/basic): mem_bot ([#4211](https://github.com/leanprover-community/mathlib/pull/4211))
Snippet from the Witt project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* mem_bot

Modified src/ring_theory/ideal/over.lean




## [2020-09-22 14:52:30](https://github.com/leanprover-community/mathlib/commit/f2458d6)
chore(data/mv_polynomial): Rename variables ([#4208](https://github.com/leanprover-community/mathlib/pull/4208))
I renamed `α` to `R` throughout. I also changed the `\sigma` to `σ` in `basic.lean`, see leanprover-community/doc-gen[#62](https://github.com/leanprover-community/mathlib/pull/62)
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \+/\- *lemma* C_add
- \+/\- *lemma* C_mul
- \+/\- *lemma* C_pow
- \+/\- *lemma* C_eq_coe_nat
- \+/\- *lemma* smul_eq_C_mul
- \+/\- *lemma* X_pow_eq_single
- \+/\- *lemma* single_eq_C_mul_X
- \+/\- *lemma* monomial_add
- \+/\- *lemma* monomial_mul
- \+/\- *lemma* monomial_zero
- \+/\- *lemma* monomial_eq
- \+/\- *lemma* induction_on
- \+/\- *lemma* hom_eq_hom
- \+/\- *lemma* is_id
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_C
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* monic_monomial_eq
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* coeff_mul_X
- \+/\- *lemma* coeff_mul_X'
- \+/\- *lemma* eq_zero_iff
- \+/\- *lemma* ne_zero_iff
- \+/\- *lemma* exists_coeff_ne_zero
- \+/\- *lemma* constant_coeff_eq
- \+/\- *lemma* constant_coeff_C
- \+/\- *lemma* constant_coeff_monomial
- \+/\- *lemma* support_sum_monomial_coeff
- \+/\- *lemma* as_sum
- \+/\- *lemma* eval₂_eq
- \+/\- *lemma* eval₂_eq'
- \+/\- *lemma* eval₂_zero
- \+/\- *lemma* eval₂_one
- \+/\- *lemma* eval₂_pow
- \+/\- *lemma* coe_eval₂_hom
- \+/\- *lemma* eval₂_hom_congr
- \+/\- *lemma* eval₂_hom_C
- \+/\- *lemma* eval₂_hom_X'
- \+/\- *lemma* comp_eval₂_hom
- \+/\- *lemma* map_eval₂_hom
- \+/\- *lemma* eval₂_hom_monomial
- \+/\- *lemma* eval₂_comp_left
- \+/\- *lemma* eval₂_eta
- \+/\- *lemma* eval₂_congr
- \+/\- *lemma* eval₂_prod
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval₂_assoc
- \+/\- *lemma* eval_eq
- \+/\- *lemma* eval_eq'
- \+/\- *lemma* smul_eval
- \+/\- *lemma* eval_sum
- \+/\- *lemma* eval_prod
- \+/\- *lemma* eval₂_comp_right
- \+/\- *lemma* map_eval₂
- \+/\- *lemma* coeff_map
- \+/\- *lemma* eval_map
- \+/\- *lemma* eval₂_map
- \+/\- *lemma* eval₂_hom_map_hom
- \+/\- *lemma* constant_coeff_map
- \+/\- *lemma* constant_coeff_comp_map
- \+/\- *lemma* support_map_subset
- \+/\- *lemma* support_map_of_injective
- \+/\- *lemma* aeval_C
- \+/\- *lemma* aeval_monomial
- \+/\- *lemma* eval₂_hom_eq_zero
- \+/\- *lemma* aeval_eq_zero
- \+/\- *theorem* algebra_map_eq
- \+/\- *theorem* induction_on'
- \+/\- *theorem* map_monomial
- \+/\- *theorem* map_C
- \+/\- *theorem* map_X
- \+/\- *theorem* map_id
- \+/\- *theorem* map_map
- \+/\- *theorem* eval₂_eq_eval_map
- \+/\- *theorem* aeval_def
- \+/\- *theorem* eval_unique
- \+/\- *def* mv_polynomial
- \+/\- *def* coeff_coe_to_fun
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* coeff
- \+/\- *def* constant_coeff
- \+/\- *def* eval₂
- \+/\- *def* eval₂_hom
- \+/\- *def* eval
- \+/\- *def* map
- \+/\- *def* aeval

Modified src/data/mv_polynomial/comm_ring.lean
- \+/\- *lemma* C_sub
- \+/\- *lemma* C_neg
- \+/\- *lemma* coeff_neg
- \+/\- *lemma* coeff_sub
- \+/\- *lemma* degrees_neg
- \+/\- *lemma* degrees_sub
- \+/\- *lemma* hom_C
- \+/\- *lemma* eval₂_hom_X
- \+/\- *lemma* total_degree_neg
- \+/\- *lemma* total_degree_sub
- \+/\- *def* hom_equiv

Modified src/data/mv_polynomial/equiv.lean
- \+/\- *lemma* sum_to_iter_C
- \+/\- *lemma* sum_to_iter_Xl
- \+/\- *lemma* sum_to_iter_Xr
- \+/\- *lemma* iter_to_sum_C_C
- \+/\- *lemma* iter_to_sum_X
- \+/\- *lemma* iter_to_sum_C_X
- \+/\- *def* pempty_ring_equiv
- \+/\- *def* punit_ring_equiv
- \+/\- *def* ring_equiv_of_equiv
- \+/\- *def* ring_equiv_congr
- \+/\- *def* sum_to_iter
- \+/\- *def* iter_to_sum
- \+/\- *def* mv_polynomial_equiv_mv_polynomial
- \+/\- *def* sum_ring_equiv
- \+/\- *def* option_equiv_left
- \+/\- *def* option_equiv_right

Modified src/data/mv_polynomial/monad.lean


Modified src/data/mv_polynomial/variables.lean
- \+/\- *lemma* degrees_monomial
- \+/\- *lemma* degrees_monomial_eq
- \+/\- *lemma* degrees_C
- \+/\- *lemma* degrees_X
- \+/\- *lemma* degrees_zero
- \+/\- *lemma* degrees_one
- \+/\- *lemma* degrees_add
- \+/\- *lemma* degrees_sum
- \+/\- *lemma* degrees_mul
- \+/\- *lemma* degrees_prod
- \+/\- *lemma* degrees_pow
- \+/\- *lemma* mem_degrees
- \+/\- *lemma* le_degrees_add
- \+/\- *lemma* degrees_add_of_disjoint
- \+/\- *lemma* degrees_map
- \+/\- *lemma* degrees_map_of_injective
- \+/\- *lemma* vars_0
- \+/\- *lemma* vars_C
- \+/\- *lemma* vars_X
- \+/\- *lemma* mem_support_not_mem_vars_zero
- \+/\- *lemma* vars_add_subset
- \+/\- *lemma* vars_mul
- \+/\- *lemma* vars_one
- \+/\- *lemma* vars_pow
- \+/\- *lemma* vars_prod
- \+/\- *lemma* vars_monomial_single
- \+/\- *lemma* total_degree_eq
- \+/\- *lemma* total_degree_le_degrees_card
- \+/\- *lemma* total_degree_C
- \+/\- *lemma* total_degree_zero
- \+/\- *lemma* total_degree_one
- \+/\- *lemma* total_degree_X
- \+/\- *lemma* total_degree_add
- \+/\- *lemma* total_degree_mul
- \+/\- *lemma* total_degree_pow
- \+/\- *lemma* total_degree_multiset_prod
- \+/\- *lemma* exists_degree_lt
- \+/\- *lemma* coeff_eq_zero_of_total_degree_lt
- \+/\- *lemma* eval₂_hom_eq_constant_coeff_of_vars
- \+/\- *lemma* aeval_eq_constant_coeff_of_vars
- \+/\- *def* degrees
- \+/\- *def* vars
- \+/\- *def* degree_of
- \+/\- *def* total_degree



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
- \+/\- *theorem* adjoin_int

Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_map_of_subring
- \+ *lemma* coe_algebra_map_of_subring
- \+ *lemma* algebra_map_of_subring_apply
- \+ *lemma* is_subring_coe_algebra_map_hom
- \+ *lemma* is_subring_coe_algebra_map
- \+ *lemma* is_subring_algebra_map_apply
- \+ *lemma* map_inv
- \+ *lemma* map_div
- \+ *lemma* mem_range
- \+ *lemma* coe_range
- \+/\- *lemma* mem_subalgebra_of_subring
- \+ *lemma* mem_subalgebra_of_is_subring
- \- *lemma* subring_coe_algebra_map_hom
- \- *lemma* subring_coe_algebra_map
- \- *lemma* subring_algebra_map_apply
- \+ *def* to_subring
- \+/\- *def* subalgebra_of_subring
- \+ *def* subalgebra_of_is_subring

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/subring.lean
- \+ *lemma* mem_range_self
- \+ *lemma* surjective_onto_range
- \+ *theorem* sub_mem
- \+ *def* set.to_subring
- \- *def* to_comm_ring



## [2020-09-22 11:28:53](https://github.com/leanprover-community/mathlib/commit/d09ef4a)
feat(category_theory/monoidal): transport monoidal structure along an equivalence ([#4123](https://github.com/leanprover-community/mathlib/pull/4123))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+/\- *lemma* functor_unit_comp

Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* id_tensor_comp_tensor_id
- \+/\- *lemma* tensor_id_comp_id_tensor

Modified src/category_theory/monoidal/functor.lean
- \+ *def* id

Created src/category_theory/monoidal/transport.lean
- \+ *def* transport
- \+ *def* transported
- \+ *def* lax_to_transported
- \+ *def* to_transported
- \+ *def* lax_from_transported
- \+ *def* from_transported
- \+ *def* transported_monoidal_unit_iso
- \+ *def* transported_monoidal_counit_iso



## [2020-09-22 11:28:51](https://github.com/leanprover-community/mathlib/commit/caffd02)
feat(data/polynomial/degree/trailing_degree): basic definitions and properties ([#4113](https://github.com/leanprover-community/mathlib/pull/4113))
Adds trailing_degree, trailing_nat_degree, trailing_coeff and various lemmas add functionality to work with trailing coefficients
#### Estimated changes
Created src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* trailing_degree_lt_wf
- \+ *lemma* trailing_monic.def
- \+ *lemma* trailing_monic.trailing_coeff
- \+ *lemma* trailing_degree_zero
- \+ *lemma* nat_trailing_degree_zero
- \+ *lemma* trailing_degree_eq_top
- \+ *lemma* trailing_degree_eq_nat_trailing_degree
- \+ *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq
- \+ *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos
- \+ *lemma* nat_trailing_degree_eq_of_trailing_degree_eq_some
- \+ *lemma* nat_trailing_degree_le_trailing_degree
- \+ *lemma* nat_trailing_degree_eq_of_trailing_degree_eq
- \+ *lemma* le_trailing_degree_of_ne_zero
- \+ *lemma* nat_trailing_degree_le_of_ne_zero
- \+ *lemma* trailing_degree_le_trailing_degree
- \+ *lemma* trailing_degree_ne_of_nat_trailing_degree_ne
- \+ *lemma* nat_trailing_degree_le_nat_trailing_degree
- \+ *lemma* trailing_degree_C
- \+ *lemma* le_trailing_degree_C
- \+ *lemma* trailing_degree_one_le
- \+ *lemma* nat_trailing_degree_C
- \+ *lemma* nat_trailing_degree_one
- \+ *lemma* nat_trailing_degree_nat_cast
- \+ *lemma* trailing_degree_monomial
- \+ *lemma* monomial_le_trailing_degree
- \+ *lemma* coeff_eq_zero_of_trailing_degree_lt
- \+ *lemma* coeff_eq_zero_of_lt_nat_trailing_degree
- \+ *lemma* coeff_nat_trailing_degree_pred_eq_zero
- \+ *lemma* nat_trailing_degree_X_le
- \+ *lemma* trailing_degree_one
- \+ *lemma* trailing_degree_X
- \+ *lemma* nat_trailing_degree_X
- \+ *lemma* trailing_degree_neg
- \+ *lemma* nat_trailing_degree_neg
- \+ *lemma* nat_trailing_degree_int_cast
- \+ *lemma* next_coeff_up_C_eq_zero
- \+ *lemma* next_coeff_up_of_pos_nat_trailing_degree
- \+ *lemma* coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
- \+ *lemma* ne_zero_of_trailing_degree_lt
- \+ *theorem* nat_trailing_degree_le_of_trailing_degree_le
- \+ *theorem* le_trailing_degree_C_mul_X_pow
- \+ *theorem* le_trailing_degree_X_pow
- \+ *theorem* le_trailing_degree_X
- \+ *def* trailing_degree
- \+ *def* nat_trailing_degree
- \+ *def* trailing_coeff
- \+ *def* trailing_monic
- \+ *def* next_coeff_up



## [2020-09-22 10:04:16](https://github.com/leanprover-community/mathlib/commit/58d0bfc)
feat(topology/sheaves): alternate formulation of the sheaf condition ([#4190](https://github.com/leanprover-community/mathlib/pull/4190))
Currently the sheaf condition is stated as it often is in textbooks, e.g. 
https://stacks.math.columbia.edu/tag/0072. That is, it is about an equalizer of the two maps `∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
This PR adds an equivalent formulation, saying that `F.obj (supr U)` (with its natural projection maps) is the limit of the diagram consisting of the `F.obj (U i)` and the `F.obj (U i ⊓ U j)`. 
I'd like to add further reformulations in subsequent PRs, in particular the nice one I saw in Lurie's SAG, just saying that `F.obj (supr U)` is the limit over the diagram of all `F.obj V` where `V` is an open subset of *some* `U i`. This version is actually much nicer to formalise, and I'm hoping we can translate over quite a lot of what we've already done about the sheaf condition to that version
#### Estimated changes
Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Created src/category_theory/category/pairwise.lean
- \+ *def* id
- \+ *def* comp
- \+ *def* diagram_obj
- \+ *def* diagram_map
- \+ *def* diagram
- \+ *def* cone_π_app
- \+ *def* cone
- \+ *def* cone_is_limit

Modified src/category_theory/opposites.lean
- \+ *lemma* le_of_op_hom
- \+ *def* op_hom_of_le

Modified src/topology/sheaves/forget.lean
- \+/\- *def* map_cone_fork

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf.lean
- \- *lemma* w
- \- *lemma* fork_X
- \- *lemma* fork_ι
- \- *lemma* fork_π_app_walking_parallel_pair_zero
- \- *lemma* fork_π_app_walking_parallel_pair_one
- \- *def* pi_opens
- \- *def* pi_inters
- \- *def* left_res
- \- *def* right_res
- \- *def* res
- \- *def* diagram
- \- *def* fork
- \- *def* pi_opens.iso_of_iso
- \- *def* pi_inters.iso_of_iso
- \- *def* diagram.iso_of_iso
- \- *def* fork.iso_of_iso
- \- *def* cover.of_open_embedding
- \- *def* pi_opens.iso_of_open_embedding
- \- *def* pi_inters.iso_of_open_embedding
- \- *def* diagram.iso_of_open_embedding
- \- *def* fork.iso_of_open_embedding

Created src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+ *lemma* w
- \+ *lemma* fork_X
- \+ *lemma* fork_ι
- \+ *lemma* fork_π_app_walking_parallel_pair_zero
- \+ *lemma* fork_π_app_walking_parallel_pair_one
- \+ *def* pi_opens
- \+ *def* pi_inters
- \+ *def* left_res
- \+ *def* right_res
- \+ *def* res
- \+ *def* diagram
- \+ *def* fork
- \+ *def* pi_opens.iso_of_iso
- \+ *def* pi_inters.iso_of_iso
- \+ *def* diagram.iso_of_iso
- \+ *def* fork.iso_of_iso
- \+ *def* cover.of_open_embedding
- \+ *def* pi_opens.iso_of_open_embedding
- \+ *def* pi_inters.iso_of_open_embedding
- \+ *def* diagram.iso_of_open_embedding
- \+ *def* fork.iso_of_open_embedding

Created src/topology/sheaves/sheaf_condition/pairwise_intersections.lean
- \+ *def* sheaf_condition_pairwise_intersections
- \+ *def* sheaf_condition_preserves_limit_pairwise_intersections
- \+ *def* cone_equiv_functor_obj
- \+ *def* cone_equiv_functor
- \+ *def* cone_equiv_inverse_obj
- \+ *def* cone_equiv_inverse
- \+ *def* cone_equiv_unit_iso_app
- \+ *def* cone_equiv_unit_iso
- \+ *def* cone_equiv_counit_iso
- \+ *def* cone_equiv
- \+ *def* is_limit_map_cone_of_is_limit_sheaf_condition_fork
- \+ *def* is_limit_sheaf_condition_fork_of_is_limit_map_cone
- \+ *def* sheaf_condition_equiv_sheaf_condition_pairwise_intersections
- \+ *def* sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections

Modified src/topology/sheaves/sheaf_of_functions.lean




## [2020-09-22 08:41:20](https://github.com/leanprover-community/mathlib/commit/b4641ef)
feat(l1_space): add measurability to integrable ([#4170](https://github.com/leanprover-community/mathlib/pull/4170))
This PR defines `integrable` such that `integrable` implies `measurable`. The old version is called `has_finite_integral`.
This allows us to drop *many* measurability conditions from lemmas that also require integrability.
There are some lemmas that have extra measurability conditions, if it has `integrable` as conclusion without corresponding `measurable` hypothesis.
There are many results that require an additional `[measurable_space E]` hypothesis, and some that require `[borel_space E]` or `[second_countable_space E]` (usually when using that addition is measurable).
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* integrable_pair
- \+/\- *lemma* integral_sub
- \+/\- *lemma* of_simple_func_zero
- \+/\- *lemma* of_simple_func_add
- \+/\- *lemma* of_simple_func_sub
- \+/\- *lemma* integral_eq
- \+/\- *lemma* integral_undef
- \+/\- *lemma* integral_add
- \+/\- *lemma* l1.integral_of_fun_eq_integral
- \+/\- *lemma* tendsto_integral_of_l1
- \+/\- *lemma* integral_eq_lintegral_max_sub_lintegral_min
- \+/\- *lemma* l1.norm_of_fun_eq_integral_norm
- \+/\- *lemma* integral_mono
- \+/\- *lemma* integral_mono_of_nonneg
- \+/\- *lemma* norm_integral_le_of_norm_le
- \+/\- *lemma* integral_finset_sum
- \+ *lemma* integral_add_measure'
- \+/\- *lemma* integral_add_measure
- \- *lemma* integral_non_integrable

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* refl
- \+/\- *lemma* neg
- \+/\- *lemma* add
- \+/\- *lemma* sub
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+/\- *lemma* integral_add
- \+/\- *lemma* integral_sub
- \+/\- *lemma* integral_has_strict_fderiv_at_of_tendsto_ae
- \+/\- *lemma* integral_has_strict_fderiv_at
- \+/\- *lemma* integral_has_strict_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_strict_deriv_at_right
- \+/\- *lemma* integral_has_strict_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_strict_deriv_at_left
- \+/\- *lemma* integral_has_fderiv_at_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_at
- \+/\- *lemma* fderiv_integral_of_tendsto_ae
- \+/\- *lemma* fderiv_integral
- \+/\- *lemma* integral_has_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_deriv_at_right
- \+/\- *lemma* deriv_integral_of_tendsto_ae_right
- \+/\- *lemma* deriv_integral_right
- \+/\- *lemma* integral_has_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_deriv_at_left
- \+/\- *lemma* deriv_integral_of_tendsto_ae_left
- \+/\- *lemma* deriv_integral_left
- \+/\- *lemma* integral_has_fderiv_within_at_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_within_at
- \+/\- *lemma* fderiv_within_integral_of_tendsto_ae
- \+/\- *lemma* integral_has_deriv_within_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_deriv_within_at_right
- \+/\- *lemma* deriv_within_integral_of_tendsto_ae_right
- \+/\- *lemma* deriv_within_integral_right
- \+/\- *lemma* integral_has_deriv_within_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_deriv_within_at_left
- \+/\- *lemma* deriv_within_integral_of_tendsto_ae_left
- \+/\- *lemma* deriv_within_integral_left

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* lintegral_nnnorm_eq_lintegral_edist
- \+/\- *lemma* lintegral_norm_eq_lintegral_edist
- \+/\- *lemma* lintegral_edist_triangle
- \+/\- *lemma* lintegral_nnnorm_zero
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* lintegral_nnnorm_neg
- \+ *lemma* has_finite_integral_iff_norm
- \+ *lemma* has_finite_integral_iff_edist
- \+ *lemma* has_finite_integral_iff_of_real
- \+ *lemma* has_finite_integral.mono
- \+ *lemma* has_finite_integral.mono'
- \+ *lemma* has_finite_integral.congr'
- \+ *lemma* has_finite_integral_congr'
- \+ *lemma* has_finite_integral.congr
- \+ *lemma* has_finite_integral_congr
- \+ *lemma* has_finite_integral_const_iff
- \+ *lemma* has_finite_integral_const
- \+ *lemma* has_finite_integral_of_bounded
- \+ *lemma* has_finite_integral.mono_measure
- \+ *lemma* has_finite_integral.add_measure
- \+ *lemma* has_finite_integral.left_of_add_measure
- \+ *lemma* has_finite_integral.right_of_add_measure
- \+ *lemma* has_finite_integral_add_measure
- \+ *lemma* has_finite_integral.smul_measure
- \+ *lemma* has_finite_integral_zero_measure
- \+ *lemma* has_finite_integral_zero
- \+ *lemma* has_finite_integral.neg
- \+ *lemma* has_finite_integral_neg_iff
- \+ *lemma* has_finite_integral.norm
- \+ *lemma* has_finite_integral_norm_iff
- \+ *lemma* has_finite_integral_of_dominated_convergence
- \+ *lemma* has_finite_integral.max_zero
- \+ *lemma* has_finite_integral.min_zero
- \+ *lemma* has_finite_integral.smul
- \+ *lemma* has_finite_integral_smul_iff
- \+ *lemma* has_finite_integral.const_mul
- \+ *lemma* has_finite_integral.mul_const
- \+ *lemma* integrable.measurable
- \+ *lemma* integrable.has_finite_integral
- \+/\- *lemma* integrable.mono
- \+/\- *lemma* integrable.mono'
- \+/\- *lemma* integrable.congr'
- \+/\- *lemma* integrable_congr'
- \+/\- *lemma* integrable.congr
- \+/\- *lemma* integrable_congr
- \+/\- *lemma* integrable_const_iff
- \+/\- *lemma* integrable_const
- \+/\- *lemma* integrable.mono_measure
- \+/\- *lemma* integrable.add_measure
- \+/\- *lemma* integrable.left_of_add_measure
- \+/\- *lemma* integrable.right_of_add_measure
- \+/\- *lemma* integrable_add_measure
- \+/\- *lemma* integrable.smul_measure
- \+/\- *lemma* integrable_map_measure
- \+/\- *lemma* lintegral_edist_lt_top
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* integrable.add
- \+/\- *lemma* integrable_finset_sum
- \+/\- *lemma* integrable.neg
- \+/\- *lemma* integrable_neg_iff
- \+/\- *lemma* integrable.sub
- \+/\- *lemma* integrable.norm
- \+/\- *lemma* integrable_norm_iff
- \+/\- *lemma* integrable.max_zero
- \+/\- *lemma* integrable.min_zero
- \+/\- *lemma* integrable.smul
- \+/\- *lemma* integrable_smul_iff
- \+/\- *lemma* of_fun_eq_mk
- \+/\- *lemma* of_fun_eq_of_fun
- \+/\- *lemma* of_fun_zero
- \+/\- *lemma* of_fun_add
- \+/\- *lemma* of_fun_neg
- \+/\- *lemma* of_fun_sub
- \+/\- *lemma* norm_of_fun
- \+/\- *lemma* norm_of_fun_eq_lintegral_norm
- \+/\- *lemma* of_fun_smul
- \+/\- *lemma* of_fun_to_fun
- \+/\- *lemma* to_fun_of_fun
- \+/\- *lemma* dist_to_fun
- \+ *lemma* measurable.integrable_zero
- \- *lemma* integrable_iff_norm
- \- *lemma* integrable_iff_edist
- \- *lemma* integrable_iff_of_real
- \- *lemma* integrable_of_bounded
- \- *lemma* integrable_zero_measure
- \- *lemma* integrable_of_dominated_convergence
- \+ *def* has_finite_integral
- \+/\- *def* integrable
- \+/\- *def* l1
- \+/\- *def* of_fun

Modified src/measure_theory/set_integral.lean
- \+ *lemma* has_finite_integral_restrict_of_bounded
- \+/\- *lemma* integrable_on_empty
- \+/\- *lemma* integrable_on_finite_union
- \+/\- *lemma* integrable_on_finset_union
- \+/\- *lemma* integrable_indicator_iff
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+/\- *lemma* is_compact.integrable_on_of_nhds_within
- \+/\- *lemma* continuous_on.integrable_on_compact
- \+/\- *lemma* norm_comp_l1_apply_le
- \+/\- *lemma* integrable_comp
- \+/\- *lemma* comp_l1_apply
- \+/\- *lemma* measurable_comp_l1
- \+/\- *lemma* integral_comp_comm
- \+/\- *lemma* integral_comp_l1_comm
- \- *lemma* integrable_on_of_bounded
- \+/\- *def* comp_l1

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* simple_func_sequence_tendsto'



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
- \- *theorem* prod_eq_zero_iff

Modified src/algebra/gcd_monoid.lean
- \+ *lemma* associates.mk_normalize
- \+/\- *lemma* normalize_apply

Modified src/data/multiset/basic.lean
- \+ *theorem* prod_eq_zero_iff

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* of_ufd_of_unique_irreducible
- \+ *theorem* ufd

Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factors_unique
- \+ *lemma* prime_factors_unique
- \+ *lemma* prime_factors_irreducible
- \+ *lemma* wf_dvd_monoid_of_exists_prime_of_factor
- \+ *lemma* irreducible_iff_prime_of_exists_prime_of_factor
- \+/\- *lemma* factors_irreducible
- \+/\- *lemma* exists_mem_factors_of_dvd
- \+ *lemma* no_factors_of_no_prime_of_factor
- \+ *lemma* dvd_of_dvd_mul_left_of_no_prime_of_factor
- \+ *lemma* dvd_of_dvd_mul_right_of_no_prime_of_factor
- \+/\- *lemma* exists_reduced_factors
- \+/\- *lemma* exists_reduced_factors'
- \- *lemma* irreducible_iff_prime
- \- *lemma* irreducible_factors
- \- *lemma* unique
- \- *lemma* associates_irreducible_iff_prime
- \- *lemma* no_factors_of_no_prime_factors
- \- *lemma* dvd_of_dvd_mul_left_of_no_prime_factors
- \- *lemma* dvd_of_dvd_mul_right_of_no_prime_factors
- \- *lemma* exists_prime_dvd_of_gcd_ne_one
- \+ *theorem* exists_prime_of_factor
- \+ *theorem* unique_factorization_monoid_of_exists_prime_of_factor
- \+ *theorem* unique_factorization_monoid_iff_exists_prime_of_factor
- \+ *theorem* irreducible_iff_prime_of_exists_unique_irreducible_of_factor
- \+ *theorem* unique_factorization_monoid.of_exists_unique_irreducible_of_factor
- \+ *theorem* factors_prod
- \+ *theorem* prime_of_factor
- \+ *theorem* irreducible_of_factor
- \+ *theorem* normalize_factor
- \+/\- *theorem* map_subtype_coe_factors'
- \+/\- *theorem* factors_mk
- \- *theorem* coprime_iff_gcd_eq_one
- \+/\- *def* {u}
- \- *def* of_unique_irreducible_factorization
- \- *def* factors'
- \- *def* factors
- \- *def* unique_factorization_domain.to_gcd_monoid



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




## [2020-09-21 13:06:58](https://github.com/leanprover-community/mathlib/commit/4a8c38e)
chore(category_theory/limits/lattice): cleanup ([#4191](https://github.com/leanprover-community/mathlib/pull/4191))
#### Estimated changes
Modified src/category_theory/limits/lattice.lean
- \+ *lemma* limit_iso_infi_hom
- \+ *lemma* limit_iso_infi_inv
- \+ *lemma* colimit_iso_supr_hom
- \+ *lemma* colimit_iso_supr_inv
- \+ *def* limit_cone
- \+ *def* colimit_cocone
- \+ *def* limit_iso_infi
- \+ *def* colimit_iso_supr



## [2020-09-21 10:21:23](https://github.com/leanprover-community/mathlib/commit/cd4a91f)
fix(scripts/mk_all): macOS compatibility fix ([#4148](https://github.com/leanprover-community/mathlib/pull/4148))
`readlink -f` doesn't work macOS unfortunately - there are alternatives but I think it's probably safe to remove it altogether? This assumes `mk_all.sh` isn't a symlink but I can't think of a reason why it should be - and `rm_all.sh` uses `dirname "${BASH_SOURCE[0]}"` directly 🙂
#### Estimated changes
Modified scripts/mk_all.sh




## [2020-09-21 08:37:54](https://github.com/leanprover-community/mathlib/commit/e483298)
feat(ring_theory/unique_factorization_domain): API for coprime, coprime factor of a power is a power ([#4049](https://github.com/leanprover-community/mathlib/pull/4049))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* exists_rep
- \+ *lemma* exists_non_zero_rep

Modified src/algebra/big_operators/basic.lean
- \+ *lemma* count_sum'
- \+ *lemma* to_finset_sum_count_smul_eq
- \+ *theorem* exists_smul_of_dvd_count

Modified src/algebra/group_with_zero_power.lean
- \+/\- *theorem* pow_eq_zero'
- \+/\- *theorem* pow_ne_zero'

Modified src/data/list/basic.lean
- \+/\- *lemma* dvd_prod

Modified src/data/multiset/basic.lean
- \+/\- *lemma* dvd_prod
- \+ *lemma* count_sum
- \+ *theorem* map_repeat

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* count_some
- \+ *lemma* count_zero
- \+ *lemma* count_reducible
- \+ *lemma* factor_set_mem_eq_mem
- \+ *lemma* mem_factor_set_top
- \+ *lemma* mem_factor_set_some
- \+ *lemma* reducible_not_mem_factor_set
- \+ *lemma* dvd_of_mem_factors
- \+ *lemma* dvd_of_mem_factors'
- \+ *lemma* mem_factors'_of_dvd
- \+ *lemma* mem_factors'_iff_dvd
- \+ *lemma* associates_irreducible_iff_prime
- \+ *lemma* mem_factors_of_dvd
- \+ *lemma* mem_factors_iff_dvd
- \+ *lemma* exists_prime_dvd_of_not_inf_one
- \+ *lemma* factors_one
- \+ *lemma* count_pow
- \+ *lemma* exists_prime_dvd_of_gcd_ne_one
- \+ *theorem* coprime_iff_inf_one
- \+ *theorem* factors_prime_pow
- \+ *theorem* prime_pow_dvd_iff_le
- \+ *theorem* le_of_count_ne_zero
- \+ *theorem* count_mul
- \+ *theorem* count_of_coprime
- \+ *theorem* count_mul_of_coprime
- \+ *theorem* count_mul_of_coprime'
- \+ *theorem* dvd_count_of_dvd_count_mul
- \+ *theorem* pow_factors
- \+ *theorem* dvd_count_pow
- \+ *theorem* is_pow_of_dvd_count
- \+ *theorem* eq_pow_of_mul_eq_pow
- \+ *theorem* coprime_iff_gcd_eq_one
- \+ *def* bcount
- \+ *def* count
- \+ *def* bfactor_set_mem
- \+ *def* factor_set_mem



## [2020-09-21 06:08:33](https://github.com/leanprover-community/mathlib/commit/40f582b)
feat(data/*/nat_antidiagonal): induction lemmas about antidiagonals ([#4193](https://github.com/leanprover-community/mathlib/pull/4193))
Adds a `nat.antidiagonal_succ` lemma for `list`, `multiset`, and `finset`, useful for proving facts about power series derivatives
#### Estimated changes
Modified src/algebra/big_operators/default.lean


Created src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* sum_antidiagonal_succ

Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ
- \+ *lemma* map_swap_antidiagonal

Modified src/data/list/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ

Modified src/data/multiset/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ



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
- \+ *lemma* filter_false_of_mem

Modified src/data/monoid_algebra.lean




## [2020-09-20 21:53:36](https://github.com/leanprover-community/mathlib/commit/db9842c)
feat(analysis/calculus/times_cont_diff): inversion of continuous linear maps is smooth ([#4185](https://github.com/leanprover-community/mathlib/pull/4185))
- Introduce an `inverse` function on the space of continuous linear maps between two Banach spaces, which is the inverse if the map is a continuous linear equivalence and zero otherwise.
- Prove that this function is `times_cont_diff_at` each `continuous_linear_equiv`.
- Some of the constructions used had been introduced in [#3282](https://github.com/leanprover-community/mathlib/pull/3282) and placed in `analysis.normed_space.operator_norm` (normed spaces); they are moved to the earlier file `topology.algebra.module` (topological vector spaces).
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* inverse_unit
- \+ *lemma* inverse_non_unit

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_ring_inverse
- \+/\- *lemma* differentiable_at_inverse
- \- *lemma* has_fderiv_at_inverse

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at.prod
- \+ *lemma* times_cont_diff_at_ring_inverse
- \+ *lemma* times_cont_diff_at_map_inverse
- \- *lemma* times_cont_diff_at_inverse

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* units_equiv_to_continuous_linear_map
- \- *def* of_unit
- \- *def* to_unit
- \- *def* units_equiv

Modified src/topology/algebra/module.lean
- \+ *lemma* comp_coe
- \+ *lemma* refl_symm
- \+ *lemma* units_equiv_apply
- \+ *lemma* inverse_equiv
- \+ *lemma* inverse_non_equiv
- \+ *lemma* ring_inverse_equiv
- \+ *lemma* to_ring_inverse
- \+ *lemma* ring_inverse_eq_map_inverse
- \+ *theorem* trans_apply
- \+ *theorem* symm_trans_apply
- \+ *def* of_unit
- \+ *def* to_unit
- \+ *def* units_equiv



## [2020-09-20 21:53:34](https://github.com/leanprover-community/mathlib/commit/d774ef6)
feat(topology/path_connected): add lemmas about paths and continuous families of paths ([#4063](https://github.com/leanprover-community/mathlib/pull/4063))
From the sphere eversion project (see https://github.com/leanprover-community/sphere-eversion/pull/12)
#### Estimated changes
Modified src/topology/path_connected.lean
- \+ *lemma* proj_I_zero
- \+ *lemma* proj_I_one
- \+ *lemma* refl_range
- \+ *lemma* refl_symm
- \+ *lemma* symm_range
- \+ *lemma* extend_extends
- \+ *lemma* extend_extends'
- \+ *lemma* extend_range
- \+ *lemma* extend_le_zero
- \+ *lemma* extend_one_le
- \+ *lemma* refl_extend
- \+ *lemma* refl_trans_refl
- \+ *lemma* trans_range
- \+ *lemma* symm_cast
- \+ *lemma* trans_cast
- \+ *lemma* symm_continuous_family
- \+ *lemma* continuous_uncurry_extend_of_continuous_family
- \+ *lemma* trans_continuous_family
- \+ *lemma* truncate_range
- \+ *lemma* truncate_continuous_family
- \+ *lemma* truncate_const_continuous_family
- \+ *lemma* truncate_self
- \+ *lemma* truncate_zero_zero
- \+ *lemma* truncate_one_one
- \+ *lemma* truncate_zero_one
- \+ *lemma* is_path_connected.exists_path_through_family
- \+ *lemma* is_path_connected.exists_path_through_family'
- \+ *lemma* exists_path_through_family
- \+ *lemma* exists_path_through_family'
- \+ *def* truncate
- \+ *def* truncate_of_le



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
- \+ *lemma* sub_lt_iff_lt_add
- \+ *lemma* sub_eq_iff_eq_add

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_limsup_eq_zero
- \+ *lemma* ae_eventually_not_mem

Modified src/order/complete_lattice.lean
- \+ *lemma* supr_ge_eq_supr_nat_add
- \+ *lemma* infi_ge_eq_infi_nat_add

Modified src/order/liminf_limsup.lean
- \+ *lemma* limsup_eq_infi_supr_of_nat'
- \+ *lemma* liminf_eq_supr_infi_of_nat'

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* le_has_sum
- \+ *lemma* le_tsum
- \+ *lemma* le_has_sum'
- \+ *lemma* le_tsum'
- \+ *lemma* has_sum_zero_iff
- \+ *lemma* tsum_eq_zero_iff

Modified src/topology/instances/ennreal.lean
- \+ *lemma* to_nnreal_apply_of_tsum_ne_top
- \+ *lemma* summable_to_nnreal_of_tsum_ne_top
- \+ *lemma* tendsto_sum_nat_add

Modified src/topology/instances/nnreal.lean
- \+ *lemma* summable_nat_add
- \+ *lemma* sum_add_tsum_nat_add



## [2020-09-20 16:28:24](https://github.com/leanprover-community/mathlib/commit/2c9b063)
feat(algebra/big_operators): add prod boole lemma ([#4192](https://github.com/leanprover-community/mathlib/pull/4192))
A small lemma to simplify products of indicator functions
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_boole



## [2020-09-20 00:47:20](https://github.com/leanprover-community/mathlib/commit/44667ba)
feat(ring_theory/power_series): power series lemmas ([#4171](https://github.com/leanprover-community/mathlib/pull/4171))
A couple of little lemmas for multiplication and coefficients
#### Estimated changes
Modified src/ring_theory/power_series.lean
- \+ *lemma* coeff_C_mul
- \+ *lemma* coeff_smul



## [2020-09-20 00:00:33](https://github.com/leanprover-community/mathlib/commit/9232032)
refactor(linear_algebra/tensor_algebra): build as a quotient of a free algebra ([#4079](https://github.com/leanprover-community/mathlib/pull/4079))
#### Estimated changes
Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* ring_quot_mk_alg_hom_free_algebra_ι_eq_ι
- \+ *theorem* lift_ι_apply
- \+/\- *theorem* hom_ext
- \+/\- *def* tensor_algebra
- \- *def* has_coe_module
- \- *def* has_coe_semiring
- \- *def* has_mul
- \- *def* has_add
- \- *def* has_zero
- \- *def* has_one
- \- *def* has_scalar
- \- *def* lift_fun



## [2020-09-19 23:11:09](https://github.com/leanprover-community/mathlib/commit/7013e5b)
feat(category_theory/internal): commutative monoid objects ([#4186](https://github.com/leanprover-community/mathlib/pull/4186))
This reprises a series of our recent PRs on monoid objects in monoidal categories, developing the same material for commutative monoid objects in braided categories.
#### Estimated changes
Modified src/category_theory/monad/equiv_mon.lean


Created src/category_theory/monoidal/CommMon_.lean
- \+ *lemma* id_hom
- \+ *lemma* comp_hom
- \+ *lemma* forget₂_Mon_obj_one
- \+ *lemma* forget₂_Mon_obj_mul
- \+ *lemma* forget₂_Mon_map_hom
- \+ *def* trivial
- \+ *def* forget₂_Mon_
- \+ *def* map_CommMon
- \+ *def* map_CommMon_functor
- \+ *def* lax_braided_to_CommMon
- \+ *def* CommMon_to_lax_braided
- \+ *def* unit_iso
- \+ *def* counit_iso
- \+ *def* equiv_lax_braided_functor_punit

Created src/category_theory/monoidal/Mod.lean
- \+ *lemma* assoc_flip
- \+ *lemma* id_hom'
- \+ *lemma* comp_hom'
- \+ *def* id
- \+ *def* comp
- \+ *def* regular
- \+ *def* forget
- \+ *def* comap

Renamed src/category_theory/monoidal/internal.lean to src/category_theory/monoidal/Mon_.lean
- \- *lemma* assoc_flip
- \- *lemma* id_hom'
- \- *lemma* comp_hom'
- \- *def* id
- \- *def* comp
- \- *def* regular
- \- *def* forget
- \- *def* comap

Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* comp_to_nat_trans
- \+ *def* id
- \+ *def* comp
- \+ *def* mk_iso
- \+ *def* to_lax_braided_functor
- \+ *def* discrete.braided_functor

Modified src/category_theory/monoidal/discrete.lean


Modified src/category_theory/monoidal/functor_category.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/monoidal/internal/functor_category.lean
- \+ *def* functor
- \+ *def* inverse
- \+ *def* unit_iso
- \+ *def* counit_iso
- \+ *def* CommMon_functor_category_equivalence

Modified src/category_theory/monoidal/internal/types.lean
- \+ *def* functor
- \+ *def* inverse
- \+ *def* CommMon_Type_equivalence_CommMon
- \+ *def* CommMon_Type_equivalence_CommMon_forget

Modified src/category_theory/monoidal/types.lean
- \+ *lemma* braiding_hom_apply
- \+ *lemma* braiding_inv_apply



## [2020-09-19 20:26:57](https://github.com/leanprover-community/mathlib/commit/5b143ff)
feat(data/set/basic): a few lemmas ([#4184](https://github.com/leanprover-community/mathlib/pull/4184))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* image_union_image_compl_eq_range
- \+ *theorem* inter_union_compl



## [2020-09-19 19:45:22](https://github.com/leanprover-community/mathlib/commit/640ba6c)
feat(geometry/euclidean): cospherical points ([#4178](https://github.com/leanprover-community/mathlib/pull/4178))
Define cospherical points in a Euclidean space (the general-dimension
version of the two-dimensional concept of a set of points being
concyclic) and prove some very basic lemmas about them.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* cospherical_def
- \+ *lemma* cospherical_subset
- \+ *lemma* cospherical_empty
- \+ *lemma* cospherical_singleton
- \+ *lemma* cospherical_insert_singleton
- \+ *def* cospherical

Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* cospherical_iff_exists_mem_of_complete
- \+ *lemma* cospherical_iff_exists_mem_of_finite_dimensional
- \+ *lemma* exists_circumradius_eq_of_cospherical_subset
- \+ *lemma* circumradius_eq_of_cospherical_subset
- \+ *lemma* exists_circumradius_eq_of_cospherical
- \+ *lemma* circumradius_eq_of_cospherical
- \+ *lemma* exists_circumcenter_eq_of_cospherical_subset
- \+ *lemma* circumcenter_eq_of_cospherical_subset
- \+ *lemma* exists_circumcenter_eq_of_cospherical
- \+ *lemma* circumcenter_eq_of_cospherical



## [2020-09-19 19:03:21](https://github.com/leanprover-community/mathlib/commit/02b492a)
feat(category_theory/Mon): Mon_ C has limits when C does ([#4133](https://github.com/leanprover-community/mathlib/pull/4133))
If `C` has limits, so does `Mon_ C`.
(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)
#### Estimated changes
Modified src/category_theory/functorial.lean
- \+ *lemma* map_as_map
- \+ *lemma* functorial.map_id
- \+ *lemma* functorial.map_comp

Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/internal.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/monoidal/internal/functor_category.lean


Created src/category_theory/monoidal/internal/limits.lean
- \+ *def* limit
- \+ *def* limit_cone
- \+ *def* forget_map_cone_limit_cone_iso
- \+ *def* limit_cone_is_limit

Modified src/category_theory/monoidal/limits.lean
- \+ *lemma* lim_lax_ε
- \+ *lemma* lim_lax_μ



## [2020-09-19 04:51:22](https://github.com/leanprover-community/mathlib/commit/567954f)
feat(category_theory): `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is monoidal ([#4132](https://github.com/leanprover-community/mathlib/pull/4132))
A step towards constructing limits in `Mon_ C` (and thence towards sheaves of modules as internal objects).
#### Estimated changes
Created src/category_theory/monoidal/limits.lean
- \+ *lemma* limit_functorial_map
- \+ *lemma* lim_lax_obj
- \+ *lemma* lim_lax_obj'
- \+ *lemma* lim_lax_map
- \+ *def* lim_lax



## [2020-09-19 03:33:07](https://github.com/leanprover-community/mathlib/commit/04fe4b6)
feat(algebra/ring_quot): quotients of noncommutative rings ([#4078](https://github.com/leanprover-community/mathlib/pull/4078))
#### Estimated changes
Created src/algebra/ring_quot.lean
- \+ *lemma* mk_ring_hom_rel
- \+ *lemma* mk_ring_hom_surjective
- \+ *lemma* ring_quot_ext
- \+ *lemma* lift_mk_ring_hom_apply
- \+ *lemma* lift_unique
- \+ *lemma* eq_lift_comp_mk_ring_hom
- \+ *lemma* ring_quot_to_ideal_quotient_apply
- \+ *lemma* ideal_quotient_to_ring_quot_apply
- \+ *lemma* mk_alg_hom_coe
- \+ *lemma* mk_alg_hom_rel
- \+ *lemma* mk_alg_hom_surjective
- \+ *lemma* ring_quot_ext'
- \+ *lemma* lift_alg_hom_mk_alg_hom_apply
- \+ *lemma* lift_alg_hom_unique
- \+ *lemma* eq_lift_alg_hom_comp_mk_alg_hom
- \+ *theorem* rel.add_right
- \+ *theorem* rel.neg
- \+ *theorem* rel.smul
- \+ *def* ring_quot
- \+ *def* mk_ring_hom
- \+ *def* lift
- \+ *def* ring_quot_to_ideal_quotient
- \+ *def* ideal_quotient_to_ring_quot
- \+ *def* ring_quot_equiv_ideal_quotient
- \+ *def* mk_alg_hom
- \+ *def* lift_alg_hom

Modified src/data/equiv/ring.lean
- \+ *lemma* of_hom_inv_apply
- \+ *lemma* of_hom_inv_symm_apply
- \+ *def* of_hom_inv

Modified src/linear_algebra/basic.lean
- \+ *lemma* mem_Inf

Modified src/ring_theory/ideal/basic.lean
- \+ *def* of_rel



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
- \+ *lemma* measurable_comp
- \- *lemma* continuous_linear_map.measurable
- \- *lemma* measurable.clm_apply

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integrable.induction
- \+ *lemma* integrable_comp
- \+ *lemma* norm_comp_l1_apply_le
- \+ *lemma* comp_l1_apply
- \+ *lemma* integrable_comp_l1
- \+ *lemma* measurable_comp_l1
- \+ *lemma* integral_comp_l1
- \+ *lemma* norm_comp_l1_le
- \+ *lemma* norm_compl1L_le
- \+ *lemma* continuous_integral_comp_l1
- \+ *lemma* integral_comp_comm
- \+ *lemma* integral_comp_l1_comm
- \+ *def* comp_l1
- \+ *def* comp_l1ₗ
- \+ *def* comp_l1L



## [2020-09-18 20:21:39](https://github.com/leanprover-community/mathlib/commit/4e3729b)
feat(geometry/euclidean/basic): intersections of circles ([#4088](https://github.com/leanprover-community/mathlib/pull/4088))
Add two versions of the statement that two circles in two-dimensional
space intersect in at most two points, along with some lemmas involved
in the proof (some of which can be interpreted in terms of
intersections of circles or spheres and lines).
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* inner_vsub_vsub_of_dist_eq_of_dist_eq
- \+ *lemma* dist_smul_vadd_square
- \+ *lemma* dist_smul_vadd_eq_dist
- \+ *lemma* eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two
- \+ *lemma* eq_of_dist_eq_of_dist_eq_of_findim_eq_two



## [2020-09-18 17:25:27](https://github.com/leanprover-community/mathlib/commit/9051aa7)
feat(polynomial): prepare for transcendence of e by adding small lemmas ([#4175](https://github.com/leanprover-community/mathlib/pull/4175))
This will be a series of pull request to prepare for the proof of transcendence of e by adding lots of small lemmas.
#### Estimated changes
Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/coeff.lean
- \+ *lemma* not_mem_support_iff_coeff_zero

Modified src/data/polynomial/degree.lean
- \+ *lemma* eq_C_of_nat_degree_eq_zero

Modified src/data/polynomial/derivative.lean
- \+ *theorem* nat_degree_eq_zero_of_derivative_eq_zero



## [2020-09-18 11:37:08](https://github.com/leanprover-community/mathlib/commit/ae72826)
feat(data/mv_polynomial): define comap ([#4161](https://github.com/leanprover-community/mathlib/pull/4161))
More from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/category/CommRing/adjunctions.lean


Created src/data/mv_polynomial/comap.lean
- \+ *lemma* comap_apply
- \+ *lemma* comap_id_apply
- \+ *lemma* comap_id
- \+ *lemma* comap_comp_apply
- \+ *lemma* comap_comp
- \+ *lemma* comap_eq_id_of_eq_id
- \+ *lemma* comap_rename
- \+ *lemma* comap_equiv_coe
- \+ *lemma* comap_equiv_symm_coe

Modified src/data/mv_polynomial/rename.lean
- \+/\- *def* rename



## [2020-09-18 09:43:35](https://github.com/leanprover-community/mathlib/commit/953a5dc)
feat(category_theory/monoidal): monoid objects are just lax monoidal functors from punit ([#4121](https://github.com/leanprover-community/mathlib/pull/4121))
#### Estimated changes
Modified src/category_theory/monoidal/internal.lean
- \+ *def* lax_monoidal_to_Mon
- \+ *def* Mon_to_lax_monoidal
- \+ *def* unit_iso
- \+ *def* counit_iso
- \+ *def* equiv_lax_monoidal_functor_punit

Modified src/category_theory/monoidal/natural_transformation.lean
- \+ *lemma* comp_to_nat_trans'
- \+ *lemma* comp_to_nat_trans''
- \+ *lemma* of_components.hom_app
- \+ *lemma* of_components.inv_app
- \+ *def* of_components

Modified src/category_theory/natural_isomorphism.lean




## [2020-09-18 08:44:32](https://github.com/leanprover-community/mathlib/commit/c158ce8)
feat(analysis/calculus): converse mean value inequality  ([#4173](https://github.com/leanprover-community/mathlib/pull/4173))
Also restate mean value inequality in terms of `lipschitz_on_with`.
From the sphere eversion project.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.le_of_lip
- \+ *lemma* fderiv_at.le_of_lip

Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.lipschitz_on_with_of_norm_has_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_fderiv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_fderiv_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_has_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_deriv_within_le
- \+ *theorem* convex.lipschitz_on_with_of_norm_deriv_le

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_on_with_empty



## [2020-09-18 08:44:30](https://github.com/leanprover-community/mathlib/commit/f68c936)
feat(analysis/normed_space/real_inner_product): orthogonal subspace lemmas ([#4152](https://github.com/leanprover-community/mathlib/pull/4152))
Add a few more lemmas about `submodule.orthogonal`.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* submodule.orthogonal_le
- \+ *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \+ *lemma* submodule.findim_add_inf_findim_orthogonal



## [2020-09-18 08:44:28](https://github.com/leanprover-community/mathlib/commit/b00b01f)
feat(linear_algebra/affine_space): more lemmas ([#4127](https://github.com/leanprover-community/mathlib/pull/4127))
Add another batch of lemmas relating to affine spaces.  These include
factoring out `vector_span_mono` as a combination of two other lemmas
that's used several times, and additional variants of lemmas relating
to finite-dimensional subspaces.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* vector_span_mono
- \+ *lemma* eq_iff_direction_eq_of_mem
- \+ *lemma* eq_of_direction_eq_of_nonempty_of_le

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* findim_vector_span_image_finset_of_affine_independent
- \+/\- *lemma* findim_vector_span_of_affine_independent
- \+ *lemma* vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one



## [2020-09-18 07:44:06](https://github.com/leanprover-community/mathlib/commit/43ff7dc)
feat(topology/algebra/ordered): generalize two lemmas ([#4177](https://github.com/leanprover-community/mathlib/pull/4177))
they hold for conditionally complete linear orders, not just for complete linear orders
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *theorem* filter.tendsto.limsup_eq
- \+/\- *theorem* filter.tendsto.liminf_eq



## [2020-09-18 05:39:35](https://github.com/leanprover-community/mathlib/commit/58883e3)
feat(topology/ωCPO): define Scott topology in connection with ω-complete partial orders ([#4037](https://github.com/leanprover-community/mathlib/pull/4037))
#### Estimated changes
Modified src/control/lawful_fix.lean


Modified src/order/basic.lean
- \+ *def* as_linear_order

Modified src/order/bounded_lattice.lean
- \+ *lemma* le_iff_imp

Modified src/order/complete_lattice.lean
- \+ *theorem* Sup_le_Sup_of_forall_exists_le
- \+ *theorem* Inf_le_Inf_of_forall_exists_le

Modified src/order/lattice.lean
- \+ *lemma* le_sup_iff
- \+ *lemma* inf_le_iff

Modified src/order/omega_complete_partial_order.lean
- \+ *lemma* inf_continuous
- \+ *lemma* Sup_continuous
- \+ *lemma* sup_continuous
- \+ *lemma* top_continuous
- \+ *lemma* bot_continuous
- \+ *lemma* monotone
- \+ *theorem* Sup_continuous'

Modified src/order/preorder_hom.lean
- \+ *lemma* monotone

Modified src/tactic/monotonicity/basic.lean


Created src/topology/omega_complete_partial_order.lean
- \+ *lemma* not_below_is_open
- \+ *lemma* is_ωSup_ωSup
- \+ *lemma* Scott_continuous_of_continuous
- \+ *lemma* continuous_of_Scott_continuous
- \+ *theorem* is_open_univ
- \+ *theorem* is_open_inter
- \+ *theorem* is_open_sUnion
- \+ *def* is_ωSup
- \+ *def* is_open
- \+ *def* Scott
- \+ *def* not_below



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
Created src/deprecated/subfield.lean
- \+ *lemma* is_subfield_Union_of_directed
- \+ *theorem* ring_closure_subset
- \+ *theorem* mem_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_subset_iff
- \+ *theorem* closure_mono
- \+ *def* closure

Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/subfield.lean
- \+ *lemma* coe_to_subring
- \+ *lemma* mem_mk
- \+ *lemma* mem_to_subring
- \+ *lemma* list_prod_mem
- \+ *lemma* list_sum_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* multiset_sum_mem
- \+ *lemma* prod_mem
- \+ *lemma* sum_mem
- \+ *lemma* pow_mem
- \+ *lemma* gsmul_mem
- \+ *lemma* coe_int_mem
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* mem_to_submonoid
- \+ *lemma* coe_to_submonoid
- \+ *lemma* mem_to_add_subgroup
- \+ *lemma* coe_to_add_subgroup
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* coe_field_range
- \+ *lemma* mem_field_range
- \+ *lemma* map_field_range
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* Inf_to_subring
- \+ *lemma* is_glb_Inf
- \+ *lemma* mem_closure_iff
- \+ *lemma* subring_closure_le
- \+ *lemma* subset_closure
- \+ *lemma* mem_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* closure_sUnion
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* coe_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_Sup_of_directed_on
- \+ *lemma* restrict_field_apply
- \+ *lemma* coe_range_restrict_field
- \+ *lemma* eq_on_field_closure
- \+ *lemma* eq_of_eq_on_subfield_top
- \+ *lemma* eq_of_eq_on_of_field_closure_eq_top
- \+ *lemma* field_closure_preimage_le
- \+ *lemma* map_field_closure
- \+ *lemma* field_range_subtype
- \+ *lemma* closure_preimage_le
- \- *lemma* is_subfield_Union_of_directed
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* zero_mem
- \+ *theorem* mul_mem
- \+ *theorem* add_mem
- \+ *theorem* neg_mem
- \+ *theorem* inv_mem
- \+ *theorem* div_mem
- \+ *theorem* coe_subtype
- \- *theorem* ring_closure_subset
- \- *theorem* mem_closure
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* closure_subset_iff
- \- *theorem* closure_mono
- \+ *def* to_add_subgroup
- \+ *def* to_submonoid
- \+ *def* subring.to_subfield
- \+ *def* subtype
- \+ *def* comap
- \+ *def* map
- \+ *def* field_range
- \+/\- *def* closure
- \+ *def* cod_restrict_field
- \+ *def* restrict_field
- \+ *def* range_restrict_field
- \+ *def* eq_locus_field
- \+ *def* inclusion
- \+ *def* subfield_congr

Modified src/ring_theory/subring.lean
- \+ *lemma* coe_eq_zero_iff



## [2020-09-17 15:33:35](https://github.com/leanprover-community/mathlib/commit/34ebade)
feat(algebra/free_algebra): free (noncommutative) algebras ([#4077](https://github.com/leanprover-community/mathlib/pull/4077))
Previously, @adamtopaz constructed the tensor algebra of an `R`-module via a direct construction of a quotient of a free algebra.
This uses essentially the same construction to build a free algebra (on a type) directly. In a PR coming shortly, I'll refactor his development of the tensor algebra to use this construction.
#### Estimated changes
Created src/algebra/free_algebra.lean
- \+ *lemma* quot_mk_eq_ι
- \+ *theorem* ι_comp_lift
- \+ *theorem* lift_ι_apply
- \+ *theorem* lift_unique
- \+ *theorem* lift_comp_ι
- \+ *theorem* hom_ext
- \+ *def* has_coe_generator
- \+ *def* has_coe_semiring
- \+ *def* has_mul
- \+ *def* has_add
- \+ *def* has_zero
- \+ *def* has_one
- \+ *def* has_scalar
- \+ *def* lift_fun
- \+ *def* free_algebra
- \+ *def* ι
- \+ *def* lift
- \+ *def* equiv_monoid_algebra_free_monoid

Modified src/data/monoid_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean




## [2020-09-17 14:29:36](https://github.com/leanprover-community/mathlib/commit/b62dd28)
feat(linear_algebra/eigenspace): beginning to relate minimal polynomials to eigenvalues ([#4165](https://github.com/leanprover-community/mathlib/pull/4165))
rephrases some lemmas in `linear_algebra` to use `aeval` instead of `eval2` and `algebra_map`
shows that an eigenvalue of a linear transformation is a root of its minimal polynomial, and vice versa
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_endomorphism

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* eigenspace_aeval_polynomial_degree_1
- \+ *lemma* ker_aeval_ring_hom'_unit_polynomial
- \- *lemma* eigenspace_eval₂_polynomial_degree_1
- \- *lemma* ker_eval₂_ring_hom'_unit_polynomial
- \+ *theorem* aeval_apply_of_has_eigenvector
- \+ *theorem* is_root_of_has_eigenvalue
- \+ *theorem* has_eigenvalue_of_is_root
- \+ *theorem* has_eigenvalue_iff_is_root

Modified src/linear_algebra/matrix.lean
- \+ *lemma* findim_linear_map

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
- \+ *lemma* alg_hom_ext
- \+ *lemma* alg_hom_ext_iff



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
- \+/\- *lemma* mem_vars
- \+ *lemma* vars_mul
- \+ *lemma* vars_one
- \+ *lemma* vars_pow
- \+ *lemma* vars_prod
- \+ *lemma* vars_C_mul



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
- \- *lemma* coe_to_alg_hom

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
- \+ *lemma* lipschitz_on_with_iff_norm_sub_le
- \+ *lemma* lipschitz_on_with.norm_sub_le

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniform_continuous_on_iff

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_on_with.mono
- \+ *lemma* lipschitz_on_with_iff_dist_le_mul
- \+ *lemma* lipschitz_on_univ
- \+ *lemma* lipschitz_on_with_iff_restrict
- \+ *def* lipschitz_on_with

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.has_basis.uniform_continuous_on_iff
- \+/\- *lemma* uniform_continuous_on_iff_restrict
- \+ *lemma* uniform_continuous_on.continuous_on



## [2020-09-16 08:03:26](https://github.com/leanprover-community/mathlib/commit/4c9d3a5)
feat(operator_norm): smul_right lemmas ([#4150](https://github.com/leanprover-community/mathlib/pull/4150))
from the sphere eversion project
We need a version of `continuous_linear_map.smul_right` that is itself a continuous linear map from a normed space to a space of continuous linear maps. 
breaking changes:
* rename `smul_right_norm` to `norm_smul_right_apply`
* in `homothety_norm` remove useless sign assumption and switch from assuming positive dimension to `nontrivial`
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* homothety_norm
- \+ *lemma* norm_smul_right_apply
- \+ *lemma* norm_smul_rightL_apply
- \+ *lemma* norm_smul_rightL
- \+ *lemma* continuous_applyₗ
- \- *lemma* smul_right_norm
- \+ *def* smul_rightL
- \+ *def* applyₗ
- \+ *def* apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* nontrivial_span_singleton

Modified src/topology/algebra/module.lean
- \+ *def* smul_rightₗ



## [2020-09-16 06:06:09](https://github.com/leanprover-community/mathlib/commit/f585ce5)
feat(category_theory): monoidal natural transformations and discrete monoidal categories ([#4112](https://github.com/leanprover-community/mathlib/pull/4112))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *theorem* congr_fun
- \+ *theorem* congr_arg

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* map_div

Modified src/algebra/ring/basic.lean
- \+ *theorem* congr_fun
- \+ *theorem* congr_arg

Modified src/category_theory/discrete_category.lean
- \+ *lemma* eq_of_hom

Modified src/category_theory/limits/lattice.lean


Created src/category_theory/monoidal/discrete.lean
- \+ *def* discrete.monoidal_functor
- \+ *def* discrete.monoidal_functor_comp

Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *def* map_Mon_functor

Created src/category_theory/monoidal/natural_transformation.lean
- \+ *def* id
- \+ *def* vcomp
- \+ *def* hcomp

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
- \+/\- *lemma* any_functor_const_on_obj
- \+ *lemma* is_connected.of_any_functor_const_on_obj
- \+/\- *lemma* constant_of_preserves_morphisms
- \+ *lemma* is_connected.of_constant_of_preserves_morphisms
- \+/\- *lemma* induct_on_objects
- \+ *lemma* is_connected.of_induct
- \+/\- *lemma* equiv_relation
- \+ *lemma* is_connected_zigzag
- \+ *lemma* zigzag_is_connected
- \+/\- *lemma* exists_zigzag'
- \+ *lemma* is_connected_of_zigzag
- \+ *lemma* nat_trans_from_is_connected
- \- *lemma* connected_zigzag
- \- *lemma* nat_trans_from_connected
- \+ *def* iso_constant
- \+ *def* discrete_is_connected_equiv_punit
- \- *def* connected.of_any_functor_const_on_obj
- \- *def* connected.of_constant_of_preserves_morphisms
- \- *def* connected.of_induct
- \- *def* zigzag_connected
- \- *def* connected_of_zigzag
- \- *def* discrete_connected_equiv_punit

Modified src/category_theory/limits/connected.lean
- \+/\- *def* prod_preserves_connected_limits

Modified src/category_theory/limits/shapes/constructions/over/connected.lean
- \+/\- *lemma* raised_cone_lowers_to_original
- \+/\- *def* raise_cone
- \+/\- *def* raised_cone_is_limit



## [2020-09-15 11:43:08](https://github.com/leanprover-community/mathlib/commit/427d414)
feat(data/enat): some API and a module docstring ([#4103](https://github.com/leanprover-community/mathlib/pull/4103))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* to_with_top_add



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
- \+ *lemma* comp_zero
- \+ *lemma* zero_comp

Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/preadditive/schur.lean




## [2020-09-14 23:27:30](https://github.com/leanprover-community/mathlib/commit/3d73bd8)
feat(topology/algebra/ordered): monotone continuous function is homeomorphism, relative version ([#4043](https://github.com/leanprover-community/mathlib/pull/4043))
A function `f : α → β` restricts to a homeomorphism `(Ioo a b) → β`, if it (1) is order-preserving within the interval; (2) is `continuous_on` the interval; (3) tends to positive infinity at the right endpoint; and (4) tends to negative infinity at the left endpoint. The orders `α`, `β` are required to be conditionally complete, and the order on `α` must also be dense.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* nonempty_Icc_subtype
- \+ *lemma* nonempty_Ico_subtype
- \+ *lemma* nonempty_Ioc_subtype
- \+ *lemma* nonempty_Ioo_subtype

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Ioo_at_top_eq_nhds_within
- \+ *lemma* Ioo_at_bot_eq_nhds_within
- \+ *lemma* coe_homeomorph_of_strict_mono_continuous_Ioo



## [2020-09-14 21:25:17](https://github.com/leanprover-community/mathlib/commit/ff2639d)
feat(tactic/pretty_cases): provide a skeleton for a proof by induction / cases ([#4093](https://github.com/leanprover-community/mathlib/pull/4093))
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Created src/tactic/pretty_cases.lean


Created test/pretty_cases.lean




## [2020-09-14 19:35:47](https://github.com/leanprover-community/mathlib/commit/218ef40)
feat(measure_theory): image of Lebesgue measure under shift/rescale ([#3760](https://github.com/leanprover-community/mathlib/pull/3760))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* supr_option_to_finset
- \+ *lemma* infi_option_to_finset
- \+ *lemma* supr_bind
- \+ *lemma* infi_bind
- \+ *lemma* bUnion_option_to_finset
- \+ *lemma* bInter_option_to_finset
- \+ *lemma* bUnion_bind
- \+ *lemma* bInter_bind

Modified src/data/indicator_function.lean
- \+ *lemma* indicator_Union_apply

Modified src/data/set/basic.lean
- \+ *theorem* set_coe.forall'

Modified src/data/set/disjointed.lean
- \+ *lemma* subset_Union_disjointed
- \+/\- *lemma* Union_disjointed
- \+/\- *lemma* Union_disjointed_of_mono

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measure_ext_Ioo_rat

Modified src/measure_theory/integration.lean
- \+ *lemma* set_lintegral_one
- \+ *lemma* set_lintegral_congr
- \+ *lemma* set_lintegral_map

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* integral_smul_measure
- \+ *lemma* integral_comp_add_right
- \+ *lemma* integral_comp_mul_right
- \+ *lemma* integral_comp_neg

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* volume_Ico
- \+ *lemma* volume_Icc
- \+ *lemma* volume_Ioo
- \+ *lemma* volume_Ioc
- \+ *lemma* volume_singleton
- \+ *lemma* volume_interval
- \+ *lemma* map_volume_add_left
- \+ *lemma* map_volume_add_right
- \+ *lemma* smul_map_volume_mul_left
- \+ *lemma* map_volume_mul_left
- \+ *lemma* smul_map_volume_mul_right
- \+ *lemma* map_volume_mul_right
- \+ *lemma* map_volume_neg
- \- *lemma* real.volume_Ico
- \- *lemma* real.volume_Icc
- \- *lemma* real.volume_Ioo
- \- *lemma* real.volume_Ioc
- \- *lemma* real.volume_singleton
- \- *lemma* real.volume_interval
- \+ *theorem* volume_val
- \- *theorem* real.volume_val

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.bUnion_decode2
- \+/\- *lemma* is_measurable.Union
- \+/\- *lemma* is_measurable.union
- \+/\- *lemma* is_measurable.inter
- \+/\- *lemma* is_measurable.diff
- \+/\- *lemma* is_measurable.disjointed
- \+/\- *lemma* is_measurable.const

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_mono_top
- \+/\- *lemma* measure_diff
- \+ *lemma* measure_Union_eq_supr
- \+ *lemma* measure_bUnion_eq_supr
- \+ *lemma* measure_Inter_eq_infi
- \+/\- *lemma* measure_eq_inter_diff
- \+ *lemma* measure_union_add_inter
- \+ *lemma* restrict_restrict
- \+ *lemma* restrict_union_add_inter
- \+ *lemma* restrict_Union_apply_eq_supr
- \+ *lemma* restrict_map
- \+ *lemma* restrict_congr_meas
- \+ *lemma* restrict_congr_mono
- \+ *lemma* restrict_union_congr
- \+ *lemma* restrict_finset_bUnion_congr
- \+ *lemma* restrict_Union_congr
- \+ *lemma* restrict_bUnion_congr
- \+ *lemma* restrict_sUnion_congr
- \+ *lemma* ext_iff_of_Union_eq_univ
- \+ *lemma* ext_iff_of_bUnion_eq_univ
- \+ *lemma* ext_iff_of_sUnion_eq_univ
- \+ *lemma* ext_of_generate_from_of_cover
- \+ *lemma* ext_of_generate_from_of_cover_subset
- \+ *lemma* ae_eq_empty
- \+ *lemma* ae_le_set
- \+ *lemma* union_ae_eq_right
- \+ *lemma* diff_ae_eq_self
- \+ *lemma* restrict_congr_set
- \+ *lemma* measure_countable
- \+ *lemma* measure_finite
- \+ *lemma* measure_finset
- \+ *lemma* insert_ae_eq_self
- \+ *lemma* Iio_ae_eq_Iic
- \+ *lemma* Ioi_ae_eq_Ici
- \+ *lemma* Ioo_ae_eq_Ioc
- \+ *lemma* Ioc_ae_eq_Icc
- \+ *lemma* Ioo_ae_eq_Ico
- \+ *lemma* Ioo_ae_eq_Icc
- \+ *lemma* Ico_ae_eq_Icc
- \+ *lemma* Ico_ae_eq_Ioc
- \- *lemma* measure_Union_eq_supr_nat
- \- *lemma* measure_Inter_eq_infi_nat
- \- *lemma* restrict_congr

Modified src/measure_theory/set_integral.lean
- \+ *lemma* set_integral_map

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq.inter
- \+ *lemma* eventually_eq.union
- \+ *lemma* eventually_eq.compl
- \+ *lemma* eventually_eq.diff
- \+ *lemma* eventually_eq_empty
- \+ *lemma* eventually_le_antisymm_iff



## [2020-09-14 16:35:45](https://github.com/leanprover-community/mathlib/commit/a18be37)
feat(ring_theory/ideal/over): Going up theorem for integral extensions ([#4064](https://github.com/leanprover-community/mathlib/pull/4064))
The main statement is `exists_ideal_over_prime_of_is_integral` which shows that for an integral extension, every prime ideal of the original ring lies under some prime ideal of the extension ring.
`is_field_of_is_integral_of_is_field` is a brute force proof that if `R → S` is an integral extension, and `S` is a field, then `R` is also a field (using the somewhat new `is_field` proposition). `is_maximal_comap_of_is_integral_of_is_maximal` Gives essentially the same statement in terms of maximal ideals.
`disjoint_compl` has also been replaced with `disjoint_compl_left` and `disjoint_compl_right` variants.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_eq_sum_range

Modified src/data/set/lattice.lean
- \+ *theorem* disjoint_compl_left
- \+ *theorem* disjoint_compl_right
- \- *theorem* disjoint_compl

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/matrix.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/set_integral.lean


Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* algebra_map_quotient_injective
- \+ *def* quotient_map

Modified src/ring_theory/ideal/over.lean
- \+ *lemma* is_maximal_comap_of_is_integral_of_is_maximal
- \+ *lemma* exists_ideal_over_prime_of_is_integral'
- \+ *theorem* exists_ideal_over_prime_of_is_integral

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_quotient_of_is_integral
- \+ *lemma* is_field_of_is_integral_of_is_field

Modified src/ring_theory/localization.lean
- \+ *lemma* at_prime.map_eq_maximal_ideal
- \+ *lemma* at_prime.comap_maximal_ideal
- \+ *lemma* algebra_map_mk'
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
- \+ *lemma* continuous_integral
- \+ *lemma* l1.integral_eq_integral
- \+ *lemma* l1.integral_of_fun_eq_integral
- \+ *lemma* l1.norm_eq_integral_norm
- \+ *lemma* l1.norm_of_fun_eq_integral_norm

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.const_mul
- \+ *lemma* measurable.mul_const
- \+ *lemma* continuous_linear_map.measurable
- \+ *lemma* measurable.clm_apply

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.const_mul
- \+ *lemma* integrable.mul_const
- \+ *lemma* measurable_norm
- \+ *lemma* integrable_norm

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integral_indicator_const



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
- \+ *lemma* finite_dimensional_of_le
- \+ *lemma* linear_independent_iff_card_eq_findim_span
- \+/\- *theorem* dim_sup_add_dim_inf_eq



## [2020-09-14 14:48:27](https://github.com/leanprover-community/mathlib/commit/d5c58eb)
chore(category_theory/*): make all forgetful functors use explicit arguments ([#4139](https://github.com/leanprover-community/mathlib/pull/4139))
As suggested as https://github.com/leanprover-community/mathlib/pull/4131#discussion_r487527599, for the sake of more uniform API.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/grothendieck.lean


Modified src/category_theory/limits/over.lean
- \+/\- *def* to_cocone
- \+/\- *def* to_cone
- \+/\- *def* colimit
- \+/\- *def* forget_colimit_is_colimit
- \+/\- *def* limit
- \+/\- *def* forget_limit_is_limit

Modified src/category_theory/limits/shapes/constructions/over/connected.lean
- \+/\- *def* raise_cone
- \+/\- *def* raised_cone_is_limit

Modified src/category_theory/monad/bundled.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *def* forget

Modified src/category_theory/over.lean
- \+/\- *lemma* forget_obj
- \+/\- *lemma* forget_map



## [2020-09-14 12:41:02](https://github.com/leanprover-community/mathlib/commit/a998fd1)
feat(algebra/category/Module): the monoidal category of R-modules is symmetric ([#4140](https://github.com/leanprover-community/mathlib/pull/4140))
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* braiding_naturality
- \+ *lemma* hexagon_forward
- \+ *lemma* hexagon_reverse
- \+ *lemma* braiding_hom_apply
- \+ *lemma* braiding_inv_apply
- \+ *def* braiding



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
- \+/\- *lemma* one_lt_iff_ne_zero_and_ne_one
- \+/\- *lemma* eq_zero_of_double_le
- \+/\- *lemma* eq_zero_of_mul_le
- \+/\- *lemma* zero_max
- \+/\- *lemma* one_le_of_lt
- \+/\- *lemma* exists_eq_add_of_le
- \+/\- *lemma* exists_eq_add_of_lt
- \+/\- *lemma* add_eq_one_iff
- \+/\- *lemma* pred_eq_succ_iff
- \+/\- *lemma* mul_eq_one_iff
- \+/\- *lemma* mul_right_eq_self_iff
- \+/\- *lemma* mul_left_eq_self_iff
- \+/\- *lemma* lt_succ_iff_lt_or_eq
- \+/\- *lemma* le_induction
- \+/\- *lemma* decreasing_induction_self
- \+/\- *lemma* decreasing_induction_succ
- \+/\- *lemma* decreasing_induction_succ'
- \+/\- *lemma* decreasing_induction_trans
- \+/\- *lemma* decreasing_induction_succ_left
- \+/\- *lemma* two_mul_odd_div_two
- \+/\- *lemma* div_dvd_of_dvd
- \+/\- *lemma* dvd_div_of_mul_dvd
- \+/\- *lemma* mul_dvd_of_dvd_div
- \+/\- *lemma* div_mul_div
- \+/\- *lemma* div_div_div_eq_div
- \+/\- *lemma* eq_of_dvd_of_div_eq_one
- \+/\- *lemma* eq_zero_of_dvd_of_div_eq_zero
- \+/\- *lemma* eq_zero_of_dvd_of_lt
- \+/\- *lemma* div_le_div_left
- \+/\- *lemma* div_eq_self
- \+/\- *lemma* pow_left_strict_mono
- \+/\- *lemma* pow_le_iff_le_left
- \+/\- *lemma* pow_dvd_pow_iff_pow_le_pow
- \+/\- *lemma* pow_dvd_pow_iff_le_right
- \+/\- *lemma* pow_dvd_pow_iff_le_right'
- \+/\- *lemma* pow_dvd_of_le_of_pow_dvd
- \+/\- *lemma* dvd_of_pow_dvd
- \+/\- *lemma* find_eq_zero
- \+/\- *lemma* find_pos
- \+/\- *lemma* find_greatest_zero
- \+/\- *lemma* find_greatest_eq
- \+/\- *lemma* find_greatest_of_not
- \+/\- *lemma* find_greatest_spec_and_le
- \+/\- *lemma* find_greatest_spec
- \+/\- *lemma* find_greatest_le
- \+/\- *lemma* le_find_greatest
- \+/\- *lemma* find_greatest_is_greatest
- \+/\- *lemma* find_greatest_eq_zero
- \+/\- *lemma* find_greatest_of_ne_zero
- \+/\- *lemma* bit0_le_bit1_iff
- \+/\- *lemma* bit0_lt_bit1_iff
- \+/\- *lemma* bit1_le_bit0_iff
- \+/\- *lemma* bit1_lt_bit0_iff
- \+/\- *lemma* one_le_bit0_iff
- \+/\- *lemma* one_lt_bit0_iff
- \+/\- *lemma* bit_le_bit_iff
- \+/\- *lemma* bit_lt_bit_iff
- \+/\- *lemma* bit_le_bit1_iff
- \+/\- *lemma* pos_of_bit0_pos
- \- *lemma* triangle_succ
- \- *lemma* fact_mul_pow_le_fact
- \- *lemma* monotone_fact
- \- *lemma* fact_lt
- \- *lemma* one_lt_fact
- \- *lemma* fact_eq_one
- \- *lemma* fact_inj
- \- *lemma* choose_zero_right
- \- *lemma* choose_zero_succ
- \- *lemma* choose_succ_succ
- \- *lemma* choose_eq_zero_of_lt
- \- *lemma* choose_self
- \- *lemma* choose_succ_self
- \- *lemma* choose_one_right
- \- *lemma* choose_two_right
- \- *lemma* choose_pos
- \- *lemma* succ_mul_choose_eq
- \- *lemma* choose_mul_fact_mul_fact
- \- *lemma* choose_symm
- \- *lemma* choose_symm_of_eq_add
- \- *lemma* choose_symm_add
- \- *lemma* choose_symm_half
- \- *lemma* choose_succ_right_eq
- \- *lemma* choose_succ_self_right
- \- *lemma* choose_mul_succ_eq
- \- *lemma* with_bot.add_eq_zero_iff
- \- *lemma* with_bot.add_eq_one_iff
- \- *lemma* with_bot.coe_nonneg
- \- *lemma* with_bot.lt_zero_iff
- \- *lemma* pow_le_iff_le_log
- \- *lemma* log_pow
- \- *lemma* pow_succ_log_gt_self
- \- *lemma* pow_log_le_self
- \+ *theorem* nat.eq_of_mul_eq_mul_right
- \+/\- *theorem* units_eq_one
- \+/\- *theorem* add_units_eq_zero
- \+/\- *theorem* pos_iff_ne_zero
- \+/\- *theorem* le_zero_iff
- \+/\- *theorem* eq_of_lt_succ_of_not_lt
- \+/\- *theorem* one_add
- \+/\- *theorem* add_def
- \+/\- *theorem* mul_def
- \+/\- *theorem* add_pos_left
- \+/\- *theorem* add_pos_right
- \+/\- *theorem* add_pos_iff_pos_or_pos
- \+/\- *theorem* le_add_one_iff
- \+/\- *theorem* pred_eq_of_eq_succ
- \+/\- *theorem* pred_sub
- \+/\- *theorem* mul_self_le_mul_self
- \+/\- *theorem* mul_self_lt_mul_self
- \+/\- *theorem* mul_self_le_mul_self_iff
- \+/\- *theorem* mul_self_lt_mul_self_iff
- \+/\- *theorem* le_mul_self
- \+/\- *theorem* mul_self_inj
- \+/\- *theorem* le_rec_on_self
- \+/\- *theorem* le_rec_on_succ
- \+/\- *theorem* le_rec_on_succ'
- \+/\- *theorem* le_rec_on_trans
- \+/\- *theorem* le_rec_on_succ_left
- \+/\- *theorem* le_rec_on_injective
- \+/\- *theorem* le_rec_on_surjective
- \+/\- *theorem* strong_rec_on_beta'
- \+/\- *theorem* mod_pow_succ
- \+/\- *theorem* pow_dvd_pow
- \+/\- *theorem* pow_dvd_pow_of_dvd
- \+/\- *theorem* bit_le
- \+/\- *theorem* bit_ne_zero
- \+/\- *theorem* bit0_le_bit
- \+/\- *theorem* bit_le_bit1
- \+/\- *theorem* bit_lt_bit0
- \+/\- *theorem* bit_lt_bit
- \- *theorem* eq_of_mul_eq_mul_right
- \- *theorem* pred_eq_ppred
- \- *theorem* sub_eq_psub
- \- *theorem* ppred_eq_some
- \- *theorem* ppred_eq_none
- \- *theorem* psub_eq_some
- \- *theorem* psub_eq_none
- \- *theorem* ppred_eq_pred
- \- *theorem* psub_eq_sub
- \- *theorem* psub_add
- \- *theorem* fact_zero
- \- *theorem* fact_succ
- \- *theorem* fact_one
- \- *theorem* fact_pos
- \- *theorem* fact_ne_zero
- \- *theorem* fact_dvd_fact
- \- *theorem* dvd_fact
- \- *theorem* fact_le
- \- *theorem* choose_eq_fact_div_fact
- \- *theorem* fact_mul_fact_dvd_fact
- \+/\- *def* le_rec_on
- \+/\- *def* strong_rec_on'
- \+/\- *def* decreasing_induction
- \+/\- *def* bit_cases
- \- *def* ppred
- \- *def* psub
- \- *def* fact
- \- *def* choose
- \- *def* log

Deleted src/data/nat/choose.lean
- \- *lemma* nat.prime.dvd_choose_add
- \- *lemma* nat.prime.dvd_choose_self
- \- *lemma* choose_le_succ_of_lt_half_left
- \- *lemma* choose_le_middle
- \- *lemma* sum_range_choose_halfway
- \- *lemma* choose_middle_le_pow
- \- *theorem* commute.add_pow
- \- *theorem* add_pow
- \- *theorem* sum_range_choose

Created src/data/nat/choose/basic.lean
- \+ *lemma* choose_zero_right
- \+ *lemma* choose_zero_succ
- \+ *lemma* choose_succ_succ
- \+ *lemma* choose_eq_zero_of_lt
- \+ *lemma* choose_self
- \+ *lemma* choose_succ_self
- \+ *lemma* choose_one_right
- \+ *lemma* triangle_succ
- \+ *lemma* choose_two_right
- \+ *lemma* choose_pos
- \+ *lemma* succ_mul_choose_eq
- \+ *lemma* choose_mul_fact_mul_fact
- \+ *lemma* choose_symm
- \+ *lemma* choose_symm_of_eq_add
- \+ *lemma* choose_symm_add
- \+ *lemma* choose_symm_half
- \+ *lemma* choose_succ_right_eq
- \+ *lemma* choose_succ_self_right
- \+ *lemma* choose_mul_succ_eq
- \+ *lemma* choose_le_succ_of_lt_half_left
- \+ *lemma* choose_le_middle
- \+ *theorem* choose_eq_fact_div_fact
- \+ *theorem* fact_mul_fact_dvd_fact
- \+ *def* choose

Created src/data/nat/choose/default.lean


Created src/data/nat/choose/dvd.lean
- \+ *lemma* dvd_choose_add
- \+ *lemma* dvd_choose_self

Created src/data/nat/choose/sum.lean
- \+ *lemma* sum_range_choose_halfway
- \+ *lemma* choose_middle_le_pow
- \+ *theorem* commute.add_pow
- \+ *theorem* add_pow
- \+ *theorem* sum_range_choose

Created src/data/nat/fact.lean
- \+ *lemma* fact_mul_pow_le_fact
- \+ *lemma* monotone_fact
- \+ *lemma* fact_lt
- \+ *lemma* one_lt_fact
- \+ *lemma* fact_eq_one
- \+ *lemma* fact_inj
- \+ *theorem* fact_zero
- \+ *theorem* fact_succ
- \+ *theorem* fact_one
- \+ *theorem* fact_pos
- \+ *theorem* fact_ne_zero
- \+ *theorem* fact_dvd_fact
- \+ *theorem* dvd_fact
- \+ *theorem* fact_le
- \+ *def* fact

Modified src/data/nat/gcd.lean


Created src/data/nat/log.lean
- \+ *lemma* pow_le_iff_le_log
- \+ *lemma* log_pow
- \+ *lemma* pow_succ_log_gt_self
- \+ *lemma* pow_log_le_self
- \+ *def* log

Modified src/data/nat/multiplicity.lean


Created src/data/nat/psub.lean
- \+ *theorem* pred_eq_ppred
- \+ *theorem* sub_eq_psub
- \+ *theorem* ppred_eq_some
- \+ *theorem* ppred_eq_none
- \+ *theorem* psub_eq_some
- \+ *theorem* psub_eq_none
- \+ *theorem* ppred_eq_pred
- \+ *theorem* psub_eq_sub
- \+ *theorem* psub_add
- \+ *def* ppred
- \+ *def* psub

Modified src/data/nat/sqrt.lean


Created src/data/nat/with_bot.lean
- \+ *lemma* with_bot.add_eq_zero_iff
- \+ *lemma* with_bot.add_eq_one_iff
- \+ *lemma* with_bot.coe_nonneg
- \+ *lemma* with_bot.lt_zero_iff

Modified src/data/num/lemmas.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/number_theory/primorial.lean


Modified src/ring_theory/ideal/operations.lean




## [2020-09-14 11:13:26](https://github.com/leanprover-community/mathlib/commit/39962b7)
chore(data/polynomial/derivative): golf proof of mem_support_derivative ([#4134](https://github.com/leanprover-community/mathlib/pull/4134))
Golfed proof to be similar to what it was like prior to the refactor.
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* mem_support_iff_coeff_ne_zero

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
Created src/data/mv_polynomial/monad.lean
- \+ *lemma* aeval_eq_bind₁
- \+ *lemma* eval₂_hom_C_eq_bind₁
- \+ *lemma* eval₂_hom_eq_bind₂
- \+ *lemma* aeval_id_eq_join₁
- \+ *lemma* eval₂_hom_C_id_eq_join₁
- \+ *lemma* eval₂_hom_id_X_eq_join₂
- \+ *lemma* bind₁_X_right
- \+ *lemma* bind₂_X_right
- \+ *lemma* bind₁_X_left
- \+ *lemma* aeval_X_left
- \+ *lemma* aeval_X_left_apply
- \+ *lemma* bind₁_C_right
- \+ *lemma* bind₂_C_left
- \+ *lemma* bind₂_C_right
- \+ *lemma* bind₂_comp_C
- \+ *lemma* join₂_map
- \+ *lemma* join₂_comp_map
- \+ *lemma* aeval_rename
- \+ *lemma* join₁_rename
- \+ *lemma* bind₁_id
- \+ *lemma* bind₂_id
- \+ *lemma* bind₁_bind₁
- \+ *lemma* bind₁_comp_bind₁
- \+ *lemma* bind₂_bind₂
- \+ *lemma* bind₂_comp_bind₂
- \+ *lemma* rename_bind₁
- \+ *lemma* map_bind₂
- \+ *lemma* bind₁_rename
- \+ *lemma* bind₂_map
- \+ *lemma* map_comp_C
- \+ *lemma* hom_bind₁
- \+ *lemma* map_bind₁
- \+ *lemma* eval₂_hom_comp_C
- \+ *lemma* eval₂_hom_bind₁
- \+ *lemma* aeval_bind₁
- \+ *lemma* aeval_comp_bind₁
- \+ *lemma* eval₂_hom_bind₂
- \+ *lemma* eval₂_hom_comp_bind₂
- \+ *lemma* aeval_bind₂
- \+ *lemma* eval₂_hom_C_left
- \+ *lemma* bind₁_monomial
- \+ *lemma* bind₂_monomial
- \+ *lemma* bind₂_monomial_one
- \+ *def* bind₁
- \+ *def* bind₂
- \+ *def* join₁
- \+ *def* join₂
- \+ *def* bind
- \+ *def* join
- \+ *def* ajoin



## [2020-09-14 09:42:28](https://github.com/leanprover-community/mathlib/commit/ed71b2d)
feat(computability/tm_computable): define computable (in polytime) for TMs, prove id is computable in constant time  ([#4048](https://github.com/leanprover-community/mathlib/pull/4048))
We define computability in polynomial time to be used in our future PR on P and NP.
We also prove that id is computable in constant time.
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Created src/computability/tm_computable.lean
- \+ *def* stmt
- \+ *def* cfg
- \+ *def* step
- \+ *def* init_list
- \+ *def* halt_list
- \+ *def* evals_to.refl
- \+ *def* evals_to.trans
- \+ *def* evals_to_in_time.refl
- \+ *def* evals_to_in_time.trans
- \+ *def* tm2_outputs
- \+ *def* tm2_outputs_in_time
- \+ *def* tm2_outputs_in_time.to_tm2_outputs
- \+ *def* tm2_computable_in_time.to_tm2_computable
- \+ *def* tm2_computable_in_poly_time.to_tm2_computable_in_time
- \+ *def* id_computer
- \+ *def* id_computable_in_poly_time
- \+ *def* id_computable_in_time
- \+ *def* id_computable



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
Created src/algebra/big_operators/finsupp.lean
- \+ *theorem* finset.sum_apply'
- \+ *theorem* finsupp.sum_apply'
- \+ *theorem* finsupp.sum_sum_index'

Modified src/algebra/group_ring_action.lean
- \+ *theorem* eq_of_smul_eq_smul
- \+ *theorem* injective_to_semiring_hom

Modified src/data/set/function.lean
- \+ *theorem* inj_on_insert

Modified src/field_theory/fixed.lean
- \+ *lemma* linear_independent_smul_of_linear_independent
- \+ *lemma* dim_le_card
- \+ *lemma* findim_le_card
- \+ *lemma* linear_independent_to_linear_map
- \+ *lemma* cardinal_mk_alg_hom
- \+ *lemma* findim_alg_hom
- \+ *lemma* coe_to_alg_hom
- \+ *lemma* to_alg_hom_apply
- \+ *theorem* smul
- \+ *theorem* smul_polynomial
- \+ *theorem* coe_algebra_map
- \+ *theorem* monic
- \+ *theorem* eval₂
- \+ *theorem* ne_one
- \+ *theorem* of_eval₂
- \+ *theorem* irreducible_aux
- \+ *theorem* irreducible
- \+ *theorem* is_integral
- \+ *theorem* minpoly.minimal_polynomial
- \+ *theorem* findim_eq_card
- \- *theorem* fixed_points.smul
- \- *theorem* fixed_points.smul_polynomial
- \- *theorem* fixed_points.coe_algebra_map
- \- *theorem* fixed_points.minpoly.monic
- \- *theorem* fixed_points.minpoly.eval₂
- \- *theorem* fixed_points.is_integral
- \- *theorem* fixed_points.minpoly.ne_one
- \- *theorem* fixed_points.of_eval₂
- \- *theorem* fixed_points.minpoly.irreducible_aux
- \- *theorem* fixed_points.minpoly.irreducible
- \- *theorem* fixed_points.minpoly.minimal_polynomial
- \+ *def* minpoly
- \+ *def* to_alg_hom
- \- *def* fixed_points.minpoly

Modified src/field_theory/tower.lean
- \+ *lemma* right
- \+ *lemma* findim_linear_map
- \+ *lemma* findim_linear_map'

Modified src/group_theory/group_action.lean
- \+ *lemma* to_fun_apply
- \+ *def* to_fun

Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_independent_of_comp
- \+ *theorem* linear_independent_equiv
- \+ *theorem* linear_independent_equiv'
- \+ *theorem* linear_independent_image
- \+ *theorem* linear_independent.image'
- \+ *theorem* linear_independent_insert
- \+ *theorem* linear_independent_insert'

Modified src/linear_algebra/dimension.lean
- \+ *theorem* is_basis.mk_eq_dim''
- \+ *theorem* dim_le
- \+ *theorem* {u₁}

Modified src/linear_algebra/finsupp.lean
- \+ *theorem* total_apply_of_mem_supported

Modified src/ring_theory/algebra.lean
- \+ *def* linear_map.lto_fun

Modified src/ring_theory/algebra_tower.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* card_le_of



## [2020-09-14 08:03:35](https://github.com/leanprover-community/mathlib/commit/b1e5a6b)
doc(measure_theory): docstrings for continuity from above and below ([#4122](https://github.com/leanprover-community/mathlib/pull/4122))
#### Estimated changes
Modified src/measure_theory/measure_space.lean




## [2020-09-14 08:03:33](https://github.com/leanprover-community/mathlib/commit/5a478f0)
doc(category_theory/natural_isomorphism): documentation and cleanup ([#4120](https://github.com/leanprover-community/mathlib/pull/4120))
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* app
- \- *def* is_iso_app_of_is_iso



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
- \+ *lemma* circumcenter_eq_of_range_eq

Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* monge_point_eq_of_range_eq
- \+ *lemma* orthocenter_eq_of_range_eq

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* centroid_eq_centroid_image_of_inj_on
- \+ *lemma* centroid_eq_of_inj_on_of_image_eq

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* centroid_eq_of_range_eq



## [2020-09-14 08:03:29](https://github.com/leanprover-community/mathlib/commit/b19fbd7)
feat(ring_theory/algebra_tower): coefficients for a basis in an algebra tower ([#4114](https://github.com/leanprover-community/mathlib/pull/4114))
This PR gives an expression for `(is_basis.smul hb hc).repr` in terms of `hb.repr` and `hc.repr`, useful if you have a field extension `L / K`, and `x y : L`, and want to write `y` in terms of the power basis of `K(x)`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.ext_on

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* is_basis.ext
- \+ *lemma* is_basis.repr_eq_iff
- \+ *lemma* is_basis.repr_apply_eq

Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* linear_independent_smul
- \+/\- *theorem* is_basis.smul
- \+ *theorem* is_basis.smul_repr
- \+ *theorem* is_basis.smul_repr_mk



## [2020-09-14 06:53:07](https://github.com/leanprover-community/mathlib/commit/e355933)
chore(category_theory/limits): remove unnecessary typeclass arguments ([#4141](https://github.com/leanprover-community/mathlib/pull/4141))
Ongoing cleanup post [#3995](https://github.com/leanprover-community/mathlib/pull/3995).
Previously we couldn't construct things like `instance : has_kernel (0 : X \hom Y)`, because it wouldn't have agreed definitionally with more general instances. Now we can.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* equalizer.iso_source_of_self_hom
- \+/\- *lemma* equalizer.iso_source_of_self_inv
- \+/\- *lemma* coequalizer.iso_target_of_self_hom
- \+/\- *lemma* coequalizer.iso_target_of_self_inv
- \+/\- *def* equalizer.iso_source_of_self
- \+/\- *def* coequalizer.iso_target_of_self

Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *lemma* kernel_zero_iso_source_hom
- \+/\- *lemma* kernel_zero_iso_source_inv
- \+/\- *lemma* cokernel_zero_iso_target_hom
- \+/\- *lemma* cokernel_zero_iso_target_inv
- \+/\- *def* kernel_zero_iso_source
- \+/\- *def* kernel.ι_of_zero
- \+/\- *def* cokernel_zero_iso_target
- \+/\- *def* cokernel.π_of_zero



## [2020-09-14 00:14:59](https://github.com/leanprover-community/mathlib/commit/bd385fb)
chore(category_theory/limits/functor_category): shuffle limits in functor cats ([#4124](https://github.com/leanprover-community/mathlib/pull/4124))
Give `is_limit` versions for statements about limits in the functor category, and write the `has_limit` versions in terms of those.
This also generalises the universes a little.
As usual, suggestions for better docstrings or better names appreciated!
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* cone.w
- \+/\- *lemma* cocone.w

Modified src/category_theory/limits/functor_category.lean
- \- *lemma* cone.functor_w
- \- *lemma* cocone.functor_w
- \+ *def* evaluation_jointly_reflects_limits
- \+ *def* combine_cones
- \+ *def* evaluate_combined_cones
- \+ *def* combined_is_limit
- \+ *def* evaluation_jointly_reflects_colimits
- \+ *def* combine_cocones
- \+ *def* evaluate_combined_cocones
- \+ *def* combined_is_colimit
- \- *def* functor_category_limit_cone
- \- *def* functor_category_colimit_cocone
- \- *def* evaluate_functor_category_limit_cone
- \- *def* evaluate_functor_category_colimit_cocone
- \- *def* functor_category_is_limit_cone
- \- *def* functor_category_is_colimit_cocone



## [2020-09-13 08:21:22](https://github.com/leanprover-community/mathlib/commit/5d35e62)
feat(algebraic_geometry/*): Gamma the global sections functor ([#4126](https://github.com/leanprover-community/mathlib/pull/4126))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* Γ_def
- \+ *lemma* Γ_obj
- \+ *lemma* Γ_obj_op
- \+ *lemma* Γ_map
- \+ *lemma* Γ_map_op
- \+ *def* Γ

Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* Γ_def
- \+ *lemma* Γ_obj
- \+ *lemma* Γ_obj_op
- \+ *lemma* Γ_map
- \+ *lemma* Γ_map_op
- \+ *def* Γ

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* Γ_obj_op
- \+ *lemma* Γ_map_op
- \+ *def* Γ

Modified src/algebraic_geometry/sheafed_space.lean
- \+ *lemma* Γ_def
- \+ *lemma* Γ_obj
- \+ *lemma* Γ_obj_op
- \+ *lemma* Γ_map
- \+ *lemma* Γ_map_op
- \+ *def* Γ

Modified src/topology/category/Top/opens.lean
- \+ *def* bot_le
- \+ *def* le_top
- \+ *def* le_map_top



## [2020-09-13 03:55:56](https://github.com/leanprover-community/mathlib/commit/f403a8b)
feat(category_theory/limits/types): is_limit versions of limits in type ([#4130](https://github.com/leanprover-community/mathlib/pull/4130))
`is_limit` versions for definitions and lemmas about limits in `Type u`.
#### Estimated changes
Modified src/category_theory/limits/types.lean
- \+ *lemma* is_limit_equiv_sections_apply
- \+ *lemma* is_limit_equiv_sections_symm_apply
- \+ *def* is_limit_equiv_sections



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
- \+ *lemma* normed_group.tendsto_nhds_nhds
- \+ *lemma* norm_smul_of_nonneg

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* is_basis.coe_constrL
- \+ *lemma* is_basis.constrL_apply
- \+ *lemma* is_basis.constrL_basis
- \+ *lemma* is_basis.sup_norm_le_norm
- \+ *lemma* is_basis.op_norm_le
- \+ *def* is_basis.constrL
- \+ *def* is_basis.equiv_funL

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_of_linear_of_bound
- \+ *lemma* op_norm_le_of_ball
- \+ *lemma* op_norm_eq_of_bounds

Modified src/linear_algebra/basis.lean
- \+ *theorem* is_basis.constr_apply_fintype

Modified src/topology/algebra/module.lean
- \+ *lemma* map_sum



## [2020-09-12 16:34:13](https://github.com/leanprover-community/mathlib/commit/c8771b6)
fix(algebra/ring/basic): delete mul_self_sub_mul_self_eq ([#4119](https://github.com/leanprover-community/mathlib/pull/4119))
It's redundant with `mul_self_sub_mul_self`.
Also renamed `mul_self_sub_one_eq` to `mul_self_sub_one`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* mul_self_sub_one
- \- *lemma* mul_self_sub_mul_self_eq
- \- *lemma* mul_self_sub_one_eq



## [2020-09-12 15:49:53](https://github.com/leanprover-community/mathlib/commit/169384a)
feat(slim_check): add test cases ([#4100](https://github.com/leanprover-community/mathlib/pull/4100))
#### Estimated changes
Modified src/system/random/basic.lean
- \+ *def* run_rand_with

Modified src/tactic/slim_check.lean


Modified src/testing/slim_check/testable.lean
- \+/\- *def* testable.check

Created test/random.lean
- \+ *def* primality_test
- \+ *def* iterated_primality_test_aux
- \+ *def* iterated_primality_test
- \+ *def* find_prime_aux
- \+ *def* find_prime

Modified test/slim_check.lean
- \- *def* primality_test
- \- *def* iterated_primality_test_aux
- \- *def* iterated_primality_test
- \- *def* find_prime_aux
- \- *def* find_prime



## [2020-09-12 09:38:07](https://github.com/leanprover-community/mathlib/commit/c3a6a69)
doc(group_theory/subgroup): fix links in module doc ([#4115](https://github.com/leanprover-community/mathlib/pull/4115))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2020-09-12 09:38:05](https://github.com/leanprover-community/mathlib/commit/88dd01b)
chore(category_theory): minor cleanups ([#4110](https://github.com/leanprover-community/mathlib/pull/4110))
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean
- \+ *def* colimit_cocone_is_colimit
- \- *def* colimit_is_colimit

Modified src/category_theory/limits/limits.lean
- \+ *def* is_limit.map
- \+ *def* is_colimit.map
- \- *def* is_limit_map
- \- *def* is_colimit_map

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/types.lean
- \+ *lemma* hom_inv_id_apply
- \+ *lemma* inv_hom_id_apply



## [2020-09-12 07:45:55](https://github.com/leanprover-community/mathlib/commit/b1a210e)
feat(logic/basic): Add more simp lemmas for forall ([#4117](https://github.com/leanprover-community/mathlib/pull/4117))
#### Estimated changes
Modified src/computability/partrec_code.lean


Modified src/logic/basic.lean
- \+ *theorem* forall_eq_apply_imp_iff
- \+ *theorem* forall_eq_apply_imp_iff'



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
- \+ *def* binary_product_limit_cone
- \+ *def* biprod_iso_prod
- \+ *def* product_limit_cone
- \+ *def* biproduct_iso_pi

Modified src/algebra/category/Group/colimits.lean
- \- *def* cokernel_iso_quotient

Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Module/kernels.lean
- \+ *lemma* has_kernels_Module
- \+ *lemma* has_cokernels_Module
- \- *def* has_kernels_Module
- \- *def* has_cokernels_Module

Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/homology/homology.lean


Modified src/algebra/homology/image_to_kernel_map.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/abelian/basic.lean
- \+ *lemma* has_finite_biproducts
- \+ *lemma* has_pullbacks
- \+ *lemma* has_pushouts
- \- *def* has_finite_biproducts
- \- *def* has_pullbacks
- \- *def* has_pushouts

Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* pullback_of_mono
- \+ *lemma* pushout_of_epi
- \+ *lemma* has_limit_parallel_pair
- \+ *lemma* has_colimit_parallel_pair
- \- *def* pullback_of_mono
- \- *def* pushout_of_epi
- \- *def* has_limit_parallel_pair
- \- *def* has_colimit_parallel_pair

Modified src/category_theory/adjunction/limits.lean
- \+ *lemma* has_colimit_of_comp_equivalence
- \+ *lemma* has_limit_of_comp_equivalence
- \- *def* has_colimit_of_comp_equivalence
- \- *def* has_limit_of_comp_equivalence

Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/graded_object.lean
- \- *def* total

Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean
- \+ *lemma* has_limit_of_created
- \+ *lemma* has_colimit_of_created
- \- *def* has_limit_of_created
- \- *def* has_colimit_of_created

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/fubini.lean
- \- *def* diagram_of_cones.mk_of_has_limits
- \- *def* limit_uncurry_iso_limit_comp_lim
- \- *def* limit_iso_limit_curry_comp_lim

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/limits.lean
- \+ *lemma* has_limit.mk
- \+ *lemma* limit.cone_X
- \+ *lemma* has_limit_of_iso
- \+ *lemma* has_limit.of_cones_iso
- \+ *lemma* has_limit_of_equivalence_comp
- \+ *lemma* is_limit_map_π
- \+ *lemma* has_limits_of_shape_of_equivalence
- \+ *lemma* has_colimit.mk
- \+ *lemma* colimit.cocone_X
- \+ *lemma* has_colimit_of_iso
- \+ *lemma* has_colimit.of_cocones_iso
- \+ *lemma* has_colimit_of_equivalence_comp
- \+ *lemma* ι_is_colimit_map
- \+ *lemma* has_colimits_of_shape_of_equivalence
- \+ *def* get_limit_cone
- \+/\- *def* limit.cone
- \+ *def* is_limit_map
- \+ *def* get_colimit_cocone
- \+/\- *def* colimit.cocone
- \+ *def* is_colimit_map
- \- *def* has_limit_of_iso
- \- *def* has_limit.of_cones_iso
- \- *def* has_limit_of_equivalence_comp
- \- *def* has_limits_of_shape_of_equivalence
- \- *def* has_colimit_of_iso
- \- *def* has_colimit.of_cocones_iso
- \- *def* has_colimit_of_equivalence_comp
- \- *def* has_colimits_of_shape_of_equivalence

Modified src/category_theory/limits/opposites.lean
- \+ *lemma* has_limit_of_has_colimit_left_op
- \+ *lemma* has_limits_of_shape_op_of_has_colimits_of_shape
- \+ *lemma* has_limits_op_of_has_colimits
- \+ *lemma* has_colimit_of_has_limit_left_op
- \+ *lemma* has_colimits_of_shape_op_of_has_limits_of_shape
- \+ *lemma* has_colimits_op_of_has_limits
- \+ *lemma* has_coproducts_opposite
- \+ *lemma* has_products_opposite
- \- *def* has_limit_of_has_colimit_left_op
- \- *def* has_limits_of_shape_op_of_has_colimits_of_shape
- \- *def* has_limits_op_of_has_colimits
- \- *def* has_colimit_of_has_limit_left_op
- \- *def* has_colimits_of_shape_op_of_has_limits_of_shape
- \- *def* has_colimits_op_of_has_limits
- \- *def* has_coproducts_opposite
- \- *def* has_products_opposite

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/pi.lean
- \+ *lemma* has_limit_of_has_limit_comp_eval
- \+ *lemma* has_colimit_of_has_colimit_comp_eval
- \- *def* has_limit_of_has_limit_comp_eval
- \- *def* has_colimit_of_has_colimit_comp_eval

Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/preserves/shapes.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* has_binary_products_of_has_limit_pair
- \+ *lemma* has_binary_coproducts_of_has_colimit_pair
- \- *def* has_binary_products_of_has_limit_pair
- \- *def* has_binary_coproducts_of_has_colimit_pair

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* has_biproduct.mk
- \+ *lemma* biproduct.bicone_π
- \+ *lemma* biproduct.bicone_ι
- \+ *lemma* biproduct.lift_π
- \+ *lemma* biproduct.ι_desc
- \+ *lemma* biproduct.map_π
- \+ *lemma* biproduct.ι_map
- \+ *lemma* has_binary_biproduct.mk
- \+ *lemma* has_binary_biproducts_of_finite_biproducts
- \+ *lemma* binary_biproduct.bicone_fst
- \+ *lemma* binary_biproduct.bicone_snd
- \+ *lemma* binary_biproduct.bicone_inl
- \+ *lemma* binary_biproduct.bicone_inr
- \+ *lemma* biprod.lift_fst
- \+ *lemma* biprod.lift_snd
- \+ *lemma* biprod.inl_desc
- \+ *lemma* biprod.inr_desc
- \+ *lemma* has_biproduct_of_total
- \+ *lemma* has_biproduct.of_has_product
- \+ *lemma* has_biproduct.of_has_coproduct
- \+ *lemma* has_finite_biproducts.of_has_finite_products
- \+ *lemma* has_finite_biproducts.of_has_finite_coproducts
- \+ *lemma* has_binary_biproduct_of_total
- \+ *lemma* has_binary_biproduct.of_has_binary_product
- \+ *lemma* has_binary_biproducts.of_has_binary_products
- \+ *lemma* has_binary_biproduct.of_has_binary_coproduct
- \+ *lemma* has_binary_biproducts.of_has_binary_coproducts
- \- *lemma* biproduct.inl_map
- \+ *def* get_biproduct_data
- \+ *def* biproduct.bicone
- \+ *def* biproduct.is_limit
- \+ *def* biproduct.is_colimit
- \+ *def* get_binary_biproduct_data
- \+ *def* binary_biproduct.bicone
- \+ *def* binary_biproduct.is_limit
- \+ *def* binary_biproduct.is_colimit
- \+/\- *def* biprod.map_iso
- \- *def* has_binary_biproducts_of_finite_biproducts
- \- *def* has_biproduct_of_total
- \- *def* has_biproduct.of_has_product
- \- *def* has_biproduct.of_has_coproduct
- \- *def* has_finite_biproducts.of_has_finite_products
- \- *def* has_finite_biproducts.of_has_finite_coproducts
- \- *def* has_binary_biproduct_of_total
- \- *def* has_binary_biproduct.of_has_binary_product
- \- *def* has_binary_biproducts.of_has_binary_products
- \- *def* has_binary_biproduct.of_has_binary_coproduct
- \- *def* has_binary_biproducts.of_has_binary_coproducts

Modified src/category_theory/limits/shapes/constructions/binary_products.lean
- \+ *lemma* has_binary_products_of_terminal_and_pullbacks
- \- *def* has_binary_products_of_terminal_and_pullbacks

Modified src/category_theory/limits/shapes/constructions/equalizers.lean
- \+ *lemma* has_equalizers_of_pullbacks_and_binary_products
- \- *def* has_equalizers_of_pullbacks_and_binary_products

Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* limits_from_equalizers_and_products
- \+ *lemma* finite_limits_from_equalizers_and_finite_products
- \- *def* limits_from_equalizers_and_products
- \- *def* finite_limits_from_equalizers_and_finite_products

Modified src/category_theory/limits/shapes/constructions/over/default.lean


Modified src/category_theory/limits/shapes/constructions/over/products.lean
- \+ *lemma* has_over_limit_discrete_of_wide_pullback_limit
- \+ *lemma* over_product_of_wide_pullback
- \+ *lemma* over_binary_product_of_pullback
- \+ *lemma* over_products_of_wide_pullbacks
- \+ *lemma* over_finite_products_of_finite_wide_pullbacks
- \+ *lemma* over_has_terminal
- \- *def* has_over_limit_discrete_of_wide_pullback_limit
- \- *def* over_product_of_wide_pullback
- \- *def* over_binary_product_of_pullback
- \- *def* over_products_of_wide_pullbacks
- \- *def* over_finite_products_of_finite_wide_pullbacks
- \- *def* over_has_terminal

Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean
- \+ *lemma* has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \+ *lemma* has_pullbacks_of_has_binary_products_of_has_equalizers
- \+ *lemma* has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \+ *lemma* has_pushouts_of_has_binary_coproducts_of_has_coequalizers
- \- *def* has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
- \- *def* has_pullbacks_of_has_binary_products_of_has_equalizers
- \- *def* has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
- \- *def* has_pushouts_of_has_binary_coproducts_of_has_coequalizers

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* has_equalizers_of_has_limit_parallel_pair
- \+ *lemma* has_coequalizers_of_has_colimit_parallel_pair
- \- *def* has_equalizers_of_has_limit_parallel_pair
- \- *def* has_coequalizers_of_has_colimit_parallel_pair

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *lemma* has_finite_limits_of_has_limits
- \+ *lemma* has_finite_colimits_of_has_colimits
- \+ *lemma* has_finite_wide_pullbacks_of_has_finite_limits
- \+ *lemma* has_finite_wide_pushouts_of_has_finite_limits
- \+/\- *def* has_finite_limits
- \+/\- *def* has_finite_colimits
- \+/\- *def* has_finite_wide_pullbacks
- \+/\- *def* has_finite_wide_pushouts
- \- *def* has_finite_limits_of_has_limits
- \- *def* has_finite_colimits_of_has_colimits
- \- *def* has_finite_wide_pullbacks_of_has_finite_limits
- \- *def* has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+ *lemma* has_finite_products_of_has_finite_limits
- \+ *lemma* has_finite_products_of_has_products
- \+ *lemma* has_finite_coproducts_of_has_finite_colimits
- \+ *lemma* has_finite_coproducts_of_has_coproducts
- \+/\- *def* has_finite_products
- \+/\- *def* has_finite_coproducts
- \- *def* has_finite_products_of_has_finite_limits
- \- *def* has_finite_products_of_has_products
- \- *def* has_finite_coproducts_of_has_finite_colimits
- \- *def* has_finite_coproducts_of_has_coproducts

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* has_pullbacks_of_has_limit_cospan
- \+ *lemma* has_pushouts_of_has_colimit_span
- \- *def* has_pullbacks_of_has_limit_cospan
- \- *def* has_pushouts_of_has_colimit_span

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* has_terminal_of_unique
- \+ *lemma* has_initial_of_unique
- \- *def* has_terminal_of_unique
- \- *def* has_initial_of_unique

Modified src/category_theory/limits/shapes/types.lean
- \- *lemma* terminal
- \- *lemma* terminal_from
- \- *lemma* initial
- \- *lemma* prod
- \- *lemma* prod_fst
- \- *lemma* prod_snd
- \- *lemma* prod_lift
- \- *lemma* prod_map
- \- *lemma* coprod
- \- *lemma* coprod_inl
- \- *lemma* coprod_inr
- \- *lemma* coprod_desc
- \- *lemma* coprod_map
- \- *lemma* pi
- \- *lemma* pi_π
- \- *lemma* pi_lift
- \- *lemma* pi_map
- \- *lemma* sigma
- \- *lemma* sigma_ι
- \- *lemma* sigma_desc
- \- *lemma* sigma_map
- \+ *def* terminal_limit_cone
- \+ *def* initial_limit_cone
- \+ *def* binary_product_limit_cone
- \+ *def* binary_coproduct_limit_cone
- \+ *def* product_limit_cone
- \+ *def* coproduct_limit_cone
- \- *def* types_has_terminal
- \- *def* types_has_initial
- \- *def* types_has_binary_products
- \- *def* types_has_binary_coproducts
- \- *def* types_has_products
- \- *def* types_has_coproducts

Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* has_initial
- \+ *lemma* has_terminal
- \- *def* has_initial
- \- *def* has_terminal

Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/limits.lean
- \+ *lemma* has_limit_of_comp_forget_has_limit
- \+ *lemma* forget_creates_colimits_of_monad_preserves
- \+ *lemma* monadic_creates_limits
- \+ *lemma* has_limits_of_reflective
- \- *def* has_limit_of_comp_forget_has_limit
- \- *def* forget_creates_colimits_of_monad_preserves
- \- *def* monadic_creates_limits
- \- *def* has_limits_of_reflective

Created src/category_theory/monoidal/of_chosen_finite_products.lean
- \+ *lemma* binary_fan.swap_fst
- \+ *lemma* binary_fan.swap_snd
- \+ *lemma* has_binary_product.swap
- \+ *lemma* binary_fan.assoc_fst
- \+ *lemma* binary_fan.assoc_snd
- \+ *lemma* binary_fan.assoc_inv_fst
- \+ *lemma* binary_fan.assoc_inv_snd
- \+ *lemma* tensor_id
- \+ *lemma* tensor_comp
- \+ *lemma* pentagon
- \+ *lemma* triangle
- \+ *lemma* left_unitor_naturality
- \+ *lemma* right_unitor_naturality
- \+ *lemma* associator_naturality
- \+ *lemma* braiding_naturality
- \+ *lemma* hexagon_forward
- \+ *lemma* hexagon_reverse
- \+ *lemma* symmetry
- \+ *def* binary_fan.swap
- \+ *def* is_limit.swap_binary_fan
- \+ *def* binary_fan.braiding
- \+ *def* binary_fan.assoc
- \+ *def* binary_fan.assoc_inv
- \+ *def* is_limit.assoc
- \+ *def* binary_fan.associator
- \+ *def* binary_fan.associator_of_limit_cone
- \+ *def* binary_fan.left_unitor
- \+ *def* binary_fan.right_unitor
- \+ *def* tensor_obj
- \+ *def* tensor_hom
- \+ *def* monoidal_of_chosen_finite_products
- \+ *def* monoidal_of_chosen_finite_products_synonym
- \+ *def* symmetric_of_chosen_finite_products

Modified src/category_theory/monoidal/of_has_finite_products.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/over.lean
- \- *lemma* iso_mk_hom_left
- \- *lemma* iso_mk_inv_left
- \+/\- *def* iso_mk

Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/default.lean
- \+ *lemma* has_limit_parallel_pair
- \+ *lemma* has_equalizers_of_has_kernels
- \+ *lemma* has_colimit_parallel_pair
- \+ *lemma* has_coequalizers_of_has_cokernels
- \- *def* has_limit_parallel_pair
- \- *def* has_equalizers_of_has_kernels
- \- *def* has_colimit_parallel_pair
- \- *def* has_coequalizers_of_has_cokernels

Modified src/group_theory/quotient_group.lean
- \+ *lemma* lift_quot_mk

Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* inf_le_left_apply
- \+ *lemma* inf_le_left_apply_mk
- \+ *lemma* le_supr_apply_mk

Modified src/topology/category/UniformSpace.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* sheaf_condition_fac
- \+ *lemma* sheaf_condition_uniq

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
- \+/\- *theorem* forall_eq'
- \+ *theorem* forall_apply_eq_imp_iff
- \+ *theorem* forall_apply_eq_imp_iff'

Modified src/measure_theory/borel_space.lean




## [2020-09-11 17:48:43](https://github.com/leanprover-community/mathlib/commit/17a5807)
feat(category_theory/limits/fubini): another formulation for limits commuting ([#4034](https://github.com/leanprover-community/mathlib/pull/4034))
The statement that you can swap limits, rather than just combine into a single limit as we had before.
(This just uses two copies of the previous isomorphism.)
#### Estimated changes
Modified src/category_theory/limits/fubini.lean
- \+ *lemma* limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_hom_π_π
- \+ *lemma* limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_inv_π_π
- \+ *def* limit_curry_swap_comp_lim_iso_limit_curry_comp_lim

Modified src/category_theory/limits/limits.lean
- \+ *lemma* has_limit.iso_of_equivalence_hom_π
- \+ *lemma* has_limit.iso_of_equivalence_inv_π
- \+ *lemma* has_colimit.iso_of_equivalence_hom_π
- \+ *lemma* has_colimit.iso_of_equivalence_inv_π
- \- *lemma* has_limit.iso_of_equivalence_π
- \- *lemma* has_colimit.iso_of_equivalence_π

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
- \+ *def* inf_le_left
- \+ *def* inf_le_right

Modified src/topology/sheaves/local_predicate.lean


Created src/topology/sheaves/sheafify.lean
- \+ *lemma* stalk_to_fiber_surjective
- \+ *lemma* stalk_to_fiber_injective
- \+ *def* is_germ
- \+ *def* is_locally_germ
- \+ *def* sheafify
- \+ *def* to_sheafify
- \+ *def* stalk_to_fiber
- \+ *def* sheafify_stalk_iso

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* germ_eq
- \+ *lemma* germ_res_apply'



## [2020-09-11 17:48:37](https://github.com/leanprover-community/mathlib/commit/5509a30)
feat(category_theory/skeleton): add skeletal categories and construct a special case ([#3929](https://github.com/leanprover-community/mathlib/pull/3929))
I'm interested in the quotient construction of the skeleton for a thin category in particular for topos and sheafification PRs, but of course the general construction is useful too, so I've marked that as TODO and I'll make a followup PR so that this one doesn't get too big.
The advantage of handling this special case separately is that the skeleton of a thin category is a partial order, and so lattice constructions can be used (which is needed for my application), and also there are nice definitional equalities.
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Created src/category_theory/skeletal.lean
- \+ *lemma* functor.eq_of_iso
- \+ *lemma* functor_skeletal
- \+ *lemma* comp_to_thin_skeleton
- \+ *lemma* equiv_of_both_ways
- \+ *lemma* skeletal
- \+ *lemma* map_comp_eq
- \+ *lemma* map_id_eq
- \+ *lemma* map_iso_eq
- \+ *def* skeletal
- \+ *def* thin_skeleton
- \+ *def* to_thin_skeleton
- \+ *def* map
- \+ *def* map_nat_trans
- \+ *def* map₂

Deleted src/category_theory/sparse.lean
- \- *def* sparse_category

Created src/category_theory/thin.lean
- \+ *def* thin_category
- \+ *def* iso_of_both_ways



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
- \+ *lemma* orthogonal_projection_eq_circumcenter_of_exists_dist_eq
- \+ *lemma* orthogonal_projection_eq_circumcenter_of_dist_eq
- \+ *lemma* eq_or_eq_reflection_of_dist_eq



## [2020-09-11 15:53:15](https://github.com/leanprover-community/mathlib/commit/872a37e)
cleanup(group_theory/presented_group): () -> [], and remove some FIXMEs ([#4076](https://github.com/leanprover-community/mathlib/pull/4076))
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/presented_group.lean
- \- *lemma* to_group.mul
- \- *lemma* to_group.one
- \- *lemma* to_group.inv

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* le_normalizer_of_normal
- \+/\- *lemma* conjugates_subset_normal
- \+/\- *lemma* normal_closure_subset_iff
- \- *lemma* normal_of_comm
- \- *lemma* bot_normal
- \- *lemma* center_normal
- \- *lemma* normal_in_normalizer
- \- *lemma* normal_closure_normal
- \- *lemma* subgroup.normal_comap
- \- *lemma* monoid_hom.normal_ker
- \+/\- *theorem* conjugates_of_set_subset
- \+/\- *theorem* normal_closure_le_normal



## [2020-09-11 15:53:13](https://github.com/leanprover-community/mathlib/commit/377c7c9)
feat(category_theory/braided): braiding and unitors ([#4075](https://github.com/leanprover-community/mathlib/pull/4075))
The interaction between braidings and unitors in a braided category.
Requested by @cipher1024 for some work he's doing on monads.
I've changed the statements of some `@[simp]` lemmas, in particular `left_unitor_tensor`, `left_unitor_tensor_inv`, `right_unitor_tensor`, `right_unitor_tensor_inv`. The new theory is that the components of a unitor indexed by a tensor product object are "more complicated" than other unitors. (We already follow the same principle for simplifying associators using the pentagon equation.)
#### Estimated changes
Modified src/category_theory/monoidal/End.lean


Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* braiding_left_unitor_aux₁
- \+ *lemma* braiding_left_unitor_aux₂
- \+ *lemma* braiding_left_unitor
- \+ *lemma* braiding_right_unitor_aux₁
- \+ *lemma* braiding_right_unitor_aux₂
- \+ *lemma* braiding_right_unitor

Modified src/category_theory/monoidal/category.lean
- \+ *lemma* left_unitor_tensor'
- \+/\- *lemma* left_unitor_tensor
- \+ *lemma* left_unitor_tensor_inv'
- \+/\- *lemma* left_unitor_tensor_inv
- \+/\- *lemma* right_unitor_tensor
- \+/\- *lemma* right_unitor_tensor_inv

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
- \+/\- *lemma* apply_dite
- \+/\- *lemma* apply_ite
- \+/\- *lemma* apply_dite2
- \+/\- *lemma* apply_ite2
- \+/\- *lemma* dite_apply
- \+/\- *lemma* ite_apply
- \+ *lemma* dite_not
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
- \+ *lemma* cons_inj_right
- \+ *lemma* cons_inj_left
- \+ *lemma* cons_swap
- \+ *lemma* mem_cons
- \+ *lemma* mem_cons_of_mem
- \+ *lemma* mem_cons_self
- \+ *lemma* cons_of_coe_eq
- \+ *lemma* sound
- \+ *lemma* cons_equiv_eq_equiv_cons
- \+/\- *def* sym
- \+/\- *def* vector.perm.is_setoid
- \+ *def* of_vector
- \+ *def* nil
- \+ *def* cons
- \+ *def* mem
- \+/\- *def* sym'
- \+ *def* cons'
- \+/\- *def* sym_equiv_sym'

Modified src/data/sym2.lean
- \+/\- *lemma* congr_right
- \+ *lemma* congr_left
- \+ *lemma* map_pair_eq
- \+/\- *lemma* mk_has_mem_right
- \+/\- *lemma* mem_other_spec
- \+ *lemma* mem_other_mem
- \+ *lemma* sym2_ext
- \+ *lemma* diag_is_diag
- \+ *lemma* mem_other_ne
- \+ *lemma* mem_from_rel_irrefl_other_ne
- \+ *lemma* mem_other_spec'
- \+ *lemma* other_eq_other'
- \+ *lemma* mem_other_mem'
- \+ *lemma* other_invol'
- \+ *lemma* other_invol
- \- *lemma* vmem_other_spec
- \- *lemma* other_is_mem_other
- \+ *def* mem.other'
- \- *def* vmem
- \- *def* mk_has_vmem
- \- *def* vmem.other



## [2020-09-11 14:46:51](https://github.com/leanprover-community/mathlib/commit/7886c27)
feat(category_theory/monoidal): lax monoidal functors take monoids to monoids ([#4108](https://github.com/leanprover-community/mathlib/pull/4108))
#### Estimated changes
Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/internal.lean
- \+ *lemma* one_mul_hom
- \+ *lemma* mul_one_hom
- \+ *def* trivial
- \+ *def* map_Mon



## [2020-09-11 14:46:48](https://github.com/leanprover-community/mathlib/commit/bd74baa)
feat(algebra/homology/exact): lemmas about exactness ([#4106](https://github.com/leanprover-community/mathlib/pull/4106))
These are a few lemmas on the way to showing how `exact` changes under isomorphisms applied to the objects. It's not everthing one might want; I'm salvaging this from an old branch and unlikely to do more in the near future, but hopefully this is mergeable progress as is.
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* exact.w_assoc
- \+ *lemma* exact_of_zero

Modified src/algebra/homology/image_to_kernel_map.lean
- \+ *lemma* image_to_kernel_map_comp_iso
- \+ *lemma* image_to_kernel_map_iso_comp

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.factor_thru_image_pre_comp

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* equalizer_as_kernel
- \+ *lemma* coequalizer_as_cokernel



## [2020-09-11 14:46:45](https://github.com/leanprover-community/mathlib/commit/233a802)
feat(algebraic_geometry/Scheme): Spec as Scheme ([#4104](https://github.com/leanprover-community/mathlib/pull/4104))
```lean
def Spec (R : CommRing) : Scheme
```
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *def* Spec

Modified src/algebraic_geometry/Spec.lean
- \+ *def* Spec.LocallyRingedSpace

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *def* of_restrict
- \+ *def* to_restrict_top
- \+ *def* restrict_top_iso

Modified src/topology/category/Top/opens.lean
- \+ *def* is_open_map.adjunction



## [2020-09-11 14:46:44](https://github.com/leanprover-community/mathlib/commit/34e0f31)
feat(nnreal): absolute value ([#4098](https://github.com/leanprover-community/mathlib/pull/4098))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnreal.norm_eq

Modified src/data/real/nnreal.lean
- \+ *lemma* abs_eq
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
- \+ *def* Type_to_Cat

Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* eq_to_iso_refl
- \+/\- *lemma* eq_to_hom_op
- \+ *lemma* inv_eq_to_hom

Created src/category_theory/grothendieck.lean
- \+ *lemma* ext
- \+ *def* id
- \+ *def* comp
- \+ *def* forget
- \+ *def* grothendieck_Type_to_Cat

Modified src/category_theory/isomorphism.lean
- \+ *lemma* inv_comp_eq
- \+ *lemma* eq_inv_comp
- \+ *lemma* comp_inv_eq
- \+ *lemma* comp_is_iso_eq



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
- \+/\- *def* yoneda

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
- \+ *lemma* sum_reflection_circumcenter_weights_with_circumcenter
- \+ *lemma* reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *def* reflection_circumcenter_weights_with_circumcenter

Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* dist_orthocenter_reflection_circumcenter
- \+ *lemma* dist_orthocenter_reflection_circumcenter_finset



## [2020-09-11 11:35:23](https://github.com/leanprover-community/mathlib/commit/4ce27a5)
feat(category_theory/limits): filtered colimits commute with finite limits (in Type) ([#4046](https://github.com/leanprover-community/mathlib/pull/4046))
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean


Modified src/category_theory/filtered.lean
- \+/\- *lemma* sup_exists
- \+/\- *lemma* to_sup_commutes
- \- *lemma* sup_exists'
- \+/\- *def* sup
- \+/\- *def* to_sup

Created src/category_theory/limits/colimit_limit.lean
- \+ *lemma* map_id_left_eq_curry_map
- \+ *lemma* map_id_right_eq_curry_swap_map
- \+ *lemma* ι_colimit_limit_to_limit_colimit_π
- \+ *lemma* ι_colimit_limit_to_limit_colimit_π_apply
- \+ *def* colimit_limit_to_limit_colimit

Created src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean
- \+ *lemma* colimit_limit_to_limit_colimit_injective
- \+ *lemma* colimit_limit_to_limit_colimit_surjective

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.w
- \+/\- *lemma* colimit.w

Modified src/category_theory/limits/types.lean
- \+ *lemma* limit.π_mk
- \+ *lemma* colimit_sound'
- \+ *def* limit.mk

Modified src/category_theory/types.lean
- \+ *def* is_iso_equiv_bijective



## [2020-09-11 06:18:46](https://github.com/leanprover-community/mathlib/commit/80a9e4f)
refactor(data/mv_polynomial/pderivative): make pderivative a linear map ([#4095](https://github.com/leanprover-community/mathlib/pull/4095))
Make `pderivative i` a linear map as suggested at https://github.com/leanprover-community/mathlib/pull/4083#issuecomment-689712833
#### Estimated changes
Modified src/data/mv_polynomial/pderivative.lean
- \- *lemma* pderivative_add
- \- *lemma* pderivative_zero
- \- *lemma* pderivative.add_monoid_hom_apply
- \+/\- *def* pderivative
- \- *def* pderivative.add_monoid_hom



## [2020-09-11 00:47:31](https://github.com/leanprover-community/mathlib/commit/9a24f68)
chore(scripts): update nolints.txt ([#4105](https://github.com/leanprover-community/mathlib/pull/4105))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-10 18:33:51](https://github.com/leanprover-community/mathlib/commit/7d88b31)
feat(ring_theory/algebra_operations): add le_div_iff_mul_le ([#4102](https://github.com/leanprover-community/mathlib/pull/4102))
#### Estimated changes
Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* le_div_iff_mul_le



## [2020-09-10 16:46:37](https://github.com/leanprover-community/mathlib/commit/e33a777)
feat(data/fin): iffs about succ_above ordering ([#4092](https://github.com/leanprover-community/mathlib/pull/4092))
New lemmas:
`succ_above_lt_iff`
`lt_succ_above_iff`
These help avoid needing to do case analysis when faced with
inequalities about `succ_above`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* succ_above_lt_iff
- \+ *lemma* lt_succ_above_iff



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


Created src/algebra/group_power/basic.lean
- \+ *lemma* pow_right
- \+ *theorem* pow_right
- \+ *theorem* pow_left
- \+ *theorem* pow_pow
- \+ *theorem* self_pow
- \+ *theorem* pow_self
- \+ *theorem* pow_pow_self
- \+ *theorem* pow_zero
- \+ *theorem* zero_nsmul
- \+ *theorem* pow_succ
- \+ *theorem* succ_nsmul
- \+ *theorem* pow_two
- \+ *theorem* two_nsmul
- \+ *theorem* pow_mul_comm'
- \+ *theorem* nsmul_add_comm'
- \+ *theorem* pow_succ'
- \+ *theorem* succ_nsmul'
- \+ *theorem* pow_add
- \+ *theorem* add_nsmul
- \+ *def* monoid.pow
- \+ *def* nsmul
- \+ *def* gpow
- \+ *def* gsmul

Created src/algebra/group_power/default.lean


Renamed src/algebra/group_power.lean to src/algebra/group_power/lemmas.lean
- \- *lemma* pow_right
- \- *theorem* pow_right
- \- *theorem* pow_left
- \- *theorem* pow_pow
- \- *theorem* self_pow
- \- *theorem* pow_self
- \- *theorem* pow_pow_self
- \- *theorem* pow_zero
- \- *theorem* zero_nsmul
- \- *theorem* pow_succ
- \- *theorem* succ_nsmul
- \- *theorem* pow_mul_comm'
- \- *theorem* nsmul_add_comm'
- \- *theorem* pow_succ'
- \- *theorem* succ_nsmul'
- \- *theorem* pow_two
- \- *theorem* two_nsmul
- \- *theorem* pow_add
- \- *theorem* add_nsmul
- \- *theorem* nat.pow_eq_pow
- \- *def* monoid.pow
- \- *def* nsmul
- \- *def* gpow
- \- *def* gsmul

Modified src/analysis/specific_limits.lean


Modified src/data/bitvec/basic.lean


Created src/data/bitvec/core.lean
- \+ *theorem* bits_to_nat_to_list
- \+ *theorem* to_nat_append
- \+ *theorem* bits_to_nat_to_bool
- \+ *theorem* of_nat_succ
- \+ *theorem* to_nat_of_nat
- \+ *def* bitvec
- \+ *def* append
- \+ *def* shl
- \+ *def* fill_shr
- \+ *def* ushr
- \+ *def* sshr
- \+ *def* not
- \+ *def* and
- \+ *def* or
- \+ *def* xor
- \+ *def* adc
- \+ *def* sbb
- \+ *def* uborrow
- \+ *def* ult
- \+ *def* ugt
- \+ *def* ule
- \+ *def* uge
- \+ *def* sborrow
- \+ *def* slt
- \+ *def* sgt
- \+ *def* sle
- \+ *def* sge
- \+ *def* add_lsb
- \+ *def* bits_to_nat

Modified src/data/fintype/card.lean


Modified src/data/nat/basic.lean
- \+ *lemma* pow_succ
- \+ *lemma* pow_zero
- \+/\- *lemma* one_pow
- \+/\- *lemma* pow_right_strict_mono
- \+/\- *lemma* pow_right_injective
- \+ *lemma* shiftl_eq_mul_pow
- \+ *lemma* shiftl'_tt_eq_mul_pow
- \+ *lemma* one_shiftl
- \+ *lemma* zero_shiftl
- \+ *lemma* shiftr_eq_div_pow
- \+ *lemma* zero_shiftr
- \+ *theorem* pow_one
- \+ *theorem* pow_le_pow_of_le_left
- \+ *theorem* pow_le_pow_of_le_right
- \+ *theorem* pos_pow_of_pos
- \+ *theorem* zero_pow
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_lt_pow_of_lt_right
- \+ *theorem* mod_pow_succ
- \+/\- *theorem* pow_two

Modified src/data/nat/gcd.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/prime.lean


Modified src/data/num/bitwise.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/ring_homs.lean
- \+/\- *lemma* lim_nth_hom_add
- \+/\- *lemma* lim_nth_hom_mul

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/separable.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/primorial.lean


Modified src/ring_theory/multiplicity.lean


Modified src/tactic/norm_num.lean
- \- *lemma* from_nat_pow

Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified test/localized/localized.lean




## [2020-09-10 13:02:29](https://github.com/leanprover-community/mathlib/commit/d5be9f3)
refactor(data/mv_polynomial): move `smul` lemmas into basic.lean ([#4097](https://github.com/leanprover-community/mathlib/pull/4097))
`C_mul'`, `smul_eq_C_mul` and `smul_eval` seemed a bit out of place in `comm_ring.lean`, since they only need `comm_semiring α`. So I moved them to `basic.lean` where they probably fit in a bit better?
I've also golfed the proof of `smul_eq_C_mul`.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* smul_eval
- \+ *theorem* C_mul'

Modified src/data/mv_polynomial/comm_ring.lean
- \- *lemma* smul_eq_C_mul
- \- *lemma* smul_eval
- \- *theorem* C_mul'



## [2020-09-10 13:02:28](https://github.com/leanprover-community/mathlib/commit/19b9ae6)
feat(data/mv_polynomial): a few facts about `constant_coeff` and `aeval` ([#4085](https://github.com/leanprover-community/mathlib/pull/4085))
A few additional facts about `constant_coeff_map` and `aeval` from the witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* constant_coeff_map
- \+ *lemma* constant_coeff_comp_map
- \+ *lemma* eval₂_hom_eq_zero
- \+ *lemma* aeval_eq_zero



## [2020-09-10 13:02:25](https://github.com/leanprover-community/mathlib/commit/d857def)
feat(slim_check): make `shrink` recursive ([#4038](https://github.com/leanprover-community/mathlib/pull/4038))
Make example shrinking recursive to make it faster and more reliable. It now acts more like a binary search and less like a linear search.
#### Estimated changes
Renamed src/data/lazy_list2.lean to src/data/lazy_list/basic.lean
- \+ *lemma* append_nil
- \+ *lemma* append_assoc
- \+ *lemma* append_bind
- \+ *def* find
- \+ *def* reverse
- \+ *def* mfirst

Modified src/data/pnat/basic.lean
- \+ *def* pnat.nat_pred

Modified src/tactic/interactive.lean


Modified src/testing/slim_check/sampleable.lean
- \+ *lemma* list.sizeof_drop_lt_sizeof_of_lt_length
- \+ *lemma* list.sizeof_cons_lt_right
- \+ *lemma* list.sizeof_cons_lt_left
- \+ *lemma* list.sizeof_append_lt_left
- \+ *lemma* list.one_le_sizeof
- \+ *lemma* tree.one_le_sizeof
- \+/\- *def* nat.shrink'
- \+/\- *def* nat.shrink
- \+/\- *def* sampleable.lift
- \+ *def* iterate_shrink
- \+ *def* sizeof_lt
- \+ *def* shrink_fn
- \+ *def* prod.shrink
- \+/\- *def* sum.shrink
- \+ *def* list.shrink_removes
- \+ *def* list.shrink_one
- \+/\- *def* list.shrink_with
- \+ *def* no_shrink
- \+ *def* no_shrink.mk
- \+ *def* no_shrink.get
- \+ *def* rec_shrink
- \+/\- *def* tree.shrink_with
- \- *def* lazy_list.lseq
- \- *def* int.shrink'
- \- *def* int.shrink
- \- *def* list.shrink'

Modified src/testing/slim_check/testable.lean
- \+ *def* minimize_aux
- \+/\- *def* minimize



## [2020-09-10 11:22:25](https://github.com/leanprover-community/mathlib/commit/55cab6c)
feat(data/{int,nat}/cast): dvd cast lemmas ([#4086](https://github.com/leanprover-community/mathlib/pull/4086))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* coe_int_dvd

Modified src/data/nat/cast.lean
- \+ *lemma* coe_nat_dvd



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
- \+/\- *lemma* coe_ring_equiv
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* commutes
- \+/\- *lemma* map_sum
- \+ *lemma* to_alg_hom_eq_coe
- \+/\- *lemma* coe_alg_hom
- \+/\- *lemma* injective
- \+/\- *lemma* surjective
- \+/\- *lemma* bijective
- \+ *lemma* to_alg_hom_to_linear_map
- \+ *lemma* to_linear_equiv_to_linear_map
- \+ *lemma* to_linear_map_apply
- \+ *lemma* trans_to_linear_map
- \+ *lemma* mem_map
- \+ *theorem* to_linear_equiv_inj
- \+ *theorem* to_linear_map_inj
- \+ *def* to_alg_hom
- \+ *def* to_linear_map

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* map_div

Created src/ring_theory/dedekind_domain.lean
- \+ *lemma* dimension_le_one.principal_ideal_ring
- \+ *lemma* dimension_le_one.integral_closure
- \+ *lemma* is_dedekind_domain_iff
- \+ *lemma* is_dedekind_domain_inv_iff
- \+ *def* ring.dimension_le_one

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_mk
- \+ *lemma* mem_map
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+ *lemma* map_coe_ideal
- \+ *lemma* map_one
- \+ *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_mul
- \+ *lemma* map_map_symm
- \+ *lemma* map_symm_map
- \+/\- *lemma* map_equiv_apply
- \+ *lemma* exists_ne_zero_mem_is_integer
- \+ *lemma* map_ne_zero
- \+ *lemma* map_eq_zero_iff
- \+ *lemma* inv_eq
- \+ *lemma* div_zero
- \+ *lemma* inv_zero
- \+ *lemma* map_div
- \+ *lemma* map_inv

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* not_is_field_of_subsingleton
- \+ *lemma* exists_not_is_unit_of_not_is_field
- \+ *lemma* not_is_field_iff_exists_ideal_bot_lt_and_lt_top
- \+ *lemma* not_is_field_iff_exists_prime
- \+ *lemma* bot_lt_of_maximal

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* span_mul_span'
- \+ *lemma* span_singleton_mul_span_singleton

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* integral_closure_map_alg_equiv

Modified src/ring_theory/localization.lean
- \+ *lemma* alg_equiv_of_quotient_apply
- \+ *lemma* alg_equiv_of_quotient_symm_apply



## [2020-09-10 07:43:56](https://github.com/leanprover-community/mathlib/commit/8e9b1f0)
feat(linear_algebra): add `restrict` for endomorphisms ([#4053](https://github.com/leanprover-community/mathlib/pull/4053))
Add a `restrict` function for endomorphisms. Add some lemmas about the new function, including one about generalized eigenspaces. Add some additional lemmas about `linear_map.comp` that I do not use in the final proof, but still consider useful.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* restrict_apply
- \+ *lemma* subtype_comp_restrict
- \+ *lemma* restrict_eq_cod_restrict_dom_restrict
- \+ *lemma* restrict_eq_dom_restrict_cod_restrict
- \+ *lemma* add_comp
- \+ *lemma* comp_add
- \+ *lemma* comp_neg
- \+ *lemma* sub_comp
- \+ *lemma* comp_sub
- \+ *def* restrict

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* generalized_eigenspace_restrict



## [2020-09-10 05:42:47](https://github.com/leanprover-community/mathlib/commit/47264da)
feat(linear_algebra): tiny missing pieces ([#4089](https://github.com/leanprover-community/mathlib/pull/4089))
From the sphere eversion project.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* applyₗ

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* equiv_fin
- \+ *lemma* fin_basis



## [2020-09-10 01:34:24](https://github.com/leanprover-community/mathlib/commit/9f55ed7)
feat(data/polynomial/ring_division): make `polynomial.roots` a multiset ([#4061](https://github.com/leanprover-community/mathlib/pull/4061))
The original definition of `polynomial.roots` was basically "while ∃ x, p.is_root x { finset.insert x polynomial.roots }", so it was not
too hard to replace this with `multiset.cons`.
I tried to refactor most usages of `polynomial.roots` to talk about the multiset instead of coercing it to a finset, since that should give a bit more power to the results.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* degree_eq_zero_of_is_unit
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* prime_of_degree_eq_one_of_monic
- \+/\- *lemma* irreducible_of_degree_eq_one_of_monic
- \+ *lemma* root_multiplicity_zero
- \+ *lemma* root_multiplicity_eq_zero
- \+ *lemma* root_multiplicity_pos
- \+ *lemma* root_multiplicity_mul
- \+ *lemma* root_multiplicity_X_sub_C_self
- \+ *lemma* root_multiplicity_X_sub_C
- \+ *lemma* exists_multiset_roots
- \+/\- *lemma* roots_zero
- \+ *lemma* count_roots
- \+/\- *lemma* roots_mul
- \+/\- *lemma* roots_X_sub_C
- \+/\- *lemma* roots_C
- \- *lemma* exists_finset_roots
- \+/\- *theorem* prime_X_sub_C
- \+/\- *theorem* prime_X
- \+/\- *theorem* irreducible_X_sub_C
- \+/\- *theorem* irreducible_X
- \+/\- *theorem* eq_of_monic_of_associated
- \+/\- *def* nth_roots

Modified src/field_theory/finite.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/separable.lean
- \+ *lemma* multiplicity_le_one_of_seperable
- \+ *lemma* root_multiplicity_le_one_of_seperable
- \+ *lemma* count_roots_le_one
- \+ *lemma* nodup_roots
- \- *lemma* eq_prod_roots_of_separable
- \- *lemma* nat_degree_separable_eq_card_roots
- \- *lemma* degree_separable_eq_card_roots

Modified src/field_theory/splitting_field.lean
- \+ *lemma* eq_prod_roots_of_splits
- \+ *lemma* nat_degree_multiset_prod
- \+ *lemma* nat_degree_eq_card_roots
- \+ *lemma* degree_eq_card_roots

Modified src/linear_algebra/lagrange.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/multiplicity.lean
- \+ *lemma* dvd_iff_multiplicity_pos



## [2020-09-09 23:56:32](https://github.com/leanprover-community/mathlib/commit/660a6c4)
feat(topology): misc topological lemmas ([#4091](https://github.com/leanprover-community/mathlib/pull/4091))
From the sphere eversion project.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* is_countably_generated_principal
- \+ *lemma* inf
- \+ *lemma* inf_principal

Modified src/order/filter/basic.lean
- \+ *lemma* diff_mem_inf_principal_compl

Modified src/topology/bases.lean
- \+ *lemma* exists_dense_seq
- \+ *lemma* dense_seq_dense
- \+ *lemma* is_countably_generated_nhds
- \+ *lemma* is_countably_generated_nhds_within
- \+ *def* dense_seq

Modified src/topology/continuous_on.lean
- \+ *lemma* diff_mem_nhds_within_compl



## [2020-09-09 23:56:30](https://github.com/leanprover-community/mathlib/commit/9da39cf)
feat(ordered_field): missing inequality lemmas ([#4090](https://github.com/leanprover-community/mathlib/pull/4090))
From the sphere eversion project.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* inv_mul_le_iff
- \+ *lemma* inv_mul_le_iff'
- \+ *lemma* mul_inv_le_iff
- \+ *lemma* mul_inv_le_iff'
- \+ *lemma* inv_mul_lt_iff
- \+ *lemma* inv_mul_lt_iff'
- \+ *lemma* mul_inv_lt_iff
- \+ *lemma* mul_inv_lt_iff'



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
- \- *lemma* pderivative_add
- \- *lemma* pderivative_monomial
- \- *lemma* pderivative_C
- \- *lemma* pderivative_zero
- \- *lemma* pderivative.add_monoid_hom_apply
- \- *lemma* pderivative_eq_zero_of_not_mem_vars
- \- *lemma* pderivative_monomial_single
- \- *lemma* pderivative_monomial_mul
- \- *lemma* pderivative_mul
- \- *lemma* pderivative_C_mul
- \- *def* pderivative
- \- *def* pderivative.add_monoid_hom

Created src/data/mv_polynomial/pderivative.lean
- \+ *lemma* pderivative_add
- \+ *lemma* pderivative_monomial
- \+ *lemma* pderivative_C
- \+ *lemma* pderivative_zero
- \+ *lemma* pderivative.add_monoid_hom_apply
- \+ *lemma* pderivative_eq_zero_of_not_mem_vars
- \+ *lemma* pderivative_monomial_single
- \+ *lemma* pderivative_monomial_mul
- \+ *lemma* pderivative_mul
- \+ *lemma* pderivative_C_mul
- \+ *def* pderivative
- \+ *def* pderivative.add_monoid_hom



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
- \+ *lemma* subset_affine_span
- \+ *lemma* affine_span_mono
- \+ *lemma* affine_span_insert_affine_span
- \+ *lemma* affine_span_insert_eq_affine_span

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_def
- \+ *lemma* affine_independent_iff_of_fintype
- \+ *lemma* affine_independent_of_subset_affine_independent
- \+ *lemma* affine_independent_of_affine_independent_set_of_injective



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
- \+ *lemma* le_cSup_image
- \+ *lemma* cSup_image_le
- \+ *lemma* cInf_image_le
- \+ *lemma* le_cInf_image
- \+ *lemma* subset_Sup_def
- \+ *lemma* subset_Sup_of_within
- \+ *lemma* subset_Inf_def
- \+ *lemma* subset_Inf_of_within
- \+ *lemma* Sup_within_of_ord_connected
- \+ *lemma* Inf_within_of_ord_connected

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
- \- *lemma* C_0
- \- *lemma* C_1
- \- *lemma* C_mul_monomial
- \- *lemma* C_add
- \- *lemma* C_mul
- \- *lemma* C_pow
- \- *lemma* C_injective
- \- *lemma* C_inj
- \- *lemma* C_eq_coe_nat
- \- *lemma* X_pow_eq_single
- \- *lemma* monomial_add_single
- \- *lemma* monomial_single_add
- \- *lemma* single_eq_C_mul_X
- \- *lemma* monomial_add
- \- *lemma* monomial_mul
- \- *lemma* monomial_zero
- \- *lemma* sum_monomial
- \- *lemma* monomial_eq
- \- *lemma* induction_on
- \- *lemma* hom_eq_hom
- \- *lemma* is_id
- \- *lemma* ring_hom_ext
- \- *lemma* alg_hom_ext
- \- *lemma* alg_hom_C
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* coeff_add
- \- *lemma* coeff_zero
- \- *lemma* coeff_zero_X
- \- *lemma* coeff_sum
- \- *lemma* monic_monomial_eq
- \- *lemma* coeff_monomial
- \- *lemma* coeff_C
- \- *lemma* coeff_X_pow
- \- *lemma* coeff_X'
- \- *lemma* coeff_X
- \- *lemma* coeff_C_mul
- \- *lemma* coeff_mul
- \- *lemma* coeff_mul_X
- \- *lemma* coeff_mul_X'
- \- *lemma* eq_zero_iff
- \- *lemma* ne_zero_iff
- \- *lemma* exists_coeff_ne_zero
- \- *lemma* constant_coeff_eq
- \- *lemma* constant_coeff_C
- \- *lemma* constant_coeff_X
- \- *lemma* constant_coeff_monomial
- \- *lemma* support_sum_monomial_coeff
- \- *lemma* as_sum
- \- *lemma* eval₂_eq
- \- *lemma* eval₂_eq'
- \- *lemma* eval₂_zero
- \- *lemma* eval₂_add
- \- *lemma* eval₂_monomial
- \- *lemma* eval₂_C
- \- *lemma* eval₂_one
- \- *lemma* eval₂_X
- \- *lemma* eval₂_mul_monomial
- \- *lemma* eval₂_mul
- \- *lemma* eval₂_pow
- \- *lemma* coe_eval₂_hom
- \- *lemma* eval₂_hom_congr
- \- *lemma* eval₂_hom_C
- \- *lemma* eval₂_hom_X'
- \- *lemma* comp_eval₂_hom
- \- *lemma* map_eval₂_hom
- \- *lemma* eval₂_hom_monomial
- \- *lemma* eval₂_comp_left
- \- *lemma* eval₂_eta
- \- *lemma* eval₂_congr
- \- *lemma* eval₂_prod
- \- *lemma* eval₂_sum
- \- *lemma* eval₂_assoc
- \- *lemma* eval_eq
- \- *lemma* eval_eq'
- \- *lemma* eval_monomial
- \- *lemma* eval_C
- \- *lemma* eval_X
- \- *lemma* eval_sum
- \- *lemma* eval_prod
- \- *lemma* eval₂_comp_right
- \- *lemma* map_eval₂
- \- *lemma* coeff_map
- \- *lemma* map_injective
- \- *lemma* eval_map
- \- *lemma* eval₂_map
- \- *lemma* eval₂_hom_map_hom
- \- *lemma* support_map_subset
- \- *lemma* support_map_of_injective
- \- *lemma* degrees_monomial
- \- *lemma* degrees_monomial_eq
- \- *lemma* degrees_C
- \- *lemma* degrees_X
- \- *lemma* degrees_zero
- \- *lemma* degrees_one
- \- *lemma* degrees_add
- \- *lemma* degrees_sum
- \- *lemma* degrees_mul
- \- *lemma* degrees_prod
- \- *lemma* degrees_pow
- \- *lemma* mem_degrees
- \- *lemma* le_degrees_add
- \- *lemma* degrees_add_of_disjoint
- \- *lemma* degrees_map
- \- *lemma* degrees_map_of_injective
- \- *lemma* vars_0
- \- *lemma* vars_monomial
- \- *lemma* vars_C
- \- *lemma* vars_X
- \- *lemma* mem_support_not_mem_vars_zero
- \- *lemma* vars_add_subset
- \- *lemma* vars_add_of_disjoint
- \- *lemma* vars_sum_subset
- \- *lemma* vars_sum_of_disjoint
- \- *lemma* vars_map
- \- *lemma* vars_map_of_injective
- \- *lemma* vars_monomial_single
- \- *lemma* mem_vars
- \- *lemma* vars_eq_support_bind_support
- \- *lemma* total_degree_eq
- \- *lemma* total_degree_le_degrees_card
- \- *lemma* total_degree_C
- \- *lemma* total_degree_zero
- \- *lemma* total_degree_one
- \- *lemma* total_degree_X
- \- *lemma* total_degree_add
- \- *lemma* total_degree_mul
- \- *lemma* total_degree_pow
- \- *lemma* total_degree_list_prod
- \- *lemma* total_degree_multiset_prod
- \- *lemma* total_degree_finset_prod
- \- *lemma* exists_degree_lt
- \- *lemma* coeff_eq_zero_of_total_degree_lt
- \- *lemma* aeval_eq_eval₂_hom
- \- *lemma* aeval_X
- \- *lemma* aeval_C
- \- *lemma* comp_aeval
- \- *lemma* map_aeval
- \- *lemma* aeval_zero
- \- *lemma* aeval_zero'
- \- *lemma* aeval_monomial
- \- *lemma* eval₂_hom_eq_constant_coeff_of_vars
- \- *lemma* aeval_eq_constant_coeff_of_vars
- \- *lemma* C_sub
- \- *lemma* C_neg
- \- *lemma* coeff_neg
- \- *lemma* coeff_sub
- \- *lemma* smul_eq_C_mul
- \- *lemma* smul_eval
- \- *lemma* degrees_neg
- \- *lemma* degrees_sub
- \- *lemma* vars_neg
- \- *lemma* vars_sub_subset
- \- *lemma* vars_sub_of_disjoint
- \- *lemma* eval₂_sub
- \- *lemma* eval₂_neg
- \- *lemma* hom_C
- \- *lemma* eval₂_hom_X
- \- *lemma* total_degree_neg
- \- *lemma* total_degree_sub
- \- *lemma* rename_C
- \- *lemma* rename_X
- \- *lemma* map_rename
- \- *lemma* rename_rename
- \- *lemma* rename_id
- \- *lemma* rename_monomial
- \- *lemma* rename_eq
- \- *lemma* rename_injective
- \- *lemma* total_degree_rename_le
- \- *lemma* eval₂_rename
- \- *lemma* eval₂_hom_rename
- \- *lemma* rename_eval₂
- \- *lemma* rename_prodmk_eval₂
- \- *lemma* eval₂_rename_prodmk
- \- *lemma* eval_rename_prodmk
- \- *lemma* eval₂_cast_comp
- \- *lemma* sum_to_iter_C
- \- *lemma* sum_to_iter_Xl
- \- *lemma* sum_to_iter_Xr
- \- *lemma* iter_to_sum_C_C
- \- *lemma* iter_to_sum_X
- \- *lemma* iter_to_sum_C_X
- \- *lemma* pderivative_add
- \- *lemma* pderivative_monomial
- \- *lemma* pderivative_C
- \- *lemma* pderivative_zero
- \- *lemma* pderivative.add_monoid_hom_apply
- \- *lemma* pderivative_eq_zero_of_not_mem_vars
- \- *lemma* pderivative_monomial_single
- \- *lemma* pderivative_monomial_mul
- \- *lemma* pderivative_mul
- \- *lemma* pderivative_C_mul
- \- *theorem* algebra_map_eq
- \- *theorem* induction_on'
- \- *theorem* eval_assoc
- \- *theorem* map_monomial
- \- *theorem* map_C
- \- *theorem* map_X
- \- *theorem* map_id
- \- *theorem* map_map
- \- *theorem* eval₂_eq_eval_map
- \- *theorem* aeval_def
- \- *theorem* eval_unique
- \- *theorem* C_mul'
- \- *theorem* exists_finset_rename
- \- *theorem* exists_fin_rename
- \- *def* mv_polynomial
- \- *def* coeff_coe_to_fun
- \- *def* monomial
- \- *def* C
- \- *def* X
- \- *def* coeff
- \- *def* constant_coeff
- \- *def* eval₂
- \- *def* eval₂_hom
- \- *def* eval
- \- *def* map
- \- *def* degrees
- \- *def* vars
- \- *def* degree_of
- \- *def* total_degree
- \- *def* aeval
- \- *def* hom_equiv
- \- *def* rename
- \- *def* pempty_ring_equiv
- \- *def* punit_ring_equiv
- \- *def* ring_equiv_of_equiv
- \- *def* ring_equiv_congr
- \- *def* sum_to_iter
- \- *def* iter_to_sum
- \- *def* mv_polynomial_equiv_mv_polynomial
- \- *def* sum_ring_equiv
- \- *def* option_equiv_left
- \- *def* option_equiv_right
- \- *def* fin_succ_equiv
- \- *def* pderivative
- \- *def* pderivative.add_monoid_hom

Created src/data/mv_polynomial/basic.lean
- \+ *lemma* C_0
- \+ *lemma* C_1
- \+ *lemma* C_mul_monomial
- \+ *lemma* C_add
- \+ *lemma* C_mul
- \+ *lemma* C_pow
- \+ *lemma* C_injective
- \+ *lemma* C_inj
- \+ *lemma* C_eq_coe_nat
- \+ *lemma* X_pow_eq_single
- \+ *lemma* monomial_add_single
- \+ *lemma* monomial_single_add
- \+ *lemma* single_eq_C_mul_X
- \+ *lemma* monomial_add
- \+ *lemma* monomial_mul
- \+ *lemma* monomial_zero
- \+ *lemma* sum_monomial
- \+ *lemma* monomial_eq
- \+ *lemma* induction_on
- \+ *lemma* hom_eq_hom
- \+ *lemma* is_id
- \+ *lemma* ring_hom_ext
- \+ *lemma* alg_hom_ext
- \+ *lemma* alg_hom_C
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coeff_add
- \+ *lemma* coeff_zero
- \+ *lemma* coeff_zero_X
- \+ *lemma* coeff_sum
- \+ *lemma* monic_monomial_eq
- \+ *lemma* coeff_monomial
- \+ *lemma* coeff_C
- \+ *lemma* coeff_X_pow
- \+ *lemma* coeff_X'
- \+ *lemma* coeff_X
- \+ *lemma* coeff_C_mul
- \+ *lemma* coeff_mul
- \+ *lemma* coeff_mul_X
- \+ *lemma* coeff_mul_X'
- \+ *lemma* eq_zero_iff
- \+ *lemma* ne_zero_iff
- \+ *lemma* exists_coeff_ne_zero
- \+ *lemma* constant_coeff_eq
- \+ *lemma* constant_coeff_C
- \+ *lemma* constant_coeff_X
- \+ *lemma* constant_coeff_monomial
- \+ *lemma* support_sum_monomial_coeff
- \+ *lemma* as_sum
- \+ *lemma* eval₂_eq
- \+ *lemma* eval₂_eq'
- \+ *lemma* eval₂_zero
- \+ *lemma* eval₂_add
- \+ *lemma* eval₂_monomial
- \+ *lemma* eval₂_C
- \+ *lemma* eval₂_one
- \+ *lemma* eval₂_X
- \+ *lemma* eval₂_mul_monomial
- \+ *lemma* eval₂_mul
- \+ *lemma* eval₂_pow
- \+ *lemma* coe_eval₂_hom
- \+ *lemma* eval₂_hom_congr
- \+ *lemma* eval₂_hom_C
- \+ *lemma* eval₂_hom_X'
- \+ *lemma* comp_eval₂_hom
- \+ *lemma* map_eval₂_hom
- \+ *lemma* eval₂_hom_monomial
- \+ *lemma* eval₂_comp_left
- \+ *lemma* eval₂_eta
- \+ *lemma* eval₂_congr
- \+ *lemma* eval₂_prod
- \+ *lemma* eval₂_sum
- \+ *lemma* eval₂_assoc
- \+ *lemma* eval_eq
- \+ *lemma* eval_eq'
- \+ *lemma* eval_monomial
- \+ *lemma* eval_C
- \+ *lemma* eval_X
- \+ *lemma* eval_sum
- \+ *lemma* eval_prod
- \+ *lemma* eval₂_comp_right
- \+ *lemma* map_eval₂
- \+ *lemma* coeff_map
- \+ *lemma* map_injective
- \+ *lemma* eval_map
- \+ *lemma* eval₂_map
- \+ *lemma* eval₂_hom_map_hom
- \+ *lemma* support_map_subset
- \+ *lemma* support_map_of_injective
- \+ *lemma* aeval_eq_eval₂_hom
- \+ *lemma* aeval_X
- \+ *lemma* aeval_C
- \+ *lemma* comp_aeval
- \+ *lemma* map_aeval
- \+ *lemma* aeval_zero
- \+ *lemma* aeval_zero'
- \+ *lemma* aeval_monomial
- \+ *theorem* algebra_map_eq
- \+ *theorem* induction_on'
- \+ *theorem* eval_assoc
- \+ *theorem* map_monomial
- \+ *theorem* map_C
- \+ *theorem* map_X
- \+ *theorem* map_id
- \+ *theorem* map_map
- \+ *theorem* eval₂_eq_eval_map
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *def* mv_polynomial
- \+ *def* coeff_coe_to_fun
- \+ *def* monomial
- \+ *def* C
- \+ *def* X
- \+ *def* coeff
- \+ *def* constant_coeff
- \+ *def* eval₂
- \+ *def* eval₂_hom
- \+ *def* eval
- \+ *def* map
- \+ *def* aeval

Created src/data/mv_polynomial/comm_ring.lean
- \+ *lemma* C_sub
- \+ *lemma* C_neg
- \+ *lemma* coeff_neg
- \+ *lemma* coeff_sub
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* smul_eval
- \+ *lemma* degrees_neg
- \+ *lemma* degrees_sub
- \+ *lemma* vars_neg
- \+ *lemma* vars_sub_subset
- \+ *lemma* vars_sub_of_disjoint
- \+ *lemma* eval₂_sub
- \+ *lemma* eval₂_neg
- \+ *lemma* hom_C
- \+ *lemma* eval₂_hom_X
- \+ *lemma* total_degree_neg
- \+ *lemma* total_degree_sub
- \+ *theorem* C_mul'
- \+ *def* hom_equiv

Created src/data/mv_polynomial/default.lean


Created src/data/mv_polynomial/equiv.lean
- \+ *lemma* sum_to_iter_C
- \+ *lemma* sum_to_iter_Xl
- \+ *lemma* sum_to_iter_Xr
- \+ *lemma* iter_to_sum_C_C
- \+ *lemma* iter_to_sum_X
- \+ *lemma* iter_to_sum_C_X
- \+ *def* pempty_ring_equiv
- \+ *def* punit_ring_equiv
- \+ *def* ring_equiv_of_equiv
- \+ *def* ring_equiv_congr
- \+ *def* sum_to_iter
- \+ *def* iter_to_sum
- \+ *def* mv_polynomial_equiv_mv_polynomial
- \+ *def* sum_ring_equiv
- \+ *def* option_equiv_left
- \+ *def* option_equiv_right
- \+ *def* fin_succ_equiv

Created src/data/mv_polynomial/pderiv.lean
- \+ *lemma* pderivative_add
- \+ *lemma* pderivative_monomial
- \+ *lemma* pderivative_C
- \+ *lemma* pderivative_zero
- \+ *lemma* pderivative.add_monoid_hom_apply
- \+ *lemma* pderivative_eq_zero_of_not_mem_vars
- \+ *lemma* pderivative_monomial_single
- \+ *lemma* pderivative_monomial_mul
- \+ *lemma* pderivative_mul
- \+ *lemma* pderivative_C_mul
- \+ *def* pderivative
- \+ *def* pderivative.add_monoid_hom

Created src/data/mv_polynomial/rename.lean
- \+ *lemma* rename_C
- \+ *lemma* rename_X
- \+ *lemma* map_rename
- \+ *lemma* rename_rename
- \+ *lemma* rename_id
- \+ *lemma* rename_monomial
- \+ *lemma* rename_eq
- \+ *lemma* rename_injective
- \+ *lemma* total_degree_rename_le
- \+ *lemma* eval₂_rename
- \+ *lemma* eval₂_hom_rename
- \+ *lemma* rename_eval₂
- \+ *lemma* rename_prodmk_eval₂
- \+ *lemma* eval₂_rename_prodmk
- \+ *lemma* eval_rename_prodmk
- \+ *lemma* eval₂_cast_comp
- \+ *theorem* exists_finset_rename
- \+ *theorem* exists_fin_rename
- \+ *def* rename

Created src/data/mv_polynomial/variables.lean
- \+ *lemma* degrees_monomial
- \+ *lemma* degrees_monomial_eq
- \+ *lemma* degrees_C
- \+ *lemma* degrees_X
- \+ *lemma* degrees_zero
- \+ *lemma* degrees_one
- \+ *lemma* degrees_add
- \+ *lemma* degrees_sum
- \+ *lemma* degrees_mul
- \+ *lemma* degrees_prod
- \+ *lemma* degrees_pow
- \+ *lemma* mem_degrees
- \+ *lemma* le_degrees_add
- \+ *lemma* degrees_add_of_disjoint
- \+ *lemma* degrees_map
- \+ *lemma* degrees_map_of_injective
- \+ *lemma* vars_0
- \+ *lemma* vars_monomial
- \+ *lemma* vars_C
- \+ *lemma* vars_X
- \+ *lemma* mem_support_not_mem_vars_zero
- \+ *lemma* vars_add_subset
- \+ *lemma* vars_add_of_disjoint
- \+ *lemma* vars_sum_subset
- \+ *lemma* vars_sum_of_disjoint
- \+ *lemma* vars_map
- \+ *lemma* vars_map_of_injective
- \+ *lemma* vars_monomial_single
- \+ *lemma* mem_vars
- \+ *lemma* vars_eq_support_bind_support
- \+ *lemma* total_degree_eq
- \+ *lemma* total_degree_le_degrees_card
- \+ *lemma* total_degree_C
- \+ *lemma* total_degree_zero
- \+ *lemma* total_degree_one
- \+ *lemma* total_degree_X
- \+ *lemma* total_degree_add
- \+ *lemma* total_degree_mul
- \+ *lemma* total_degree_pow
- \+ *lemma* total_degree_list_prod
- \+ *lemma* total_degree_multiset_prod
- \+ *lemma* total_degree_finset_prod
- \+ *lemma* exists_degree_lt
- \+ *lemma* coeff_eq_zero_of_total_degree_lt
- \+ *lemma* eval₂_hom_eq_constant_coeff_of_vars
- \+ *lemma* aeval_eq_constant_coeff_of_vars
- \+ *def* degrees
- \+ *def* vars
- \+ *def* degree_of
- \+ *def* total_degree

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-09-09 04:32:30](https://github.com/leanprover-community/mathlib/commit/d5580f4)
feat(data/equiv/basic): add ext_iff for perm ([#4067](https://github.com/leanprover-community/mathlib/pull/4067))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* ext_iff
- \+ *lemma* perm.ext_iff



## [2020-09-08 21:33:25](https://github.com/leanprover-community/mathlib/commit/f5ee84c)
feat(analysis/special_functions/pow): Added lemmas bounding rpow in ennreal ([#4039](https://github.com/leanprover-community/mathlib/pull/4039))
Continuation of [#3715](https://github.com/leanprover-community/mathlib/pull/3715). Added lemmas in `ennreal` corresponding to the `real` and `nnreal` lemmas added in that PR
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_lt_one
- \+/\- *lemma* rpow_le_one
- \+ *lemma* rpow_lt_one_of_one_lt_of_neg
- \+ *lemma* rpow_le_one_of_one_le_of_neg
- \+/\- *lemma* one_le_rpow
- \+ *lemma* one_lt_rpow_of_pos_of_lt_one_of_neg
- \+ *lemma* one_le_rpow_of_pos_of_le_one_of_neg



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
- \+ *lemma* reflection_mem_of_le_of_mem
- \+ *lemma* reflection_orthogonal_vadd
- \+ *lemma* reflection_vadd_smul_vsub_orthogonal_projection



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
- \+ *lemma* mul_one'



## [2020-09-07 19:41:48](https://github.com/leanprover-community/mathlib/commit/c7d6a8e)
feat(ring_theory/unique_factorization_domain): descending chain condition for divisibility ([#4031](https://github.com/leanprover-community/mathlib/pull/4031))
Defines the strict divisibility relation `dvd_not_unit`
Defines class `wf_dvd_monoid`, indicating that `dvd_not_unit` is well-founded
Provides instances of `wf_dvd_monoid`
Prepares to refactor `unique_factorization_domain` as a predicate extending `wf_dvd_monoid`
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* le_of_mul_le_mul_right
- \+ *theorem* mk_surjective
- \+ *theorem* irreducible_mk
- \+ *theorem* mk_dvd_not_unit_mk_iff
- \+ *theorem* dvd_not_unit_of_lt
- \+ *theorem* dvd_not_unit_iff_lt
- \- *theorem* irreducible_mk_iff

Modified src/algebra/divisibility.lean
- \+ *lemma* dvd_not_unit_of_dvd_of_not_dvd
- \+ *def* dvd_not_unit

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/noetherian.lean
- \- *lemma* well_founded_dvd_not_unit
- \- *lemma* exists_irreducible_factor
- \- *lemma* irreducible_induction_on
- \- *lemma* exists_factors

Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* exists_irreducible_factor
- \+ *lemma* induction_on_irreducible
- \+ *lemma* exists_factors
- \+ *theorem* of_wf_dvd_monoid_associates
- \+ *theorem* well_founded_associates
- \+ *theorem* wf_dvd_monoid.of_well_founded_associates
- \+ *theorem* wf_dvd_monoid.iff_well_founded_associates



## [2020-09-07 17:54:54](https://github.com/leanprover-community/mathlib/commit/851e83e)
feat(category_theory): colimits for pi categories ([#4054](https://github.com/leanprover-community/mathlib/pull/4054))
#### Estimated changes
Modified src/category_theory/limits/pi.lean
- \+ *def* cocone_comp_eval
- \+ *def* cocone_of_cocone_comp_eval
- \+ *def* cocone_of_cocone_eval_is_colimit
- \+ *def* has_colimit_of_has_colimit_comp_eval



## [2020-09-07 13:36:36](https://github.com/leanprover-community/mathlib/commit/c259305)
feat(topology/algebra/floor_ring): add basic topological facts about `floor`, `ceil` and `fract` ([#4042](https://github.com/leanprover-community/mathlib/pull/4042))
From the sphere eversion project
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* floor_eq_on_Ico
- \+ *lemma* floor_eq_on_Ico'
- \+ *lemma* ceil_eq_iff
- \+ *lemma* ceil_eq_on_Ioc
- \+ *lemma* ceil_eq_on_Ioc'

Created src/topology/algebra/floor_ring.lean
- \+ *lemma* tendsto_floor_at_top
- \+ *lemma* tendsto_floor_at_bot
- \+ *lemma* tendsto_ceil_at_top
- \+ *lemma* tendsto_ceil_at_bot
- \+ *lemma* continuous_on_floor
- \+ *lemma* continuous_on_ceil
- \+ *lemma* tendsto_floor_right'
- \+ *lemma* tendsto_ceil_left'
- \+ *lemma* tendsto_floor_right
- \+ *lemma* tendsto_ceil_left
- \+ *lemma* tendsto_floor_left
- \+ *lemma* tendsto_ceil_right
- \+ *lemma* tendsto_floor_left'
- \+ *lemma* tendsto_ceil_right'
- \+ *lemma* continuous_on_fract
- \+ *lemma* tendsto_fract_left'
- \+ *lemma* tendsto_fract_left
- \+ *lemma* tendsto_fract_right'
- \+ *lemma* tendsto_fract_right
- \+ *lemma* continuous_on.comp_fract'
- \+ *lemma* continuous_on.comp_fract

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_inv_nhds_within_Ici
- \+ *lemma* tendsto_inv_nhds_within_Iic
- \+ *lemma* tendsto_inv_nhds_within_Ici_inv
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
- \- *lemma* basic_open_open
- \+/\- *def* basic_open

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* res_apply
- \+ *lemma* const_apply
- \+ *lemma* const_apply'
- \+ *lemma* exists_const
- \+ *lemma* res_const
- \+ *lemma* res_const'
- \+ *lemma* const_zero
- \+ *lemma* const_self
- \+ *lemma* const_one
- \+ *lemma* const_add
- \+ *lemma* const_mul
- \+ *lemma* const_ext
- \+ *lemma* const_congr
- \+ *lemma* const_mul_rev
- \+ *lemma* const_mul_cancel
- \+ *lemma* const_mul_cancel'
- \+ *lemma* to_open_res
- \+ *lemma* to_open_apply
- \+ *lemma* to_open_eq_const
- \+ *lemma* to_open_germ
- \+ *lemma* germ_to_open
- \+ *lemma* germ_to_top
- \+ *lemma* is_unit_to_basic_open_self
- \+ *lemma* to_basic_open_mk'
- \+ *lemma* localization_to_basic_open
- \+ *lemma* to_basic_open_to_map
- \+ *lemma* is_unit_to_stalk
- \+ *lemma* localization_to_stalk_of
- \+ *lemma* localization_to_stalk_mk'
- \+ *lemma* coe_open_to_localization
- \+ *lemma* open_to_localization_apply
- \+ *lemma* germ_comp_stalk_to_fiber_ring_hom
- \+ *lemma* stalk_to_fiber_ring_hom_germ'
- \+ *lemma* stalk_to_fiber_ring_hom_germ
- \+ *lemma* to_stalk_comp_stalk_to_fiber_ring_hom
- \+ *lemma* stalk_to_fiber_ring_hom_to_stalk
- \+ *def* const
- \+ *def* to_open
- \+ *def* to_stalk
- \+ *def* to_basic_open
- \+ *def* localization_to_stalk
- \+ *def* open_to_localization
- \+/\- *def* stalk_to_fiber_ring_hom
- \+/\- *def* stalk_iso
- \- *def* compare_stalks

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* germ_ext
- \+ *lemma* stalk_hom_ext



## [2020-09-07 00:51:55](https://github.com/leanprover-community/mathlib/commit/2e198b4)
chore(scripts): update nolints.txt ([#4058](https://github.com/leanprover-community/mathlib/pull/4058))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-09-06 23:47:49](https://github.com/leanprover-community/mathlib/commit/4662b20)
feat(category_theory): definition of `diag` in `binary_products` ([#4051](https://github.com/leanprover-community/mathlib/pull/4051))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.diag_map
- \+ *lemma* prod.diag_map_fst_snd
- \+ *lemma* prod.diag_map_comp
- \+ *lemma* prod.diag_map_fst_snd_comp
- \+ *lemma* coprod.map_codiag
- \+ *lemma* coprod.map_inl_inr_codiag
- \+ *lemma* coprod.map_comp_codiag
- \+ *lemma* coprod.map_comp_inl_inr_codiag



## [2020-09-06 23:08:44](https://github.com/leanprover-community/mathlib/commit/4945c77)
cleanup(ring_theory/ring_invo): update old module doc, add ring_invo.involution with cleaner statement ([#4052](https://github.com/leanprover-community/mathlib/pull/4052))
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean


Renamed src/ring_theory/maps.lean to src/ring_theory/ring_invo.lean
- \+ *lemma* involution



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
- \+ *lemma* generalized_eigenspace_le_generalized_eigenspace_findim
- \+ *lemma* generalized_eigenspace_eq_generalized_eigenspace_findim_of_le

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_lt_findim_of_lt
- \+ *lemma* exists_ker_pow_eq_ker_pow_succ
- \+ *lemma* ker_pow_constant
- \+ *lemma* ker_pow_eq_ker_pow_findim_of_le
- \+ *lemma* ker_pow_le_ker_pow_findim



## [2020-09-06 11:28:33](https://github.com/leanprover-community/mathlib/commit/fabf34f)
feat(analysis/special_functions/trigonometric): Added lemmas for deriv of tan ([#3746](https://github.com/leanprover-community/mathlib/pull/3746))
I added lemmas for the derivative of the tangent function in both the complex and real namespaces. I also corrected two typos in comment lines.
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* cos_pos_of_mem_Ioo
- \+ *lemma* cos_nonneg_of_mem_Icc
- \+ *lemma* exp_pi_mul_I
- \+ *lemma* has_deriv_at_tan
- \+ *lemma* differentiable_at_tan
- \+ *lemma* deriv_tan
- \+/\- *lemma* continuous_tan
- \+ *lemma* continuous_on_tan
- \+ *lemma* has_deriv_at_tan_of_mem_Ioo
- \+ *lemma* differentiable_at_tan_of_mem_Ioo
- \+ *lemma* deriv_tan_of_mem_Ioo
- \- *lemma* cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
- \- *lemma* cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
- \+/\- *theorem* cos_eq_zero_iff
- \+/\- *theorem* cos_ne_zero_iff



## [2020-09-06 06:48:30](https://github.com/leanprover-community/mathlib/commit/6296386)
feat(data/mv_polynomial): fill in API for vars ([#4018](https://github.com/leanprover-community/mathlib/pull/4018))
`mv_polynomial.vars` was missing a lot of API. This doesn't cover everything, but it fleshes out the theory quite a bit. There's probably more coming eventually -- this is what we have now.
Co-authored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* support_map_subset
- \+ *lemma* support_map_of_injective
- \+ *lemma* mem_degrees
- \+ *lemma* le_degrees_add
- \+ *lemma* degrees_add_of_disjoint
- \+ *lemma* degrees_map
- \+ *lemma* degrees_map_of_injective
- \+ *lemma* vars_add_subset
- \+ *lemma* vars_add_of_disjoint
- \+ *lemma* vars_sum_subset
- \+ *lemma* vars_sum_of_disjoint
- \+ *lemma* vars_map
- \+ *lemma* vars_map_of_injective
- \+ *lemma* vars_monomial_single
- \+ *lemma* mem_vars
- \+ *lemma* vars_eq_support_bind_support
- \+ *lemma* eval₂_hom_eq_constant_coeff_of_vars
- \+ *lemma* aeval_eq_constant_coeff_of_vars
- \+ *lemma* vars_neg
- \+ *lemma* vars_sub_subset
- \+ *lemma* vars_sub_of_disjoint



## [2020-09-06 05:07:42](https://github.com/leanprover-community/mathlib/commit/7b3c653)
chore(data/finset/lattice): remove unneeded assumptions ([#4020](https://github.com/leanprover-community/mathlib/pull/4020))
#### Estimated changes
Modified src/combinatorics/composition.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* min'_singleton
- \+/\- *lemma* max'_singleton
- \+/\- *lemma* min'_lt_max'_of_card
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_max'
- \+/\- *theorem* min'_lt_max'

Modified src/data/finset/sort.lean
- \+ *lemma* sorted_zero_eq_min'_aux
- \+/\- *lemma* sorted_zero_eq_min'
- \+ *lemma* min'_eq_sorted_zero
- \+ *lemma* sorted_last_eq_max'_aux
- \+/\- *lemma* sorted_last_eq_max'
- \+ *lemma* max'_eq_sorted_last
- \+/\- *lemma* mono_of_fin_zero
- \+/\- *lemma* mono_of_fin_last

Modified src/order/filter/at_top_bot.lean




## [2020-09-05 13:51:33](https://github.com/leanprover-community/mathlib/commit/815a2f9)
feat(computability/encoding): define encoding of basic data types ([#3976](https://github.com/leanprover-community/mathlib/pull/3976))
We define the encoding of natural numbers and booleans to strings for Turing machines to be used in our future PR on polynomial time computation on Turing machines.
#### Estimated changes
Created src/computability/encoding.lean
- \+ *lemma* left_inverse_section_inclusion
- \+ *lemma* inclusion_bool_Γ'_injective
- \+ *lemma* encode_pos_num_nonempty
- \+ *lemma* decode_encode_pos_num
- \+ *lemma* decode_encode_num
- \+ *lemma* decode_encode_nat
- \+ *lemma* unary_decode_encode_nat
- \+ *lemma* decode_encode_bool
- \+ *def* inclusion_bool_Γ'
- \+ *def* section_Γ'_bool
- \+ *def* encode_pos_num
- \+ *def* encode_num
- \+ *def* encode_nat
- \+ *def* decode_pos_num
- \+ *def* decode_num
- \+ *def* decode_nat
- \+ *def* encoding_nat_bool
- \+ *def* fin_encoding_nat_bool
- \+ *def* encoding_nat_Γ'
- \+ *def* fin_encoding_nat_Γ'
- \+ *def* unary_encode_nat
- \+ *def* unary_decode_nat
- \+ *def* unary_fin_encoding_nat
- \+ *def* encode_bool
- \+ *def* decode_bool
- \+ *def* fin_encoding_bool_bool



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
- \+ *theorem* is_integral
- \+ *theorem* min_poly_dvd_char_poly



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
- \+/\- *lemma* to_fun_as_coe
- \+/\- *lemma* inv_fun_as_coe

Modified src/data/equiv/local_equiv.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* mem_atlas_iff
- \+/\- *lemma* mem_chart_target_iff
- \+/\- *lemma* coe_chart_at_symm_fst
- \+ *lemma* tangent_bundle.proj_apply
- \+ *lemma* tangent_bundle_model_space_homeomorph_coe
- \+ *lemma* tangent_bundle_model_space_homeomorph_coe_symm
- \- *lemma* tangent_bundle_model_space_topology_eq_prod
- \+/\- *def* tangent_space
- \+/\- *def* tangent_bundle
- \+ *def* tangent_bundle_model_space_homeomorph

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* tangent_map_chart_symm

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/topological_fiber_bundle.lean
- \+/\- *def* total_space



## [2020-09-04 00:52:11](https://github.com/leanprover-community/mathlib/commit/ecf18c6)
refactor(field_theory/minimal_polynomial, *): make `aeval`, `is_integral`, and `minimal_polynomial` noncommutative ([#4001](https://github.com/leanprover-community/mathlib/pull/4001))
Makes `aeval`, `is_integral`, and `minimal_polynomial` compatible with noncommutative algebras
Renames `eval₂_ring_hom_noncomm` to `eval₂_ring_hom'`
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/eval.lean
- \+/\- *lemma* eval₂_mul_noncomm
- \+/\- *lemma* eval₂_list_prod_noncomm
- \+ *def* eval₂_ring_hom'
- \- *def* eval₂_ring_hom_noncomm

Modified src/field_theory/minimal_polynomial.lean


Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* ker_eval₂_ring_hom'_unit_polynomial
- \- *lemma* ker_eval₂_ring_hom_noncomm_unit_polynomial

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *theorem* is_integral_of_noetherian
- \+ *theorem* is_integral_of_submodule_noetherian
- \- *theorem* is_integral_of_noetherian'



## [2020-09-03 21:00:06](https://github.com/leanprover-community/mathlib/commit/e3057ba)
doc(slim_check): add suggestion ([#4024](https://github.com/leanprover-community/mathlib/pull/4024))
#### Estimated changes
Modified src/tactic/slim_check.lean




## [2020-09-03 19:18:55](https://github.com/leanprover-community/mathlib/commit/a056ccb)
feat(slim_check): subtype instances for `le` `lt` and `list.perm` ([#4027](https://github.com/leanprover-community/mathlib/pull/4027))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* perm_insert_nth

Modified src/data/list/sort.lean


Modified src/testing/slim_check/gen.lean
- \+ *def* permutation_of

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
- \+/\- *lemma* ext
- \+/\- *lemma* coe_sub
- \+ *lemma* norm_def
- \+ *lemma* norm_le_one
- \+/\- *lemma* norm_one
- \+ *lemma* norm_mul
- \+ *lemma* norm_pow
- \+ *lemma* norm_eq_of_norm_add_lt_right
- \+ *lemma* norm_eq_of_norm_add_lt_left
- \+ *lemma* norm_int_cast_eq_padic_norm
- \+ *lemma* norm_eq_padic_norm
- \+ *lemma* exists_pow_neg_lt
- \+ *lemma* exists_pow_neg_lt_rat
- \+/\- *lemma* norm_int_lt_one_iff_dvd
- \+ *lemma* norm_int_le_pow_iff_dvd
- \+ *lemma* norm_le_pow_iff_le_valuation
- \+ *lemma* mem_span_pow_iff_le_valuation
- \+ *lemma* norm_le_pow_iff_mem_span_pow
- \+ *lemma* norm_le_pow_iff_norm_lt_pow_add_one
- \+ *lemma* norm_lt_pow_iff_norm_le_pow_sub_one
- \+/\- *lemma* norm_lt_one_iff_dvd
- \+/\- *lemma* pow_p_dvd_int_iff
- \- *lemma* padic_norm_z
- \- *lemma* le_one
- \- *lemma* one
- \- *lemma* mul
- \- *lemma* pow
- \- *lemma* eq_of_norm_add_lt_right
- \- *lemma* eq_of_norm_add_lt_left
- \- *lemma* padic_norm_z_of_int
- \- *lemma* padic_norm_z_eq_padic_norm_e
- \- *lemma* p_dvd_of_norm_lt_one
- \- *lemma* is_unit_denom
- \- *lemma* norm_sub_mod_part_aux
- \- *lemma* mod_part_lt_p
- \- *lemma* mod_part_nonneg
- \- *lemma* norm_sub_mod_part
- \- *lemma* zmod_congr_of_sub_mem_span_aux
- \- *lemma* zmod_congr_of_sub_mem_span
- \- *lemma* zmod_congr_of_sub_mem_max_ideal
- \- *lemma* exists_mem_range
- \- *lemma* zmod_repr_spec
- \- *lemma* zmod_repr_lt_p
- \- *lemma* sub_zmod_repr_mem
- \- *lemma* to_zmod_spec
- \- *lemma* ker_to_zmod
- \- *lemma* appr_lt
- \- *lemma* appr_spec
- \- *lemma* ker_to_zmod_pow
- \- *lemma* padic_val_of_cong_pow_p
- \+ *theorem* norm_add_eq_max_of_ne
- \- *theorem* add_eq_max_of_ne
- \+/\- *def* coe.ring_hom
- \+ *def* of_int_seq
- \- *def* mod_part
- \- *def* zmod_repr
- \- *def* to_zmod_hom
- \- *def* to_zmod
- \- *def* to_zmod_pow

Modified src/data/padics/padic_numbers.lean
- \+ *lemma* norm_int_le_pow_iff_dvd
- \- *lemma* norm_int_lt_pow_iff_dvd

Created src/data/padics/ring_homs.lean
- \+ *lemma* mod_part_lt_p
- \+ *lemma* mod_part_nonneg
- \+ *lemma* is_unit_denom
- \+ *lemma* norm_sub_mod_part_aux
- \+ *lemma* norm_sub_mod_part
- \+ *lemma* exists_mem_range_of_norm_rat_le_one
- \+ *lemma* zmod_congr_of_sub_mem_span_aux
- \+ *lemma* zmod_congr_of_sub_mem_span
- \+ *lemma* zmod_congr_of_sub_mem_max_ideal
- \+ *lemma* exists_mem_range
- \+ *lemma* zmod_repr_spec
- \+ *lemma* zmod_repr_lt_p
- \+ *lemma* sub_zmod_repr_mem
- \+ *lemma* to_zmod_spec
- \+ *lemma* ker_to_zmod
- \+ *lemma* appr_lt
- \+ *lemma* appr_mono
- \+ *lemma* dvd_appr_sub_appr
- \+ *lemma* appr_spec
- \+ *lemma* ker_to_zmod_pow
- \+ *lemma* zmod_cast_comp_to_zmod_pow
- \+ *lemma* cast_to_zmod_pow
- \+ *lemma* dense_range_nat_cast
- \+ *lemma* dense_range_int_cast
- \+ *lemma* nth_hom_zero
- \+ *lemma* pow_dvd_nth_hom_sub
- \+ *lemma* is_cau_seq_nth_hom
- \+ *lemma* nth_hom_seq_one
- \+ *lemma* nth_hom_seq_add
- \+ *lemma* nth_hom_seq_mul
- \+ *lemma* lim_nth_hom_spec
- \+ *lemma* lim_nth_hom_zero
- \+ *lemma* lim_nth_hom_one
- \+ *lemma* lim_nth_hom_add
- \+ *lemma* lim_nth_hom_mul
- \+ *lemma* lift_sub_val_mem_span
- \+ *lemma* lift_spec
- \+ *lemma* lift_unique
- \+ *lemma* lift_self
- \+ *lemma* ext_of_to_zmod_pow
- \+ *lemma* to_zmod_pow_eq_iff_ext
- \+ *def* mod_part
- \+ *def* zmod_repr
- \+ *def* to_zmod_hom
- \+ *def* to_zmod
- \+ *def* to_zmod_pow
- \+ *def* nth_hom
- \+ *def* nth_hom_seq
- \+ *def* lim_nth_hom
- \+ *def* lift

Modified src/data/real/cau_seq.lean
- \+ *lemma* add_equiv_add
- \+ *lemma* neg_equiv_neg

Modified src/data/zmod/basic.lean
- \+ *lemma* cast_neg



## [2020-09-03 16:43:52](https://github.com/leanprover-community/mathlib/commit/49173c0)
ci(scripts/detect_errors.py): enforce silent builds ([#4025](https://github.com/leanprover-community/mathlib/pull/4025))
Refactor of [#3989](https://github.com/leanprover-community/mathlib/pull/3989). 
This changes the GitHub Actions workflow so that the main build step and the test step run `lean` with `--json`. The JSON output is piped to `detect_errors.py` which now exits at the end of the build if there is any output and also writes a file `src/.noisy_files` with the names of the noisy Lean files. This file is now included in the olean caches uploaded to Azure.
The "try to find olean cache" step now uses `src/.noisy_files` to delete all of the `.olean` files corresponding to the noisy Lean files, thus making the results of CI idempotent (hopefully).
#### Estimated changes
Modified .github/workflows/build.yml


Modified .gitignore


Modified scripts/detect_errors.py
- \+ *def* format_msg(msg):
- \+ *def* write_and_print_noisy_files(noisy_files):

Modified scripts/fetch_olean_cache.sh


Modified src/analysis/specific_limits.lean




## [2020-09-03 14:47:30](https://github.com/leanprover-community/mathlib/commit/8b277a9)
feat(category_theory/filtered): finite diagrams in filtered categories admit cocones ([#4026](https://github.com/leanprover-community/mathlib/pull/4026))
This is only step towards eventual results about filtered colimits commuting with finite limits, `forget CommRing` preserving filtered colimits, and applications to `Scheme`.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* coeq_condition
- \+ *lemma* sup_objs_exists
- \+ *lemma* sup_exists'
- \+ *lemma* sup_exists
- \+ *lemma* to_sup_commutes
- \+ *lemma* cocone_nonempty
- \+ *def* sup
- \+ *def* to_sup

Created src/category_theory/fin_category.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/linear_algebra/basic.lean


Modified src/logic/basic.lean
- \+/\- *theorem* exists_eq'
- \+ *theorem* exists_apply_eq_apply
- \+ *theorem* exists_apply_eq_apply'



## [2020-09-03 11:22:52](https://github.com/leanprover-community/mathlib/commit/fa6485a)
feat(category_theory/limits/concrete): simp lemmas ([#3973](https://github.com/leanprover-community/mathlib/pull/3973))
Some specialisations of simp lemmas about (co)limits for concrete categories, where the equation in morphisms has been applied to an element.
This isn't exhaustive; just the things I've wanted recently.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean
- \- *lemma* lift_π_apply

Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* w_apply
- \+ *lemma* w_forget_apply
- \+ *lemma* limit.lift_π_apply
- \+ *lemma* limit.w_apply
- \+ *lemma* colimit.ι_desc_apply
- \+ *lemma* colimit.w_apply
- \- *lemma* naturality_concrete



## [2020-09-03 04:04:29](https://github.com/leanprover-community/mathlib/commit/dd633c2)
feat(geometry/euclidean/circumcenter): more lemmas ([#4028](https://github.com/leanprover-community/mathlib/pull/4028))
Add some more basic lemmas about `circumcenter` and `circumradius`.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* circumradius_nonneg
- \+ *lemma* circumradius_pos
- \+ *lemma* circumcenter_eq_point
- \+ *lemma* circumcenter_eq_centroid
- \+ *lemma* orthogonal_projection_circumcenter



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


Created test/README.md


Modified test/continuity.lean


Modified test/doc_commands.lean


Modified test/general_recursion.lean


Modified test/library_search/exp_le_exp.lean


Modified test/library_search/filter.lean


Modified test/library_search/nat.lean


Modified test/linarith.lean
- \+/\- *lemma* abs_nonneg'
- \+/\- *lemma* zero_lt_one

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
- \+ *lemma* rel_hom.injective_of_increasing
- \+ *lemma* to_rel_hom_eq_coe
- \+ *lemma* coe_coe_fn
- \+ *theorem* map_rel
- \+/\- *theorem* coe_fn_mk
- \+ *theorem* coe_fn_to_fun
- \+ *theorem* coe_fn_inj
- \+/\- *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* id_apply
- \+ *theorem* comp_apply
- \+ *theorem* surjective.well_founded_iff
- \+ *def* preimage
- \+ *def* to_rel_hom
- \- *def* rsymm
- \- *def* osymm
- \- *def* order_iso.osymm

Modified src/ring_theory/noetherian.lean




## [2020-09-02 15:51:17](https://github.com/leanprover-community/mathlib/commit/57463fa)
feat(linear_algebra/affine_space): more lemmas ([#3990](https://github.com/leanprover-community/mathlib/pull/3990))
Add another batch of lemmas about affine spaces.  These lemmas mostly
relate to manipulating centroids and the relations between centroids
of points given by different subsets of the index type.
#### Estimated changes
Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* weighted_vsub_of_point_map
- \+ *lemma* weighted_vsub_map
- \+ *lemma* affine_combination_map
- \+ *lemma* centroid_insert_singleton
- \+ *lemma* centroid_insert_singleton_fin
- \+ *lemma* centroid_map
- \+ *lemma* centroid_weights_indicator_def
- \+ *lemma* sum_centroid_weights_indicator
- \+ *lemma* sum_centroid_weights_indicator_eq_one_of_card_ne_zero
- \+ *lemma* sum_centroid_weights_indicator_eq_one_of_nonempty
- \+ *lemma* sum_centroid_weights_indicator_eq_one_of_card_eq_add_one
- \+ *lemma* centroid_eq_affine_combination_fintype
- \+ *def* centroid_weights_indicator

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_of_ne
- \+ *lemma* range_face_points
- \+ *lemma* face_centroid_eq_centroid
- \+ *lemma* centroid_eq_iff
- \+ *lemma* face_centroid_eq_iff



## [2020-09-02 15:11:55](https://github.com/leanprover-community/mathlib/commit/71ef45e)
chore(topology/sheaves): depend less on rfl ([#3994](https://github.com/leanprover-community/mathlib/pull/3994))
Another backport from the `prop_limits` branch.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* pi_lift_π_apply
- \+ *lemma* pi_map_π_apply
- \- *lemma* lift_π_apply'

Modified src/category_theory/limits/types.lean
- \+ *lemma* limit_w_apply
- \+ *lemma* map_π_apply
- \+ *lemma* colimit_w_apply
- \+ *lemma* ι_map_apply
- \+ *lemma* colimit_sound
- \+ *lemma* colimit_eq_iff_aux
- \+/\- *lemma* colimit_eq_iff

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/stalks.lean




## [2020-09-02 13:19:05](https://github.com/leanprover-community/mathlib/commit/895f6ee)
chore(algebra/category/CommRing/limits): don't use deprecated.subring ([#4010](https://github.com/leanprover-community/mathlib/pull/4010))
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean
- \+ *def* sections_subring



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
- \+ *lemma* cast_succ_pos
- \+/\- *lemma* succ_above_below
- \+/\- *lemma* succ_above_above
- \+ *lemma* succ_above_lt_ge
- \+ *lemma* succ_above_lt_gt
- \+ *lemma* succ_above_right_inj
- \+ *lemma* succ_above_right_injective
- \+/\- *lemma* succ_above_descend
- \+/\- *lemma* pred_above_succ_above
- \+ *lemma* succ_above_left_inj
- \+ *lemma* succ_above_left_injective
- \+/\- *theorem* succ_above_ne
- \+/\- *def* succ_above

Modified src/data/fintype/basic.lean
- \+ *lemma* fin.univ_succ_above

Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.prod_univ_zero
- \+ *theorem* fin.prod_univ_succ_above
- \+ *theorem* fin.sum_univ_succ_above
- \+/\- *theorem* fin.prod_univ_succ
- \+/\- *theorem* fin.sum_univ_succ
- \+/\- *theorem* fin.prod_univ_cast_succ
- \+/\- *theorem* fin.sum_univ_cast_succ



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
- \+ *lemma* nat_degree_map_of_leading_coeff_ne_zero
- \+ *lemma* leading_coeff_map_of_leading_coeff_ne_zero
- \+ *lemma* leading_coeff_map'

Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_mul_eq_zero_of_left
- \+ *lemma* eval₂_mul_eq_zero_of_right

Modified src/data/polynomial/monic.lean
- \+ *lemma* monic_mul_C_of_leading_coeff_mul_eq_one

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mem_map_of_mem

Modified src/ring_theory/algebra.lean
- \+ *lemma* mem_algebra_map_submonoid_of_mem
- \+ *def* algebra_map_submonoid

Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_integral_mul_unit

Modified src/ring_theory/localization.lean
- \- *lemma* mul_mem_non_zero_divisors
- \- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \- *lemma* mem_non_zero_divisors_iff_ne_zero
- \- *lemma* map_ne_zero_of_mem_non_zero_divisors
- \- *lemma* map_mem_non_zero_divisors
- \- *lemma* le_non_zero_divisors_of_domain
- \+ *theorem* is_integral_localization_at_leading_coeff
- \+ *theorem* is_integral_localization
- \- *def* non_zero_divisors

Created src/ring_theory/non_zero_divisors.lean
- \+ *lemma* mul_mem_non_zero_divisors
- \+ *lemma* eq_zero_of_ne_zero_of_mul_right_eq_zero
- \+ *lemma* eq_zero_of_ne_zero_of_mul_left_eq_zero
- \+ *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* le_non_zero_divisors_of_domain
- \+ *def* non_zero_divisors

Modified src/ring_theory/polynomial/rational_root.lean
- \- *lemma* coeff_scale_roots
- \- *lemma* coeff_scale_roots_nat_degree
- \- *lemma* zero_scale_roots
- \- *lemma* scale_roots_ne_zero
- \- *lemma* support_scale_roots_le
- \- *lemma* support_scale_roots_eq
- \- *lemma* degree_scale_roots
- \- *lemma* nat_degree_scale_roots
- \- *lemma* monic_scale_roots_iff
- \- *lemma* scale_roots_eval₂_eq_zero
- \- *lemma* scale_roots_aeval_eq_zero
- \- *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \- *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero

Created src/ring_theory/polynomial/scale_roots.lean
- \+ *lemma* coeff_scale_roots
- \+ *lemma* coeff_scale_roots_nat_degree
- \+ *lemma* zero_scale_roots
- \+ *lemma* scale_roots_ne_zero
- \+ *lemma* support_scale_roots_le
- \+ *lemma* support_scale_roots_eq
- \+ *lemma* degree_scale_roots
- \+ *lemma* nat_degree_scale_roots
- \+ *lemma* monic_scale_roots_iff
- \+ *lemma* scale_roots_eval₂_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero
- \+ *lemma* scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
- \+ *lemma* scale_roots_aeval_eq_zero_of_aeval_div_eq_zero



## [2020-09-02 11:43:54](https://github.com/leanprover-community/mathlib/commit/cd36773)
feat(linear_algebra/eigenspace): add generalized eigenspaces ([#4015](https://github.com/leanprover-community/mathlib/pull/4015))
Add the definition of generalized eigenspaces, eigenvectors and eigenvalues. Add some basic lemmas about them.
Another step towards [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* pow_mul_pow_sub
- \+ *theorem* nsmul_add_sub_nsmul
- \+ *theorem* pow_sub_mul_pow
- \+ *theorem* sub_nsmul_nsmul_add

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* exp_ne_zero_of_has_generalized_eigenvalue
- \+ *lemma* generalized_eigenspace_mono
- \+ *lemma* has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le
- \+ *lemma* eigenspace_le_generalized_eigenspace
- \+ *lemma* has_generalized_eigenvalue_of_has_eigenvalue
- \+ *def* generalized_eigenspace
- \+ *def* has_generalized_eigenvector
- \+ *def* has_generalized_eigenvalue



## [2020-09-02 08:30:45](https://github.com/leanprover-community/mathlib/commit/7310eab)
feat(field_theory/adjoin): adjoining elements to fields ([#3913](https://github.com/leanprover-community/mathlib/pull/3913))
Defines adjoining elements to fields
#### Estimated changes
Created src/field_theory/adjoin.lean
- \+ *lemma* adjoin.algebra_map_mem
- \+ *lemma* subset_adjoin_of_subset_left
- \+ *lemma* adjoin.range_algebra_map_subset
- \+ *lemma* subset_adjoin
- \+ *lemma* adjoin.mono
- \+ *lemma* adjoin_contains_field_as_subfield
- \+ *lemma* subset_adjoin_of_subset_right
- \+ *lemma* adjoin_subset_subfield
- \+ *lemma* adjoin_subset_iff
- \+ *lemma* subfield_subset_adjoin_self
- \+ *lemma* adjoin_subset_adjoin_iff
- \+ *lemma* adjoin_adjoin_left
- \+ *lemma* adjoin_singleton
- \+ *lemma* mem_adjoin_simple_self
- \+ *lemma* adjoin_simple.algebra_map_gen
- \+ *lemma* adjoin_simple_adjoin_simple
- \+ *def* adjoin
- \+ *def* adjoin_simple.gen

Modified src/ring_theory/algebra.lean
- \+ *lemma* set_range_subset



## [2020-09-02 06:01:22](https://github.com/leanprover-community/mathlib/commit/8026ea8)
feat(ring_theory/localization): localization away from an element ([#4019](https://github.com/leanprover-community/mathlib/pull/4019))
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* mk'_self'
- \+/\- *lemma* mk'_self
- \+ *lemma* away_map.lift_eq
- \+ *lemma* away_map.lift_comp
- \+ *lemma* away.mk_eq_monoid_of_mk'
- \+ *def* away_map
- \+ *def* away
- \+ *def* away.inv_self
- \+ *def* away.monoid_of

Modified src/ring_theory/jacobson.lean
- \+ *lemma* disjoint_powers_iff_not_mem
- \- *lemma* disjoint_closure_singleton_iff_not_mem

Modified src/ring_theory/localization.lean
- \+ *lemma* away_map.lift_eq
- \+ *lemma* away_map.lift_comp
- \+ *lemma* away.mk_eq_mk'
- \+ *def* away_map
- \+ *def* away.of



## [2020-09-02 00:37:30](https://github.com/leanprover-community/mathlib/commit/0b4444c)
feat(pfun/recursion): unbounded recursion ([#3778](https://github.com/leanprover-community/mathlib/pull/3778))
#### Estimated changes
Created src/control/fix.lean
- \+ *lemma* fix_def'
- \+ *def* fix.approx
- \+ *def* fix_aux

Created src/control/lawful_fix.lean
- \+ *lemma* lawful_fix.fix_eq'
- \+ *lemma* approx_mono'
- \+ *lemma* approx_mono
- \+ *lemma* mem_iff
- \+ *lemma* approx_le_fix
- \+ *lemma* exists_fix_le_approx
- \+ *lemma* le_f_of_mem_approx
- \+ *lemma* approx_mem_approx_chain
- \+ *lemma* fix_eq_ωSup
- \+ *lemma* fix_le
- \+ *lemma* fix_eq
- \+ *lemma* to_unit_cont
- \+ *lemma* continuous_curry
- \+ *lemma* continuous_uncurry
- \+ *lemma* uncurry_curry_continuous
- \+ *def* approx_chain
- \+ *def* to_unit_mono
- \+ *def* monotone_curry
- \+ *def* monotone_uncurry

Created src/data/nat/upto.lean
- \+ *def* upto
- \+ *def* zero
- \+ *def* succ

Modified src/data/pfun.lean
- \+ *lemma* eq_none_or_eq_some
- \+ *lemma* le_total_of_le_of_le
- \+ *lemma* assert_pos
- \+ *lemma* assert_neg
- \+ *lemma* bind_le

Modified src/data/sigma/basic.lean
- \+ *def* sigma.curry
- \+ *def* sigma.uncurry

Modified src/order/bounded_lattice.lean


Modified src/order/category/Preorder.lean
- \- *lemma* ext
- \- *lemma* coe_inj
- \- *lemma* coe_id
- \- *lemma* comp_id
- \- *lemma* id_comp
- \- *def* id
- \- *def* comp

Created src/order/category/omega_complete_partial_order.lean
- \+ *def* ωCPO
- \+ *def* of

Created src/order/omega_complete_partial_order.lean
- \+ *lemma* mem_map
- \+ *lemma* exists_of_mem_map
- \+ *lemma* mem_map_iff
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_le_map
- \+ *lemma* le_ωSup_of_le
- \+ *lemma* ωSup_total
- \+ *lemma* ωSup_le_ωSup_of_le
- \+ *lemma* ωSup_le_iff
- \+ *lemma* continuous.to_monotone
- \+ *lemma* continuous.of_bundled
- \+ *lemma* continuous.of_bundled'
- \+ *lemma* continuous.to_bundled
- \+ *lemma* continuous_id
- \+ *lemma* continuous_comp
- \+ *lemma* id_continuous'
- \+ *lemma* const_continuous'
- \+ *lemma* eq_of_chain
- \+ *lemma* ωSup_eq_some
- \+ *lemma* ωSup_eq_none
- \+ *lemma* mem_chain_of_mem_ωSup
- \+ *lemma* mem_ωSup
- \+ *lemma* flip₁_continuous'
- \+ *lemma* flip₂_continuous'
- \+ *lemma* ite_continuous'
- \+ *lemma* ωSup_bind
- \+ *lemma* bind_continuous'
- \+ *lemma* map_continuous'
- \+ *lemma* seq_continuous'
- \+ *lemma* continuous
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* comp_assoc
- \+ *lemma* coe_apply
- \+ *lemma* forall_forall_merge
- \+ *lemma* forall_forall_merge'
- \+ *lemma* ωSup_def
- \+ *lemma* ωSup_ωSup
- \+ *theorem* const_apply
- \+ *def* const
- \+ *def* prod.diag
- \+ *def* prod.map
- \+ *def* prod.fst
- \+ *def* prod.snd
- \+ *def* prod.zip
- \+ *def* bind
- \+ *def* chain
- \+ *def* map
- \+ *def* zip
- \+ *def* continuous
- \+ *def* continuous'
- \+ *def* monotone_apply
- \+ *def* to_fun_hom
- \+ *def* of_fun
- \+ *def* of_mono
- \+ *def* id
- \+ *def* comp
- \+ *def* apply
- \+ *def* to_mono
- \+ *def* flip

Created src/order/preorder_hom.lean
- \+ *lemma* coe_fun_mk
- \+ *lemma* ext
- \+ *lemma* coe_inj
- \+ *lemma* coe_id
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *def* id
- \+ *def* comp

Created test/general_recursion.lean
- \+ *lemma* f91.cont
- \+ *lemma* f91_spec
- \+ *lemma* f91_dom
- \+ *lemma* f91_spec'
- \+ *theorem* easy.cont
- \+ *theorem* easy.equations.eqn_1
- \+ *theorem* div.cont
- \+ *theorem* div.equations.eqn_1
- \+ *theorem* tree_map.cont
- \+ *theorem* tree_map.equations.eqn_1
- \+ *theorem* tree_map.equations.eqn_2
- \+ *theorem* tree_map'.cont
- \+ *theorem* tree_map'.equations.eqn_1
- \+ *theorem* tree_map'.equations.eqn_2
- \+ *theorem* f91.equations.eqn_1
- \+ *def* easy.intl
- \+ *def* easy
- \+ *def* div.intl
- \+ *def* div
- \+ *def* tree_map.intl
- \+ *def* tree_map
- \+ *def* tree_map'.intl
- \+ *def* tree_map'
- \+ *def* f91.intl
- \+ *def* f91
- \+ *def* f91'



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
- \+ *def* init
- \+ *def* interleave
- \+ *def* interleave_all

Created src/tactic/slim_check.lean


Created src/testing/slim_check/gen.lean
- \+ *def* gen
- \+ *def* io.run_gen
- \+ *def* choose_any
- \+ *def* choose
- \+ *def* choose_nat
- \+ *def* sized
- \+ *def* vector_of
- \+ *def* list_of
- \+ *def* one_of_aux
- \+ *def* one_of

Created src/testing/slim_check/sampleable.lean
- \+ *def* lazy_list.lseq
- \+ *def* nat.shrink'
- \+ *def* nat.shrink
- \+ *def* sampleable.lift
- \+ *def* int.shrink'
- \+ *def* int.shrink
- \+ *def* sum.shrink
- \+ *def* sampleable_char
- \+ *def* list.shrink'
- \+ *def* list.shrink_with
- \+ *def* tree.sample
- \+ *def* tree.shrink_with
- \+ *def* print_samples

Created src/testing/slim_check/testable.lean
- \+ *def* test_result.to_string
- \+ *def* combine
- \+ *def* and_counter_example
- \+ *def* or_counter_example
- \+ *def* convert_counter_example
- \+ *def* convert_counter_example'
- \+ *def* add_to_counter_example
- \+ *def* add_var_to_counter_example
- \+ *def* named_binder
- \+ *def* is_failure
- \+ *def* trace_if_giveup
- \+ *def* combine_testable
- \+ *def* minimize
- \+ *def* retry
- \+ *def* give_up
- \+ *def* testable.run_suite_aux
- \+ *def* testable.run_suite
- \+ *def* testable.check'
- \+ *def* decorations_of
- \+ *def* foo
- \+ *def* testable.check



## [2020-09-01 12:58:32](https://github.com/leanprover-community/mathlib/commit/329393a)
feat(analysis/calculus/times_cont_diff): iterated smoothness in terms of deriv ([#4017](https://github.com/leanprover-community/mathlib/pull/4017))
Currently, iterated smoothness is only formulated in terms of the Fréchet derivative. For one-dimensional functions, it is more handy to use the one-dimensional derivative `deriv`. This PR provides a basic interface in this direction.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_within_of_open

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_of_open

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on.fderiv_of_open
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_of_open
- \+ *lemma* times_cont_diff_on.deriv_within
- \+ *lemma* times_cont_diff_on.deriv_of_open
- \+ *lemma* times_cont_diff_on.continuous_on_deriv_within
- \+ *lemma* times_cont_diff_on.continuous_on_deriv_of_open
- \+ *theorem* times_cont_diff_on_succ_iff_fderiv_of_open
- \+ *theorem* times_cont_diff_on_top_iff_fderiv_of_open
- \+ *theorem* times_cont_diff_on_succ_iff_deriv_within
- \+ *theorem* times_cont_diff_on_succ_iff_deriv_of_open
- \+ *theorem* times_cont_diff_on_top_iff_deriv_within
- \+ *theorem* times_cont_diff_on_top_iff_deriv_of_open



## [2020-09-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/849a5f9)
feat(docs,ci): move overview, undergrad, and 100 theorems lists from website ([#4016](https://github.com/leanprover-community/mathlib/pull/4016))
See conversation at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/website.20overview/near/208659351
We'll store these lists in mathlib so that we can catch breakage as soon as it happens, rather than continually repairing the website build. This PR adds the lists and a CI step that checks that every declaration name appearing in the lists actually exists in the library.
#### Estimated changes
Modified .github/workflows/build.yml


Created docs/100.yaml


Created docs/overview.yaml


Created docs/undergrad.yaml


Created scripts/yaml_check.lean
- \+ *def* fails
- \+ *def* databases

Created scripts/yaml_check.py
- \+ *def* tiered_extract(db:
- \+ *def* print_list(fn:



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
- \+/\- *def* of

Modified src/algebra/category/Algebra/limits.lean
- \+/\- *def* limit_π_alg_hom

Modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* limit_π_ring_hom

Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* of
- \+/\- *def* linear_equiv.to_Module_iso'

Modified src/algebra/category/Module/kernels.lean


Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Module/monoidal.lean
- \+/\- *lemma* triangle
- \+/\- *lemma* hom_apply
- \+/\- *lemma* left_unitor_hom_apply
- \+/\- *lemma* right_unitor_hom_apply
- \+/\- *lemma* associator_hom_apply
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor

Modified src/algebra/category/Mon/limits.lean
- \+/\- *def* limit_π_monoid_hom

Modified src/category_theory/concrete_category/basic.lean
- \+/\- *def* forget
- \+/\- *def* concrete_category.has_coe_to_sort
- \+/\- *def* forget₂
- \+/\- *def* has_forget₂.mk'

Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/concrete_category/reflects_isomorphisms.lean


Modified src/category_theory/monoidal/internal/Module.lean
- \+/\- *lemma* algebra_map
- \+/\- *def* functor
- \+/\- *def* Mon_Module_equivalence_Algebra



## [2020-09-01 09:54:45](https://github.com/leanprover-community/mathlib/commit/a97d71b)
feat(data/mv_polynomial): assorted lemmas ([#4002](https://github.com/leanprover-community/mathlib/pull/4002))
Assorted additions to `mv_polynomial`. This is more from the Witt vector development. Nothing too deep here, just scattered lemmas and the `constant_coeff` ring hom.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->
Hopefully this builds -- it's split off from a branch with a lot of other changes. I think it shouldn't have dependencies!
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* ring_hom_ext
- \+ *lemma* alg_hom_ext
- \+ *lemma* alg_hom_C
- \+ *lemma* constant_coeff_eq
- \+ *lemma* constant_coeff_C
- \+ *lemma* constant_coeff_X
- \+ *lemma* constant_coeff_monomial
- \+ *lemma* eval₂_hom_C
- \+ *lemma* eval₂_hom_X'
- \+ *lemma* comp_eval₂_hom
- \+ *lemma* map_eval₂_hom
- \+ *lemma* eval₂_hom_monomial
- \+ *lemma* eval_map
- \+ *lemma* eval₂_map
- \+ *lemma* eval₂_hom_map_hom
- \+ *lemma* aeval_eq_eval₂_hom
- \+ *lemma* comp_aeval
- \+ *lemma* map_aeval
- \+ *lemma* aeval_zero
- \+ *lemma* aeval_zero'
- \+ *lemma* aeval_monomial
- \+ *lemma* eval₂_hom_rename
- \+ *def* constant_coeff



## [2020-09-01 06:48:21](https://github.com/leanprover-community/mathlib/commit/2688d42)
feat(archive/100-theorems-list): friendship theorem (nr 83) ([#3970](https://github.com/leanprover-community/mathlib/pull/3970))
defines friendship graphs
proves the friendship theorem (freek [#83](https://github.com/leanprover-community/mathlib/pull/83))
#### Estimated changes
Created archive/100-theorems-list/83_friendship_graphs.lean
- \+ *lemma* mem_common_friends
- \+ *lemma* adj_matrix_pow_three_of_not_adj
- \+ *lemma* degree_eq_of_not_adj
- \+ *lemma* card_of_regular
- \+ *lemma* card_mod_p_of_regular
- \+ *lemma* adj_matrix_sq_mod_p_of_regular
- \+ *lemma* adj_matrix_sq_mul_const_one_of_regular
- \+ *lemma* adj_matrix_mul_const_one_mod_p_of_regular
- \+ *lemma* adj_matrix_pow_mod_p_of_regular
- \+ *lemma* false_of_three_le_degree
- \+ *lemma* exists_politician_of_degree_le_one
- \+ *lemma* neighbor_finset_eq_of_degree_eq_two
- \+ *lemma* exists_politician_of_degree_eq_two
- \+ *lemma* exists_politician_of_degree_le_two
- \+ *theorem* adj_matrix_sq_of_ne
- \+ *theorem* is_regular_of_not_exists_politician
- \+ *theorem* adj_matrix_sq_of_regular
- \+ *theorem* friendship_theorem
- \+ *def* common_friends
- \+ *def* friendship
- \+ *def* exists_politician

Modified docs/references.bib




## [2020-09-01 04:51:03](https://github.com/leanprover-community/mathlib/commit/12763ec)
chore(*): more use of bundled ring homs ([#4012](https://github.com/leanprover-community/mathlib/pull/4012))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* prod_hom

Modified src/data/multiset/basic.lean
- \+/\- *lemma* prod_hom

Modified src/data/polynomial/eval.lean


Modified src/ring_theory/ideal/operations.lean




## [2020-09-01 04:51:01](https://github.com/leanprover-community/mathlib/commit/51546d2)
chore(ring_theory/free_ring): use bundled ring homs ([#4011](https://github.com/leanprover-community/mathlib/pull/4011))
Use bundled ring homs in `free_ring` and `free_comm_ring`.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *lemma* lift_comp_of
- \- *lemma* lift_zero
- \- *lemma* lift_one
- \- *lemma* lift_add
- \- *lemma* lift_neg
- \- *lemma* lift_sub
- \- *lemma* lift_mul
- \- *lemma* coe_lift_hom
- \- *lemma* lift_pow
- \- *lemma* lift_hom_comp_of
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* map_mul
- \- *lemma* map_pow
- \- *lemma* restriction_zero
- \- *lemma* restriction_one
- \- *lemma* restriction_add
- \- *lemma* restriction_neg
- \- *lemma* restriction_sub
- \- *lemma* restriction_mul
- \+/\- *def* lift
- \- *def* lift_hom

Modified src/ring_theory/free_ring.lean
- \+/\- *lemma* map_of
- \- *lemma* lift_zero
- \- *lemma* lift_one
- \- *lemma* lift_add
- \- *lemma* lift_neg
- \- *lemma* lift_sub
- \- *lemma* lift_mul
- \- *lemma* lift_pow
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* map_mul
- \- *lemma* map_pow
- \+/\- *def* lift
- \+/\- *def* map
- \- *def* lift_hom
- \- *def* map_hom



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
- \+ *lemma* ne_one
- \+ *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul
- \+/\- *lemma* dvd_iff_dvd_of_rel_right
- \+/\- *lemma* eq_zero_iff_of_associated
- \+/\- *lemma* ne_zero_iff_of_associated
- \+/\- *lemma* prime_of_associated
- \+/\- *lemma* prime_iff_of_associated
- \+/\- *lemma* irreducible_of_associated
- \+/\- *lemma* irreducible_iff_of_associated
- \+ *lemma* eq_of_mul_eq_mul_right
- \+ *lemma* le_of_mul_le_mul_right
- \- *lemma* prime.ne_zero
- \- *lemma* prime.ne_one
- \+ *theorem* mk_dvd_mk
- \+ *theorem* irreducible_iff_prime_iff
- \- *def* prime

Modified src/ring_theory/integral_domain.lean
- \- *lemma* left_dvd_or_dvd_right_of_dvd_prime_mul

Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* associates_irreducible_iff_prime



## [2020-09-01 04:50:54](https://github.com/leanprover-community/mathlib/commit/7cd67b5)
feat(category_theory/limits/shapes/terminal): is_terminal object ([#3957](https://github.com/leanprover-community/mathlib/pull/3957))
Add language to talk about when an object is terminal, and generalise some results to use this
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* initial_mono
- \+/\- *def* zero_mul
- \+/\- *def* mul_zero
- \+/\- *def* pow_zero
- \+ *def* strict_initial

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* is_terminal.hom_ext
- \+ *lemma* is_initial.hom_ext
- \+ *lemma* is_terminal.mono_from
- \+ *lemma* is_initial.epi_to
- \+ *def* as_empty_cone
- \+ *def* as_empty_cocone
- \+ *def* is_terminal.from
- \+ *def* is_initial.to
- \+ *def* terminal_is_terminal
- \+ *def* initial_is_initial



## [2020-09-01 03:18:29](https://github.com/leanprover-community/mathlib/commit/fc57cf4)
feat(data/{finset,finsupp,multiset}): more assorted lemmas ([#4006](https://github.com/leanprover-community/mathlib/pull/4006))
Another grab bag of facts from the Witt vector branch.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* union_subset_union
- \+ *lemma* to_finset_union
- \+ *lemma* to_finset_subset
- \+ *lemma* disjoint_to_finset

Modified src/data/finset/fold.lean
- \+ *lemma* fold_union_empty_singleton
- \+ *lemma* fold_sup_bot_singleton

Modified src/data/finset/lattice.lean
- \+ *lemma* mem_sup
- \+ *lemma* sup_subset

Modified src/data/finsupp/basic.lean
- \+ *lemma* mem_to_multiset

Modified src/data/multiset/basic.lean
- \+ *theorem* count_ne_zero



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
- \+ *lemma* hom_apply
- \+ *lemma* left_unitor_hom_apply
- \+ *lemma* right_unitor_hom_apply
- \+ *lemma* associator_hom_apply
- \- *lemma* left_unitor_hom
- \- *lemma* right_unitor_hom
- \- *lemma* associator_hom

Modified src/algebra/module/basic.lean
- \+ *lemma* lcongr_fun

Created src/category_theory/monoidal/internal/Module.lean
- \+ *lemma* algebra_map
- \+ *def* functor
- \+ *def* inverse_obj
- \+ *def* inverse
- \+ *def* Mon_Module_equivalence_Algebra
- \+ *def* Mon_Module_equivalence_Algebra_forget

Modified src/category_theory/monoidal/types.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* linear_map_apply
- \+ *lemma* lmul'_apply
- \+ *def* lmul'

