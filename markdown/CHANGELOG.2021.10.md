## [2021-10-31 23:00:49](https://github.com/leanprover-community/mathlib/commit/932e954)
feat(data/finset): some simple finset lemmas ([#10079](https://github.com/leanprover-community/mathlib/pull/10079))
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* product_subset_product
- \+ *lemma* product_subset_product_left
- \+ *lemma* product_subset_product_right
- \+ *lemma* diag_empty
- \+ *lemma* off_diag_empty



## [2021-10-31 23:00:48](https://github.com/leanprover-community/mathlib/commit/60cb2cf)
feat(data/list): length_filter_lt_length_iff_exists ([#10074](https://github.com/leanprover-community/mathlib/pull/10074))
Also moved a lemma about filter_map that was placed in the wrong file
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* filter_map_cons
- \+ *theorem* length_eq_countp_add_countp
- \+ *theorem* length_filter_lt_length_iff_exists

modified src/data/list/forall2.lean
- \- *theorem* filter_map_cons



## [2021-10-31 23:00:47](https://github.com/leanprover-community/mathlib/commit/af4f4df)
feat(list/init): simplifier lemmas for list.init ([#10061](https://github.com/leanprover-community/mathlib/pull/10061))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* init_cons_of_ne_nil
- \+ *lemma* init_append_of_ne_nil



## [2021-10-31 23:00:45](https://github.com/leanprover-community/mathlib/commit/d6dd451)
chore(data/list/basic): use dot notation here and there ([#10056](https://github.com/leanprover-community/mathlib/pull/10056))
### Renamed lemmas
- `list.cons_sublist_cons` → `list.sublist.cons_cons`;
- `list.infix_of_prefix` → `list.is_prefix.is_infix`;
- `list.infix_of_suffix` → `list.is_suffix.is_infix`;
- `list.sublist_of_infix` → `list.is_infix.sublist`;
- `list.sublist_of_prefix` → `list.is_prefix.sublist`;
- `list.sublist_of_suffix` → `list.is_suffix.sublist`;
- `list.length_le_of_infix` → `list.is_infix.length_le`.
### New `simp` attrs
`list.singleton_sublist`, `list.repeat_sublist_repeat`, `list.reverse_suffix`, `list.reverse_prefix`.
### New lemmas
`list.infix_insert`, `list.sublist_insert`, `list.subset_insert`.
#### Estimated changes
modified src/data/list/basic.lean
- \+/\- *lemma* tail_sublist
- \+/\- *lemma* tail_sublist
- \+ *theorem* sublist.cons_cons
- \+/\- *theorem* singleton_sublist
- \+/\- *theorem* repeat_sublist_repeat
- \+ *theorem* is_prefix.is_infix
- \+ *theorem* is_suffix.is_infix
- \+/\- *theorem* infix_refl
- \+/\- *theorem* nil_infix
- \+/\- *theorem* reverse_suffix
- \+/\- *theorem* reverse_prefix
- \+ *theorem* infix.length_le
- \+ *theorem* infix_insert
- \+ *theorem* sublist_insert
- \+ *theorem* subset_insert
- \- *theorem* cons_sublist_cons
- \+/\- *theorem* singleton_sublist
- \+/\- *theorem* repeat_sublist_repeat
- \- *theorem* infix_of_prefix
- \- *theorem* infix_of_suffix
- \+/\- *theorem* infix_refl
- \+/\- *theorem* nil_infix
- \- *theorem* sublist_of_infix
- \- *theorem* sublist_of_prefix
- \- *theorem* sublist_of_suffix
- \+/\- *theorem* reverse_suffix
- \+/\- *theorem* reverse_prefix
- \- *theorem* length_le_of_infix

modified src/data/list/forall2.lean

modified src/data/list/lattice.lean

modified src/data/list/nodup.lean

modified src/data/list/pairwise.lean

modified src/data/list/sublists.lean

modified src/data/multiset/finset_ops.lean



## [2021-10-31 23:00:44](https://github.com/leanprover-community/mathlib/commit/76f13b3)
feat(algebra/star/basic): `ring.inverse_star` ([#10039](https://github.com/leanprover-community/mathlib/pull/10039))
Also adds `is_unit.star` and `is_unit_star`.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* is_unit.star
- \+ *lemma* is_unit_star
- \+ *lemma* ring.inverse_star



## [2021-10-31 21:28:18](https://github.com/leanprover-community/mathlib/commit/106dc57)
chore(ring_theory/ideal/operations): generalize typeclass in map_map and comap_comap ([#10077](https://github.com/leanprover-community/mathlib/pull/10077))
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024) which is hitting timeouts somewhere more irritating.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* comap_comap
- \+/\- *lemma* map_map
- \+/\- *lemma* comap_comap
- \+/\- *lemma* map_map



## [2021-10-31 21:28:17](https://github.com/leanprover-community/mathlib/commit/233eb66)
feat(data/real/ennreal): more on integer powers on ennreal ([#10071](https://github.com/leanprover-community/mathlib/pull/10071))
#### Estimated changes
modified src/algebra/group_power/basic.lean
- \+ *theorem* zpow_two

modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_mem_Ico_zpow
- \+ *lemma* exists_mem_Ioc_zpow
- \- *lemma* exists_zpow_near
- \- *lemma* exists_zpow_near'

modified src/analysis/normed_space/basic.lean

modified src/data/real/ennreal.lean
- \+ *lemma* one_le_pow_of_one_le
- \+ *lemma* add_div
- \+ *lemma* coe_zpow
- \+ *lemma* zpow_pos
- \+ *lemma* zpow_lt_top
- \+ *lemma* exists_mem_Ico_zpow
- \+ *lemma* exists_mem_Ioc_zpow
- \+ *lemma* Ioo_zero_top_eq_Union_Ico_zpow
- \+ *lemma* zpow_le_of_le
- \+ *lemma* monotone_zpow
- \+ *lemma* zpow_add

modified src/data/real/nnreal.lean
- \+ *lemma* coe_zpow
- \+ *lemma* exists_mem_Ico_zpow
- \+ *lemma* exists_mem_Ioc_zpow
- \+ *lemma* inv_lt_one_iff
- \+ *lemma* inv_lt_one
- \+ *lemma* zpow_pos

modified src/topology/instances/ennreal.lean
- \+ *lemma* continuous_pow



## [2021-10-31 18:58:21](https://github.com/leanprover-community/mathlib/commit/5ca3c5e)
chore(data/set/intervals): add some lemmas ([#10062](https://github.com/leanprover-community/mathlib/pull/10062))
Add several lemma lemmas about intersection/difference of intervals.
#### Estimated changes
modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Iic_inter_Ioc_of_le
- \+ *lemma* Ioc_inter_Iic
- \+ *lemma* Ico_inter_Ici
- \+ *lemma* Ioc_diff_Iic
- \+/\- *lemma* Iic_inter_Ioc_of_le



## [2021-10-31 18:58:20](https://github.com/leanprover-community/mathlib/commit/05bd61d)
chore(analysis): move more code out of `analysis.normed_space.basic` ([#10055](https://github.com/leanprover-community/mathlib/pull/10055))
#### Estimated changes
created src/analysis/normed/group/completion.lean
- \+ *lemma* norm_coe

modified src/analysis/normed/group/hom_completion.lean

created src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_finset_iff_vanishing_norm
- \+ *lemma* summable_iff_vanishing_norm
- \+ *lemma* cauchy_seq_finset_of_norm_bounded
- \+ *lemma* cauchy_seq_finset_of_summable_norm
- \+ *lemma* has_sum_of_subseq_of_summable
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable_norm
- \+ *lemma* summable_of_norm_bounded
- \+ *lemma* has_sum.norm_le_of_bounded
- \+ *lemma* tsum_of_norm_bounded
- \+ *lemma* norm_tsum_le_tsum_norm
- \+ *lemma* tsum_of_nnnorm_bounded
- \+ *lemma* nnnorm_tsum_le
- \+ *lemma* summable_of_norm_bounded_eventually
- \+ *lemma* summable_of_nnnorm_bounded
- \+ *lemma* summable_of_summable_norm
- \+ *lemma* summable_of_summable_nnnorm

modified src/analysis/normed_space/basic.lean
- \- *lemma* cauchy_seq_finset_iff_vanishing_norm
- \- *lemma* summable_iff_vanishing_norm
- \- *lemma* cauchy_seq_finset_of_norm_bounded
- \- *lemma* cauchy_seq_finset_of_summable_norm
- \- *lemma* has_sum_of_subseq_of_summable
- \- *lemma* has_sum_iff_tendsto_nat_of_summable_norm
- \- *lemma* summable_of_norm_bounded
- \- *lemma* has_sum.norm_le_of_bounded
- \- *lemma* tsum_of_norm_bounded
- \- *lemma* norm_tsum_le_tsum_norm
- \- *lemma* tsum_of_nnnorm_bounded
- \- *lemma* nnnorm_tsum_le
- \- *lemma* summable_of_norm_bounded_eventually
- \- *lemma* summable_of_nnnorm_bounded
- \- *lemma* summable_of_summable_norm
- \- *lemma* summable_of_summable_nnnorm
- \- *lemma* norm_coe

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* extension_coe
- \+/\- *lemma* extension_coe



## [2021-10-31 18:58:19](https://github.com/leanprover-community/mathlib/commit/8390325)
fix(data/pequiv): fix lint ([#10043](https://github.com/leanprover-community/mathlib/pull/10043))
#### Estimated changes
modified src/data/pequiv.lean



## [2021-10-31 18:58:18](https://github.com/leanprover-community/mathlib/commit/66f7114)
feat(measure_theory/group): add `measurable_set.const_smul` ([#10025](https://github.com/leanprover-community/mathlib/pull/10025))
Partially based on lemmas from [#2819](https://github.com/leanprover-community/mathlib/pull/2819).
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* zero_smul_subset
- \+ *lemma* subsingleton_zero_smul_set

created src/measure_theory/group/pointwise.lean
- \+ *lemma* measurable_set.const_smul
- \+ *lemma* measurable_set.const_smul_of_ne_zero
- \+ *lemma* measurable_set.const_smul₀

modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* set.subsingleton.measurable_set



## [2021-10-31 17:26:29](https://github.com/leanprover-community/mathlib/commit/f2b77d7)
refactor(set_theory/cardinal): swap sides of `simp` lemmas ([#10040](https://github.com/leanprover-community/mathlib/pull/10040))
## API changes
### Swap sides of simp lemmas
- `cardinal.add_def` is no loner a `simp` lemma, `cardinal.mk_sum` (renamed from `cardinal.add`) simplifies `#(α ⊕ β)` to `lift.{v u} (#α) + lift.{u v} (#β)`;
- `cardinal.mul_def` is no loner a `simp` lemma, `cardinal.mk_prod` (merged with `cardinal.mul`) simplifies `#(α × β)` to `lift.{v u} (#α) * lift.{u v} (#β)`;
- `cardinal.power_def` is no longer a `simp` lemma. New lemma `cardinal.mk_arrow` computes `#(α → β)`. It is not a `simp` lemma because it follows from other `simp` lemmas.
- replace `cardinal.sum_mk` with `cardinal.mk_sigma` and `cardinal.prod_mk` with `cardinal.mk_pi`;
### Other changes
- new lemmas `@[simp] cardinal.lift_uzero` and `cardinal.lift_umax'`;
- split `cardinal.linear_order` into `cardinal.preorder` (doesn't rely on `classical.choice`), `cardinal.partial_order` (needs `classical.choice`, computable), and `cardinal.linear_order` (noncomputable);
- add `cardinal.lift_order_embedding`;
- add `cardinal.mk_psum`;
- rename `cardinal.prop_eq_two` to `cardinal.mk_Prop`, drop the old `mk_Prop`;
- use local notation for natural power;
- rename old `sum_const` to `sum_const'`, the new `@[simp] lemma sum_const` is what used to be `sum_const_eq_lift_mul`;
- rename old `prod_const` to `prod_const'`, the new `@[simp] lemma prod_const` deals with types in different universes;
- add `@[simp]` to `cardinal.prod_eq_zero` and `cardinal.omega_le_mk`;
- add `@[simp]` lemmas `cardinal.mk_eq_one`, `cardinal.mk_vector`, `cardinal.omega_mul_eq`, and `cardinal.mul_omega_eq`;
- replace `mk_plift_of_true` and `mk_plift_of_false` with `mk_plift_true` and `mk_plift_false`;
- `mk_list_eq_mk` and `mk_finset_eq_mk` now assume `[infinite α]` instead of `ω ≤ #α`.
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/data/array/lemmas.lean
- \- *def* vector_equiv_fin

modified src/data/vector/basic.lean
- \+ *def* _root_.equiv.vector_equiv_fin

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/free_module/finite/rank.lean

modified src/linear_algebra/free_module/rank.lean
- \+/\- *lemma* rank_prod
- \+/\- *lemma* rank_prod

modified src/set_theory/cardinal.lean
- \+ *lemma* mk_eq_one
- \+ *lemma* mk_sum
- \+ *lemma* mk_psum
- \+ *lemma* mk_prod
- \+/\- *lemma* omega_le_mk
- \+/\- *lemma* omega_mul_omega
- \- *lemma* add
- \- *lemma* mul
- \+/\- *lemma* omega_le_mk
- \+/\- *lemma* omega_mul_omega
- \+ *theorem* lift_umax'
- \+ *theorem* lift_uzero
- \+/\- *theorem* add_def
- \+/\- *theorem* mul_def
- \+/\- *theorem* power_def
- \+ *theorem* mk_arrow
- \+/\- *theorem* mk_bool
- \+/\- *theorem* mk_Prop
- \+/\- *theorem* lift_one
- \+/\- *theorem* lift_add
- \+/\- *theorem* lift_mul
- \+/\- *theorem* lift_bit0
- \+/\- *theorem* lift_bit1
- \+/\- *theorem* lift_two
- \+/\- *theorem* mk_set
- \+/\- *theorem* lift_two_power
- \+/\- *theorem* cantor
- \+/\- *theorem* one_lt_iff_nontrivial
- \+ *theorem* mk_sigma
- \+/\- *theorem* sum_const
- \+ *theorem* sum_const'
- \+ *theorem* mk_pi
- \+/\- *theorem* prod_const
- \+ *theorem* prod_const'
- \+/\- *theorem* prod_eq_zero
- \+/\- *theorem* mk_empty
- \+/\- *theorem* mk_pempty
- \+/\- *theorem* mk_punit
- \+/\- *theorem* mk_unit
- \+ *theorem* mk_plift_true
- \+ *theorem* mk_plift_false
- \+ *theorem* mk_vector
- \+/\- *theorem* mk_list_eq_sum_pow
- \+/\- *theorem* one_lt_iff_nontrivial
- \+/\- *theorem* add_def
- \+/\- *theorem* mul_def
- \+/\- *theorem* power_def
- \- *theorem* prop_eq_two
- \+/\- *theorem* lift_one
- \+/\- *theorem* lift_add
- \+/\- *theorem* lift_mul
- \+/\- *theorem* lift_bit0
- \+/\- *theorem* lift_bit1
- \+/\- *theorem* lift_two
- \+/\- *theorem* lift_two_power
- \+/\- *theorem* cantor
- \- *theorem* sum_mk
- \+/\- *theorem* sum_const
- \- *theorem* prod_mk
- \+/\- *theorem* prod_const
- \+/\- *theorem* prod_eq_zero
- \- *theorem* mk_prod
- \- *theorem* sum_const_eq_lift_mul
- \+/\- *theorem* mk_empty
- \+/\- *theorem* mk_pempty
- \+/\- *theorem* mk_unit
- \+/\- *theorem* mk_punit
- \- *theorem* mk_plift_of_true
- \- *theorem* mk_plift_of_false
- \+/\- *theorem* mk_bool
- \+/\- *theorem* mk_Prop
- \+/\- *theorem* mk_set
- \+/\- *theorem* mk_list_eq_sum_pow
- \+ *def* lift_order_embedding

modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* omega_mul_eq
- \+ *theorem* mul_omega_eq
- \+/\- *theorem* mk_list_eq_mk
- \+/\- *theorem* mk_finset_eq_mk
- \+/\- *theorem* mk_list_eq_mk
- \+/\- *theorem* mk_finset_eq_mk

modified src/set_theory/cofinality.lean



## [2021-10-31 14:01:29](https://github.com/leanprover-community/mathlib/commit/4ef3fcd)
chore(algebra/group/inj_surj): add 2 missing `def`s ([#10068](https://github.com/leanprover-community/mathlib/pull/10068))
`function.injective.right_cancel_monoid` and `function.injective.cancel_monoid` were missing.
`function.injective.sub_neg_monoid` was also misnamed `function.injective.sub_neg_add_monoid`.
#### Estimated changes
modified src/algebra/group/inj_surj.lean



## [2021-10-31 14:01:28](https://github.com/leanprover-community/mathlib/commit/36de1ef)
chore(ring_theory/noetherian): generalize to semiring ([#10032](https://github.com/leanprover-community/mathlib/pull/10032))
This weakens some typeclasses on some results about `is_noetherian` (which already permits modules over semirings), and relaxes `is_noetherian_ring` to permit semirings.
This does not actually try changing any of the proofs, it just relaxes assumptions that were stronger than what was actually used.
#### Estimated changes
modified src/ring_theory/noetherian.lean
- \+/\- *lemma* well_founded_submodule_gt
- \+/\- *lemma* is_noetherian.induction
- \+/\- *lemma* is_noetherian_ring_iff_ideal_fg
- \+/\- *lemma* well_founded_submodule_gt
- \+/\- *lemma* is_noetherian.induction
- \+/\- *lemma* is_noetherian_ring_iff_ideal_fg
- \+/\- *theorem* set_has_maximal_iff_noetherian
- \+/\- *theorem* monotone_stabilizes_iff_noetherian
- \+/\- *theorem* is_noetherian_ring_iff
- \+/\- *theorem* ring.is_noetherian_of_zero_eq_one
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_tower
- \+/\- *theorem* set_has_maximal_iff_noetherian
- \+/\- *theorem* monotone_stabilizes_iff_noetherian
- \+/\- *theorem* is_noetherian_ring_iff
- \+/\- *theorem* ring.is_noetherian_of_zero_eq_one
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_tower



## [2021-10-31 13:18:04](https://github.com/leanprover-community/mathlib/commit/ca7fee8)
feat(category_theory/limits): Results about pullbacks ([#9984](https://github.com/leanprover-community/mathlib/pull/9984))
- Provided the explicit isomorphism `X ×[Z] Y ≅ Y ×[Z] X`.
- Provided the pullback of f g when either one is iso or when both are mono.
#### Estimated changes
modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* epi_of_is_colimit_mk_id_id
- \+ *lemma* has_pullback_symmetry
- \+ *lemma* pullback_symmetry_hom_comp_fst
- \+ *lemma* pullback_symmetry_hom_comp_snd
- \+ *lemma* pullback_symmetry_inv_comp_fst
- \+ *lemma* pullback_symmetry_inv_comp_snd
- \+ *lemma* has_pushout_symmetry
- \+ *lemma* inl_comp_pushout_symmetry_hom
- \+ *lemma* inr_comp_pushout_symmetry_hom
- \+ *lemma* inl_comp_pushout_symmetry_inv
- \+ *lemma* inr_comp_pushout_symmetry_inv
- \+ *lemma* pullback_cone_of_left_iso_X
- \+ *lemma* pullback_cone_of_left_iso_fst
- \+ *lemma* pullback_cone_of_left_iso_snd
- \+ *lemma* pullback_cone_of_left_iso_π_app_none
- \+ *lemma* pullback_cone_of_left_iso_π_app_left
- \+ *lemma* pullback_cone_of_left_iso_π_app_right
- \+ *lemma* has_pullback_of_left_iso
- \+ *lemma* pullback_cone_of_right_iso_X
- \+ *lemma* pullback_cone_of_right_iso_fst
- \+ *lemma* pullback_cone_of_right_iso_snd
- \+ *lemma* pullback_cone_of_right_iso_π_app_none
- \+ *lemma* pullback_cone_of_right_iso_π_app_left
- \+ *lemma* pullback_cone_of_right_iso_π_app_right
- \+ *lemma* has_pullback_of_right_iso
- \+ *lemma* pushout_cocone_of_left_iso_X
- \+ *lemma* pushout_cocone_of_left_iso_inl
- \+ *lemma* pushout_cocone_of_left_iso_inr
- \+ *lemma* pushout_cocone_of_left_iso_ι_app_none
- \+ *lemma* pushout_cocone_of_left_iso_ι_app_left
- \+ *lemma* pushout_cocone_of_left_iso_ι_app_right
- \+ *lemma* has_pushout_of_left_iso
- \+ *lemma* pushout_cocone_of_right_iso_X
- \+ *lemma* pushout_cocone_of_right_iso_inl
- \+ *lemma* pushout_cocone_of_right_iso_inr
- \+ *lemma* pushout_cocone_of_right_iso_ι_app_none
- \+ *lemma* pushout_cocone_of_right_iso_ι_app_left
- \+ *lemma* pushout_cocone_of_right_iso_ι_app_right
- \+ *lemma* has_pushout_of_right_iso
- \+ *lemma* fst_eq_snd_of_mono_eq
- \+ *lemma* pullback_symmetry_hom_of_mono_eq
- \+ *lemma* inl_eq_inr_of_epi_eq
- \+ *lemma* pullback_symmetry_hom_of_epi_eq
- \+ *def* is_colimit_mk_id_id
- \+ *def* pushout_is_pushout
- \+ *def* pullback_symmetry
- \+ *def* pushout_symmetry
- \+ *def* pullback_cone_of_left_iso
- \+ *def* pullback_cone_of_left_iso_is_limit
- \+ *def* pullback_cone_of_right_iso
- \+ *def* pullback_cone_of_right_iso_is_limit
- \+ *def* pushout_cocone_of_left_iso
- \+ *def* pushout_cocone_of_left_iso_is_limit
- \+ *def* pushout_cocone_of_right_iso
- \+ *def* pushout_cocone_of_right_iso_is_limit



## [2021-10-31 11:57:21](https://github.com/leanprover-community/mathlib/commit/be0a4af)
chore(analysis): move `real.angle` to a dedicated file ([#10065](https://github.com/leanprover-community/mathlib/pull/10065))
We don't use this type anywhere else.
#### Estimated changes
created src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* coe_coe_hom
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_nat_mul_eq_nsmul
- \+ *lemma* coe_int_mul_eq_zsmul
- \+ *lemma* angle_eq_iff_two_pi_dvd_sub
- \+ *lemma* coe_two_pi
- \+ *theorem* cos_eq_iff_eq_or_eq_neg
- \+ *theorem* sin_eq_iff_eq_or_add_eq_pi
- \+ *theorem* cos_sin_inj
- \+ *def* angle
- \+ *def* coe_hom

modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* coe_zero
- \- *lemma* coe_add
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *lemma* coe_nat_mul_eq_nsmul
- \- *lemma* coe_int_mul_eq_zsmul
- \- *lemma* coe_two_pi
- \- *lemma* angle_eq_iff_two_pi_dvd_sub
- \- *theorem* cos_eq_iff_eq_or_eq_neg
- \- *theorem* sin_eq_iff_eq_or_add_eq_pi
- \- *theorem* cos_sin_inj
- \- *def* angle



## [2021-10-31 11:57:20](https://github.com/leanprover-community/mathlib/commit/0433eb6)
doc(topology/uniform_space/uniform_embedding): add some docs ([#10045](https://github.com/leanprover-community/mathlib/pull/10045))
#### Estimated changes
modified src/topology/uniform_space/uniform_embedding.lean
- \- *theorem* uniform_inducing.uniform_embedding



## [2021-10-31 11:57:19](https://github.com/leanprover-community/mathlib/commit/e5f9bec)
chore(linear_algebra/basic): relax ring to semiring ([#10030](https://github.com/leanprover-community/mathlib/pull/10030))
This relaxes a random selection of lemmas from `ring R` to `semiring R`, and cleans up some unused `variables` nearby.
Probably the most useful of these are `submodule.mem_map_equiv`, `map_subtype.rel_iso`, and `submodule.disjoint_iff_comap_eq_bot`
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+/\- *def* iterate_range
- \+/\- *def* iterate_ker
- \+/\- *def* map_subtype.rel_iso
- \+/\- *def* map_subtype.order_embedding
- \+/\- *def* iterate_range
- \+/\- *def* iterate_ker
- \+/\- *def* map_subtype.rel_iso
- \+/\- *def* map_subtype.order_embedding



## [2021-10-31 11:57:18](https://github.com/leanprover-community/mathlib/commit/35cf154)
feat(linear_algebra/eigenspace): define `eigenvalues` of an endomorphism ([#10027](https://github.com/leanprover-community/mathlib/pull/10027))
Prerequisites in `linear_algebra/eigenspace` for [#9995](https://github.com/leanprover-community/mathlib/pull/9995), including a definition `module.End.eigenvalues`, the eigenvalues of an endomorphism considered as a subtype of the scalar ring.
#### Estimated changes
modified src/linear_algebra/eigenspace.lean
- \+ *lemma* has_eigenvalue.exists_has_eigenvector
- \+ *lemma* eigenspace_restrict_le_eigenspace
- \+ *lemma* eigenspace_restrict_eq_bot
- \+ *def* eigenvalues



## [2021-10-31 10:19:07](https://github.com/leanprover-community/mathlib/commit/175ac2c)
chore(algebra/group/defs): golf a proof ([#10067](https://github.com/leanprover-community/mathlib/pull/10067))
Use `monoid.ext` to golf `div_inv_monoid.ext`.
#### Estimated changes
modified src/algebra/group/defs.lean



## [2021-10-31 10:19:06](https://github.com/leanprover-community/mathlib/commit/31c8aa5)
chore(algebra/group_with_zero/basic): zero, one, and pow lemmas for `ring.inverse` ([#10049](https://github.com/leanprover-community/mathlib/pull/10049))
This adds:
* `ring.inverse_zero`
* `ring.inverse_one`
* `ring.inverse_pow` (to match `inv_pow`, `inv_pow₀`)
* `commute.ring_inverse_ring_inverse` (to match `commute.inv_inv`)
#### Estimated changes
modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* inverse_one
- \+ *lemma* inverse_zero
- \+ *lemma* mul_inverse_rev'
- \+/\- *lemma* mul_inverse_rev
- \+ *lemma* commute.ring_inverse_ring_inverse
- \+ *lemma* monoid_with_zero_hom.map_units_inv
- \+/\- *lemma* mul_inverse_rev

modified src/algebra/group_with_zero/power.lean
- \+ *lemma* ring.inverse_pow



## [2021-10-31 09:46:36](https://github.com/leanprover-community/mathlib/commit/43e7d1b)
feat(order/antichain): Antichains ([#9926](https://github.com/leanprover-community/mathlib/pull/9926))
This defines antichains mimicking the definition of chains.
#### Estimated changes
created src/order/antichain.lean
- \+ *lemma* mono
- \+ *lemma* mono_on
- \+ *lemma* eq_of_related
- \+ *lemma* swap
- \+ *lemma* image
- \+ *lemma* preimage
- \+ *lemma* _root_.is_antichain_insert
- \+ *lemma* _root_.is_antichain_insert_of_symmetric
- \+ *lemma* insert_of_symmetric
- \+ *lemma* mk_is_antichain
- \+ *lemma* mk_subset
- \+ *lemma* mk_max
- \+ *lemma* set.subsingleton.is_antichain
- \+ *def* is_antichain



## [2021-10-31 07:34:51](https://github.com/leanprover-community/mathlib/commit/b7f120f)
chore(*): clean up the library using to_additive ([#9790](https://github.com/leanprover-community/mathlib/pull/9790))
Since [#9138](https://github.com/leanprover-community/mathlib/pull/9138) and [#5487](https://github.com/leanprover-community/mathlib/pull/5487) to_additive got a lot better, so a lot of duplication in the library becomes unnecessary and makes maintenence a burden. So we remove a large number of copy-pasted declarations that can now be generated automatically.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_const
- \+/\- *lemma* pow_eq_prod_const
- \+/\- *lemma* prod_const
- \+/\- *lemma* pow_eq_prod_const
- \- *lemma* sum_update_of_mem
- \- *lemma* sum_nsmul
- \- *lemma* sum_const

modified src/algebra/group/defs.lean
- \- *lemma* nsmul_one'

modified src/algebra/group/hom_instances.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_left
- \+/\- *lemma* units.coe_pow
- \- *lemma* sub_zsmul
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_left
- \+/\- *theorem* monoid_hom.map_zpow
- \- *theorem* add_one_zsmul
- \- *theorem* add_zsmul
- \- *theorem* one_add_zsmul
- \- *theorem* zsmul_add_comm
- \- *theorem* zsmul_mul'
- \- *theorem* mul_zsmul
- \- *theorem* bit0_zsmul
- \- *theorem* bit1_zsmul
- \+/\- *theorem* monoid_hom.map_zpow
- \- *theorem* add_monoid_hom.map_zsmul

modified src/algebra/iterate_hom.lean
- \+/\- *lemma* mul_left_iterate
- \+/\- *lemma* mul_right_iterate
- \+/\- *lemma* mul_left_iterate
- \+/\- *lemma* mul_right_iterate
- \- *lemma* add_left_iterate
- \- *lemma* add_right_iterate
- \- *lemma* add_right_iterate_apply_zero

modified src/data/equiv/mul_add.lean

modified src/data/fintype/card.lean
- \- *lemma* sum_take_of_fn

modified src/data/int/gcd.lean

modified src/data/list/basic.lean
- \- *lemma* length_pos_of_sum_ne_zero

modified src/deprecated/submonoid.lean
- \- *lemma* multiples.zero_mem
- \- *lemma* multiples.self_mem
- \- *lemma* multiples.add_mem
- \- *lemma* is_add_submonoid.smul_mem
- \- *lemma* is_add_submonoid.multiple_subset
- \- *def* multiples

modified src/group_theory/coset.lean
- \- *def* quotient

modified src/group_theory/order_of_element.lean
- \+/\- *lemma* order_of_one
- \+/\- *lemma* order_of_eq_one_iff
- \+/\- *lemma* fin_equiv_powers_apply
- \+/\- *lemma* fin_equiv_powers_symm_apply
- \+/\- *lemma* fin_equiv_zpowers_apply
- \+/\- *lemma* fin_equiv_zpowers_symm_apply
- \+/\- *lemma* pow_card_eq_one
- \- *lemma* add_order_of_nsmul_eq_zero
- \- *lemma* nsmul_ne_zero_of_lt_add_order_of'
- \- *lemma* add_order_of_le_of_nsmul_eq_zero
- \+/\- *lemma* order_of_one
- \- *lemma* add_order_of_zero
- \+/\- *lemma* order_of_eq_one_iff
- \- *lemma* add_order_of_eq_one_iff
- \- *lemma* nsmul_eq_mod_add_order_of
- \- *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \- *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \- *lemma* exists_nsmul_eq_self_of_coprime
- \- *lemma* add_order_of_eq_add_order_of_iff
- \- *lemma* add_order_of_injective
- \- *lemma* add_order_of_nsmul'
- \- *lemma* add_order_of_nsmul''
- \- *lemma* add_order_of_eq_prime_pow
- \- *lemma* nsmul_injective_aux
- \- *lemma* nsmul_injective_of_lt_add_order_of
- \- *lemma* zsmul_eq_mod_add_order_of
- \- *lemma* nsmul_inj_mod
- \- *lemma* sum_card_add_order_of_eq_card_nsmul_eq_zero
- \- *lemma* exists_nsmul_eq_zero
- \- *lemma* add_order_of_le_card_univ
- \- *lemma* add_order_of_pos
- \- *lemma* add_order_of_nsmul
- \- *lemma* mem_multiples_iff_mem_range_add_order_of
- \+/\- *lemma* fin_equiv_powers_apply
- \- *lemma* fin_equiv_multiples_apply
- \+/\- *lemma* fin_equiv_powers_symm_apply
- \- *lemma* fin_equiv_multiples_symm_apply
- \- *lemma* multiples_equiv_multiples_apply
- \- *lemma* add_order_of_eq_card_multiples
- \- *lemma* exists_zpow_eq_one
- \- *lemma* exists_zsmul_eq_zero
- \- *lemma* mem_multiples_iff_mem_zmultiples
- \- *lemma* multiples_eq_zmultiples
- \- *lemma* mem_zmultiples_iff_mem_range_add_order_of
- \+/\- *lemma* fin_equiv_zpowers_apply
- \- *lemma* fin_equiv_zmultiples_apply
- \+/\- *lemma* fin_equiv_zpowers_symm_apply
- \- *lemma* fin_equiv_zmultiples_symm_apply
- \- *lemma* zmultiples_equiv_zmultiples_apply
- \- *lemma* add_order_eq_card_zmultiples
- \- *lemma* add_order_of_dvd_card_univ
- \+/\- *lemma* pow_card_eq_one
- \- *lemma* card_nsmul_eq_zero
- \- *lemma* gcd_nsmul_card_eq_zero_iff

modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* coe_copy
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow
- \+/\- *lemma* of_left_inverse_apply
- \+/\- *lemma* of_left_inverse_symm_apply
- \+/\- *lemma* coe_copy
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow
- \- *lemma* mem_closure_singleton
- \- *lemma* closure_singleton_zero
- \- *lemma* coe_smul
- \- *lemma* coe_zsmul
- \+/\- *lemma* of_left_inverse_apply
- \+/\- *lemma* of_left_inverse_symm_apply
- \- *lemma* zmultiples_subset



## [2021-10-31 03:19:22](https://github.com/leanprover-community/mathlib/commit/236f395)
chore(topology/compacts): add a missing simp lemma ([#10063](https://github.com/leanprover-community/mathlib/pull/10063))
#### Estimated changes
modified src/topology/compacts.lean
- \+ *lemma* positive_compacts_univ_val



## [2021-10-31 01:33:41](https://github.com/leanprover-community/mathlib/commit/c952017)
chore(logic/embedding): docs, fixes ([#10047](https://github.com/leanprover-community/mathlib/pull/10047))
* generalize `function.extend` and some lemmas from `Type*` to `Sort*`.
* add missing docs in `logic.embedding`;
* swap `function.embedding.arrow_congr_left` and `function.embedding.arrow_congr_right`;
* use `function.extend` to define the new `function.embedding.arrow_congr_left`.
#### Estimated changes
modified src/algebra/module/pi.lean
- \+/\- *lemma* function.extend_smul
- \+/\- *lemma* function.extend_smul

modified src/logic/basic.lean
- \+/\- *theorem* exists_eq
- \+/\- *theorem* exists_apply_eq_apply
- \+/\- *theorem* exists_apply_eq_apply'
- \+/\- *theorem* exists_eq
- \+/\- *theorem* exists_apply_eq_apply
- \+/\- *theorem* exists_apply_eq_apply'

modified src/logic/embedding.lean
- \+ *lemma* arrow_congr_right_apply
- \+/\- *def* Pi_congr_right
- \+ *def* arrow_congr_right
- \+/\- *def* Pi_congr_right
- \- *def* arrow_congr_left

modified src/logic/function/basic.lean

modified src/set_theory/cardinal.lean



## [2021-10-31 00:02:40](https://github.com/leanprover-community/mathlib/commit/951c063)
chore(data/set/pairwise): rename `set.pairwise_on` to `set.pairwise` to match `list.pairwise` and `multiset.pairwise` ([#10035](https://github.com/leanprover-community/mathlib/pull/10035))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_sUnion

modified src/analysis/box_integral/partition/basic.lean

modified src/analysis/box_integral/partition/split.lean

modified src/analysis/convex/basic.lean
- \+ *lemma* convex_iff_pairwise_pos
- \- *lemma* convex_iff_pairwise_on_pos

modified src/analysis/convex/function.lean
- \+ *lemma* convex_on_iff_pairwise_pos
- \+ *lemma* concave_on_iff_pairwise_pos
- \- *lemma* convex_on_iff_pairwise_on_pos
- \- *lemma* concave_on_iff_pairwise_on_pos

modified src/data/list/nodup.lean
- \+ *lemma* nodup.pairwise_of_set_pairwise
- \- *lemma* nodup.pairwise_of_set_pairwise_on

modified src/data/list/pairwise.lean
- \+ *lemma* pairwise.set_pairwise
- \- *lemma* pairwise.set_pairwise_on

modified src/data/polynomial/field_division.lean

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_of_forall
- \+ *lemma* pairwise.imp_on
- \+ *lemma* pairwise.imp
- \+ *lemma* pairwise.mono
- \+ *lemma* pairwise.mono'
- \+ *lemma* pairwise_top
- \+ *lemma* pairwise_empty
- \+ *lemma* pairwise_singleton
- \+ *lemma* nonempty.pairwise_iff_exists_forall
- \+ *lemma* nonempty.pairwise_eq_iff_exists_eq
- \+ *lemma* pairwise_iff_exists_forall
- \+ *lemma* pairwise_eq_iff_exists_eq
- \+ *lemma* pairwise_union
- \+ *lemma* pairwise_union_of_symmetric
- \+ *lemma* pairwise_insert
- \+ *lemma* pairwise_insert_of_symmetric
- \+ *lemma* pairwise_pair
- \+ *lemma* pairwise_pair_of_symmetric
- \+ *lemma* pairwise_disjoint_on_mono
- \+ *lemma* pairwise_univ
- \+ *lemma* pairwise.on_injective
- \+ *lemma* inj_on.pairwise_image
- \+ *lemma* pairwise_disjoint_fiber
- \+ *lemma* pairwise_Union
- \+ *lemma* pairwise_sUnion
- \+ *lemma* pairwise.set_pairwise
- \- *lemma* pairwise_on_of_forall
- \- *lemma* pairwise_on.imp_on
- \- *lemma* pairwise_on.imp
- \- *lemma* pairwise_on.mono
- \- *lemma* pairwise_on.mono'
- \- *lemma* pairwise_on_top
- \- *lemma* pairwise_on_empty
- \- *lemma* pairwise_on_singleton
- \- *lemma* nonempty.pairwise_on_iff_exists_forall
- \- *lemma* nonempty.pairwise_on_eq_iff_exists_eq
- \- *lemma* pairwise_on_iff_exists_forall
- \- *lemma* pairwise_on_eq_iff_exists_eq
- \- *lemma* pairwise_on_union
- \- *lemma* pairwise_on_union_of_symmetric
- \- *lemma* pairwise_on_insert
- \- *lemma* pairwise_on_insert_of_symmetric
- \- *lemma* pairwise_on_pair
- \- *lemma* pairwise_on_pair_of_symmetric
- \- *lemma* pairwise_on_disjoint_on_mono
- \- *lemma* pairwise_on_univ
- \- *lemma* pairwise_on.on_injective
- \- *lemma* inj_on.pairwise_on_image
- \- *lemma* pairwise_on_disjoint_fiber
- \- *lemma* pairwise_on_Union
- \- *lemma* pairwise_on_sUnion
- \- *lemma* pairwise.pairwise_on
- \- *def* pairwise_on

modified src/geometry/euclidean/circumcenter.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/cycles.lean

modified src/measure_theory/covering/besicovitch.lean

modified src/measure_theory/covering/besicovitch_vector_space.lean

modified src/measure_theory/covering/vitali.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_bUnion_finset
- \+/\- *lemma* measure_bUnion_finset

modified src/order/zorn.lean
- \+/\- *def* chain
- \+/\- *def* chain

modified src/ring_theory/coprime/lemmas.lean

modified src/topology/bases.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* is_closed_of_pairwise_le_dist
- \- *lemma* is_closed_of_pairwise_on_le_dist

modified src/topology/uniform_space/separation.lean



## [2021-10-30 23:31:00](https://github.com/leanprover-community/mathlib/commit/7ef3262)
ci(.github/workflows/bors.yml): "bors" label for staging builds ([#10064](https://github.com/leanprover-community/mathlib/pull/10064))
#### Estimated changes
modified .github/workflows/bors.yml

modified .github/workflows/mk_build_yml.sh



## [2021-10-30 20:45:45](https://github.com/leanprover-community/mathlib/commit/bdf38cf)
chore(*): rename int_pow to zpow ([#10058](https://github.com/leanprover-community/mathlib/pull/10058))
Leftovers of [#9989](https://github.com/leanprover-community/mathlib/pull/9989)
#### Estimated changes
modified src/algebra/group_with_zero/power.lean

modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_zpow_near
- \+ *lemma* exists_zpow_near'
- \- *lemma* exists_int_pow_near
- \- *lemma* exists_int_pow_near'

modified src/analysis/normed_space/basic.lean

modified src/linear_algebra/matrix/zpow.lean

modified src/set_theory/surreal/dyadic.lean
- \+ *lemma* zsmul_pow_two_pow_half
- \- *lemma* nsmul_int_pow_two_pow_half



## [2021-10-30 09:45:40](https://github.com/leanprover-community/mathlib/commit/5ff850b)
feat(algebra/module/submodule_lattice): add `add_subgroup.to_int_submodule` ([#10051](https://github.com/leanprover-community/mathlib/pull/10051))
This converts an `add_subgroup M` to a `submodule ℤ M`. We already have the analogous construction for `add_submonoid M`.
#### Estimated changes
modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* add_subgroup.to_int_submodule_symm
- \+ *lemma* add_subgroup.coe_to_int_submodule
- \+ *lemma* add_subgroup.to_int_submodule_to_add_subgroup
- \+ *lemma* submodule.to_add_subgroup_to_int_submodule
- \+ *def* add_subgroup.to_int_submodule



## [2021-10-30 08:28:49](https://github.com/leanprover-community/mathlib/commit/d06bd9a)
feat(algebra/big_operators/finprod): add finprod_eq_of_bijective ([#10048](https://github.com/leanprover-community/mathlib/pull/10048))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_eq_of_bijective
- \+ *lemma* finprod_comp



## [2021-10-30 06:04:06](https://github.com/leanprover-community/mathlib/commit/06b1d87)
feat(algebra/group): add `commute.is_unit_mul_iff` ([#10042](https://github.com/leanprover-community/mathlib/pull/10042))
#### Estimated changes
modified src/algebra/group/commute.lean
- \+ *lemma* is_unit_mul_iff
- \+ *lemma* _root_.is_unit_mul_self_iff

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* is_unit_pow_succ_iff
- \+/\- *lemma* is_unit_pos_pow_iff
- \+/\- *lemma* is_unit_pos_pow_iff



## [2021-10-30 01:45:12](https://github.com/leanprover-community/mathlib/commit/fcc158e)
chore(*): update to Lean-3.35.0c ([#9988](https://github.com/leanprover-community/mathlib/pull/9988))
Move `stream`, `rbtree`, and `rbmap` from core to `mathlib` and reflows some long lines. Rename some files to avoid name clashes.
#### Estimated changes
modified leanpkg.toml

modified scripts/nolints.txt

modified scripts/style-exceptions.txt

modified src/data/list/defs.lean

created src/data/rbmap/basic.lean
- \+ *def* rbmap_lt
- \+ *def* rbmap
- \+ *def* mk_rbmap
- \+ *def* empty
- \+ *def* to_list
- \+ *def* min
- \+ *def* max
- \+ *def* fold
- \+ *def* rev_fold
- \+ *def* rbmap_lt_dec
- \+ *def* insert
- \+ *def* find_entry
- \+ *def* to_value
- \+ *def* find
- \+ *def* contains
- \+ *def* from_list
- \+ *def* rbmap_of

created src/data/rbmap/default.lean
- \+ *lemma* eq_some_of_to_value_eq_some
- \+ *lemma* eq_none_of_to_value_eq_none
- \+ *lemma* not_mem_mk_rbmap
- \+ *lemma* not_mem_of_empty
- \+ *lemma* not_mem_of_find_entry_none
- \+ *lemma* not_mem_of_find_none
- \+ *lemma* mem_of_find_entry_some
- \+ *lemma* mem_of_find_some
- \+ *lemma* find_entry_eq_find_entry_of_eqv
- \+ *lemma* find_eq_find_of_eqv
- \+ *lemma* find_entry_correct
- \+ *lemma* eqv_of_find_entry_some
- \+ *lemma* eq_of_find_entry_some
- \+ *lemma* find_correct
- \+ *lemma* constains_correct
- \+ *lemma* mem_of_mem_of_eqv
- \+ *lemma* mem_insert_of_incomp
- \+ *lemma* mem_insert
- \+ *lemma* mem_insert_of_equiv
- \+ *lemma* mem_insert_of_mem
- \+ *lemma* equiv_or_mem_of_mem_insert
- \+ *lemma* incomp_or_mem_of_mem_ins
- \+ *lemma* eq_or_mem_of_mem_ins
- \+ *lemma* find_entry_insert_of_eqv
- \+ *lemma* find_entry_insert
- \+ *lemma* find_insert_of_eqv
- \+ *lemma* find_insert
- \+ *lemma* find_entry_insert_of_disj
- \+ *lemma* find_entry_insert_of_not_eqv
- \+ *lemma* find_entry_insert_of_ne
- \+ *lemma* find_insert_of_disj
- \+ *lemma* find_insert_of_not_eqv
- \+ *lemma* find_insert_of_ne
- \+ *lemma* mem_of_min_eq
- \+ *lemma* mem_of_max_eq
- \+ *lemma* eq_leaf_of_min_eq_none
- \+ *lemma* eq_leaf_of_max_eq_none
- \+ *lemma* min_is_minimal
- \+ *lemma* max_is_maximal
- \+ *lemma* min_is_minimal_of_total
- \+ *lemma* max_is_maximal_of_total

created src/data/rbtree/basic.lean
- \+ *lemma* lo_lt_hi
- \+ *lemma* is_searchable_of_is_searchable_of_incomp
- \+ *lemma* is_searchable_of_incomp_of_is_searchable
- \+ *lemma* is_searchable_some_low_of_is_searchable_of_lt
- \+ *lemma* is_searchable_none_low_of_is_searchable_some_low
- \+ *lemma* is_searchable_some_high_of_is_searchable_of_lt
- \+ *lemma* is_searchable_none_high_of_is_searchable_some_high
- \+ *lemma* range
- \+ *lemma* lt_of_mem_left
- \+ *lemma* lt_of_mem_right
- \+ *lemma* lt_of_mem_left_right
- \+ *lemma* depth_min
- \+ *lemma* depth_max'
- \+ *lemma* depth_max
- \+ *lemma* balanced
- \+ *def* lift

created src/data/rbtree/default.lean

created src/data/rbtree/default_lt.lean

created src/data/rbtree/find.lean
- \+ *lemma* find.induction
- \+ *lemma* find_correct
- \+ *lemma* mem_of_mem_exact
- \+ *lemma* find_correct_exact
- \+ *lemma* eqv_of_find_some
- \+ *lemma* find_eq_find_of_eqv

created src/data/rbtree/init.lean
- \+ *def* depth
- \+ *def* fold
- \+ *def* rev_fold
- \+ *def* balance1
- \+ *def* balance1_node
- \+ *def* balance2
- \+ *def* balance2_node
- \+ *def* get_color
- \+ *def* ins
- \+ *def* mk_insert_result
- \+ *def* insert
- \+ *def* mem
- \+ *def* mem_exact
- \+ *def* find
- \+ *def* rbtree
- \+ *def* mk_rbtree
- \+ *def* mem_exact
- \+ *def* depth
- \+ *def* fold
- \+ *def* rev_fold
- \+ *def* empty
- \+ *def* to_list
- \+ *def* insert
- \+ *def* find
- \+ *def* contains
- \+ *def* from_list
- \+ *def* rbtree_of

created src/data/rbtree/insert.lean
- \+ *lemma* balance1_eq₁
- \+ *lemma* balance1_eq₂
- \+ *lemma* balance1_eq₃
- \+ *lemma* balance2_eq₁
- \+ *lemma* balance2_eq₂
- \+ *lemma* balance2_eq₃
- \+ *lemma* balance.cases
- \+ *lemma* balance1_ne_leaf
- \+ *lemma* balance1_node_ne_leaf
- \+ *lemma* balance2_ne_leaf
- \+ *lemma* balance2_node_ne_leaf
- \+ *lemma* ins.induction
- \+ *lemma* is_searchable_balance1
- \+ *lemma* is_searchable_balance1_node
- \+ *lemma* is_searchable_balance2
- \+ *lemma* is_searchable_balance2_node
- \+ *lemma* is_searchable_ins
- \+ *lemma* is_searchable_mk_insert_result
- \+ *lemma* is_searchable_insert
- \+ *lemma* mem_balance1_node_of_mem_left
- \+ *lemma* mem_balance2_node_of_mem_left
- \+ *lemma* mem_balance1_node_of_mem_right
- \+ *lemma* mem_balance2_node_of_mem_right
- \+ *lemma* mem_balance1_node_of_incomp
- \+ *lemma* mem_balance2_node_of_incomp
- \+ *lemma* ins_ne_leaf
- \+ *lemma* insert_ne_leaf
- \+ *lemma* mem_ins_of_incomp
- \+ *lemma* mem_ins_of_mem
- \+ *lemma* mem_mk_insert_result
- \+ *lemma* mem_of_mem_mk_insert_result
- \+ *lemma* mem_insert_of_incomp
- \+ *lemma* mem_insert_of_mem
- \+ *lemma* of_mem_balance1_node
- \+ *lemma* of_mem_balance2_node
- \+ *lemma* equiv_or_mem_of_mem_ins
- \+ *lemma* equiv_or_mem_of_mem_insert
- \+ *lemma* mem_exact_balance1_node_of_mem_exact
- \+ *lemma* mem_exact_balance2_node_of_mem_exact
- \+ *lemma* find_balance1_node
- \+ *lemma* find_balance2_node
- \+ *lemma* ite_eq_of_not_lt
- \+ *lemma* find_ins_of_eqv
- \+ *lemma* find_mk_insert_result
- \+ *lemma* find_insert_of_eqv
- \+ *lemma* weak_trichotomous
- \+ *lemma* find_black_eq_find_red
- \+ *lemma* find_red_of_lt
- \+ *lemma* find_red_of_gt
- \+ *lemma* find_red_of_incomp
- \+ *lemma* find_balance1_lt
- \+ *lemma* find_balance1_node_lt
- \+ *lemma* find_balance1_gt
- \+ *lemma* find_balance1_node_gt
- \+ *lemma* find_balance1_eqv
- \+ *lemma* find_balance1_node_eqv
- \+ *lemma* find_balance2_lt
- \+ *lemma* find_balance2_node_lt
- \+ *lemma* find_balance2_gt
- \+ *lemma* find_balance2_node_gt
- \+ *lemma* find_balance2_eqv
- \+ *lemma* find_balance2_node_eqv
- \+ *lemma* find_ins_of_disj
- \+ *lemma* find_insert_of_disj
- \+ *lemma* find_insert_of_not_eqv
- \+ *lemma* balance1_rb
- \+ *lemma* balance2_rb
- \+ *lemma* balance1_node_rb
- \+ *lemma* balance2_node_rb
- \+ *lemma* of_get_color_eq_red
- \+ *lemma* of_get_color_ne_red
- \+ *lemma* ins_rb
- \+ *lemma* insert_rb
- \+ *lemma* insert_is_red_black
- \+ *def* ins_rb_result
- \+ *def* insert_rb_result

created src/data/rbtree/main.lean
- \+ *lemma* is_searchable_of_well_formed
- \+ *lemma* is_red_black_of_well_formed
- \+ *lemma* balanced
- \+ *lemma* not_mem_mk_rbtree
- \+ *lemma* not_mem_of_empty
- \+ *lemma* mem_of_mem_of_eqv
- \+ *lemma* insert_ne_mk_rbtree
- \+ *lemma* find_correct
- \+ *lemma* find_correct_of_total
- \+ *lemma* find_correct_exact
- \+ *lemma* find_insert_of_eqv
- \+ *lemma* find_insert
- \+ *lemma* find_insert_of_disj
- \+ *lemma* find_insert_of_not_eqv
- \+ *lemma* find_insert_of_ne
- \+ *lemma* not_mem_of_find_none
- \+ *lemma* eqv_of_find_some
- \+ *lemma* eq_of_find_some
- \+ *lemma* mem_of_find_some
- \+ *lemma* find_eq_find_of_eqv
- \+ *lemma* contains_correct
- \+ *lemma* mem_insert_of_incomp
- \+ *lemma* mem_insert
- \+ *lemma* mem_insert_of_equiv
- \+ *lemma* mem_insert_of_mem
- \+ *lemma* equiv_or_mem_of_mem_insert
- \+ *lemma* incomp_or_mem_of_mem_ins
- \+ *lemma* eq_or_mem_of_mem_ins
- \+ *lemma* mem_of_min_eq
- \+ *lemma* mem_of_max_eq
- \+ *lemma* eq_leaf_of_min_eq_none
- \+ *lemma* eq_leaf_of_max_eq_none
- \+ *lemma* min_is_minimal
- \+ *lemma* max_is_maximal

created src/data/rbtree/min_max.lean
- \+ *lemma* mem_of_min_eq
- \+ *lemma* mem_of_max_eq
- \+ *lemma* eq_leaf_of_min_eq_none
- \+ *lemma* eq_leaf_of_max_eq_none
- \+ *lemma* min_is_minimal
- \+ *lemma* max_is_maximal

modified src/data/seq/computation.lean

modified src/data/seq/seq.lean

modified src/data/stream/basic.lean

created src/data/stream/init.lean
- \+ *theorem* nth_zero_cons
- \+ *theorem* head_cons
- \+ *theorem* tail_cons
- \+ *theorem* tail_drop
- \+ *theorem* nth_drop
- \+ *theorem* tail_eq_drop
- \+ *theorem* drop_drop
- \+ *theorem* nth_succ
- \+ *theorem* drop_succ
- \+ *theorem* all_def
- \+ *theorem* any_def
- \+ *theorem* mem_cons
- \+ *theorem* mem_cons_of_mem
- \+ *theorem* eq_or_mem_of_mem_cons
- \+ *theorem* mem_of_nth_eq
- \+ *theorem* drop_map
- \+ *theorem* nth_map
- \+ *theorem* tail_map
- \+ *theorem* head_map
- \+ *theorem* map_eq
- \+ *theorem* map_cons
- \+ *theorem* map_id
- \+ *theorem* map_map
- \+ *theorem* map_tail
- \+ *theorem* mem_map
- \+ *theorem* exists_of_mem_map
- \+ *theorem* drop_zip
- \+ *theorem* nth_zip
- \+ *theorem* head_zip
- \+ *theorem* tail_zip
- \+ *theorem* zip_eq
- \+ *theorem* mem_const
- \+ *theorem* const_eq
- \+ *theorem* tail_const
- \+ *theorem* map_const
- \+ *theorem* nth_const
- \+ *theorem* drop_const
- \+ *theorem* head_iterate
- \+ *theorem* tail_iterate
- \+ *theorem* iterate_eq
- \+ *theorem* nth_zero_iterate
- \+ *theorem* nth_succ_iterate
- \+ *theorem* bisim_simple
- \+ *theorem* coinduction
- \+ *theorem* iterate_id
- \+ *theorem* map_iterate
- \+ *theorem* corec_def
- \+ *theorem* corec_eq
- \+ *theorem* corec_id_id_eq_const
- \+ *theorem* corec_id_f_eq_iterate
- \+ *theorem* corec'_eq
- \+ *theorem* unfolds_eq
- \+ *theorem* nth_unfolds_head_tail
- \+ *theorem* unfolds_head_eq
- \+ *theorem* interleave_eq
- \+ *theorem* tail_interleave
- \+ *theorem* interleave_tail_tail
- \+ *theorem* nth_interleave_left
- \+ *theorem* nth_interleave_right
- \+ *theorem* mem_interleave_left
- \+ *theorem* mem_interleave_right
- \+ *theorem* odd_eq
- \+ *theorem* head_even
- \+ *theorem* tail_even
- \+ *theorem* even_cons_cons
- \+ *theorem* even_tail
- \+ *theorem* even_interleave
- \+ *theorem* interleave_even_odd
- \+ *theorem* nth_even
- \+ *theorem* nth_odd
- \+ *theorem* mem_of_mem_even
- \+ *theorem* mem_of_mem_odd
- \+ *theorem* nil_append_stream
- \+ *theorem* cons_append_stream
- \+ *theorem* append_append_stream
- \+ *theorem* map_append_stream
- \+ *theorem* drop_append_stream
- \+ *theorem* append_stream_head_tail
- \+ *theorem* mem_append_stream_right
- \+ *theorem* mem_append_stream_left
- \+ *theorem* approx_zero
- \+ *theorem* approx_succ
- \+ *theorem* nth_approx
- \+ *theorem* append_approx_drop
- \+ *theorem* take_theorem
- \+ *theorem* cycle_eq
- \+ *theorem* mem_cycle
- \+ *theorem* cycle_singleton
- \+ *theorem* tails_eq
- \+ *theorem* nth_tails
- \+ *theorem* tails_eq_iterate
- \+ *theorem* inits_core_eq
- \+ *theorem* tail_inits
- \+ *theorem* inits_tail
- \+ *theorem* cons_nth_inits_core
- \+ *theorem* nth_inits
- \+ *theorem* inits_eq
- \+ *theorem* zip_inits_tails
- \+ *theorem* identity
- \+ *theorem* composition
- \+ *theorem* homomorphism
- \+ *theorem* interchange
- \+ *theorem* map_eq_apply
- \+ *theorem* nth_nats
- \+ *theorem* nats_eq
- \+ *def* stream
- \+ *def* cons
- \+ *def* head
- \+ *def* tail
- \+ *def* drop
- \+ *def* nth
- \+ *def* all
- \+ *def* any
- \+ *def* map
- \+ *def* zip
- \+ *def* const
- \+ *def* iterate
- \+ *def* corec
- \+ *def* corec_on
- \+ *def* corec'
- \+ *def* unfolds
- \+ *def* interleave
- \+ *def* even
- \+ *def* odd
- \+ *def* append_stream
- \+ *def* approx
- \+ *def* cycle
- \+ *def* tails
- \+ *def* inits_core
- \+ *def* inits
- \+ *def* pure
- \+ *def* apply
- \+ *def* nats

modified src/data/tree.lean

modified src/tactic/derive_inhabited.lean

modified test/coinductive.lean



## [2021-10-29 19:43:29](https://github.com/leanprover-community/mathlib/commit/c722dae)
chore(data/fintype/basic): add a few `infinite` instances ([#10037](https://github.com/leanprover-community/mathlib/pull/10037))
#### Estimated changes
modified src/data/fintype/basic.lean
- \- *lemma* nonempty

modified src/data/multiset/basic.lean
- \+ *theorem* repeat_injective



## [2021-10-29 19:43:27](https://github.com/leanprover-community/mathlib/commit/4f053a5)
feat(data/list): chain'_drop lemma ([#10028](https://github.com/leanprover-community/mathlib/pull/10028))
#### Estimated changes
modified src/data/list/chain.lean
- \+ *theorem* chain'.drop



## [2021-10-29 17:12:04](https://github.com/leanprover-community/mathlib/commit/c545660)
chore(algebra/group_with_zero/basic): move `ring.inverse`, generalize and rename `inverse_eq_has_inv` ([#10033](https://github.com/leanprover-community/mathlib/pull/10033))
This moves `ring.inverse` earlier in the import graph, since it's not about rings at all.
#### Estimated changes
modified src/algebra/field.lean
- \- *lemma* inverse_eq_has_inv

modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* inverse_unit
- \+ *lemma* inverse_non_unit
- \+ *lemma* mul_inverse_cancel
- \+ *lemma* inverse_mul_cancel
- \+ *lemma* mul_inverse_cancel_right
- \+ *lemma* inverse_mul_cancel_right
- \+ *lemma* mul_inverse_cancel_left
- \+ *lemma* inverse_mul_cancel_left
- \+ *lemma* mul_inverse_rev
- \+ *lemma* ring.inverse_eq_inv
- \+ *lemma* ring.inverse_eq_inv'

modified src/algebra/ring/basic.lean
- \- *lemma* inverse_unit
- \- *lemma* inverse_non_unit
- \- *lemma* mul_inverse_cancel
- \- *lemma* inverse_mul_cancel
- \- *lemma* mul_inverse_cancel_right
- \- *lemma* inverse_mul_cancel_right
- \- *lemma* mul_inverse_cancel_left
- \- *lemma* inverse_mul_cancel_left
- \- *lemma* mul_inverse_rev

modified src/analysis/calculus/times_cont_diff.lean



## [2021-10-29 14:39:48](https://github.com/leanprover-community/mathlib/commit/e1bafaa)
feat(category_theory/limits/shapes/images): some explicit instances of has_image_map ([#9977](https://github.com/leanprover-community/mathlib/pull/9977))
#### Estimated changes
modified src/category_theory/arrow.lean
- \+ *lemma* inv_left
- \+ *lemma* inv_right

modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* fac_lift
- \+ *lemma* has_image.of_arrow_iso
- \- *lemma* is_image.fac_lift
- \+ *def* of_arrow_iso
- \+ *def* of_arrow_iso
- \+ *def* of_arrow_iso



## [2021-10-29 13:53:07](https://github.com/leanprover-community/mathlib/commit/4f3443a)
feat(measure_theory/group/arithmetic): add a section about `opposite` ([#10026](https://github.com/leanprover-community/mathlib/pull/10026))
#### Estimated changes
modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_op
- \+ *lemma* measurable_unop



## [2021-10-29 08:04:41](https://github.com/leanprover-community/mathlib/commit/3f6174b)
fix(tactic/norm_cast): make push_cast discharger match the others ([#10021](https://github.com/leanprover-community/mathlib/pull/10021))
closes [#9822](https://github.com/leanprover-community/mathlib/pull/9822)
#### Estimated changes
modified src/tactic/norm_cast.lean

modified test/linarith.lean
- \+ *lemma* mytest



## [2021-10-29 01:24:36](https://github.com/leanprover-community/mathlib/commit/4ce2a5f)
chore(algebra/module/submodule_lattice): lemmas about the trivial submodule ([#10022](https://github.com/leanprover-community/mathlib/pull/10022))
Lemmas about the trivial submodule.  Also move an existing lemma `exists_mem_ne_zero_of_ne_bot` about the trivial submodule from `linear_algebra/dimension` to `algebra/module/submodule_lattice`, since it doesn't use any facts about dimension.
#### Estimated changes
modified src/algebra/module/submodule_lattice.lean
- \+/\- *lemma* nonzero_mem_of_bot_lt
- \+ *lemma* exists_mem_ne_zero_of_ne_bot
- \+ *lemma* eq_bot_of_subsingleton
- \+/\- *lemma* nonzero_mem_of_bot_lt

modified src/linear_algebra/dimension.lean
- \- *lemma* exists_mem_ne_zero_of_ne_bot

modified src/linear_algebra/eigenspace.lean



## [2021-10-29 01:24:35](https://github.com/leanprover-community/mathlib/commit/7538f9b)
feat(data/list/defs): map_with_prefix_suffix and map_with_complement ([#10020](https://github.com/leanprover-community/mathlib/pull/10020))
Adds two list definitions: one that will be useful to me, and a generalization which may be useful to @semorrison
#### Estimated changes
modified src/data/list/defs.lean
- \+ *def* map_with_prefix_suffix_aux
- \+ *def* map_with_prefix_suffix
- \+ *def* map_with_complement



## [2021-10-29 01:24:33](https://github.com/leanprover-community/mathlib/commit/c7f5139)
chore(measure_theory): drop a few `measurable_set` assumptions ([#9999](https://github.com/leanprover-community/mathlib/pull/9999))
We had an extra `measurable_set` assumption in (one of the copies of) Caratheodory. Also remove `measurable f` assumption in `is_finite_measure (map f μ)` and make it an instance.
#### Estimated changes
modified src/measure_theory/constructions/pi.lean

modified src/measure_theory/decomposition/unsigned_hahn.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_inter_add_diff
- \+/\- *lemma* measure_union_add_inter
- \+ *lemma* measure_union_add_inter'
- \+/\- *lemma* restrict_union_add_inter
- \+/\- *lemma* measure.is_finite_measure_map
- \- *lemma* measure_eq_inter_diff
- \+/\- *lemma* measure_union_add_inter
- \+/\- *lemma* restrict_union_add_inter
- \+/\- *lemma* measure.is_finite_measure_map

modified src/probability_theory/density.lean



## [2021-10-29 00:33:15](https://github.com/leanprover-community/mathlib/commit/bdcb731)
feat(linear_algebra/matrix/adjugate): det_adjugate and adjugate_adjugate ([#9991](https://github.com/leanprover-community/mathlib/pull/9991))
This also adds `matrix.mv_polynomial_X`
#### Estimated changes
modified src/linear_algebra/matrix/adjugate.lean
- \+/\- *lemma* _root_.ring_hom.map_adjugate
- \+ *lemma* _root_.alg_hom.map_adjugate
- \+ *lemma* det_adjugate
- \+ *lemma* det_smul_adjugate_adjugate
- \+ *lemma* adjugate_adjugate
- \+ *lemma* adjugate_adjugate'
- \- *lemma* det_adjugate_of_cancel
- \- *lemma* det_adjugate_eq_one
- \- *lemma* det_adjugate_of_is_unit
- \+/\- *lemma* _root_.ring_hom.map_adjugate

created src/linear_algebra/matrix/mv_polynomial.lean
- \+ *lemma* mv_polynomial_X_map_eval₂
- \+ *lemma* mv_polynomial_X_map_matrix_eval
- \+ *lemma* mv_polynomial_X_map_matrix_aeval
- \+ *lemma* det_mv_polynomial_X_ne_zero

modified src/linear_algebra/special_linear_group.lean



## [2021-10-28 20:48:25](https://github.com/leanprover-community/mathlib/commit/415da22)
chore(topology,measure_theory): generalize a few instances ([#9967](https://github.com/leanprover-community/mathlib/pull/9967))
* Prove that `Π i : ι, π i` has second countable topology if `ι` is encodable and each `π i` has second countable topology.
* Similarly for `borel_space`.
* Preserve old instances about `fintype` because we don't have (and can't have) an instance `fintype ι → encodable ι`.
#### Estimated changes
modified src/data/subtype.lean
- \+ *lemma* surjective_restrict

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/bases.lean



## [2021-10-28 20:48:24](https://github.com/leanprover-community/mathlib/commit/0cfae43)
feat(archive/imo): IMO 2021 Q1 ([#8432](https://github.com/leanprover-community/mathlib/pull/8432))
Formalised solution to IMO 2021 Q1
#### Estimated changes
created archive/imo/imo2021_q1.lean
- \+ *lemma* lower_bound
- \+ *lemma* upper_bound
- \+ *lemma* radical_inequality
- \+ *lemma* exists_numbers_in_interval
- \+ *lemma* exists_triplet_summing_to_squares
- \+ *lemma* exists_finset_3_le_card_with_pairs_summing_to_squares
- \+ *theorem* IMO_2021_Q1

modified src/algebra/order/monoid.lean
- \+ *lemma* lt_or_lt_of_add_lt_add

modified src/data/finset/basic.lean
- \+ *lemma* exists_subset_or_subset_of_two_mul_lt_card



## [2021-10-28 18:57:48](https://github.com/leanprover-community/mathlib/commit/99a2d5b)
feat(ring_theory/adjoin_root): golf and generalize the algebra structure on `adjoin_root` ([#10019](https://github.com/leanprover-community/mathlib/pull/10019))
We already have a more general version of this instance elsewhere, lets just reuse it.
#### Estimated changes
modified src/ring_theory/adjoin_root.lean
- \+ *lemma* algebra_map_eq'



## [2021-10-28 18:57:46](https://github.com/leanprover-community/mathlib/commit/18dce13)
feat(data/finset/interval): Bounded intervals in locally finite orders are finite ([#9960](https://github.com/leanprover-community/mathlib/pull/9960))
A set which is bounded above and below is finite. A set which is bounded below in an `order_top` is finite. A set which is bounded above in an `order_bot` is finite.
Also provide the `order_dual` constructions for `bdd_stuff` and `locally_finite_order`.
#### Estimated changes
modified src/data/finset/locally_finite.lean
- \+ *lemma* _root_.bdd_below.finite_of_bdd_above
- \+ *lemma* _root_.bdd_below.finite
- \+ *lemma* _root_.bdd_above.finite
- \+ *def* _root_.set.fintype_of_mem_bounds

modified src/order/bounds.lean
- \+ *lemma* bdd_above.dual
- \+ *lemma* bdd_below.dual
- \+ *lemma* is_least.dual
- \+ *lemma* is_greatest.dual
- \+ *lemma* is_lub.dual
- \+ *lemma* is_glb.dual
- \+/\- *lemma* is_glb.lower_bounds_eq
- \+/\- *lemma* is_glb.nonempty
- \+/\- *lemma* lt_is_glb_iff
- \+/\- *lemma* is_glb_lt_iff
- \+/\- *lemma* is_glb.lower_bounds_eq
- \+/\- *lemma* is_glb.nonempty
- \+/\- *lemma* lt_is_glb_iff
- \+/\- *lemma* is_glb_lt_iff

modified src/order/locally_finite.lean
- \+ *lemma* this
- \+ *lemma* Icc_to_dual
- \+ *lemma* Ico_to_dual
- \+ *lemma* Ioc_to_dual
- \+ *lemma* Ioo_to_dual



## [2021-10-28 18:57:45](https://github.com/leanprover-community/mathlib/commit/1733920)
feat(list): add some lemmas ([#9873](https://github.com/leanprover-community/mathlib/pull/9873))
Add a few lemmas about lists.
These are helpful when manipulating lists.
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* last'_eq_last_of_ne_nil
- \+ *theorem* mem_last'_cons
- \+ *theorem* last'_cons_cons
- \+ *theorem* head'_append

modified src/data/list/pairwise.lean
- \+ *theorem* pairwise.drop



## [2021-10-28 17:00:22](https://github.com/leanprover-community/mathlib/commit/e927aa4)
feat(data/set/function): restrict `dite/ite/piecewise/extend` ([#10017](https://github.com/leanprover-community/mathlib/pull/10017))
#### Estimated changes
modified src/data/set/function.lean
- \+ *lemma* restrict_dite
- \+ *lemma* restrict_dite_compl
- \+ *lemma* restrict_ite
- \+ *lemma* restrict_ite_compl
- \+ *lemma* restrict_piecewise
- \+ *lemma* restrict_piecewise_compl
- \+ *lemma* restrict_extend_range
- \+ *lemma* restrict_extend_compl_range



## [2021-10-28 17:00:20](https://github.com/leanprover-community/mathlib/commit/0d6548f)
chore(*): a few lemmas about `range_splitting ([#10016](https://github.com/leanprover-community/mathlib/pull/10016))
#### Estimated changes
modified src/data/equiv/set.lean
- \+ *lemma* coe_of_injective_symm

modified src/data/set/basic.lean
- \+ *lemma* coe_comp_range_factorization
- \+ *lemma* right_inverse_range_splitting
- \+ *lemma* preimage_range_splitting

modified src/logic/function/basic.lean
- \+ *theorem* left_inverse.right_inverse_of_injective
- \+ *theorem* left_inverse.right_inverse_of_surjective



## [2021-10-28 17:00:18](https://github.com/leanprover-community/mathlib/commit/b9ff26b)
chore(measure_theory/measure/measure_space): reorder, golf ([#10015](https://github.com/leanprover-community/mathlib/pull/10015))
Move `restrict_apply'` up and use it to golf some proofs. Drop an unneeded `measurable_set` assumption in 1 proof.
#### Estimated changes
modified src/measure_theory/function/ae_eq_of_integral.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* restrict_apply'
- \+ *lemma* restrict_eq_self'
- \+/\- *lemma* restrict_empty
- \+/\- *lemma* ae_of_ae_restrict_of_ae_restrict_compl
- \+/\- *lemma* restrict_empty
- \- *lemma* restrict_eq_self_of_measurable_subset
- \+/\- *lemma* restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* restrict_apply'
- \- *lemma* restrict_eq_self_of_subset_of_measurable
- \+/\- *lemma* ae_of_ae_restrict_of_ae_restrict_compl



## [2021-10-28 17:00:16](https://github.com/leanprover-community/mathlib/commit/fd6f681)
feat(order/bounded_lattice): add `is_compl.le_sup_right_iff_inf_left_le` ([#10014](https://github.com/leanprover-community/mathlib/pull/10014))
This lemma is a generalization of `is_compl.inf_left_eq_bot_iff`.
Also drop `inf_eq_bot_iff_le_compl` in favor of
`is_compl.inf_left_eq_bot_iff` and add
`set.subset_union_compl_iff_inter_subset`.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *theorem* subset_union_compl_iff_inter_subset

modified src/order/bounded_lattice.lean
- \+ *lemma* inf_left_le_of_le_sup_right
- \+ *lemma* le_sup_right_iff_inf_left_le
- \- *lemma* inf_eq_bot_iff_le_compl

modified src/topology/uniform_space/separation.lean



## [2021-10-28 17:00:14](https://github.com/leanprover-community/mathlib/commit/22d32dc)
fix(field_theory/intermediate_field): use a better `algebra.smul` definition, and generalize ([#10012](https://github.com/leanprover-community/mathlib/pull/10012))
Previously coe_smul was not true by `rfl`
#### Estimated changes
modified src/field_theory/intermediate_field.lean
- \+ *lemma* coe_smul
- \+ *lemma* lift2_algebra_map

modified src/ring_theory/trace.lean



## [2021-10-28 17:00:12](https://github.com/leanprover-community/mathlib/commit/fe76b5c)
feat(group_theory/subgroup/basic): `mul_mem_sup` ([#10007](https://github.com/leanprover-community/mathlib/pull/10007))
Adds `mul_mem_sup` and golfs a couple proofs that reprove this result.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mul_mem_sup

modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mul_mem_sup

modified src/group_theory/sylow.lean



## [2021-10-28 17:00:10](https://github.com/leanprover-community/mathlib/commit/c495ed6)
move(data/set/pairwise): Move `set.pairwise_on` ([#9986](https://github.com/leanprover-community/mathlib/pull/9986))
This moves `set.pairwise_on` to `data.set.pairwise`, where `pairwise` and `set.pairwise_disjoint` already are.
#### Estimated changes
modified src/analysis/box_integral/partition/basic.lean

modified src/data/list/pairwise.lean

modified src/data/set/basic.lean
- \- *lemma* pairwise_on_of_forall
- \- *lemma* pairwise_on.imp_on
- \- *lemma* pairwise_on.imp
- \- *lemma* pairwise_on_empty
- \- *lemma* pairwise_on_singleton
- \- *lemma* pairwise_on_iff_exists_forall
- \- *lemma* pairwise_on_eq_iff_exists_eq
- \- *lemma* pairwise_on_union
- \- *lemma* pairwise_on_union_of_symmetric
- \- *lemma* pairwise_on_insert
- \- *lemma* pairwise_on_insert_of_symmetric
- \- *lemma* pairwise_on_pair
- \- *lemma* pairwise_on_pair_of_symmetric
- \- *lemma* pairwise_on_disjoint_on_mono
- \- *theorem* pairwise_on.mono
- \- *theorem* pairwise_on.mono'
- \- *theorem* pairwise_on_top
- \- *theorem* nonempty.pairwise_on_iff_exists_forall
- \- *theorem* nonempty.pairwise_on_eq_iff_exists_eq
- \- *def* pairwise_on

modified src/data/set/function.lean
- \- *lemma* inj_on.pairwise_on_image

modified src/data/set/lattice.lean
- \- *lemma* pairwise_on_Union
- \- *lemma* pairwise_on_sUnion
- \- *lemma* bUnion_diff_bUnion_eq
- \- *theorem* pairwise_on_disjoint_fiber

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise.mono
- \+ *lemma* pairwise_on_bool
- \+ *lemma* pairwise_disjoint_on_bool
- \+/\- *lemma* symmetric.pairwise_on
- \+ *lemma* pairwise_disjoint_on
- \+ *lemma* pairwise_on_of_forall
- \+ *lemma* pairwise_on.imp_on
- \+ *lemma* pairwise_on.imp
- \+ *lemma* pairwise_on.mono
- \+ *lemma* pairwise_on.mono'
- \+ *lemma* pairwise_on_top
- \+ *lemma* pairwise_on_empty
- \+ *lemma* pairwise_on_singleton
- \+ *lemma* nonempty.pairwise_on_iff_exists_forall
- \+ *lemma* nonempty.pairwise_on_eq_iff_exists_eq
- \+ *lemma* pairwise_on_iff_exists_forall
- \+ *lemma* pairwise_on_eq_iff_exists_eq
- \+ *lemma* pairwise_on_union
- \+ *lemma* pairwise_on_union_of_symmetric
- \+ *lemma* pairwise_on_insert
- \+ *lemma* pairwise_on_insert_of_symmetric
- \+ *lemma* pairwise_on_pair
- \+ *lemma* pairwise_on_pair_of_symmetric
- \+ *lemma* pairwise_on_disjoint_on_mono
- \+ *lemma* pairwise_on_univ
- \+ *lemma* pairwise_on.on_injective
- \+ *lemma* inj_on.pairwise_on_image
- \+ *lemma* pairwise_on_disjoint_fiber
- \+ *lemma* pairwise_on_Union
- \+ *lemma* pairwise_on_sUnion
- \+ *lemma* pairwise.pairwise_on
- \+ *lemma* pairwise_disjoint_fiber
- \+ *lemma* bUnion_diff_bUnion_eq
- \+/\- *lemma* symmetric.pairwise_on
- \- *theorem* set.pairwise_on_univ
- \- *theorem* set.pairwise_on.on_injective
- \- *theorem* pairwise.mono
- \- *theorem* pairwise_on_bool
- \- *theorem* pairwise_disjoint_on_bool
- \- *theorem* pairwise_disjoint_on
- \- *theorem* pairwise.pairwise_on
- \- *theorem* pairwise_disjoint_fiber
- \+/\- *def* pairwise
- \+ *def* pairwise_on
- \+/\- *def* pairwise

modified src/order/zorn.lean



## [2021-10-28 17:00:08](https://github.com/leanprover-community/mathlib/commit/628f418)
feat(computability/tm_to_partrec): prove finiteness ([#6955](https://github.com/leanprover-community/mathlib/pull/6955))
The proof in this file was incomplete, and I finally found the time to
finish it. `tm_to_partrec.lean` constructs a turing machine that can
simulate a given partial recursive function. Previously, the functional
correctness of this machine was proven, but it uses an infinite state
space so it is not a priori obvious that it is in fact a true (finite)
turing machine, which is important for the Church-Turing theorem. This
PR adds a proof that the machine is in fact finite.
#### Estimated changes
modified src/computability/tm_to_partrec.lean
- \+ *theorem* tr_stmts₁_trans
- \+ *theorem* tr_stmts₁_self
- \+ *theorem* code_supp'_self
- \+ *theorem* code_supp_self
- \+ *theorem* code_supp_zero
- \+ *theorem* code_supp_succ
- \+ *theorem* code_supp_tail
- \+ *theorem* code_supp_cons
- \+ *theorem* code_supp_comp
- \+ *theorem* code_supp_case
- \+ *theorem* code_supp_fix
- \+ *theorem* cont_supp_cons₁
- \+ *theorem* cont_supp_cons₂
- \+ *theorem* cont_supp_comp
- \+ *theorem* cont_supp_fix
- \+ *theorem* cont_supp_halt
- \+ *theorem* supports_insert
- \+ *theorem* supports_singleton
- \+ *theorem* supports_union
- \+ *theorem* supports_bUnion
- \+ *theorem* head_supports
- \+ *theorem* ret_supports
- \+ *theorem* tr_stmts₁_supports
- \+ *theorem* tr_stmts₁_supports'
- \+ *theorem* tr_normal_supports
- \+ *theorem* code_supp'_supports
- \+ *theorem* cont_supp_supports
- \+ *theorem* code_supp_supports
- \+ *theorem* tr_supports
- \+ *def* tr_stmts₁
- \+ *def* code_supp'
- \+ *def* cont_supp
- \+ *def* code_supp
- \+ *def* Λ'.supports
- \+ *def* supports

modified src/computability/turing_machine.lean

modified src/data/finset/basic.lean
- \+ *theorem* union_subset_left
- \+ *theorem* union_subset_right
- \+ *theorem* union_left_idem
- \+ *theorem* union_right_idem
- \+ *theorem* inter_left_idem
- \+ *theorem* inter_right_idem
- \+ *theorem* bUnion_subset



## [2021-10-28 15:13:55](https://github.com/leanprover-community/mathlib/commit/c8d1429)
feat(data/{finset,multiset}/locally_finite): Simple interval lemmas ([#9877](https://github.com/leanprover-community/mathlib/pull/9877))
`(finset/multiset).image_add_(left/right)_Ixx` and `multiset.nodup_Ixx`
#### Estimated changes
modified src/algebra/big_operators/intervals.lean
- \+/\- *lemma* sum_Ico_add
- \+/\- *lemma* prod_Ico_add
- \+/\- *lemma* sum_Ico_add
- \+/\- *lemma* prod_Ico_add

modified src/data/finset/locally_finite.lean
- \+ *lemma* image_add_left_Icc
- \+ *lemma* image_add_left_Ico
- \+ *lemma* image_add_left_Ioc
- \+ *lemma* image_add_left_Ioo
- \+ *lemma* image_add_right_Icc
- \+ *lemma* image_add_right_Ico
- \+ *lemma* image_add_right_Ioc
- \+ *lemma* image_add_right_Ioo
- \- *lemma* image_add_const_Icc
- \- *lemma* image_add_const_Ico
- \- *lemma* image_add_const_Ioc
- \- *lemma* image_add_const_Ioo

modified src/data/multiset/locally_finite.lean
- \+ *lemma* nodup_Icc
- \+ *lemma* nodup_Ioc
- \+ *lemma* nodup_Ioo
- \+ *lemma* map_add_left_Icc
- \+ *lemma* map_add_left_Ioc
- \+ *lemma* map_add_left_Ioo
- \+ *lemma* map_add_right_Icc
- \+ *lemma* map_add_right_Ioc
- \+ *lemma* map_add_right_Ioo
- \- *lemma* map_add_const_Icc
- \- *lemma* map_add_const_Ioc
- \- *lemma* map_add_const_Ioo



## [2021-10-28 12:41:11](https://github.com/leanprover-community/mathlib/commit/acbb2a5)
feat(analysis/normed_space/pi_Lp): use typeclass inference for `1 ≤ p` ([#9922](https://github.com/leanprover-community/mathlib/pull/9922))
In `measure_theory.Lp`, the exponent `(p : ℝ≥0∞)` is an explicit hypothesis, and typeclass inference finds `[fact (1 ≤ p)]` silently (with the help of some pre-built `fact_one_le_two_ennreal` etc for specific use cases).
Currently, in `pi_Lp`, the fact that `(hp : 1 ≤ p)` must be provided explicitly.  I propose changing over to the `fact` system as used `measure_theory.Lp` -- I think it looks a bit prettier in typical use cases.
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean

modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* fact_one_le_one_real
- \+ *lemma* fact_one_le_two_real
- \+/\- *lemma* lipschitz_with_equiv
- \+/\- *lemma* norm_eq
- \+/\- *lemma* norm_eq_of_nat
- \+/\- *lemma* lipschitz_with_equiv
- \+/\- *lemma* norm_eq
- \+/\- *lemma* norm_eq_of_nat
- \+/\- *def* pi_Lp
- \+/\- *def* pseudo_emetric_aux
- \+/\- *def* emetric_aux
- \+/\- *def* pi_Lp
- \+/\- *def* pseudo_emetric_aux
- \+/\- *def* emetric_aux

modified src/geometry/manifold/instances/real.lean



## [2021-10-28 09:24:44](https://github.com/leanprover-community/mathlib/commit/b0349aa)
chore(measure_theory): a `continuous_map` is measurable ([#9998](https://github.com/leanprover-community/mathlib/pull/9998))
Also move the proof of `homeomorph.measurable` up and use it in the
definition of `homeomorph.to_measurable_equiv`.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous_map.measurable
- \- *lemma* homeomorph.measurable



## [2021-10-28 09:24:43](https://github.com/leanprover-community/mathlib/commit/73423cf)
feat(measure/measurable_space): add `measurable_equiv.of_unique_of_unique` ([#9968](https://github.com/leanprover-community/mathlib/pull/9968))
Also fix a typo in a lemma name: `measurable_equiv.measurable_coe_iff` → `measurable_comp_iff`.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/measurable_space.lean
- \+ *def* of_unique_of_unique



## [2021-10-28 09:24:41](https://github.com/leanprover-community/mathlib/commit/7f2b806)
feat(analysis/inner_product_space/dual): complex Riesz representation theorem ([#9924](https://github.com/leanprover-community/mathlib/pull/9924))
Now that we have conjugate-linear maps, the Riesz representation theorem can be stated in a form that works over both `ℝ` and `ℂ`, as the construction of a conjugate-linear isometric equivalence from a complete inner product space `E` to its dual.
#### Estimated changes
modified src/analysis/inner_product_space/dual.lean
- \+/\- *lemma* to_dual_map_apply
- \+/\- *lemma* to_dual_apply
- \- *lemma* to_dual'_apply
- \- *lemma* norm_to_dual'_apply
- \- *lemma* to_dual'_isometry
- \- *lemma* to_dual'_surjective
- \+/\- *lemma* to_dual_map_apply
- \+/\- *lemma* to_dual_apply
- \+/\- *def* to_dual_map
- \+/\- *def* to_dual
- \- *def* to_dual'
- \+/\- *def* to_dual_map
- \+/\- *def* to_dual



## [2021-10-28 06:57:32](https://github.com/leanprover-community/mathlib/commit/f78b739)
feat(category_theory/arrow): is_iso, mono, epi instances for maps between arrows ([#9976](https://github.com/leanprover-community/mathlib/pull/9976))
#### Estimated changes
modified src/category_theory/arrow.lean
- \+ *lemma* is_iso_of_iso_left_of_is_iso_right



## [2021-10-28 06:57:30](https://github.com/leanprover-community/mathlib/commit/8159af6)
feat(measure_theory/construction/borel_space): two measures are equal if they agree on closed-open intervals ([#9396](https://github.com/leanprover-community/mathlib/pull/9396))
#### Estimated changes
modified src/data/set/intervals/disjoint.lean
- \+ *lemma* Union_Ico_eq_Iio_self_iff
- \+ *lemma* Union_Ioc_eq_Ioi_self_iff
- \+ *lemma* bUnion_Ico_eq_Iio_self_iff
- \+ *lemma* bUnion_Ioc_eq_Ioi_self_iff

modified src/data/set/lattice.lean

modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* borel_eq_generate_from_Iio
- \+ *lemma* borel_eq_generate_from_Ioi
- \+ *lemma* bsupr_measure_Iic
- \+ *lemma* generate_from_Ico_mem_le_borel
- \+ *lemma* dense.borel_eq_generate_from_Ico_mem_aux
- \+ *lemma* dense.borel_eq_generate_from_Ico_mem
- \+ *lemma* borel_eq_generate_from_Ico
- \+ *lemma* dense.borel_eq_generate_from_Ioc_mem_aux
- \+ *lemma* dense.borel_eq_generate_from_Ioc_mem
- \+ *lemma* borel_eq_generate_from_Ioc
- \+ *lemma* ext_of_Ico_finite
- \+ *lemma* ext_of_Ioc_finite
- \+ *lemma* ext_of_Ico'
- \+ *lemma* ext_of_Ioc'
- \+ *lemma* ext_of_Ico
- \+ *lemma* ext_of_Ioc
- \+ *lemma* ext_of_Iic
- \+ *lemma* ext_of_Ici
- \- *lemma* is_pi_system_Ioo_mem
- \- *lemma* is_pi_system_Ioo
- \- *lemma* borel_eq_generate_Iio
- \- *lemma* borel_eq_generate_Ioi

modified src/measure_theory/measurable_space.lean
- \+ *lemma* generate_from_mono
- \- *lemma* generate_from_le_generate_from

modified src/measure_theory/measure/stieltjes.lean

modified src/measure_theory/pi_system.lean
- \+ *lemma* is_pi_system_image_Iio
- \+ *lemma* is_pi_system_Iio
- \+ *lemma* is_pi_system_image_Ioi
- \+ *lemma* is_pi_system_Ioi
- \+ *lemma* is_pi_system_Ixx_mem
- \+ *lemma* is_pi_system_Ixx
- \+ *lemma* is_pi_system_Ioo_mem
- \+ *lemma* is_pi_system_Ioo
- \+ *lemma* is_pi_system_Ioc_mem
- \+ *lemma* is_pi_system_Ioc
- \+ *lemma* is_pi_system_Ico_mem
- \+ *lemma* is_pi_system_Ico
- \+ *lemma* is_pi_system_Icc_mem
- \+ *lemma* is_pi_system_Icc

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* dense.order_dual
- \+ *lemma* dense.exists_lt
- \+ *lemma* dense.exists_gt
- \+ *lemma* dense.exists_le
- \+ *lemma* dense.exists_ge
- \+ *lemma* dense.exists_le'
- \+ *lemma* dense.exists_ge'
- \+ *lemma* dense.exists_between

modified src/topology/bases.lean
- \+ *lemma* dense.exists_countable_dense_subset_bot_top
- \+ *lemma* exists_countable_dense_bot_top



## [2021-10-28 04:50:38](https://github.com/leanprover-community/mathlib/commit/468a9d5)
chore(scripts): update nolints.txt ([#10013](https://github.com/leanprover-community/mathlib/pull/10013))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-10-28 04:50:37](https://github.com/leanprover-community/mathlib/commit/bcaeb57)
fix(data/equiv/encodable): turn `unique.encodable` into a `def` ([#10006](https://github.com/leanprover-community/mathlib/pull/10006))
#### Estimated changes
modified src/data/equiv/encodable/basic.lean
- \+ *def* _root_.unique.encodable



## [2021-10-28 02:37:00](https://github.com/leanprover-community/mathlib/commit/9db7270)
chore(*): rename gsmul to zsmul and gmultiples to zmultiples ([#10010](https://github.com/leanprover-community/mathlib/pull/10010))
This is consistent with an earlier rename from `gpow` to `zpow`.
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/algebra/subalgebra.lean
- \+ *theorem* zsmul_mem
- \- *theorem* gsmul_mem

modified src/algebra/big_operators/basic.lean
- \+ *lemma* zsmul_sum
- \- *lemma* gsmul_sum

modified src/algebra/category/Group/Z_Module_equivalence.lean

modified src/algebra/category/Group/basic.lean

modified src/algebra/group/defs.lean
- \+ *def* zsmul_rec
- \- *def* gsmul_rec

modified src/algebra/group/hom_instances.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/type_tags.lean

modified src/algebra/group_power/basic.lean
- \+ *lemma* of_add_zsmul
- \- *lemma* of_add_gsmul

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* sub_zsmul
- \+ *lemma* zsmul_pos
- \+ *lemma* zsmul_strict_mono_right
- \+ *lemma* zsmul_mono_right
- \+ *lemma* abs_zsmul
- \+ *lemma* zsmul_right_injective
- \+ *lemma* zsmul_right_inj
- \+ *lemma* zsmul_eq_zsmul_iff'
- \+ *lemma* zsmul_int_int
- \+ *lemma* zsmul_int_one
- \+ *lemma* zmultiples_hom_apply
- \+ *lemma* zmultiples_hom_symm_apply
- \+ *lemma* zmultiples_add_hom_apply
- \+ *lemma* zmultiples_add_hom_symm_apply
- \- *lemma* sub_gsmul
- \- *lemma* gsmul_pos
- \- *lemma* gsmul_strict_mono_right
- \- *lemma* gsmul_mono_right
- \- *lemma* abs_gsmul
- \- *lemma* gsmul_right_injective
- \- *lemma* gsmul_right_inj
- \- *lemma* gsmul_eq_gsmul_iff'
- \- *lemma* gsmul_int_int
- \- *lemma* gsmul_int_one
- \- *lemma* gmultiples_hom_apply
- \- *lemma* gmultiples_hom_symm_apply
- \- *lemma* gmultiples_add_hom_apply
- \- *lemma* gmultiples_add_hom_symm_apply
- \+ *theorem* zsmul_one
- \+ *theorem* add_one_zsmul
- \+ *theorem* add_zsmul
- \+ *theorem* one_add_zsmul
- \+ *theorem* zsmul_add_comm
- \+ *theorem* zsmul_mul'
- \+ *theorem* mul_zsmul
- \+ *theorem* bit0_zsmul
- \+ *theorem* bit1_zsmul
- \+ *theorem* add_monoid_hom.map_zsmul
- \+ *theorem* zsmul_strict_mono_left
- \+ *theorem* zsmul_mono_left
- \+ *theorem* zsmul_le_zsmul
- \+ *theorem* zsmul_lt_zsmul
- \+ *theorem* zsmul_le_zsmul_iff
- \+ *theorem* zsmul_lt_zsmul_iff
- \+ *theorem* zsmul_le_zsmul'
- \+ *theorem* zsmul_lt_zsmul'
- \+ *theorem* zsmul_le_zsmul_iff'
- \+ *theorem* zsmul_lt_zsmul_iff'
- \+ *theorem* zsmul_eq_mul
- \+ *theorem* zsmul_eq_mul'
- \+ *theorem* mul_zsmul_left
- \+ *theorem* mul_zsmul_assoc
- \- *theorem* gsmul_one
- \- *theorem* add_one_gsmul
- \- *theorem* add_gsmul
- \- *theorem* one_add_gsmul
- \- *theorem* gsmul_add_comm
- \- *theorem* gsmul_mul'
- \- *theorem* mul_gsmul
- \- *theorem* bit0_gsmul
- \- *theorem* bit1_gsmul
- \- *theorem* add_monoid_hom.map_gsmul
- \- *theorem* gsmul_strict_mono_left
- \- *theorem* gsmul_mono_left
- \- *theorem* gsmul_le_gsmul
- \- *theorem* gsmul_lt_gsmul
- \- *theorem* gsmul_le_gsmul_iff
- \- *theorem* gsmul_lt_gsmul_iff
- \- *theorem* gsmul_le_gsmul'
- \- *theorem* gsmul_lt_gsmul'
- \- *theorem* gsmul_le_gsmul_iff'
- \- *theorem* gsmul_lt_gsmul_iff'
- \- *theorem* gsmul_eq_mul
- \- *theorem* gsmul_eq_mul'
- \- *theorem* mul_gsmul_left
- \- *theorem* mul_gsmul_assoc
- \+ *def* zmultiples_hom
- \+ *def* zmultiples_add_hom
- \- *def* gmultiples_hom
- \- *def* gmultiples_add_hom

modified src/algebra/group_power/order.lean

modified src/algebra/homology/additive.lean

modified src/algebra/iterate_hom.lean
- \+ *theorem* iterate_map_zsmul
- \+ *theorem* iterate_map_zsmul
- \- *theorem* iterate_map_gsmul
- \- *theorem* iterate_map_gsmul

modified src/algebra/lie/basic.lean
- \+ *lemma* zsmul_lie
- \+ *lemma* lie_zsmul
- \- *lemma* gsmul_lie
- \- *lemma* lie_gsmul

modified src/algebra/module/basic.lean
- \+ *lemma* zsmul_eq_smul_cast
- \+ *lemma* int_smul_eq_zsmul
- \- *lemma* gsmul_eq_smul_cast
- \- *lemma* int_smul_eq_gsmul

modified src/algebra/module/linear_map.lean

modified src/algebra/order/archimedean.lean

modified src/algebra/periodic.lean
- \+ *lemma* periodic.zsmul
- \+ *lemma* periodic.sub_zsmul_eq
- \+ *lemma* periodic.zsmul_sub_eq
- \+ *lemma* periodic.zsmul_eq
- \- *lemma* periodic.gsmul
- \- *lemma* periodic.sub_gsmul_eq
- \- *lemma* periodic.gsmul_sub_eq
- \- *lemma* periodic.gsmul_eq

modified src/algebra/quaternion.lean

modified src/algebra/ring/ulift.lean

modified src/algebra/star/basic.lean
- \+ *lemma* star_zsmul
- \- *lemma* star_gsmul

modified src/algebra/star/chsh.lean

modified src/analysis/calculus/fderiv_symmetric.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_zsmul_le
- \+ *lemma* nnnorm_zsmul_le
- \- *lemma* norm_gsmul_le
- \- *lemma* nnnorm_gsmul_le

modified src/analysis/special_functions/trigonometric/basic.lean
- \+ *lemma* coe_int_mul_eq_zsmul
- \- *lemma* coe_int_mul_eq_gsmul

modified src/category_theory/linear/default.lean

modified src/category_theory/linear/linear_functor.lean

modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* map_zsmul
- \- *lemma* map_gsmul

modified src/category_theory/preadditive/default.lean
- \+ *lemma* zsmul_comp
- \+ *lemma* comp_zsmul
- \- *lemma* gsmul_comp
- \- *lemma* comp_gsmul

modified src/category_theory/preadditive/functor_category.lean
- \+ *lemma* app_zsmul
- \- *lemma* app_gsmul

modified src/data/complex/basic.lean

modified src/data/dfinsupp.lean

modified src/data/finsupp/basic.lean

modified src/data/holor.lean

modified src/data/int/basic.lean

modified src/data/polynomial/basic.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/real/cau_seq_completion.lean

modified src/data/zmod/basic.lean

modified src/data/zmod/quotient.lean
- \+ *def* quotient_zmultiples_nat_equiv_zmod
- \+ *def* quotient_zmultiples_equiv_zmod
- \- *def* quotient_gmultiples_nat_equiv_zmod
- \- *def* quotient_gmultiples_equiv_zmod

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/field_theory/intermediate_field.lean
- \+ *lemma* zsmul_mem
- \- *lemma* gsmul_mem

modified src/field_theory/subfield.lean
- \+ *lemma* zsmul_mem
- \- *lemma* gsmul_mem

modified src/group_theory/archimedean.lean

modified src/group_theory/free_abelian_group.lean

modified src/group_theory/free_abelian_group_finsupp.lean
- \+ *lemma* support_zsmul
- \- *lemma* support_gsmul

modified src/group_theory/order_of_element.lean
- \+ *lemma* zsmul_eq_mod_add_order_of
- \+ *lemma* exists_zsmul_eq_zero
- \+ *lemma* mem_multiples_iff_mem_zmultiples
- \+ *lemma* multiples_eq_zmultiples
- \+ *lemma* mem_zmultiples_iff_mem_range_add_order_of
- \+ *lemma* fin_equiv_zmultiples_apply
- \+ *lemma* fin_equiv_zmultiples_symm_apply
- \+ *lemma* zmultiples_equiv_zmultiples_apply
- \+ *lemma* add_order_eq_card_zmultiples
- \- *lemma* gsmul_eq_mod_add_order_of
- \- *lemma* exists_gsmul_eq_zero
- \- *lemma* mem_multiples_iff_mem_gmultiples
- \- *lemma* multiples_eq_gmultiples
- \- *lemma* mem_gmultiples_iff_mem_range_add_order_of
- \- *lemma* fin_equiv_gmultiples_apply
- \- *lemma* fin_equiv_gmultiples_symm_apply
- \- *lemma* gmultiples_equiv_gmultiples_apply
- \- *lemma* add_order_eq_card_gmultiples

modified src/group_theory/specific_groups/quaternion.lean

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* coe_zsmul
- \+ *lemma* range_zmultiples_hom
- \+ *lemma* zmultiples_subset
- \+ *lemma* int.mem_zmultiples_iff
- \+ *lemma* of_mul_image_zpowers_eq_zmultiples_of_mul
- \+ *lemma* of_add_image_zmultiples_eq_zpowers_of_add
- \- *lemma* coe_gsmul
- \- *lemma* range_gmultiples_hom
- \- *lemma* gmultiples_subset
- \- *lemma* int.mem_gmultiples_iff
- \- *lemma* of_mul_image_zpowers_eq_gmultiples_of_mul
- \- *lemma* of_add_image_gmultiples_eq_zpowers_of_add
- \+ *def* zmultiples
- \- *def* gmultiples

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/matrix/determinant.lean

modified src/linear_algebra/multilinear/basic.lean

modified src/linear_algebra/quotient.lean

modified src/linear_algebra/tensor_product.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/dioph.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/ring_theory/int/basic.lean
- \+ *lemma* zmultiples_nat_abs
- \- *lemma* gmultiples_nat_abs

modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral.zsmul
- \- *lemma* is_integral.gsmul

modified src/ring_theory/localization.lean

modified src/ring_theory/subring.lean
- \+ *lemma* zsmul_mem
- \- *lemma* gsmul_mem

modified src/set_theory/surreal/dyadic.lean

modified src/tactic/abel.lean
- \+ *theorem* unfold_zsmul
- \- *theorem* unfold_gsmul

modified src/tactic/noncomm_ring.lean

modified src/topology/algebra/module.lean
- \+ *lemma* continuous_zsmul
- \+ *lemma* continuous.zsmul
- \- *lemma* continuous_gsmul
- \- *lemma* continuous.gsmul



## [2021-10-27 20:21:14](https://github.com/leanprover-community/mathlib/commit/d360f3c)
feat(linear_algebra/free_module/finite/rank): add linear_algebra/free_module/finite/rank ([#9832](https://github.com/leanprover-community/mathlib/pull/9832))
A basic API for rank of free modules.
- [x] depends on: [#9821](https://github.com/leanprover-community/mathlib/pull/9821)
#### Estimated changes
modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_self
- \+/\- *lemma* dim_self

modified src/linear_algebra/finite_dimensional.lean

created src/linear_algebra/free_module/finite/rank.lean
- \+ *lemma* rank_lt_omega
- \+ *lemma* finrank_eq_rank
- \+ *lemma* finrank_eq_card_choose_basis_index
- \+ *lemma* finrank_finsupp
- \+ *lemma* finrank_pi
- \+ *lemma* finrank_direct_sum
- \+ *lemma* finrank_prod
- \+ *lemma* finrank_pi_fintype
- \+ *lemma* finrank_matrix
- \+ *lemma* finrank_linear_hom
- \+ *lemma* finrank_tensor_product

modified src/linear_algebra/free_module/rank.lean
- \+/\- *lemma* rank_direct_sum
- \+ *lemma* rank_pi_fintype
- \+ *lemma* rank_matrix
- \+ *lemma* rank_matrix'
- \+ *lemma* rank_matrix''
- \+/\- *lemma* rank_direct_sum

modified src/set_theory/cardinal.lean
- \+/\- *lemma* to_nat_mul
- \+ *lemma* to_nat_add_of_lt_omega
- \+/\- *lemma* to_nat_mul



## [2021-10-27 17:47:32](https://github.com/leanprover-community/mathlib/commit/8ce5da4)
feat(algebra/order/archimedean): a few more lemmas ([#9997](https://github.com/leanprover-community/mathlib/pull/9997))
Prove that `a + m • b ∈ Ioc c (c + b)` for some `m : ℤ`, and similarly for `Ico`.
Also move some lemmas out of a namespace.
#### Estimated changes
modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_add_int_smul_mem_Ico
- \+ *lemma* exists_add_int_smul_mem_Ioc

modified src/algebra/periodic.lean
- \+ *lemma* periodic.exists_mem_Ico₀
- \+/\- *lemma* periodic.exists_mem_Ico
- \+ *lemma* periodic.exists_mem_Ioc
- \+/\- *lemma* periodic.exists_mem_Ico

modified src/topology/instances/real.lean



## [2021-10-27 17:47:31](https://github.com/leanprover-community/mathlib/commit/ec51fb7)
chore(algebra/order/floor): prove `subsingleton`s ([#9996](https://github.com/leanprover-community/mathlib/pull/9996))
#### Estimated changes
modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean

modified src/algebra/order/floor.lean
- \+ *lemma* subsingleton_floor_semiring
- \+ *lemma* subsingleton_floor_ring
- \- *lemma* floor_semiring_unique
- \- *lemma* floor_ring_unique



## [2021-10-27 17:47:29](https://github.com/leanprover-community/mathlib/commit/eaec1da)
feat(group_theory/group_action/conj_act): A characteristic subgroup of a normal subgroup is normal ([#9992](https://github.com/leanprover-community/mathlib/pull/9992))
Uses `mul_aut.conj_normal` to prove an instance stating that a characteristic subgroup of a normal subgroup is normal.
#### Estimated changes
modified src/group_theory/group_action/conj_act.lean



## [2021-10-27 17:47:27](https://github.com/leanprover-community/mathlib/commit/c529711)
refactor(*): rename fpow and gpow to zpow ([#9989](https://github.com/leanprover-community/mathlib/pull/9989))
Historically, we had two notions of integer power, one on groups called `gpow` and the other one on fields called `fpow`. Since the introduction of `div_inv_monoid` and `group_with_zero`, these definitions have been merged into one, and the boundaries are not clear any more. We rename both of them to `zpow`, adding a subscript `0` to disambiguate lemma names when there is a collision, where the subscripted version is for groups with zeroes (as is already done for inv lemmas).
To limit the scope of the change. this PR does not rename `gsmul` to `zsmul` or `gmultiples` to `zmultiples`.
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* ring_hom.map_zpow
- \+ *lemma* ring_equiv.map_zpow
- \+ *lemma* zpow_bit0_neg
- \+ *lemma* even.zpow_neg
- \+ *lemma* zpow_bit1_neg
- \+ *lemma* zpow_eq_zero_iff
- \+ *lemma* zpow_nonneg
- \+ *lemma* zpow_pos_of_pos
- \+ *lemma* zpow_le_of_le
- \+ *lemma* zpow_le_one_of_nonpos
- \+ *lemma* one_le_zpow_of_nonneg
- \+ *lemma* even.zpow_nonneg
- \+ *lemma* even.zpow_abs
- \+ *lemma* zpow_bit0_abs
- \+ *lemma* even.abs_zpow
- \+ *lemma* abs_zpow_bit0
- \+ *lemma* one_lt_zpow
- \+ *lemma* nat.zpow_pos_of_pos
- \+ *lemma* nat.zpow_ne_zero_of_pos
- \+ *lemma* zpow_strict_mono
- \+ *lemma* zpow_lt_iff_lt
- \+ *lemma* zpow_le_iff_le
- \+ *lemma* zpow_injective
- \+ *lemma* zpow_inj
- \- *lemma* ring_hom.map_fpow
- \- *lemma* ring_equiv.map_fpow
- \- *lemma* fpow_bit0_neg
- \- *lemma* even.fpow_neg
- \- *lemma* fpow_bit1_neg
- \- *lemma* fpow_eq_zero_iff
- \- *lemma* fpow_nonneg
- \- *lemma* fpow_pos_of_pos
- \- *lemma* fpow_le_of_le
- \- *lemma* fpow_le_one_of_nonpos
- \- *lemma* one_le_fpow_of_nonneg
- \- *lemma* even.fpow_nonneg
- \- *lemma* even.fpow_abs
- \- *lemma* fpow_bit0_abs
- \- *lemma* even.abs_fpow
- \- *lemma* abs_fpow_bit0
- \- *lemma* one_lt_fpow
- \- *lemma* nat.fpow_pos_of_pos
- \- *lemma* nat.fpow_ne_zero_of_pos
- \- *lemma* fpow_strict_mono
- \- *lemma* fpow_lt_iff_lt
- \- *lemma* fpow_le_iff_le
- \- *lemma* fpow_injective
- \- *lemma* fpow_inj
- \+ *theorem* zpow_bit0_nonneg
- \+ *theorem* zpow_two_nonneg
- \+ *theorem* zpow_bit0_pos
- \+ *theorem* zpow_two_pos_of_ne_zero
- \+ *theorem* zpow_bit1_neg_iff
- \+ *theorem* zpow_bit1_nonneg_iff
- \+ *theorem* zpow_bit1_nonpos_iff
- \+ *theorem* zpow_bit1_pos_iff
- \+ *theorem* even.zpow_pos
- \+ *theorem* odd.zpow_nonneg
- \+ *theorem* odd.zpow_pos
- \+ *theorem* odd.zpow_nonpos
- \+ *theorem* odd.zpow_neg
- \+ *theorem* rat.cast_zpow
- \- *theorem* fpow_bit0_nonneg
- \- *theorem* fpow_two_nonneg
- \- *theorem* fpow_bit0_pos
- \- *theorem* fpow_two_pos_of_ne_zero
- \- *theorem* fpow_bit1_neg_iff
- \- *theorem* fpow_bit1_nonneg_iff
- \- *theorem* fpow_bit1_nonpos_iff
- \- *theorem* fpow_bit1_pos_iff
- \- *theorem* even.fpow_pos
- \- *theorem* odd.fpow_nonneg
- \- *theorem* odd.fpow_pos
- \- *theorem* odd.fpow_nonpos
- \- *theorem* odd.fpow_neg
- \- *theorem* rat.cast_fpow

modified src/algebra/group/conj.lean
- \+ *lemma* conj_zpow
- \- *lemma* conj_gpow

modified src/algebra/group/defs.lean
- \+ *def* zpow_rec
- \- *def* gpow_rec

modified src/algebra/group/hom_instances.lean

modified src/algebra/group/pi.lean

modified src/algebra/group/prod.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/type_tags.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group_power/basic.lean
- \+ *lemma* zpow_eq_pow
- \+ *lemma* mul_zpow_neg_one
- \+ *lemma* of_mul_zpow
- \+ *lemma* semiconj_by.zpow_right
- \+ *lemma* zpow_right
- \+ *lemma* zpow_left
- \+ *lemma* zpow_zpow
- \- *lemma* gpow_eq_pow
- \- *lemma* mul_gpow_neg_one
- \- *lemma* of_mul_gpow
- \- *lemma* semiconj_by.gpow_right
- \- *lemma* gpow_right
- \- *lemma* gpow_left
- \- *lemma* gpow_gpow
- \+ *theorem* zpow_coe_nat
- \+ *theorem* zpow_of_nat
- \+ *theorem* zpow_neg_succ_of_nat
- \+ *theorem* zpow_zero
- \+ *theorem* zpow_one
- \+ *theorem* one_zpow
- \+ *theorem* zpow_neg
- \+ *theorem* zpow_neg_one
- \+ *theorem* inv_zpow
- \+ *theorem* commute.mul_zpow
- \+ *theorem* mul_zpow
- \+ *theorem* div_zpow
- \+ *theorem* self_zpow
- \+ *theorem* zpow_self
- \+ *theorem* zpow_zpow_self
- \- *theorem* gpow_coe_nat
- \- *theorem* gpow_of_nat
- \- *theorem* gpow_neg_succ_of_nat
- \- *theorem* gpow_zero
- \- *theorem* gpow_one
- \- *theorem* one_gpow
- \- *theorem* gpow_neg
- \- *theorem* gpow_neg_one
- \- *theorem* inv_gpow
- \- *theorem* commute.mul_gpow
- \- *theorem* mul_gpow
- \- *theorem* div_gpow
- \- *theorem* self_gpow
- \- *theorem* gpow_self
- \- *theorem* gpow_gpow_self
- \+ *def* zpow_group_hom
- \- *def* gpow_group_hom

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* zpow_add_one
- \+ *lemma* zpow_sub_one
- \+ *lemma* zpow_add
- \+ *lemma* mul_self_zpow
- \+ *lemma* mul_zpow_self
- \+ *lemma* zpow_sub
- \+ *lemma* units.coe_zpow
- \+ *lemma* zpowers_hom_apply
- \+ *lemma* zpowers_hom_symm_apply
- \+ *lemma* zpowers_mul_hom_apply
- \+ *lemma* zpowers_mul_hom_symm_apply
- \+ *lemma* units_zpow_right
- \+ *lemma* units_zpow_right
- \+ *lemma* units_zpow_left
- \+ *lemma* int.to_add_zpow
- \+ *lemma* op_zpow
- \+ *lemma* unop_zpow
- \- *lemma* gpow_add_one
- \- *lemma* gpow_sub_one
- \- *lemma* gpow_add
- \- *lemma* mul_self_gpow
- \- *lemma* mul_gpow_self
- \- *lemma* gpow_sub
- \- *lemma* units.coe_gpow
- \- *lemma* gpowers_hom_apply
- \- *lemma* gpowers_hom_symm_apply
- \- *lemma* gpowers_mul_hom_apply
- \- *lemma* gpowers_mul_hom_symm_apply
- \- *lemma* units_gpow_right
- \- *lemma* units_gpow_right
- \- *lemma* units_gpow_left
- \- *lemma* int.to_add_gpow
- \- *lemma* op_gpow
- \- *lemma* unop_gpow
- \+ *theorem* zpow_one_add
- \+ *theorem* zpow_mul_comm
- \+ *theorem* zpow_mul
- \+ *theorem* zpow_mul'
- \+ *theorem* zpow_bit0
- \+ *theorem* zpow_bit1
- \+ *theorem* monoid_hom.map_zpow
- \- *theorem* gpow_one_add
- \- *theorem* gpow_mul_comm
- \- *theorem* gpow_mul
- \- *theorem* gpow_mul'
- \- *theorem* gpow_bit0
- \- *theorem* gpow_bit1
- \- *theorem* monoid_hom.map_gpow
- \+ *def* zpowers_hom
- \+ *def* zpowers_mul_hom
- \- *def* gpowers_hom
- \- *def* gpowers_mul_hom

modified src/algebra/group_power/order.lean
- \+ *theorem* one_le_zpow
- \- *theorem* one_le_gpow

modified src/algebra/group_with_zero/power.lean
- \+ *lemma* zero_zpow
- \+ *lemma* zpow_add_one₀
- \+ *lemma* zpow_sub_one₀
- \+ *lemma* zpow_add₀
- \+ *lemma* zpow_add'
- \+ *lemma* units.coe_zpow₀
- \+ *lemma* zpow_ne_zero_of_ne_zero
- \+ *lemma* zpow_sub₀
- \+ *lemma* commute.mul_zpow₀
- \+ *lemma* mul_zpow₀
- \+ *lemma* zpow_eq_zero
- \+ *lemma* zpow_ne_zero
- \+ *lemma* inv_zpow'
- \+ *lemma* monoid_with_zero_hom.map_zpow
- \- *lemma* zero_fpow
- \- *lemma* fpow_add_one
- \- *lemma* fpow_sub_one
- \- *lemma* fpow_add
- \- *lemma* fpow_add'
- \- *lemma* units.coe_gpow₀
- \- *lemma* fpow_ne_zero_of_ne_zero
- \- *lemma* fpow_sub
- \- *lemma* commute.mul_fpow
- \- *lemma* mul_fpow
- \- *lemma* fpow_eq_zero
- \- *lemma* fpow_ne_zero
- \- *lemma* inv_fpow'
- \- *lemma* monoid_with_zero_hom.map_fpow
- \+ *theorem* one_zpow₀
- \+ *theorem* zpow_neg₀
- \+ *theorem* zpow_neg_one₀
- \+ *theorem* inv_zpow₀
- \+ *theorem* zpow_one_add₀
- \+ *theorem* semiconj_by.zpow_right₀
- \+ *theorem* commute.zpow_right₀
- \+ *theorem* commute.zpow_left₀
- \+ *theorem* commute.zpow_zpow₀
- \+ *theorem* commute.zpow_self₀
- \+ *theorem* commute.self_zpow₀
- \+ *theorem* commute.zpow_zpow_self₀
- \+ *theorem* zpow_bit0₀
- \+ *theorem* zpow_bit1₀
- \+ *theorem* zpow_mul₀
- \+ *theorem* zpow_mul₀'
- \+ *theorem* zpow_bit0'
- \+ *theorem* zpow_bit1'
- \+ *theorem* zpow_neg_mul_zpow_self
- \+ *theorem* one_div_zpow
- \+ *theorem* div_zpow₀
- \- *theorem* one_fpow
- \- *theorem* fpow_neg
- \- *theorem* fpow_neg_one
- \- *theorem* inv_fpow
- \- *theorem* fpow_one_add
- \- *theorem* semiconj_by.fpow_right
- \- *theorem* commute.fpow_right
- \- *theorem* commute.fpow_left
- \- *theorem* commute.fpow_fpow
- \- *theorem* commute.fpow_self
- \- *theorem* commute.self_fpow
- \- *theorem* commute.fpow_fpow_self
- \- *theorem* fpow_bit0
- \- *theorem* fpow_bit1
- \- *theorem* fpow_mul
- \- *theorem* fpow_mul'
- \- *theorem* fpow_bit0'
- \- *theorem* fpow_bit1'
- \- *theorem* fpow_neg_mul_fpow_self
- \- *theorem* one_div_fpow
- \- *theorem* div_fpow

modified src/algebra/iterate_hom.lean
- \+ *theorem* iterate_map_zpow
- \- *theorem* iterate_map_gpow

modified src/algebra/opposites.lean

modified src/algebra/order/archimedean.lean

modified src/algebra/punit_instances.lean

modified src/algebra/star/basic.lean
- \+ *lemma* star_zpow
- \+ *lemma* star_zpow₀
- \- *lemma* star_gpow
- \- *lemma* star_fpow

modified src/analysis/asymptotics/specific_asymptotics.lean
- \+ *lemma* tendsto_zpow_at_top_at_top
- \- *lemma* tendsto_fpow_at_top_at_top

modified src/analysis/asymptotics/superpolynomial_decay.lean
- \+ *lemma* superpolynomial_decay_of_is_O_zpow_le
- \+ *lemma* superpolynomial_decay_of_is_O_zpow_lt
- \- *lemma* superpolynomial_decay_of_is_O_fpow_le
- \- *lemma* superpolynomial_decay_of_is_O_fpow_lt

modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_strict_deriv_at_zpow
- \+ *lemma* has_deriv_at_zpow
- \+ *lemma* differentiable_at_zpow
- \+ *lemma* differentiable_within_at_zpow
- \+ *lemma* differentiable_on_zpow
- \+ *lemma* deriv_zpow
- \+ *lemma* deriv_zpow'
- \+ *lemma* deriv_within_zpow
- \+ *lemma* iter_deriv_zpow'
- \+ *lemma* iter_deriv_zpow
- \- *lemma* has_strict_deriv_at_fpow
- \- *lemma* has_deriv_at_fpow
- \- *lemma* differentiable_at_fpow
- \- *lemma* differentiable_within_at_fpow
- \- *lemma* differentiable_on_fpow
- \- *lemma* deriv_fpow
- \- *lemma* deriv_fpow'
- \- *lemma* deriv_within_fpow
- \- *lemma* iter_deriv_fpow'
- \- *lemma* iter_deriv_fpow
- \+ *theorem* has_deriv_within_at_zpow
- \- *theorem* has_deriv_within_at_fpow

modified src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_zpow
- \- *lemma* convex_on_fpow

modified src/analysis/fourier.lean

modified src/analysis/mean_inequalities.lean
- \+ *theorem* zpow_arith_mean_le_arith_mean_zpow
- \- *theorem* fpow_arith_mean_le_arith_mean_fpow

modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_zpow
- \+ *lemma* nnnorm_zpow
- \- *lemma* norm_fpow
- \- *lemma* nnnorm_fpow

modified src/analysis/special_functions/exp.lean

modified src/analysis/special_functions/polynomials.lean

modified src/analysis/special_functions/pow.lean

modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_norm_zpow_nhds_within_0_at_top
- \+ *lemma* continuous_at_zpow
- \- *lemma* tendsto_norm_fpow_nhds_within_0_at_top
- \- *lemma* continuous_at_fpow

modified src/category_theory/conj.lean
- \+ *lemma* conj_Aut_zpow
- \- *lemma* conj_Aut_gpow

modified src/category_theory/endomorphism.lean

modified src/data/complex/basic.lean
- \+ *lemma* I_zpow_bit0
- \+ *lemma* I_zpow_bit1
- \+ *lemma* of_real_zpow
- \- *lemma* I_fpow_bit0
- \- *lemma* I_fpow_bit1
- \- *lemma* of_real_fpow

modified src/data/complex/is_R_or_C.lean
- \+ *lemma* of_real_zpow
- \- *lemma* of_real_fpow

modified src/data/equiv/mul_add_aut.lean

modified src/data/equiv/ring_aut.lean

modified src/data/int/gcd.lean

modified src/data/real/irrational.lean
- \+ *theorem* of_zpow
- \- *theorem* of_fpow

modified src/deprecated/subfield.lean

modified src/dynamics/circle/rotation_number/translation_number.lean
- \+ *lemma* translate_zpow
- \+ *lemma* translation_number_zpow
- \- *lemma* translate_gpow
- \- *lemma* translation_number_gpow

modified src/field_theory/finite/basic.lean

modified src/field_theory/intermediate_field.lean

modified src/group_theory/free_group.lean

modified src/group_theory/group_action/group.lean
- \+ *lemma* smul_zpow
- \- *lemma* smul_gpow

modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_dvd_iff_zpow_eq_one
- \+ *lemma* zpow_eq_mod_order_of
- \+/\- *lemma* exists_zpow_eq_one
- \+ *lemma* mem_powers_iff_mem_zpowers
- \+ *lemma* powers_eq_zpowers
- \+ *lemma* mem_zpowers_iff_mem_range_order_of
- \+ *lemma* fin_equiv_zpowers_apply
- \+ *lemma* fin_equiv_zpowers_symm_apply
- \+ *lemma* zpowers_equiv_zpowers_apply
- \+ *lemma* order_eq_card_zpowers
- \+ *lemma* zpow_eq_mod_card
- \- *lemma* order_of_dvd_iff_gpow_eq_one
- \- *lemma* gpow_eq_mod_order_of
- \- *lemma* exists_gpow_eq_one
- \- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_zpow_eq_one
- \- *lemma* mem_powers_iff_mem_gpowers
- \- *lemma* powers_eq_gpowers
- \- *lemma* mem_gpowers_iff_mem_range_order_of
- \- *lemma* fin_equiv_gpowers_apply
- \- *lemma* fin_equiv_gpowers_symm_apply
- \- *lemma* gpowers_equiv_gpowers_apply
- \- *lemma* order_eq_card_gpowers
- \- *lemma* gpow_eq_mod_card

modified src/group_theory/perm/basic.lean
- \+ *lemma* zpow_apply_comm
- \- *lemma* gpow_apply_comm

modified src/group_theory/perm/concrete_cycle.lean

modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle.exists_zpow_eq
- \+ *lemma* is_cycle.zpowers_equiv_support_apply
- \+ *lemma* is_cycle.zpowers_equiv_support_symm_apply
- \+ *lemma* is_cycle_of_is_cycle_zpow
- \+ *lemma* same_cycle_zpow_left_iff
- \+ *lemma* cycle_of_zpow_apply_self
- \+ *lemma* cycle_of_apply_apply_zpow_self
- \+ *lemma* cycle_of_self_apply_zpow
- \- *lemma* is_cycle.exists_gpow_eq
- \- *lemma* is_cycle.gpowers_equiv_support_apply
- \- *lemma* is_cycle.gpowers_equiv_support_symm_apply
- \- *lemma* is_cycle_of_is_cycle_gpow
- \- *lemma* same_cycle_gpow_left_iff
- \- *lemma* cycle_of_gpow_apply_self
- \- *lemma* cycle_of_apply_apply_gpow_self
- \- *lemma* cycle_of_self_apply_gpow

modified src/group_theory/perm/fin.lean

modified src/group_theory/perm/list.lean
- \+ *lemma* form_perm_zpow_apply_mem_imp_mem
- \- *lemma* form_perm_gpow_apply_mem_imp_mem

modified src/group_theory/perm/support.lean
- \+ *lemma* zpow_apply_eq_self_of_apply_eq_self
- \+ *lemma* zpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* disjoint.zpow_disjoint_zpow
- \+ *lemma* set_support_zpow_subset
- \+ *lemma* zpow_apply_mem_support
- \+ *lemma* support_zpow_le
- \- *lemma* gpow_apply_eq_self_of_apply_eq_self
- \- *lemma* gpow_apply_eq_of_apply_apply_eq_self
- \- *lemma* disjoint.gpow_disjoint_gpow
- \- *lemma* set_support_gpow_subset
- \- *lemma* gpow_apply_mem_support
- \- *lemma* support_gpow_le

modified src/group_theory/quotient_group.lean
- \+ *lemma* coe_zpow
- \- *lemma* coe_gpow

modified src/group_theory/specific_groups/cyclic.lean
- \+ *lemma* order_of_eq_card_of_forall_mem_zpowers
- \+/\- *lemma* is_cyclic.image_range_order_of
- \+/\- *lemma* is_cyclic.image_range_card
- \- *lemma* order_of_eq_card_of_forall_mem_gpowers
- \+/\- *lemma* is_cyclic.image_range_order_of
- \+/\- *lemma* is_cyclic.image_range_card

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* zpow_mem
- \+ *lemma* coe_zpow
- \+ *lemma* mem_zpowers
- \+ *lemma* zpowers_eq_closure
- \+ *lemma* range_zpowers_hom
- \+ *lemma* zpowers_subset
- \+ *lemma* mem_zpowers_iff
- \+ *lemma* forall_zpowers
- \+ *lemma* exists_zpowers
- \+ *lemma* forall_mem_zpowers
- \+ *lemma* exists_mem_zpowers
- \+ *lemma* of_mul_image_zpowers_eq_gmultiples_of_mul
- \+ *lemma* of_add_image_gmultiples_eq_zpowers_of_add
- \+ *lemma* saturated_iff_zpow
- \- *lemma* gpow_mem
- \- *lemma* coe_gpow
- \- *lemma* mem_gpowers
- \- *lemma* gpowers_eq_closure
- \- *lemma* range_gpowers_hom
- \- *lemma* gpowers_subset
- \- *lemma* mem_gpowers_iff
- \- *lemma* forall_gpowers
- \- *lemma* exists_gpowers
- \- *lemma* forall_mem_gpowers
- \- *lemma* exists_mem_gpowers
- \- *lemma* of_mul_image_gpowers_eq_gmultiples_of_mul
- \- *lemma* of_add_image_gmultiples_eq_gpowers_of_add
- \- *lemma* saturated_iff_gpow
- \+ *def* zpowers
- \- *def* gpowers

modified src/group_theory/sylow.lean

renamed src/linear_algebra/matrix/fpow.lean to src/linear_algebra/matrix/zpow.lean
- \+ *lemma* zero_zpow
- \+ *lemma* zero_zpow_eq
- \+ *lemma* zpow_neg_one
- \+ *lemma* _root_.is_unit.det_zpow
- \+ *lemma* is_unit_det_zpow_iff
- \+ *lemma* inv_zpow'
- \+ *lemma* zpow_add_one
- \+ *lemma* zpow_sub_one
- \+ *lemma* zpow_add
- \+ *lemma* zpow_add_of_nonpos
- \+ *lemma* zpow_add_of_nonneg
- \+ *lemma* zpow_add_one_of_ne_neg_one
- \+ *lemma* units.coe_zpow
- \+ *lemma* zpow_ne_zero_of_is_unit_det
- \+ *lemma* zpow_sub
- \+ *lemma* commute.mul_zpow
- \- *lemma* zero_fpow
- \- *lemma* zero_fpow_eq
- \- *lemma* fpow_neg_one
- \- *lemma* _root_.is_unit.det_fpow
- \- *lemma* is_unit_det_fpow_iff
- \- *lemma* inv_fpow'
- \- *lemma* fpow_add_one
- \- *lemma* fpow_sub_one
- \- *lemma* fpow_add
- \- *lemma* fpow_add_of_nonpos
- \- *lemma* fpow_add_of_nonneg
- \- *lemma* fpow_add_one_of_ne_neg_one
- \- *lemma* units.coe_fpow
- \- *lemma* fpow_ne_zero_of_is_unit_det
- \- *lemma* fpow_sub
- \- *lemma* commute.mul_fpow
- \+ *theorem* one_zpow
- \+ *theorem* inv_zpow
- \+ *theorem* zpow_coe_nat
- \+ *theorem* zpow_neg_coe_nat
- \+ *theorem* zpow_neg
- \+ *theorem* zpow_one_add
- \+ *theorem* semiconj_by.zpow_right
- \+ *theorem* commute.zpow_right
- \+ *theorem* commute.zpow_left
- \+ *theorem* commute.zpow_zpow
- \+ *theorem* commute.zpow_self
- \+ *theorem* commute.self_zpow
- \+ *theorem* commute.zpow_zpow_self
- \+ *theorem* zpow_bit0
- \+ *theorem* zpow_bit1
- \+ *theorem* zpow_mul
- \+ *theorem* zpow_mul'
- \+ *theorem* zpow_bit0'
- \+ *theorem* zpow_bit1'
- \+ *theorem* zpow_neg_mul_zpow_self
- \+ *theorem* one_div_zpow
- \- *theorem* one_fpow
- \- *theorem* inv_fpow
- \- *theorem* fpow_coe_nat
- \- *theorem* fpow_neg_coe_nat
- \- *theorem* fpow_neg
- \- *theorem* fpow_one_add
- \- *theorem* semiconj_by.fpow_right
- \- *theorem* commute.fpow_right
- \- *theorem* commute.fpow_left
- \- *theorem* commute.fpow_fpow
- \- *theorem* commute.fpow_self
- \- *theorem* commute.self_fpow
- \- *theorem* commute.fpow_fpow_self
- \- *theorem* fpow_bit0
- \- *theorem* fpow_bit1
- \- *theorem* fpow_mul
- \- *theorem* fpow_mul'
- \- *theorem* fpow_bit0'
- \- *theorem* fpow_bit1'
- \- *theorem* fpow_neg_mul_fpow_self
- \- *theorem* one_div_fpow

modified src/measure_theory/group/arithmetic.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/padic_norm.lean

modified src/number_theory/padics/padic_numbers.lean

modified src/number_theory/padics/ring_homs.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* zpow_eq_one
- \+ *lemma* zpow_eq_one_iff_dvd
- \+ *lemma* zpow_of_gcd_eq_one
- \+ *lemma* zpow_eq_one₀
- \+ *lemma* zpow_eq_one_iff_dvd₀
- \+ *lemma* zpow_of_gcd_eq_one₀
- \+ *lemma* zmod_equiv_zpowers_apply_coe_int
- \+ *lemma* zmod_equiv_zpowers_apply_coe_nat
- \+ *lemma* zmod_equiv_zpowers_symm_apply_zpow
- \+ *lemma* zmod_equiv_zpowers_symm_apply_zpow'
- \+ *lemma* zmod_equiv_zpowers_symm_apply_pow
- \+ *lemma* zmod_equiv_zpowers_symm_apply_pow'
- \+ *lemma* zpowers_eq
- \- *lemma* gpow_eq_one
- \- *lemma* gpow_eq_one_iff_dvd
- \- *lemma* gpow_of_gcd_eq_one
- \- *lemma* fpow_eq_one
- \- *lemma* fpow_eq_one_iff_dvd
- \- *lemma* fpow_of_gcd_eq_one
- \- *lemma* zmod_equiv_gpowers_apply_coe_int
- \- *lemma* zmod_equiv_gpowers_apply_coe_nat
- \- *lemma* zmod_equiv_gpowers_symm_apply_gpow
- \- *lemma* zmod_equiv_gpowers_symm_apply_gpow'
- \- *lemma* zmod_equiv_gpowers_symm_apply_pow
- \- *lemma* zmod_equiv_gpowers_symm_apply_pow'
- \- *lemma* gpowers_eq
- \+ *def* zmod_equiv_zpowers
- \- *def* zmod_equiv_gpowers

modified src/tactic/group.lean
- \+ *lemma* tactic.group.zpow_trick
- \+ *lemma* tactic.group.zpow_trick_one
- \+ *lemma* tactic.group.zpow_trick_one'
- \+ *lemma* tactic.group.zpow_trick_sub
- \- *lemma* tactic.group.gpow_trick
- \- *lemma* tactic.group.gpow_trick_one
- \- *lemma* tactic.group.gpow_trick_one'
- \- *lemma* tactic.group.gpow_trick_sub

modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous_at_zpow
- \+ *lemma* continuous_on_zpow
- \+ *lemma* filter.tendsto.zpow
- \+ *lemma* continuous_at.zpow
- \+ *lemma* continuous_within_at.zpow
- \+ *lemma* continuous_on.zpow
- \+ *lemma* continuous.zpow
- \- *lemma* continuous_at_fpow
- \- *lemma* continuous_on_fpow
- \- *lemma* filter.tendsto.fpow
- \- *lemma* continuous_at.fpow
- \- *lemma* continuous_within_at.fpow
- \- *lemma* continuous_on.fpow
- \- *lemma* continuous.fpow

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* tendsto_zpow_at_top_zero
- \+ *lemma* tendsto_const_mul_zpow_at_top_zero
- \+ *lemma* tendsto_const_mul_zpow_at_top_zero_iff
- \- *lemma* tendsto_fpow_at_top_zero
- \- *lemma* tendsto_const_mul_fpow_at_top_zero
- \- *lemma* tendsto_const_mul_fpow_at_top_zero_iff

modified test/refine_struct.lean



## [2021-10-27 17:47:26](https://github.com/leanprover-community/mathlib/commit/9e4609b)
chore(data/fintype/card): add `fin.prod_univ_{one,two}` ([#9987](https://github.com/leanprover-community/mathlib/pull/9987))
Sometimes Lean fails to simplify `(default : fin 1)` to `0` and
`0.succ` to `1` in complex expressions. These lemmas explicitly use
`f 0` and `f 1` in the output.
#### Estimated changes
modified src/data/fintype/card.lean
- \+ *theorem* fin.prod_univ_one
- \+ *theorem* fin.prod_univ_two



## [2021-10-27 17:47:25](https://github.com/leanprover-community/mathlib/commit/29079ba)
feat(tactic/lint): linter improvements ([#9901](https://github.com/leanprover-community/mathlib/pull/9901))
* Make the linter framework easier to use on projects outside mathlib with the new `lint_project` (replacing `lint_mathlib`). Also replace `lint_mathlib_decls` by `lint_project_decls`.
* Make most declarations in the frontend not-private (I want to use them in other projects)
* The unused argument linter does not report declarations that contain `sorry`. It will still report declarations that use other declarations that contain sorry. I did not add a test for this, since it's hard to do that while keeping the test suite silent (but I did test locally).
* Some minor changes in the test suite (not important, but they cannot hurt).
#### Estimated changes
modified scripts/lint_mathlib.lean

modified src/tactic/core.lean

modified src/tactic/lint/frontend.lean

modified src/tactic/lint/misc.lean

created src/tactic/project_dir.lean
- \+ *lemma* mathlib_dir_locator

modified test/lint.lean



## [2021-10-27 15:13:53](https://github.com/leanprover-community/mathlib/commit/25718c2)
feat(data/nat/basic): Add two lemmas two nat/basic which are necessary for the count PR ([#10001](https://github.com/leanprover-community/mathlib/pull/10001))
Add two lemmas proved by refl to data/nat/basic. They are needed for the count PR, and are changing a file low enogh in the import hierarchy to be a separate PR.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* nat.subtype.coe_bot
- \+ *lemma* sub_succ'



## [2021-10-27 15:13:51](https://github.com/leanprover-community/mathlib/commit/4e29dc7)
chore(topology/algebra/module): add `continuous_linear_equiv.arrow_congr_equiv` ([#9982](https://github.com/leanprover-community/mathlib/pull/9982))
#### Estimated changes
modified src/topology/algebra/module.lean
- \+ *def* arrow_congr_equiv



## [2021-10-27 15:13:50](https://github.com/leanprover-community/mathlib/commit/a3f4a02)
chore(analysis/normed_space/is_R_or_C + data/complex/is_R_or_C): make some proof steps standalone lemmas ([#9933](https://github.com/leanprover-community/mathlib/pull/9933))
Separate some proof steps from `linear_map.bound_of_sphere_bound` as standalone lemmas to golf them a little bit.
#### Estimated changes
modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_coe_norm

modified src/data/complex/is_R_or_C.lean
- \+ *lemma* norm_of_nonneg



## [2021-10-27 15:13:49](https://github.com/leanprover-community/mathlib/commit/d7c689d)
feat(algebraic_geometry/prime_spectrum): Closed points in prime spectrum ([#9861](https://github.com/leanprover-community/mathlib/pull/9861))
This PR adds lemmas about the correspondence between closed points in `prime_spectrum R` and maximal ideals of `R`.
In order to import and talk about integral maps I had to move some lemmas from `noetherian.lean` to `prime_spectrum.lean` to prevent cyclic import dependencies.
#### Estimated changes
renamed src/algebraic_geometry/prime_spectrum.lean to src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* is_closed_singleton_iff_is_maximal
- \+ *lemma* t1_space_iff_is_field
- \+ *lemma* comap_injective_of_surjective
- \+ *lemma* comap_singleton_is_closed_of_surjective
- \+ *lemma* comap_singleton_is_closed_of_is_integral

renamed src/algebraic_geometry/is_open_comap_C.lean to src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean

created src/algebraic_geometry/prime_spectrum/noetherian.lean
- \+ *lemma* exists_prime_spectrum_prod_le
- \+ *lemma* exists_prime_spectrum_prod_le_and_ne_bot_of_domain

modified src/algebraic_geometry/structure_sheaf.lean

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/noetherian.lean
- \- *lemma* exists_prime_spectrum_prod_le
- \- *lemma* exists_prime_spectrum_prod_le_and_ne_bot_of_domain

modified src/ring_theory/nullstellensatz.lean



## [2021-10-27 07:01:26](https://github.com/leanprover-community/mathlib/commit/d9cea39)
refactor(topology+algebraic_geometry): prove and make use of equalities to simplify definitions ([#9972](https://github.com/leanprover-community/mathlib/pull/9972))
Prove and make use of equalities whenever possible, even between functors (which is discouraged according to certain philosophy), to replace isomorphisms by equalities, to remove the need of transporting across isomorphisms in various definitions (using `eq_to_hom` directly), most notably: [simplified definition of identity morphism for PresheafedSpace](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR89), [simplified extensionality lemma for morphisms](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR68), [simplified definition of composition](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR96) and [the global section functor](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR228) (takes advantage of defeq and doesn't require proving any new equality).
Other small changes to mathlib:
- Define pushforward functor of presheaves in topology/sheaves/presheaf.lean
- Add new file functor.lean in topology/sheaves, proves the pushforward of a sheaf is a sheaf, and defines the pushforward functor of sheaves, with the expectation that pullbacks will be added later.
- Make one of the arguments in various `restrict`s implicit.
- Change statement of [`to_open_comp_comap`](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-54364470f443f847742b1c105e853afebc25da68faad63cc5a73db167bc85d06R973) in structure_sheaf.lean to be more general (the same proof works!)
The new definitions result in simplified proofs, but apart from the main files opens.lean, presheaf.lean and presheafed_space.lean where proofs are optimized, I did only the minimum changes required to fix the broken proofs, and I expect there to be large room of improvement with the new definitions especially in the files changed in this PR. I also didn't remove the old lemmas and mostly just add new ones, so subsequent cleanup may be desired.
#### Estimated changes
modified src/algebraic_geometry/Scheme.lean

modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/locally_ringed_space.lean
- \+/\- *def* restrict
- \+/\- *def* restrict

modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* hext
- \+ *lemma* comp_c
- \+ *lemma* restrict_top_presheaf
- \+ *lemma* of_restrict_top_c

modified src/algebraic_geometry/presheafed_space/has_colimits.lean

modified src/algebraic_geometry/sheafed_space.lean

modified src/algebraic_geometry/stalks.lean
- \+/\- *lemma* restrict_stalk_iso_hom_eq_germ
- \+/\- *lemma* restrict_stalk_iso_inv_eq_germ
- \+/\- *lemma* restrict_stalk_iso_hom_eq_germ
- \+/\- *lemma* restrict_stalk_iso_inv_eq_germ

modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *lemma* to_open_comp_comap
- \+/\- *lemma* to_open_comp_comap

modified src/category_theory/whiskering.lean

modified src/topology/category/Top/opens.lean
- \+ *lemma* map_supr
- \+ *lemma* map_id_eq
- \+ *lemma* map_comp_eq
- \+ *lemma* map_eq
- \+ *lemma* inclusion_top_functor
- \+ *def* inclusion_top_iso

created src/topology/sheaves/functors.lean
- \+ *lemma* map_diagram
- \+ *lemma* map_cocone
- \+ *theorem* pushforward_sheaf_of_sheaf
- \+ *theorem* pushforward_sheaf_of_sheaf
- \+ *def* pushforward

modified src/topology/sheaves/presheaf.lean
- \+ *lemma* pushforward_eq'
- \+ *lemma* id_eq
- \+ *lemma* comp_eq
- \+ *lemma* id_pushforward
- \+ *def* pushforward



## [2021-10-27 04:25:01](https://github.com/leanprover-community/mathlib/commit/996ece5)
feat(tactic/suggest): add a flag to disable "Try this" lines ([#9820](https://github.com/leanprover-community/mathlib/pull/9820))
#### Estimated changes
modified src/tactic/suggest.lean



## [2021-10-27 02:40:26](https://github.com/leanprover-community/mathlib/commit/62edbe5)
chore(scripts): update nolints.txt ([#9994](https://github.com/leanprover-community/mathlib/pull/9994))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-10-26 22:41:21](https://github.com/leanprover-community/mathlib/commit/b592589)
refactor(order/boolean_algebra): factor out pi.sdiff and pi.compl ([#9955](https://github.com/leanprover-community/mathlib/pull/9955))
Provide definitional lemmas about sdiff and compl on pi types.
This allows usage later on even without a whole `boolean_algebra` instance.
#### Estimated changes
modified src/order/boolean_algebra.lean
- \+ *lemma* pi.sdiff_def
- \+ *lemma* pi.sdiff_apply
- \+ *lemma* pi.compl_def
- \+ *lemma* pi.compl_apply



## [2021-10-26 22:41:20](https://github.com/leanprover-community/mathlib/commit/120cf5b)
doc(topology) add a library note about continuity lemmas ([#9954](https://github.com/leanprover-community/mathlib/pull/9954))
* This is a note with some tips how to formulate a continuity (or measurability, differentiability, ...) lemma.
* I wanted to write this up after formulating `continuous.strans` in many "wrong" ways before discovering the "right" way.
* I think many lemmas are not following this principle, and could be improved in generality and/or convenience by following this advice.
* Based on experience from the sphere eversion project.
* The note mentions a lemma that will be added in [#9959](https://github.com/leanprover-community/mathlib/pull/9959), but I don't think we necessarily have to wait for that PR.
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* continuous_on.comp_fract
- \+ *def* strans



## [2021-10-26 21:02:25](https://github.com/leanprover-community/mathlib/commit/36a2015)
feat(topology/[separation, dense_embedding]): a function to a T1 space which has a limit at x is continuous at x ([#9934](https://github.com/leanprover-community/mathlib/pull/9934))
We prove that, for a function `f` with values in a T1 space, knowing that `f` admits *any* limit at `x` suffices to prove that `f` is continuous at `x`.
We then use it to give a variant of `dense_inducing.extend_eq` with the same assumption required for continuity of the extension, which makes using both `extend_eq` and `continuous_extend` easier, and also brings us closer to Bourbaki who makes no explicit continuity assumption on the function to extend.
#### Estimated changes
modified src/topology/algebra/uniform_field.lean

modified src/topology/dense_embedding.lean
- \+/\- *lemma* extend_eq_at
- \+ *lemma* extend_eq_at'
- \+ *lemma* extend_eq'
- \+/\- *lemma* extend_eq_at

modified src/topology/separation.lean
- \+ *lemma* eq_of_tendsto_nhds
- \+ *lemma* continuous_at_of_tendsto_nhds

modified src/topology/uniform_space/uniform_embedding.lean



## [2021-10-26 20:05:59](https://github.com/leanprover-community/mathlib/commit/92e9078)
fix(linear_algebra/matrix/determinant): remove coercions ([#9975](https://github.com/leanprover-community/mathlib/pull/9975))
#### Estimated changes
modified src/linear_algebra/matrix/determinant.lean



## [2021-10-26 20:05:58](https://github.com/leanprover-community/mathlib/commit/2a32c70)
refactor(linear_algebra/matrix/nonsingular_inverse): split out files for adjugate and nondegenerate ([#9974](https://github.com/leanprover-community/mathlib/pull/9974))
This breaks the file roughly in two, and rescues lost lemmas that ended up in the wrong sections of the file.
The module docstrings have been tweaked a little, but all the lemmas have just been moved around.
#### Estimated changes
modified src/linear_algebra/bilinear_form.lean

created src/linear_algebra/matrix/adjugate.lean
- \+ *lemma* cramer_map_is_linear
- \+ *lemma* cramer_is_linear
- \+ *lemma* cramer_apply
- \+ *lemma* cramer_transpose_row_self
- \+ *lemma* cramer_row_self
- \+ *lemma* cramer_one
- \+ *lemma* cramer_smul
- \+ *lemma* cramer_subsingleton_apply
- \+ *lemma* cramer_zero
- \+ *lemma* sum_cramer
- \+ *lemma* sum_cramer_apply
- \+ *lemma* adjugate_def
- \+ *lemma* adjugate_apply
- \+ *lemma* adjugate_transpose
- \+ *lemma* cramer_eq_adjugate_mul_vec
- \+ *lemma* mul_adjugate_apply
- \+ *lemma* mul_adjugate
- \+ *lemma* adjugate_mul
- \+ *lemma* adjugate_smul
- \+ *lemma* mul_vec_cramer
- \+ *lemma* det_adjugate_of_cancel
- \+ *lemma* adjugate_subsingleton
- \+ *lemma* adjugate_eq_one_of_card_eq_one
- \+ *lemma* adjugate_zero
- \+ *lemma* adjugate_one
- \+ *lemma* det_adjugate_eq_one
- \+ *lemma* det_adjugate_of_is_unit
- \+ *lemma* adjugate_fin_zero
- \+ *lemma* adjugate_fin_one
- \+ *lemma* adjugate_fin_two
- \+ *lemma* adjugate_fin_two'
- \+ *lemma* _root_.ring_hom.map_adjugate
- \+ *lemma* adjugate_conj_transpose
- \+ *lemma* is_regular_of_is_left_regular_det
- \+ *lemma* adjugate_mul_distrib_aux
- \+ *lemma* adjugate_mul_distrib
- \+ *lemma* adjugate_pow
- \+ *def* cramer_map
- \+ *def* cramer
- \+ *def* adjugate

created src/linear_algebra/matrix/nondegenerate.lean
- \+ *lemma* nondegenerate.eq_zero_of_ortho
- \+ *lemma* nondegenerate.exists_not_ortho_of_ne_zero
- \+ *theorem* nondegenerate_of_det_ne_zero
- \+ *theorem* eq_zero_of_vec_mul_eq_zero
- \+ *theorem* eq_zero_of_mul_vec_eq_zero
- \+ *def* nondegenerate

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \- *lemma* cramer_map_is_linear
- \- *lemma* cramer_is_linear
- \- *lemma* cramer_apply
- \- *lemma* cramer_transpose_row_self
- \- *lemma* cramer_row_self
- \- *lemma* cramer_one
- \- *lemma* cramer_smul
- \- *lemma* cramer_subsingleton_apply
- \- *lemma* cramer_zero
- \- *lemma* sum_cramer
- \- *lemma* sum_cramer_apply
- \- *lemma* adjugate_def
- \- *lemma* adjugate_apply
- \- *lemma* adjugate_transpose
- \- *lemma* cramer_eq_adjugate_mul_vec
- \- *lemma* mul_adjugate_apply
- \- *lemma* mul_adjugate
- \- *lemma* adjugate_mul
- \- *lemma* adjugate_smul
- \- *lemma* det_adjugate_of_cancel
- \- *lemma* adjugate_subsingleton
- \- *lemma* adjugate_eq_one_of_card_eq_one
- \- *lemma* adjugate_zero
- \- *lemma* adjugate_one
- \- *lemma* det_adjugate_eq_one
- \- *lemma* det_adjugate_of_is_unit
- \- *lemma* adjugate_fin_zero
- \- *lemma* adjugate_fin_one
- \- *lemma* adjugate_fin_two
- \- *lemma* adjugate_fin_two'
- \- *lemma* _root_.ring_hom.map_adjugate
- \- *lemma* adjugate_conj_transpose
- \- *lemma* is_regular_of_is_left_regular_det
- \- *lemma* adjugate_mul_distrib_aux
- \- *lemma* adjugate_mul_distrib
- \- *lemma* adjugate_pow
- \- *lemma* mul_vec_cramer
- \- *lemma* nondegenerate.eq_zero_of_ortho
- \- *lemma* nondegenerate.exists_not_ortho_of_ne_zero
- \- *theorem* nondegenerate_of_det_ne_zero
- \- *theorem* eq_zero_of_vec_mul_eq_zero
- \- *theorem* eq_zero_of_mul_vec_eq_zero
- \- *def* cramer_map
- \- *def* cramer
- \- *def* adjugate
- \- *def* nondegenerate

modified src/linear_algebra/matrix/to_linear_equiv.lean



## [2021-10-26 17:54:26](https://github.com/leanprover-community/mathlib/commit/ce164e2)
chore(data/{finset,multiset}/locally_finite): rename from `.interval` ([#9980](https://github.com/leanprover-community/mathlib/pull/9980))
The pattern is `data.stuff.interval` for files about `locally_finite_order stuff` and... `finset α` and `multiset α` are locally finite orders. This thus makes space for this theory.
#### Estimated changes
modified src/data/finset/default.lean

renamed src/data/finset/interval.lean to src/data/finset/locally_finite.lean

renamed src/data/multiset/interval.lean to src/data/multiset/locally_finite.lean

modified src/data/nat/interval.lean



## [2021-10-26 17:54:24](https://github.com/leanprover-community/mathlib/commit/3aa5749)
feat(group_theory/subgroup/basic): Define characteristic subgroups ([#9921](https://github.com/leanprover-community/mathlib/pull/9921))
This PR defines characteristic subgroups and builds the basic API.
Getting `@[to_additive]` to work correctly was a bit tricky, so I mostly just copied the setup for `subgroup.normal`.
#### Estimated changes
modified src/data/equiv/mul_add_aut.lean
- \+/\- *lemma* conj_apply
- \+/\- *lemma* conj_apply

modified src/group_theory/nilpotent.lean

modified src/group_theory/solvable.lean

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* characteristic_iff_comap_eq
- \+ *lemma* characteristic_iff_comap_le
- \+ *lemma* characteristic_iff_le_comap
- \+ *lemma* characteristic_iff_map_eq
- \+ *lemma* characteristic_iff_map_le
- \+ *lemma* characteristic_iff_le_map



## [2021-10-26 16:22:50](https://github.com/leanprover-community/mathlib/commit/50c6094)
feat(topology/uniform_space/basic): add lemma `comp_open_symm_mem_uniformity_sets` ([#9981](https://github.com/leanprover-community/mathlib/pull/9981))
#### Estimated changes
modified src/topology/uniform_space/basic.lean
- \+ *lemma* comp_open_symm_mem_uniformity_sets



## [2021-10-26 12:23:43](https://github.com/leanprover-community/mathlib/commit/d2b1221)
feat(algebra/order/group|order/filter): add two lemmas ([#9956](https://github.com/leanprover-community/mathlib/pull/9956))
* Also open `function` namespace in `order.filter.basic`
* From the sphere eversion project
#### Estimated changes
modified src/algebra/order/group.lean
- \+ *lemma* le_div_self_iff

modified src/order/filter/basic.lean
- \+/\- *lemma* image_mem_map_iff
- \+ *lemma* _root_.function.surjective.filter_map_top
- \+/\- *lemma* comap_map
- \+/\- *lemma* mem_comap_iff
- \+/\- *lemma* map_inj
- \+/\- *lemma* map_inf
- \+/\- *lemma* pure_injective
- \+/\- *lemma* image_mem_map_iff
- \+/\- *lemma* comap_map
- \+/\- *lemma* mem_comap_iff
- \+/\- *lemma* map_inj
- \+/\- *lemma* map_inf
- \+/\- *lemma* pure_injective
- \+/\- *theorem* map_comap_of_surjective
- \+/\- *theorem* map_comap_of_surjective



## [2021-10-26 09:49:59](https://github.com/leanprover-community/mathlib/commit/41df5b3)
docs(data/sigma/basic): Add module docstring ([#9908](https://github.com/leanprover-community/mathlib/pull/9908))
#### Estimated changes
modified src/data/sigma/basic.lean



## [2021-10-26 09:09:15](https://github.com/leanprover-community/mathlib/commit/6b47ccb)
feat(group_theory/p_group): Center of a p-group is nontrivial ([#9973](https://github.com/leanprover-community/mathlib/pull/9973))
The center of a p-group is nontrivial, stated in two different ways.
#### Estimated changes
modified src/group_theory/p_group.lean
- \+ *lemma* center_nontrivial
- \+ *lemma* bot_lt_center



## [2021-10-26 07:25:48](https://github.com/leanprover-community/mathlib/commit/f229c83)
chore(*): move 2 lemmas to reorder imports ([#9969](https://github.com/leanprover-community/mathlib/pull/9969))
I want to use `measure_theory.measure_preserving` in various files, including `measure_theory.integral.lebesgue`. The file about measure preserving map had two lemmas about product measures. I move them to `measure_theory.constructions.prod`. I also golfed (and made it more readable at the same time!) the proof of `measure_theory.measure.prod_prod_le` using `to_measurable_set`.
#### Estimated changes
modified src/dynamics/ergodic/conservative.lean

modified src/dynamics/ergodic/measure_preserving.lean
- \- *lemma* skew_product
- \- *lemma* prod

modified src/measure_theory/constructions/prod.lean
- \+ *lemma* skew_product



## [2021-10-26 07:25:47](https://github.com/leanprover-community/mathlib/commit/367d71e)
chore(order/iterate): review, add docs ([#9965](https://github.com/leanprover-community/mathlib/pull/9965))
* reorder sections;
* add section docs;
* use inequalities between functions in a few statements;
* add a few lemmas about `strict_mono` functions.
#### Estimated changes
modified src/order/iterate.lean
- \+/\- *lemma* le_iterate_comp_of_le
- \+/\- *lemma* iterate_comp_le_of_le
- \+/\- *lemma* iterate_le_of_le
- \+ *lemma* le_iterate_of_le
- \+/\- *lemma* id_le_iterate_of_id_le
- \+/\- *lemma* iterate_le_id_of_le_id
- \+ *lemma* monotone_iterate_of_id_le
- \+ *lemma* antitone_iterate_of_le_id
- \+ *lemma* monotone_iterate_of_le_map
- \+ *lemma* antitone_iterate_of_map_le
- \+ *lemma* strict_mono_iterate_of_lt_map
- \+ *lemma* strict_anti_iterate_of_map_lt
- \+/\- *lemma* id_le_iterate_of_id_le
- \+/\- *lemma* iterate_le_id_of_le_id
- \- *lemma* iterate_le_iterate_of_id_le
- \- *lemma* iterate_le_iterate_of_le_id
- \+/\- *lemma* le_iterate_comp_of_le
- \+/\- *lemma* iterate_comp_le_of_le
- \+/\- *lemma* iterate_le_of_le
- \- *lemma* iterate_ge_of_ge



## [2021-10-26 07:25:45](https://github.com/leanprover-community/mathlib/commit/717de02)
refactor(linear_algebra/free_module/pid): move lemmas ([#9962](https://github.com/leanprover-community/mathlib/pull/9962))
`linear_algebra/free_module/pid` contains several results not directly related to PID. We move them in more appropriate files.
Except for small golfing and easy generalization, the statements and the proofs are untouched.
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+ *lemma* not_mem_of_ortho
- \+ *lemma* ne_zero_of_ortho

modified src/linear_algebra/basic.lean
- \+ *lemma* mem_submodule_image
- \+ *lemma* mem_submodule_image_of_le
- \+ *lemma* submodule_image_apply_of_le
- \+ *def* submodule_image

modified src/linear_algebra/basis.lean
- \+ *lemma* _root_.eq_bot_of_rank_eq_zero
- \+ *def* submodule.induction_on_rank_aux

modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.card_le_card_of_linear_independent_aux
- \+ *lemma* basis.card_le_card_of_linear_independent
- \+ *lemma* basis.card_le_card_of_submodule
- \+ *lemma* basis.card_le_card_of_le
- \+ *lemma* ideal.rank_eq
- \+ *def* submodule.induction_on_rank

modified src/linear_algebra/free_module/pid.lean
- \- *lemma* eq_bot_of_rank_eq_zero
- \- *lemma* linear_map.mem_submodule_image
- \- *lemma* linear_map.mem_submodule_image_of_le
- \- *lemma* linear_map.submodule_image_apply_of_le
- \- *lemma* generator_map_dvd_of_mem
- \- *lemma* generator_submodule_image_dvd_of_mem
- \- *lemma* not_mem_of_ortho
- \- *lemma* ne_zero_of_ortho
- \- *lemma* basis.card_le_card_of_linear_independent_aux
- \- *lemma* basis.card_le_card_of_linear_independent
- \- *lemma* basis.card_le_card_of_submodule
- \- *lemma* basis.card_le_card_of_le
- \- *lemma* ideal.rank_eq
- \- *def* linear_map.submodule_image
- \- *def* submodule.induction_on_rank_aux
- \- *def* submodule.induction_on_rank

modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* generator_map_dvd_of_mem
- \+ *lemma* generator_submodule_image_dvd_of_mem



## [2021-10-26 05:22:54](https://github.com/leanprover-community/mathlib/commit/5227f53)
chore(data/equiv/encodable): a `[unique]` type is encodable ([#9970](https://github.com/leanprover-community/mathlib/pull/9970))
#### Estimated changes
modified src/data/equiv/encodable/basic.lean

modified src/data/equiv/encodable/small.lean



## [2021-10-26 02:28:08](https://github.com/leanprover-community/mathlib/commit/a8e6442)
chore(scripts): update nolints.txt ([#9971](https://github.com/leanprover-community/mathlib/pull/9971))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt

modified scripts/style-exceptions.txt



## [2021-10-26 01:01:18](https://github.com/leanprover-community/mathlib/commit/e88b4ed)
chore(measure_theory/constructions/pi): add `pi_of_empty` ([#9937](https://github.com/leanprover-community/mathlib/pull/9937))
#### Estimated changes
modified src/measure_theory/constructions/pi.lean
- \+ *lemma* pi_univ
- \+ *lemma* pi_of_empty



## [2021-10-25 22:55:58](https://github.com/leanprover-community/mathlib/commit/56de12a)
refactor(data/mv_polynomial): upgrade `monomial` to a `linear_map` ([#9870](https://github.com/leanprover-community/mathlib/pull/9870))
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* C_eq_smul_one
- \+ *lemma* monomial_pow
- \+/\- *lemma* monomial_mul
- \+ *lemma* monomial_one_hom_apply
- \+ *lemma* X_pow_eq_monomial
- \+ *lemma* monomial_zero'
- \+/\- *lemma* sum_monomial_eq
- \+ *lemma* monomial_sum_one
- \+ *lemma* monomial_sum_index
- \+ *lemma* monomial_finsupp_sum_index
- \+ *lemma* finsupp_support_eq_support
- \+ *lemma* eval₂_mul_C
- \- *lemma* X_pow_eq_single
- \- *lemma* monomial_add
- \+/\- *lemma* monomial_mul
- \+/\- *lemma* sum_monomial_eq
- \+/\- *def* monomial
- \+ *def* monomial_one_hom
- \+/\- *def* monomial

modified src/data/mv_polynomial/comm_ring.lean
- \- *lemma* monomial_neg
- \- *lemma* monomial_sub

modified src/data/mv_polynomial/monad.lean

modified src/data/mv_polynomial/pderiv.lean

modified src/data/mv_polynomial/rename.lean

modified src/ring_theory/mv_polynomial/basic.lean

modified src/ring_theory/polynomial/symmetric.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean



## [2021-10-25 22:55:56](https://github.com/leanprover-community/mathlib/commit/34b9933)
feat(number_theory/liouville): the set of Liouville numbers has measure zero ([#9702](https://github.com/leanprover-community/mathlib/pull/9702))
As a corollary, the filters `residual ℝ` and `volume.ae` are disjoint.
#### Estimated changes
created src/number_theory/liouville/liouville_with.lean
- \+ *lemma* liouville_with_one
- \+ *lemma* exists_pos
- \+ *lemma* mono
- \+ *lemma* frequently_lt_rpow_neg
- \+ *lemma* mul_rat
- \+ *lemma* mul_rat_iff
- \+ *lemma* rat_mul_iff
- \+ *lemma* rat_mul
- \+ *lemma* mul_int_iff
- \+ *lemma* mul_int
- \+ *lemma* int_mul_iff
- \+ *lemma* int_mul
- \+ *lemma* mul_nat_iff
- \+ *lemma* mul_nat
- \+ *lemma* nat_mul_iff
- \+ *lemma* nat_mul
- \+ *lemma* add_rat
- \+ *lemma* add_rat_iff
- \+ *lemma* rat_add_iff
- \+ *lemma* rat_add
- \+ *lemma* add_int_iff
- \+ *lemma* int_add_iff
- \+ *lemma* add_nat_iff
- \+ *lemma* nat_add_iff
- \+ *lemma* add_int
- \+ *lemma* int_add
- \+ *lemma* add_nat
- \+ *lemma* nat_add
- \+ *lemma* neg_iff
- \+ *lemma* sub_rat_iff
- \+ *lemma* sub_rat
- \+ *lemma* sub_int_iff
- \+ *lemma* sub_int
- \+ *lemma* sub_nat_iff
- \+ *lemma* sub_nat
- \+ *lemma* rat_sub_iff
- \+ *lemma* rat_sub
- \+ *lemma* int_sub_iff
- \+ *lemma* int_sub
- \+ *lemma* nat_sub_iff
- \+ *lemma* nat_sub
- \+ *lemma* ne_cast_int
- \+ *lemma* frequently_exists_num
- \+ *lemma* forall_liouville_with_iff
- \+ *def* liouville_with

created src/number_theory/liouville/measure.lean
- \+ *lemma* set_of_liouville_with_subset_aux
- \+ *lemma* volume_Union_set_of_liouville_with
- \+ *lemma* ae_not_liouville_with
- \+ *lemma* ae_not_liouville
- \+ *lemma* volume_set_of_liouville
- \+ *lemma* real.disjoint_residual_ae

modified src/order/filter/basic.lean
- \+ *lemma* disjoint_of_disjoint_of_mem
- \+ *lemma* eventually.and_frequently

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* filter.eventually.exists_gt
- \+ *lemma* filter.eventually.exists_lt



## [2021-10-25 22:55:55](https://github.com/leanprover-community/mathlib/commit/c363ad6)
feat(category_theory/sites/*): Cover preserving functors ([#9691](https://github.com/leanprover-community/mathlib/pull/9691))
Split from [#9650](https://github.com/leanprover-community/mathlib/pull/9650)
- Defined `cover_preserving` functors as functors that push covering sieves to covering sieves.
- Defined `compatible_preserving` functors as functors that push compatible families to compatible families.
- Proved that functors that are both `cover_preserving` and `compatible_preserving` pulls sheaves to sheaves.
#### Estimated changes
created src/category_theory/sites/cover_preserving.lean
- \+ *lemma* id_cover_preserving
- \+ *lemma* cover_preserving.comp
- \+ *lemma* presieve.family_of_elements.compatible.functor_pushforward
- \+ *lemma* compatible_preserving.apply_map
- \+ *theorem* pullback_is_sheaf_of_cover_preserving
- \+ *def* pullback_sheaf
- \+ *def* sites.pullback

modified src/category_theory/sites/sheaf.lean

modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* family_of_elements.comp_of_compatible
- \+ *def* family_of_elements.functor_pushforward

modified src/category_theory/sites/sieves.lean



## [2021-10-25 20:31:21](https://github.com/leanprover-community/mathlib/commit/5421200)
feat(group_theory/index): Small values of `subgroup.index` ([#9893](https://github.com/leanprover-community/mathlib/pull/9893))
`H.index = 1 ↔ H = ⊤` and related results.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* index_eq_one
- \+ *lemma* index_ne_zero_of_fintype
- \+ *lemma* one_lt_index_of_ne_top



## [2021-10-25 20:31:20](https://github.com/leanprover-community/mathlib/commit/880c7bd)
chore(linear_algebra/matrix): add fin expansions for trace and adjugate, and some trace lemmas ([#9884](https://github.com/leanprover-community/mathlib/pull/9884))
We have these expansions for `det` already, I figured we may as well have them for these.
This adds some other trivial trace lemmas while I'm touching the same file.
#### Estimated changes
modified src/algebra/lie/classical.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* adjugate_fin_zero
- \+ *lemma* adjugate_fin_one

modified src/linear_algebra/matrix/trace.lean
- \+ *lemma* diag_col_mul_row
- \+ *lemma* trace_mul_cycle
- \+ *lemma* trace_mul_cycle'
- \+ *lemma* trace_col_mul_row
- \+ *lemma* trace_fin_zero
- \+ *lemma* trace_fin_one
- \+ *lemma* trace_fin_two
- \+ *lemma* trace_fin_three



## [2021-10-25 20:31:19](https://github.com/leanprover-community/mathlib/commit/e808b41)
feat(data/matrix/basic): lemmas about transpose and conj_transpose on sums and products ([#9880](https://github.com/leanprover-community/mathlib/pull/9880))
This also generalizes some previous results from `star_ring` to `star_add_monoid` now that the latter exists.
To help prove the non-commutative statements, this adds `monoid_hom.unop_map_list_prod` and similar.
This could probably used for proving `star_list_prod` in future.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* ring_hom.unop_map_list_prod

modified src/data/equiv/ring.lean
- \+ *lemma* unop_map_list_prod

modified src/data/list/basic.lean
- \+ *lemma* _root_.opposite.op_list_prod
- \+ *lemma* _root_.opposite.unop_list_prod
- \+ *lemma* monoid_hom.unop_map_list_prod
- \+ *theorem* prod_concat

modified src/data/matrix/basic.lean
- \+ *lemma* transpose_add_equiv_symm
- \+ *lemma* transpose_list_sum
- \+ *lemma* transpose_multiset_sum
- \+ *lemma* transpose_sum
- \+ *lemma* transpose_list_prod
- \+/\- *lemma* conj_transpose_add
- \+/\- *lemma* conj_transpose_sub
- \+ *lemma* conj_transpose_add_equiv_symm
- \+ *lemma* conj_transpose_list_sum
- \+ *lemma* conj_transpose_multiset_sum
- \+ *lemma* conj_transpose_sum
- \+ *lemma* conj_transpose_list_prod
- \+/\- *lemma* conj_transpose_add
- \+/\- *lemma* conj_transpose_sub
- \+ *def* transpose_add_equiv
- \+ *def* transpose_ring_equiv
- \+ *def* conj_transpose_add_equiv
- \+ *def* conj_transpose_ring_equiv



## [2021-10-25 17:43:11](https://github.com/leanprover-community/mathlib/commit/87fa12a)
chore(linear_algebra/matrix/nonsingular_inverse): replace `1 < fintype.card n` with `nontrivial n` ([#9953](https://github.com/leanprover-community/mathlib/pull/9953))
This likely makes this a better simp lemma
#### Estimated changes
modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* adjugate_zero
- \+/\- *lemma* adjugate_zero



## [2021-10-25 17:43:10](https://github.com/leanprover-community/mathlib/commit/0d131fe)
chore(group_theory/submonoid): move a lemma to reduce imports ([#9951](https://github.com/leanprover-community/mathlib/pull/9951))
Currently, `algebra.pointwise` is a relatively "heavy" import (e.g., it depends on `data.set.finite`) and I want to use submonoid closures a bit earlier than that.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/membership.lean
- \- *lemma* mem_closure_inv

modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* mem_closure_inv

modified src/ring_theory/subsemiring.lean



## [2021-10-25 17:43:09](https://github.com/leanprover-community/mathlib/commit/374885a)
feat(linear_algebra/matrix/nonsingular_inverse): lemmas about adjugate ([#9947](https://github.com/leanprover-community/mathlib/pull/9947))
#### Estimated changes
modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_update_row_smul'
- \+ *lemma* det_update_column_smul'

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* cramer_smul
- \+ *lemma* adjugate_smul
- \+ *lemma* _root_.ring_hom.map_adjugate
- \+ *lemma* adjugate_conj_transpose
- \- *lemma* ring_hom.map_adjugate

modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* map_update_smul



## [2021-10-25 17:43:06](https://github.com/leanprover-community/mathlib/commit/c693682)
chore(analysis/normed/group/basic): make various norm instances computable ([#9946](https://github.com/leanprover-community/mathlib/pull/9946))
Instead of defining the default `edist` as `ennreal.of_real` which introduces an `ite` on an undecidable equality, this constructs the `ennreal` directly using a proof of non-negativity.
This removes `noncomputable theory` from some files so as to make it obvious from the source alone which definitions are and are not computable.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+ *def* semi_normed_group.of_core
- \+ *def* normed_group.of_core

modified src/topology/metric_space/basic.lean
- \- *def* diam



## [2021-10-25 17:43:03](https://github.com/leanprover-community/mathlib/commit/5fcbd2b)
chore(linear_algebra/matrix/nonsingular_inverse): use pi.single instead of ite ([#9944](https://github.com/leanprover-community/mathlib/pull/9944))
#### Estimated changes
modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *def* adjugate
- \+/\- *def* adjugate



## [2021-10-25 17:43:01](https://github.com/leanprover-community/mathlib/commit/5778df8)
chore(analysis/complex/circle): upgrade `exp_map_circle` to `continuous_map` ([#9942](https://github.com/leanprover-community/mathlib/pull/9942))
#### Estimated changes
modified src/analysis/complex/circle.lean
- \+ *lemma* exp_map_circle_zero
- \+ *lemma* exp_map_circle_add
- \+/\- *def* exp_map_circle
- \+/\- *def* exp_map_circle



## [2021-10-25 17:43:00](https://github.com/leanprover-community/mathlib/commit/2026a5f)
feat(measure_theory/measure): better `measure.restrict_singleton` ([#9936](https://github.com/leanprover-community/mathlib/pull/9936))
With new `restrict_singleton`, `simp` can simplify `∫ x in {a}, f x ∂μ`
to `(μ {a}).to_real • f a`.
#### Estimated changes
modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* integral_dirac'
- \+/\- *lemma* integral_dirac
- \+/\- *lemma* integral_dirac'
- \+/\- *lemma* integral_dirac

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* restrict_singleton
- \+/\- *lemma* measure.restrict_singleton'
- \+/\- *lemma* measure.restrict_singleton'



## [2021-10-25 17:42:59](https://github.com/leanprover-community/mathlib/commit/8eb1c02)
feat(analysis/special_functions/pow): Equivalent conditions for zero powers ([#9897](https://github.com/leanprover-community/mathlib/pull/9897))
Lemmas for 0^x in the reals and complex numbers.
#### Estimated changes
modified src/analysis/special_functions/pow.lean
- \+ *lemma* zero_cpow_eq_iff
- \+ *lemma* eq_zero_cpow_iff
- \+ *lemma* zero_rpow_eq_iff
- \+ *lemma* eq_zero_rpow_iff



## [2021-10-25 17:42:58](https://github.com/leanprover-community/mathlib/commit/312db88)
feat(*): use `ordered_sub` instead of `nat.sub` lemmas  ([#9855](https://github.com/leanprover-community/mathlib/pull/9855))
* For all `nat.sub` lemmas in core, prefer to use the `has_ordered_sub` version.
* Most lemmas have an identical version for `has_ordered_sub`. In some cases we only have the symmetric version.
* Make arguments to `tsub_add_eq_tsub_tsub` and `tsub_add_eq_tsub_tsub_swap` explicit
* Rename `add_tsub_add_right_eq_tsub -> add_tsub_add_eq_tsub_right` (for consistency with the `_left` version)
* Rename `sub_mul' -> tsub_mul` and `mul_sub' -> mul_tsub` (these were forgotten in [#9793](https://github.com/leanprover-community/mathlib/pull/9793))
* Many of the fixes are to fix the identification of `n < m` and `n.succ \le m`.
* Add projection notation `h.nat_succ_le` for `nat.succ_le_of_lt h`.
#### Estimated changes
modified archive/100-theorems-list/83_friendship_graphs.lean

modified archive/imo/imo1977_q6.lean

modified archive/imo/imo1981_q3.lean

modified archive/miu_language/decision_suf.lean

modified archive/oxford_invariants/2021summer/week3_p1.lean

modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/big_operators/intervals.lean

modified src/algebra/char_p/basic.lean

modified src/algebra/continued_fractions/terminated_stable.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/group_power/lemmas.lean

modified src/algebra/group_power/order.lean

modified src/algebra/group_with_zero/power.lean

modified src/algebra/linear_recurrence.lean

modified src/algebra/order/ring.lean
- \+ *lemma* mul_tsub
- \+ *lemma* tsub_mul
- \- *lemma* mul_sub'
- \- *lemma* sub_mul'

modified src/algebra/order/sub.lean
- \+/\- *lemma* tsub_add_eq_tsub_tsub
- \+/\- *lemma* tsub_add_eq_tsub_tsub_swap
- \+ *lemma* add_tsub_add_eq_tsub_right
- \+/\- *lemma* tsub_add_eq_tsub_tsub
- \+/\- *lemma* tsub_add_eq_tsub_tsub_swap
- \- *lemma* add_tsub_add_right_eq_tsub

modified src/algebra/pointwise.lean

modified src/analysis/analytic/basic.lean

modified src/analysis/analytic/composition.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/calculus/specific_functions.lean

modified src/analysis/specific_limits.lean

modified src/combinatorics/composition.lean

modified src/combinatorics/derangements/finite.lean

modified src/combinatorics/hall/finite.lean

modified src/combinatorics/simple_graph/degree_sum.lean

modified src/computability/DFA.lean

modified src/computability/primrec.lean

modified src/computability/turing_machine.lean

modified src/data/bitvec/core.lean

modified src/data/buffer/parser/basic.lean

modified src/data/complex/exponential.lean

modified src/data/equiv/list.lean

modified src/data/fin/basic.lean

modified src/data/finset/basic.lean

modified src/data/hash_map.lean

modified src/data/int/basic.lean

modified src/data/int/cast.lean

modified src/data/list/basic.lean

modified src/data/list/cycle.lean

modified src/data/list/intervals.lean

modified src/data/list/nat_antidiagonal.lean

modified src/data/list/nodup_equiv_fin.lean

modified src/data/list/perm.lean

modified src/data/list/range.lean

modified src/data/list/rotate.lean

modified src/data/list/zip.lean

modified src/data/multiset/nodup.lean

modified src/data/mv_polynomial/basic.lean

modified src/data/mv_polynomial/pderiv.lean

modified src/data/nat/basic.lean
- \+ *lemma* _root_.has_lt.lt.nat_succ_le

modified src/data/nat/bitwise.lean

modified src/data/nat/cast.lean

modified src/data/nat/choose/basic.lean

modified src/data/nat/choose/cast.lean

modified src/data/nat/choose/dvd.lean

modified src/data/nat/choose/sum.lean

modified src/data/nat/dist.lean

modified src/data/nat/enat.lean

modified src/data/nat/factorial/basic.lean

modified src/data/nat/factorial/cast.lean

modified src/data/nat/interval.lean

modified src/data/nat/log.lean

modified src/data/nat/modeq.lean

modified src/data/nat/pairing.lean

modified src/data/nat/parity.lean

modified src/data/nat/pow.lean

modified src/data/nat/prime.lean

modified src/data/nat/psub.lean

modified src/data/nat/totient.lean

modified src/data/pnat/basic.lean

modified src/data/pnat/xgcd.lean

modified src/data/polynomial/cancel_leads.lean

modified src/data/polynomial/coeff.lean

modified src/data/polynomial/degree/trailing_degree.lean

modified src/data/polynomial/denoms_clearable.lean

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/div.lean

modified src/data/polynomial/erase_lead.lean

modified src/data/polynomial/hasse_deriv.lean

modified src/data/polynomial/integral_normalization.lean

modified src/data/polynomial/iterated_deriv.lean

modified src/data/polynomial/mirror.lean

modified src/data/polynomial/reverse.lean

modified src/data/polynomial/ring_division.lean

modified src/data/real/ennreal.lean

modified src/data/real/nnreal.lean

modified src/data/sym/card.lean

modified src/data/vector/basic.lean

modified src/data/zmod/basic.lean

modified src/dynamics/ergodic/conservative.lean

modified src/dynamics/ergodic/measure_preserving.lean

modified src/dynamics/periodic_pts.lean

modified src/geometry/euclidean/monge_point.lean

modified src/group_theory/nilpotent.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/perm/concrete_cycle.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/list.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/lagrange.lean

modified src/linear_algebra/matrix/fpow.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/linear_algebra/vandermonde.lean

modified src/measure_theory/decomposition/signed_hahn.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/number_theory/bernoulli.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/class_number/admissible_card_pow_degree.lean

modified src/number_theory/dioph.lean

modified src/number_theory/liouville/liouville_constant.lean

modified src/number_theory/lucas_lehmer.lean

modified src/number_theory/padics/padic_norm.lean

modified src/number_theory/padics/ring_homs.lean

modified src/number_theory/pell.lean

modified src/number_theory/primorial.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/order/complete_lattice.lean

modified src/order/filter/at_top_bot.lean

modified src/order/jordan_holder.lean

modified src/order/well_founded_set.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/perfection.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/pochhammer.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/polynomial/scale_roots.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/witt_vector/defs.lean

modified src/ring_theory/witt_vector/frobenius.lean

modified src/ring_theory/witt_vector/is_poly.lean

modified src/ring_theory/witt_vector/structure_polynomial.lean

modified src/ring_theory/witt_vector/teichmuller.lean

modified src/ring_theory/witt_vector/verschiebung.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/set_theory/game/domineering.lean

modified src/set_theory/ordinal_arithmetic.lean

modified src/set_theory/ordinal_notation.lean

modified src/tactic/group.lean

modified src/tactic/monotonicity/lemmas.lean

modified src/tactic/norm_num.lean

modified src/tactic/omega/coeffs.lean

modified src/tactic/omega/nat/sub_elim.lean

modified src/tactic/suggest.lean

modified src/testing/slim_check/sampleable.lean

modified test/library_search/basic.lean



## [2021-10-25 17:42:56](https://github.com/leanprover-community/mathlib/commit/f298c55)
refactor(linear_algebra/finite_dimensional): define finite_dimensional using module.finite ([#9854](https://github.com/leanprover-community/mathlib/pull/9854))
`finite_dimensional K V` is by definition `is_noetherian K V`. We refactor this to use everywhere `finite K V` instead.
To keep the PR reasonably small, we don't delete `finite_dimension`, but we define it as `module.finite`. In a future PR we will remove it.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/data/complex/is_R_or_C.lean

modified src/field_theory/adjoin.lean

modified src/field_theory/finite/polynomial.lean

modified src/field_theory/fixed.lean

modified src/field_theory/galois.lean

modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/normal.lean

modified src/field_theory/splitting_field.lean

modified src/field_theory/tower.lean

modified src/geometry/manifold/whitney_embedding.lean

modified src/linear_algebra/affine_space/finite_dimensional.lean

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finite_dimensional.lean
- \+ *def* fintype_basis_index

modified src/linear_algebra/finsupp_vector_space.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/dedekind_domain.lean

modified src/topology/metric_space/hausdorff_dimension.lean



## [2021-10-25 13:43:52](https://github.com/leanprover-community/mathlib/commit/3d457a2)
chore(topology/continuous_function): review API ([#9950](https://github.com/leanprover-community/mathlib/pull/9950))
* add `simps` config for `α →ᵇ β`;
* use better variable names in `topology.continuous_function.compact`;
* weaken some TC assumptions in `topology.continuous_function.compact`;
* migrate more API from `α →ᵇ β` to `C(α, β)`.
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *lemma* const_apply'
- \- *lemma* mk_of_discrete_apply
- \- *lemma* coe_const
- \- *lemma* const_apply
- \+ *def* simps.apply
- \+/\- *def* mk_of_discrete
- \+/\- *def* const
- \+/\- *def* mk_of_discrete
- \+/\- *def* const

modified src/topology/continuous_function/compact.lean
- \+ *lemma* _root_.bounded_continuous_function.dist_mk_of_compact
- \+ *lemma* _root_.bounded_continuous_function.dist_forget_boundedness
- \+ *lemma* dist_apply_le_dist
- \+/\- *lemma* dist_lt_iff_of_nonempty
- \+/\- *lemma* dist_lt_of_nonempty
- \+/\- *lemma* dist_lt_iff
- \+ *lemma* continuous_eval
- \+ *lemma* continuous_evalx
- \+ *lemma* continuous_coe
- \+ *lemma* _root_.bounded_continuous_function.norm_mk_of_compact
- \+/\- *lemma* _root_.bounded_continuous_function.norm_forget_boundedness_eq
- \+/\- *lemma* linear_isometry_bounded_of_compact_symm_apply
- \+/\- *lemma* linear_isometry_bounded_of_compact_apply_apply
- \- *lemma* add_equiv_bounded_of_compact_apply_apply
- \- *lemma* add_equiv_bounded_of_compact_to_equiv
- \+/\- *lemma* dist_lt_of_nonempty
- \+/\- *lemma* dist_lt_iff
- \+/\- *lemma* dist_lt_iff_of_nonempty
- \+/\- *lemma* _root_.bounded_continuous_function.norm_forget_boundedness_eq
- \+/\- *lemma* linear_isometry_bounded_of_compact_symm_apply
- \+/\- *lemma* linear_isometry_bounded_of_compact_apply_apply
- \+/\- *def* equiv_bounded_of_compact
- \+/\- *def* add_equiv_bounded_of_compact
- \+/\- *def* isometric_bounded_of_compact
- \+/\- *def* equiv_bounded_of_compact
- \+/\- *def* add_equiv_bounded_of_compact
- \+/\- *def* isometric_bounded_of_compact

modified src/topology/continuous_function/stone_weierstrass.lean



## [2021-10-25 13:43:51](https://github.com/leanprover-community/mathlib/commit/f23354d)
feat(linear_algebra/basic, ring_theory/ideal/basic): add span_insert ([#9941](https://github.com/leanprover-community/mathlib/pull/9941))
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* span_insert

modified src/ring_theory/ideal/basic.lean
- \+ *lemma* span_insert



## [2021-10-25 10:59:45](https://github.com/leanprover-community/mathlib/commit/26c838f)
refactor(data/real/ennreal): remove ordered sub simp lemmas ([#9902](https://github.com/leanprover-community/mathlib/pull/9902))
* They are now simp lemmas in `algebra/order/sub`
* Squeeze some simps
#### Estimated changes
modified src/algebra/order/sub.lean
- \+/\- *lemma* add_tsub_cancel_of_le
- \+/\- *lemma* tsub_eq_zero_iff_le
- \+ *lemma* tsub_eq_zero_of_le
- \+/\- *lemma* tsub_pos_iff_lt
- \+/\- *lemma* add_tsub_cancel_of_le
- \+/\- *lemma* tsub_eq_zero_iff_le
- \+/\- *lemma* tsub_pos_iff_lt

modified src/analysis/special_functions/integrals.lean

modified src/analysis/specific_limits.lean

modified src/computability/halting.lean

modified src/data/real/ennreal.lean
- \- *lemma* sub_eq_zero_of_le

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/regular.lean

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/emetric_space.lean



## [2021-10-25 08:37:22](https://github.com/leanprover-community/mathlib/commit/dc1484e)
feat(ring_theory/polynomial/cyclotomic): add lemmas about evaluation of cyclotomic polynomials at one ([#9910](https://github.com/leanprover-community/mathlib/pull/9910))
#### Estimated changes
modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* eval_one_cyclotomic_prime
- \+ *lemma* eval₂_one_cyclotomic_prime
- \+ *lemma* eval_one_cyclotomic_prime_pow
- \+ *lemma* eval₂_one_cyclotomic_prime_pow



## [2021-10-25 06:51:07](https://github.com/leanprover-community/mathlib/commit/7e53203)
chore(group_theory/submonoid/operations): golf a few proofs ([#9948](https://github.com/leanprover-community/mathlib/pull/9948))
#### Estimated changes
modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mk_mul_mk
- \+ *lemma* mul_def
- \+ *lemma* one_def



## [2021-10-25 06:51:05](https://github.com/leanprover-community/mathlib/commit/bfcbe68)
feat(group_theory/subgroup/basic): `normalizer_eq_top` ([#9917](https://github.com/leanprover-community/mathlib/pull/9917))
The normalizer is the whole group if and only if the subgroup is normal.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* normalizer_eq_top



## [2021-10-25 06:51:03](https://github.com/leanprover-community/mathlib/commit/41b90d7)
feat(group_theory/index): Second isomorphism theorem in terms of `relindex` ([#9915](https://github.com/leanprover-community/mathlib/pull/9915))
Restates the second isomorphism theorem in terms of `relindex`.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* inf_relindex_eq_relindex_sup
- \+ *lemma* relindex_eq_relindex_sup



## [2021-10-25 05:13:27](https://github.com/leanprover-community/mathlib/commit/b9260f2)
feat(group_theory/subgroup/basic): `map_subtype_le` ([#9916](https://github.com/leanprover-community/mathlib/pull/9916))
A subgroup of a subgroup is `≤`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* map_subtype_le



## [2021-10-25 01:28:17](https://github.com/leanprover-community/mathlib/commit/951a60e)
chore(data/list/basic): golf a proof ([#9949](https://github.com/leanprover-community/mathlib/pull/9949))
Prove `list.mem_map` directly, get `list.exists_of_mem_map` and
`list.mem_map_of_mem` as corollaries.
#### Estimated changes
modified src/data/list/basic.lean
- \+/\- *theorem* mem_map
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* pmap_eq_map
- \+/\- *theorem* mem_map_of_mem
- \- *theorem* exists_of_mem_map
- \+/\- *theorem* mem_map
- \+/\- *theorem* pmap_eq_map



## [2021-10-25 01:28:16](https://github.com/leanprover-community/mathlib/commit/264d33e)
docs(control/traversable/lemmas): Add module docstring ([#9927](https://github.com/leanprover-community/mathlib/pull/9927))
#### Estimated changes
modified docs/references.bib

modified src/control/traversable/lemmas.lean
- \+/\- *lemma* pure_traverse
- \+/\- *lemma* id_sequence
- \+/\- *lemma* traverse_id
- \+/\- *lemma* traverse_eq_map_id'
- \+/\- *lemma* pure_traverse
- \+/\- *lemma* id_sequence
- \+/\- *lemma* traverse_id
- \+/\- *lemma* traverse_eq_map_id'
- \+/\- *theorem* pure_transformation_apply
- \+/\- *theorem* map_traverse
- \+/\- *theorem* pure_transformation_apply
- \+/\- *theorem* map_traverse



## [2021-10-24 22:52:58](https://github.com/leanprover-community/mathlib/commit/c4760b9)
feat(algebra/big_operators/basic): prod/sum over an empty type ([#9939](https://github.com/leanprover-community/mathlib/pull/9939))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_empty

modified src/linear_algebra/multilinear/basic.lean



## [2021-10-24 22:52:57](https://github.com/leanprover-community/mathlib/commit/f9da68c)
feat(*): a few more `fun_unique`s ([#9938](https://github.com/leanprover-community/mathlib/pull/9938))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+/\- *def* fun_unique
- \+/\- *def* fun_unique

modified src/linear_algebra/pi.lean
- \+ *def* fun_unique

modified src/topology/algebra/module.lean
- \+ *lemma* coe_fun_unique
- \+ *lemma* coe_fun_unique_symm
- \+ *def* fun_unique

modified src/topology/homeomorph.lean
- \+ *def* fun_unique



## [2021-10-24 22:52:56](https://github.com/leanprover-community/mathlib/commit/942e60f)
chore(algebra/*/pi): add missing lemmas about function.update and set.piecewise ([#9935](https://github.com/leanprover-community/mathlib/pull/9935))
This adds `function.update_{zero,one,add,mul,sub,div,neg,inv,smul,vadd}`, and moves `pi.piecewise_{sub,div,neg,inv}` into the `set` namespace to match `set.piecewise_{add,mul}`.
This also adds `finset.piecewise_erase_univ`, as this is tangentially related.
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* update_one
- \+ *lemma* update_mul
- \+ *lemma* update_inv
- \+ *lemma* update_div
- \+ *lemma* set.piecewise_inv
- \+ *lemma* set.piecewise_div
- \- *lemma* pi.piecewise_inv
- \- *lemma* pi.piecewise_div

modified src/algebra/module/pi.lean
- \+ *lemma* update_smul
- \+ *lemma* piecewise_smul

modified src/data/fintype/basic.lean
- \+ *lemma* compl_singleton
- \+ *lemma* piecewise_erase_univ

modified src/logic/function/basic.lean
- \+ *lemma* apply_update₂



## [2021-10-24 22:52:55](https://github.com/leanprover-community/mathlib/commit/1e7f6b9)
docs(control/bitraversable/instances): Add def docstrings ([#9931](https://github.com/leanprover-community/mathlib/pull/9931))
#### Estimated changes
modified src/control/bitraversable/instances.lean
- \+/\- *def* const.bitraverse
- \+/\- *def* const.bitraverse



## [2021-10-24 22:52:54](https://github.com/leanprover-community/mathlib/commit/5d1e8f7)
docs(control/applicative): Add module docstring ([#9930](https://github.com/leanprover-community/mathlib/pull/9930))
#### Estimated changes
modified src/control/applicative.lean
- \+/\- *lemma* applicative.pure_seq_eq_map'
- \+/\- *lemma* applicative.pure_seq_eq_map'



## [2021-10-24 22:52:53](https://github.com/leanprover-community/mathlib/commit/6f1d45d)
docs(control/bitraversable/basic): Add defs docstrings ([#9929](https://github.com/leanprover-community/mathlib/pull/9929))
#### Estimated changes
modified src/control/bitraversable/basic.lean



## [2021-10-24 22:52:52](https://github.com/leanprover-community/mathlib/commit/5642c62)
docs(control/traversable/equiv): Add module docstring ([#9928](https://github.com/leanprover-community/mathlib/pull/9928))
#### Estimated changes
modified src/control/traversable/equiv.lean



## [2021-10-24 22:52:51](https://github.com/leanprover-community/mathlib/commit/8c0b8c7)
feat(group_theory/subgroup/basic): Contrapositive of `card_le_one_iff_eq_bot` ([#9918](https://github.com/leanprover-community/mathlib/pull/9918))
Adds contrapositive of `card_le_one_iff_eq_bot`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* one_lt_card_iff_ne_bot



## [2021-10-24 22:52:50](https://github.com/leanprover-community/mathlib/commit/4468231)
feat(data/nat/log): Equivalent conditions for logarithms to equal zero and one ([#9903](https://github.com/leanprover-community/mathlib/pull/9903))
Add equivalent conditions for a `nat.log` to equal 0 or 1.
#### Estimated changes
modified src/data/nat/log.lean
- \+ *lemma* log_of_one_lt_of_le
- \+ *lemma* log_eq_zero_iff
- \+ *lemma* log_eq_one_iff



## [2021-10-24 22:52:49](https://github.com/leanprover-community/mathlib/commit/12515db)
feat(data/list): product of list.update_nth in terms of inverses ([#9800](https://github.com/leanprover-community/mathlib/pull/9800))
Expression for the product of `l.update_nth n x` in terms of inverses instead of `take` and `drop`, assuming a group instead of a monoid.
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* prod_drop_succ
- \+ *lemma* prod_update_nth'
- \- *lemma* sum_take_add_sum_drop
- \- *lemma* sum_take_succ

modified src/data/list/zip.lean
- \+ *lemma* prod_mul_prod_eq_prod_zip_with_mul_prod_drop
- \+ *lemma* prod_mul_prod_eq_prod_zip_with_of_length_eq

modified src/data/vector/basic.lean
- \+ *lemma* to_list_update_nth
- \+ *lemma* prod_update_nth
- \+ *lemma* prod_update_nth'

modified src/data/vector/zip.lean
- \+ *lemma* prod_mul_prod_eq_prod_zip_with



## [2021-10-24 22:06:49](https://github.com/leanprover-community/mathlib/commit/c20f08e)
feat(dynamics/ergodic/measure_preserving): add `measure_preserving.symm` ([#9940](https://github.com/leanprover-community/mathlib/pull/9940))
Also make the proof of `measure_preserving.skew_product` a bit more readable.
#### Estimated changes
modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* symm



## [2021-10-24 22:06:48](https://github.com/leanprover-community/mathlib/commit/4ea8de9)
feat(measure_theory/integral): Divergence theorem for Bochner integral ([#9811](https://github.com/leanprover-community/mathlib/pull/9811))
#### Estimated changes
created src/measure_theory/integral/divergence_theorem.lean
- \+ *lemma* integral_divergence_of_has_fderiv_within_at_off_countable



## [2021-10-24 21:16:31](https://github.com/leanprover-community/mathlib/commit/a30e190)
split(analysis/normed_space/exponential): split file to minimize dependencies ([#9932](https://github.com/leanprover-community/mathlib/pull/9932))
As suggested by @urkud, this moves all the results depending on derivatives, `complex.exp` and `real.exp` to a new file `analysis/special_function/exponential`. That way the definitions of `exp` and `[complex, real].exp` are independent, which means we could eventually redefine the latter in terms of the former without breaking the import tree.
#### Estimated changes
modified src/analysis/normed_space/exponential.lean
- \- *lemma* has_strict_fderiv_at_exp_zero_of_radius_pos
- \- *lemma* has_fderiv_at_exp_zero_of_radius_pos
- \- *lemma* has_fderiv_at_exp_of_mem_ball
- \- *lemma* has_strict_fderiv_at_exp_of_mem_ball
- \- *lemma* has_strict_deriv_at_exp_of_mem_ball
- \- *lemma* has_deriv_at_exp_of_mem_ball
- \- *lemma* has_strict_deriv_at_exp_zero_of_radius_pos
- \- *lemma* has_deriv_at_exp_zero_of_radius_pos
- \- *lemma* has_strict_fderiv_at_exp_zero
- \- *lemma* has_fderiv_at_exp_zero
- \- *lemma* has_strict_fderiv_at_exp
- \- *lemma* has_fderiv_at_exp
- \- *lemma* has_strict_deriv_at_exp
- \- *lemma* has_deriv_at_exp
- \- *lemma* has_strict_deriv_at_exp_zero
- \- *lemma* has_deriv_at_exp_zero
- \- *lemma* complex.exp_eq_exp_ℂ_ℂ
- \- *lemma* real.exp_eq_exp_ℝ_ℝ

created src/analysis/special_functions/exponential.lean
- \+ *lemma* has_strict_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* has_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* has_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_strict_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_strict_deriv_at_exp_of_mem_ball
- \+ *lemma* has_deriv_at_exp_of_mem_ball
- \+ *lemma* has_strict_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_strict_fderiv_at_exp_zero
- \+ *lemma* has_fderiv_at_exp_zero
- \+ *lemma* has_strict_fderiv_at_exp
- \+ *lemma* has_fderiv_at_exp
- \+ *lemma* has_strict_deriv_at_exp
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* has_strict_deriv_at_exp_zero
- \+ *lemma* has_deriv_at_exp_zero
- \+ *lemma* complex.exp_eq_exp_ℂ_ℂ
- \+ *lemma* real.exp_eq_exp_ℝ_ℝ

modified src/combinatorics/derangements/exponential.lean



## [2021-10-24 16:04:22](https://github.com/leanprover-community/mathlib/commit/dc6b8e1)
feat(topology): add some lemmas ([#9907](https://github.com/leanprover-community/mathlib/pull/9907))
* From the sphere eversion project
* Add compositional version `continuous.fst` of `continuous_fst`, compare `measurable.fst`.
* Add `comp_continuous_at_iff` and `comp_continuous_at_iff'` for `homeomorph` (and for `inducing`).
* Add some variants of these (requested by review).
#### Estimated changes
modified src/topology/constructions.lean
- \+ *lemma* continuous.fst
- \+ *lemma* continuous_at.fst
- \+ *lemma* continuous.snd
- \+ *lemma* continuous_at.snd

modified src/topology/continuous_on.lean
- \+ *lemma* inducing.continuous_within_at_iff
- \+ *lemma* continuous_on.fst
- \+/\- *lemma* continuous_within_at.fst
- \+ *lemma* continuous_on.snd
- \+/\- *lemma* continuous_within_at.fst

modified src/topology/homeomorph.lean
- \+ *lemma* comp_continuous_at_iff
- \+ *lemma* comp_continuous_at_iff'
- \+ *lemma* comp_continuous_within_at_iff

modified src/topology/maps.lean
- \+ *lemma* inducing.continuous_at_iff
- \+ *lemma* inducing.continuous_at_iff'



## [2021-10-24 13:34:54](https://github.com/leanprover-community/mathlib/commit/696f07f)
split(data/list/lattice): split off `data.list.basic` ([#9906](https://github.com/leanprover-community/mathlib/pull/9906))
#### Estimated changes
deleted src/data/list/bag_inter.lean
- \- *theorem* nil_bag_inter
- \- *theorem* bag_inter_nil
- \- *theorem* cons_bag_inter_of_pos
- \- *theorem* cons_bag_inter_of_neg
- \- *theorem* mem_bag_inter
- \- *theorem* count_bag_inter
- \- *theorem* bag_inter_sublist_left
- \- *theorem* bag_inter_nil_iff_inter_nil

modified src/data/list/basic.lean
- \- *lemma* inter_reverse
- \- *theorem* disjoint.symm
- \- *theorem* disjoint_comm
- \- *theorem* disjoint_left
- \- *theorem* disjoint_right
- \- *theorem* disjoint_iff_ne
- \- *theorem* disjoint_of_subset_left
- \- *theorem* disjoint_of_subset_right
- \- *theorem* disjoint_of_disjoint_cons_left
- \- *theorem* disjoint_of_disjoint_cons_right
- \- *theorem* disjoint_nil_left
- \- *theorem* disjoint_nil_right
- \- *theorem* singleton_disjoint
- \- *theorem* disjoint_singleton
- \- *theorem* disjoint_append_left
- \- *theorem* disjoint_append_right
- \- *theorem* disjoint_cons_left
- \- *theorem* disjoint_cons_right
- \- *theorem* disjoint_of_disjoint_append_left_left
- \- *theorem* disjoint_of_disjoint_append_left_right
- \- *theorem* disjoint_of_disjoint_append_right_left
- \- *theorem* disjoint_of_disjoint_append_right_right
- \- *theorem* disjoint_take_drop
- \- *theorem* nil_union
- \- *theorem* cons_union
- \- *theorem* mem_union
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* sublist_suffix_of_union
- \- *theorem* suffix_union_right
- \- *theorem* union_sublist_append
- \- *theorem* forall_mem_union
- \- *theorem* forall_mem_of_forall_mem_union_left
- \- *theorem* forall_mem_of_forall_mem_union_right
- \- *theorem* inter_nil
- \- *theorem* inter_cons_of_mem
- \- *theorem* inter_cons_of_not_mem
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* mem_inter_of_mem_of_mem
- \- *theorem* mem_inter
- \- *theorem* inter_subset_left
- \- *theorem* inter_subset_right
- \- *theorem* subset_inter
- \- *theorem* inter_eq_nil_iff_disjoint
- \- *theorem* forall_mem_inter_of_forall_left
- \- *theorem* forall_mem_inter_of_forall_right

modified src/data/list/default.lean

modified src/data/list/intervals.lean

created src/data/list/lattice.lean
- \+ *lemma* disjoint.symm
- \+ *lemma* disjoint_comm
- \+ *lemma* disjoint_left
- \+ *lemma* disjoint_right
- \+ *lemma* disjoint_iff_ne
- \+ *lemma* disjoint_of_subset_left
- \+ *lemma* disjoint_of_subset_right
- \+ *lemma* disjoint_of_disjoint_cons_left
- \+ *lemma* disjoint_of_disjoint_cons_right
- \+ *lemma* disjoint_nil_left
- \+ *lemma* disjoint_nil_right
- \+ *lemma* singleton_disjoint
- \+ *lemma* disjoint_singleton
- \+ *lemma* disjoint_append_left
- \+ *lemma* disjoint_append_right
- \+ *lemma* disjoint_cons_left
- \+ *lemma* disjoint_cons_right
- \+ *lemma* disjoint_of_disjoint_append_left_left
- \+ *lemma* disjoint_of_disjoint_append_left_right
- \+ *lemma* disjoint_of_disjoint_append_right_left
- \+ *lemma* disjoint_of_disjoint_append_right_right
- \+ *lemma* disjoint_take_drop
- \+ *lemma* nil_union
- \+ *lemma* cons_union
- \+ *lemma* mem_union
- \+ *lemma* mem_union_left
- \+ *lemma* mem_union_right
- \+ *lemma* sublist_suffix_of_union
- \+ *lemma* suffix_union_right
- \+ *lemma* union_sublist_append
- \+ *lemma* forall_mem_union
- \+ *lemma* forall_mem_of_forall_mem_union_left
- \+ *lemma* forall_mem_of_forall_mem_union_right
- \+ *lemma* inter_nil
- \+ *lemma* inter_cons_of_mem
- \+ *lemma* inter_cons_of_not_mem
- \+ *lemma* mem_of_mem_inter_left
- \+ *lemma* mem_of_mem_inter_right
- \+ *lemma* mem_inter_of_mem_of_mem
- \+ *lemma* mem_inter
- \+ *lemma* inter_subset_left
- \+ *lemma* inter_subset_right
- \+ *lemma* subset_inter
- \+ *lemma* inter_eq_nil_iff_disjoint
- \+ *lemma* forall_mem_inter_of_forall_left
- \+ *lemma* forall_mem_inter_of_forall_right
- \+ *lemma* inter_reverse
- \+ *lemma* nil_bag_inter
- \+ *lemma* bag_inter_nil
- \+ *lemma* cons_bag_inter_of_pos
- \+ *lemma* cons_bag_inter_of_neg
- \+ *lemma* mem_bag_inter
- \+ *lemma* count_bag_inter
- \+ *lemma* bag_inter_sublist_left
- \+ *lemma* bag_inter_nil_iff_inter_nil

modified src/data/list/nodup.lean

modified src/data/list/perm.lean



## [2021-10-24 13:34:52](https://github.com/leanprover-community/mathlib/commit/9dc3b4d)
feat(topology/algebra/group): continuous div lemmas ([#9905](https://github.com/leanprover-community/mathlib/pull/9905))
* From the sphere eversion project
* There were already some lemmas about `sub`, now they also have multiplicative versions
* Add more lemmas about `div` being continuous
* Add `continuous_at.inv`
* Rename `nhds_translation` -> `nhds_translation_sub`.
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/topology/algebra/group.lean
- \+ *lemma* continuous_at.inv
- \+ *lemma* filter.tendsto.div'
- \+ *lemma* filter.tendsto.const_div'
- \+ *lemma* filter.tendsto.div_const'
- \+ *lemma* continuous.div'
- \+ *lemma* continuous_div_left'
- \+ *lemma* continuous_div_right'
- \+ *lemma* continuous_at.div'
- \+ *lemma* continuous_within_at.div'
- \+ *lemma* continuous_on.div'
- \+ *lemma* nhds_translation_div
- \- *lemma* filter.tendsto.sub
- \- *lemma* continuous.sub
- \- *lemma* continuous_within_at.sub
- \- *lemma* continuous_on.sub
- \- *lemma* nhds_translation

modified src/topology/algebra/uniform_group.lean



## [2021-10-24 10:50:08](https://github.com/leanprover-community/mathlib/commit/be94800)
feat(data/real/nnreal): use the nonneg instance ([#9701](https://github.com/leanprover-community/mathlib/pull/9701))
... to show that `nnreal` forms a conditionally complete linear order with bot.
This requires some fixes in the order hierarchy.
* orders on subtypes are now obtained by lifting `coe` instead of `subtype.val`. This has the nice side benefit that some proofs became simpler.
* `subset_conditionally_complete_linear_order` is now reducible
#### Estimated changes
modified src/algebra/order/nonneg.lean

modified src/algebraic_geometry/ringed_space.lean

modified src/data/equiv/denumerable.lean
- \+/\- *lemma* exists_succ
- \+/\- *lemma* exists_succ

modified src/data/real/nnreal.lean

modified src/order/basic.lean

modified src/order/conditionally_complete_lattice.lean

modified src/topology/sheaves/sheaf_condition/sites.lean

modified src/topology/sheaves/stalks.lean



## [2021-10-24 08:26:39](https://github.com/leanprover-community/mathlib/commit/416edee)
feat(analysis/normed_space/is_R_or_C): add three lemmas on bounds of linear maps over is_R_or_C. ([#9827](https://github.com/leanprover-community/mathlib/pull/9827))
Adding lemmas `linear_map.bound_of_sphere_bound`, `linear_map.bound_of_ball_bound`, `continuous_linear_map.op_norm_bound_of_ball_bound` as a preparation of a PR on Banach-Alaoglu theorem.
#### Estimated changes
created src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* linear_map.bound_of_sphere_bound
- \+ *lemma* linear_map.bound_of_ball_bound
- \+ *lemma* continuous_linear_map.op_norm_bound_of_ball_bound



## [2021-10-24 03:33:39](https://github.com/leanprover-community/mathlib/commit/ecc544e)
chore(scripts): update nolints.txt ([#9923](https://github.com/leanprover-community/mathlib/pull/9923))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt

modified scripts/style-exceptions.txt



## [2021-10-24 03:33:38](https://github.com/leanprover-community/mathlib/commit/e836a72)
feat(order/galois_connection): add `exists_eq_{l,u}`, tidy up lemmas ([#9904](https://github.com/leanprover-community/mathlib/pull/9904))
This makes some arguments implicit to `compose` as these are inferrable from the other arguments, and changes `u_l_u_eq_u` and `l_u_l_eq_l` to be applied rather than unapplied, which shortens both the proof and the places where the lemma is used.
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum.lean

modified src/group_theory/submonoid/operations.lean

modified src/model_theory/basic.lean

modified src/order/closure.lean

modified src/order/galois_connection.lean
- \+/\- *lemma* u_l_u_eq_u
- \+ *lemma* u_l_u_eq_u'
- \+ *lemma* exists_eq_u
- \+/\- *lemma* l_u_l_eq_l
- \+ *lemma* l_u_l_eq_l'
- \+ *lemma* exists_eq_l
- \+/\- *lemma* u_l_u_eq_u
- \+/\- *lemma* l_u_l_eq_l

modified src/ring_theory/ideal/operations.lean



## [2021-10-24 03:33:37](https://github.com/leanprover-community/mathlib/commit/49c6841)
chore(topology): generalize `real.image_Icc` etc ([#9784](https://github.com/leanprover-community/mathlib/pull/9784))
* add lemmas about `Ici`/`Iic`/`Icc` in `α × β`;
* introduce a typeclass for `is_compact_Icc` so that the same lemma works for `ℝ` and `ℝⁿ`;
* generalize `real.image_Icc` etc to a conditionally complete linear order (e.g., now it works for `nnreal`, `ennreal`, `ereal`), move these lemmas to the `continuous_on` namespace.
#### Estimated changes
modified docs/undergrad.yaml

modified src/analysis/box_integral/basic.lean

modified src/analysis/box_integral/box/basic.lean

modified src/analysis/box_integral/divergence_theorem.lean

modified src/analysis/box_integral/partition/measure.lean

modified src/data/set/intervals/basic.lean
- \+ *lemma* Iic_prod_Iic
- \+ *lemma* Ici_prod_Ici
- \+ *lemma* Ici_prod_eq
- \+ *lemma* Iic_prod_eq
- \+ *lemma* Icc_prod_Icc
- \+ *lemma* Icc_prod_eq

modified src/measure_theory/integral/interval_integral.lean

modified src/topology/algebra/ordered/compact.lean
- \+/\- *lemma* is_compact_interval
- \+/\- *lemma* is_compact.exists_Inf_image_eq
- \+/\- *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* is_compact.exists_forall_le
- \+/\- *lemma* is_compact.exists_forall_ge
- \+/\- *lemma* continuous.exists_forall_le
- \+/\- *lemma* continuous.exists_forall_ge
- \+ *lemma* continuous_on.image_Icc
- \+ *lemma* continuous_on.image_interval_eq_Icc
- \+ *lemma* continuous_on.image_interval
- \- *lemma* is_compact_Icc
- \+/\- *lemma* is_compact_interval
- \- *lemma* is_compact_pi_Icc
- \+/\- *lemma* is_compact.exists_Inf_image_eq
- \+/\- *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* is_compact.exists_forall_le
- \+/\- *lemma* is_compact.exists_forall_ge
- \+/\- *lemma* continuous.exists_forall_le
- \+/\- *lemma* continuous.exists_forall_ge

modified src/topology/algebra/ordered/intermediate_value.lean
- \+ *lemma* continuous_on.surj_on_Icc
- \+ *lemma* continuous_on.surj_on_interval

modified src/topology/instances/real.lean
- \- *lemma* real.image_Icc
- \- *lemma* real.image_interval_eq_Icc
- \- *lemma* real.image_interval
- \- *lemma* real.interval_subset_image_interval



## [2021-10-24 01:53:46](https://github.com/leanprover-community/mathlib/commit/55a1160)
feat(linear_algebra): add notation for star-linear maps ([#9875](https://github.com/leanprover-community/mathlib/pull/9875))
This PR adds the notation `M →ₗ⋆[R] N`, `M ≃ₗ⋆[R] N`, etc, to denote star-linear maps/equivalences, i.e. semilinear maps where the ring hom is `star`. A special case of this are conjugate-linear maps when `R = ℂ`.
#### Estimated changes
modified src/algebra/module/linear_map.lean

modified src/analysis/normed_space/linear_isometry.lean

modified src/data/equiv/module.lean

modified src/topology/algebra/module.lean

created test/semilinear.lean



## [2021-10-24 00:37:39](https://github.com/leanprover-community/mathlib/commit/5ec1572)
feat(nat/choose/central): definition of the central binomial coefficient, and bounds ([#9753](https://github.com/leanprover-community/mathlib/pull/9753))
Two exponential lower bounds on the central binomial coefficient.
#### Estimated changes
created src/data/nat/choose/central.lean
- \+ *lemma* central_binom_eq_two_mul_choose
- \+ *lemma* central_binom_pos
- \+ *lemma* central_binom_ne_zero
- \+ *lemma* central_binom_zero
- \+ *lemma* choose_le_central_binom
- \+ *lemma* two_le_central_binom
- \+ *lemma* succ_mul_central_binom_succ
- \+ *lemma* four_pow_lt_mul_central_binom
- \+ *lemma* four_pow_le_two_mul_self_mul_central_binom
- \+ *def* central_binom



## [2021-10-24 00:37:37](https://github.com/leanprover-community/mathlib/commit/d788647)
feat(ring_theory): generalize `adjoin_root.power_basis` ([#9536](https://github.com/leanprover-community/mathlib/pull/9536))
Now we only need that `g` is monic to state that `adjoin_root g` has a power basis. Note that this does not quite imply the result of [#9529](https://github.com/leanprover-community/mathlib/pull/9529): this is phrased in terms of `minpoly R (root g)` and the other PR in terms of `g` itself, so I don't have a direct use for the current PR. However, it seems useful enough to have this statement, so I PR'd it anyway.
#### Estimated changes
modified src/data/polynomial/div.lean
- \+ *lemma* sum_fin
- \+ *lemma* sum_mod_by_monic_coeff

modified src/ring_theory/adjoin_root.lean
- \+ *lemma* mk_eq_mk
- \+ *lemma* is_integral_root'
- \+ *lemma* mod_by_monic_hom_mk
- \+ *lemma* mk_left_inverse
- \+ *lemma* mk_surjective
- \+ *def* mod_by_monic_hom
- \+ *def* power_basis_aux'
- \+ *def* power_basis'



## [2021-10-23 22:10:47](https://github.com/leanprover-community/mathlib/commit/928d0e0)
docs(data/dlist/instances): Add module docstring ([#9912](https://github.com/leanprover-community/mathlib/pull/9912))
#### Estimated changes
modified src/control/traversable/equiv.lean

modified src/data/dlist/instances.lean



## [2021-10-23 22:10:46](https://github.com/leanprover-community/mathlib/commit/15161e9)
docs(data/list/sigma): Add missing def dosctrings, expand module docs ([#9909](https://github.com/leanprover-community/mathlib/pull/9909))
#### Estimated changes
modified src/data/list/sigma.lean
- \+/\- *theorem* keys_nil
- \+/\- *theorem* keys_cons
- \+/\- *theorem* keys_nil
- \+/\- *theorem* keys_cons
- \+/\- *def* keys
- \+/\- *def* nodupkeys
- \+/\- *def* keys
- \+/\- *def* nodupkeys



## [2021-10-23 22:10:45](https://github.com/leanprover-community/mathlib/commit/75b1a94)
refactor(analysis/special_functions/exp_log): split into 4 files ([#9882](https://github.com/leanprover-community/mathlib/pull/9882))
#### Estimated changes
modified src/analysis/ODE/gronwall.lean

modified src/analysis/special_functions/arsinh.lean

modified src/analysis/special_functions/complex/log.lean

created src/analysis/special_functions/exp.lean
- \+ *lemma* exp_bound_sq
- \+ *lemma* locally_lipschitz_exp
- \+ *lemma* continuous_exp
- \+ *lemma* continuous_on_exp
- \+ *lemma* filter.tendsto.cexp
- \+ *lemma* continuous_within_at.cexp
- \+ *lemma* continuous_at.cexp
- \+ *lemma* continuous_on.cexp
- \+ *lemma* continuous.cexp
- \+ *lemma* continuous_exp
- \+ *lemma* continuous_on_exp
- \+ *lemma* filter.tendsto.exp
- \+ *lemma* continuous_within_at.exp
- \+ *lemma* continuous_at.exp
- \+ *lemma* continuous_on.exp
- \+ *lemma* continuous.exp
- \+ *lemma* tendsto_exp_at_top
- \+ *lemma* tendsto_exp_neg_at_top_nhds_0
- \+ *lemma* tendsto_exp_nhds_0_nhds_1
- \+ *lemma* tendsto_exp_at_bot
- \+ *lemma* tendsto_exp_at_bot_nhds_within
- \+ *lemma* tendsto_exp_div_pow_at_top
- \+ *lemma* tendsto_pow_mul_exp_neg_at_top_nhds_0
- \+ *lemma* tendsto_mul_exp_add_div_pow_at_top
- \+ *lemma* tendsto_div_pow_mul_exp_add_at_top
- \+ *lemma* coe_exp_order_iso_apply
- \+ *lemma* coe_comp_exp_order_iso
- \+ *lemma* range_exp
- \+ *lemma* map_exp_at_top
- \+ *lemma* comap_exp_at_top
- \+ *lemma* tendsto_exp_comp_at_top
- \+ *lemma* tendsto_comp_exp_at_top
- \+ *lemma* map_exp_at_bot
- \+ *lemma* comap_exp_nhds_within_Ioi_zero
- \+ *lemma* tendsto_comp_exp_at_bot
- \+ *def* exp_order_iso

created src/analysis/special_functions/exp_deriv.lean
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* differentiable_exp
- \+ *lemma* differentiable_at_exp
- \+ *lemma* deriv_exp
- \+ *lemma* iter_deriv_exp
- \+ *lemma* times_cont_diff_exp
- \+ *lemma* has_strict_deriv_at_exp
- \+ *lemma* has_strict_fderiv_at_exp_real
- \+ *lemma* is_open_map_exp
- \+ *lemma* has_strict_deriv_at.cexp
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_cexp
- \+ *lemma* has_strict_deriv_at.cexp_real
- \+ *lemma* has_deriv_at.cexp_real
- \+ *lemma* has_deriv_within_at.cexp_real
- \+ *lemma* has_strict_fderiv_at.cexp
- \+ *lemma* has_fderiv_within_at.cexp
- \+ *lemma* has_fderiv_at.cexp
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable.cexp
- \+ *lemma* times_cont_diff.cexp
- \+ *lemma* times_cont_diff_at.cexp
- \+ *lemma* times_cont_diff_on.cexp
- \+ *lemma* times_cont_diff_within_at.cexp
- \+ *lemma* has_strict_deriv_at_exp
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* times_cont_diff_exp
- \+ *lemma* differentiable_exp
- \+ *lemma* differentiable_at_exp
- \+ *lemma* deriv_exp
- \+ *lemma* iter_deriv_exp
- \+ *lemma* has_strict_deriv_at.exp
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* deriv_within_exp
- \+ *lemma* deriv_exp
- \+ *lemma* times_cont_diff.exp
- \+ *lemma* times_cont_diff_at.exp
- \+ *lemma* times_cont_diff_on.exp
- \+ *lemma* times_cont_diff_within_at.exp
- \+ *lemma* has_fderiv_within_at.exp
- \+ *lemma* has_fderiv_at.exp
- \+ *lemma* has_strict_fderiv_at.exp
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable.exp
- \+ *lemma* fderiv_within_exp
- \+ *lemma* fderiv_exp

deleted src/analysis/special_functions/exp_log.lean
- \- *lemma* exp_bound_sq
- \- *lemma* locally_lipschitz_exp
- \- *lemma* continuous_exp
- \- *lemma* continuous_on_exp
- \- *lemma* filter.tendsto.cexp
- \- *lemma* continuous_within_at.cexp
- \- *lemma* continuous_at.cexp
- \- *lemma* continuous_on.cexp
- \- *lemma* continuous.cexp
- \- *lemma* continuous_exp
- \- *lemma* continuous_on_exp
- \- *lemma* has_deriv_at_exp
- \- *lemma* differentiable_exp
- \- *lemma* differentiable_at_exp
- \- *lemma* deriv_exp
- \- *lemma* iter_deriv_exp
- \- *lemma* times_cont_diff_exp
- \- *lemma* has_strict_deriv_at_exp
- \- *lemma* has_strict_fderiv_at_exp_real
- \- *lemma* is_open_map_exp
- \- *lemma* has_strict_deriv_at.cexp
- \- *lemma* has_deriv_at.cexp
- \- *lemma* has_deriv_within_at.cexp
- \- *lemma* deriv_within_cexp
- \- *lemma* deriv_cexp
- \- *lemma* has_strict_deriv_at.cexp_real
- \- *lemma* has_deriv_at.cexp_real
- \- *lemma* has_deriv_within_at.cexp_real
- \- *lemma* has_strict_fderiv_at.cexp
- \- *lemma* has_fderiv_within_at.cexp
- \- *lemma* has_fderiv_at.cexp
- \- *lemma* differentiable_within_at.cexp
- \- *lemma* differentiable_at.cexp
- \- *lemma* differentiable_on.cexp
- \- *lemma* differentiable.cexp
- \- *lemma* times_cont_diff.cexp
- \- *lemma* times_cont_diff_at.cexp
- \- *lemma* times_cont_diff_on.cexp
- \- *lemma* times_cont_diff_within_at.cexp
- \- *lemma* has_strict_deriv_at_exp
- \- *lemma* has_deriv_at_exp
- \- *lemma* times_cont_diff_exp
- \- *lemma* differentiable_exp
- \- *lemma* differentiable_at_exp
- \- *lemma* deriv_exp
- \- *lemma* iter_deriv_exp
- \- *lemma* has_strict_deriv_at.exp
- \- *lemma* has_deriv_at.exp
- \- *lemma* has_deriv_within_at.exp
- \- *lemma* deriv_within_exp
- \- *lemma* deriv_exp
- \- *lemma* times_cont_diff.exp
- \- *lemma* times_cont_diff_at.exp
- \- *lemma* times_cont_diff_on.exp
- \- *lemma* times_cont_diff_within_at.exp
- \- *lemma* has_fderiv_within_at.exp
- \- *lemma* has_fderiv_at.exp
- \- *lemma* has_strict_fderiv_at.exp
- \- *lemma* differentiable_within_at.exp
- \- *lemma* differentiable_at.exp
- \- *lemma* differentiable_on.exp
- \- *lemma* differentiable.exp
- \- *lemma* fderiv_within_exp
- \- *lemma* fderiv_exp
- \- *lemma* tendsto_exp_at_top
- \- *lemma* tendsto_exp_neg_at_top_nhds_0
- \- *lemma* tendsto_exp_nhds_0_nhds_1
- \- *lemma* tendsto_exp_at_bot
- \- *lemma* tendsto_exp_at_bot_nhds_within
- \- *lemma* coe_exp_order_iso_apply
- \- *lemma* coe_comp_exp_order_iso
- \- *lemma* range_exp
- \- *lemma* map_exp_at_top
- \- *lemma* comap_exp_at_top
- \- *lemma* tendsto_exp_comp_at_top
- \- *lemma* tendsto_comp_exp_at_top
- \- *lemma* map_exp_at_bot
- \- *lemma* comap_exp_nhds_within_Ioi_zero
- \- *lemma* tendsto_comp_exp_at_bot
- \- *lemma* log_of_ne_zero
- \- *lemma* log_of_pos
- \- *lemma* exp_log_eq_abs
- \- *lemma* exp_log
- \- *lemma* exp_log_of_neg
- \- *lemma* log_exp
- \- *lemma* surj_on_log
- \- *lemma* log_surjective
- \- *lemma* range_log
- \- *lemma* log_zero
- \- *lemma* log_one
- \- *lemma* log_abs
- \- *lemma* log_neg_eq_log
- \- *lemma* surj_on_log'
- \- *lemma* log_mul
- \- *lemma* log_div
- \- *lemma* log_inv
- \- *lemma* log_le_log
- \- *lemma* log_lt_log
- \- *lemma* log_lt_log_iff
- \- *lemma* log_pos_iff
- \- *lemma* log_pos
- \- *lemma* log_neg_iff
- \- *lemma* log_neg
- \- *lemma* log_nonneg_iff
- \- *lemma* log_nonneg
- \- *lemma* log_nonpos_iff
- \- *lemma* log_nonpos_iff'
- \- *lemma* log_nonpos
- \- *lemma* strict_mono_on_log
- \- *lemma* strict_anti_on_log
- \- *lemma* log_inj_on_pos
- \- *lemma* eq_one_of_pos_of_log_eq_zero
- \- *lemma* log_ne_zero_of_pos_of_ne_one
- \- *lemma* log_eq_zero
- \- *lemma* tendsto_log_at_top
- \- *lemma* tendsto_log_nhds_within_zero
- \- *lemma* continuous_on_log
- \- *lemma* continuous_log
- \- *lemma* continuous_log'
- \- *lemma* continuous_at_log
- \- *lemma* continuous_at_log_iff
- \- *lemma* has_strict_deriv_at_log_of_pos
- \- *lemma* has_strict_deriv_at_log
- \- *lemma* has_deriv_at_log
- \- *lemma* differentiable_at_log
- \- *lemma* differentiable_on_log
- \- *lemma* differentiable_at_log_iff
- \- *lemma* deriv_log
- \- *lemma* deriv_log'
- \- *lemma* times_cont_diff_on_log
- \- *lemma* times_cont_diff_at_log
- \- *lemma* filter.tendsto.log
- \- *lemma* continuous.log
- \- *lemma* continuous_at.log
- \- *lemma* continuous_within_at.log
- \- *lemma* continuous_on.log
- \- *lemma* has_deriv_within_at.log
- \- *lemma* has_deriv_at.log
- \- *lemma* has_strict_deriv_at.log
- \- *lemma* deriv_within.log
- \- *lemma* deriv.log
- \- *lemma* has_fderiv_within_at.log
- \- *lemma* has_fderiv_at.log
- \- *lemma* has_strict_fderiv_at.log
- \- *lemma* differentiable_within_at.log
- \- *lemma* differentiable_at.log
- \- *lemma* times_cont_diff_at.log
- \- *lemma* times_cont_diff_within_at.log
- \- *lemma* times_cont_diff_on.log
- \- *lemma* times_cont_diff.log
- \- *lemma* differentiable_on.log
- \- *lemma* differentiable.log
- \- *lemma* fderiv_within.log
- \- *lemma* fderiv.log
- \- *lemma* tendsto_exp_div_pow_at_top
- \- *lemma* tendsto_pow_mul_exp_neg_at_top_nhds_0
- \- *lemma* tendsto_mul_exp_add_div_pow_at_top
- \- *lemma* tendsto_div_pow_mul_exp_add_at_top
- \- *lemma* tendsto_mul_log_one_plus_div_at_top
- \- *lemma* abs_log_sub_add_sum_range_le
- \- *theorem* has_sum_pow_div_log_of_abs_lt_1
- \- *def* exp_order_iso

created src/analysis/special_functions/log.lean
- \+ *lemma* log_of_ne_zero
- \+ *lemma* log_of_pos
- \+ *lemma* exp_log_eq_abs
- \+ *lemma* exp_log
- \+ *lemma* exp_log_of_neg
- \+ *lemma* log_exp
- \+ *lemma* surj_on_log
- \+ *lemma* log_surjective
- \+ *lemma* range_log
- \+ *lemma* log_zero
- \+ *lemma* log_one
- \+ *lemma* log_abs
- \+ *lemma* log_neg_eq_log
- \+ *lemma* surj_on_log'
- \+ *lemma* log_mul
- \+ *lemma* log_div
- \+ *lemma* log_inv
- \+ *lemma* log_le_log
- \+ *lemma* log_lt_log
- \+ *lemma* log_lt_log_iff
- \+ *lemma* log_pos_iff
- \+ *lemma* log_pos
- \+ *lemma* log_neg_iff
- \+ *lemma* log_neg
- \+ *lemma* log_nonneg_iff
- \+ *lemma* log_nonneg
- \+ *lemma* log_nonpos_iff
- \+ *lemma* log_nonpos_iff'
- \+ *lemma* log_nonpos
- \+ *lemma* strict_mono_on_log
- \+ *lemma* strict_anti_on_log
- \+ *lemma* log_inj_on_pos
- \+ *lemma* eq_one_of_pos_of_log_eq_zero
- \+ *lemma* log_ne_zero_of_pos_of_ne_one
- \+ *lemma* log_eq_zero
- \+ *lemma* tendsto_log_at_top
- \+ *lemma* tendsto_log_nhds_within_zero
- \+ *lemma* continuous_on_log
- \+ *lemma* continuous_log
- \+ *lemma* continuous_log'
- \+ *lemma* continuous_at_log
- \+ *lemma* continuous_at_log_iff
- \+ *lemma* filter.tendsto.log
- \+ *lemma* continuous.log
- \+ *lemma* continuous_at.log
- \+ *lemma* continuous_within_at.log
- \+ *lemma* continuous_on.log

created src/analysis/special_functions/log_deriv.lean
- \+ *lemma* has_strict_deriv_at_log_of_pos
- \+ *lemma* has_strict_deriv_at_log
- \+ *lemma* has_deriv_at_log
- \+ *lemma* differentiable_at_log
- \+ *lemma* differentiable_on_log
- \+ *lemma* differentiable_at_log_iff
- \+ *lemma* deriv_log
- \+ *lemma* deriv_log'
- \+ *lemma* times_cont_diff_on_log
- \+ *lemma* times_cont_diff_at_log
- \+ *lemma* has_deriv_within_at.log
- \+ *lemma* has_deriv_at.log
- \+ *lemma* has_strict_deriv_at.log
- \+ *lemma* deriv_within.log
- \+ *lemma* deriv.log
- \+ *lemma* has_fderiv_within_at.log
- \+ *lemma* has_fderiv_at.log
- \+ *lemma* has_strict_fderiv_at.log
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* differentiable_at.log
- \+ *lemma* times_cont_diff_at.log
- \+ *lemma* times_cont_diff_within_at.log
- \+ *lemma* times_cont_diff_on.log
- \+ *lemma* times_cont_diff.log
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable.log
- \+ *lemma* fderiv_within.log
- \+ *lemma* fderiv.log
- \+ *lemma* tendsto_mul_log_one_plus_div_at_top
- \+ *lemma* abs_log_sub_add_sum_range_le
- \+ *theorem* has_sum_pow_div_log_of_abs_lt_1

modified src/analysis/special_functions/pow.lean

modified src/analysis/special_functions/trigonometric/basic.lean

modified src/data/complex/exponential_bounds.lean
- \+/\- *lemma* exp_one_near_10
- \+/\- *lemma* exp_one_near_20
- \+/\- *lemma* log_two_near_10
- \+/\- *lemma* exp_one_near_10
- \+/\- *lemma* exp_one_near_20
- \+/\- *lemma* log_two_near_10

modified test/differentiable.lean

modified test/library_search/exp_le_exp.lean



## [2021-10-23 22:10:44](https://github.com/leanprover-community/mathlib/commit/59db903)
feat(topology/metric_space/lipschitz): continuity on product of continuity in 1 var and Lipschitz continuity in another ([#9758](https://github.com/leanprover-community/mathlib/pull/9758))
Also apply the new lemma to `continuous_bounded_map`s and add a few lemmas there.
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *lemma* lipschitz_evalx
- \+ *lemma* continuous_coe
- \+ *theorem* uniform_continuous_coe
- \+/\- *theorem* continuous_evalx
- \+/\- *theorem* continuous_evalx

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* edist_lt_of_edist_lt_div
- \+ *lemma* edist_lt_of_edist_lt_div
- \+ *lemma* continuous_on_prod_of_continuous_on_lipschitz_on
- \+ *lemma* continuous_prod_of_continuous_lipschitz



## [2021-10-23 20:04:35](https://github.com/leanprover-community/mathlib/commit/939e8b9)
docs(control/traversable/instances): Add module docstring ([#9913](https://github.com/leanprover-community/mathlib/pull/9913))
#### Estimated changes
modified src/control/traversable/instances.lean



## [2021-10-23 20:04:34](https://github.com/leanprover-community/mathlib/commit/14b998b)
docs(control/bifunctor): Add module and defs docstrings ([#9911](https://github.com/leanprover-community/mathlib/pull/9911))
#### Estimated changes
modified src/control/bifunctor.lean
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* fst
- \+/\- *def* snd



## [2021-10-23 20:04:33](https://github.com/leanprover-community/mathlib/commit/78252a3)
chore(data/real/sqrt): A couple of lemmas about sqrt ([#9892](https://github.com/leanprover-community/mathlib/pull/9892))
Add a couple of lemmas about `sqrt x / x`.
#### Estimated changes
modified src/data/real/sqrt.lean
- \+ *theorem* sqrt_div_self'
- \+ *theorem* sqrt_div_self



## [2021-10-23 20:04:32](https://github.com/leanprover-community/mathlib/commit/3f58dc7)
feat(linear_algebra/free_module/pid): golf basis.card_le_card_of_linear_independent_aux ([#9813](https://github.com/leanprover-community/mathlib/pull/9813))
We go from a 70 lines proof to a one line proof.
#### Estimated changes
modified src/linear_algebra/free_module/pid.lean



## [2021-10-23 20:04:31](https://github.com/leanprover-community/mathlib/commit/fc3c056)
chore(data/real): make more instances on real, nnreal, and ennreal computable ([#9806](https://github.com/leanprover-community/mathlib/pull/9806))
This makes it possible to talk about the add_monoid structure of nnreal and ennreal without worrying about computability.
To make it clear exactly which operations are computable, we remove `noncomputable theory`.
#### Estimated changes
modified src/algebra/order/nonneg.lean

modified src/data/real/basic.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul
- \- *def* of_nnreal_hom

modified src/data/real/nnreal.lean
- \- *def* _root_.real.to_nnreal
- \- *def* nnabs



## [2021-10-23 17:11:13](https://github.com/leanprover-community/mathlib/commit/5c5d818)
chore(data/fintype/basic): make units.fintype computable ([#9846](https://github.com/leanprover-community/mathlib/pull/9846))
This also:
* renames `equiv.units_equiv_ne_zero` to `units_equiv_ne_zero`, and resolves the TODO comment about generalization
* renames and generalizes `finite_field.card_units` to `fintype.card_units`, and proves it right next to the fintype instance
* generalizes some typeclass assumptions in `finite_field.basic` as the linter already required me to tweak them
#### Estimated changes
modified src/data/equiv/ring.lean
- \- *lemma* coe_units_equiv_ne_zero
- \- *def* units_equiv_ne_zero

modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_subtype_eq
- \+/\- *lemma* fintype.card_subtype_eq'
- \+ *lemma* fintype.card_units
- \+/\- *lemma* fintype.card_subtype_eq
- \+/\- *lemma* fintype.card_subtype_eq'
- \+ *def* _root_.units_equiv_prod_subtype
- \+ *def* _root_.units_equiv_ne_zero

modified src/field_theory/chevalley_warning.lean

modified src/field_theory/finite/basic.lean
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* sum_pow_units
- \- *lemma* card_units
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* sum_pow_units

modified src/field_theory/finite/polynomial.lean

modified src/ring_theory/integral_domain.lean



## [2021-10-23 17:11:12](https://github.com/leanprover-community/mathlib/commit/36f8c1d)
refactor(order/filter/bases): turn `is_countably_generated` into a class ([#9838](https://github.com/leanprover-community/mathlib/pull/9838))
## API changes
### Filters
* turn `filter.is_countably_generated` into a class, turn some lemmas into instances;
* remove definition/lemmas (all were in the `filter.is_countably_generated` namespace): `generating_set`, `countable_generating_set`, `eq_generate`, `countable_filter_basis`, `filter_basis_filter`, `has_countable_basis`, `exists_countable_infi_principal`, `exists_seq`;
* rename `filter.is_countably_generated.exists_antitone_subbasis` to `filter.has_basis.exists_antitone_subbasis`;
* rename `filter.is_countably_generated.exists_antitone_basis` to `filter.exists_antitone_basis`;
* rename `filter.is_countably_generated.exists_antitone_seq'` to `filter.exists_antitone_seq`;
* rename `filter.is_countably_generated.exists_seq` to `filter.exists_antitone_eq_infi_principal`;
* rename `filter.is_countably_generated.tendsto_iff_seq_tendsto` to `filter.tendsto_iff_seq_tendsto`;
* rename `filter.is_countably_generated.tendsto_of_seq_tendsto` to `filter.tendsto_of_seq_tendsto`;
* slightly generalize `is_countably_generated_at_top` and `is_countably_generated_at_bot`;
* add `filter.generate_eq_binfi`;
### Topology
* merge `is_closed.is_Gδ` with `is_closed.is_Gδ'`;
* merge `is_Gδ_set_of_continuous_at_of_countably_generated_uniformity` with `is_Gδ_set_of_continuous_at`;
* merge `is_lub.exists_seq_strict_mono_tendsto_of_not_mem'` with `is_lub.exists_seq_strict_mono_tendsto_of_not_mem`;
* merge `is_lub.exists_seq_monotone_tendsto'` with `is_lub.exists_seq_monotone_tendsto`;
* merge `is_glb.exists_seq_strict_anti_tendsto_of_not_mem'` with `is_glb.exists_seq_strict_anti_tendsto_of_not_mem`;
* merge `is_glb.exists_seq_antitone_tendsto'` with `is_glb.exists_seq_antitone_tendsto`;
* drop `emetric.first_countable_topology`, turn `uniform_space.first_countable_topology` into an instance;
* drop `emetric.second_countable_of_separable`, use `uniform_space.second_countable_of_separable` instead;
* drop `metric.compact_iff_seq_compact`, use `uniform_space.compact_iff_seq_compact` instead;
* drop `metric.compact_space_iff_seq_compact_space`, use `uniform_space.compact_space_iff_seq_compact_space` instead;
## Measure theory and integrals
Various lemmas assume `[is_countably_generated l]` instead of `(h : is_countably_generated l)`.
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/analysis/calculus/parametric_integral.lean

modified src/measure_theory/function/ae_eq_of_integral.lean

modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* ae_cover.lintegral_tendsto_of_countably_generated
- \+/\- *lemma* ae_cover.lintegral_eq_of_tendsto
- \+/\- *lemma* ae_cover.supr_lintegral_eq_of_countably_generated
- \+/\- *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto
- \+/\- *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto'
- \+/\- *lemma* ae_cover.integrable_of_integral_norm_tendsto
- \+/\- *lemma* ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
- \+/\- *lemma* ae_cover.integral_tendsto_of_countably_generated
- \+/\- *lemma* ae_cover.integral_eq_of_tendsto
- \+/\- *lemma* ae_cover.integral_eq_of_tendsto_of_nonneg_ae
- \+/\- *lemma* ae_cover.lintegral_tendsto_of_countably_generated
- \+/\- *lemma* ae_cover.lintegral_eq_of_tendsto
- \+/\- *lemma* ae_cover.supr_lintegral_eq_of_countably_generated
- \+/\- *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto
- \+/\- *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto'
- \+/\- *lemma* ae_cover.integrable_of_integral_norm_tendsto
- \+/\- *lemma* ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
- \+/\- *lemma* ae_cover.integral_tendsto_of_countably_generated
- \+/\- *lemma* ae_cover.integral_eq_of_tendsto
- \+/\- *lemma* ae_cover.integral_eq_of_tendsto_of_nonneg_ae

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/order/filter/archimedean.lean
- \- *lemma* at_top_countably_generated_of_archimedean
- \- *lemma* at_bot_countably_generated

modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* tendsto_iff_seq_tendsto
- \+/\- *lemma* tendsto_of_seq_tendsto
- \+ *lemma* subseq_tendsto_of_ne_bot
- \- *lemma* is_countably_generated_at_top
- \- *lemma* is_countably_generated_at_bot
- \+/\- *lemma* tendsto_iff_seq_tendsto
- \+/\- *lemma* tendsto_of_seq_tendsto
- \- *lemma* subseq_tendsto

modified src/order/filter/bases.lean
- \+/\- *lemma* has_countable_basis.is_countably_generated
- \+ *lemma* has_basis.exists_antitone_subbasis
- \+/\- *lemma* exists_antitone_basis
- \+ *lemma* exists_antitone_eq_infi_principal
- \+ *lemma* exists_antitone_seq
- \+/\- *lemma* is_countably_generated_seq
- \+/\- *lemma* is_countably_generated_principal
- \+ *lemma* is_countably_generated_bot
- \+ *lemma* is_countably_generated_top
- \- *lemma* countable_generating_set
- \- *lemma* eq_generate
- \- *lemma* filter_basis_filter
- \- *lemma* has_countable_basis
- \- *lemma* exists_countable_infi_principal
- \- *lemma* exists_seq
- \- *lemma* exists_antitone_subbasis
- \+/\- *lemma* exists_antitone_basis
- \+/\- *lemma* has_countable_basis.is_countably_generated
- \+/\- *lemma* is_countably_generated_seq
- \+/\- *lemma* is_countably_generated_principal
- \- *lemma* inf
- \- *lemma* inf_principal
- \- *lemma* exists_antitone_seq'
- \- *def* is_countably_generated
- \- *def* generating_set
- \- *def* countable_filter_basis

modified src/order/filter/basic.lean
- \+ *lemma* generate_eq_binfi

modified src/topology/G_delta.lean
- \+/\- *lemma* is_closed.is_Gδ
- \+/\- *lemma* is_Gδ_set_of_continuous_at
- \- *lemma* is_closed.is_Gδ'
- \+/\- *lemma* is_closed.is_Gδ
- \- *lemma* is_Gδ_set_of_continuous_at_of_countably_generated_uniformity
- \+/\- *lemma* is_Gδ_set_of_continuous_at

modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem
- \+/\- *lemma* is_lub.exists_seq_monotone_tendsto
- \+/\- *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem
- \+/\- *lemma* is_glb.exists_seq_antitone_tendsto
- \- *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem'
- \- *lemma* is_lub.exists_seq_monotone_tendsto'
- \+/\- *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem
- \+/\- *lemma* is_lub.exists_seq_monotone_tendsto
- \- *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem'
- \- *lemma* is_glb.exists_seq_antitone_tendsto'
- \+/\- *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem
- \+/\- *lemma* is_glb.exists_seq_antitone_tendsto

modified src/topology/bases.lean
- \- *lemma* is_countably_generated_nhds
- \- *lemma* is_countably_generated_nhds_within

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean
- \- *lemma* second_countable_of_separable
- \- *theorem* uniformity_has_countable_basis

modified src/topology/sequences.lean
- \+/\- *lemma* lebesgue_number_lemma_seq
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space
- \+/\- *lemma* lebesgue_number_lemma_seq
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space
- \- *lemma* metric.compact_iff_seq_compact
- \- *lemma* metric.compact_space_iff_seq_compact_space

modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_space.has_seq_basis
- \+/\- *lemma* uniform_space.has_seq_basis

modified src/topology/uniform_space/cauchy.lean



## [2021-10-23 17:11:11](https://github.com/leanprover-community/mathlib/commit/d0d1520)
chore(ring_theory/derivation): add `leibniz_pow` and `leibniz_inv` ([#9837](https://github.com/leanprover-community/mathlib/pull/9837))
#### Estimated changes
modified src/ring_theory/derivation.lean
- \+ *lemma* leibniz_pow
- \+ *lemma* leibniz_of_mul_eq_one
- \+ *lemma* leibniz_inv_of
- \+ *lemma* leibniz_inv



## [2021-10-23 17:11:09](https://github.com/leanprover-community/mathlib/commit/1ebea89)
feat(field_theory/finite/galois_field): finite fields with the same cardinality are isomorphic ([#9834](https://github.com/leanprover-community/mathlib/pull/9834))
Added the isomorphism of finite fields of the same cardinality.
#### Estimated changes
modified src/field_theory/finite/galois_field.lean
- \+ *def* alg_equiv_of_card_eq
- \+ *def* ring_equiv_of_card_eq



## [2021-10-23 17:11:08](https://github.com/leanprover-community/mathlib/commit/0411b1e)
feat(ring_theory/ideal): `simp` lemmas for `ideal.quotient.mk` + `algebra_map` ([#9829](https://github.com/leanprover-community/mathlib/pull/9829))
Some `simp` lemmas I needed for combining `algebra_map` with `ideal.quotient.mk`. This also allowed me to golf two existing proofs.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient.algebra_map_eq
- \+ *lemma* quotient.mk_comp_algebra_map
- \+ *lemma* quotient.mk_algebra_map
- \+ *lemma* quotient_map_algebra_map



## [2021-10-23 17:11:07](https://github.com/leanprover-community/mathlib/commit/44ab28e)
refactor(linear_algebra/free_module/finite): move to a new folder ([#9821](https://github.com/leanprover-community/mathlib/pull/9821))
We move `linear_algebra/free_module/finite` to `linear_algebra/free_module/finite/basic`.
We also move two lemmas from `linear_algebra/free_module/finite/basic` to `linear_algebra/free_module/basic`, since they don't need any finiteness assumption on the modules.
#### Estimated changes
modified src/linear_algebra/charpoly/basic.lean

modified src/linear_algebra/free_module/basic.lean

renamed src/linear_algebra/free_module/finite.lean to src/linear_algebra/free_module/finite/basic.lean



## [2021-10-23 14:30:44](https://github.com/leanprover-community/mathlib/commit/a58ae54)
chore(algebra/big_operators/finprod): remove outdated todo ([#9900](https://github.com/leanprover-community/mathlib/pull/9900))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean



## [2021-10-23 14:30:43](https://github.com/leanprover-community/mathlib/commit/bd81d55)
feat(data/finsupp): add lemmas about `single` ([#9894](https://github.com/leanprover-community/mathlib/pull/9894))
These are subset versions of the four lemmas related to `support_eq_singleton`.
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* support_subset_singleton
- \+ *lemma* support_subset_singleton'
- \+ *lemma* card_support_le_one
- \+ *lemma* card_support_le_one'



## [2021-10-23 14:30:42](https://github.com/leanprover-community/mathlib/commit/95535a3)
refactor(ring_theory/unique_factorization_domain): golf some factor_set lemmas ([#9889](https://github.com/leanprover-community/mathlib/pull/9889))
#### Estimated changes
modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* factor_set.prod_eq_zero_iff
- \+ *theorem* factor_set.unique
- \+/\- *theorem* factors'_cong
- \+/\- *theorem* prod_factors
- \+/\- *theorem* factors'_cong
- \+/\- *theorem* prod_factors



## [2021-10-23 14:30:41](https://github.com/leanprover-community/mathlib/commit/e1c0dbc)
feat(set_theory/cardinal): add `add_le_omega` ([#9887](https://github.com/leanprover-community/mathlib/pull/9887))
* simplify `c₁ + c₂ ≤ ω` to `c₁ ≤ ω ∧ c₂ ≤ ω`;
* simplify `ω + ω` to `ω`;
* simplify `#s ≤ ω` to `s.countable`;
* simplify `(s ∪ t).countable` and `(insert a s).countable`.
Motivated by lemmas from flypitch.
#### Estimated changes
modified src/data/real/cardinality.lean

modified src/data/set/countable.lean
- \+ *lemma* countable_union
- \+ *lemma* countable_insert

modified src/set_theory/cardinal.lean
- \+ *lemma* mk_set_le_omega
- \+ *lemma* omega_add_omega
- \+ *lemma* omega_mul_omega
- \+ *lemma* add_le_omega
- \+ *lemma* mk_union_le_omega
- \- *lemma* countable_iff

modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* succ_omega

modified src/set_theory/cofinality.lean
- \+ *lemma* is_regular.pos
- \+ *lemma* is_regular.ord_pos



## [2021-10-23 14:30:40](https://github.com/leanprover-community/mathlib/commit/82896b5)
feat(topology): add a few lemmas ([#9885](https://github.com/leanprover-community/mathlib/pull/9885))
Add `is_topological_basis.is_open_map_iff`,
`is_topological_basis.exists_nonempty_subset`, and
`interior_{s,b,}Inter_subset`.
Motivated by lemmas from `flypitch`.
#### Estimated changes
modified src/topology/bases.lean
- \+ *lemma* is_topological_basis.is_open_map_iff
- \+ *lemma* is_topological_basis.exists_nonempty_subset

modified src/topology/basic.lean
- \+ *lemma* interior_Inter_subset
- \+ *lemma* interior_bInter_subset
- \+ *lemma* interior_sInter_subset



## [2021-10-23 14:30:39](https://github.com/leanprover-community/mathlib/commit/1e0661c)
feat(ring_theory/noetherian): generalize to semiring ([#9881](https://github.com/leanprover-community/mathlib/pull/9881))
We generalize some of the results in `ring_theory/noetherian` to `semiring`.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)
#### Estimated changes
modified src/ring_theory/algebra_tower.lean

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/finiteness.lean
- \+/\- *lemma* of_injective
- \+/\- *lemma* of_injective

modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_of_fg_map_injective
- \+/\- *lemma* fg_of_fg_map
- \+/\- *lemma* fg_top
- \+/\- *lemma* is_noetherian_of_injective
- \+/\- *lemma* fg_of_injective
- \+ *lemma* is_noetherian_of_ker_bot
- \+ *lemma* fg_of_ker_bot
- \+/\- *lemma* fg_of_fg_map
- \+/\- *lemma* fg_top
- \+/\- *lemma* is_noetherian_of_injective
- \+/\- *lemma* fg_of_injective



## [2021-10-23 14:30:38](https://github.com/leanprover-community/mathlib/commit/bb71667)
feat(topology/instances/irrational): new file ([#9872](https://github.com/leanprover-community/mathlib/pull/9872))
* move `is_Gδ_irrational` etc to a new file `topology.instances.irrational`;
* prove that a small ball around an irrational number is disjoint with the set of rational numbers with bounded denominators;
* prove `order_topology`, `no_top_order`, `no_bot_order`, and `densely_ordered` instances for `{x // irrational x}`.
#### Estimated changes
modified src/number_theory/liouville/residual.lean
- \- *lemma* is_Gδ_irrational
- \- *lemma* dense_irrational
- \- *lemma* eventually_residual_irrational

created src/topology/instances/irrational.lean
- \+ *lemma* is_Gδ_irrational
- \+ *lemma* dense_irrational
- \+ *lemma* eventually_residual_irrational
- \+ *lemma* eventually_forall_le_dist_cast_div
- \+ *lemma* eventually_forall_le_dist_cast_div_of_denom_le
- \+ *lemma* eventually_forall_le_dist_cast_rat_of_denom_le



## [2021-10-23 14:30:37](https://github.com/leanprover-community/mathlib/commit/b877f6b)
chore(analysis/normed/group): generalize `cauchy_seq.add` ([#9868](https://github.com/leanprover-community/mathlib/pull/9868))
Also golf a few proofs.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* cauchy_seq_sum_of_eventually_eq
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_sub_eq_zero_iff
- \- *lemma* cauchy_seq.add
- \+/\- *lemma* cauchy_seq_sum_of_eventually_eq
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_sub_eq_zero_iff

modified src/topology/algebra/uniform_group.lean
- \+ *lemma* cauchy_seq.add



## [2021-10-23 14:30:36](https://github.com/leanprover-community/mathlib/commit/29c7266)
refactor(linear_algebra/matrix/nonsingular_inverse): use ring.inverse in matrix.has_inv ([#9863](https://github.com/leanprover-community/mathlib/pull/9863))
This makes some of the proofs a little shorter.
Independently, this removes an assumption from `matrix.transpose_nonsing_inv`.
This adds the missing `units.is_unit_units_mul` to complement the existing `units.is_unit_mul_units`, even though it ultimately was not used in this PR.
This removes the def `matrix.nonsing_inv` in favor of just using `has_inv.inv` directly. Having two ways to spell the same thing isn't helpful here.
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/algebra/group/units.lean
- \+/\- *lemma* is_unit.mul
- \+/\- *lemma* is_unit.mul
- \+ *theorem* units.is_unit_units_mul

modified src/algebra/ring/basic.lean
- \+ *lemma* mul_inverse_rev

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/matrix/fpow.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* inv_def
- \+/\- *lemma* transpose_nonsing_inv
- \+/\- *lemma* mul_inv_rev
- \+/\- *lemma* inv_def
- \+/\- *lemma* transpose_nonsing_inv
- \+/\- *lemma* mul_inv_rev



## [2021-10-23 14:30:35](https://github.com/leanprover-community/mathlib/commit/2a1f454)
refactor(algebra/algebra): choose `coe` as the normal form for the map `alg_equiv → ring_equiv` ([#9848](https://github.com/leanprover-community/mathlib/pull/9848))
We never chose a `simp`-normal form for this map, resulting in some duplicate work and annoying `show _ = _, from rfl` when rewriting. I picked this choice because it matches the convention for the map `alg_hom → ring_hom`.
Very surprisingly, there were absolutely no CI failures due to this choice.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* to_ring_equiv_eq_coe
- \+/\- *lemma* coe_ring_equiv'
- \+/\- *lemma* coe_ring_equiv'



## [2021-10-23 14:30:34](https://github.com/leanprover-community/mathlib/commit/5f11361)
refactor(algebra/continued_fractions): remove use of open ... as ([#9847](https://github.com/leanprover-community/mathlib/pull/9847))
Lean 4 doesn't support the use of `open ... as ...`, so let's get rid of the few uses from mathlib rather than automating it in mathport.
#### Estimated changes
modified src/algebra/continued_fractions/basic.lean
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *lemma* coe_to_simple_continued_fraction
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *lemma* coe_to_simple_continued_fraction
- \+/\- *lemma* coe_to_generalized_continued_fraction
- \+/\- *def* map
- \+/\- *def* of_integer
- \+/\- *def* partial_numerators
- \+/\- *def* partial_denominators
- \+/\- *def* terminated_at
- \+/\- *def* terminates
- \+/\- *def* of_integer
- \+/\- *def* of_integer
- \+/\- *def* next_continuants
- \+/\- *def* continuants_aux
- \+/\- *def* continuants
- \+/\- *def* numerators
- \+/\- *def* denominators
- \+/\- *def* convergents
- \+/\- *def* convergents'_aux
- \+/\- *def* convergents'
- \+/\- *def* map
- \+/\- *def* of_integer
- \+/\- *def* partial_numerators
- \+/\- *def* partial_denominators
- \+/\- *def* terminated_at
- \+/\- *def* terminates
- \+/\- *def* of_integer
- \+/\- *def* of_integer
- \+/\- *def* next_continuants
- \+/\- *def* continuants_aux
- \+/\- *def* continuants
- \+/\- *def* numerators
- \+/\- *def* denominators
- \+/\- *def* convergents
- \+/\- *def* convergents'_aux
- \+/\- *def* convergents'

modified src/algebra/continued_fractions/computation/approximation_corollaries.lean
- \+/\- *lemma* of_convergents_eq_convergents'
- \+/\- *lemma* of_convergents_eq_convergents'

modified src/algebra/continued_fractions/computation/approximations.lean
- \+/\- *lemma* of_part_num_eq_one_and_exists_int_part_denom_eq
- \+/\- *lemma* of_part_num_eq_one
- \+/\- *lemma* fib_le_of_continuants_aux_b
- \+/\- *lemma* succ_nth_fib_le_of_nth_denom
- \+/\- *lemma* zero_le_of_continuants_aux_b
- \+/\- *lemma* zero_le_of_denom
- \+/\- *lemma* determinant_aux
- \+/\- *lemma* determinant
- \+/\- *lemma* of_part_num_eq_one_and_exists_int_part_denom_eq
- \+/\- *lemma* of_part_num_eq_one
- \+/\- *lemma* fib_le_of_continuants_aux_b
- \+/\- *lemma* succ_nth_fib_le_of_nth_denom
- \+/\- *lemma* zero_le_of_continuants_aux_b
- \+/\- *lemma* zero_le_of_denom
- \+/\- *lemma* determinant_aux
- \+/\- *lemma* determinant
- \+/\- *theorem* of_denom_mono
- \+/\- *theorem* abs_sub_convergents_le
- \+/\- *theorem* of_denom_mono
- \+/\- *theorem* abs_sub_convergents_le

modified src/algebra/continued_fractions/computation/basic.lean

modified src/algebra/continued_fractions/computation/correctness_terminating.lean
- \+/\- *lemma* of_correctness_of_terminates
- \+/\- *lemma* of_correctness_at_top_of_terminates
- \+/\- *lemma* of_correctness_of_terminates
- \+/\- *lemma* of_correctness_at_top_of_terminates
- \+/\- *theorem* of_correctness_of_terminated_at
- \+/\- *theorem* of_correctness_of_terminated_at

modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean
- \+/\- *lemma* exists_rat_eq_nth_numerator
- \+/\- *lemma* exists_rat_eq_nth_denominator
- \+/\- *lemma* exists_rat_eq_nth_convergent
- \+/\- *lemma* coe_of_h_rat_eq
- \+/\- *lemma* coe_of_s_rat_eq
- \+/\- *lemma* coe_of_rat_eq
- \+/\- *lemma* exists_rat_eq_nth_numerator
- \+/\- *lemma* exists_rat_eq_nth_denominator
- \+/\- *lemma* exists_rat_eq_nth_convergent
- \+/\- *lemma* coe_of_h_rat_eq
- \+/\- *lemma* coe_of_s_rat_eq
- \+/\- *lemma* coe_of_rat_eq
- \+/\- *theorem* exists_rat_eq_of_terminates
- \+/\- *theorem* terminates_of_rat
- \+/\- *theorem* terminates_iff_rat
- \+/\- *theorem* exists_rat_eq_of_terminates
- \+/\- *theorem* terminates_of_rat
- \+/\- *theorem* terminates_iff_rat

modified src/algebra/continued_fractions/computation/translations.lean
- \+/\- *lemma* of_h_eq_int_fract_pair_seq1_fst_b
- \+/\- *lemma* of_h_eq_floor
- \+/\- *lemma* int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some
- \+/\- *lemma* of_h_eq_int_fract_pair_seq1_fst_b
- \+/\- *lemma* of_h_eq_floor
- \+/\- *lemma* int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some

modified src/algebra/continued_fractions/continuants_recurrence.lean
- \+/\- *lemma* continuants_aux_recurrence
- \+/\- *lemma* continuants_recurrence_aux
- \+/\- *lemma* numerators_recurrence
- \+/\- *lemma* denominators_recurrence
- \+/\- *lemma* continuants_aux_recurrence
- \+/\- *lemma* continuants_recurrence_aux
- \+/\- *lemma* numerators_recurrence
- \+/\- *lemma* denominators_recurrence
- \+/\- *theorem* continuants_recurrence
- \+/\- *theorem* continuants_recurrence

modified src/algebra/continued_fractions/convergents_equiv.lean
- \+/\- *lemma* squash_seq_nth_of_not_terminated
- \+/\- *lemma* squash_seq_nth_of_not_terminated
- \+/\- *theorem* convergents_eq_convergents'
- \+/\- *theorem* convergents_eq_convergents'
- \+/\- *def* squash_seq
- \+/\- *def* squash_gcf
- \+/\- *def* squash_seq
- \+/\- *def* squash_gcf

modified src/algebra/continued_fractions/terminated_stable.lean
- \+/\- *lemma* convergents'_aux_stable_step_of_terminated
- \+/\- *lemma* convergents'_aux_stable_of_terminated
- \+/\- *lemma* convergents'_aux_stable_step_of_terminated
- \+/\- *lemma* convergents'_aux_stable_of_terminated

modified src/algebra/continued_fractions/translations.lean
- \+/\- *lemma* part_num_eq_s_a
- \+/\- *lemma* part_denom_eq_s_b
- \+/\- *lemma* second_continuant_aux_eq
- \+/\- *lemma* first_continuant_eq
- \+/\- *lemma* first_numerator_eq
- \+/\- *lemma* first_denominator_eq
- \+/\- *lemma* zeroth_convergent'_aux_eq_zero
- \+/\- *lemma* part_num_eq_s_a
- \+/\- *lemma* part_denom_eq_s_b
- \+/\- *lemma* second_continuant_aux_eq
- \+/\- *lemma* first_continuant_eq
- \+/\- *lemma* first_numerator_eq
- \+/\- *lemma* first_denominator_eq
- \+/\- *lemma* zeroth_convergent'_aux_eq_zero



## [2021-10-23 13:13:59](https://github.com/leanprover-community/mathlib/commit/7b979aa)
move(algebra/order/*): More algebraic order files in the correct place ([#9899](https://github.com/leanprover-community/mathlib/pull/9899))
`algebra.module.ordered` and `algebra.algebra.ordered` were really continuations of `algebra.order.smul` (the first being quite literally the same with additive inverses), so it makes sense to bring them closer. `algebra.floor` and `algebra.archimedean` also perfectly qualify for the subfolder.
#### Estimated changes
modified src/algebra/continued_fractions/computation/basic.lean

renamed src/algebra/algebra/ordered.lean to src/algebra/order/algebra.lean

renamed src/algebra/archimedean.lean to src/algebra/order/archimedean.lean

renamed src/algebra/floor.lean to src/algebra/order/floor.lean

renamed src/algebra/module/ordered.lean to src/algebra/order/module.lean

modified src/algebra/order/nonneg.lean

modified src/algebra/periodic.lean

modified src/algebra/star/chsh.lean

modified src/analysis/convex/basic.lean

modified src/data/complex/module.lean

modified src/data/rat/floor.lean

modified src/data/real/basic.lean

modified src/data/real/pointwise.lean

modified src/group_theory/archimedean.lean

modified src/linear_algebra/affine_space/ordered.lean

modified src/order/filter/archimedean.lean

modified src/topology/algebra/floor_ring.lean



## [2021-10-23 08:22:49](https://github.com/leanprover-community/mathlib/commit/eb1e037)
doc(algebra/ring): correct docs for surjective pushforwards ([#9896](https://github.com/leanprover-community/mathlib/pull/9896))
#### Estimated changes
modified src/algebra/ring/basic.lean



## [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/a75f762)
feat(ring_theory/localization): generalize `exist_integer_multiples` to finite families ([#9859](https://github.com/leanprover-community/mathlib/pull/9859))
This PR shows we can clear denominators of finitely-indexed collections of fractions (i.e. elements of `S` where `is_localization M S`), with the existing result about finite sets of fractions as a special case.
#### Estimated changes
modified src/ring_theory/localization.lean
- \+ *lemma* exist_integer_multiples
- \+ *lemma* exist_integer_multiples_of_fintype
- \+/\- *lemma* exist_integer_multiples_of_finset
- \+/\- *lemma* exist_integer_multiples_of_finset



## [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/294ce35)
fix(algebra/module/submodule): fix incorrectly generalized arguments to `smul_mem_iff'` and `smul_of_tower_mem` ([#9851](https://github.com/leanprover-community/mathlib/pull/9851))
These put unnecessary requirements on `S`.
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* coe_smul_of_tower
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* coe_smul_of_tower

modified src/group_theory/group_action/sub_mul_action.lean
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'

modified src/topology/algebra/module.lean



## [2021-10-23 08:22:47](https://github.com/leanprover-community/mathlib/commit/2cbd4ba)
feat(group_theory/index): `relindex_dvd_of_le_left` ([#9835](https://github.com/leanprover-community/mathlib/pull/9835))
If `H ≤ K`, then `K.relindex L ∣ H.relindex L`.
Caution: `relindex_dvd_of_le_right` is not true. `relindex_le_of_le_right` is true, but it is harder to prove, and harder to state (because you have to be careful about `relindex = 0`).
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* inf_relindex_right
- \+ *lemma* inf_relindex_left
- \+ *lemma* relindex_dvd_of_le_left



## [2021-10-23 05:53:41](https://github.com/leanprover-community/mathlib/commit/183b8c8)
refactor(data/list/defs): move defs about rb_map ([#9844](https://github.com/leanprover-community/mathlib/pull/9844))
There is nothing intrinsically `meta` about `rb_map`, but in practice in mathlib we prove nothing about it and only use it in tactic infrastructure. This PR moves a definition involving `rb_map` out of `data.list.defs` and into `meta.rb_map` (where many others already exist).
(motivated by mathport; rb_map is of course disappearing/changing, so better to quarantine this stuff off with other things that aren't being automatically ported)
`rbmap` is not related to `rb_map`. It can likely be moved from core to mathlib entirely.
#### Estimated changes
modified src/data/list/defs.lean
- \+/\- *def* to_rbmap
- \+/\- *def* to_rbmap

modified src/meta/rb_map.lean



## [2021-10-23 02:55:56](https://github.com/leanprover-community/mathlib/commit/45ba2ad)
chore(scripts): update nolints.txt ([#9895](https://github.com/leanprover-community/mathlib/pull/9895))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-10-22 22:06:02](https://github.com/leanprover-community/mathlib/commit/7690e0a)
chore(order/complete_lattice): add `(supr|infi)_option_elim` ([#9886](https://github.com/leanprover-community/mathlib/pull/9886))
Motivated by `supr_option'` and `infi_option'` from `flypitch`.
#### Estimated changes
modified src/order/complete_lattice.lean
- \+ *lemma* supr_option_elim
- \+ *lemma* infi_option_elim



## [2021-10-22 20:15:57](https://github.com/leanprover-community/mathlib/commit/72c20fa)
feat(analysis/special_functions/exp_log): Classify when log is zero ([#9815](https://github.com/leanprover-community/mathlib/pull/9815))
Classify when the real `log` function is zero.
#### Estimated changes
modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* log_eq_zero



## [2021-10-22 15:58:28](https://github.com/leanprover-community/mathlib/commit/d23b833)
chore(data/set/lattice): add `@[simp]` to a few lemmas ([#9883](https://github.com/leanprover-community/mathlib/pull/9883))
Add `@[simp]` to `Union_subset_iff`, `subset_Inter_iff`,
`sUnion_subset_iff`, and `subset_sInter_iff` (new lemma).
#### Estimated changes
modified src/data/set/lattice.lean
- \+/\- *theorem* Union_subset_iff
- \+/\- *theorem* subset_Inter_iff
- \+/\- *theorem* sUnion_subset_iff
- \+ *theorem* subset_sInter_iff
- \+/\- *theorem* Union_subset_iff
- \+/\- *theorem* subset_Inter_iff
- \+/\- *theorem* sUnion_subset_iff



## [2021-10-22 15:58:26](https://github.com/leanprover-community/mathlib/commit/3d237db)
feat(linear_algebra/matrix/determinant): det_conj_transpose ([#9879](https://github.com/leanprover-community/mathlib/pull/9879))
Also:
* Makes the arguments of `ring_hom.map_det` and `alg_hom.map_det` explicit, and removes them from the `matrix` namespace to enable dot notation.
* Adds `ring_equiv.map_det` and `alg_equiv.map_det`
#### Estimated changes
modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* _root_.ring_hom.map_det
- \+ *lemma* _root_.ring_equiv.map_det
- \+ *lemma* _root_.alg_hom.map_det
- \+ *lemma* _root_.alg_equiv.map_det
- \+ *lemma* det_conj_transpose
- \- *lemma* ring_hom.map_det
- \- *lemma* alg_hom.map_det

modified src/ring_theory/trace.lean



## [2021-10-22 15:58:25](https://github.com/leanprover-community/mathlib/commit/20bb02f)
feat(data/fintype/basic): `fintype.card_pos` ([#9876](https://github.com/leanprover-community/mathlib/pull/9876))
Two lemmas `fintype.card_pos` and `fintype.card_ne_zero` that are often easier to use than `fintype.card_pos_iff`.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* card_pos
- \+ *lemma* card_ne_zero



## [2021-10-22 15:58:24](https://github.com/leanprover-community/mathlib/commit/22c7474)
feat(algebra/module/basic): a few more instances ([#9871](https://github.com/leanprover-community/mathlib/pull/9871))
* generalize `is_scalar_tower.rat`;
* add `smul_comm_class.rat` and `smul_comm_class.rat'`;
* golf a few proofs.
#### Estimated changes
modified src/algebra/algebra/tower.lean

modified src/algebra/module/basic.lean



## [2021-10-22 15:58:23](https://github.com/leanprover-community/mathlib/commit/87ea780)
chore(set_theory/cardinal): use `protected` instead of `private` ([#9869](https://github.com/leanprover-community/mathlib/pull/9869))
Also use `mk_congr`.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+/\- *theorem* mk_emptyc
- \+/\- *theorem* mk_emptyc



## [2021-10-22 15:58:21](https://github.com/leanprover-community/mathlib/commit/d8b9259)
feat(*): add various divisibility-related lemmas ([#9866](https://github.com/leanprover-community/mathlib/pull/9866))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* irreducible.dvd_irreducible_iff_associated
- \+ *theorem* prime.dvd_prime_iff_associated
- \+ *theorem* mk_ne_zero

modified src/algebra/ring/basic.lean
- \+ *lemma* is_unit.neg_iff

modified src/ring_theory/int/basic.lean
- \+ *lemma* nonneg_of_normalize_eq_self
- \+ *lemma* nonneg_iff_normalize_eq_self
- \+ *lemma* eq_of_associated_of_nonneg

modified src/ring_theory/prime.lean
- \+ *lemma* prime.neg
- \+ *lemma* prime.abs



## [2021-10-22 15:58:20](https://github.com/leanprover-community/mathlib/commit/2955306)
feat(ring_theory/finiteness): generalize module.finite to noncommutative setting ([#9860](https://github.com/leanprover-community/mathlib/pull/9860))
An almost for free generalization of `module.finite` to `semiring`.
#### Estimated changes
modified src/ring_theory/finiteness.lean
- \+/\- *lemma* finite_def
- \+/\- *lemma* of_injective
- \+/\- *lemma* of_restrict_scalars_finite
- \+/\- *lemma* trans
- \+/\- *lemma* finite_def
- \+/\- *lemma* of_injective
- \+/\- *lemma* of_restrict_scalars_finite
- \+/\- *lemma* trans
- \+/\- *def* algebra.finite_presentation
- \+/\- *def* algebra.finite_presentation



## [2021-10-22 15:58:19](https://github.com/leanprover-community/mathlib/commit/0a7f448)
chore(group_theory/congruence): lower priority for `con.quotient.decidable_eq` ([#9826](https://github.com/leanprover-community/mathlib/pull/9826))
I was debugging some slow typeclass searches, and it turns out (`add_`)`con.quotient.decidable_eq` wants to be applied to all quotient types, causing a search for a `has_mul` instance before the elaborator can try unifying the `con.to_setoid` relation with the quotient type's relation, so e.g. `decidable_eq (multiset α)` first tries going all the way up to searching for a `linear_ordered_normed_etc_field (list α)` before even trying `multiset.decidable_eq`.
Another approach would be to make `multiset` and/or `con.quotient` irreducible, but that would require a lot more work to ensure we don't break the irreducibility barrier.
#### Estimated changes
modified src/group_theory/congruence.lean



## [2021-10-22 15:58:17](https://github.com/leanprover-community/mathlib/commit/03ba4cc)
feat(algebra/floor): Floor semirings ([#9592](https://github.com/leanprover-community/mathlib/pull/9592))
A floor semiring is a semiring equipped with a `floor` and a `ceil` function.
#### Estimated changes
modified src/algebra/floor.lean
- \+/\- *lemma* le_floor_iff
- \+ *lemma* le_floor
- \+ *lemma* floor_lt
- \+ *lemma* lt_of_floor_lt
- \+/\- *lemma* floor_le
- \+ *lemma* lt_succ_floor
- \+/\- *lemma* lt_floor_add_one
- \+/\- *lemma* floor_coe
- \+/\- *lemma* floor_zero
- \+ *lemma* floor_one
- \+/\- *lemma* floor_of_nonpos
- \+/\- *lemma* floor_mono
- \+ *lemma* le_floor_iff'
- \+ *lemma* floor_lt'
- \+/\- *lemma* floor_pos
- \+/\- *lemma* pos_of_floor_pos
- \+/\- *lemma* lt_of_lt_floor
- \+ *lemma* floor_eq_zero
- \+ *lemma* floor_eq_iff
- \+ *lemma* floor_eq_on_Ico
- \+ *lemma* floor_eq_on_Ico'
- \+ *lemma* gc_ceil_coe
- \+/\- *lemma* ceil_le
- \+/\- *lemma* lt_ceil
- \+/\- *lemma* le_ceil
- \+/\- *lemma* ceil_mono
- \+/\- *lemma* ceil_coe
- \+/\- *lemma* ceil_zero
- \+/\- *lemma* ceil_eq_zero
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+/\- *lemma* floor_lt_ceil_of_lt_of_pos
- \+/\- *lemma* floor_add_nat
- \+/\- *lemma* floor_add_one
- \+/\- *lemma* sub_one_lt_floor
- \+/\- *lemma* ceil_add_nat
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_lt_add_one
- \+ *lemma* floor_semiring_unique
- \+/\- *lemma* floor_ring_floor_eq
- \+/\- *lemma* floor_ring_ceil_eq
- \+ *lemma* floor_nonpos
- \+ *lemma* floor_to_nat
- \+ *lemma* ceil_to_nat
- \+/\- *lemma* floor_ring_floor_eq
- \+/\- *lemma* floor_ring_ceil_eq
- \+/\- *lemma* floor_of_nonpos
- \+/\- *lemma* floor_le
- \- *lemma* le_floor_of_le
- \+/\- *lemma* le_floor_iff
- \+/\- *lemma* floor_pos
- \+/\- *lemma* pos_of_floor_pos
- \+/\- *lemma* lt_of_lt_floor
- \- *lemma* floor_lt_iff
- \+/\- *lemma* floor_mono
- \+/\- *lemma* floor_coe
- \+/\- *lemma* floor_zero
- \+/\- *lemma* floor_add_nat
- \+/\- *lemma* floor_add_one
- \+/\- *lemma* lt_floor_add_one
- \+/\- *lemma* sub_one_lt_floor
- \- *lemma* floor_eq_zero_iff
- \+/\- *lemma* ceil_le
- \+/\- *lemma* lt_ceil
- \+/\- *lemma* le_ceil
- \+/\- *lemma* ceil_mono
- \+/\- *lemma* ceil_coe
- \+/\- *lemma* ceil_zero
- \+/\- *lemma* ceil_eq_zero
- \+/\- *lemma* ceil_add_nat
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_lt_add_one
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+/\- *lemma* floor_lt_ceil_of_lt_of_pos
- \+/\- *def* floor
- \+/\- *def* ceil
- \+/\- *def* floor
- \+/\- *def* ceil

modified src/data/int/basic.lean
- \+ *lemma* le_to_nat_iff

modified src/topology/metric_space/gromov_hausdorff.lean



## [2021-10-22 13:16:18](https://github.com/leanprover-community/mathlib/commit/bee8d4a)
chore(order/filter/basic): golf a proof ([#9874](https://github.com/leanprover-community/mathlib/pull/9874))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean

modified src/data/set/lattice.lean
- \+ *lemma* Union_coe_set
- \+ *lemma* Inter_coe_set
- \- *lemma* Union_subtype
- \+ *theorem* Union_subtype
- \+ *theorem* Inter_subtype

modified src/measure_theory/measure/measure_space_def.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* mem_infi_finset
- \+/\- *lemma* mem_infi_finset

modified src/topology/metric_space/hausdorff_dimension.lean

modified src/topology/paracompact.lean



## [2021-10-22 13:16:16](https://github.com/leanprover-community/mathlib/commit/b812fb9)
refactor(ring_theory/ideal): split off `quotient.lean` ([#9850](https://github.com/leanprover-community/mathlib/pull/9850))
Both `ring_theory/ideal/basic.lean` and `ring_theory/ideal/operations.lean` were starting to get a bit long, so I split off the definition of `ideal.quotient` and the results that had no further dependencies.
I also went through all the imports for files depending on either `ideal/basic.lean` or `ideal/operations.lean` to check whether they shouldn't depend on `ideal/quotient.lean` instead.
#### Estimated changes
modified src/algebra/ring_quot.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/invariant_basis_number.lean

modified src/linear_algebra/smodeq.lean

modified src/number_theory/basic.lean

modified src/ring_theory/finiteness.lean

modified src/ring_theory/ideal/basic.lean
- \- *lemma* ring_hom_ext
- \- *lemma* eq_zero_iff_mem
- \- *lemma* mk_surjective
- \- *lemma* quotient_ring_saturate
- \- *lemma* is_domain_iff_prime
- \- *lemma* exists_inv
- \- *lemma* lift_mk
- \- *lemma* factor_mk
- \- *lemma* factor_comp_mk
- \- *lemma* quot_equiv_of_eq_mk
- \- *lemma* map_pi
- \- *theorem* mk_eq_mk
- \- *theorem* zero_eq_one_iff
- \- *theorem* zero_ne_one_iff
- \- *theorem* maximal_of_is_field
- \- *theorem* maximal_ideal_iff_is_field_quotient
- \- *def* quotient
- \- *def* mk
- \- *def* lift
- \- *def* factor
- \- *def* quot_equiv_of_eq

modified src/ring_theory/ideal/local_ring.lean

modified src/ring_theory/ideal/operations.lean
- \- *theorem* exists_sub_one_mem_and_mem
- \- *theorem* exists_sub_mem
- \- *theorem* quotient_inf_to_pi_quotient_bijective
- \- *def* quotient_inf_to_pi_quotient

created src/ring_theory/ideal/quotient.lean
- \+ *lemma* ring_hom_ext
- \+ *lemma* eq_zero_iff_mem
- \+ *lemma* mk_surjective
- \+ *lemma* quotient_ring_saturate
- \+ *lemma* is_domain_iff_prime
- \+ *lemma* exists_inv
- \+ *lemma* lift_mk
- \+ *lemma* factor_mk
- \+ *lemma* factor_comp_mk
- \+ *lemma* quot_equiv_of_eq_mk
- \+ *lemma* map_pi
- \+ *theorem* mk_eq_mk
- \+ *theorem* zero_eq_one_iff
- \+ *theorem* zero_ne_one_iff
- \+ *theorem* maximal_of_is_field
- \+ *theorem* maximal_ideal_iff_is_field_quotient
- \+ *theorem* exists_sub_one_mem_and_mem
- \+ *theorem* exists_sub_mem
- \+ *theorem* quotient_inf_to_pi_quotient_bijective
- \+ *def* quotient
- \+ *def* mk
- \+ *def* lift
- \+ *def* factor
- \+ *def* quot_equiv_of_eq
- \+ *def* quotient_inf_to_pi_quotient

modified src/ring_theory/jacobson_ideal.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/mv_polynomial/basic.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/valuation/basic.lean

modified src/topology/algebra/nonarchimedean/adic_topology.lean

modified src/topology/algebra/ring.lean



## [2021-10-22 13:16:15](https://github.com/leanprover-community/mathlib/commit/e6c516d)
feat(topology/maps): Characterize open/closed maps in terms of images of interior/closure ([#9814](https://github.com/leanprover-community/mathlib/pull/9814))
Also provide the docstring for `inducing`.
#### Estimated changes
modified src/topology/maps.lean
- \+ *lemma* is_open_map_iff_interior
- \+ *lemma* closure_image_subset
- \+ *lemma* is_closed_map_iff_closure_image



## [2021-10-22 10:49:49](https://github.com/leanprover-community/mathlib/commit/43cd79f)
feat(data/finset/basic): Simple `finset.erase` lemmas ([#9878](https://github.com/leanprover-community/mathlib/pull/9878))
`finset.erase.singleton` and `finset.(map/image)_erase`
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* erase_singleton
- \+ *lemma* image_erase
- \+ *lemma* map_erase



## [2021-10-22 06:47:53](https://github.com/leanprover-community/mathlib/commit/76212e6)
feat(measure_theory/integral/set_integral): integral of a `is_R_or_C` function equals integral of real part + integral of imaginary part ([#9735](https://github.com/leanprover-community/mathlib/pull/9735))
#### Estimated changes
modified src/data/complex/is_R_or_C.lean
- \+ *lemma* norm_of_real

modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* integrable.of_real
- \+ *lemma* integrable.re_im_iff

modified src/measure_theory/function/lp_space.lean
- \+ *lemma* lipschitz_with.comp_mem_ℒp
- \+ *lemma* measure_theory.mem_ℒp.of_comp_antilipschitz_with
- \+ *lemma* comp_mem_ℒp
- \+ *lemma* comp_mem_ℒp'
- \+ *lemma* _root_.measure_theory.mem_ℒp.of_real
- \+ *lemma* _root_.measure_theory.mem_ℒp_re_im_iff

modified src/measure_theory/function/special_functions.lean
- \+ *lemma* is_R_or_C.measurable_of_real
- \+ *lemma* measurable_of_re_im
- \+ *lemma* ae_measurable_of_re_im

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* integral_coe_re_add_coe_im
- \+ *lemma* integral_re_add_im
- \+ *lemma* set_integral_re_add_im

modified test/measurability.lean



## [2021-10-22 01:15:49](https://github.com/leanprover-community/mathlib/commit/c4c71d2)
feat(topology): define class `[noncompact_space]` ([#9839](https://github.com/leanprover-community/mathlib/pull/9839))
#### Estimated changes
modified src/topology/alexandroff.lean
- \+/\- *lemma* dense_range_coe
- \+/\- *lemma* dense_embedding_coe
- \+/\- *lemma* dense_range_coe
- \+/\- *lemma* dense_embedding_coe

modified src/topology/instances/real.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* ediam_univ_eq_top_iff_noncompact
- \+ *lemma* ediam_univ_of_noncompact
- \+ *lemma* diam_univ_of_noncompact

modified src/topology/subset_properties.lean
- \+ *lemma* noncompact_space_of_ne_bot
- \+ *lemma* filter.cocompact_ne_bot_iff
- \+ *lemma* not_compact_space_iff
- \+/\- *lemma* filter.coprod_cocompact
- \+ *lemma* prod.noncompact_space_iff
- \- *lemma* filter.cocompact_ne_bot_tfae
- \+/\- *lemma* filter.coprod_cocompact



## [2021-10-21 23:04:20](https://github.com/leanprover-community/mathlib/commit/6f837a6)
feat(data/polynomial): generalize and rename `polynomial.normalize_monic` ([#9853](https://github.com/leanprover-community/mathlib/pull/9853))
This PR renames `polynomial.normalize_monic` to `polynomial.monic.normalize_eq_self` (more dot notation!) and generalizes it from fields to `normalization_monoid`s.
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \+ *lemma* monic.normalize_eq_self
- \- *lemma* normalize_monic



## [2021-10-21 23:04:19](https://github.com/leanprover-community/mathlib/commit/16a9031)
refactor(data/complex/*): replace `complex.conj` and `is_R_or_C.conj` with star ([#9640](https://github.com/leanprover-community/mathlib/pull/9640))
This PR replaces `complex.conj` and `is_R_or_C.conj` by the star operation defined in `algebra/star`. Both of these are replaced with `star_ring_aut`, which is also made available under the notation `conj` defined in the locale `complex_conjugate`. This effectively also upgrades conj from a `ring_hom` to a `ring_aut`.
Fixes [#9421](https://github.com/leanprover-community/mathlib/pull/9421)
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* star_ring_aut_apply
- \+ *lemma* star_ring_aut_self_apply

modified src/analysis/complex/basic.lean
- \+/\- *lemma* continuous_conj
- \+/\- *lemma* conj_cle_apply
- \+/\- *lemma* continuous_conj
- \+/\- *lemma* conj_cle_apply
- \- *lemma* conj_to_complex

modified src/analysis/complex/circle.lean
- \+/\- *lemma* coe_inv_circle_eq_conj
- \+/\- *lemma* coe_inv_circle_eq_conj

modified src/analysis/complex/conformal.lean

modified src/analysis/complex/isometry.lean

modified src/analysis/complex/real_deriv.lean

modified src/analysis/fourier.lean
- \+/\- *lemma* fourier_neg
- \+/\- *lemma* fourier_neg

modified src/analysis/inner_product_space/basic.lean
- \+/\- *lemma* real_inner_comm
- \+/\- *lemma* real_inner_comm

modified src/analysis/inner_product_space/dual.lean

modified src/analysis/inner_product_space/pi_L2.lean

modified src/analysis/inner_product_space/projection.lean

modified src/data/complex/basic.lean
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_of_real
- \- *lemma* conj_conj
- \- *lemma* conj_involutive
- \- *lemma* conj_bijective
- \- *lemma* conj_inj
- \- *lemma* conj_eq_zero
- \- *lemma* conj_sub
- \- *lemma* conj_one
- \- *def* conj

modified src/data/complex/exponential.lean

modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* abs_sq_re_add_conj
- \+/\- *lemma* abs_sq_re_add_conj'
- \+/\- *lemma* conj_mul_eq_norm_sq_left
- \+/\- *lemma* conj_to_real
- \- *lemma* conj_conj
- \- *lemma* conj_involutive
- \- *lemma* conj_bijective
- \- *lemma* conj_inj
- \- *lemma* conj_eq_zero
- \- *lemma* ring_equiv_apply
- \- *lemma* conj_inv
- \- *lemma* conj_div
- \+/\- *lemma* abs_sq_re_add_conj
- \+/\- *lemma* abs_sq_re_add_conj'
- \+/\- *lemma* conj_mul_eq_norm_sq_left
- \+/\- *lemma* conj_to_real
- \- *def* conj_to_ring_equiv

modified src/data/complex/module.lean

modified src/linear_algebra/clifford_algebra/equivs.lean
- \+/\- *lemma* of_complex_conj
- \+/\- *lemma* of_complex_conj

modified src/measure_theory/function/l2_space.lean

modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_conj
- \+/\- *lemma* integral_conj



## [2021-10-21 20:06:24](https://github.com/leanprover-community/mathlib/commit/912039d)
feat(algebra/group_power/lemmas): Positivity of an odd/even power ([#9796](https://github.com/leanprover-community/mathlib/pull/9796))
This adds `odd.pow_nonneg` and co and `pow_right_comm`.
This also deletes `pow_odd_nonneg` and `pow_odd_pos` as they are special cases of `pow_nonneg` and `pow_pos`.
To make dot notation work, this renames `(pow/fpow)_(odd/even)_(nonneg/nonpos/pos/neg/abs)` to `(odd/even).(pow/fpow)_(nonneg/nonpos/pos/neg/abs)`
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* even.fpow_neg
- \+ *lemma* even.fpow_nonneg
- \+ *lemma* even.fpow_abs
- \+/\- *lemma* fpow_bit0_abs
- \+ *lemma* even.abs_fpow
- \- *lemma* fpow_even_neg
- \- *lemma* fpow_even_nonneg
- \- *lemma* fpow_even_abs
- \+/\- *lemma* fpow_bit0_abs
- \- *lemma* abs_fpow_even
- \+ *theorem* even.fpow_pos
- \+ *theorem* odd.fpow_nonneg
- \+ *theorem* odd.fpow_pos
- \+ *theorem* odd.fpow_nonpos
- \+ *theorem* odd.fpow_neg
- \- *theorem* fpow_even_pos
- \- *theorem* fpow_odd_nonneg
- \- *theorem* fpow_odd_pos
- \- *theorem* fpow_odd_nonpos
- \- *theorem* fpow_odd_neg

modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_right_comm

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* even.pow_nonneg
- \+ *lemma* even.pow_pos
- \+ *lemma* odd.pow_nonpos
- \+ *lemma* odd.pow_neg
- \+ *lemma* odd.pow_nonneg_iff
- \+ *lemma* odd.pow_nonpos_iff
- \+ *lemma* odd.pow_pos_iff
- \+ *lemma* odd.pow_neg_iff
- \+ *lemma* even.pow_pos_iff
- \+ *lemma* even.pow_abs
- \+/\- *lemma* pow_bit0_abs
- \- *lemma* pow_even_abs
- \+/\- *lemma* pow_bit0_abs
- \- *theorem* pow_even_nonneg
- \- *theorem* pow_even_pos
- \- *theorem* pow_odd_nonneg
- \- *theorem* pow_odd_pos
- \- *theorem* pow_odd_nonpos
- \- *theorem* pow_odd_neg



## [2021-10-21 18:28:20](https://github.com/leanprover-community/mathlib/commit/15d4e5f)
refactor(data/real/ennreal): remove sub lemmas ([#9857](https://github.com/leanprover-community/mathlib/pull/9857))
* Remove all lemmas about subtraction on `ennreal` that are special cases of `has_ordered_sub` lemmas.
* [This](https://github.com/leanprover-community/mathlib/blob/fe5ddaf42c5d61ecc740e815d63ac38f5e94a2e8/src/data/real/ennreal.lean#L734-L795) gives a list of renamings.
* The lemmas that have a `@[simp]` attribute will be done in a separate PR
#### Estimated changes
modified src/analysis/analytic/basic.lean

modified src/analysis/box_integral/integrability.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* mul_sub
- \- *lemma* le_sub_add_self
- \- *lemma* sub_self
- \- *lemma* zero_sub
- \- *lemma* sub_le_sub
- \- *lemma* sub_add_self_eq_max
- \- *lemma* sub_le_self
- \- *lemma* sub_zero
- \- *lemma* sub_le_sub_add_sub
- \- *lemma* lt_sub_iff_add_lt
- \- *lemma* lt_sub_comm
- \+/\- *lemma* mul_sub

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/content.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/regular.lean

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/contracting.lean



## [2021-10-21 18:28:19](https://github.com/leanprover-community/mathlib/commit/5b72c4e)
feat(linear_algebra/quotient): `S.restrict_scalars.quotient` is `S.quotient` ([#9535](https://github.com/leanprover-community/mathlib/pull/9535))
This PR adds a more general module instance on submodule quotients, in order to show that `(S.restrict_scalars R).quotient` is equivalent to `S.quotient`. If we decide this instance is not a good idea, I can write it instead as `S.quotient.restrict_scalars`, but that is a bit less convenient to work with.
#### Estimated changes
modified src/linear_algebra/quotient.lean
- \+ *lemma* restrict_scalars_equiv_mk
- \+ *lemma* restrict_scalars_equiv_symm_mk
- \+/\- *theorem* mk_smul
- \+/\- *theorem* mk_smul
- \- *theorem* mk_nsmul
- \+ *def* restrict_scalars_equiv

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/finiteness.lean

modified src/ring_theory/ideal/operations.lean



## [2021-10-21 15:43:25](https://github.com/leanprover-community/mathlib/commit/9be8247)
feat(logic/function/embedding): add `function.embedding.option_elim` ([#9841](https://github.com/leanprover-community/mathlib/pull/9841))
* add `option.injective_iff`;
* add `function.embedding.option_elim`;
* use it in the proof of `cardinal.add_one_le_succ`;
* add `function.embedding.cardinal_le`, `cardinal.succ_pos`;
* add `@[simp]` to `cardinal.lt_succ`.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* option.injective_iff

modified src/logic/embedding.lean
- \+ *def* option_elim

modified src/set_theory/cardinal.lean
- \+ *lemma* succ_pos
- \+/\- *lemma* succ_ne_zero
- \+/\- *lemma* succ_ne_zero
- \+ *theorem* _root_.function.embedding.cardinal_le
- \+/\- *theorem* mk_option
- \+/\- *theorem* lt_succ
- \+/\- *theorem* add_one_le_succ
- \+/\- *theorem* lt_succ
- \+/\- *theorem* add_one_le_succ
- \+/\- *theorem* mk_option



## [2021-10-21 15:43:23](https://github.com/leanprover-community/mathlib/commit/14ec1c8)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate of a 2x2 matrix ([#9830](https://github.com/leanprover-community/mathlib/pull/9830))
Since we have `det_fin_two`, let's have `adjugate_fin_two` as well.
#### Estimated changes
modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* adjugate_fin_two
- \+ *lemma* adjugate_fin_two'



## [2021-10-21 15:43:20](https://github.com/leanprover-community/mathlib/commit/9c240b5)
feat(analysis/inner_product_space): define `orthogonal_family` of subspaces ([#9718](https://github.com/leanprover-community/mathlib/pull/9718))
Define `orthogonal_family` on `V : ι → submodule 𝕜 E` to mean that any two vectors from distinct subspaces are orthogonal.  Prove that an orthogonal family of subspaces is `complete_lattice.independent`.
Also prove that in finite dimension an orthogonal family `V` satisifies `direct_sum.submodule_is_internal` (i.e., it provides an internal direct sum decomposition of `E`) if and only if their joint orthogonal complement is trivial, `(supr V)ᗮ = ⊥`, and that in this case, the identification of `E` with the direct sum of `V` is an isometry.
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.eq_ite
- \+ *lemma* orthogonal_family.inner_right_dfinsupp
- \+ *lemma* orthogonal_family.inner_right_fintype
- \+ *lemma* orthogonal_family.independent
- \+ *def* orthogonal_family

modified src/analysis/inner_product_space/pi_L2.lean
- \+ *def* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family

modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* orthogonal_family.submodule_is_internal_iff



## [2021-10-21 13:16:18](https://github.com/leanprover-community/mathlib/commit/d8096aa)
fix(ring_theory/subring): `inclusion` is a ring_hom! ([#9849](https://github.com/leanprover-community/mathlib/pull/9849))
#### Estimated changes
modified src/ring_theory/subring.lean
- \+/\- *def* inclusion
- \+/\- *def* inclusion



## [2021-10-21 13:16:17](https://github.com/leanprover-community/mathlib/commit/d8b0d1a)
chore(algebra/big_operators): avoid 'abel' tactic ([#9833](https://github.com/leanprover-community/mathlib/pull/9833))
I'd like to add an import ` algebra.euclidean_domain` → `algebra.associated` in [#9606](https://github.com/leanprover-community/mathlib/pull/9606), so this removes the dependency in the other direction (`algebra.associated` → `algebra.big_operators.basic` → `tactic.abel` → `tactic.norm_num` → `data.rat.cast` → `data.rat.order` → `data.rat.basic` → ` algebra.euclidean_domain`). Fortunately, the dependency on `abel` was quite shallow here.
#### Estimated changes
modified archive/oxford_invariants/2021summer/week3_p1.lean

modified src/algebra/algebra/basic.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/geom_sum.lean

modified src/algebra/homology/homotopy.lean

modified src/algebra/module/basic.lean

modified src/data/int/interval.lean

modified src/data/pnat/interval.lean

modified src/linear_algebra/affine_space/affine_map.lean

modified src/linear_algebra/sesquilinear_form.lean

modified src/ring_theory/ideal/basic.lean



## [2021-10-21 13:16:16](https://github.com/leanprover-community/mathlib/commit/de13786)
chore(topology/algebra/ordered): move IVT to a new file ([#9792](https://github.com/leanprover-community/mathlib/pull/9792))
#### Estimated changes
modified src/topology/algebra/ordered/basic.lean
- \- *lemma* intermediate_value_univ₂
- \- *lemma* intermediate_value_univ₂_eventually₁
- \- *lemma* intermediate_value_univ₂_eventually₂
- \- *lemma* is_preconnected.intermediate_value₂
- \- *lemma* is_preconnected.intermediate_value₂_eventually₁
- \- *lemma* is_preconnected.intermediate_value₂_eventually₂
- \- *lemma* is_preconnected.intermediate_value
- \- *lemma* is_preconnected.intermediate_value_Ico
- \- *lemma* is_preconnected.intermediate_value_Ioc
- \- *lemma* is_preconnected.intermediate_value_Ioo
- \- *lemma* is_preconnected.intermediate_value_Ici
- \- *lemma* is_preconnected.intermediate_value_Iic
- \- *lemma* is_preconnected.intermediate_value_Ioi
- \- *lemma* is_preconnected.intermediate_value_Iio
- \- *lemma* is_preconnected.intermediate_value_Iii
- \- *lemma* intermediate_value_univ
- \- *lemma* mem_range_of_exists_le_of_exists_ge
- \- *lemma* is_preconnected.Icc_subset
- \- *lemma* is_connected.Icc_subset
- \- *lemma* is_preconnected.eq_univ_of_unbounded
- \- *lemma* is_preconnected.ord_connected
- \- *lemma* is_connected.Ioo_cInf_cSup_subset
- \- *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \- *lemma* is_preconnected.Ioi_cInf_subset
- \- *lemma* is_preconnected.Iio_cSup_subset
- \- *lemma* is_preconnected.mem_intervals
- \- *lemma* set_of_is_preconnected_subset_of_ordered
- \- *lemma* is_closed.mem_of_ge_of_forall_exists_gt
- \- *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \- *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within
- \- *lemma* is_preconnected_Icc
- \- *lemma* is_preconnected_interval
- \- *lemma* set.ord_connected.is_preconnected
- \- *lemma* is_preconnected_iff_ord_connected
- \- *lemma* is_preconnected_Ici
- \- *lemma* is_preconnected_Iic
- \- *lemma* is_preconnected_Iio
- \- *lemma* is_preconnected_Ioi
- \- *lemma* is_preconnected_Ioo
- \- *lemma* is_preconnected_Ioc
- \- *lemma* is_preconnected_Ico
- \- *lemma* set_of_is_preconnected_eq_of_ordered
- \- *lemma* intermediate_value_Icc
- \- *lemma* intermediate_value_Icc'
- \- *lemma* intermediate_value_interval
- \- *lemma* intermediate_value_Ico
- \- *lemma* intermediate_value_Ico'
- \- *lemma* intermediate_value_Ioc
- \- *lemma* intermediate_value_Ioc'
- \- *lemma* intermediate_value_Ioo
- \- *lemma* intermediate_value_Ioo'
- \- *lemma* continuous.surjective
- \- *lemma* continuous.surjective'
- \- *lemma* continuous_on.surj_on_of_tendsto
- \- *lemma* continuous_on.surj_on_of_tendsto'

modified src/topology/algebra/ordered/compact.lean

created src/topology/algebra/ordered/intermediate_value.lean
- \+ *lemma* intermediate_value_univ₂
- \+ *lemma* intermediate_value_univ₂_eventually₁
- \+ *lemma* intermediate_value_univ₂_eventually₂
- \+ *lemma* is_preconnected.intermediate_value₂
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₁
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₂
- \+ *lemma* is_preconnected.intermediate_value
- \+ *lemma* is_preconnected.intermediate_value_Ico
- \+ *lemma* is_preconnected.intermediate_value_Ioc
- \+ *lemma* is_preconnected.intermediate_value_Ioo
- \+ *lemma* is_preconnected.intermediate_value_Ici
- \+ *lemma* is_preconnected.intermediate_value_Iic
- \+ *lemma* is_preconnected.intermediate_value_Ioi
- \+ *lemma* is_preconnected.intermediate_value_Iio
- \+ *lemma* is_preconnected.intermediate_value_Iii
- \+ *lemma* intermediate_value_univ
- \+ *lemma* mem_range_of_exists_le_of_exists_ge
- \+ *lemma* is_preconnected.Icc_subset
- \+ *lemma* is_preconnected.ord_connected
- \+ *lemma* is_connected.Icc_subset
- \+ *lemma* is_preconnected.eq_univ_of_unbounded
- \+ *lemma* is_connected.Ioo_cInf_cSup_subset
- \+ *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \+ *lemma* is_preconnected.Ioi_cInf_subset
- \+ *lemma* is_preconnected.Iio_cSup_subset
- \+ *lemma* is_preconnected.mem_intervals
- \+ *lemma* set_of_is_preconnected_subset_of_ordered
- \+ *lemma* is_closed.mem_of_ge_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within
- \+ *lemma* is_preconnected_Icc
- \+ *lemma* is_preconnected_interval
- \+ *lemma* set.ord_connected.is_preconnected
- \+ *lemma* is_preconnected_iff_ord_connected
- \+ *lemma* is_preconnected_Ici
- \+ *lemma* is_preconnected_Iic
- \+ *lemma* is_preconnected_Iio
- \+ *lemma* is_preconnected_Ioi
- \+ *lemma* is_preconnected_Ioo
- \+ *lemma* is_preconnected_Ioc
- \+ *lemma* is_preconnected_Ico
- \+ *lemma* set_of_is_preconnected_eq_of_ordered
- \+ *lemma* intermediate_value_Icc
- \+ *lemma* intermediate_value_Icc'
- \+ *lemma* intermediate_value_interval
- \+ *lemma* intermediate_value_Ico
- \+ *lemma* intermediate_value_Ico'
- \+ *lemma* intermediate_value_Ioc
- \+ *lemma* intermediate_value_Ioc'
- \+ *lemma* intermediate_value_Ioo
- \+ *lemma* intermediate_value_Ioo'
- \+ *lemma* continuous.surjective
- \+ *lemma* continuous.surjective'
- \+ *lemma* continuous_on.surj_on_of_tendsto
- \+ *lemma* continuous_on.surj_on_of_tendsto'



## [2021-10-21 13:16:14](https://github.com/leanprover-community/mathlib/commit/d9daf54)
feat(topology/metric_space/isometry): add simps config ([#9757](https://github.com/leanprover-community/mathlib/pull/9757))
Also make `isometric.complete_space` take `complete_space β` as an instance argument.
#### Estimated changes
modified src/topology/metric_space/isometry.lean
- \- *lemma* to_homeomorph_to_equiv
- \- *lemma* isometry.isometric_on_range_apply
- \+ *def* simps.apply
- \+ *def* simps.symm_apply



## [2021-10-21 11:25:37](https://github.com/leanprover-community/mathlib/commit/fe5ddaf)
feat(ring_theory/polynomial/cyclotomic): add cyclotomic_prime_pow_eq_geom_sum and supporting lemmas ([#9845](https://github.com/leanprover-community/mathlib/pull/9845))
Clean up a little bit in src/number_theory/divisors.lean using to_additive too.
#### Estimated changes
modified src/number_theory/divisors.lean
- \+ *lemma* prime.prod_proper_divisors
- \+ *lemma* prime.prod_divisors
- \+ *lemma* mem_proper_divisors_prime_pow
- \+ *lemma* proper_divisors_prime_pow
- \+ *lemma* prod_proper_divisors_prime_pow
- \- *lemma* prime.sum_proper_divisors
- \- *lemma* prime.sum_divisors
- \- *lemma* prod_divisors_prime
- \- *lemma* sum_divisors_prime_pow

modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* cyclotomic_prime_pow_eq_geom_sum



## [2021-10-21 11:25:35](https://github.com/leanprover-community/mathlib/commit/edd801f)
chore(set_theory/cardinal): ensure `c ^ ↑n = c ^ n` is definitional ([#9842](https://github.com/leanprover-community/mathlib/pull/9842))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+/\- *lemma* pow_cast_right
- \+/\- *lemma* pow_cast_right
- \+/\- *theorem* power_add
- \+/\- *theorem* power_add



## [2021-10-21 11:25:33](https://github.com/leanprover-community/mathlib/commit/777f11c)
feat(group_theory/index): Special cases of relindex ([#9831](https://github.com/leanprover-community/mathlib/pull/9831))
Adds special cases of relindex. Also refactors the file to use `nat.card`, rather than the equivalent `(# _).to_nat`.
#### Estimated changes
modified src/group_theory/index.lean
- \+/\- *lemma* index_bot
- \+ *lemma* relindex_top_left
- \+ *lemma* relindex_top_right
- \+ *lemma* relindex_bot_left
- \+ *lemma* relindex_bot_left_eq_card
- \+ *lemma* relindex_bot_right
- \+ *lemma* relindex_self
- \+/\- *lemma* index_bot



## [2021-10-21 11:25:32](https://github.com/leanprover-community/mathlib/commit/bfa4010)
feat(data/nat/modeq): `modeq.le_of_lt_add` ([#9816](https://github.com/leanprover-community/mathlib/pull/9816))
If `a ≡ b [MOD m]` and `a < b + m`, then `a ≤ b`.
#### Estimated changes
modified src/data/nat/modeq.lean
- \+ *lemma* le_of_lt_add
- \+ *lemma* add_le_of_lt



## [2021-10-21 08:38:42](https://github.com/leanprover-community/mathlib/commit/da01792)
refactor(*): remove integral_domain, rename domain to is_domain ([#9748](https://github.com/leanprover-community/mathlib/pull/9748))
#### Estimated changes
modified archive/imo/imo1962_q4.lean
- \+/\- *lemma* formula
- \+/\- *lemma* formula

modified src/algebra/algebra/basic.lean
- \+/\- *lemma* iff_algebra_map_injective
- \+/\- *lemma* iff_algebra_map_injective

modified src/algebra/algebra/bilinear.lean

modified src/algebra/algebra/subalgebra.lean

modified src/algebra/char_p/algebra.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/field.lean

modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/gcd_monoid/finset.lean

modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq

modified src/algebra/opposites.lean

modified src/algebra/order/ring.lean

modified src/algebra/quadratic_discriminant.lean

modified src/algebra/quaternion.lean

modified src/algebra/ring/basic.lean
- \- *lemma* integral_domain.to_is_integral_domain
- \- *theorem* is_integral_domain.to_integral_domain

modified src/data/equiv/ring.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/mv_polynomial/funext.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/polynomial/cancel_leads.lean
- \+/\- *lemma* nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree
- \+/\- *lemma* nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/integral_normalization.lean

modified src/data/polynomial/mirror.lean
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* irreducible_of_mirror
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* irreducible_of_mirror

modified src/data/polynomial/reverse.lean
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* eq_of_infinite_eval_eq
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_zero
- \+/\- *lemma* root_set_C
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic
- \+/\- *lemma* eq_of_infinite_eval_eq
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_zero
- \+/\- *lemma* root_set_C
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic
- \- *lemma* polynomial
- \+/\- *def* nth_roots_finset
- \+/\- *def* root_set
- \+/\- *def* nth_roots_finset
- \+/\- *def* root_set

modified src/data/rat/basic.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/zmod/basic.lean

modified src/field_theory/finite/basic.lean
- \+/\- *lemma* sq_add_sq
- \+/\- *lemma* sq_add_sq

modified src/field_theory/fixed.lean

modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* algebra_map_surjective_of_is_integral
- \+/\- *lemma* algebra_map_surjective_of_is_algebraic
- \+/\- *lemma* algebra_map_surjective_of_is_integral
- \+/\- *lemma* algebra_map_surjective_of_is_algebraic

modified src/field_theory/minpoly.lean
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+/\- *lemma* gcd_domain_eq_field_fractions

modified src/field_theory/perfect_closure.lean
- \+/\- *theorem* eq_iff
- \+/\- *theorem* eq_iff

modified src/field_theory/separable.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/determinant.lean
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/free_module/pid.lean
- \+/\- *lemma* ideal.rank_eq
- \+/\- *lemma* ideal.rank_eq

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+/\- *lemma* exists_mul_vec_eq_zero_iff
- \+/\- *lemma* exists_vec_mul_eq_zero_iff
- \+/\- *lemma* exists_mul_vec_eq_zero_iff
- \+/\- *lemma* exists_vec_mul_eq_zero_iff
- \+/\- *theorem* nondegenerate_iff_det_ne_zero
- \+/\- *theorem* nondegenerate_iff_det_ne_zero

modified src/linear_algebra/sesquilinear_form.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/function_field.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/class_group.lean

modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* dimension_le_one.is_integral_closure
- \+/\- *lemma* dimension_le_one.integral_closure
- \+/\- *lemma* dimension_le_one.is_integral_closure
- \+/\- *lemma* dimension_le_one.integral_closure

modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* of_has_unit_mul_pow_irreducible_factorization
- \+/\- *lemma* of_has_unit_mul_pow_irreducible_factorization
- \+/\- *theorem* iff_pid_with_one_nonzero_prime
- \+/\- *theorem* iff_pid_with_one_nonzero_prime

modified src/ring_theory/eisenstein_criterion.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* order_mul
- \+/\- *lemma* order_mul

modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* bot_prime
- \+/\- *lemma* span_singleton_eq_span_singleton
- \+/\- *lemma* span_singleton_lt_span_singleton
- \+/\- *lemma* factors_decreasing
- \+ *lemma* is_domain_iff_prime
- \+/\- *lemma* bot_prime
- \+/\- *lemma* span_singleton_eq_span_singleton
- \+/\- *lemma* span_singleton_lt_span_singleton
- \+/\- *lemma* factors_decreasing
- \- *lemma* is_integral_domain_iff_prime

modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* mul_eq_bot
- \+/\- *lemma* prod_eq_bot
- \+ *lemma* radical_bot_of_is_domain
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* mul_eq_bot
- \+/\- *lemma* prod_eq_bot
- \- *lemma* radical_bot_of_integral_domain
- \+/\- *lemma* ker_is_prime

modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* comap_ne_bot_of_root_mem
- \+/\- *lemma* comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* comap_ne_bot_of_integral_mem
- \+/\- *lemma* eq_bot_of_comap_eq_bot
- \+/\- *lemma* exists_ideal_over_maximal_of_is_integral
- \+/\- *lemma* comap_ne_bot_of_root_mem
- \+/\- *lemma* comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* comap_ne_bot_of_integral_mem
- \+/\- *lemma* eq_bot_of_comap_eq_bot
- \+/\- *lemma* exists_ideal_over_maximal_of_is_integral

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/integral_domain.lean
- \+ *lemma* is_cyclic_of_subgroup_is_domain
- \- *lemma* is_cyclic_of_subgroup_integral_domain
- \+ *def* division_ring_of_is_domain
- \+ *def* field_of_is_domain
- \- *def* division_ring_of_domain
- \- *def* field_of_integral_domain

modified src/ring_theory/integrally_closed.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/localization.lean
- \+ *theorem* is_domain_of_le_non_zero_divisors
- \+ *theorem* is_domain_localization
- \- *theorem* integral_domain_of_le_non_zero_divisors
- \- *theorem* integral_domain_localization
- \- *theorem* to_integral_domain

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/norm.lean
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis

modified src/ring_theory/perfection.lean

modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* is_domain_map_C_quotient
- \+ *lemma* is_domain_fin_zero
- \+ *lemma* is_domain_fin
- \+ *lemma* is_domain_fintype
- \- *lemma* is_integral_domain_map_C_quotient
- \- *lemma* is_integral_domain_fin_zero
- \- *lemma* is_integral_domain_fin
- \- *lemma* is_integral_domain_fintype
- \- *theorem* integral_domain_fintype

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* roots_of_cyclotomic
- \+/\- *lemma* roots_of_cyclotomic
- \+/\- *def* cyclotomic'
- \+/\- *def* cyclotomic'

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/polynomial/scale_roots.lean

modified src/ring_theory/power_basis.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* to_maximal_ideal

modified src/ring_theory/roots_of_unity.lean
- \+/\- *def* primitive_roots
- \+/\- *def* primitive_roots

modified src/ring_theory/subring.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/ring_theory/valuation/integral.lean



## [2021-10-21 02:55:10](https://github.com/leanprover-community/mathlib/commit/3c11bd7)
chore(*): bump to lean 3.34.0 ([#9824](https://github.com/leanprover-community/mathlib/pull/9824))
### Backport coercions from Lean 4
Now `has_coe_to_fun` and `has_coe_to_sort` take the output type as an `out_param` argument. This change comes with some changes in the elaboration order, so some proofs/definitions need more type annotations.
### Smarter `by_contra`
Now `by_contra h` does better job if the goal is a negation.
### `open` and current namespace
In
```lean
namespace A
open B _root_.C
end A
```
Lean will try to open `A.B`; if this fails, it will open `B`. It will also open `C`.
`setup_tactic_parser_cmd` command was updated to open appropriate `_root_.*` namespaces.
#### Estimated changes
modified counterexamples/phillips.lean

modified leanpkg.toml

modified src/algebra/algebra/basic.lean
- \+ *theorem* coe_fn_inj

modified src/algebra/category/Algebra/basic.lean

modified src/algebra/category/CommRing/basic.lean

modified src/algebra/category/FinVect.lean

modified src/algebra/category/Group/basic.lean

modified src/algebra/category/Module/adjunctions.lean
- \+ *lemma* μ_natural
- \+ *lemma* left_unitality
- \+ *lemma* right_unitality
- \+ *lemma* associativity
- \+ *def* ε
- \+ *def* μ

modified src/algebra/category/Module/basic.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/category/Semigroup/basic.lean

modified src/algebra/direct_sum/basic.lean

modified src/algebra/group/hom.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/type_tags.lean

modified src/algebra/group_action_hom.lean

modified src/algebra/lie/basic.lean

modified src/algebra/lie/tensor_product.lean

modified src/algebra/module/linear_map.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/non_unital_alg_hom.lean

modified src/algebra/order/absolute_value.lean

modified src/algebra/quandle.lean

modified src/algebra/quaternion.lean

modified src/algebra/ring/basic.lean

modified src/algebraic_geometry/locally_ringed_space.lean

modified src/algebraic_geometry/structure_sheaf.lean

modified src/algebraic_topology/topological_simplex.lean

modified src/analysis/box_integral/partition/additive.lean

modified src/analysis/calculus/specific_functions.lean
- \+/\- *lemma* support_eq
- \+/\- *lemma* support_eq
- \+/\- *lemma* support_eq
- \+/\- *lemma* support_eq

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/normed/group/SemiNormedGroup.lean
- \+ *lemma* coe_comp'

modified src/analysis/normed/group/SemiNormedGroup/completion.lean

modified src/analysis/normed/group/hom.lean
- \+/\- *lemma* coe_inj
- \+/\- *lemma* coe_inj_iff
- \+/\- *lemma* coe_inj
- \+/\- *lemma* coe_inj_iff

modified src/analysis/normed_space/affine_isometry.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_one

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/dual.lean

modified src/analysis/normed_space/enorm.lean
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* coe_inj
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* coe_inj

modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_one

modified src/analysis/normed_space/mazur_ulam.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/seminorm.lean

modified src/category_theory/Fintype.lean

modified src/category_theory/abelian/pseudoelements.lean
- \+/\- *def* object_to_sort
- \+/\- *def* hom_to_fun
- \+/\- *def* object_to_sort
- \+/\- *def* hom_to_fun

modified src/category_theory/category/Cat.lean

modified src/category_theory/category/Quiv.lean

modified src/category_theory/concrete_category/basic.lean
- \+/\- *def* concrete_category.has_coe_to_fun
- \+/\- *def* concrete_category.has_coe_to_fun

modified src/category_theory/concrete_category/bundled.lean
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_mk

modified src/category_theory/full_subcategory.lean

modified src/category_theory/linear/yoneda.lean

modified src/category_theory/monad/products.lean

modified src/category_theory/monoidal/internal/Module.lean

modified src/category_theory/simple.lean

modified src/category_theory/sites/grothendieck.lean

modified src/category_theory/sites/pretopology.lean

modified src/category_theory/sites/sieves.lean

modified src/combinatorics/derangements/basic.lean

modified src/combinatorics/hales_jewett.lean

modified src/combinatorics/quiver.lean

modified src/computability/partrec_code.lean

modified src/computability/turing_machine.lean

modified src/control/traversable/basic.lean

modified src/data/analysis/filter.lean

modified src/data/analysis/topology.lean

modified src/data/complex/basic.lean

modified src/data/dfinsupp.lean

modified src/data/equiv/basic.lean

modified src/data/equiv/local_equiv.lean

modified src/data/equiv/module.lean

modified src/data/equiv/mul_add.lean

modified src/data/equiv/ring.lean

modified src/data/equiv/set.lean

modified src/data/finset/basic.lean

modified src/data/finsupp/basic.lean

modified src/data/fintype/basic.lean

modified src/data/fintype/card_embedding.lean

modified src/data/int/gcd.lean

modified src/data/mv_polynomial/basic.lean

modified src/data/nat/prime.lean

modified src/data/num/lemmas.lean

modified src/data/pequiv.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/set/basic.lean

modified src/data/set/intervals/basic.lean

modified src/data/set_like/basic.lean
- \+/\- *theorem* coe_sort_coe
- \+/\- *theorem* coe_sort_coe

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/dynamics/flow.lean

modified src/field_theory/polynomial_galois_group.lean

modified src/geometry/euclidean/basic.lean

modified src/geometry/manifold/algebra/left_invariant_derivation.lean

modified src/geometry/manifold/algebra/monoid.lean

modified src/geometry/manifold/bump_function.lean

modified src/geometry/manifold/derivation_bundle.lean

modified src/geometry/manifold/diffeomorph.lean

modified src/geometry/manifold/partition_of_unity.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean

modified src/geometry/manifold/times_cont_mdiff_map.lean

modified src/group_theory/congruence.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean

modified src/group_theory/specific_groups/dihedral.lean

modified src/group_theory/subgroup/basic.lean

modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* coe_fn_inj
- \+/\- *lemma* coe_fn_inj

modified src/linear_algebra/affine_space/affine_map.lean

modified src/linear_algebra/alternating.lean
- \+ *theorem* coe_injective
- \+/\- *theorem* coe_inj
- \+/\- *theorem* coe_inj

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/dual.lean

modified src/linear_algebra/general_linear_group.lean

modified src/linear_algebra/linear_pmap.lean

modified src/linear_algebra/multilinear/basic.lean
- \+ *theorem* coe_injective
- \+/\- *theorem* coe_inj
- \+/\- *theorem* coe_inj

modified src/linear_algebra/quadratic_form/basic.lean

modified src/linear_algebra/sesquilinear_form.lean

modified src/linear_algebra/special_linear_group.lean

modified src/linear_algebra/unitary_group.lean

modified src/logic/basic.lean
- \+ *theorem* coe_fn_coe_trans'
- \+ *theorem* coe_fn_coe_base'

modified src/logic/embedding.lean

modified src/measure_theory/category/Meas.lean

modified src/measure_theory/function/ae_eq_fun.lean

modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* coe_injective
- \+/\- *lemma* coe_injective

modified src/measure_theory/integral/mean_inequalities.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure/content.lean

modified src/measure_theory/measure/finite_measure_weak_convergence.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/measure_space_def.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/measure_theory/measure/stieltjes.lean

modified src/measure_theory/measure/vector_measure.lean

modified src/measure_theory/probability_mass_function.lean

modified src/meta/coinductive_predicates.lean

modified src/meta/expr.lean

modified src/model_theory/basic.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/dioph.lean

modified src/number_theory/fermat4.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/ring_homs.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/order/category/LinearOrder.lean

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/category/PartialOrder.lean

modified src/order/category/Preorder.lean

modified src/order/category/omega_complete_partial_order.lean

modified src/order/closure.lean

modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* map_at_top
- \+/\- *lemma* map_at_bot
- \+/\- *lemma* map_at_top
- \+/\- *lemma* map_at_bot

modified src/order/jordan_holder.lean

modified src/order/lexicographic.lean

modified src/order/omega_complete_partial_order.lean

modified src/order/preorder_hom.lean

modified src/order/rel_iso.lean

modified src/ring_theory/algebraic_independent.lean
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_C
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_none
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_some

modified src/ring_theory/derivation.lean

modified src/ring_theory/finiteness.lean

modified src/ring_theory/flat.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/hahn_series.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/perfection.lean

modified src/ring_theory/ring_invo.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/valuation/basic.lean

modified src/ring_theory/witt_vector/is_poly.lean

modified src/set_theory/ordinal.lean

modified src/set_theory/pgame.lean
- \+/\- *theorem* lt_mk_of_le
- \+/\- *theorem* lt_mk_of_le

modified src/set_theory/zfc.lean
- \+/\- *theorem* mem_powerset
- \+/\- *theorem* mem_powerset

modified src/tactic/abel.lean

modified src/tactic/cache.lean

modified src/tactic/converter/interactive.lean

modified src/tactic/core.lean

modified src/tactic/elementwise.lean

modified src/tactic/elide.lean

modified src/tactic/explode.lean

modified src/tactic/explode_widget.lean

modified src/tactic/field_simp.lean

modified src/tactic/fin_cases.lean

modified src/tactic/finish.lean

modified src/tactic/generalize_proofs.lean

modified src/tactic/generalizes.lean

modified src/tactic/group.lean

modified src/tactic/hint.lean

modified src/tactic/interactive.lean

modified src/tactic/lift.lean

modified src/tactic/linarith/preprocessing.lean

modified src/tactic/lint/type_classes.lean

modified src/tactic/monotonicity/basic.lean

modified src/tactic/norm_fin.lean

modified src/tactic/norm_swap.lean

modified src/tactic/reassoc_axiom.lean

modified src/tactic/replacer.lean

modified src/tactic/rewrite.lean

modified src/tactic/ring.lean

modified src/tactic/simp_result.lean

modified src/tactic/simpa.lean

modified src/tactic/simps.lean

modified src/tactic/slice.lean

modified src/tactic/solve_by_elim.lean

modified src/tactic/split_ifs.lean

modified src/tactic/squeeze.lean

modified src/tactic/subtype_instance.lean

modified src/tactic/suggest.lean

modified src/tactic/tfae.lean

modified src/tactic/tidy.lean

modified src/tactic/trunc_cases.lean

modified src/tactic/wlog.lean

modified src/testing/slim_check/functions.lean

modified src/testing/slim_check/testable.lean

modified src/topology/algebra/module.lean

modified src/topology/algebra/multilinear.lean

modified src/topology/algebra/weak_dual_topology.lean

modified src/topology/category/CompHaus/default.lean

modified src/topology/category/Compactum.lean

modified src/topology/category/Profinite/default.lean

modified src/topology/category/Top/basic.lean

modified src/topology/category/Top/open_nhds.lean

modified src/topology/category/Top/opens.lean

modified src/topology/category/TopCommRing.lean

modified src/topology/category/UniformSpace.lean

modified src/topology/connected.lean

modified src/topology/continuous_function/algebra.lean

modified src/topology/continuous_function/basic.lean

modified src/topology/continuous_function/bounded.lean

modified src/topology/continuous_function/stone_weierstrass.lean

modified src/topology/discrete_quotient.lean

modified src/topology/fiber_bundle.lean

modified src/topology/homeomorph.lean

modified src/topology/homotopy/basic.lean

modified src/topology/homotopy/path.lean

modified src/topology/local_homeomorph.lean

modified src/topology/locally_constant/basic.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/isometry.lean

modified src/topology/partition_of_unity.lean

modified src/topology/path_connected.lean

modified src/topology/shrinking_lemma.lean

modified src/topology/subset_properties.lean

modified src/topology/vector_bundle.lean

modified test/delta_instance.lean
- \+/\- *def* X
- \+/\- *def* X

modified test/lint_coe_to_fun.lean

modified test/lint_simp_nf.lean

modified test/norm_cast_coe_fn.lean

modified test/simps.lean



## [2021-10-20 19:43:22](https://github.com/leanprover-community/mathlib/commit/8366f93)
feat(ring_theory/integral_domain): finite domains are division rings ([#9823](https://github.com/leanprover-community/mathlib/pull/9823))
TODO: Prove Wedderburn's little theorem
which shows a finite domain is in fact commutative, hence a field.
#### Estimated changes
modified src/ring_theory/integral_domain.lean
- \+ *lemma* mul_right_bijective₀
- \+ *lemma* mul_left_bijective₀
- \+ *def* division_ring_of_domain



## [2021-10-20 18:03:33](https://github.com/leanprover-community/mathlib/commit/4ebeb05)
chore(group_theory/submonoid/center): add decidable_mem_center ([#9825](https://github.com/leanprover-community/mathlib/pull/9825))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/center.lean

modified src/ring_theory/subring.lean

modified src/ring_theory/subsemiring.lean



## [2021-10-20 18:03:31](https://github.com/leanprover-community/mathlib/commit/3d00081)
feat(group_theory/index): Index of top and bottom subgroups ([#9819](https://github.com/leanprover-community/mathlib/pull/9819))
This PR computes the index of the top and bottom subgroups.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* index_top
- \+ *lemma* index_bot
- \+ *lemma* index_bot_eq_card

modified src/set_theory/cardinal.lean
- \+/\- *lemma* zero_to_nat
- \+/\- *lemma* one_to_nat
- \+ *lemma* to_nat_eq_one
- \+ *lemma* to_nat_eq_one_iff_unique
- \+/\- *lemma* zero_to_nat
- \+/\- *lemma* one_to_nat



## [2021-10-20 15:39:06](https://github.com/leanprover-community/mathlib/commit/68a674e)
refactor(algebra/order/sub): rename sub -> tsub ([#9793](https://github.com/leanprover-community/mathlib/pull/9793))
* Renames lemmas in the file `algebra/order/sub` to use `tsub` instead of `sub` in the name
* Remove primes from lemma names where possible
* [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_lt_mul'''')
* Remove `sub_mul_ge`, `mul_sub_ge` and `lt_sub_iff_lt_sub`. They were special cases of `le_sub_mul`, `le_mul_sub` and `lt_sub_comm`, respectively.
#### Estimated changes
modified archive/100-theorems-list/73_ascending_descending_sequences.lean

modified archive/imo/imo1977_q6.lean

modified archive/imo/imo1998_q2.lean

modified archive/oxford_invariants/2021summer/week3_p1.lean

modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean

modified src/algebra/associated.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/big_operators/intervals.lean

modified src/algebra/geom_sum.lean

modified src/algebra/linear_recurrence.lean

modified src/algebra/order/ring.lean
- \- *lemma* sub_mul_ge
- \- *lemma* mul_sub_ge

modified src/algebra/order/sub.lean
- \+ *lemma* tsub_le_iff_right
- \+ *lemma* add_tsub_le_right
- \+ *lemma* le_tsub_add
- \+ *lemma* add_hom.le_map_tsub
- \+ *lemma* le_mul_tsub
- \+ *lemma* le_tsub_mul
- \+ *lemma* order_iso.map_tsub
- \+ *lemma* tsub_le_iff_left
- \+ *lemma* le_add_tsub
- \+ *lemma* add_tsub_le_left
- \+ *lemma* tsub_le_tsub_right
- \+ *lemma* tsub_le_iff_tsub_le
- \+ *lemma* tsub_tsub_le
- \+ *lemma* add_monoid_hom.le_map_tsub
- \+ *lemma* tsub_tsub
- \+ *lemma* tsub_le_tsub_left
- \+ *lemma* tsub_le_tsub
- \+ *lemma* tsub_add_eq_tsub_tsub
- \+ *lemma* tsub_add_eq_tsub_tsub_swap
- \+ *lemma* add_le_add_add_tsub
- \+ *lemma* tsub_right_comm
- \+ *lemma* add_tsub_le_assoc
- \+ *lemma* le_tsub_add_add
- \+ *lemma* tsub_le_tsub_add_tsub
- \+ *lemma* tsub_tsub_tsub_le_tsub
- \+ *lemma* le_add_tsub_swap
- \+ *lemma* le_add_tsub'
- \+ *lemma* tsub_eq_of_eq_add
- \+ *lemma* eq_tsub_of_add_eq
- \+ *lemma* tsub_eq_of_eq_add_rev
- \+ *lemma* add_tsub_cancel_right
- \+ *lemma* add_tsub_cancel_left
- \+ *lemma* le_tsub_of_add_le_left
- \+ *lemma* le_tsub_of_add_le_right
- \+ *lemma* lt_add_of_tsub_lt_left
- \+ *lemma* lt_add_of_tsub_lt_right
- \+ *lemma* add_tsub_add_right_eq_tsub
- \+ *lemma* add_tsub_add_eq_tsub_left
- \+ *lemma* lt_of_tsub_lt_tsub_right
- \+ *lemma* lt_tsub_iff_right
- \+ *lemma* lt_tsub_iff_left
- \+ *lemma* lt_tsub_comm
- \+ *lemma* lt_of_tsub_lt_tsub_left
- \+ *lemma* add_tsub_cancel_of_le
- \+ *lemma* tsub_add_cancel_of_le
- \+ *lemma* add_tsub_cancel_iff_le
- \+ *lemma* tsub_add_cancel_iff_le
- \+ *lemma* add_le_of_le_tsub_right_of_le
- \+ *lemma* add_le_of_le_tsub_left_of_le
- \+ *lemma* tsub_le_tsub_iff_right
- \+ *lemma* tsub_left_inj
- \+ *lemma* lt_of_tsub_lt_tsub_right_of_le
- \+ *lemma* tsub_eq_zero_iff_le
- \+ *lemma* tsub_self
- \+ *lemma* tsub_le_self
- \+ *lemma* tsub_zero
- \+ *lemma* zero_tsub
- \+ *lemma* tsub_self_add
- \+ *lemma* tsub_inj_left
- \+ *lemma* tsub_pos_iff_not_le
- \+ *lemma* tsub_pos_of_lt
- \+ *lemma* tsub_add_tsub_cancel
- \+ *lemma* tsub_tsub_tsub_cancel_right
- \+ *lemma* eq_tsub_iff_add_eq_of_le
- \+ *lemma* tsub_eq_iff_eq_add_of_le
- \+ *lemma* add_tsub_assoc_of_le
- \+ *lemma* tsub_add_eq_add_tsub
- \+ *lemma* tsub_tsub_assoc
- \+ *lemma* le_tsub_iff_left
- \+ *lemma* le_tsub_iff_right
- \+ *lemma* tsub_lt_iff_left
- \+ *lemma* tsub_lt_iff_right
- \+ *lemma* lt_tsub_of_add_lt_right
- \+ *lemma* lt_tsub_of_add_lt_left
- \+ *lemma* tsub_lt_iff_tsub_lt
- \+ *lemma* le_tsub_iff_le_tsub
- \+ *lemma* lt_tsub_iff_right_of_le
- \+ *lemma* lt_tsub_iff_left_of_le
- \+ *lemma* lt_of_tsub_lt_tsub_left_of_le
- \+ *lemma* tsub_le_tsub_iff_left
- \+ *lemma* tsub_right_inj
- \+ *lemma* tsub_lt_tsub_right_of_le
- \+ *lemma* tsub_inj_right
- \+ *lemma* tsub_lt_tsub_iff_left_of_le_of_le
- \+ *lemma* add_tsub_tsub_cancel
- \+ *lemma* tsub_tsub_cancel_of_le
- \+ *lemma* tsub_pos_iff_lt
- \+ *lemma* tsub_eq_tsub_min
- \+ *lemma* tsub_lt_tsub_iff_right
- \+ *lemma* tsub_lt_self
- \+ *lemma* tsub_lt_self_iff
- \+ *lemma* tsub_lt_tsub_iff_left_of_le
- \+ *lemma* tsub_add_eq_max
- \+ *lemma* add_tsub_eq_max
- \+ *lemma* tsub_min
- \+ *lemma* tsub_add_min
- \- *lemma* sub_le_iff_right
- \- *lemma* add_sub_le_right
- \- *lemma* le_sub_add
- \- *lemma* add_hom.le_map_sub
- \- *lemma* le_mul_sub
- \- *lemma* le_sub_mul
- \- *lemma* order_iso.map_sub
- \- *lemma* sub_le_iff_left
- \- *lemma* le_add_sub
- \- *lemma* add_sub_le_left
- \- *lemma* sub_le_sub_right'
- \- *lemma* sub_le_iff_sub_le
- \- *lemma* sub_sub_le
- \- *lemma* add_monoid_hom.le_map_sub
- \- *lemma* sub_sub'
- \- *lemma* sub_le_sub_left'
- \- *lemma* sub_le_sub'
- \- *lemma* sub_add_eq_sub_sub'
- \- *lemma* sub_add_eq_sub_sub_swap'
- \- *lemma* add_le_add_add_sub
- \- *lemma* sub_right_comm'
- \- *lemma* add_sub_le_assoc
- \- *lemma* le_sub_add_add
- \- *lemma* sub_le_sub_add_sub
- \- *lemma* sub_sub_sub_le_sub
- \- *lemma* le_add_sub_swap
- \- *lemma* le_add_sub'
- \- *lemma* sub_eq_of_eq_add''
- \- *lemma* eq_sub_of_add_eq''
- \- *lemma* sub_eq_of_eq_add_rev
- \- *lemma* add_sub_cancel_right
- \- *lemma* add_sub_cancel_left
- \- *lemma* le_sub_of_add_le_left'
- \- *lemma* le_sub_of_add_le_right'
- \- *lemma* lt_add_of_sub_lt_left'
- \- *lemma* lt_add_of_sub_lt_right'
- \- *lemma* add_sub_add_right_eq_sub'
- \- *lemma* add_sub_add_eq_sub_left'
- \- *lemma* lt_of_sub_lt_sub_right
- \- *lemma* lt_sub_iff_right
- \- *lemma* lt_sub_iff_left
- \- *lemma* lt_sub_comm
- \- *lemma* lt_of_sub_lt_sub_left
- \- *lemma* add_sub_cancel_of_le
- \- *lemma* sub_add_cancel_of_le
- \- *lemma* add_sub_cancel_iff_le
- \- *lemma* sub_add_cancel_iff_le
- \- *lemma* add_le_of_le_sub_right_of_le
- \- *lemma* add_le_of_le_sub_left_of_le
- \- *lemma* sub_le_sub_iff_right'
- \- *lemma* sub_left_inj'
- \- *lemma* lt_of_sub_lt_sub_right_of_le
- \- *lemma* sub_eq_zero_iff_le
- \- *lemma* sub_self'
- \- *lemma* sub_le_self'
- \- *lemma* sub_zero'
- \- *lemma* zero_sub'
- \- *lemma* sub_self_add
- \- *lemma* sub_inj_left
- \- *lemma* sub_pos_iff_not_le
- \- *lemma* sub_pos_of_lt'
- \- *lemma* sub_add_sub_cancel''
- \- *lemma* sub_sub_sub_cancel_right'
- \- *lemma* eq_sub_iff_add_eq_of_le
- \- *lemma* sub_eq_iff_eq_add_of_le
- \- *lemma* add_sub_assoc_of_le
- \- *lemma* sub_add_eq_add_sub'
- \- *lemma* sub_sub_assoc
- \- *lemma* le_sub_iff_left
- \- *lemma* le_sub_iff_right
- \- *lemma* sub_lt_iff_left
- \- *lemma* sub_lt_iff_right
- \- *lemma* lt_sub_of_add_lt_right
- \- *lemma* lt_sub_of_add_lt_left
- \- *lemma* sub_lt_iff_sub_lt
- \- *lemma* le_sub_iff_le_sub
- \- *lemma* lt_sub_iff_right_of_le
- \- *lemma* lt_sub_iff_left_of_le
- \- *lemma* lt_of_sub_lt_sub_left_of_le
- \- *lemma* sub_le_sub_iff_left'
- \- *lemma* sub_right_inj'
- \- *lemma* sub_lt_sub_right_of_le
- \- *lemma* sub_inj_right
- \- *lemma* sub_lt_sub_iff_left_of_le_of_le
- \- *lemma* add_sub_sub_cancel'
- \- *lemma* sub_sub_cancel_of_le
- \- *lemma* sub_pos_iff_lt
- \- *lemma* sub_eq_sub_min
- \- *lemma* sub_lt_sub_iff_right'
- \- *lemma* lt_sub_iff_lt_sub
- \- *lemma* sub_lt_self'
- \- *lemma* sub_lt_self_iff'
- \- *lemma* sub_lt_sub_iff_left_of_le
- \- *lemma* sub_add_eq_max
- \- *lemma* add_sub_eq_max
- \- *lemma* sub_min
- \- *lemma* sub_add_min

modified src/algebra/pointwise.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/normed/group/basic.lean

modified src/analysis/specific_limits.lean

modified src/combinatorics/composition.lean

modified src/combinatorics/derangements/exponential.lean

modified src/combinatorics/derangements/finite.lean

modified src/computability/DFA.lean

modified src/computability/turing_machine.lean

modified src/data/complex/exponential.lean

modified src/data/equiv/denumerable.lean

modified src/data/equiv/fin.lean

modified src/data/fin/basic.lean

modified src/data/finset/basic.lean

modified src/data/finset/sort.lean

modified src/data/finsupp/antidiagonal.lean

modified src/data/finsupp/basic.lean

modified src/data/list/basic.lean

modified src/data/list/cycle.lean

modified src/data/list/intervals.lean

modified src/data/list/perm.lean

modified src/data/list/rotate.lean

modified src/data/matrix/notation.lean

modified src/data/multiset/antidiagonal.lean

modified src/data/multiset/basic.lean
- \+/\- *theorem* le_union_left
- \+/\- *theorem* eq_union_left
- \+/\- *theorem* le_union_left
- \+/\- *theorem* eq_union_left

modified src/data/multiset/nodup.lean

modified src/data/multiset/powerset.lean

modified src/data/nat/basic.lean

modified src/data/nat/choose/basic.lean

modified src/data/nat/dist.lean

modified src/data/nat/factorial/basic.lean

modified src/data/nat/interval.lean

modified src/data/nat/modeq.lean

modified src/data/nat/multiplicity.lean

modified src/data/nat/pairing.lean

modified src/data/nat/prime.lean

modified src/data/nat/sqrt.lean

modified src/data/nat/succ_pred.lean

modified src/data/nat/upto.lean

modified src/data/ordmap/ordset.lean

modified src/data/pnat/factors.lean

modified src/data/polynomial/hasse_deriv.lean

modified src/data/polynomial/mirror.lean

modified src/data/polynomial/reverse.lean

modified src/data/polynomial/ring_division.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* lt_sub_comm
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* lt_sub_comm

modified src/data/vector/basic.lean

modified src/data/zmod/basic.lean

modified src/field_theory/finite/polynomial.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/list.lean

modified src/group_theory/specific_groups/alternating.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/number_theory/bernoulli.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/class_number/admissible_card_pow_degree.lean

modified src/number_theory/padics/ring_homs.lean

modified src/order/filter/at_top_bot.lean

modified src/order/iterate.lean

modified src/order/jordan_holder.lean

modified src/order/well_founded_set.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/witt_vector/frobenius.lean

modified src/set_theory/game/state.lean

modified src/set_theory/ordinal_arithmetic.lean

modified src/system/random/basic.lean

modified src/tactic/monotonicity/lemmas.lean

modified src/tactic/omega/coeffs.lean

modified src/testing/slim_check/gen.lean

modified src/testing/slim_check/sampleable.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/basic.lean

modified test/general_recursion.lean



## [2021-10-20 13:23:09](https://github.com/leanprover-community/mathlib/commit/5223e26)
feat(field_theory/finite/galois_field): uniqueness of finite fields ([#9817](https://github.com/leanprover-community/mathlib/pull/9817))
Every finite field is isomorphic to some Galois field. Closes [#9599](https://github.com/leanprover-community/mathlib/pull/9599)
#### Estimated changes
modified src/field_theory/finite/basic.lean
- \+/\- *theorem* card'
- \+/\- *theorem* card'

modified src/field_theory/finite/galois_field.lean
- \+ *lemma* is_splitting_field_of_card_eq
- \+ *theorem* splits_X_pow_card_sub_X
- \+ *def* alg_equiv_galois_field



## [2021-10-20 11:46:43](https://github.com/leanprover-community/mathlib/commit/49ab444)
fix(algebra/module/submodule_lattice): correct bad lemma ([#9809](https://github.com/leanprover-community/mathlib/pull/9809))
This lemma was accidentally stating that inf and inter are the same on sets, and wasn't about submodule at all.
The old statement was `↑p ⊓ ↑q = ↑p ∩ ↑q`, the new one is `↑(p ⊓ q) = ↑p ∩ ↑q`
#### Estimated changes
modified src/algebra/module/submodule_lattice.lean
- \+/\- *theorem* inf_coe
- \+/\- *theorem* inf_coe



## [2021-10-20 09:53:23](https://github.com/leanprover-community/mathlib/commit/24901dd)
feat(linear_algebra/free_module/rank): rank of free modules  ([#9810](https://github.com/leanprover-community/mathlib/pull/9810))
This file contains a basic API for the rank of free modules.
We will add the results for finite free modules in a future PR.
#### Estimated changes
created src/linear_algebra/free_module/rank.lean
- \+ *lemma* rank_eq_card_choose_basis_index
- \+ *lemma* rank_finsupp
- \+ *lemma* rank_finsupp'
- \+ *lemma* rank_prod
- \+ *lemma* rank_prod'
- \+ *lemma* rank_direct_sum
- \+ *lemma* rank_tensor_product
- \+ *lemma* rank_tensor_product'



## [2021-10-20 09:53:22](https://github.com/leanprover-community/mathlib/commit/2f54840)
refactor(*): replace comm_ring/integral_domain with ring/domain where possible ([#9739](https://github.com/leanprover-community/mathlib/pull/9739))
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/integral_normalization.lean

modified src/data/polynomial/mirror.lean
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul

modified src/data/polynomial/reverse.lean
- \+/\- *lemma* trailing_coeff_mul
- \+/\- *lemma* trailing_coeff_mul

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* root_mul
- \+/\- *lemma* root_or_root_of_root_mul
- \+/\- *lemma* root_mul
- \+/\- *lemma* root_or_root_of_root_mul

modified src/data/real/cau_seq.lean

modified src/field_theory/fixed.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/free_module/pid.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* order_mul
- \+/\- *lemma* order_mul

modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* bot_prime
- \+/\- *lemma* bot_prime

modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* ker_is_prime

modified src/ring_theory/localization.lean

modified src/ring_theory/power_series/basic.lean



## [2021-10-20 08:19:58](https://github.com/leanprover-community/mathlib/commit/a6d5ba8)
chore(set_theory/cardinal): add `map`, `induction_on` etc ([#9812](https://github.com/leanprover-community/mathlib/pull/9812))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *lemma* induction_on
- \+ *lemma* induction_on₂
- \+ *lemma* induction_on₃
- \+ *lemma* mk_congr
- \+ *lemma* map_mk
- \+/\- *lemma* succ_ne_zero
- \+/\- *lemma* succ_ne_zero
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+/\- *theorem* lift_zero
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+/\- *theorem* lift_zero
- \+ *def* map
- \+ *def* map₂

modified src/set_theory/ordinal.lean



## [2021-10-20 04:15:08](https://github.com/leanprover-community/mathlib/commit/9dafdf7)
feat(group_theory/subgroup/basic): `subgroup_of_self` ([#9818](https://github.com/leanprover-community/mathlib/pull/9818))
A subgroup is the top subgroup of itself.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup_of_self



## [2021-10-20 04:15:07](https://github.com/leanprover-community/mathlib/commit/6898728)
feat(analysis/complex/basic): a complex-valued function `has_sum` iff its real part and imaginary part `has_sum` ([#9648](https://github.com/leanprover-community/mathlib/pull/9648))
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* has_sum_iff
- \+ *def* equiv_real_prod_add_hom
- \+ *def* equiv_real_prod_add_hom_lm
- \+ *def* equiv_real_prodₗ

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.prod_mk



## [2021-10-20 01:45:58](https://github.com/leanprover-community/mathlib/commit/cd34347)
chore(*): remove uses of `universe variable` ([#9794](https://github.com/leanprover-community/mathlib/pull/9794))
Most of these uses are relics of when the distinction between `universe` and `universe variable` was more significant. There is still a difference inside sections, but it's an edge case and I don't think any of these uses are consciously trying to handle the edge case.
#### Estimated changes
modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/prime_spectrum.lean

modified src/algebraic_topology/simplex_category.lean

modified src/control/applicative.lean

modified src/control/functor.lean

modified src/control/traversable/lemmas.lean

modified src/data/equiv/fin.lean

modified src/data/fin_enum.lean

modified src/data/list/perm.lean

modified src/data/list/sort.lean

modified src/data/set/basic.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/free_algebra.lean

modified src/logic/basic.lean
- \+/\- *lemma* nonempty_subtype
- \+/\- *lemma* nonempty_pprod
- \+/\- *lemma* nonempty_psum
- \+/\- *lemma* nonempty_psigma
- \+/\- *lemma* nonempty_plift
- \+/\- *lemma* nonempty.forall
- \+/\- *lemma* nonempty.exists
- \+/\- *lemma* classical.nonempty_pi
- \+/\- *lemma* nonempty.map
- \+/\- *lemma* nonempty_subtype
- \+/\- *lemma* nonempty_pprod
- \+/\- *lemma* nonempty_psum
- \+/\- *lemma* nonempty_psigma
- \+/\- *lemma* nonempty_plift
- \+/\- *lemma* nonempty.forall
- \+/\- *lemma* nonempty.exists
- \+/\- *lemma* classical.nonempty_pi
- \+/\- *lemma* nonempty.map

modified src/logic/relator.lean

modified src/measure_theory/measure/content.lean

modified src/model_theory/basic.lean

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/copy.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/flat.lean

modified src/ring_theory/henselian.lean

modified src/ring_theory/witt_vector/is_poly.lean

modified src/tactic/core.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/weak_dual_topology.lean

modified src/topology/category/Compactum.lean

modified src/topology/category/Profinite/default.lean

modified src/topology/category/Profinite/projective.lean

modified test/simps.lean



## [2021-10-19 23:43:31](https://github.com/leanprover-community/mathlib/commit/2d17c5a)
feat(group_theory/index): Relative index ([#9780](https://github.com/leanprover-community/mathlib/pull/9780))
Defines relative index between subgroups, and proves that relative index is multiplicative in towers.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* index_comap
- \+ *lemma* relindex_mul_index
- \+/\- *lemma* index_dvd_of_le
- \+ *lemma* relindex_subgroup_of
- \+ *lemma* relindex_mul_relindex
- \- *lemma* index_eq_mul_of_le
- \+/\- *lemma* index_dvd_of_le



## [2021-10-19 20:59:45](https://github.com/leanprover-community/mathlib/commit/72cb2e8)
refactor(*): rename some declarations ending with '' ([#9504](https://github.com/leanprover-community/mathlib/pull/9504))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \- *lemma* smul_def''

modified src/algebra/algebra/tower.lean

modified src/algebra/free.lean
- \+ *def* rec_on_mul
- \+ *def* rec_on_pure
- \- *def* rec_on'
- \- *def* rec_on'

modified src/algebra/group_power/order.lean
- \+ *theorem* pow_lt_pow'
- \- *theorem* pow_lt_pow''

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/support.lean
- \+ *lemma* mul_support_inv'
- \- *lemma* mul_support_inv''

modified src/category_theory/abelian/exact.lean
- \+ *theorem* exact_iff_image_eq_kernel
- \- *theorem* exact_iff''

modified src/category_theory/monoidal/natural_transformation.lean
- \+ *lemma* comp_to_nat_trans_lax
- \+ *lemma* comp_to_nat_trans
- \- *lemma* comp_to_nat_trans'
- \- *lemma* comp_to_nat_trans''

modified src/data/matrix/basic.lean

modified src/field_theory/abel_ruffini.lean

modified src/field_theory/fixed.lean

modified src/field_theory/minpoly.lean
- \+ *lemma* eq_of_irreducible
- \- *lemma* unique''
- \+ *theorem* eq_of_irreducible_of_monic
- \- *theorem* unique'

modified src/ring_theory/derivation.lean

modified src/ring_theory/polynomial_algebra.lean



## [2021-10-19 16:49:58](https://github.com/leanprover-community/mathlib/commit/65eef74)
fix(data/int/basic): ensure the additive group structure on integers is computable ([#9803](https://github.com/leanprover-community/mathlib/pull/9803))
This prevents the following failure:
```lean
import analysis.normed_space.basic
instance whoops : add_comm_group ℤ := by apply_instance
-- definition 'whoops' is noncomputable, it depends on 'int.normed_comm_ring'
```
#### Estimated changes
modified src/data/int/basic.lean



## [2021-10-19 15:18:56](https://github.com/leanprover-community/mathlib/commit/e61584d)
fix(topology/sheaves/*): Fix docstrings ([#9807](https://github.com/leanprover-community/mathlib/pull/9807))
As noted by @alreadydone in [#9607](https://github.com/leanprover-community/mathlib/pull/9607), I forgot propagate naming changes to docstrings. This PR fixes that.
#### Estimated changes
modified src/topology/sheaves/forget.lean

modified src/topology/sheaves/local_predicate.lean

modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean

modified src/topology/sheaves/sheaf_condition/unique_gluing.lean

modified src/topology/sheaves/sheaf_of_functions.lean



## [2021-10-19 12:47:04](https://github.com/leanprover-community/mathlib/commit/34aa23a)
feat(ring_theory/dedekind_domain): connect (/) and (⁻¹) on fractional ideals ([#9808](https://github.com/leanprover-community/mathlib/pull/9808))
Turns out we never actually proved the `div_eq_mul_inv` lemma on fractional ideals, which motivated the entire definition of `div_inv_monoid`. So here it is, along with some useful supporting lemmas.
#### Estimated changes
modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* mul_right_le_iff
- \+ *lemma* mul_left_le_iff
- \+ *lemma* mul_right_strict_mono
- \+ *lemma* mul_left_strict_mono



## [2021-10-19 11:59:41](https://github.com/leanprover-community/mathlib/commit/065a708)
refactor(analysis/inner_product_space/projection): speedup proof ([#9804](https://github.com/leanprover-community/mathlib/pull/9804))
Speed up slow proof that caused a timeout on another branch.
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean
- \+ *def* reflection_linear_equiv



## [2021-10-19 09:31:15](https://github.com/leanprover-community/mathlib/commit/b961b68)
feat(topology/connected): product of connected spaces is a connected space ([#9789](https://github.com/leanprover-community/mathlib/pull/9789))
* prove more in the RHS of `filter.mem_infi'`;
* prove that the product of (pre)connected sets is a (pre)connected set;
* prove a similar statement about indexed product `set.pi set.univ _`;
* add instances for `prod.preconnected_space`, `prod.connected_space`, `pi.preconnected_space`, and `pi.connected_space`.
#### Estimated changes
modified src/order/filter/basic.lean

modified src/topology/connected.lean
- \+ *theorem* is_preconnected_singleton
- \+ *theorem* set.subsingleton.is_preconnected
- \+ *theorem* is_preconnected_Union
- \+ *theorem* is_preconnected.prod
- \+ *theorem* is_connected.prod
- \+ *theorem* is_preconnected_univ_pi
- \+ *theorem* is_connected_univ_pi

modified src/topology/constructions.lean
- \+ *lemma* exists_finset_piecewise_mem_of_mem_nhds

modified src/topology/continuous_on.lean



## [2021-10-19 09:31:13](https://github.com/leanprover-community/mathlib/commit/ff3e868)
refactor(algebra/domain): make domain and integral_domain mixins ([#9719](https://github.com/leanprover-community/mathlib/pull/9719))
This PR turns `domain` and `integral_domain` into mixins. There's quite a lot of work here, as the unused argument linter then forces us to do some generalizations! (i.e. getting rid of unnecessary `integral_domain` arguments).
This PR does the minimum possible generalization: [#9739](https://github.com/leanprover-community/mathlib/pull/9739) does some more.
In a subsequent PR we can unify `domain` and `integral_domain`, which now only differ in their typeclass requirements.
This also remove use of `old_structure_cmd` in `euclidean_domain`.
- [x] depends on: [#9725](https://github.com/leanprover-community/mathlib/pull/9725) [An RFC]
- [x] depends on: [#9736](https://github.com/leanprover-community/mathlib/pull/9736)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
modified archive/imo/imo1962_q4.lean
- \+/\- *lemma* formula
- \+/\- *lemma* formula

modified src/algebra/algebra/basic.lean
- \+/\- *lemma* iff_algebra_map_injective
- \+/\- *lemma* iff_algebra_map_injective

modified src/algebra/algebra/subalgebra.lean

modified src/algebra/char_p/algebra.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/gcd_monoid/finset.lean

modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq

modified src/algebra/opposites.lean

modified src/algebra/quadratic_discriminant.lean

modified src/algebra/quaternion.lean

modified src/algebra/ring/basic.lean
- \+/\- *lemma* integral_domain.to_is_integral_domain
- \+/\- *lemma* integral_domain.to_is_integral_domain
- \+ *theorem* is_integral_domain.to_integral_domain
- \- *def* is_integral_domain.to_integral_domain

modified src/data/equiv/ring.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/mv_polynomial/funext.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/polynomial/cancel_leads.lean
- \+/\- *lemma* nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree
- \+/\- *lemma* nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/div.lean
- \+ *lemma* root_multiplicity_zero
- \+ *lemma* root_multiplicity_eq_zero
- \+ *lemma* root_multiplicity_pos

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/integral_normalization.lean

modified src/data/polynomial/mirror.lean
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* irreducible_of_mirror
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* irreducible_of_mirror

modified src/data/polynomial/reverse.lean
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* eq_of_infinite_eval_eq
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_zero
- \+/\- *lemma* root_set_C
- \+/\- *lemma* root_set_finite
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic
- \- *lemma* root_multiplicity_zero
- \- *lemma* root_multiplicity_eq_zero
- \- *lemma* root_multiplicity_pos
- \+/\- *lemma* eq_of_infinite_eval_eq
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_zero
- \+/\- *lemma* root_set_C
- \+/\- *lemma* root_set_finite
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic
- \+/\- *def* nth_roots_finset
- \+/\- *def* root_set
- \+/\- *def* nth_roots_finset
- \+/\- *def* root_set

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/zmod/basic.lean

modified src/field_theory/finite/basic.lean
- \+/\- *lemma* sq_add_sq
- \+/\- *lemma* sq_add_sq

modified src/field_theory/finite/galois_field.lean

modified src/field_theory/fixed.lean

modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* algebra_map_surjective_of_is_integral
- \+/\- *lemma* algebra_map_surjective_of_is_integral'
- \+/\- *lemma* algebra_map_surjective_of_is_algebraic
- \+/\- *lemma* algebra_map_surjective_of_is_integral
- \+/\- *lemma* algebra_map_surjective_of_is_integral'
- \+/\- *lemma* algebra_map_surjective_of_is_algebraic

modified src/field_theory/minpoly.lean
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+/\- *lemma* gcd_domain_eq_field_fractions

modified src/field_theory/perfect_closure.lean
- \+/\- *theorem* eq_iff
- \+/\- *theorem* eq_iff

modified src/field_theory/separable.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/determinant.lean
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/free_module/pid.lean
- \+/\- *lemma* ideal.rank_eq
- \+/\- *lemma* ideal.rank_eq
- \+/\- *theorem* ideal.exists_smith_normal_form
- \+/\- *theorem* ideal.exists_smith_normal_form

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+/\- *lemma* exists_mul_vec_eq_zero_iff'
- \+/\- *lemma* exists_mul_vec_eq_zero_iff
- \+/\- *lemma* exists_vec_mul_eq_zero_iff
- \+/\- *lemma* exists_mul_vec_eq_zero_iff'
- \+/\- *lemma* exists_mul_vec_eq_zero_iff
- \+/\- *lemma* exists_vec_mul_eq_zero_iff
- \+/\- *theorem* nondegenerate_iff_det_ne_zero
- \+/\- *theorem* nondegenerate_iff_det_ne_zero

modified src/linear_algebra/sesquilinear_form.lean

modified src/number_theory/class_number/finite.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/class_group.lean

modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* dimension_le_one.is_integral_closure
- \+/\- *lemma* dimension_le_one.integral_closure
- \+/\- *lemma* mul_generator_self_inv
- \+/\- *lemma* dimension_le_one.is_integral_closure
- \+/\- *lemma* dimension_le_one.integral_closure
- \+/\- *lemma* mul_generator_self_inv

modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* of_ufd_of_unique_irreducible
- \+/\- *lemma* of_has_unit_mul_pow_irreducible_factorization
- \+/\- *lemma* of_ufd_of_unique_irreducible
- \+/\- *lemma* of_has_unit_mul_pow_irreducible_factorization
- \+/\- *theorem* iff_pid_with_one_nonzero_prime
- \+/\- *theorem* iff_pid_with_one_nonzero_prime
- \+/\- *def* has_unit_mul_pow_irreducible_factorization
- \+/\- *def* has_unit_mul_pow_irreducible_factorization

modified src/ring_theory/eisenstein_criterion.lean

modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ne_zero_of_mul_eq_one
- \+/\- *lemma* mk'_mul_coe_ideal_eq_coe_ideal
- \+/\- *lemma* span_singleton_mul_coe_ideal_eq_coe_ideal
- \+/\- *lemma* ne_zero_of_mul_eq_one
- \+/\- *lemma* mk'_mul_coe_ideal_eq_coe_ideal
- \+/\- *lemma* span_singleton_mul_coe_ideal_eq_coe_ideal

modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* order_mul
- \+/\- *lemma* is_pwo_Union_support_powers
- \+/\- *lemma* order_mul
- \+/\- *lemma* is_pwo_Union_support_powers

modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* bot_prime
- \+/\- *lemma* span_singleton_eq_span_singleton
- \+/\- *lemma* span_singleton_lt_span_singleton
- \+/\- *lemma* factors_decreasing
- \+/\- *lemma* bot_prime
- \+/\- *lemma* span_singleton_eq_span_singleton
- \+/\- *lemma* span_singleton_lt_span_singleton
- \+/\- *lemma* factors_decreasing

modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* mul_eq_bot
- \+/\- *lemma* prod_eq_bot
- \+/\- *lemma* radical_bot_of_integral_domain
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* mul_eq_bot
- \+/\- *lemma* prod_eq_bot
- \+/\- *lemma* radical_bot_of_integral_domain
- \+/\- *lemma* ker_is_prime

modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* exists_coeff_ne_zero_mem_comap_of_root_mem
- \+/\- *lemma* comap_lt_comap_of_integral_mem_sdiff
- \+/\- *lemma* comap_ne_bot_of_root_mem
- \+/\- *lemma* is_maximal_of_is_integral_of_is_maximal_comap'
- \+/\- *lemma* comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* comap_ne_bot_of_integral_mem
- \+/\- *lemma* eq_bot_of_comap_eq_bot
- \+/\- *lemma* is_maximal_comap_of_is_integral_of_is_maximal'
- \+/\- *lemma* is_integral_closure.comap_ne_bot
- \+/\- *lemma* is_integral_closure.eq_bot_of_comap_eq_bot
- \+/\- *lemma* integral_closure.comap_ne_bot
- \+/\- *lemma* integral_closure.eq_bot_of_comap_eq_bot
- \+/\- *lemma* exists_ideal_over_maximal_of_is_integral
- \+/\- *lemma* exists_coeff_ne_zero_mem_comap_of_root_mem
- \+/\- *lemma* comap_ne_bot_of_root_mem
- \+/\- *lemma* comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* comap_ne_bot_of_integral_mem
- \+/\- *lemma* eq_bot_of_comap_eq_bot
- \+/\- *lemma* comap_lt_comap_of_integral_mem_sdiff
- \+/\- *lemma* is_maximal_of_is_integral_of_is_maximal_comap'
- \+/\- *lemma* is_maximal_comap_of_is_integral_of_is_maximal'
- \+/\- *lemma* is_integral_closure.comap_ne_bot
- \+/\- *lemma* is_integral_closure.eq_bot_of_comap_eq_bot
- \+/\- *lemma* integral_closure.comap_ne_bot
- \+/\- *lemma* integral_closure.eq_bot_of_comap_eq_bot
- \+/\- *lemma* exists_ideal_over_maximal_of_is_integral

modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_field_of_is_integral_of_is_field
- \+/\- *lemma* is_field_of_is_integral_of_is_field

modified src/ring_theory/integral_domain.lean

modified src/ring_theory/integrally_closed.lean

modified src/ring_theory/jacobson.lean
- \+/\- *lemma* jacobson_bot_of_integral_localization
- \+/\- *lemma* is_maximal_comap_C_of_is_maximal
- \+/\- *lemma* is_maximal_comap_C_of_is_jacobson
- \+/\- *lemma* quotient_mk_comp_C_is_integral_of_jacobson
- \+/\- *lemma* comp_C_integral_of_surjective_of_jacobson
- \+/\- *lemma* jacobson_bot_of_integral_localization
- \+/\- *lemma* is_maximal_comap_C_of_is_maximal
- \+/\- *lemma* is_maximal_comap_C_of_is_jacobson
- \+/\- *lemma* quotient_mk_comp_C_is_integral_of_jacobson
- \+/\- *lemma* comp_C_integral_of_surjective_of_jacobson

modified src/ring_theory/localization.lean
- \+/\- *lemma* localization_map_bijective_of_field
- \+/\- *lemma* localization_map_bijective_of_field
- \+ *theorem* integral_domain_of_le_non_zero_divisors
- \+ *theorem* integral_domain_localization
- \+ *theorem* to_integral_domain
- \- *def* integral_domain_of_le_non_zero_divisors
- \- *def* integral_domain_localization
- \- *def* to_integral_domain

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/norm.lean
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis

modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* exists_irreducible_of_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_ne_zero
- \+ *theorem* integral_domain_fintype
- \+/\- *theorem* exists_irreducible_of_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_ne_zero
- \- *def* integral_domain_fintype

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* cyclotomic'_zero
- \+/\- *lemma* cyclotomic'_one
- \+/\- *lemma* cyclotomic'_two
- \+/\- *lemma* cyclotomic'.monic
- \+/\- *lemma* cyclotomic'_ne_zero
- \+/\- *lemma* roots_of_cyclotomic
- \+/\- *lemma* cyclotomic'_zero
- \+/\- *lemma* cyclotomic'_one
- \+/\- *lemma* cyclotomic'_two
- \+/\- *lemma* cyclotomic'.monic
- \+/\- *lemma* cyclotomic'_ne_zero
- \+/\- *lemma* roots_of_cyclotomic
- \+/\- *def* cyclotomic'
- \+/\- *def* cyclotomic'

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/polynomial/scale_roots.lean

modified src/ring_theory/power_basis.lean
- \+/\- *lemma* degree_minpoly_gen
- \+/\- *lemma* nat_degree_minpoly_gen
- \+/\- *lemma* minpoly_gen_monic
- \+/\- *lemma* is_integral_gen
- \+/\- *lemma* degree_minpoly_gen
- \+/\- *lemma* nat_degree_minpoly_gen
- \+/\- *lemma* minpoly_gen_monic
- \+/\- *lemma* is_integral_gen

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* is_field.is_principal_ideal_ring
- \+/\- *lemma* ne_zero_of_mem_factors
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* is_field.is_principal_ideal_ring
- \+/\- *lemma* ne_zero_of_mem_factors

modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* roots_of_unity.coe_pow
- \+/\- *lemma* ring_hom.restrict_roots_of_unity_coe_apply
- \+/\- *lemma* ring_equiv.restrict_roots_of_unity_coe_apply
- \+/\- *lemma* ring_equiv.restrict_roots_of_unity_symm
- \+/\- *lemma* pow
- \+/\- *lemma* roots_of_unity.coe_pow
- \+/\- *lemma* ring_hom.restrict_roots_of_unity_coe_apply
- \+/\- *lemma* ring_equiv.restrict_roots_of_unity_coe_apply
- \+/\- *lemma* ring_equiv.restrict_roots_of_unity_symm
- \+/\- *lemma* pow
- \+/\- *def* ring_hom.restrict_roots_of_unity
- \+/\- *def* ring_equiv.restrict_roots_of_unity
- \+/\- *def* primitive_roots
- \+/\- *def* ring_hom.restrict_roots_of_unity
- \+/\- *def* ring_equiv.restrict_roots_of_unity
- \+/\- *def* primitive_roots

modified src/ring_theory/subring.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/ring_theory/valuation/integral.lean



## [2021-10-19 07:46:18](https://github.com/leanprover-community/mathlib/commit/a7bc717)
feat(algebra/big_operators/order): Upper bound on the cardinality of `finset.bUnion` ([#9797](https://github.com/leanprover-community/mathlib/pull/9797))
Also fix notation in all the additivized statements docstrings.
#### Estimated changes
modified src/algebra/big_operators/order.lean
- \+ *lemma* card_bUnion_le_card_mul



## [2021-10-19 07:46:17](https://github.com/leanprover-community/mathlib/commit/4df649c)
feat(data/nat/modeq): Upper bound for `chinese_remainder` ([#9783](https://github.com/leanprover-community/mathlib/pull/9783))
Proves that `chinese_remainder' < lcm n m` and `chinese_remainder < n * m`, as claimed by the doc-strings.
#### Estimated changes
modified src/data/nat/modeq.lean
- \+ *lemma* chinese_remainder'_lt_lcm
- \+ *lemma* chinese_remainder_lt_mul



## [2021-10-19 07:05:07](https://github.com/leanprover-community/mathlib/commit/1f8c96b)
feat(data/nat/succ_pred): `ℕ` is succ- and pred- archimedean ([#9730](https://github.com/leanprover-community/mathlib/pull/9730))
This provides the instances `succ_order ℕ`, `pred_order ℕ`, `is_succ_archimedean ℕ`, `is_pred_archimedean ℕ`.
#### Estimated changes
created src/data/nat/succ_pred.lean
- \+ *lemma* nat.succ_iterate
- \+ *lemma* nat.pred_iterate

modified src/order/succ_pred.lean
- \+/\- *lemma* succ_lt_succ_iff
- \+/\- *lemma* succ_lt_succ_iff



## [2021-10-19 04:41:01](https://github.com/leanprover-community/mathlib/commit/1ec385d)
chore(scripts): update nolints.txt ([#9799](https://github.com/leanprover-community/mathlib/pull/9799))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-10-19 02:24:00](https://github.com/leanprover-community/mathlib/commit/04094c4)
feat(analysis/box_integral): Divergence thm for a Henstock-style integral ([#9496](https://github.com/leanprover-community/mathlib/pull/9496))
* Define integrals of Riemann, McShane, and Henstock (plus a few
  variations).
* Prove basic properties.
* Prove a version of the divergence theorem for one of these integrals.
* Prove that a Bochner integrable function is McShane integrable.
#### Estimated changes
modified docs/references.bib

modified src/algebra/order/field.lean
- \+ *lemma* left_lt_add_div_two
- \+ *lemma* add_div_two_lt_right
- \+ *lemma* exists_pos_mul_lt

created src/analysis/box_integral/basic.lean
- \+ *lemma* integral_sum_bUnion_tagged
- \+ *lemma* integral_sum_bUnion_partition
- \+ *lemma* integral_sum_inf_partition
- \+ *lemma* integral_sum_fiberwise
- \+ *lemma* integral_sum_sub_partitions
- \+ *lemma* integral_sum_disj_union
- \+ *lemma* integral_sum_add
- \+ *lemma* integral_sum_neg
- \+ *lemma* integral_sum_smul
- \+ *lemma* has_integral.tendsto
- \+ *lemma* has_integral_iff
- \+ *lemma* has_integral_of_mul
- \+ *lemma* integrable_iff_cauchy
- \+ *lemma* integrable_iff_cauchy_basis
- \+ *lemma* has_integral.mono
- \+ *lemma* integrable.mono
- \+ *lemma* has_integral.unique
- \+ *lemma* has_integral.integrable
- \+ *lemma* has_integral.integral_eq
- \+ *lemma* has_integral.add
- \+ *lemma* integrable.add
- \+ *lemma* integral_add
- \+ *lemma* has_integral.neg
- \+ *lemma* integrable.neg
- \+ *lemma* integrable.of_neg
- \+ *lemma* integrable_neg
- \+ *lemma* integral_neg
- \+ *lemma* has_integral.sub
- \+ *lemma* integrable.sub
- \+ *lemma* integral_sub
- \+ *lemma* has_integral_const
- \+ *lemma* integral_const
- \+ *lemma* integrable_const
- \+ *lemma* has_integral_zero
- \+ *lemma* integrable_zero
- \+ *lemma* integral_zero
- \+ *lemma* has_integral_sum
- \+ *lemma* has_integral.smul
- \+ *lemma* integrable.smul
- \+ *lemma* integrable.of_smul
- \+ *lemma* integral_smul
- \+ *lemma* integral_nonneg
- \+ *lemma* norm_integral_le_of_norm_le
- \+ *lemma* norm_integral_le_of_le_const
- \+ *lemma* convergence_r_cond
- \+ *lemma* dist_integral_sum_integral_le_of_mem_base_set
- \+ *lemma* dist_integral_sum_le_of_mem_base_set
- \+ *lemma* tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity
- \+ *lemma* cauchy_map_integral_sum_to_filter_Union
- \+ *lemma* to_subbox_aux
- \+ *lemma* to_subbox
- \+ *lemma* tendsto_integral_sum_to_filter_Union_single
- \+ *lemma* dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq
- \+ *lemma* dist_integral_sum_sum_integral_le_of_mem_base_set
- \+ *lemma* tendsto_integral_sum_sum_integral
- \+ *lemma* sum_integral_congr
- \+ *lemma* integrable_of_continuous_on
- \+ *lemma* has_integral_of_bRiemann_eq_ff_of_forall_is_o
- \+ *lemma* has_integral_of_le_Henstock_of_forall_is_o
- \+ *lemma* has_integral_McShane_of_forall_is_o
- \+ *def* integral_sum
- \+ *def* has_integral
- \+ *def* integrable
- \+ *def* integral
- \+ *def* convergence_r
- \+ *def* to_box_additive

created src/analysis/box_integral/box/basic.lean
- \+ *lemma* lower_le_upper
- \+ *lemma* mem_mk
- \+ *lemma* mem_coe
- \+ *lemma* mem_def
- \+ *lemma* mem_univ_Ioc
- \+ *lemma* coe_eq_pi
- \+ *lemma* upper_mem
- \+ *lemma* exists_mem
- \+ *lemma* nonempty_coe
- \+ *lemma* coe_ne_empty
- \+ *lemma* empty_ne_coe
- \+ *lemma* le_def
- \+ *lemma* le_tfae
- \+ *lemma* coe_subset_coe
- \+ *lemma* le_iff_bounds
- \+ *lemma* injective_coe
- \+ *lemma* coe_inj
- \+ *lemma* ext
- \+ *lemma* ne_of_disjoint_coe
- \+ *lemma* Icc_def
- \+ *lemma* upper_mem_Icc
- \+ *lemma* lower_mem_Icc
- \+ *lemma* Icc_eq_pi
- \+ *lemma* le_iff_Icc
- \+ *lemma* antitone_lower
- \+ *lemma* monotone_upper
- \+ *lemma* coe_subset_Icc
- \+ *lemma* coe_bot
- \+ *lemma* coe_coe
- \+ *lemma* is_some_iff
- \+ *lemma* bUnion_coe_eq_coe
- \+ *lemma* with_bot_coe_subset_iff
- \+ *lemma* with_bot_coe_inj
- \+ *lemma* mk'_eq_bot
- \+ *lemma* mk'_eq_coe
- \+ *lemma* coe_mk'
- \+ *lemma* coe_inf
- \+ *lemma* disjoint_with_bot_coe
- \+ *lemma* disjoint_coe
- \+ *lemma* not_disjoint_coe_iff_nonempty_inter
- \+ *lemma* face_mk
- \+ *lemma* face_mono
- \+ *lemma* maps_to_insert_nth_face_Icc
- \+ *lemma* maps_to_insert_nth_face
- \+ *lemma* continuous_on_face_Icc
- \+ *lemma* distortion_eq_of_sub_eq_div
- \+ *lemma* nndist_le_distortion_mul
- \+ *lemma* dist_le_distortion_mul
- \+ *lemma* diam_Icc_le_of_distortion_le
- \+ *def* mk'
- \+ *def* face
- \+ *def* distortion

created src/analysis/box_integral/box/subbox_induction.lean
- \+ *lemma* mem_split_center_box
- \+ *lemma* split_center_box_le
- \+ *lemma* disjoint_split_center_box
- \+ *lemma* injective_split_center_box
- \+ *lemma* exists_mem_split_center_box
- \+ *lemma* Union_coe_split_center_box
- \+ *lemma* upper_sub_lower_split_center_box
- \+ *lemma* subbox_induction_on'
- \+ *def* split_center_box
- \+ *def* split_center_box_emb

created src/analysis/box_integral/divergence_theorem.lean
- \+ *lemma* norm_volume_sub_integral_face_upper_sub_lower_smul_le
- \+ *lemma* has_integral_bot_pderiv
- \+ *lemma* has_integral_bot_divergence_of_forall_has_deriv_within_at

created src/analysis/box_integral/integrability.lean
- \+ *lemma* has_integral_indicator_const
- \+ *lemma* has_integral_zero_of_ae_eq_zero
- \+ *lemma* has_integral.congr_ae
- \+ *lemma* has_box_integral
- \+ *lemma* box_integral_eq_integral
- \+ *lemma* integrable_on.has_box_integral

created src/analysis/box_integral/partition/additive.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* coe_injective
- \+ *lemma* coe_inj
- \+ *lemma* sum_partition_boxes
- \+ *lemma* map_split_add
- \+ *lemma* sum_boxes_congr
- \+ *lemma* to_smul_apply
- \+ *def* restrict
- \+ *def* of_map_split_add
- \+ *def* map
- \+ *def* to_smul
- \+ *def* {u}

created src/analysis/box_integral/partition/basic.lean
- \+ *lemma* mem_boxes
- \+ *lemma* mem_mk
- \+ *lemma* disjoint_coe_of_mem
- \+ *lemma* eq_of_mem_of_mem
- \+ *lemma* eq_of_le_of_le
- \+ *lemma* eq_of_le
- \+ *lemma* le_of_mem
- \+ *lemma* lower_le_lower
- \+ *lemma* upper_le_upper
- \+ *lemma* injective_boxes
- \+ *lemma* ext
- \+ *lemma* mem_single
- \+ *lemma* le_def
- \+ *lemma* mem_top
- \+ *lemma* top_boxes
- \+ *lemma* not_mem_bot
- \+ *lemma* bot_boxes
- \+ *lemma* inj_on_set_of_mem_Icc_set_of_lower_eq
- \+ *lemma* card_filter_mem_Icc_le
- \+ *lemma* Union_def
- \+ *lemma* Union_def'
- \+ *lemma* mem_Union
- \+ *lemma* Union_single
- \+ *lemma* Union_top
- \+ *lemma* Union_eq_empty
- \+ *lemma* Union_bot
- \+ *lemma* subset_Union
- \+ *lemma* Union_subset
- \+ *lemma* Union_mono
- \+ *lemma* disjoint_boxes_of_disjoint_Union
- \+ *lemma* le_iff_nonempty_imp_le_and_Union_subset
- \+ *lemma* eq_of_boxes_subset_Union_superset
- \+ *lemma* mem_bUnion
- \+ *lemma* bUnion_le
- \+ *lemma* bUnion_top
- \+ *lemma* bUnion_congr
- \+ *lemma* bUnion_congr_of_le
- \+ *lemma* Union_bUnion
- \+ *lemma* sum_bUnion_boxes
- \+ *lemma* bUnion_index_mem
- \+ *lemma* bUnion_index_le
- \+ *lemma* mem_bUnion_index
- \+ *lemma* le_bUnion_index
- \+ *lemma* bUnion_index_of_mem
- \+ *lemma* bUnion_assoc
- \+ *lemma* mem_of_with_bot
- \+ *lemma* Union_of_with_bot
- \+ *lemma* of_with_bot_le
- \+ *lemma* le_of_with_bot
- \+ *lemma* of_with_bot_mono
- \+ *lemma* sum_of_with_bot
- \+ *lemma* mem_restrict
- \+ *lemma* mem_restrict'
- \+ *lemma* restrict_mono
- \+ *lemma* monotone_restrict
- \+ *lemma* restrict_boxes_of_le
- \+ *lemma* restrict_self
- \+ *lemma* Union_restrict
- \+ *lemma* restrict_bUnion
- \+ *lemma* bUnion_le_iff
- \+ *lemma* le_bUnion_iff
- \+ *lemma* inf_def
- \+ *lemma* mem_inf
- \+ *lemma* Union_inf
- \+ *lemma* mem_filter
- \+ *lemma* filter_le
- \+ *lemma* filter_of_true
- \+ *lemma* filter_true
- \+ *lemma* Union_filter_not
- \+ *lemma* sum_fiberwise
- \+ *lemma* mem_disj_union
- \+ *lemma* Union_disj_union
- \+ *lemma* sum_disj_union_boxes
- \+ *lemma* distortion_le_of_mem
- \+ *lemma* distortion_le_iff
- \+ *lemma* distortion_bUnion
- \+ *lemma* distortion_disj_union
- \+ *lemma* distortion_of_const
- \+ *lemma* distortion_top
- \+ *lemma* distortion_bot
- \+ *lemma* is_partition_iff_Union_eq
- \+ *lemma* is_partition_single_iff
- \+ *lemma* is_partition_top
- \+ *lemma* Union_eq
- \+ *lemma* Union_subset
- \+ *lemma* nonempty_boxes
- \+ *lemma* eq_of_boxes_subset
- \+ *lemma* le_iff
- \+ *lemma* Union_bUnion_partition
- \+ *lemma* is_partition_disj_union_of_eq_diff
- \+ *def* single
- \+ *def* bUnion
- \+ *def* bUnion_index
- \+ *def* of_with_bot
- \+ *def* restrict
- \+ *def* filter
- \+ *def* disj_union
- \+ *def* distortion
- \+ *def* is_partition

created src/analysis/box_integral/partition/filter.lean
- \+ *lemma* Henstock_le_Riemann
- \+ *lemma* Henstock_le_McShane
- \+ *lemma* r_cond_of_bRiemann_eq_ff
- \+ *lemma* to_filter_inf_Union_eq
- \+ *lemma* mem_base_set.mono'
- \+ *lemma* mem_base_set.mono
- \+ *lemma* mem_base_set.exists_common_compl
- \+ *lemma* bUnion_tagged_mem_base_set
- \+ *lemma* r_cond.mono
- \+ *lemma* r_cond.min
- \+ *lemma* to_filter_distortion_mono
- \+ *lemma* to_filter_mono
- \+ *lemma* to_filter_Union_mono
- \+ *lemma* to_filter_Union_congr
- \+ *lemma* has_basis_to_filter_distortion
- \+ *lemma* has_basis_to_filter_distortion_Union
- \+ *lemma* has_basis_to_filter_Union
- \+ *lemma* has_basis_to_filter_Union_top
- \+ *lemma* has_basis_to_filter
- \+ *lemma* tendsto_embed_box_to_filter_Union_top
- \+ *lemma* exists_mem_base_set_le_Union_eq
- \+ *lemma* exists_mem_base_set_is_partition
- \+ *lemma* to_filter_distortion_Union_ne_bot
- \+ *lemma* eventually_is_partition
- \+ *def* equiv_prod
- \+ *def* iso_prod
- \+ *def* Riemann
- \+ *def* Henstock
- \+ *def* McShane
- \+ *def* r_cond
- \+ *def* to_filter_distortion
- \+ *def* to_filter
- \+ *def* to_filter_distortion_Union
- \+ *def* to_filter_Union

created src/analysis/box_integral/partition/measure.lean
- \+ *lemma* measurable_set_coe
- \+ *lemma* measurable_set_Icc
- \+ *lemma* measure_Icc_lt_top
- \+ *lemma* measure_coe_lt_top
- \+ *lemma* prepartition.measure_Union_to_real
- \+ *lemma* volume_apply
- \+ *lemma* volume_face_mul
- \+ *lemma* volume_apply
- \+ *def* to_box_additive

created src/analysis/box_integral/partition/split.lean
- \+ *lemma* coe_split_lower
- \+ *lemma* split_lower_le
- \+ *lemma* split_lower_eq_bot
- \+ *lemma* split_lower_eq_self
- \+ *lemma* split_lower_def
- \+ *lemma* coe_split_upper
- \+ *lemma* split_upper_le
- \+ *lemma* split_upper_eq_bot
- \+ *lemma* split_upper_eq_self
- \+ *lemma* split_upper_def
- \+ *lemma* disjoint_split_lower_split_upper
- \+ *lemma* split_lower_ne_split_upper
- \+ *lemma* mem_split_iff
- \+ *lemma* mem_split_iff'
- \+ *lemma* Union_split
- \+ *lemma* is_partition_split
- \+ *lemma* sum_split_boxes
- \+ *lemma* split_of_not_mem_Ioo
- \+ *lemma* coe_eq_of_mem_split_of_mem_le
- \+ *lemma* coe_eq_of_mem_split_of_lt_mem
- \+ *lemma* restrict_split
- \+ *lemma* inf_split
- \+ *lemma* split_many_empty
- \+ *lemma* split_many_insert
- \+ *lemma* split_many_le_split
- \+ *lemma* is_partition_split_many
- \+ *lemma* Union_split_many
- \+ *lemma* inf_split_many
- \+ *lemma* not_disjoint_imp_le_of_subset_of_mem_split_many
- \+ *lemma* eventually_not_disjoint_imp_le_of_mem_split_many
- \+ *lemma* eventually_split_many_inf_eq_filter
- \+ *lemma* exists_split_many_inf_eq_filter_of_finite
- \+ *lemma* is_partition.exists_split_many_le
- \+ *lemma* exists_Union_eq_diff
- \+ *lemma* Union_compl
- \+ *lemma* compl_congr
- \+ *lemma* is_partition.compl_eq_bot
- \+ *lemma* compl_top
- \+ *def* split_lower
- \+ *def* split_upper
- \+ *def* split
- \+ *def* split_many
- \+ *def* compl

created src/analysis/box_integral/partition/subbox_induction.lean
- \+ *lemma* mem_split_center
- \+ *lemma* is_partition_split_center
- \+ *lemma* upper_sub_lower_of_mem_split_center
- \+ *lemma* subbox_induction_on
- \+ *lemma* exists_tagged_partition_is_Henstock_is_subordinate_homothetic
- \+ *lemma* exists_tagged_le_is_Henstock_is_subordinate_Union_eq
- \+ *lemma* to_subordinate_to_prepartition_le
- \+ *lemma* is_Henstock_to_subordinate
- \+ *lemma* is_subordinate_to_subordinate
- \+ *lemma* distortion_to_subordinate
- \+ *lemma* Union_to_subordinate
- \+ *lemma* is_partition_union_compl_to_subordinate
- \+ *lemma* union_compl_to_subordinate_boxes
- \+ *lemma* Union_union_compl_to_subordinate_boxes
- \+ *lemma* distortion_union_compl_to_subordinate
- \+ *def* split_center
- \+ *def* to_subordinate
- \+ *def* union_compl_to_subordinate

created src/analysis/box_integral/partition/tagged.lean
- \+ *lemma* mem_to_prepartition
- \+ *lemma* mem_mk
- \+ *lemma* Union_def
- \+ *lemma* Union_mk
- \+ *lemma* Union_to_prepartition
- \+ *lemma* mem_Union
- \+ *lemma* subset_Union
- \+ *lemma* Union_subset
- \+ *lemma* is_partition_iff_Union_eq
- \+ *lemma* mem_filter
- \+ *lemma* Union_filter_not
- \+ *lemma* mem_bUnion_tagged
- \+ *lemma* tag_bUnion_tagged
- \+ *lemma* Union_bUnion_tagged
- \+ *lemma* forall_bUnion_tagged
- \+ *lemma* is_partition.bUnion_tagged
- \+ *lemma* is_partition.bUnion_prepartition
- \+ *lemma* inf_prepartition_to_prepartition
- \+ *lemma* mem_inf_prepartition_comm
- \+ *lemma* is_partition.inf_prepartition
- \+ *lemma* is_Henstock_bUnion_tagged
- \+ *lemma* is_Henstock.card_filter_tag_eq_le
- \+ *lemma* is_subordinate_bUnion_tagged
- \+ *lemma* is_subordinate.bUnion_prepartition
- \+ *lemma* is_subordinate.inf_prepartition
- \+ *lemma* is_subordinate.mono'
- \+ *lemma* is_subordinate.mono
- \+ *lemma* is_subordinate.diam_le
- \+ *lemma* mem_single
- \+ *lemma* is_partition_single_iff
- \+ *lemma* is_partition_single
- \+ *lemma* forall_mem_single
- \+ *lemma* is_Henstock_single_iff
- \+ *lemma* is_Henstock_single
- \+ *lemma* is_subordinate_single
- \+ *lemma* Union_single
- \+ *lemma* disj_union_boxes
- \+ *lemma* mem_disj_union
- \+ *lemma* Union_disj_union
- \+ *lemma* disj_union_tag_of_mem_left
- \+ *lemma* disj_union_tag_of_mem_right
- \+ *lemma* is_subordinate.disj_union
- \+ *lemma* is_Henstock.disj_union
- \+ *lemma* distortion_le_of_mem
- \+ *lemma* distortion_le_iff
- \+ *lemma* _root_.box_integral.prepartition.distortion_bUnion_tagged
- \+ *lemma* distortion_bUnion_prepartition
- \+ *lemma* distortion_disj_union
- \+ *lemma* distortion_of_const
- \+ *lemma* distortion_single
- \+ *lemma* distortion_filter_le
- \+ *def* Union
- \+ *def* is_partition
- \+ *def* filter
- \+ *def* bUnion_tagged
- \+ *def* bUnion_prepartition
- \+ *def* inf_prepartition
- \+ *def* is_Henstock
- \+ *def* is_subordinate
- \+ *def* single
- \+ *def* disj_union
- \+ *def* embed_box
- \+ *def* distortion

modified src/data/set/lattice.lean
- \+ *lemma* bUnion_diff_bUnion_subset
- \+ *lemma* bUnion_diff_bUnion_eq

modified src/logic/function/basic.lean
- \+ *lemma* exists_update_iff

modified src/topology/metric_space/basic.lean
- \+ *lemma* real.dist_le_of_mem_pi_Icc



## [2021-10-18 23:50:42](https://github.com/leanprover-community/mathlib/commit/5eee6a2)
refactor(ring_theory/adjoin/fg): replace a fragile convert with rewrites ([#9786](https://github.com/leanprover-community/mathlib/pull/9786))
#### Estimated changes
modified src/ring_theory/adjoin/fg.lean



## [2021-10-18 23:50:41](https://github.com/leanprover-community/mathlib/commit/98d07d3)
refactor(algebra/order): replace typeclasses with constructors ([#9725](https://github.com/leanprover-community/mathlib/pull/9725))
This RFC suggests removing some unused classes for the ordered algebra hierarchy, replacing them with constructors
We have `nonneg_add_comm_group extends add_comm_group`, and an instance from this to `ordered_add_comm_group`. The intention is to be able to construct an `ordered_add_comm_group` by specifying its positive cone, rather than directly its order.
There are then `nonneg_ring` and `linear_nonneg_ring`, similarly.
(None of these are actually used later in mathlib at this point.)
#### Estimated changes
modified src/algebra/order/group.lean
- \- *theorem* nonneg_def
- \- *theorem* pos_def
- \- *theorem* not_zero_pos
- \- *theorem* zero_lt_iff_nonneg_nonneg
- \- *theorem* nonneg_total_iff
- \+ *def* mk_of_positive_cone
- \+ *def* mk_of_positive_cone
- \- *def* to_linear_ordered_add_comm_group

modified src/algebra/order/ring.lean
- \+ *def* mk_of_positive_cone
- \+ *def* mk_of_positive_cone
- \- *def* to_linear_nonneg_ring
- \- *def* to_linear_order
- \- *def* to_linear_ordered_ring
- \- *def* to_linear_ordered_comm_ring



## [2021-10-18 23:50:40](https://github.com/leanprover-community/mathlib/commit/442382d)
feat(tactic/to_additive): Improvements to to_additive ([#5487](https://github.com/leanprover-community/mathlib/pull/5487))
Change a couple of things in to_additive:
- First add a `tactic.copy_attribute'` intended for user attributes with parameters very similar to `tactic.copy_attribute` that just copies the parameter over when setting the attribute. This allows to_additive after many other attributes to transfer those attributes properly (e.g. norm_cast)
- Have to additive register generated equation lemmas as such, this necessitates a bit of restructuring, first all declarations must be generated (including equational lemmas), then the equational lemmas need their attributes, then they are registered as equation lemmas, finally the attributes are added to the main declaration.
- I also fixup the library in many places to account for these changes simplifying the source files, only one new lemma was added, in src/analysis/normed/group/quotient.lean `quotient_norm_mk_le'` to replace the unprimed version in the proof of `norm_normed_mk_le` as simp got better thanks to the new simp lemmas introduced by this PR. Probably many more handwritten additive versions can now be deleted in a future PR, especially defs and instances.
- All other library changes are just simplifications by using to additive for some hand generated declarations, and many more attributes on the generated lemmas.
- The attribute mono is trickier as it contains for its parameter not actual exprs containing names but exprs making names from strings, so I don't see how to handle it right now. We now warn the user about this, and fix the library in a couple of places.
#### Estimated changes
modified src/algebra/big_operators/order.lean

modified src/algebra/category/Group/basic.lean

modified src/algebra/category/Mon/filtered_colimits.lean

modified src/algebra/free.lean

modified src/algebra/free_monoid.lean

modified src/algebra/group/basic.lean

modified src/algebra/group/defs.lean

modified src/algebra/group/hom.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group/units.lean

modified src/algebra/group/with_one.lean

modified src/algebra/group_power/order.lean

modified src/algebra/order/monoid.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_one
- \+/\- *theorem* one_eq_coe
- \+/\- *theorem* one_eq_coe

modified src/analysis/normed/group/quotient.lean
- \+/\- *lemma* quotient_norm_sub_rev
- \+ *lemma* quotient_norm_mk_le'
- \+/\- *lemma* quotient_norm_sub_rev

modified src/data/dfinsupp.lean
- \- *def* sum

modified src/data/equiv/mul_add.lean
- \- *def* add_monoid_hom.to_add_equiv

modified src/data/equiv/mul_add_aut.lean

modified src/data/finsupp/basic.lean
- \- *def* sum

modified src/data/multiset/basic.lean

modified src/group_theory/congruence.lean

modified src/group_theory/coset.lean
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* one_left_coset
- \+/\- *lemma* right_coset_one
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* one_left_coset
- \+/\- *lemma* right_coset_one

modified src/group_theory/group_action/defs.lean

modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

modified src/group_theory/quotient_group.lean

modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* to_submonoid_strict_mono
- \+/\- *lemma* to_submonoid_strict_mono

modified src/group_theory/submonoid/basic.lean
- \+/\- *lemma* coe_of_mdense
- \+/\- *lemma* coe_of_mdense

modified src/group_theory/submonoid/membership.lean

modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one

modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* mk_div
- \+/\- *lemma* mk_div

modified src/order/filter/germ.lean

modified src/tactic/transform_decl.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* mem_coe
- \+/\- *lemma* mem_coe_opens
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_subset
- \+/\- *lemma* coe_subgroup_le
- \+/\- *lemma* mem_coe
- \+/\- *lemma* mem_coe_opens
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_subset
- \+/\- *lemma* coe_subgroup_le

modified src/topology/tactic.lean

modified test/to_additive.lean



## [2021-10-18 21:08:15](https://github.com/leanprover-community/mathlib/commit/8b7e16f)
feat(tactic/lint): improve check_univs linter ([#9698](https://github.com/leanprover-community/mathlib/pull/9698))
* `check_univs` now only checks the type of `d` and ignores `d._proof_i` subterms
* move `expr.univ_params_grouped` to the linter file (it seems increasingly unlikely that this has a use in other applications)
* We now don't test automatically generated declarations anymore.
#### Estimated changes
modified src/category_theory/category/Cat.lean

modified src/category_theory/category/Groupoid.lean

modified src/category_theory/category/Quiv.lean

modified src/meta/expr.lean

modified src/model_theory/basic.lean

modified src/set_theory/ordinal.lean

modified src/set_theory/zfc.lean

modified src/tactic/lint/misc.lean



## [2021-10-18 17:55:59](https://github.com/leanprover-community/mathlib/commit/b112d4d)
refactor(ring_theory/ideal/operations): generalize various definitions to remove negation and commutativity ([#9737](https://github.com/leanprover-community/mathlib/pull/9737))
Mostly this just weakens assumptions in `variable`s lines, but occasionally this moves lemmas to a more appropriate section too.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* le_map_of_comap_le_of_surjective
- \+/\- *lemma* comap_bot_le_of_injective
- \+/\- *lemma* comap_le_iff_le_map
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* le_map_of_comap_le_of_surjective
- \+/\- *lemma* comap_bot_le_of_injective
- \+/\- *lemma* comap_le_iff_le_map
- \+/\- *lemma* not_one_mem_ker
- \+/\- *theorem* mem_colon
- \+/\- *theorem* mem_colon'
- \+/\- *theorem* colon_mono
- \+/\- *theorem* infi_colon_supr
- \+/\- *theorem* subset_union
- \+/\- *theorem* subset_union_prime'
- \+/\- *theorem* subset_union_prime
- \+/\- *theorem* comap_map_of_surjective
- \+/\- *theorem* map_eq_top_or_is_maximal_of_surjective
- \+/\- *theorem* comap_is_maximal_of_surjective
- \+/\- *theorem* map.is_maximal
- \+/\- *theorem* mem_colon
- \+/\- *theorem* mem_colon'
- \+/\- *theorem* colon_mono
- \+/\- *theorem* infi_colon_supr
- \+/\- *theorem* subset_union
- \+/\- *theorem* subset_union_prime'
- \+/\- *theorem* subset_union_prime
- \+/\- *theorem* comap_map_of_surjective
- \+/\- *theorem* map_eq_top_or_is_maximal_of_surjective
- \+/\- *theorem* comap_is_maximal_of_surjective
- \+/\- *theorem* map.is_maximal
- \+/\- *def* colon
- \+/\- *def* rel_iso_of_surjective
- \+/\- *def* colon
- \+/\- *def* rel_iso_of_surjective

modified src/ring_theory/jacobson.lean



## [2021-10-18 16:41:10](https://github.com/leanprover-community/mathlib/commit/71c203a)
feat(analysis/normed/group/SemiNormedGroup/completion): add SemiNormedGroup.Completion ([#9788](https://github.com/leanprover-community/mathlib/pull/9788))
From LTE.
#### Estimated changes
created src/analysis/normed/group/SemiNormedGroup/completion.lean
- \+ *lemma* Completion.norm_incl_eq
- \+ *lemma* Completion.map_norm_noninc
- \+ *lemma* Completion.map_zero
- \+ *lemma* Completion.lift_comp_incl
- \+ *lemma* Completion.lift_unique
- \+ *def* Completion
- \+ *def* Completion.incl
- \+ *def* Completion.map_hom
- \+ *def* Completion.lift

modified src/analysis/normed/group/hom_completion.lean
- \+ *lemma* normed_group_hom.extension_def
- \+ *lemma* normed_group_hom.extension_coe
- \+ *lemma* normed_group_hom.extension_coe_to_fun
- \+ *lemma* normed_group_hom.extension_unique
- \+ *def* normed_group_hom.extension



## [2021-10-18 16:41:09](https://github.com/leanprover-community/mathlib/commit/80071d4)
refactor(algebra/floor): Add `ceil` as a field of `floor_ring` ([#9591](https://github.com/leanprover-community/mathlib/pull/9591))
This allows more control on definitional equality.
#### Estimated changes
modified src/algebra/archimedean.lean

modified src/algebra/floor.lean
- \+ *lemma* floor_ring_floor_eq
- \+ *lemma* floor_ring_ceil_eq
- \+ *lemma* gc_coe_floor
- \+/\- *lemma* le_floor
- \+/\- *lemma* floor_lt
- \+/\- *lemma* floor_le
- \+/\- *lemma* floor_nonneg
- \+/\- *lemma* floor_mono
- \+/\- *lemma* floor_eq_iff
- \+ *lemma* gc_ceil_coe
- \+/\- *lemma* ceil_le
- \+/\- *lemma* floor_neg
- \+/\- *lemma* ceil_neg
- \+/\- *lemma* lt_ceil
- \+/\- *lemma* le_ceil
- \+/\- *lemma* ceil_mono
- \+/\- *lemma* ceil_pos
- \+/\- *lemma* ceil_nonneg
- \+/\- *lemma* ceil_eq_iff
- \+/\- *lemma* preimage_Ioi
- \+/\- *lemma* preimage_Ici
- \+/\- *lemma* preimage_Iio
- \+/\- *lemma* preimage_Iic
- \+/\- *lemma* floor_add_one
- \+/\- *lemma* ceil_add_nat
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_lt_add_one
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+/\- *lemma* le_floor
- \+/\- *lemma* floor_lt
- \+/\- *lemma* floor_le
- \+/\- *lemma* floor_nonneg
- \+/\- *lemma* floor_mono
- \+/\- *lemma* floor_eq_iff
- \+/\- *lemma* ceil_le
- \+/\- *lemma* floor_neg
- \+/\- *lemma* ceil_neg
- \+/\- *lemma* lt_ceil
- \+/\- *lemma* le_ceil
- \+/\- *lemma* ceil_mono
- \+/\- *lemma* ceil_pos
- \+/\- *lemma* ceil_nonneg
- \+/\- *lemma* ceil_eq_iff
- \+/\- *lemma* preimage_Ioi
- \+/\- *lemma* preimage_Ici
- \+/\- *lemma* preimage_Iio
- \+/\- *lemma* preimage_Iic
- \+/\- *lemma* floor_add_one
- \+/\- *lemma* ceil_add_nat
- \+/\- *lemma* ceil_add_one
- \+/\- *lemma* ceil_lt_add_one
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+ *def* floor_ring.of_floor
- \+ *def* floor_ring.of_ceil
- \+/\- *def* ceil
- \+/\- *def* ceil

modified src/data/rat/floor.lean

modified src/topology/algebra/floor_ring.lean



## [2021-10-18 14:15:51](https://github.com/leanprover-community/mathlib/commit/5ea384e)
refactor(ring_theory/finiteness): replace fragile convert with rewrites ([#9787](https://github.com/leanprover-community/mathlib/pull/9787))
#### Estimated changes
modified src/algebra/algebra/tower.lean
- \+ *lemma* coe_restrict_scalars

modified src/ring_theory/finiteness.lean



## [2021-10-18 14:15:49](https://github.com/leanprover-community/mathlib/commit/6f4aea4)
feat(data/set/pairwise): Simple `pairwise_disjoint` lemmas ([#9764](https://github.com/leanprover-community/mathlib/pull/9764))
#### Estimated changes
modified src/algebra/support.lean

modified src/data/finset/basic.lean
- \+ *lemma* disjoint_singleton
- \+ *theorem* disjoint_singleton_left
- \+ *theorem* disjoint_singleton_right
- \- *theorem* singleton_disjoint
- \- *theorem* disjoint_singleton

modified src/data/finsupp/basic.lean

modified src/data/polynomial/iterated_deriv.lean

modified src/data/set/lattice.lean
- \+ *lemma* disjoint_singleton

modified src/data/set/pairwise.lean
- \+/\- *lemma* pairwise_disjoint.subset
- \+ *lemma* pairwise_disjoint_empty
- \+ *lemma* pairwise_disjoint_singleton
- \+ *lemma* pairwise_disjoint_insert
- \+ *lemma* pairwise_disjoint.insert
- \+ *lemma* pairwise_disjoint.image_of_le
- \+/\- *lemma* pairwise_disjoint.range
- \+/\- *lemma* pairwise_disjoint.elim
- \+/\- *lemma* pairwise_disjoint.elim'
- \+ *lemma* pairwise_disjoint_range_singleton
- \+/\- *lemma* pairwise_disjoint.subset
- \+/\- *lemma* pairwise_disjoint.range
- \+/\- *lemma* pairwise_disjoint.elim
- \+/\- *lemma* pairwise_disjoint.elim'

modified src/geometry/euclidean/circumcenter.lean

modified src/group_theory/specific_groups/alternating.lean

modified src/measure_theory/integral/bochner.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/separation.lean



## [2021-10-18 12:53:50](https://github.com/leanprover-community/mathlib/commit/116e426)
chore(group_theory/order_of_element): order_of_units ([#9777](https://github.com/leanprover-community/mathlib/pull/9777))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_units



## [2021-10-18 12:53:48](https://github.com/leanprover-community/mathlib/commit/a7ac699)
feat(topology/metric_space): dimH is the supr of local dimH ([#9741](https://github.com/leanprover-community/mathlib/pull/9741))
#### Estimated changes
modified src/topology/metric_space/hausdorff_dimension.lean
- \+ *lemma* exists_mem_nhds_within_lt_dimH_of_lt_dimH
- \+ *lemma* bsupr_limsup_dimH
- \+ *lemma* supr_limsup_dimH



## [2021-10-18 12:53:47](https://github.com/leanprover-community/mathlib/commit/06179ca)
feat(data/real/pointwise): Inf and Sup of `a • s` for `s : set ℝ` ([#9707](https://github.com/leanprover-community/mathlib/pull/9707))
This relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.
#### Estimated changes
created src/data/real/pointwise.lean
- \+ *lemma* real.Inf_smul_of_nonneg
- \+ *lemma* real.Sup_smul_of_nonneg
- \+ *lemma* real.Inf_smul_of_nonpos
- \+ *lemma* real.Sup_smul_of_nonpos



## [2021-10-18 11:21:22](https://github.com/leanprover-community/mathlib/commit/e841325)
feat(linear_algebra/dfinsupp): cardinality lemmas for `complete_lattice.independent` ([#9705](https://github.com/leanprover-community/mathlib/pull/9705))
If `p` is a system of independent subspaces of a vector space `V`, and `v` is a system of nonzero vectors each contained in the corresponding subspace, then `v` is linearly independent.
Consequently, if `p` is a system of independent subspaces of `V`, then no more than `dim V` many can be nontrivial.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+/\- *def* to_span_singleton
- \+/\- *def* to_span_singleton

modified src/linear_algebra/dfinsupp.lean
- \+/\- *lemma* independent_iff_forall_dfinsupp
- \+/\- *lemma* independent_of_dfinsupp_lsum_injective
- \+ *lemma* lsum_comp_map_range_to_span_singleton
- \+/\- *lemma* independent.dfinsupp_lsum_injective
- \+/\- *lemma* independent_iff_dfinsupp_lsum_injective
- \+ *lemma* independent.linear_independent
- \+/\- *lemma* independent_iff_forall_dfinsupp
- \+/\- *lemma* independent_of_dfinsupp_lsum_injective
- \+/\- *lemma* independent.dfinsupp_lsum_injective
- \+/\- *lemma* independent_iff_dfinsupp_lsum_injective

modified src/linear_algebra/dimension.lean
- \+ *lemma* cardinal_lift_le_dim_of_linear_independent'
- \+ *lemma* complete_lattice.independent.subtype_ne_bot_le_rank

modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* _root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux
- \+ *lemma* _root_.complete_lattice.independent.subtype_ne_bot_le_finrank



## [2021-10-18 09:32:36](https://github.com/leanprover-community/mathlib/commit/39db98c)
feat(analysis/normed_space/add_torsor_bases): the convex hull has non-empty interior iff the affine span is top ([#9727](https://github.com/leanprover-community/mathlib/pull/9727))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+ *lemma* affine_subspace.convex

modified src/analysis/convex/hull.lean
- \+/\- *lemma* convex_hull_mono
- \+ *lemma* convex_hull_subset_affine_span
- \+ *lemma* affine_span_convex_hull
- \+/\- *lemma* convex_hull_mono

modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* interior_convex_hull_nonempty_iff_aff_span_eq_top

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_map.line_map_mem
- \+ *lemma* _root_.affine_span_le

modified src/topology/basic.lean
- \+/\- *lemma* interior_mono
- \+/\- *lemma* interior_mono



## [2021-10-18 08:20:00](https://github.com/leanprover-community/mathlib/commit/2e62b33)
chore(field_theory/galois): speedup a slow convert ([#9782](https://github.com/leanprover-community/mathlib/pull/9782))
This was broken by a deterministic timeout in another branch. This replaces a `convert` with an explicit `simp`.
#### Estimated changes
modified src/field_theory/galois.lean



## [2021-10-18 08:19:59](https://github.com/leanprover-community/mathlib/commit/27d28a8)
feat(linear_algebra/affine_space/independent): affine equivalences preserve affine independence of sets of points ([#9776](https://github.com/leanprover-community/mathlib/pull/9776))
The key addition is `affine_equiv.affine_independent_set_of_eq_iff`.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_equiv
- \+ *lemma* affine_equiv.affine_independent_set_of_eq_iff
- \- *lemma* affine_map.homothety_affine_independent_iff



## [2021-10-18 08:19:58](https://github.com/leanprover-community/mathlib/commit/fb5c0be)
feat(topology/metric_space): closed if spaced out ([#9754](https://github.com/leanprover-community/mathlib/pull/9754))
If pairwise distances between the points of a set are bounded from below by a positive number, then the set is closed.
Also prove some theorems about `uniform_inducing` and `uniform_embedding` and show that `coe : int → real` is a closed embedding.
#### Estimated changes
modified src/number_theory/liouville/residual.lean

modified src/topology/instances/real.lean
- \+ *lemma* dist_cast
- \+ *lemma* pairwise_one_le_dist
- \+ *lemma* uniform_embedding_coe_rat
- \+ *lemma* closed_embedding_coe_rat
- \+/\- *lemma* uniform_embedding_coe_real
- \+ *lemma* closed_embedding_coe_real
- \- *lemma* rat.dist_cast
- \+/\- *lemma* uniform_embedding_coe_real
- \+ *theorem* dist_eq
- \+ *theorem* uniform_continuous_coe_real
- \+ *theorem* uniform_embedding_coe_real
- \+ *theorem* dense_embedding_coe_real
- \+ *theorem* embedding_coe_real
- \+ *theorem* continuous_coe_real
- \- *theorem* rat.dist_eq
- \- *theorem* uniform_continuous_of_rat
- \- *theorem* uniform_embedding_of_rat
- \- *theorem* dense_embedding_of_rat
- \- *theorem* embedding_of_rat
- \- *theorem* continuous_of_rat

modified src/topology/instances/real_vector_space.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* is_closed_of_pairwise_on_le_dist
- \+ *lemma* closed_embedding_of_pairwise_le_dist
- \+ *lemma* uniform_embedding_bot_of_pairwise_le_dist

modified src/topology/uniform_space/basic.lean
- \+ *lemma* mem_uniformity_of_eq

modified src/topology/uniform_space/compare_reals.lean

modified src/topology/uniform_space/separation.lean
- \+ *lemma* is_closed_range_of_spaced_out

modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing.basis_uniformity
- \+ *lemma* comap_uniformity_of_spaced_out
- \+ *lemma* uniform_embedding_of_spaced_out
- \+ *lemma* closed_embedding_of_spaced_out
- \+ *theorem* uniform_inducing.uniform_embedding



## [2021-10-18 05:53:11](https://github.com/leanprover-community/mathlib/commit/6cd6ff4)
split(data/list/permutation): split off `data.list.basic` ([#9749](https://github.com/leanprover-community/mathlib/pull/9749))
This moves all the `list.permutations` definitions and lemmas not involving `list.perm` to a new file.
#### Estimated changes
modified src/data/list/basic.lean
- \- *lemma* permutations_aux2_snd_eq
- \- *theorem* permutations_aux2_fst
- \- *theorem* permutations_aux2_snd_nil
- \- *theorem* permutations_aux2_snd_cons
- \- *theorem* permutations_aux2_append
- \- *theorem* permutations_aux2_comp_append
- \- *theorem* map_permutations_aux2'
- \- *theorem* map_permutations_aux2
- \- *theorem* map_map_permutations_aux2
- \- *theorem* map_map_permutations'_aux
- \- *theorem* permutations'_aux_eq_permutations_aux2
- \- *theorem* mem_permutations_aux2
- \- *theorem* mem_permutations_aux2'
- \- *theorem* length_permutations_aux2
- \- *theorem* foldr_permutations_aux2
- \- *theorem* mem_foldr_permutations_aux2
- \- *theorem* length_foldr_permutations_aux2
- \- *theorem* length_foldr_permutations_aux2'
- \- *theorem* permutations_aux_nil
- \- *theorem* permutations_aux_cons
- \- *theorem* permutations_nil
- \- *theorem* map_permutations_aux
- \- *theorem* map_permutations
- \- *theorem* map_permutations'
- \- *theorem* permutations_aux_append
- \- *theorem* permutations_append

modified src/data/list/defs.lean

modified src/data/list/perm.lean

created src/data/list/permutation.lean
- \+ *lemma* permutations_aux2_fst
- \+ *lemma* permutations_aux2_snd_nil
- \+ *lemma* permutations_aux2_snd_cons
- \+ *lemma* permutations_aux2_append
- \+ *lemma* permutations_aux2_comp_append
- \+ *lemma* map_permutations_aux2'
- \+ *lemma* map_permutations_aux2
- \+ *lemma* permutations_aux2_snd_eq
- \+ *lemma* map_map_permutations_aux2
- \+ *lemma* map_map_permutations'_aux
- \+ *lemma* permutations'_aux_eq_permutations_aux2
- \+ *lemma* mem_permutations_aux2
- \+ *lemma* mem_permutations_aux2'
- \+ *lemma* length_permutations_aux2
- \+ *lemma* foldr_permutations_aux2
- \+ *lemma* mem_foldr_permutations_aux2
- \+ *lemma* length_foldr_permutations_aux2
- \+ *lemma* length_foldr_permutations_aux2'
- \+ *lemma* permutations_aux_nil
- \+ *lemma* permutations_aux_cons
- \+ *lemma* permutations_nil
- \+ *lemma* map_permutations_aux
- \+ *lemma* map_permutations
- \+ *lemma* map_permutations'
- \+ *lemma* permutations_aux_append
- \+ *lemma* permutations_append



## [2021-10-18 02:28:14](https://github.com/leanprover-community/mathlib/commit/5b527bd)
refactor(linear_algebra/quadratic_form): split file ([#9781](https://github.com/leanprover-community/mathlib/pull/9781))
The section on quadratic forms over complex numbers required pulling in the developing of the complex power function, which significantly increases the import depth. Splitting this file allows `clifford_algebra` to be compiled much earlier.
#### Estimated changes
modified src/linear_algebra/clifford_algebra/basic.lean

renamed src/linear_algebra/quadratic_form.lean to src/linear_algebra/quadratic_form/basic.lean
- \- *theorem* equivalent_sum_squares
- \- *theorem* equivalent_one_neg_one_weighted_sum_squared
- \- *theorem* equivalent_one_zero_neg_one_weighted_sum_squared

created src/linear_algebra/quadratic_form/complex.lean
- \+ *theorem* equivalent_sum_squares

created src/linear_algebra/quadratic_form/real.lean
- \+ *theorem* equivalent_one_neg_one_weighted_sum_squared
- \+ *theorem* equivalent_one_zero_neg_one_weighted_sum_squared



## [2021-10-17 21:55:29](https://github.com/leanprover-community/mathlib/commit/27a777b)
feat(data/nat/gcd): `coprime.lcm_eq_mul` ([#9761](https://github.com/leanprover-community/mathlib/pull/9761))
Surprisingly, this result doesn't seem to be present yet.
#### Estimated changes
modified src/data/nat/gcd.lean
- \+/\- *theorem* coprime.gcd_eq_one
- \+ *theorem* coprime.lcm_eq_mul
- \+/\- *theorem* coprime.gcd_eq_one



## [2021-10-17 20:43:58](https://github.com/leanprover-community/mathlib/commit/5dbe8c4)
feat(topology/metric_space): a map with a contracting iterate has a fixed pt ([#9760](https://github.com/leanprover-community/mathlib/pull/9760))
#### Estimated changes
modified src/topology/metric_space/contracting.lean
- \+ *lemma* is_fixed_pt_fixed_point_iterate



## [2021-10-17 18:13:16](https://github.com/leanprover-community/mathlib/commit/084702d)
chore(analysis/normed_algebra/exponential): golf, generalize ([#9740](https://github.com/leanprover-community/mathlib/pull/9740))
* move `real.summable_pow_div_factorial` to
  `analysis.specific_limits`, golf the proof;
* use recently added lemma `inv_nat_cast_smul_eq` to golf the proof of
  equality of exponentials defined using different fields and
  generalize the statement: we no longer require one field to be a
  normed algebra over another.
* rename `exp_eq_exp_of_field_extension` → `exp_eq_exp` and
  `exp_series_eq_exp_series_of_field_extension` →
  `exp_series_eq_exp_series` because we no longer require
  `[normed_algebra 𝕂 𝕂']`.
#### Estimated changes
modified src/algebra/order/field.lean
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* div_le_div_of_le_left

modified src/analysis/normed_space/exponential.lean
- \+ *lemma* exp_series_eq_exp_series
- \+ *lemma* exp_eq_exp
- \- *lemma* exp_series_eq_exp_series_of_field_extension
- \- *lemma* exp_eq_exp_of_field_extension

modified src/analysis/specific_limits.lean
- \+ *lemma* real.summable_pow_div_factorial
- \+ *lemma* real.tendsto_pow_div_factorial_at_top

modified src/data/nat/cast.lean
- \+/\- *theorem* mono_cast
- \+/\- *theorem* cast_lt
- \+/\- *theorem* mono_cast
- \+/\- *theorem* cast_lt



## [2021-10-17 13:18:35](https://github.com/leanprover-community/mathlib/commit/376bba8)
chore(data/finset/lattice): fix infi docstrings ([#9775](https://github.com/leanprover-community/mathlib/pull/9775))
#### Estimated changes
modified src/data/finset/lattice.lean



## [2021-10-17 13:18:34](https://github.com/leanprover-community/mathlib/commit/41b5645)
chore(topology/algebra/ordered/basic): move code out of `basic` ([#9772](https://github.com/leanprover-community/mathlib/pull/9772))
#### Estimated changes
modified src/data/real/sqrt.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/topology/algebra/group.lean
- \+ *lemma* tendsto_inv_nhds_within_Ioi
- \+ *lemma* tendsto_inv_nhds_within_Iio
- \+ *lemma* tendsto_inv_nhds_within_Ioi_inv
- \+ *lemma* tendsto_inv_nhds_within_Iio_inv
- \+ *lemma* tendsto_inv_nhds_within_Ici
- \+ *lemma* tendsto_inv_nhds_within_Iic
- \+ *lemma* tendsto_inv_nhds_within_Ici_inv
- \+ *lemma* tendsto_inv_nhds_within_Iic_inv

modified src/topology/algebra/ordered/basic.lean
- \- *lemma* is_compact_Icc
- \- *lemma* is_compact_interval
- \- *lemma* is_compact_pi_Icc
- \- *lemma* is_compact.Inf_mem
- \- *lemma* is_compact.Sup_mem
- \- *lemma* is_compact.is_glb_Inf
- \- *lemma* is_compact.is_lub_Sup
- \- *lemma* is_compact.is_least_Inf
- \- *lemma* is_compact.is_greatest_Sup
- \- *lemma* is_compact.exists_is_least
- \- *lemma* is_compact.exists_is_greatest
- \- *lemma* is_compact.exists_is_glb
- \- *lemma* is_compact.exists_is_lub
- \- *lemma* is_compact.exists_Inf_image_eq
- \- *lemma* is_compact.exists_Sup_image_eq
- \- *lemma* eq_Icc_of_connected_compact
- \- *lemma* is_compact.exists_forall_le
- \- *lemma* is_compact.exists_forall_ge
- \- *lemma* continuous.exists_forall_le
- \- *lemma* continuous.exists_forall_ge
- \- *lemma* tendsto_inv_nhds_within_Ioi
- \- *lemma* tendsto_inv_nhds_within_Iio
- \- *lemma* tendsto_inv_nhds_within_Ioi_inv
- \- *lemma* tendsto_inv_nhds_within_Iio_inv
- \- *lemma* tendsto_inv_nhds_within_Ici
- \- *lemma* tendsto_inv_nhds_within_Iic
- \- *lemma* tendsto_inv_nhds_within_Ici_inv
- \- *lemma* tendsto_inv_nhds_within_Iic_inv
- \- *lemma* nhds_left_sup_nhds_right
- \- *lemma* nhds_left'_sup_nhds_right
- \- *lemma* nhds_left_sup_nhds_right'
- \- *lemma* continuous_at_iff_continuous_left_right
- \- *lemma* continuous_within_at_Ioi_iff_Ici
- \- *lemma* continuous_within_at_Iio_iff_Iic
- \- *lemma* continuous_at_iff_continuous_left'_right'
- \- *lemma* strict_mono_on.continuous_at_right_of_exists_between
- \- *lemma* continuous_at_right_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_right_of_monotone_on_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_right_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_right_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_right_of_surj_on
- \- *lemma* strict_mono_on.continuous_at_left_of_exists_between
- \- *lemma* continuous_at_left_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_left_of_monotone_on_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_left_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_left_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_left_of_surj_on
- \- *lemma* strict_mono_on.continuous_at_of_exists_between
- \- *lemma* strict_mono_on.continuous_at_of_closure_image_mem_nhds
- \- *lemma* strict_mono_on.continuous_at_of_image_mem_nhds
- \- *lemma* continuous_at_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_of_monotone_on_of_closure_image_mem_nhds
- \- *lemma* continuous_at_of_monotone_on_of_image_mem_nhds
- \- *lemma* monotone.continuous_of_dense_range
- \- *lemma* monotone.continuous_of_surjective
- \- *lemma* coe_to_homeomorph
- \- *lemma* coe_to_homeomorph_symm
- \- *def* to_homeomorph

created src/topology/algebra/ordered/compact.lean
- \+ *lemma* is_compact_Icc
- \+ *lemma* is_compact_interval
- \+ *lemma* is_compact_pi_Icc
- \+ *lemma* is_compact.Inf_mem
- \+ *lemma* is_compact.Sup_mem
- \+ *lemma* is_compact.is_glb_Inf
- \+ *lemma* is_compact.is_lub_Sup
- \+ *lemma* is_compact.is_least_Inf
- \+ *lemma* is_compact.is_greatest_Sup
- \+ *lemma* is_compact.exists_is_least
- \+ *lemma* is_compact.exists_is_greatest
- \+ *lemma* is_compact.exists_is_glb
- \+ *lemma* is_compact.exists_is_lub
- \+ *lemma* is_compact.exists_Inf_image_eq
- \+ *lemma* is_compact.exists_Sup_image_eq
- \+ *lemma* eq_Icc_of_connected_compact
- \+ *lemma* is_compact.exists_forall_le
- \+ *lemma* is_compact.exists_forall_ge
- \+ *lemma* continuous.exists_forall_le
- \+ *lemma* continuous.exists_forall_ge

created src/topology/algebra/ordered/left_right.lean
- \+ *lemma* continuous_within_at_Ioi_iff_Ici
- \+ *lemma* continuous_within_at_Iio_iff_Iic
- \+ *lemma* nhds_left_sup_nhds_right
- \+ *lemma* nhds_left'_sup_nhds_right
- \+ *lemma* nhds_left_sup_nhds_right'
- \+ *lemma* continuous_at_iff_continuous_left_right
- \+ *lemma* continuous_at_iff_continuous_left'_right'

created src/topology/algebra/ordered/monotone_continuity.lean
- \+ *lemma* strict_mono_on.continuous_at_right_of_exists_between
- \+ *lemma* continuous_at_right_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_monotone_on_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_right_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_right_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_right_of_surj_on
- \+ *lemma* strict_mono_on.continuous_at_left_of_exists_between
- \+ *lemma* continuous_at_left_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_monotone_on_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_left_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_left_of_image_mem_nhds_within
- \+ *lemma* strict_mono_on.continuous_at_left_of_surj_on
- \+ *lemma* strict_mono_on.continuous_at_of_exists_between
- \+ *lemma* strict_mono_on.continuous_at_of_closure_image_mem_nhds
- \+ *lemma* strict_mono_on.continuous_at_of_image_mem_nhds
- \+ *lemma* continuous_at_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_of_monotone_on_of_closure_image_mem_nhds
- \+ *lemma* continuous_at_of_monotone_on_of_image_mem_nhds
- \+ *lemma* monotone.continuous_of_dense_range
- \+ *lemma* monotone.continuous_of_surjective
- \+ *lemma* coe_to_homeomorph
- \+ *lemma* coe_to_homeomorph_symm
- \+ *def* to_homeomorph

modified src/topology/instances/ereal.lean

modified src/topology/metric_space/basic.lean



## [2021-10-17 13:18:32](https://github.com/leanprover-community/mathlib/commit/1432c30)
feat(topology/algebra/mul_action): `λ x, c • x` is a closed map for all `c` ([#9756](https://github.com/leanprover-community/mathlib/pull/9756))
* rename old `is_closed_map_smul₀` to `is_closed_map_smul_of_ne_zero`;
* add a new `is_closed_map_smul₀` that assumes more about typeclasses
  but works for `c = 0`.
#### Estimated changes
modified src/topology/algebra/mul_action.lean
- \+ *lemma* is_closed_map_smul_of_ne_zero
- \+/\- *lemma* is_closed_map_smul₀
- \+/\- *lemma* is_closed_map_smul₀



## [2021-10-17 13:18:31](https://github.com/leanprover-community/mathlib/commit/48dc249)
feat(measure_theory/measure): +1 version of Borel-Cantelli, drop an assumption ([#9678](https://github.com/leanprover-community/mathlib/pull/9678))
* In all versions of Borel-Cantelli lemma, do not require that the
  sets are measurable.
* Add +1 version.
* Golf proofs.
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_limsup_eq_zero
- \+ *lemma* measure_set_of_frequently_eq_zero
- \+/\- *lemma* ae_eventually_not_mem
- \+/\- *lemma* measure_limsup_eq_zero
- \+/\- *lemma* ae_eventually_not_mem



## [2021-10-17 11:01:38](https://github.com/leanprover-community/mathlib/commit/3f15148)
chore(analysis/p_series): use `lift` tactic ([#9773](https://github.com/leanprover-community/mathlib/pull/9773))
#### Estimated changes
modified src/analysis/p_series.lean



## [2021-10-17 11:01:37](https://github.com/leanprover-community/mathlib/commit/9fec8f3)
feat(group_theory/index): `index_comap_of_surjective` ([#9768](https://github.com/leanprover-community/mathlib/pull/9768))
`subgroup.index` is preserved by `subgroup.comap`, provided that the homomorphism is surjective.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* index_comap_of_surjective



## [2021-10-17 11:01:36](https://github.com/leanprover-community/mathlib/commit/85f3640)
feat(topology/instances/ennreal): `{f | lipschitz_with K f}` is a closed set ([#9766](https://github.com/leanprover-community/mathlib/pull/9766))
#### Estimated changes
modified src/topology/instances/ennreal.lean
- \+ *lemma* is_closed_set_of_lipschitz_on_with
- \+ *lemma* is_closed_set_of_lipschitz_with
- \+/\- *theorem* continuous.edist
- \+/\- *theorem* continuous.edist



## [2021-10-17 11:01:35](https://github.com/leanprover-community/mathlib/commit/678d7ed)
chore(data/equiv/mul_add): add missing `to_equiv_mk` ([#9765](https://github.com/leanprover-community/mathlib/pull/9765))
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *lemma* to_equiv_mk



## [2021-10-17 11:01:34](https://github.com/leanprover-community/mathlib/commit/24ebeec)
feat(data/nat/gcd): Add `iff` version of `coprime.dvd_of_dvd_mul` ([#9759](https://github.com/leanprover-community/mathlib/pull/9759))
Adds `iff` versions of `coprime.dvd_of_dvd_mul_right` and `coprime.dvd_of_dvd_mul_left`.
#### Estimated changes
modified src/data/nat/gcd.lean
- \+ *theorem* coprime.dvd_mul_right
- \+ *theorem* coprime.dvd_mul_left



## [2021-10-17 11:01:33](https://github.com/leanprover-community/mathlib/commit/1558a76)
feat(group_theory/subgroup/basic): Special cases of `subgroup_of` ([#9755](https://github.com/leanprover-community/mathlib/pull/9755))
Add four lemmas regarding special cases of `subgroup_of`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* bot_subgroup_of
- \+ *lemma* top_subgroup_of
- \+ *lemma* subgroup_of_bot_eq_bot
- \+ *lemma* subgroup_of_bot_eq_top



## [2021-10-17 11:01:31](https://github.com/leanprover-community/mathlib/commit/4b00aa2)
refactor(ring_theory/jacobson): avoid shadowing hypothesis ([#9736](https://github.com/leanprover-community/mathlib/pull/9736))
This PR postpones a `rw` in a proof, which was creating a shadowed hypothesis. At present, this shadowing was not a big deal, but in another branch it caused a hard-to-diagnose error.
#### Estimated changes
modified src/ring_theory/jacobson.lean



## [2021-10-17 11:01:30](https://github.com/leanprover-community/mathlib/commit/5eb47c0)
feat(topology/homotopy): Define the fundamental groupoid of a topological space ([#9683](https://github.com/leanprover-community/mathlib/pull/9683))
#### Estimated changes
modified src/topology/homotopy/basic.lean
- \+ *def* cast
- \+ *def* cast
- \+ *def* cast

created src/topology/homotopy/fundamental_groupoid.lean
- \+ *lemma* continuous_refl_trans_symm_aux
- \+ *lemma* refl_trans_symm_aux_mem_I
- \+ *lemma* continuous_trans_refl_reparam_aux
- \+ *lemma* trans_refl_reparam_aux_mem_I
- \+ *lemma* trans_refl_reparam_aux_zero
- \+ *lemma* trans_refl_reparam_aux_one
- \+ *lemma* trans_refl_reparam
- \+ *lemma* continuous_trans_assoc_reparam_aux
- \+ *lemma* trans_assoc_reparam_aux_mem_I
- \+ *lemma* trans_assoc_reparam_aux_zero
- \+ *lemma* trans_assoc_reparam_aux_one
- \+ *lemma* trans_assoc_reparam
- \+ *def* refl_trans_symm_aux
- \+ *def* refl_trans_symm
- \+ *def* refl_symm_trans
- \+ *def* trans_refl_reparam_aux
- \+ *def* trans_refl
- \+ *def* refl_trans
- \+ *def* trans_assoc_reparam_aux
- \+ *def* trans_assoc
- \+ *def* fundamental_groupoid

modified src/topology/homotopy/path.lean
- \+ *def* cast
- \+ *def* reparam
- \+ *def* symm₂

modified src/topology/path_connected.lean
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* trans_symm



## [2021-10-17 08:53:58](https://github.com/leanprover-community/mathlib/commit/f171c61)
feat(linear_algebra/affine_space/independent): add `exists_affine_independent` ([#9747](https://github.com/leanprover-community/mathlib/pull/9747))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/data/equiv/set.lean

modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* exists_affine_independent

modified src/linear_algebra/basic.lean
- \+ *lemma* span_insert_zero

modified src/order/countable_dense_linear_order.lean



## [2021-10-17 06:23:24](https://github.com/leanprover-community/mathlib/commit/ff8a35d)
feat(group_theory/subgroup/basic): Kernel of `subtype` and `inclusion` ([#9763](https://github.com/leanprover-community/mathlib/pull/9763))
`subtype` and `inculusion` are injective, so they have trivial kernel.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* _root_.subgroup.ker_subtype
- \+ *lemma* _root_.subgroup.ker_inclusion



## [2021-10-17 03:34:30](https://github.com/leanprover-community/mathlib/commit/7aa431c)
chore(group_theory/quotient_group): Tag lemmas with `@[to_additive]` ([#9771](https://github.com/leanprover-community/mathlib/pull/9771))
Adds `@[to_additive]` to a couple lemmas.
#### Estimated changes
modified src/group_theory/quotient_group.lean
- \+/\- *lemma* subsingleton_quotient_top
- \+/\- *lemma* subgroup_eq_top_of_subsingleton
- \+/\- *lemma* subsingleton_quotient_top
- \+/\- *lemma* subgroup_eq_top_of_subsingleton



## [2021-10-17 03:34:29](https://github.com/leanprover-community/mathlib/commit/a1a05ad)
chore(measure_theory/*): don't require the codomain to be a normed group ([#9769](https://github.com/leanprover-community/mathlib/pull/9769))
Lemmas like `continuous_on.ae_measurable` are true for any codomain. Also add `continuous.integrable_on_Ioc` and `continuous.integrable_on_interval_oc`.
#### Estimated changes
modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* continuous_on.ae_measurable
- \+ *lemma* continuous.integrable_on_Ioc
- \+ *lemma* continuous.integrable_on_interval_oc
- \+/\- *lemma* continuous_on.ae_measurable

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* continuous.measurable_at_filter
- \+/\- *lemma* continuous_on.measurable_at_filter_nhds_within
- \+/\- *lemma* continuous_on.measurable_at_filter_nhds_within



## [2021-10-17 03:34:28](https://github.com/leanprover-community/mathlib/commit/08a070b)
chore(topology/instances/ennreal): golf a proof ([#9767](https://github.com/leanprover-community/mathlib/pull/9767))
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* filter.eventually_eq.continuous_at
- \+ *lemma* continuous_of_const

modified src/topology/instances/ennreal.lean



## [2021-10-17 02:23:49](https://github.com/leanprover-community/mathlib/commit/4a837fb)
chore(analysis/normed/group): add a few convenience lemmas ([#9770](https://github.com/leanprover-community/mathlib/pull/9770))
Add `lipschitz_on_with.norm_sub_le_of_le`,
`lipschitz_with.norm_sub_le`, and `lipschitz_with.norm_sub_le_of_le`.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+ *lemma* lipschitz_on_with.norm_sub_le_of_le
- \+ *lemma* lipschitz_with.norm_sub_le_of_le



## [2021-10-16 23:11:25](https://github.com/leanprover-community/mathlib/commit/cf72eff)
refactor(group_theory/quotient_group): Fix typo ([#9746](https://github.com/leanprover-community/mathlib/pull/9746))
Fix typo in `quotient_bot`.
#### Estimated changes
modified src/group_theory/quotient_group.lean



## [2021-10-16 21:46:54](https://github.com/leanprover-community/mathlib/commit/ad7000b)
feat(set_theory/cardinal): cardinal.to_nat_congr ([#9726](https://github.com/leanprover-community/mathlib/pull/9726))
If `e : α ≃ β`, then `(cardinal.mk α).to_nat = (cardinal.mk β).to_nat`.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *lemma* to_nat_lift
- \+ *lemma* to_nat_congr



## [2021-10-16 20:32:52](https://github.com/leanprover-community/mathlib/commit/b97bb92)
feat(set_theory/cardinal): lemmas ([#9690](https://github.com/leanprover-community/mathlib/pull/9690))
* swap sides of `cardinal.lift_mk`, rename it to `cardinal.mk_ulift`;
* add `cardinal.out_mk_equiv`.
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/data/mv_polynomial/cardinal.lean

modified src/linear_algebra/dimension.lean

modified src/set_theory/cardinal.lean
- \+ *theorem* mk_ulift
- \+/\- *theorem* mk_plift_of_false
- \- *theorem* lift_mk
- \+/\- *theorem* mk_plift_of_false

modified src/set_theory/cardinal_ordinal.lean



## [2021-10-16 18:01:16](https://github.com/leanprover-community/mathlib/commit/3fe67d6)
feat(analysis/special_functions/integrals): integral of `|x - a| ^ n` over `Ι a b` ([#9752](https://github.com/leanprover-community/mathlib/pull/9752))
Also use notation for `interval a b` and `interval_oc a b`.
#### Estimated changes
modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* interval_integrable_one_div
- \+/\- *lemma* interval_integrable_inv
- \+/\- *lemma* interval_integrable_log
- \+ *lemma* integral_pow_abs_sub_interval_oc
- \+/\- *lemma* integral_inv
- \+/\- *lemma* integral_one_div
- \+/\- *lemma* integral_log
- \+/\- *lemma* interval_integrable_one_div
- \+/\- *lemma* interval_integrable_inv
- \+/\- *lemma* interval_integrable_log
- \+/\- *lemma* integral_inv
- \+/\- *lemma* integral_one_div
- \+/\- *lemma* integral_log



## [2021-10-16 18:01:15](https://github.com/leanprover-community/mathlib/commit/54e9e12)
chore(topology/maps): add `is_closed_map.closed_range` ([#9751](https://github.com/leanprover-community/mathlib/pull/9751))
#### Estimated changes
modified src/topology/maps.lean
- \+ *lemma* closed_range



## [2021-10-16 18:01:14](https://github.com/leanprover-community/mathlib/commit/998ab78)
chore(data/list/lex): make data.list.lex not depend on data.list.basic ([#9750](https://github.com/leanprover-community/mathlib/pull/9750))
Another simplification in list related dependencies, if this commit breaks external code the fix is to add `import data.list.basic` to the broken file.
#### Estimated changes
modified src/data/list/lex.lean



## [2021-10-16 18:01:13](https://github.com/leanprover-community/mathlib/commit/066a168)
feat(topology/G_delta): add lemmas, minor golf ([#9742](https://github.com/leanprover-community/mathlib/pull/9742))
* the complement to a countable set is a Gδ set;
* a closed set is a Gδ set;
* finite union of Gδ sets is a Gδ set;
* generalize some universe levels in `topology.basic`;
* golf a few proofs in `topology.uniform_space.basic`;
* add `filter.has_basis.bInter_bUnion_ball`.
#### Estimated changes
modified src/topology/G_delta.lean
- \+/\- *lemma* is_Gδ_empty
- \+/\- *lemma* is_Gδ_univ
- \+/\- *lemma* is_Gδ_Inter
- \+/\- *lemma* is_Gδ_sInter
- \+ *lemma* is_Gδ_bUnion
- \+ *lemma* is_closed.is_Gδ'
- \+ *lemma* is_closed.is_Gδ
- \+ *lemma* is_Gδ_compl_singleton
- \+ *lemma* set.countable.is_Gδ_compl
- \+ *lemma* set.finite.is_Gδ_compl
- \+ *lemma* set.subsingleton.is_Gδ_compl
- \+ *lemma* finset.is_Gδ_compl
- \+/\- *lemma* is_Gδ_set_of_continuous_at
- \+/\- *lemma* is_Gδ_empty
- \+/\- *lemma* is_Gδ_univ
- \+/\- *lemma* is_Gδ_sInter
- \+/\- *lemma* is_Gδ_Inter
- \+/\- *lemma* is_Gδ_set_of_continuous_at

modified src/topology/basic.lean
- \+/\- *theorem* mem_closure_iff_nhds_basis'
- \+/\- *theorem* mem_closure_iff_nhds_basis
- \+/\- *theorem* mem_closure_iff_nhds_basis'
- \+/\- *theorem* mem_closure_iff_nhds_basis

modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* nhds_basis_uniformity
- \+ *lemma* filter.has_basis.bInter_bUnion_ball
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* nhds_basis_uniformity



## [2021-10-16 18:01:11](https://github.com/leanprover-community/mathlib/commit/aa0d0d4)
feat(group_theory/subgroup/basic): Range of inclusion ([#9732](https://github.com/leanprover-community/mathlib/pull/9732))
If `H ≤ K`, then the range of `inclusion : H → K` is `H` (viewed as a subgroup of `K`).
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* _root_.subgroup.inclusion_range



## [2021-10-16 18:01:10](https://github.com/leanprover-community/mathlib/commit/155f8e6)
feat(data/int/succ_pred): `ℤ` is succ- and pred- archimedean ([#9731](https://github.com/leanprover-community/mathlib/pull/9731))
This provides the instances `succ_order ℤ`, `pred_order ℤ`, `is_succ_archimedean ℤ`, `is_pred_archimedean ℤ`.
#### Estimated changes
created src/data/int/succ_pred.lean
- \+ *lemma* int.succ_iterate
- \+ *lemma* int.pred_iterate

modified src/order/succ_pred.lean
- \+ *def* of_succ_le_iff_of_le_lt_succ
- \+ *def* of_succ_le_iff
- \+ *def* of_le_pred_iff_of_pred_le_pred
- \+ *def* of_le_pred_iff
- \- *def* succ_order_of_succ_le_iff_of_le_lt_succ
- \- *def* succ_order_of_succ_le_iff
- \- *def* pred_order_of_le_pred_iff_of_pred_le_pred
- \- *def* pred_order_of_le_pred_iff



## [2021-10-16 18:01:09](https://github.com/leanprover-community/mathlib/commit/e744033)
feat(data/finset/basic, lattice): Simple lemmas ([#9723](https://github.com/leanprover-community/mathlib/pull/9723))
This proves lemmas about `finset.sup`/`finset.inf` and `finset.singleton`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* singleton_injective
- \+ *lemma* nonempty.cons_induction
- \+ *lemma* not_disjoint_iff

modified src/data/finset/lattice.lean
- \+/\- *lemma* sup_image
- \+ *lemma* sup_sup
- \+ *lemma* sup_attach
- \+ *lemma* sup_erase_bot
- \+ *lemma* sup_sdiff_right
- \+/\- *lemma* inf_image
- \+ *lemma* inf_inf
- \+ *lemma* inf_attach
- \+ *lemma* inf_erase_top
- \+ *lemma* sup_sdiff_left
- \+ *lemma* inf_sdiff_left
- \+ *lemma* inf_sdiff_right
- \+ *lemma* sup_singleton'
- \+/\- *lemma* sup_image
- \+/\- *lemma* inf_image

modified src/order/lattice.lean
- \+ *lemma* sup_sup_sup_comm
- \+ *lemma* inf_inf_inf_comm



## [2021-10-16 18:01:08](https://github.com/leanprover-community/mathlib/commit/bf34d9b)
feat(analysis/normed/group/SemiNormedGroup/kernels): add explicit_cokernel.map ([#9712](https://github.com/leanprover-community/mathlib/pull/9712))
From LTE.
#### Estimated changes
modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *lemma* explicit_coker.map_desc



## [2021-10-16 18:01:07](https://github.com/leanprover-community/mathlib/commit/686b363)
feat(analysis/normed/group/SemiNormedGroup/kernels): add kernels ([#9711](https://github.com/leanprover-community/mathlib/pull/9711))
From LTE.
#### Estimated changes
modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *def* parallel_pair_cone



## [2021-10-16 18:01:06](https://github.com/leanprover-community/mathlib/commit/3d99926)
feat(analysis/normed/group/SemiNormedGroup): add iso_isometry_of_norm_noninc ([#9710](https://github.com/leanprover-community/mathlib/pull/9710))
From LTE.
#### Estimated changes
modified src/analysis/normed/group/SemiNormedGroup.lean
- \+ *lemma* iso_isometry_of_norm_noninc



## [2021-10-16 18:01:05](https://github.com/leanprover-community/mathlib/commit/5ac586a)
feat(algebra/group_power/order): When a power is less than one ([#9700](https://github.com/leanprover-community/mathlib/pull/9700))
This proves a bunch of simple order lemmas relating `1`, `a` and `a ^ n`. I also move `pow_le_one` upstream as it could already be proved in `algebra.group_power.order` and remove `[nontrivial R]` from `one_lt_pow`.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* pow_le_pow_of_le_one
- \+ *lemma* pow_le_of_le_one
- \+ *lemma* sq_le
- \+/\- *lemma* pow_le_pow_of_le_one
- \- *lemma* pow_le_one

modified src/algebra/group_power/order.lean
- \+ *lemma* pow_lt_one
- \+/\- *lemma* one_lt_pow
- \+ *lemma* pow_le_one
- \+ *lemma* pow_le_one_iff_of_nonneg
- \+ *lemma* one_le_pow_iff_of_nonneg
- \+ *lemma* one_lt_pow_iff_of_nonneg
- \+ *lemma* pow_lt_one_iff_of_nonneg
- \+ *lemma* sq_le_one_iff
- \+ *lemma* sq_lt_one_iff
- \+ *lemma* one_le_sq_iff
- \+ *lemma* one_lt_sq_iff
- \+/\- *lemma* one_lt_pow



## [2021-10-16 16:46:55](https://github.com/leanprover-community/mathlib/commit/99b2d40)
feat(algebra/floor): Floor and ceil of `-a` ([#9715](https://github.com/leanprover-community/mathlib/pull/9715))
This proves `floor_neg : ⌊-a⌋ = -⌈a⌉` and `ceil_neg : ⌈-a⌉ = -⌊a⌋` and uses them to remove explicit dependency on the definition of `int.ceil` in prevision of [#9591](https://github.com/leanprover-community/mathlib/pull/9591). This also proves `⌊a + 1⌋ = ⌊a⌋ + 1` and variants.
#### Estimated changes
modified src/algebra/archimedean.lean

modified src/algebra/floor.lean
- \+ *lemma* floor_add_one
- \+ *lemma* floor_neg
- \+ *lemma* ceil_neg
- \+ *lemma* ceil_add_one
- \+ *lemma* floor_add_one
- \+ *lemma* ceil_add_one
- \+ *lemma* ceil_lt_add_one
- \- *theorem* ceil_lt_add_one



## [2021-10-16 09:26:55](https://github.com/leanprover-community/mathlib/commit/9ac2aa2)
feat(topology/metric_space/lipschitz): add `lipschitz_with.min` and `lipschitz_with.max` ([#9744](https://github.com/leanprover-community/mathlib/pull/9744))
Also change assumptions in some lemmas in `algebra.order.group` from
 `[add_comm_group α] [linear_order α] [covariant_class α α (+) (≤)]`
to `[linear_ordered_add_comm_group α]`. These two sets of assumptions
are equivalent but the latter is more readable.
#### Estimated changes
modified src/algebra/order/group.lean
- \+ *lemma* max_sub_max_le_max
- \+ *lemma* abs_max_sub_max_le_max
- \+ *lemma* abs_min_sub_min_le_max
- \+/\- *lemma* abs_max_sub_max_le_abs
- \+/\- *lemma* abs_max_sub_max_le_abs

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* subtype_mk
- \+ *lemma* _root_.lipschitz_with_max
- \+ *lemma* _root_.lipschitz_with_min
- \+ *lemma* max_const
- \+ *lemma* const_max
- \+ *lemma* min_const
- \+ *lemma* const_min



## [2021-10-16 09:26:54](https://github.com/leanprover-community/mathlib/commit/96ba8b6)
chore(topology/uniform_space/pi): add `uniform_continuous_pi` ([#9743](https://github.com/leanprover-community/mathlib/pull/9743))
#### Estimated changes
modified src/topology/uniform_space/pi.lean
- \+ *lemma* uniform_continuous_pi



## [2021-10-16 08:44:20](https://github.com/leanprover-community/mathlib/commit/e362293)
refactor(ring_theory/fractional_ideal): speedup a proof ([#9738](https://github.com/leanprover-community/mathlib/pull/9738))
This was timing out on another branch. Just replaces a `simp only []` with a `rw []`.
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean



## [2021-10-16 07:32:33](https://github.com/leanprover-community/mathlib/commit/f40cd88)
chore(topology/algebra/ordered): move some lemmas to a new file ([#9745](https://github.com/leanprover-community/mathlib/pull/9745))
#### Estimated changes
modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered/basic.lean
- \- *lemma* tendsto_at_top_is_lub
- \- *lemma* tendsto_at_bot_is_lub
- \- *lemma* tendsto_at_bot_is_glb
- \- *lemma* tendsto_at_top_is_glb
- \- *lemma* tendsto_at_top_csupr
- \- *lemma* tendsto_at_bot_csupr
- \- *lemma* tendsto_at_bot_cinfi
- \- *lemma* tendsto_at_top_cinfi
- \- *lemma* tendsto_at_top_supr
- \- *lemma* tendsto_at_bot_supr
- \- *lemma* tendsto_at_bot_infi
- \- *lemma* tendsto_at_top_infi
- \- *lemma* tendsto_of_monotone
- \- *lemma* tendsto_iff_tendsto_subseq_of_monotone
- \- *lemma* monotone.ge_of_tendsto
- \- *lemma* monotone.le_of_tendsto
- \- *lemma* is_lub_of_tendsto
- \- *lemma* is_glb_of_tendsto
- \- *lemma* supr_eq_of_tendsto
- \- *lemma* infi_eq_of_tendsto
- \- *lemma* supr_eq_supr_subseq_of_monotone
- \- *lemma* infi_eq_infi_subseq_of_monotone

created src/topology/algebra/ordered/monotone_convergence.lean
- \+ *lemma* tendsto_at_top_is_lub
- \+ *lemma* tendsto_at_bot_is_lub
- \+ *lemma* tendsto_at_bot_is_glb
- \+ *lemma* tendsto_at_top_is_glb
- \+ *lemma* tendsto_at_top_csupr
- \+ *lemma* tendsto_at_bot_csupr
- \+ *lemma* tendsto_at_bot_cinfi
- \+ *lemma* tendsto_at_top_cinfi
- \+ *lemma* tendsto_at_top_supr
- \+ *lemma* tendsto_at_bot_supr
- \+ *lemma* tendsto_at_bot_infi
- \+ *lemma* tendsto_at_top_infi
- \+ *lemma* tendsto_of_monotone
- \+ *lemma* tendsto_iff_tendsto_subseq_of_monotone
- \+ *lemma* monotone.ge_of_tendsto
- \+ *lemma* monotone.le_of_tendsto
- \+ *lemma* is_lub_of_tendsto
- \+ *lemma* is_glb_of_tendsto
- \+ *lemma* supr_eq_of_tendsto
- \+ *lemma* infi_eq_of_tendsto
- \+ *lemma* supr_eq_supr_subseq_of_monotone
- \+ *lemma* infi_eq_infi_subseq_of_monotone



## [2021-10-16 04:16:34](https://github.com/leanprover-community/mathlib/commit/150bbea)
feat(group_theory/subgroup/basic): Bottom subgroup has unique element ([#9734](https://github.com/leanprover-community/mathlib/pull/9734))
Adds instance for `unique (⊥ : subgroup G)`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean



## [2021-10-16 01:17:29](https://github.com/leanprover-community/mathlib/commit/1766588)
feat(measure_theory/covering/vitali): Vitali covering theorems ([#9680](https://github.com/leanprover-community/mathlib/pull/9680))
The topological and measurable Vitali covering theorems.
* topological version: if a space is covered by balls `(B (x_i, r_i))_{i \in I}`, one can extract a disjointed subfamily indexed by `J` such that the space is covered by the balls `B (x_j, 5 r_j)`.
* measurable version: if additionally the measure has a doubling-like property, and the covering contains balls of arbitrarily small radius at every point, then the disjointed subfamily one obtains above covers almost all the space.
These two statements are particular cases of more general statements that are proved in this PR.
#### Estimated changes
created src/measure_theory/covering/vitali.lean
- \+ *theorem* exists_disjoint_subfamily_covering_enlargment
- \+ *theorem* exists_disjoint_subfamily_covering_enlargment_closed_ball
- \+ *theorem* exists_disjoint_covering_ae



## [2021-10-15 22:57:51](https://github.com/leanprover-community/mathlib/commit/ea22ce3)
chore(data/list): move lemmas from data.list.basic that require algebra.group_power to a new file ([#9728](https://github.com/leanprover-community/mathlib/pull/9728))
Hopefully ease the dependencies on anyone importing data.list.basic, if your code broke after this change adding `import data.list.prod_monoid` should fix it.
Lemmas moved:
- `list.prod_repeat`
- `list.sum_repeat`
- `list.prod_le_of_forall_le`
- `list.sum_le_of_forall_le`
#### Estimated changes
modified src/data/list/basic.lean
- \- *lemma* prod_le_of_forall_le
- \- *theorem* prod_repeat

created src/data/list/prod_monoid.lean
- \+ *lemma* prod_le_of_forall_le
- \+ *theorem* prod_repeat

modified src/data/multiset/basic.lean

modified test/lint_unused_haves_suffices.lean



## [2021-10-15 21:35:25](https://github.com/leanprover-community/mathlib/commit/711aa75)
refactor(algebra/gcd_monoid): remove superfluous old_structure_cmd ([#9720](https://github.com/leanprover-community/mathlib/pull/9720))
#### Estimated changes
modified src/algebra/gcd_monoid/basic.lean



## [2021-10-15 16:38:20](https://github.com/leanprover-community/mathlib/commit/b3f602b)
feat(linear_algebra/linear_independent): add variant of `exists_linear_independent` ([#9708](https://github.com/leanprover-community/mathlib/pull/9708))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/dimension.lean

modified src/linear_algebra/linear_independent.lean
- \+ *lemma* exists_linear_independent_extension
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_linear_independent



## [2021-10-15 15:08:13](https://github.com/leanprover-community/mathlib/commit/d6fd5f5)
feat(linear_algebra/dimension): generalize dim_zero_iff_forall_zero ([#9713](https://github.com/leanprover-community/mathlib/pull/9713))
We generalize `dim_zero_iff_forall_zero` to `[nontrivial R] [no_zero_smul_divisors R M]`.
If you see a more general class to consider let me know.
#### Estimated changes
modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_zero_iff_forall_zero
- \+/\- *lemma* dim_zero_iff
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+/\- *lemma* dim_pos_iff_nontrivial
- \+/\- *lemma* dim_pos
- \+/\- *lemma* dim_zero_iff_forall_zero
- \+/\- *lemma* dim_zero_iff
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+/\- *lemma* dim_pos_iff_nontrivial
- \+/\- *lemma* dim_pos

modified src/linear_algebra/finite_dimensional.lean



## [2021-10-15 12:10:59](https://github.com/leanprover-community/mathlib/commit/ad6d476)
refactor(ring_theory/derivation): remove old_structure_cmd ([#9724](https://github.com/leanprover-community/mathlib/pull/9724))
#### Estimated changes
modified src/geometry/manifold/derivation_bundle.lean

modified src/ring_theory/derivation.lean
- \+/\- *lemma* mk_coe
- \- *lemma* to_fun_eq_coe
- \+/\- *lemma* mk_coe



## [2021-10-15 12:10:58](https://github.com/leanprover-community/mathlib/commit/a2737b4)
chore(data/set_like/basic): remove superfluous old_structure_cmd ([#9722](https://github.com/leanprover-community/mathlib/pull/9722))
#### Estimated changes
modified src/data/set_like/basic.lean



## [2021-10-15 11:28:36](https://github.com/leanprover-community/mathlib/commit/6bc2a1a)
refactor(algebra/lie/basic): remove old_structure_cmd ([#9721](https://github.com/leanprover-community/mathlib/pull/9721))
#### Estimated changes
modified src/algebra/lie/abelian.lean

modified src/algebra/lie/basic.lean
- \+/\- *lemma* mk_coe
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_linear_mk
- \+ *lemma* injective
- \+/\- *lemma* coe_mk
- \+/\- *lemma* symm_symm
- \+/\- *lemma* mk_coe
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_linear_mk
- \+/\- *lemma* coe_mk
- \+/\- *lemma* symm_symm
- \+ *def* to_linear_equiv
- \+ *def* to_equiv

modified src/algebra/lie/tensor_product.lean

modified src/algebra/lie/weights.lean
- \+ *def* root_space_weight_space_product_aux
- \+/\- *def* root_space_weight_space_product
- \+/\- *def* root_space_weight_space_product



## [2021-10-15 06:28:08](https://github.com/leanprover-community/mathlib/commit/7707036)
feat(tactic/by_contra): add by_contra' tactic ([#9619](https://github.com/leanprover-community/mathlib/pull/9619))
#### Estimated changes
created src/tactic/by_contra.lean

modified src/tactic/core.lean

modified src/tactic/norm_num.lean

created test/by_contra.lean



## [2021-10-15 01:06:58](https://github.com/leanprover-community/mathlib/commit/be91f69)
chore(algebra/floor): general golf ([#9716](https://github.com/leanprover-community/mathlib/pull/9716))
This cleans the file in depth:
* kill some `simp`
* use available dot notation on `≤`
* remove the `by ... ; ...` (there's one left that [#9715](https://github.com/leanprover-community/mathlib/pull/9715)) takes care of
* group definition and notation of `int.floor`,`int.ceil` and `int.fract`
* move `int.preimage_...` lemmas with the rest of the `ℤ` stuff
* homogeneize variable names
#### Estimated changes
modified src/algebra/floor.lean
- \+ *lemma* le_floor
- \+ *lemma* floor_lt
- \+ *lemma* floor_le
- \+ *lemma* floor_nonneg
- \+ *lemma* lt_succ_floor
- \+ *lemma* lt_floor_add_one
- \+/\- *lemma* sub_one_lt_floor
- \+ *lemma* floor_coe
- \+ *lemma* floor_zero
- \+ *lemma* floor_one
- \+ *lemma* floor_mono
- \+ *lemma* floor_add_int
- \+ *lemma* floor_int_add
- \+ *lemma* floor_add_nat
- \+ *lemma* floor_nat_add
- \+ *lemma* floor_sub_int
- \+ *lemma* floor_sub_nat
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+/\- *lemma* floor_eq_iff
- \+/\- *lemma* floor_eq_on_Ico
- \+/\- *lemma* floor_eq_on_Ico'
- \+/\- *lemma* floor_add_fract
- \+/\- *lemma* fract_add_floor
- \+ *lemma* fract_nonneg
- \+ *lemma* fract_lt_one
- \+/\- *lemma* fract_zero
- \+/\- *lemma* fract_floor
- \+/\- *lemma* floor_fract
- \+ *lemma* fract_eq_iff
- \+ *lemma* fract_eq_fract
- \+/\- *lemma* fract_fract
- \+ *lemma* fract_add
- \+ *lemma* fract_mul_nat
- \+ *lemma* ceil_le
- \+ *lemma* lt_ceil
- \+ *lemma* ceil_le_floor_add_one
- \+ *lemma* le_ceil
- \+ *lemma* ceil_coe
- \+ *lemma* ceil_mono
- \+ *lemma* ceil_add_int
- \+ *lemma* ceil_sub_int
- \+ *lemma* ceil_lt_add_one
- \+/\- *lemma* ceil_pos
- \+ *lemma* ceil_zero
- \+/\- *lemma* ceil_nonneg
- \+/\- *lemma* ceil_eq_iff
- \+/\- *lemma* ceil_eq_on_Ioc
- \+/\- *lemma* ceil_eq_on_Ioc'
- \+/\- *lemma* floor_lt_ceil_of_lt
- \+/\- *lemma* preimage_Ioo
- \+/\- *lemma* preimage_Ico
- \+/\- *lemma* preimage_Ioc
- \+/\- *lemma* preimage_Icc
- \+/\- *lemma* preimage_Ioi
- \+/\- *lemma* preimage_Ici
- \+/\- *lemma* preimage_Iio
- \+/\- *lemma* preimage_Iic
- \+ *lemma* le_floor_iff
- \+ *lemma* floor_lt_iff
- \+ *lemma* floor_mono
- \+ *lemma* floor_coe
- \+ *lemma* floor_zero
- \+ *lemma* floor_add_nat
- \+/\- *lemma* sub_one_lt_floor
- \+ *lemma* ceil_le
- \+ *lemma* lt_ceil
- \+ *lemma* le_ceil
- \+ *lemma* ceil_mono
- \+ *lemma* ceil_coe
- \+ *lemma* ceil_zero
- \+ *lemma* ceil_eq_zero
- \+ *lemma* ceil_add_nat
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+/\- *lemma* floor_lt_ceil_of_lt_of_pos
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+/\- *lemma* floor_eq_iff
- \+/\- *lemma* floor_eq_on_Ico
- \+/\- *lemma* floor_eq_on_Ico'
- \+/\- *lemma* floor_add_fract
- \+/\- *lemma* fract_add_floor
- \+/\- *lemma* fract_zero
- \+/\- *lemma* fract_floor
- \+/\- *lemma* floor_fract
- \+/\- *lemma* fract_fract
- \+/\- *lemma* ceil_pos
- \+/\- *lemma* ceil_nonneg
- \+/\- *lemma* ceil_eq_iff
- \+/\- *lemma* ceil_eq_on_Ioc
- \+/\- *lemma* ceil_eq_on_Ioc'
- \+/\- *lemma* floor_lt_ceil_of_lt
- \+/\- *lemma* sub_one_lt_floor
- \+/\- *lemma* lt_of_ceil_lt
- \+/\- *lemma* le_of_ceil_le
- \+/\- *lemma* floor_lt_ceil_of_lt_of_pos
- \+/\- *lemma* preimage_Ioo
- \+/\- *lemma* preimage_Ico
- \+/\- *lemma* preimage_Ioc
- \+/\- *lemma* preimage_Icc
- \+/\- *lemma* preimage_Ioi
- \+/\- *lemma* preimage_Ici
- \+/\- *lemma* preimage_Iio
- \+/\- *lemma* preimage_Iic
- \- *theorem* le_floor
- \- *theorem* floor_lt
- \- *theorem* floor_le
- \- *theorem* floor_nonneg
- \- *theorem* lt_succ_floor
- \- *theorem* lt_floor_add_one
- \- *theorem* sub_one_lt_floor
- \- *theorem* floor_coe
- \- *theorem* floor_zero
- \- *theorem* floor_one
- \- *theorem* floor_mono
- \- *theorem* floor_add_int
- \- *theorem* floor_int_add
- \- *theorem* floor_add_nat
- \- *theorem* floor_add
- \- *theorem* floor_sub_int
- \- *theorem* floor_sub_nat
- \- *theorem* fract_nonneg
- \- *theorem* fract_lt_one
- \- *theorem* fract_eq_iff
- \- *theorem* fract_eq_fract
- \- *theorem* fract_add
- \- *theorem* fract_mul_nat
- \- *theorem* ceil_le
- \- *theorem* lt_ceil
- \- *theorem* ceil_le_floor_add_one
- \- *theorem* le_ceil
- \- *theorem* ceil_coe
- \- *theorem* ceil_mono
- \- *theorem* ceil_add_int
- \- *theorem* ceil_sub_int
- \- *theorem* ceil_lt_add_one
- \- *theorem* ceil_zero
- \- *theorem* le_floor_iff
- \- *theorem* floor_lt_iff
- \- *theorem* floor_mono
- \- *theorem* floor_coe
- \- *theorem* floor_zero
- \- *theorem* floor_add_nat
- \- *theorem* ceil_le
- \- *theorem* lt_ceil
- \- *theorem* le_ceil
- \- *theorem* ceil_mono
- \- *theorem* ceil_coe
- \- *theorem* ceil_zero
- \- *theorem* ceil_eq_zero
- \- *theorem* ceil_add_nat
- \+/\- *def* ceil
- \+/\- *def* fract
- \+/\- *def* ceil
- \+/\- *def* fract
- \+/\- *def* ceil
- \+/\- *def* ceil



## [2021-10-14 23:10:05](https://github.com/leanprover-community/mathlib/commit/c37ea53)
feat(order/succ_pred): `succ`-Archimedean orders ([#9714](https://github.com/leanprover-community/mathlib/pull/9714))
This defines `succ`-Archimedean orders: orders in which `a ≤ b` means that `succ^[n] a = b` for some `n`.
#### Estimated changes
modified src/logic/function/iterate.lean
- \+ *lemma* iterate.rec_zero
- \+ *def* iterate.rec

modified src/order/succ_pred.lean
- \+ *lemma* has_le.le.exists_succ_iterate
- \+ *lemma* exists_succ_iterate_iff_le
- \+ *lemma* succ.rec
- \+ *lemma* succ.rec_iff
- \+ *lemma* has_le.le.exists_pred_iterate
- \+ *lemma* exists_pred_iterate_iff_le
- \+ *lemma* pred.rec
- \+ *lemma* pred.rec_iff
- \+ *lemma* exists_succ_iterate_or
- \+ *lemma* succ.rec_linear
- \+ *lemma* exists_pred_iterate_or
- \+ *lemma* pred.rec_linear
- \+ *lemma* succ.rec_bot
- \+ *lemma* pred.rec_top



## [2021-10-14 21:12:58](https://github.com/leanprover-community/mathlib/commit/c12aced)
feat(algebra/star): star_linear_equiv ([#9426](https://github.com/leanprover-community/mathlib/pull/9426))
#### Estimated changes
modified src/algebra/ring/comp_typeclasses.lean
- \+ *lemma* of_ring_equiv
- \+ *lemma* symm

modified src/algebra/star/basic.lean

created src/algebra/star/module.lean
- \+ *def* star_linear_equiv



## [2021-10-14 19:54:19](https://github.com/leanprover-community/mathlib/commit/158fbc5)
refactor(algebra/module/order): Make space argument explicit in the `order_iso` ([#9706](https://github.com/leanprover-community/mathlib/pull/9706))
Explicitly providing `M` in `order_iso.smul_left` and `order_iso.smul_left_dual` turns out to work much better with dot notation on `order_iso`. This allows golfing half the proofs introduced in [#9078](https://github.com/leanprover-community/mathlib/pull/9078).
#### Estimated changes
modified src/algebra/module/ordered.lean
- \+/\- *lemma* bdd_below.smul_of_nonneg
- \+/\- *lemma* bdd_above.smul_of_nonneg
- \+/\- *lemma* bdd_below.smul_of_nonpos
- \+/\- *lemma* bdd_above.smul_of_nonpos
- \+/\- *lemma* lower_bounds_smul_of_pos
- \+/\- *lemma* upper_bounds_smul_of_pos
- \+/\- *lemma* bdd_below_smul_iff_of_pos
- \+/\- *lemma* bdd_above_smul_iff_of_pos
- \+/\- *lemma* lower_bounds_smul_of_neg
- \+/\- *lemma* upper_bounds_smul_of_neg
- \+/\- *lemma* bdd_below_smul_iff_of_neg
- \+/\- *lemma* bdd_above_smul_iff_of_neg
- \+/\- *lemma* bdd_below.smul_of_nonneg
- \+/\- *lemma* bdd_above.smul_of_nonneg
- \+/\- *lemma* bdd_below.smul_of_nonpos
- \+/\- *lemma* bdd_above.smul_of_nonpos
- \+/\- *lemma* lower_bounds_smul_of_pos
- \+/\- *lemma* upper_bounds_smul_of_pos
- \+/\- *lemma* bdd_below_smul_iff_of_pos
- \+/\- *lemma* bdd_above_smul_iff_of_pos
- \+/\- *lemma* lower_bounds_smul_of_neg
- \+/\- *lemma* upper_bounds_smul_of_neg
- \+/\- *lemma* bdd_below_smul_iff_of_neg
- \+/\- *lemma* bdd_above_smul_iff_of_neg

modified src/algebra/order/smul.lean



## [2021-10-14 18:49:52](https://github.com/leanprover-community/mathlib/commit/72789f5)
feat(linear_algebra/affine_space/affine_subspace): add lemma `affine_equiv.span_eq_top_iff` ([#9695](https://github.com/leanprover-community/mathlib/pull/9695))
Together with supporting lemmas.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/algebra/add_torsor.lean
- \+ *lemma* mem_vsub

modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* image_vsub_image

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_map.vector_span_image_eq_submodule_map
- \+ *lemma* map_coe
- \+ *lemma* map_bot
- \+ *lemma* map_direction
- \+ *lemma* map_span
- \+ *lemma* map_top_of_surjective
- \+ *lemma* span_eq_top_of_surjective
- \+ *lemma* affine_equiv.span_eq_top_iff
- \+ *def* map



## [2021-10-14 18:06:10](https://github.com/leanprover-community/mathlib/commit/cef78dd)
feat(archive/abel_ruffini): speedup by squeezing  ([#9709](https://github.com/leanprover-community/mathlib/pull/9709))
30s->9s elaboration for me, hopefully stop [#9705](https://github.com/leanprover-community/mathlib/pull/9705) timing out
#### Estimated changes
modified archive/100-theorems-list/16_abel_ruffini.lean



## [2021-10-14 16:25:51](https://github.com/leanprover-community/mathlib/commit/393fe70)
chore(analysis/p_series): add 2 more versions ([#9703](https://github.com/leanprover-community/mathlib/pull/9703))
#### Estimated changes
modified docs/undergrad.yaml

modified src/analysis/p_series.lean
- \+ *lemma* real.summable_nat_rpow
- \+ *lemma* nnreal.summable_rpow_inv
- \+ *lemma* nnreal.summable_rpow
- \- *lemma* nnreal.summable_one_rpow_inv



## [2021-10-14 13:24:56](https://github.com/leanprover-community/mathlib/commit/aff49a6)
feat(data/equiv/basic): prop_equiv_pempty ([#9689](https://github.com/leanprover-community/mathlib/pull/9689))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* prop_equiv_pempty



## [2021-10-14 13:24:54](https://github.com/leanprover-community/mathlib/commit/dc23dfa)
feat(data/equiv/basic): subtype_equiv_psigma ([#9688](https://github.com/leanprover-community/mathlib/pull/9688))
- [x] depends on: [#9687](https://github.com/leanprover-community/mathlib/pull/9687)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* psigma_equiv_subtype
- \+ *def* sigma_plift_equiv_subtype
- \+ *def* sigma_ulift_plift_equiv_subtype



## [2021-10-14 13:24:52](https://github.com/leanprover-community/mathlib/commit/9da33a8)
refactor(algebra/floor): Rename floor and ceil functions ([#9590](https://github.com/leanprover-community/mathlib/pull/9590))
This renames
* `floor` -> `int.floor`
* `ceil` -> `int.ceil`
* `fract` -> `int.fract`
* `nat_floor` -> `nat.floor`
* `nat_ceil` -> `nat.ceil`
#### Estimated changes
modified archive/imo/imo2013_q5.lean

modified src/algebra/archimedean.lean

modified src/algebra/continued_fractions/computation/approximations.lean

modified src/algebra/continued_fractions/computation/basic.lean

modified src/algebra/continued_fractions/computation/correctness_terminating.lean

modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean

modified src/algebra/continued_fractions/computation/translations.lean

modified src/algebra/floor.lean
- \+/\- *lemma* floor_ring_unique
- \+ *lemma* floor_of_nonpos
- \+ *lemma* floor_le
- \+ *lemma* le_floor_of_le
- \+ *lemma* floor_pos
- \+ *lemma* pos_of_floor_pos
- \+ *lemma* lt_of_lt_floor
- \+ *lemma* lt_floor_add_one
- \+ *lemma* sub_one_lt_floor
- \+ *lemma* floor_eq_zero_iff
- \+ *lemma* lt_of_ceil_lt
- \+ *lemma* le_of_ceil_le
- \+ *lemma* floor_lt_ceil_of_lt_of_pos
- \+/\- *lemma* floor_ring_unique
- \- *lemma* nat_floor_of_nonpos
- \- *lemma* nat_floor_le
- \- *lemma* le_nat_floor_of_le
- \- *lemma* nat_floor_pos
- \- *lemma* pos_of_nat_floor_pos
- \- *lemma* lt_of_lt_nat_floor
- \- *lemma* lt_nat_floor_add_one
- \- *lemma* sub_one_lt_nat_floor
- \- *lemma* nat_floor_eq_zero_iff
- \- *lemma* lt_of_nat_ceil_lt
- \- *lemma* le_of_nat_ceil_le
- \- *lemma* nat_floor_lt_nat_ceil_of_lt_of_pos
- \+ *theorem* floor_add
- \+ *theorem* le_floor_iff
- \+ *theorem* floor_lt_iff
- \+ *theorem* floor_mono
- \+ *theorem* floor_coe
- \+ *theorem* floor_zero
- \+ *theorem* floor_add_nat
- \+ *theorem* ceil_le
- \+ *theorem* lt_ceil
- \+ *theorem* le_ceil
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_zero
- \+ *theorem* ceil_eq_zero
- \+ *theorem* ceil_add_nat
- \+ *theorem* ceil_lt_add_one
- \- *theorem* floor_nat_add
- \- *theorem* le_nat_floor_iff
- \- *theorem* nat_floor_lt_iff
- \- *theorem* nat_floor_mono
- \- *theorem* nat_floor_coe
- \- *theorem* nat_floor_zero
- \- *theorem* nat_floor_add_nat
- \- *theorem* nat_ceil_le
- \- *theorem* lt_nat_ceil
- \- *theorem* le_nat_ceil
- \- *theorem* nat_ceil_mono
- \- *theorem* nat_ceil_coe
- \- *theorem* nat_ceil_zero
- \- *theorem* nat_ceil_eq_zero
- \- *theorem* nat_ceil_add_nat
- \- *theorem* nat_ceil_lt_add_one
- \+ *def* floor
- \+ *def* ceil
- \- *def* nat_floor
- \- *def* nat_ceil

modified src/analysis/special_functions/exp_log.lean

modified src/analysis/specific_limits.lean

modified src/data/rat/floor.lean

modified src/data/real/basic.lean

modified src/data/real/pi/wallis.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/number_theory/class_number/admissible_abs.lean

modified src/number_theory/class_number/admissible_card_pow_degree.lean

modified src/topology/algebra/floor_ring.lean

modified src/topology/instances/real.lean

modified src/topology/metric_space/gromov_hausdorff.lean



## [2021-10-14 07:51:21](https://github.com/leanprover-community/mathlib/commit/264ff90)
refactor(analysis/special_functions): generalise nth-root lemmas ([#9704](https://github.com/leanprover-community/mathlib/pull/9704))
`exists_pow_nat_eq` and `exists_eq_mul_self` both hold for any algebraically closed field, so pull them out into `is_alg_closed/basic` and generalise appropriately
Closes [#4674](https://github.com/leanprover-community/mathlib/pull/4674)
#### Estimated changes
modified src/analysis/special_functions/complex/log.lean
- \- *lemma* exists_pow_nat_eq
- \- *lemma* exists_eq_mul_self

modified src/analysis/special_functions/trigonometric/complex.lean

modified src/field_theory/is_alg_closed/basic.lean
- \+ *lemma* exists_pow_nat_eq
- \+ *lemma* exists_eq_mul_self



## [2021-10-14 07:51:19](https://github.com/leanprover-community/mathlib/commit/8d67d9a)
chore(category_theory/sites/*): Generalize universes ([#9675](https://github.com/leanprover-community/mathlib/pull/9675))
This generalizes the universe levels for sheaves to some extent.
This will allow us to now consider sheaves on `C : Type u` (satisfying `[category.{v} C]` and endowed with a Grothendieck topology) taking values in an arbitrary category with no additional universe restrictions.
The only part of the theory which has not been generalized is the equivalence of the sheaf condition with the condition involving Yoneda. To generalize this would require composing with `ulift_functors`'s, which we may or may not want to do.
#### Estimated changes
modified src/category_theory/sites/closed.lean
- \+/\- *def* functor.closed_sieves
- \+/\- *def* functor.closed_sieves

modified src/category_theory/sites/sheaf.lean
- \+/\- *lemma* is_sheaf_iff_is_sheaf_of_type
- \+/\- *lemma* is_sheaf_iff_is_sheaf_forget
- \+/\- *lemma* is_sheaf_iff_is_sheaf_of_type
- \+/\- *lemma* is_sheaf_iff_is_sheaf_forget
- \+/\- *def* Sheaf_equiv_SheafOfTypes
- \+/\- *def* is_sheaf_for_is_sheaf_for'
- \+/\- *def* Sheaf_equiv_SheafOfTypes
- \+/\- *def* is_sheaf_for_is_sheaf_for'

modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* family_of_elements.comp_presheaf_map_id
- \+ *lemma* family_of_elements.comp_prersheaf_map_comp
- \+ *lemma* family_of_elements.is_amalgamation.comp_presheaf_map
- \+/\- *lemma* is_separated_for_top
- \+/\- *lemma* extension_iff_amalgamation
- \+/\- *lemma* is_sheaf_for_iff_yoneda_sheaf_condition
- \+/\- *lemma* is_sheaf_for.functor_inclusion_comp_extend
- \+/\- *lemma* is_sheaf_for.unique_extend
- \+/\- *lemma* is_sheaf_for.hom_ext
- \+/\- *lemma* is_sheaf_for_singleton_iso
- \+/\- *lemma* is_sheaf_for_top_sieve
- \+/\- *lemma* is_sheaf_for_iso
- \+/\- *lemma* is_sheaf_for_subsieve_aux
- \+/\- *lemma* is_sheaf_for_subsieve
- \+/\- *lemma* is_sheaf.is_sheaf_for
- \+/\- *lemma* is_sheaf_of_le
- \+/\- *lemma* is_separated_of_is_sheaf
- \+/\- *lemma* is_sheaf_iso
- \+/\- *lemma* is_sheaf_of_yoneda
- \+/\- *lemma* is_separated_for_top
- \+/\- *lemma* extension_iff_amalgamation
- \+/\- *lemma* is_sheaf_for_iff_yoneda_sheaf_condition
- \+/\- *lemma* is_sheaf_for.functor_inclusion_comp_extend
- \+/\- *lemma* is_sheaf_for.unique_extend
- \+/\- *lemma* is_sheaf_for.hom_ext
- \+/\- *lemma* is_sheaf_for_singleton_iso
- \+/\- *lemma* is_sheaf_for_top_sieve
- \+/\- *lemma* is_sheaf_for_iso
- \+/\- *lemma* is_sheaf_for_subsieve_aux
- \+/\- *lemma* is_sheaf_for_subsieve
- \+/\- *lemma* is_sheaf.is_sheaf_for
- \+/\- *lemma* is_sheaf_of_le
- \+/\- *lemma* is_separated_of_is_sheaf
- \+/\- *lemma* is_sheaf_iso
- \+/\- *lemma* is_sheaf_of_yoneda
- \+/\- *def* family_of_elements
- \+/\- *def* is_separated_for
- \+/\- *def* is_sheaf_for
- \+/\- *def* yoneda_sheaf_condition
- \+/\- *def* nat_trans_equiv_compatible_family
- \+/\- *def* is_separated
- \+/\- *def* is_sheaf
- \+/\- *def* first_obj
- \+/\- *def* second_obj
- \+/\- *def* second_obj
- \+/\- *def* SheafOfTypes
- \+/\- *def* SheafOfTypes_to_presheaf
- \+/\- *def* SheafOfTypes_bot_equiv
- \+/\- *def* family_of_elements
- \+/\- *def* is_separated_for
- \+/\- *def* is_sheaf_for
- \+/\- *def* yoneda_sheaf_condition
- \+/\- *def* nat_trans_equiv_compatible_family
- \+/\- *def* is_separated
- \+/\- *def* is_sheaf
- \+/\- *def* first_obj
- \+/\- *def* second_obj
- \+/\- *def* second_obj
- \+/\- *def* SheafOfTypes
- \+/\- *def* SheafOfTypes_to_presheaf
- \+/\- *def* SheafOfTypes_bot_equiv

modified src/topology/sheaves/sheaf_condition/sites.lean
- \+/\- *def* pi_opens_to_first_obj
- \+/\- *def* pi_inters_to_second_obj
- \+/\- *def* pi_opens_to_first_obj
- \+/\- *def* pi_inters_to_second_obj



## [2021-10-14 05:36:14](https://github.com/leanprover-community/mathlib/commit/34f3494)
chore(set_theory/cardinal): rename `is_empty`/`nonempty` lemmas ([#9668](https://github.com/leanprover-community/mathlib/pull/9668))
* add `is_empty_pi`, `is_empty_prod`, `is_empty_pprod`, `is_empty_sum`;
* rename `cardinal.eq_zero_of_is_empty` to `cardinal.mk_eq_zero`, make
  the argument `α : Type u` explicit;
* rename `cardinal.eq_zero_iff_is_empty` to `cardinal.mk_eq_zero_iff`;
* rename `cardinal.ne_zero_iff_nonempty` to `cardinal.mk_ne_zero_iff`;
* add `@[simp]` lemma `cardinal.mk_ne_zero`;
* fix compile errors caused by these changes, golf a few proofs.
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/logic/is_empty.lean
- \+ *lemma* is_empty_pi
- \+ *lemma* is_empty_prod
- \+ *lemma* is_empty_pprod
- \+ *lemma* is_empty_sum
- \+ *lemma* is_empty_psum

modified src/set_theory/cardinal.lean
- \+ *lemma* mk_eq_zero
- \+ *lemma* mk_eq_zero_iff
- \+ *lemma* mk_ne_zero
- \- *lemma* eq_zero_of_is_empty
- \- *lemma* eq_zero_iff_is_empty
- \+ *theorem* mk_ne_zero_iff
- \+/\- *theorem* prod_eq_zero
- \+/\- *theorem* prod_ne_zero
- \+/\- *theorem* omega_ne_zero
- \- *theorem* ne_zero_iff_nonempty
- \+/\- *theorem* prod_ne_zero
- \+/\- *theorem* prod_eq_zero
- \+/\- *theorem* omega_ne_zero

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal_arithmetic.lean



## [2021-10-14 04:04:03](https://github.com/leanprover-community/mathlib/commit/3340617)
feat(algebra/bounds): `smul` of upper/lower bounds ([#9078](https://github.com/leanprover-community/mathlib/pull/9078))
This relates `lower_bounds (a • s)`/`upper_bounds (a • s)` and `a • lower_bounds s`/`a • upper_bounds s`.
#### Estimated changes
modified src/algebra/module/ordered.lean
- \+ *lemma* smul_lower_bounds_subset_lower_bounds_smul
- \+ *lemma* smul_upper_bounds_subset_upper_bounds_smul
- \+ *lemma* bdd_below.smul_of_nonneg
- \+ *lemma* bdd_above.smul_of_nonneg
- \+ *lemma* smul_lower_bounds_subset_upper_bounds_smul
- \+ *lemma* smul_upper_bounds_subset_lower_bounds_smul
- \+ *lemma* bdd_below.smul_of_nonpos
- \+ *lemma* bdd_above.smul_of_nonpos
- \+ *lemma* lower_bounds_smul_of_pos
- \+ *lemma* upper_bounds_smul_of_pos
- \+ *lemma* bdd_below_smul_iff_of_pos
- \+ *lemma* bdd_above_smul_iff_of_pos
- \+ *lemma* lower_bounds_smul_of_neg
- \+ *lemma* upper_bounds_smul_of_neg
- \+ *lemma* bdd_below_smul_iff_of_neg
- \+ *lemma* bdd_above_smul_iff_of_neg



## [2021-10-13 21:29:32](https://github.com/leanprover-community/mathlib/commit/19da20b)
feat(combinatorics/hall): generalized Hall's Marriage Theorem ([#7825](https://github.com/leanprover-community/mathlib/pull/7825))
Used the generalized Kőnig's lemma to prove a version of Hall's Marriage Theorem with the `fintype` constraint on the index type removed.  The original `fintype` version is moved into `hall/finite.lean`, and the infinite version is put in `hall/basic.lean`.  They are in separate files because the infinite version pulls in `topology.category.Top.limits`, which is a rather large dependency.
#### Estimated changes
modified docs/references.bib

created src/combinatorics/hall/basic.lean
- \+ *lemma* hall_matchings_on.nonempty
- \+ *theorem* finset.all_card_le_bUnion_card_iff_exists_injective
- \+ *theorem* fintype.all_card_le_rel_image_card_iff_exists_injective
- \+ *theorem* fintype.all_card_le_filter_rel_iff_exists_injective
- \+ *def* hall_finset_directed_order
- \+ *def* hall_matchings_on
- \+ *def* hall_matchings_on.restrict
- \+ *def* hall_matchings_functor

renamed src/combinatorics/hall.lean to src/combinatorics/hall/finite.lean
- \+ *theorem* finset.all_card_le_bUnion_card_iff_exists_injective'
- \- *theorem* finset.all_card_le_bUnion_card_iff_exists_injective
- \- *theorem* fintype.all_card_le_rel_image_card_iff_exists_injective
- \- *theorem* fintype.all_card_le_filter_rel_iff_exists_injective



## [2021-10-13 17:58:00](https://github.com/leanprover-community/mathlib/commit/5db83f9)
feat(set_theory/cardinal): add lemmas ([#9697](https://github.com/leanprover-community/mathlib/pull/9697))
We add three easy lemmas about cardinals living in different universes.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *lemma* add
- \+ *lemma* mul
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_umax

modified src/set_theory/cofinality.lean



## [2021-10-13 17:57:59](https://github.com/leanprover-community/mathlib/commit/3faf0f5)
chore(data/real/irrational): add more lemmas ([#9684](https://github.com/leanprover-community/mathlib/pull/9684))
#### Estimated changes
modified src/data/real/irrational.lean
- \+/\- *lemma* rat.not_irrational
- \+ *lemma* int.not_irrational
- \+ *lemma* nat.not_irrational
- \+/\- *lemma* rat.not_irrational
- \+ *theorem* ne_rat
- \+ *theorem* ne_int
- \+ *theorem* ne_nat
- \+ *theorem* ne_zero
- \+ *theorem* ne_one
- \+ *theorem* of_int_add
- \+ *theorem* of_add_int
- \+ *theorem* int_add
- \+ *theorem* add_int
- \+ *theorem* of_nat_add
- \+ *theorem* of_add_nat
- \+ *theorem* nat_add
- \+ *theorem* add_nat
- \+ *theorem* sub_int
- \+ *theorem* int_sub
- \+ *theorem* of_sub_int
- \+ *theorem* of_int_sub
- \+ *theorem* sub_nat
- \+ *theorem* nat_sub
- \+ *theorem* of_sub_nat
- \+ *theorem* of_nat_sub
- \+ *theorem* of_mul_int
- \+ *theorem* of_int_mul
- \+ *theorem* mul_int
- \+ *theorem* int_mul
- \+ *theorem* of_mul_nat
- \+ *theorem* of_nat_mul
- \+ *theorem* mul_nat
- \+ *theorem* nat_mul
- \+ *theorem* of_div_rat
- \+ *theorem* rat_div
- \+ *theorem* div_rat
- \+ *theorem* of_int_div
- \+ *theorem* of_div_int
- \+ *theorem* int_div
- \+ *theorem* div_int
- \+ *theorem* of_nat_div
- \+ *theorem* of_div_nat
- \+ *theorem* nat_div
- \+ *theorem* div_nat
- \+/\- *theorem* of_mul_self
- \+ *theorem* irrational_int_add_iff
- \+ *theorem* irrational_nat_add_iff
- \+ *theorem* irrational_add_int_iff
- \+ *theorem* irrational_add_nat_iff
- \+ *theorem* irrational_int_sub_iff
- \+ *theorem* irrational_nat_sub_iff
- \+ *theorem* irrational_sub_int_iff
- \+ *theorem* irrational_sub_nat_iff
- \+ *theorem* irrational_rat_mul_iff
- \+ *theorem* irrational_mul_rat_iff
- \+ *theorem* irrational_int_mul_iff
- \+ *theorem* irrational_mul_int_iff
- \+ *theorem* irrational_nat_mul_iff
- \+ *theorem* irrational_mul_nat_iff
- \+ *theorem* irrational_rat_div_iff
- \+ *theorem* irrational_div_rat_iff
- \+ *theorem* irrational_int_div_iff
- \+ *theorem* irrational_div_int_iff
- \+ *theorem* irrational_nat_div_iff
- \+ *theorem* irrational_div_nat_iff
- \+/\- *theorem* of_mul_self



## [2021-10-13 17:57:58](https://github.com/leanprover-community/mathlib/commit/096923c)
feat(topology/connected.lean): add theorems about connectedness o… ([#9633](https://github.com/leanprover-community/mathlib/pull/9633))
feat(src/topology/connected.lean): add theorems about connectedness of closure
add two theorems is_preconnected.inclosure and is_connected.closure
	which formalize that if a set s is (pre)connected
	and a set t satisfies s ⊆ t ⊆ closure s,
	then t is (pre)connected as well
modify is_preconnected.closure and is_connected.closure
	to take these theorems into account
add a few comments for theorems in the code
#### Estimated changes
modified src/topology/connected.lean
- \+ *theorem* is_preconnected.subset_closure
- \+ *theorem* is_connected.subset_closure



## [2021-10-13 15:48:29](https://github.com/leanprover-community/mathlib/commit/32e1b6c)
chore(ring_theory/ideal): improve 1st isomorphism theorem docstrings ([#9699](https://github.com/leanprover-community/mathlib/pull/9699))
Fix a typo and add **bold** to the theorem names.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean



## [2021-10-13 15:48:28](https://github.com/leanprover-community/mathlib/commit/0ce4442)
refactor(algebra/group_power/order): relax linearity condition on `one_lt_pow` ([#9696](https://github.com/leanprover-community/mathlib/pull/9696))
`[linear_ordered_semiring R]` becomes `[ordered_semiring R] [nontrivial R]`. I also golf the proof and move ìt from `algebra.field_power` to `algebra.group_power.order`, where it belongs.
#### Estimated changes
modified archive/imo/imo2013_q5.lean

modified src/algebra/field_power.lean
- \+/\- *lemma* one_lt_fpow
- \- *lemma* one_lt_pow
- \+/\- *lemma* one_lt_fpow

modified src/algebra/group_power/order.lean
- \+ *lemma* one_lt_pow

modified src/number_theory/liouville/liouville_constant.lean



## [2021-10-13 15:48:27](https://github.com/leanprover-community/mathlib/commit/bc9e38f)
refactor(linear_algebra/dimension): remove some nontrivial assumptions ([#9693](https://github.com/leanprover-community/mathlib/pull/9693))
We remove some `nontrivial R` assumptions.
#### Estimated changes
modified src/linear_algebra/dimension.lean



## [2021-10-13 15:48:25](https://github.com/leanprover-community/mathlib/commit/313db47)
feat(measure_theory/covering/besicovitch): remove measurability assumptions ([#9679](https://github.com/leanprover-community/mathlib/pull/9679))
For applications, it is important to allow non-measurable sets in the Besicovitch covering theorem. We tweak the proof to allow this.
Also give an improved statement that is easier to use in applications.
#### Estimated changes
modified src/measure_theory/covering/besicovitch.lean
- \+ *theorem* exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux
- \+ *theorem* exists_disjoint_closed_ball_covering_ae_aux
- \+ *theorem* exists_disjoint_closed_ball_covering_ae
- \- *theorem* exists_disjoint_closed_ball_covering_of_finite_measure
- \- *theorem* exists_disjoint_closed_ball_covering



## [2021-10-13 15:48:24](https://github.com/leanprover-community/mathlib/commit/f29755b)
refactor(data/set/pairwise): generalize `pairwise_disjoint` to `semilattice_inf_bot` ([#9670](https://github.com/leanprover-community/mathlib/pull/9670))
`set.pairwise_disjoint` was only defined for `set (set α)`. Now, it's defined for `set α` where `semilattice_inf_bot α`. I also
* move it to `data.set.pairwise` because it's really not about `set` anymore.
* drop the `set` namespace.
* add more general elimination rules and rename the current one to `elim_set`.
#### Estimated changes
modified src/data/set/lattice.lean
- \- *lemma* pairwise_disjoint.subset
- \- *lemma* pairwise_disjoint.range
- \- *lemma* pairwise_disjoint.elim
- \- *def* pairwise_disjoint

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint.subset
- \+ *lemma* pairwise_disjoint.range
- \+ *lemma* pairwise_disjoint.elim
- \+ *lemma* pairwise_disjoint.elim'
- \+ *lemma* pairwise_disjoint.elim_set
- \+ *def* pairwise_disjoint

modified src/data/setoid/partition.lean



## [2021-10-13 15:48:22](https://github.com/leanprover-community/mathlib/commit/9ee2a50)
fix(group_theory/group_action): `has_scalar.comp.is_scalar_tower` is a dangerous instance ([#9656](https://github.com/leanprover-community/mathlib/pull/9656))
This issue came up in the discussion of [#9535](https://github.com/leanprover-community/mathlib/pull/9535): in certain cases, the instance `has_scalar.comp.is_scalar_tower` is fed too many metavariables and starts recursing infinitely. So I believe we should demote it from being an instance. Example trace:
```plain
[class_instances] (0) ?x_0 : has_scalar S P.quotient := @quotient.has_scalar ?x_1 ?x_2 ?x_3 ?x_4 ?x_5 ?x_6 ?x_7 ?x_8 ?x_9 ?x_10
[class_instances] (1) ?x_9 : @is_scalar_tower S R M ?x_7
  (@smul_with_zero.to_has_scalar R M
     (@mul_zero_class.to_has_zero R
        (@mul_zero_one_class.to_mul_zero_class R
           (@monoid_with_zero.to_mul_zero_one_class R (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1)))))
     (@add_zero_class.to_has_zero M
        (@add_monoid.to_add_zero_class M
           (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
     (@mul_action_with_zero.to_smul_with_zero R M (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1))
        (@add_zero_class.to_has_zero M
           (@add_monoid.to_add_zero_class M
              (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
        (@module.to_mul_action_with_zero R M (@ring.to_semiring R _inst_1)
           (@add_comm_group.to_add_comm_monoid M _inst_2)
           _inst_3)))
  ?x_8 := @has_scalar.comp.is_scalar_tower ?x_11 ?x_12 ?x_13 ?x_14 ?x_15 ?x_16 ?x_17 ?x_18 ?x_19
[class_instances] (2) ?x_18 : @is_scalar_tower ?x_11 R M ?x_15
  (@smul_with_zero.to_has_scalar R M
     (@mul_zero_class.to_has_zero R
        (@mul_zero_one_class.to_mul_zero_class R
           (@monoid_with_zero.to_mul_zero_one_class R (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1)))))
     (@add_zero_class.to_has_zero M
        (@add_monoid.to_add_zero_class M
           (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
     (@mul_action_with_zero.to_smul_with_zero R M (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1))
        (@add_zero_class.to_has_zero M
           (@add_monoid.to_add_zero_class M
              (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
        (@module.to_mul_action_with_zero R M (@ring.to_semiring R _inst_1)
           (@add_comm_group.to_add_comm_monoid M _inst_2)
           _inst_3)))
  ?x_16 := @has_scalar.comp.is_scalar_tower ?x_20 ?x_21 ?x_22 ?x_23 ?x_24 ?x_25 ?x_26 ?x_27 ?x_28
...
```
You'll see that the places where `has_scalar.comp.is_scalar_tower` expects a `has_scalar.comp` are in fact metavariables, so they always unify.
I have included a test case where the instance looks innocuous enough in its parameters: everything is phrased in terms of either irreducible defs, implicit variables or instance implicits, to argue that the issue really lies with `has_scalar.comp.is_scalar_tower`. Moreover, I don't think we lose a lot by demoting the latter from an instance since `has_scalar.comp` isn't an instance either.
#### Estimated changes
modified src/group_theory/group_action/defs.lean
- \+ *lemma* comp.is_scalar_tower

modified src/linear_algebra/basis.lean

created test/has_scalar_comp_loop.lean
- \+ *def* foo



## [2021-10-13 15:48:21](https://github.com/leanprover-community/mathlib/commit/e8427b0)
feat(ring_theory/ideal/operation): add some extra definitions in the `double_quot` section ([#9649](https://github.com/leanprover-community/mathlib/pull/9649))
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quot_quot_equiv_quot_sup_quot_quot_mk
- \+ *lemma* quot_quot_equiv_quot_sup_symm_quot_quot_mk
- \+ *lemma* quot_quot_equiv_comm_quot_quot_mk
- \+ *lemma* quot_quot_equiv_comm_comp_quot_quot_mk
- \+ *lemma* quot_quot_equiv_comm_symm
- \+ *def* quot_quot_equiv_comm



## [2021-10-13 15:48:20](https://github.com/leanprover-community/mathlib/commit/a7ec633)
chore(algebra/*): add missing lemmas about `copy` on subobjects ([#9624](https://github.com/leanprover-community/mathlib/pull/9624))
This adds `coe_copy` and `copy_eq` to `sub{mul_action,group,ring,semiring,field,module,algebra,lie_module}`, to match the lemmas already present on `submonoid`.
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/algebra/lie/submodule.lean
- \+/\- *lemma* coe_submodule_injective
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+/\- *lemma* coe_submodule_injective

modified src/algebra/module/submodule.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/data/set_like/basic.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/field_theory/subfield.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/ring_theory/subring.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

modified src/ring_theory/subsemiring.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq



## [2021-10-13 15:48:18](https://github.com/leanprover-community/mathlib/commit/577cac1)
feat(algebra/order/nonneg): properties about the nonnegative cone ([#9598](https://github.com/leanprover-community/mathlib/pull/9598))
* Provide various classes on the type `{x : α // 0 ≤ x}` where `α` has some order (and algebraic) structure.
* Use this to automatically derive the classes on `nnreal`.
* We currently do not yet define `conditionally_complete_linear_order_bot nnreal` using nonneg, since that causes some errors (I think Lean then thinks that there are two orders that are not definitionally equal (unfolding only instances)).
* We leave a bunch of `example` lines in `nnreal` to show that `nnreal` has all the old classes. These could also be removed, if desired.
* We currently only give some instances and simp/norm_cast lemmas. This could be expanded in the future.
#### Estimated changes
created src/algebra/order/nonneg.lean
- \+ *lemma* mk_eq_zero
- \+ *lemma* mk_add_mk
- \+ *lemma* nsmul_coe
- \+ *lemma* mk_eq_one
- \+ *lemma* mk_mul_mk
- \+ *lemma* inv_mk
- \+ *lemma* mk_div_mk
- \+ *lemma* coe_to_nonneg
- \+ *lemma* to_nonneg_of_nonneg
- \+ *lemma* to_nonneg_coe
- \+ *lemma* to_nonneg_le
- \+ *lemma* to_nonneg_lt
- \+ *lemma* mk_sub_mk
- \+ *def* coe_add_monoid_hom
- \+ *def* coe_ring_hom
- \+ *def* to_nonneg

modified src/algebra/order/ring.lean
- \+ *lemma* le_iff_exists_nonneg_add

modified src/analysis/normed_space/enorm.lean

modified src/data/real/nnreal.lean
- \+/\- *lemma* nsmul_coe
- \+/\- *lemma* nsmul_coe

modified src/measure_theory/decomposition/jordan.lean

modified src/order/lattice_intervals.lean



## [2021-10-13 13:20:49](https://github.com/leanprover-community/mathlib/commit/aa67421)
lint(tactic/lint/misc): do not lint autogenerated proofs for bad universes ([#9676](https://github.com/leanprover-community/mathlib/pull/9676))
#### Estimated changes
modified src/tactic/lint/misc.lean



## [2021-10-13 13:20:48](https://github.com/leanprover-community/mathlib/commit/ea360f2)
feat(group_theory/sylow): Frattini's Argument ([#9662](https://github.com/leanprover-community/mathlib/pull/9662))
Frattini's argument: If `N` is a normal subgroup of `G`, and `P` is a Sylow `p`-subgroup of `N`, then `PN=G`.
The proof is an application of Sylow's second theorem (all Sylow `p`-subgroups of `N` are conjugate).
#### Estimated changes
modified src/group_theory/group_action/conj_act.lean
- \+ *lemma* _root_.mul_aut.conj_normal_coe

modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* pointwise_smul_def

modified src/group_theory/sylow.lean
- \+ *lemma* sylow.pointwise_smul_def
- \+ *lemma* sylow.smul_def
- \+ *lemma* sylow.normalizer_sup_eq_top



## [2021-10-13 13:20:46](https://github.com/leanprover-community/mathlib/commit/acc1d4b)
feat(analysis/normed_space/SemiNormedGroup/kernels) : add lemmas ([#9654](https://github.com/leanprover-community/mathlib/pull/9654))
From LTE.
#### Estimated changes
modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *lemma* explicit_cokernel_π_surjective
- \+ *lemma* explicit_cokernel_π_apply_dom_eq_zero
- \+ *lemma* explicit_cokernel_π_desc_apply
- \+ *lemma* explicit_cokernel_desc_comp_eq_desc
- \+ *lemma* explicit_cokernel_desc_zero
- \+ *lemma* explicit_cokernel_desc_norm_noninc
- \+ *lemma* explicit_cokernel_desc_comp_eq_zero



## [2021-10-13 13:20:45](https://github.com/leanprover-community/mathlib/commit/6ea59e3)
feat(category_theory/sites/sieves): Added functor pushforward ([#9647](https://github.com/leanprover-community/mathlib/pull/9647))
Defined `sieve.functor_pushforward`.
Proved that `sieve.functor_pushforward` and `sieve.functor_pullback` forms a Galois connection.
Provided some lemmas about `sieve.functor_pushforward`, `sieve.functor_pullback` regarding the lattice structure.
#### Estimated changes
modified src/category_theory/sites/sieves.lean
- \+/\- *lemma* functor_pullback_mem
- \+/\- *lemma* functor_pullback_id
- \+ *lemma* functor_pushforward_comp
- \+ *lemma* image_mem_functor_pushforward
- \+ *lemma* functor_pullback_arrows
- \+/\- *lemma* functor_pullback_id
- \+ *lemma* functor_pullback_comp
- \+ *lemma* functor_pushforward_extend_eq
- \+ *lemma* functor_pushforward_id
- \+ *lemma* functor_pushforward_comp
- \+ *lemma* functor_galois_connection
- \+ *lemma* functor_pullback_monotone
- \+ *lemma* functor_pushforward_monotone
- \+ *lemma* le_functor_pushforward_pullback
- \+ *lemma* functor_pullback_pushforward_le
- \+ *lemma* functor_pushforward_union
- \+ *lemma* functor_pullback_union
- \+ *lemma* functor_pullback_inter
- \+ *lemma* functor_pushforward_bot
- \+ *lemma* functor_pullback_bot
- \+ *lemma* functor_pullback_top
- \+ *lemma* image_mem_functor_pushforward
- \+/\- *lemma* functor_pullback_mem
- \+/\- *lemma* functor_pullback_id
- \+/\- *lemma* functor_pullback_id
- \+/\- *def* functor_pullback
- \+ *def* functor_pushforward
- \+/\- *def* functor_pullback
- \+ *def* functor_pushforward
- \+ *def* ess_surj_full_functor_galois_insertion
- \+ *def* fully_faithful_functor_galois_coinsertion
- \+/\- *def* functor_pullback
- \+/\- *def* functor_pullback



## [2021-10-13 13:20:44](https://github.com/leanprover-community/mathlib/commit/17d8928)
feat(algebra/graded_monoid,algebra/direct_sum/ring): provide lemmas about powers in graded monoids ([#9631](https://github.com/leanprover-community/mathlib/pull/9631))
The key results are `direct_sum.of_pow` and `graded_monoid.mk_pow`.
#### Estimated changes
modified src/algebra/direct_sum/ring.lean
- \+ *lemma* of_eq_of_graded_monoid_eq
- \+ *lemma* of_pow

modified src/algebra/graded_monoid.lean
- \+ *lemma* gnpow_rec_zero
- \+ *lemma* gnpow_rec_succ
- \+ *lemma* mk_pow
- \+ *def* gnpow_rec



## [2021-10-13 13:20:43](https://github.com/leanprover-community/mathlib/commit/edf07cf)
feat(topology/sheaves/sheaf_condition/sites): Connect sheaves on sites to sheaves on spaces ([#9609](https://github.com/leanprover-community/mathlib/pull/9609))
Show that a sheaf on the site `opens X` is the same thing as a sheaf on the space `X`. This finally connects the theory of sheaves on sites to sheaves on spaces, which were previously independent of each other.
#### Estimated changes
created src/topology/sheaves/sheaf_condition/sites.lean
- \+ *lemma* covering_of_presieve_apply
- \+ *lemma* supr_eq_of_mem_grothendieck
- \+ *lemma* first_obj_iso_pi_opens_π
- \+ *lemma* second_obj_iso_pi_inters_π
- \+ *lemma* fork_map_comp_first_obj_iso_pi_opens_eq
- \+ *lemma* first_obj_iso_comp_left_res_eq
- \+ *lemma* first_obj_iso_comp_right_res_eq
- \+ *lemma* is_sheaf_sites_of_is_sheaf_spaces
- \+ *lemma* mem_grothendieck_topology
- \+ *lemma* index_of_hom_spec
- \+ *lemma* fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq
- \+ *lemma* pi_opens_to_first_obj_comp_fist_map_eq
- \+ *lemma* pi_opens_to_first_obj_comp_second_map_eq
- \+ *lemma* fork_map_comp_first_map_to_pi_opens_eq
- \+ *lemma* res_comp_pi_opens_to_first_obj_eq
- \+ *lemma* is_sheaf_spaces_of_is_sheaf_sites
- \+ *lemma* is_sheaf_sites_iff_is_sheaf_spaces
- \+ *def* covering_of_presieve
- \+ *def* first_obj_iso_pi_opens
- \+ *def* second_obj_iso_pi_inters
- \+ *def* diagram_nat_iso
- \+ *def* postcompose_diagram_fork_hom
- \+ *def* postcompose_diagram_fork_iso
- \+ *def* presieve_of_covering
- \+ *def* hom_of_index
- \+ *def* index_of_hom
- \+ *def* first_obj_to_pi_opens
- \+ *def* pi_opens_to_first_obj
- \+ *def* pi_inters_to_second_obj
- \+ *def* Sheaf_sites_to_sheaf_spaces
- \+ *def* Sheaf_spaces_to_sheaf_sites
- \+ *def* Sheaf_spaces_equivelence_sheaf_sites



## [2021-10-13 13:20:41](https://github.com/leanprover-community/mathlib/commit/f238733)
feat(algebra/order/smul): Monotonicity of scalar multiplication ([#9558](https://github.com/leanprover-community/mathlib/pull/9558))
Also prove `smul_nonneg`, `smul_pos` and variants.
#### Estimated changes
modified src/algebra/module/ordered.lean
- \+ *lemma* smul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* smul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* antitone_smul_left
- \+ *lemma* strict_anti_smul_left
- \+ *def* order_iso.smul_left_dual

modified src/algebra/order/smul.lean
- \+ *lemma* to_dual_smul
- \+ *lemma* of_dual_smul
- \+ *lemma* smul_nonneg
- \+ *lemma* smul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* monotone_smul_left
- \+ *lemma* strict_mono_smul_left
- \+ *def* order_iso.smul_left



## [2021-10-13 12:04:30](https://github.com/leanprover-community/mathlib/commit/04ed867)
chore(topology/uniform_space/cauchy): add a few simple lemmas ([#9685](https://github.com/leanprover-community/mathlib/pull/9685))
* rename `cauchy_prod` to `cauchy.prod`;
* add `cauchy_seq.tendsto_uniformity`, `cauchy_seq.nonempty`,
  `cauchy_seq.comp_tendsto`, `cauchy_seq.prod`, `cauchy_seq.prod_map`,
  `uniform_continuous.comp_cauchy_seq`, and
  `filter.tendsto.subseq_mem_entourage`;
* drop `[nonempty _]` assumption in `cauchy_seq.mem_entourage`.
#### Estimated changes
modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy.prod
- \+ *lemma* cauchy_seq.tendsto_uniformity
- \+ *lemma* cauchy_seq.nonempty
- \+/\- *lemma* cauchy_seq.mem_entourage
- \+ *lemma* cauchy_seq.comp_tendsto
- \+ *lemma* cauchy_seq.prod_map
- \+ *lemma* cauchy_seq.prod
- \+ *lemma* uniform_continuous.comp_cauchy_seq
- \+ *lemma* filter.tendsto.subseq_mem_entourage
- \+/\- *lemma* cauchy_seq.mem_entourage
- \- *lemma* cauchy_prod



## [2021-10-13 09:37:08](https://github.com/leanprover-community/mathlib/commit/46a7014)
feat(data/equiv/basic): psigma_congr_right ([#9687](https://github.com/leanprover-community/mathlib/pull/9687))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* psigma_congr_right_trans
- \+ *lemma* psigma_congr_right_symm
- \+ *lemma* psigma_congr_right_refl
- \+/\- *lemma* sigma_congr_right_trans
- \+/\- *lemma* sigma_congr_right_symm
- \+/\- *lemma* sigma_congr_right_refl
- \+/\- *lemma* sigma_congr_right_trans
- \+/\- *lemma* sigma_congr_right_symm
- \+/\- *lemma* sigma_congr_right_refl
- \+/\- *def* psigma_equiv_sigma
- \+ *def* psigma_congr_right
- \+/\- *def* sigma_congr_right
- \+/\- *def* psigma_equiv_sigma
- \+/\- *def* sigma_congr_right



## [2021-10-13 09:37:07](https://github.com/leanprover-community/mathlib/commit/4c1a9c4)
chore(order/filter): add 2 lemmas ([#9682](https://github.com/leanprover-community/mathlib/pull/9682))
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* frequently_and_distrib_left
- \+ *lemma* frequently_and_distrib_right



## [2021-10-13 09:37:00](https://github.com/leanprover-community/mathlib/commit/8886386)
feat(star/basic): add a `star_monoid (units R)` instance ([#9681](https://github.com/leanprover-community/mathlib/pull/9681))
This also moves all the `opposite R` instances to be adjacent, and add some missing `star_module` definitions.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* coe_star
- \+ *lemma* coe_star_inv
- \+/\- *lemma* unop_star
- \+/\- *lemma* op_star
- \+/\- *lemma* unop_star
- \+/\- *lemma* op_star



## [2021-10-13 09:36:59](https://github.com/leanprover-community/mathlib/commit/52d5fd4)
feat(linear_algebra/{dimension,affine_space/finite_dimensional}): independent subsets of finite-dimensional spaces are finite. ([#9674](https://github.com/leanprover-community/mathlib/pull/9674))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *def* fintype_of_fintype_ne

modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* finite_of_fin_dim_affine_independent

modified src/linear_algebra/dimension.lean
- \+ *lemma* finite_of_is_noetherian_linear_independent



## [2021-10-13 07:56:13](https://github.com/leanprover-community/mathlib/commit/2c8abe5)
feat(algebra/star): `star_gpow` and `star_fpow` ([#9661](https://github.com/leanprover-community/mathlib/pull/9661))
One unrelated proof changes as the import additions pulls in a simp lemma that was previously missing, making the call to `ring` no longer necessary.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* star_gpow
- \+ *lemma* star_fpow

modified src/ring_theory/polynomial/bernstein.lean



## [2021-10-13 02:43:35](https://github.com/leanprover-community/mathlib/commit/ea70e1c)
chore(scripts): update nolints.txt ([#9686](https://github.com/leanprover-community/mathlib/pull/9686))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-10-12 22:59:49](https://github.com/leanprover-community/mathlib/commit/c65de1e)
chore(data/sym/sym2): speed up some proofs ([#9677](https://github.com/leanprover-community/mathlib/pull/9677))
In one test, elaboration of sym2_ext went from 46.9s to 734ms, and of elems_iff_eq from 54.3s to 514ms.
#### Estimated changes
modified src/data/sym/sym2.lean



## [2021-10-12 17:00:40](https://github.com/leanprover-community/mathlib/commit/66285c9)
feat(topology/instances/ennreal): if a tsum is finite, then the tsum over the complement of a finset tends to 0 at top ([#9665](https://github.com/leanprover-community/mathlib/pull/9665))
Together with minor tweaks of the library:
* rename `bounded.subset` to `bounded.mono`
* remove `bUnion_subset_bUnion_right`, which is exactly the same as `bUnion_mono`. Same for intersections.
* add `bUnion_congr` and `bInter_congr`
* introduce lemma `null_of_locally_null`: if a set has zero measure in a neighborhood of each of its points, then it has zero measure in a second-countable space.
#### Estimated changes
modified src/data/finset/lattice.lean
- \+ *lemma* subset_set_bUnion_of_mem

modified src/data/set/accumulate.lean

modified src/data/set/function.lean
- \+ *lemma* inj_on.pairwise_on_image

modified src/data/set/lattice.lean
- \+ *lemma* bInter_congr
- \+ *lemma* bUnion_congr
- \+/\- *lemma* pairwise_on_Union
- \+ *lemma* pairwise_on_sUnion
- \+/\- *lemma* pairwise_on_Union
- \- *theorem* bUnion_subset_bUnion_right
- \- *theorem* bInter_subset_bInter_right

modified src/dynamics/omega_limit.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* null_of_locally_null

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tendsto_tsum_compl_at_top_zero
- \+/\- *lemma* summable.sigma
- \+/\- *lemma* tsum_sigma
- \+/\- *lemma* tsum_prod
- \+/\- *lemma* tsum_comm
- \+/\- *lemma* summable.sigma
- \+/\- *lemma* tsum_sigma
- \+/\- *lemma* tsum_prod
- \+/\- *lemma* tsum_comm

modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_tsum_compl_at_top_zero

modified src/topology/instances/nnreal.lean
- \+ *lemma* tendsto_tsum_compl_at_top_zero

modified src/topology/instances/real.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded.mono
- \- *lemma* bounded.subset

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/subset_properties.lean



## [2021-10-12 17:00:39](https://github.com/leanprover-community/mathlib/commit/817c70d)
feat(category_theory/*): Functors about comma categories. ([#9627](https://github.com/leanprover-community/mathlib/pull/9627))
Added `pre` and `post` for `comma`, `structured_arrow`, `costructured_arrow`.
#### Estimated changes
modified src/category_theory/comma.lean
- \+ *def* pre_left
- \+ *def* pre_right
- \+ *def* post

modified src/category_theory/structured_arrow.lean
- \+ *def* pre
- \+ *def* post
- \+ *def* pre
- \+ *def* post



## [2021-10-12 15:09:33](https://github.com/leanprover-community/mathlib/commit/f63b8f1)
feat(algebra/star/basic): add some helper lemmas about star ([#9651](https://github.com/leanprover-community/mathlib/pull/9651))
This adds the new lemmas:
* `star_pow`
* `star_nsmul`
* `star_gsmul`
* `star_prod`
* `star_div`
* `star_div'`
* `star_inv`
* `star_inv'`
* `star_mul'`
and generalizes the typeclass assumptions from `star_ring` to `star_add_monoid` on:
* `star_neg`
* `star_sub`
* `star_sum`
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* star_mul'
- \+ *lemma* star_pow
- \+ *lemma* star_inv
- \+ *lemma* star_div
- \+ *lemma* star_prod
- \+/\- *lemma* star_neg
- \+/\- *lemma* star_sub
- \+ *lemma* star_nsmul
- \+ *lemma* star_gsmul
- \+/\- *lemma* star_sum
- \+ *lemma* star_inv'
- \+ *lemma* star_div'
- \+/\- *lemma* star_sum
- \+/\- *lemma* star_neg
- \+/\- *lemma* star_sub



## [2021-10-12 11:41:14](https://github.com/leanprover-community/mathlib/commit/b486c88)
chore(analysis): fix file name ([#9673](https://github.com/leanprover-community/mathlib/pull/9673))
This file was moved since the docstring was written
#### Estimated changes
modified src/analysis/calculus/parametric_integral.lean



## [2021-10-12 11:41:13](https://github.com/leanprover-community/mathlib/commit/bcb2943)
chore(set_theory/cardinal): move defs/lemmas about `lift` up ([#9669](https://github.com/leanprover-community/mathlib/pull/9669))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+/\- *theorem* lift_mk
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+/\- *theorem* lift_lift
- \+/\- *theorem* lift_mk_le
- \+/\- *theorem* lift_mk_le'
- \+/\- *theorem* lift_mk_eq
- \+/\- *theorem* lift_mk_eq'
- \+/\- *theorem* lift_le
- \+/\- *theorem* lift_inj
- \+/\- *theorem* lift_lt
- \+/\- *theorem* lift_zero
- \+/\- *theorem* lift_power
- \+/\- *theorem* lift_one
- \+/\- *theorem* lift_add
- \+/\- *theorem* lift_mul
- \+/\- *theorem* lift_bit0
- \+/\- *theorem* lift_bit1
- \+/\- *theorem* lift_two
- \+/\- *theorem* lift_two_power
- \+/\- *theorem* lift_mk
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+/\- *theorem* lift_lift
- \+/\- *theorem* lift_mk_le
- \+/\- *theorem* lift_mk_le'
- \+/\- *theorem* lift_mk_eq
- \+/\- *theorem* lift_mk_eq'
- \+/\- *theorem* lift_le
- \+/\- *theorem* lift_inj
- \+/\- *theorem* lift_lt
- \+/\- *theorem* lift_zero
- \+/\- *theorem* lift_one
- \+/\- *theorem* lift_add
- \+/\- *theorem* lift_mul
- \+/\- *theorem* lift_power
- \+/\- *theorem* lift_bit0
- \+/\- *theorem* lift_bit1
- \+/\- *theorem* lift_two
- \+/\- *theorem* lift_two_power
- \+/\- *def* lift
- \+/\- *def* lift



## [2021-10-12 11:41:12](https://github.com/leanprover-community/mathlib/commit/a979d15)
feat(order/filter): `∃ᶠ m in at_top, m ≡ d [MOD n]` ([#9666](https://github.com/leanprover-community/mathlib/pull/9666))
#### Estimated changes
created src/order/filter/modeq.lean
- \+ *lemma* frequently_modeq
- \+ *lemma* frequently_mod_eq
- \+ *lemma* frequently_even
- \+ *lemma* frequently_odd



## [2021-10-12 08:59:45](https://github.com/leanprover-community/mathlib/commit/fd7da4e)
refactor(combinatorics/partition): add `nat` namespace ([#9672](https://github.com/leanprover-community/mathlib/pull/9672))
`partition` is now `nat.partition`
#### Estimated changes
modified src/combinatorics/partition.lean

modified src/group_theory/perm/cycle_type.lean
- \+/\- *def* partition
- \+/\- *def* partition



## [2021-10-12 08:59:43](https://github.com/leanprover-community/mathlib/commit/2e72f35)
refactor(data/opposite): Remove the `op_induction` tactic ([#9660](https://github.com/leanprover-community/mathlib/pull/9660))
The `induction` tactic is already powerful enough for this; we don't have `order_dual_induction` or `nat_induction` as tactics.
The bulk of this change is replacing `op_induction x` with `induction x using opposite.rec`.
This leaves behind the non-interactive `op_induction'` which is still needed as a `tidy` hook.
This also renames the def `opposite.op_induction` to `opposite.rec` to match `order_dual.rec` etc.
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/opposites.lean

modified src/algebra/quandle.lean

modified src/algebraic_geometry/presheafed_space.lean

modified src/algebraic_geometry/presheafed_space/has_colimits.lean

modified src/algebraic_geometry/sheafed_space.lean

modified src/algebraic_geometry/stalks.lean

modified src/category_theory/limits/cones.lean

modified src/data/opposite.lean
- \- *def* op_induction

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean

modified src/topology/sheaves/stalks.lean



## [2021-10-12 08:59:41](https://github.com/leanprover-community/mathlib/commit/ad4040d)
feat(algebra/opposites): provide npow and gpow explicitly, prove `op_gpow` and `unop_gpow` ([#9659](https://github.com/leanprover-community/mathlib/pull/9659))
By populating the `npow` and `gpow` fields in the obvious way, `op_pow` and `unop_pow` are true definitionally.
This adds the new lemmas `op_gpow` and `unop_gpow` which works for `group`s and `division_ring`s too.
Note that we do not provide an explicit `div` in `div_inv_monoid`, because there is no "reversed division" operator to define it via.
This also reorders the lemmas so that the definitional lemmas are available before any proof obligations might appear in stronger typeclasses.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* op_pow
- \+/\- *lemma* unop_pow
- \+ *lemma* op_gpow
- \+ *lemma* unop_gpow
- \+/\- *lemma* op_pow
- \+/\- *lemma* unop_pow

modified src/algebra/opposites.lean
- \+/\- *lemma* op_zero
- \+/\- *lemma* unop_zero
- \+/\- *lemma* op_one
- \+/\- *lemma* unop_one
- \+/\- *lemma* op_add
- \+/\- *lemma* unop_add
- \+/\- *lemma* op_neg
- \+/\- *lemma* unop_neg
- \+/\- *lemma* op_mul
- \+/\- *lemma* unop_mul
- \+/\- *lemma* op_inv
- \+/\- *lemma* unop_inv
- \+/\- *lemma* op_sub
- \+/\- *lemma* unop_sub
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul
- \+/\- *lemma* op_zero
- \+/\- *lemma* unop_zero
- \+/\- *lemma* op_one
- \+/\- *lemma* unop_one
- \+/\- *lemma* op_add
- \+/\- *lemma* unop_add
- \+/\- *lemma* op_neg
- \+/\- *lemma* unop_neg
- \+/\- *lemma* op_mul
- \+/\- *lemma* unop_mul
- \+/\- *lemma* op_inv
- \+/\- *lemma* unop_inv
- \+/\- *lemma* op_sub
- \+/\- *lemma* unop_sub
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul



## [2021-10-12 08:59:38](https://github.com/leanprover-community/mathlib/commit/34ffb15)
feat(linear_algebra/affine_space/finite_dimensional): upgrade `affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one` to an iff ([#9657](https://github.com/leanprover-community/mathlib/pull/9657))
Also including some related, but strictly speaking independent, lemmas such as `affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial`.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.subsingleton_iff

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* vector_span_eq_top_of_affine_span_eq_top
- \+ *lemma* affine_span_eq_top_iff_vector_span_eq_top_of_nonempty
- \+ *lemma* affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial
- \+ *lemma* card_pos_of_affine_span_eq_top

modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one
- \- *lemma* affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one



## [2021-10-12 08:16:55](https://github.com/leanprover-community/mathlib/commit/1023d81)
chore(ring_theory/tensor_product): squeeze simps in a slow proof ([#9671](https://github.com/leanprover-community/mathlib/pull/9671))
This proof just timed out in bors. Goes from 21s to 1s on my computer just by squeezing the simps.
#### Estimated changes
modified src/ring_theory/tensor_product.lean



## [2021-10-12 06:20:54](https://github.com/leanprover-community/mathlib/commit/a132d0a)
chore(analysis): move some files to `analysis/normed/group` ([#9667](https://github.com/leanprover-community/mathlib/pull/9667))
#### Estimated changes
renamed src/analysis/normed_space/SemiNormedGroup.lean to src/analysis/normed/group/SemiNormedGroup.lean

renamed src/analysis/normed_space/SemiNormedGroup/kernels.lean to src/analysis/normed/group/SemiNormedGroup/kernels.lean

renamed src/analysis/normed_space/normed_group_hom.lean to src/analysis/normed/group/hom.lean

renamed src/analysis/normed_space/normed_group_hom_completion.lean to src/analysis/normed/group/hom_completion.lean

renamed src/analysis/normed_space/normed_group_quotient.lean to src/analysis/normed/group/quotient.lean

modified src/measure_theory/function/lp_space.lean



## [2021-10-12 01:53:33](https://github.com/leanprover-community/mathlib/commit/638dd0f)
feat(data/dfinsupp, algebra/direct_sum/module): direct sum on fintype ([#9664](https://github.com/leanprover-community/mathlib/pull/9664))
Analogues for `dfinsupp`/`direct_sum` of definitions/lemmas such as `finsupp.equiv_fun_on_fintype`:  a `dfinsupp`/`direct_sum` over a finite index set is canonically equivalent to `pi` over the same index set.
#### Estimated changes
modified src/algebra/direct_sum/module.lean
- \+ *lemma* linear_equiv_fun_on_fintype_lof
- \+ *lemma* linear_equiv_fun_on_fintype_symm_single
- \+ *lemma* linear_equiv_fun_on_fintype_symm_coe
- \+ *def* linear_equiv_fun_on_fintype

modified src/data/dfinsupp.lean
- \+ *lemma* equiv_fun_on_fintype_symm_coe
- \+ *lemma* single_eq_pi_single
- \+ *lemma* equiv_fun_on_fintype_single
- \+ *lemma* equiv_fun_on_fintype_symm_single
- \+ *def* equiv_fun_on_fintype



## [2021-10-11 22:34:26](https://github.com/leanprover-community/mathlib/commit/c2a30be)
feat(analysis/normed_space/normed_group_hom): add norm_noninc.neg ([#9658](https://github.com/leanprover-community/mathlib/pull/9658))
From LTE.
#### Estimated changes
modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* neg_iff



## [2021-10-11 21:39:10](https://github.com/leanprover-community/mathlib/commit/df132fe)
feat(topology/path_connected): add `path.reparam` for reparametrising a path. ([#9643](https://github.com/leanprover-community/mathlib/pull/9643))
I've also added `simps` to some of the definitions in this file.
#### Estimated changes
modified src/topology/path_connected.lean
- \+ *lemma* coe_to_fun
- \+ *lemma* reparam_id
- \+ *lemma* range_reparam
- \+ *lemma* refl_reparam
- \+ *def* simps.apply
- \+/\- *def* refl
- \+/\- *def* symm
- \+ *def* reparam
- \+/\- *def* refl
- \+/\- *def* symm



## [2021-10-11 20:04:44](https://github.com/leanprover-community/mathlib/commit/136d0ce)
feat(topology/homotopy/path): Add homotopy between paths ([#9141](https://github.com/leanprover-community/mathlib/pull/9141))
There is also a lemma about `path.to_continuous_map` which I needed in a prior iteration of this PR that I missed in [#9133](https://github.com/leanprover-community/mathlib/pull/9133)
#### Estimated changes
modified src/topology/homotopy/basic.lean

created src/topology/homotopy/path.lean
- \+ *lemma* coe_fn_injective
- \+ *lemma* source
- \+ *lemma* target
- \+ *lemma* eval_zero
- \+ *lemma* eval_one
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans
- \+ *lemma* hcomp_apply
- \+ *lemma* hcomp_half
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* equivalence
- \+ *def* eval
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* hcomp
- \+ *def* homotopic

modified src/topology/path_connected.lean
- \+ *lemma* coe_to_continuous_map



## [2021-10-11 18:55:35](https://github.com/leanprover-community/mathlib/commit/6872dfb)
feat(analysis/normed/group/basic): add norm_le_add_norm_add ([#9655](https://github.com/leanprover-community/mathlib/pull/9655))
From LTE.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+ *lemma* norm_le_add_norm_add



## [2021-10-11 15:29:09](https://github.com/leanprover-community/mathlib/commit/fa5d9d6)
feat(tactic/lint/misc): unused haves and suffices linters ([#9310](https://github.com/leanprover-community/mathlib/pull/9310))
A linter for unused term mode have and suffices statements.
Based on initial work by @robertylewis https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/linter.20for.20helping.20grading/near/209243601 but hopefully with less false positives now.
#### Estimated changes
modified src/control/traversable/instances.lean

modified src/order/complete_lattice.lean

modified src/tactic/lint/misc.lean

created test/lint_unused_haves_suffices.lean
- \+ *lemma* test_a
- \+ *lemma* test_b
- \+ *lemma* test_c
- \+ *theorem* test_map_reverse
- \+ *theorem* test_d



## [2021-10-11 07:59:25](https://github.com/leanprover-community/mathlib/commit/c2fde70)
feat(number_theory/liouville): Liouville numbers form a dense Gδ set ([#9646](https://github.com/leanprover-community/mathlib/pull/9646))
#### Estimated changes
created src/number_theory/liouville/residual.lean
- \+ *lemma* set_of_liouville_eq_Inter_Union
- \+ *lemma* is_Gδ_set_of_liouville
- \+ *lemma* is_Gδ_irrational
- \+ *lemma* dense_irrational
- \+ *lemma* eventually_residual_irrational
- \+ *lemma* set_of_liouville_eq_irrational_inter_Inter_Union
- \+ *lemma* eventually_residual_liouville
- \+ *lemma* dense_liouville

modified src/topology/metric_space/baire.lean
- \+ *lemma* dense_of_mem_residual



## [2021-10-11 07:59:24](https://github.com/leanprover-community/mathlib/commit/082aa83)
feat(data/finset): add `finset.erase_none` ([#9630](https://github.com/leanprover-community/mathlib/pull/9630))
* move `option.to_finset` and `finset.insert_none` to a new file `data.finset.option`; redefine the latter in terms of `finset.cons`;
* define `finset.erase_none`, prove lemmas about it;
* add `finset.prod_cons`, `finset.sum_cons`, `finset.coe_cons`, `finset.cons_subset_cons`, `finset.card_cons`;
* add `finset.subtype_mono` and `finset.bUnion_congr`;
* add `set.insert_subset_insert_iff`;
* add `@[simp]` to `finset.map_subset_map`;
* upgrade `finset.map_embedding` to an `order_embedding`;
* add `@[simps]` to `equiv.option_is_some_equiv` and `function.embedding.some`;
* golf some proofs.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_cons
- \+/\- *lemma* prod_multiset_map_count
- \+/\- *lemma* prod_multiset_map_count
- \- *lemma* sum_multiset_map_count

created src/algebra/big_operators/option.lean
- \+ *lemma* prod_insert_none
- \+ *lemma* prod_erase_none

modified src/algebra/polynomial/big_operators.lean

modified src/data/equiv/basic.lean
- \+/\- *def* option_is_some_equiv
- \+/\- *def* option_is_some_equiv

modified src/data/finset/basic.lean
- \+ *lemma* coe_cons
- \+ *lemma* cons_subset_cons
- \+ *lemma* subtype_mono
- \+/\- *theorem* mem_cons
- \+/\- *theorem* map_subset_map
- \+/\- *theorem* map_inj
- \+ *theorem* card_cons
- \+ *theorem* bUnion_congr
- \+/\- *theorem* mem_cons
- \- *theorem* to_finset_none
- \- *theorem* to_finset_some
- \- *theorem* mem_to_finset
- \+/\- *theorem* map_subset_map
- \+/\- *theorem* map_inj
- \+/\- *def* map_embedding
- \- *def* to_finset
- \+/\- *def* map_embedding

modified src/data/finset/lattice.lean

created src/data/finset/option.lean
- \+ *lemma* mem_erase_none
- \+ *lemma* erase_none_eq_bUnion
- \+ *lemma* erase_none_map_some
- \+ *lemma* erase_none_image_some
- \+ *lemma* coe_erase_none
- \+ *lemma* erase_none_union
- \+ *lemma* erase_none_inter
- \+ *lemma* erase_none_empty
- \+ *lemma* erase_none_none
- \+ *lemma* image_some_erase_none
- \+ *lemma* map_some_erase_none
- \+ *lemma* insert_none_erase_none
- \+ *lemma* erase_none_insert_none
- \+ *theorem* to_finset_none
- \+ *theorem* to_finset_some
- \+ *theorem* mem_to_finset
- \+ *theorem* card_to_finset
- \+ *theorem* mem_insert_none
- \+ *theorem* some_mem_insert_none
- \+ *theorem* card_insert_none
- \+ *def* to_finset
- \+ *def* insert_none
- \+ *def* erase_none

modified src/data/finset/pimage.lean

modified src/data/fintype/basic.lean
- \- *theorem* finset.mem_insert_none
- \- *theorem* finset.some_mem_insert_none
- \- *def* finset.insert_none

modified src/data/fintype/card.lean

modified src/data/set/basic.lean
- \+ *theorem* insert_subset_insert_iff

modified src/logic/embedding.lean



## [2021-10-11 07:59:23](https://github.com/leanprover-community/mathlib/commit/1539ee1)
refactor(topology/sheaves/*): Make sheaf condition a Prop ([#9607](https://github.com/leanprover-community/mathlib/pull/9607))
Make `sheaf_condition` into a `Prop` and redefine the type of sheaves on a topological space `X` as a subtype of `(opens X)ᵒᵖ ⥤ C`.
#### Estimated changes
modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* restrict
- \+ *def* restrict_top_iso

modified src/algebraic_geometry/sheafed_space.lean
- \+/\- *def* sheaf
- \+/\- *def* sheaf

modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *lemma* exists_const
- \+/\- *lemma* exists_const
- \+/\- *def* to_stalk
- \+/\- *def* basic_open_iso
- \+/\- *def* global_sections_iso
- \+/\- *def* to_stalk
- \+/\- *def* basic_open_iso
- \+/\- *def* global_sections_iso

modified src/topology/sheaves/forget.lean
- \+ *lemma* is_sheaf_iff_is_sheaf_comp
- \- *def* sheaf_condition_equiv_sheaf_condition_comp

modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* is_sheaf
- \- *def* sheaf_condition

modified src/topology/sheaves/sheaf.lean
- \+ *lemma* is_sheaf_punit
- \+ *lemma* is_sheaf_of_iso
- \+ *lemma* is_sheaf_iso_iff
- \+ *def* is_sheaf
- \+ *def* sheaf
- \+/\- *def* forget
- \- *def* sheaf_condition
- \- *def* sheaf_condition_punit
- \- *def* sheaf_condition_equiv_of_iso
- \+/\- *def* forget

modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *lemma* is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections
- \+ *lemma* is_sheaf_iff_is_sheaf_opens_le_cover
- \+ *def* is_sheaf_opens_le_cover
- \- *def* sheaf_condition_opens_le_cover
- \- *def* sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections
- \- *def* sheaf_condition_equiv_sheaf_condition_opens_le_cover

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean
- \+ *lemma* is_sheaf_iff_is_sheaf_pairwise_intersections
- \+ *lemma* is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections
- \+ *def* is_sheaf_pairwise_intersections
- \+ *def* is_sheaf_preserves_limit_pairwise_intersections
- \- *def* sheaf_condition_pairwise_intersections
- \- *def* sheaf_condition_preserves_limit_pairwise_intersections
- \- *def* sheaf_condition_equiv_sheaf_condition_pairwise_intersections
- \- *def* sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections

modified src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \+ *lemma* is_sheaf_of_is_sheaf_unique_gluing_types
- \+ *lemma* is_sheaf_unique_gluing_of_is_sheaf_types
- \+ *lemma* is_sheaf_iff_is_sheaf_unique_gluing_types
- \+ *lemma* is_sheaf_iff_is_sheaf_unique_gluing
- \+/\- *lemma* exists_unique_gluing
- \+/\- *lemma* eq_of_locally_eq
- \+/\- *lemma* exists_unique_gluing
- \+/\- *lemma* eq_of_locally_eq
- \+ *def* is_sheaf_unique_gluing
- \- *def* gluing
- \- *def* sheaf_condition_unique_gluing
- \- *def* sheaf_condition_of_sheaf_condition_unique_gluing_types
- \- *def* sheaf_condition_unique_gluing_of_sheaf_condition_types
- \- *def* sheaf_condition_equiv_sheaf_condition_unique_gluing_types
- \- *def* sheaf_condition_equiv_sheaf_condition_unique_gluing
- \- *def* sheaf_condition_of_exists_unique_gluing

modified src/topology/sheaves/sheaf_of_functions.lean
- \+ *lemma* to_Types_is_sheaf
- \+ *lemma* to_Type_is_sheaf
- \- *def* to_Types
- \- *def* to_Type

modified src/topology/sheaves/sheafify.lean
- \+/\- *def* to_sheafify
- \+/\- *def* stalk_to_fiber
- \+/\- *def* sheafify_stalk_iso
- \+/\- *def* to_sheafify
- \+/\- *def* stalk_to_fiber
- \+/\- *def* sheafify_stalk_iso

modified src/topology/sheaves/stalks.lean
- \+/\- *lemma* section_ext
- \+/\- *lemma* section_ext



## [2021-10-11 07:59:22](https://github.com/leanprover-community/mathlib/commit/4a191ad)
feat(algebra.algebra.subalgebra): add `subalgebra.gc_map_comap` ([#9435](https://github.com/leanprover-community/mathlib/pull/9435))
Other changes:
* add `linear_map.coe_inl`/`linear_map.coe_inr` and move `@[simp]` from `inl_apply`/`inr_apply` to these lemmas;
* fix a typo in the name (`adjoint` → `adjoin`);
* drop `algebra.adjoin_inl_union_inr_le_prod `: we prove an equality anyway;
* add `alg_hom.map_adjoin` (same as `(adjoin_image _ _ _).symm`) to match `monoid_hom.map_closure` etc.
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* gc_map_comap

modified src/linear_algebra/prod.lean
- \+ *theorem* coe_inl
- \+/\- *theorem* inl_apply
- \+ *theorem* coe_inr
- \+/\- *theorem* inr_apply
- \+/\- *theorem* inl_apply
- \+/\- *theorem* inr_apply

modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_prod_le
- \+ *lemma* map_adjoin
- \- *lemma* adjoint_prod_le
- \- *lemma* adjoin_inl_union_inr_le_prod



## [2021-10-11 06:17:12](https://github.com/leanprover-community/mathlib/commit/30cf8b7)
feat(group_theory/subgroup/basic): apply_mem_map_injective ([#9637](https://github.com/leanprover-community/mathlib/pull/9637))
A translation of `function.injective.mem_set_image`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mem_map_iff_mem

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mem_map_iff_mem



## [2021-10-11 06:17:11](https://github.com/leanprover-community/mathlib/commit/957f64e)
feat(algebra/floor): When the floor is strictly positive ([#9625](https://github.com/leanprover-community/mathlib/pull/9625))
`⌊a⌋₊` and `⌊a⌋` are strictly positive iff `1 ≤ a`. We use this to slightly golf IMO 2013 P5.
#### Estimated changes
modified archive/imo/imo2013_q5.lean

modified src/algebra/floor.lean
- \+ *lemma* floor_pos
- \+ *lemma* nat_floor_pos
- \+/\- *lemma* pos_of_nat_floor_pos
- \+ *lemma* sub_one_lt_nat_floor
- \+/\- *lemma* pos_of_nat_floor_pos



## [2021-10-11 04:03:52](https://github.com/leanprover-community/mathlib/commit/bcd79a1)
chore(analysis/normed/group/basic): rename vars ([#9652](https://github.com/leanprover-community/mathlib/pull/9652))
* use `E`, `F` for (semi)normed groups and greek letters for other
  types;
* golf some proofs (`bounded_iff_forall_norm_le`, `norm_pos_iff'`);
* use `namespace lipschitz_with` and `namespace antilipschitz_with`
  instead of manual prefixes for all lemmas;
* generalize `antilipschitz_with.add_lipschitz_with` to
  `pseudo_emetric_space`;
* add `antilipschitz_with.edist_lt_top` and
  `antilipschitz_with.edist_ne_top`;
* fix a typo in `pseudo_emetric_space.to_pseudo_metric_space`.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* dist_eq_norm
- \+/\- *lemma* dist_eq_norm'
- \+/\- *lemma* dist_zero_right
- \+/\- *lemma* dist_zero_left
- \+/\- *lemma* tendsto_norm_cocompact_at_top
- \+/\- *lemma* norm_sub_rev
- \+/\- *lemma* norm_neg
- \+/\- *lemma* dist_add_left
- \+/\- *lemma* dist_add_right
- \+/\- *lemma* dist_neg_neg
- \+/\- *lemma* dist_sub_left
- \+/\- *lemma* dist_sub_right
- \+/\- *lemma* norm_add_le
- \+/\- *lemma* norm_add_le_of_le
- \+/\- *lemma* dist_add_add_le
- \+/\- *lemma* dist_add_add_le_of_le
- \+/\- *lemma* dist_sub_sub_le
- \+/\- *lemma* dist_sub_sub_le_of_le
- \+/\- *lemma* abs_dist_sub_le_dist_add_add
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* norm_zero
- \+/\- *lemma* norm_of_subsingleton
- \+/\- *lemma* norm_sum_le
- \+/\- *lemma* norm_sum_le_of_le
- \+/\- *lemma* dist_sum_sum_le_of_le
- \+/\- *lemma* dist_sum_sum_le
- \+/\- *lemma* norm_sub_le
- \+/\- *lemma* norm_sub_le_of_le
- \+/\- *lemma* dist_le_norm_add_norm
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* norm_sub_norm_le
- \+/\- *lemma* dist_norm_norm_le
- \+/\- *lemma* norm_le_insert
- \+/\- *lemma* norm_le_insert'
- \+/\- *lemma* ball_zero_eq
- \+/\- *lemma* mem_ball_iff_norm
- \+/\- *lemma* add_mem_ball_iff_norm
- \+/\- *lemma* mem_ball_iff_norm'
- \+/\- *lemma* mem_ball_zero_iff
- \+/\- *lemma* mem_closed_ball_iff_norm
- \+/\- *lemma* add_mem_closed_ball_iff_norm
- \+/\- *lemma* mem_closed_ball_iff_norm'
- \+/\- *lemma* norm_le_of_mem_closed_ball
- \+/\- *lemma* norm_le_norm_add_const_of_dist_le
- \+/\- *lemma* norm_lt_of_mem_ball
- \+/\- *lemma* norm_lt_norm_add_const_of_dist_lt
- \+/\- *lemma* bounded_iff_forall_norm_le
- \+/\- *lemma* preimage_add_ball
- \+/\- *lemma* preimage_add_closed_ball
- \+/\- *lemma* mem_sphere_iff_norm
- \+/\- *lemma* mem_sphere_zero_iff_norm
- \+/\- *lemma* norm_eq_of_mem_sphere
- \+/\- *lemma* preimage_add_sphere
- \+/\- *lemma* ne_zero_of_norm_pos
- \+/\- *lemma* nonzero_of_mem_sphere
- \+/\- *lemma* nonzero_of_mem_unit_sphere
- \+/\- *lemma* coe_neg_sphere
- \+/\- *lemma* add_right_to_equiv
- \+/\- *lemma* coe_add_right
- \+/\- *lemma* add_right_apply
- \+/\- *lemma* add_right_symm
- \+/\- *lemma* add_left_to_equiv
- \+/\- *lemma* coe_add_left
- \+/\- *lemma* add_left_symm
- \+/\- *lemma* neg_symm
- \+/\- *lemma* neg_to_equiv
- \+/\- *lemma* coe_neg
- \+/\- *lemma* normed_group.tendsto_nhds_nhds
- \+/\- *lemma* normed_group.cauchy_seq_iff
- \+/\- *lemma* cauchy_seq.add
- \+/\- *lemma* cauchy_seq_sum_of_eventually_eq
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound
- \+/\- *lemma* lipschitz_on_with_iff_norm_sub_le
- \+/\- *lemma* lipschitz_on_with.norm_sub_le
- \+/\- *lemma* lipschitz_with_iff_norm_sub_le
- \+/\- *lemma* add_monoid_hom.continuous_of_bound
- \+/\- *lemma* is_compact.exists_bound_of_continuous_on
- \+/\- *lemma* add_monoid_hom.isometry_iff_norm
- \+/\- *lemma* add_monoid_hom.isometry_of_norm
- \+/\- *lemma* controlled_sum_of_mem_closure
- \+/\- *lemma* controlled_sum_of_mem_closure_range
- \+/\- *lemma* coe_nnnorm
- \+/\- *lemma* nndist_eq_nnnorm
- \+/\- *lemma* nnnorm_zero
- \+/\- *lemma* nnnorm_add_le
- \+/\- *lemma* nnnorm_neg
- \+/\- *lemma* nndist_nnnorm_nnnorm_le
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* mem_emetric_ball_zero_iff
- \+/\- *lemma* nndist_add_add_le
- \+/\- *lemma* edist_add_add_le
- \+/\- *lemma* nnnorm_sum_le
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+ *lemma* neg
- \+ *lemma* add
- \+ *lemma* sub
- \+ *lemma* add_lipschitz_with
- \+ *lemma* add_sub_lipschitz_with
- \+/\- *lemma* prod.semi_norm_def
- \+/\- *lemma* prod.nnsemi_norm_def
- \+/\- *lemma* semi_norm_fst_le
- \+/\- *lemma* semi_norm_snd_le
- \+/\- *lemma* semi_norm_prod_le_iff
- \+/\- *lemma* pi_semi_norm_const
- \+/\- *lemma* pi_nnsemi_norm_const
- \+/\- *lemma* tendsto_iff_norm_tendsto_zero
- \+/\- *lemma* is_bounded_under_of_tendsto
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+/\- *lemma* squeeze_zero_norm'
- \+/\- *lemma* squeeze_zero_norm
- \+/\- *lemma* tendsto_norm_sub_self
- \+/\- *lemma* tendsto_norm
- \+/\- *lemma* tendsto_norm_zero
- \+/\- *lemma* continuous_norm
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* lipschitz_with_one_norm
- \+/\- *lemma* uniform_continuous_norm
- \+/\- *lemma* uniform_continuous_nnnorm
- \+/\- *lemma* filter.tendsto.norm
- \+/\- *lemma* eventually_ne_of_tendsto_norm_at_top
- \+/\- *lemma* nat.norm_cast_le
- \+/\- *lemma* semi_normed_group.mem_closure_iff
- \+/\- *lemma* norm_le_zero_iff'
- \+/\- *lemma* norm_eq_zero_iff'
- \+/\- *lemma* norm_pos_iff'
- \+/\- *lemma* normed_group.core.to_semi_normed_group.core
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* eq_of_norm_sub_le_zero
- \+/\- *lemma* eq_of_norm_sub_eq_zero
- \+/\- *lemma* norm_sub_eq_zero_iff
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* prod.norm_def
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* norm_fst_le
- \+/\- *lemma* norm_snd_le
- \+/\- *lemma* norm_prod_le_iff
- \+/\- *lemma* pi_norm_const
- \+/\- *lemma* pi_nnnorm_const
- \+/\- *lemma* tendsto_norm_nhds_within_zero
- \+/\- *lemma* dist_eq_norm
- \+/\- *lemma* dist_eq_norm'
- \+/\- *lemma* dist_zero_right
- \+/\- *lemma* dist_zero_left
- \+/\- *lemma* tendsto_norm_cocompact_at_top
- \+/\- *lemma* norm_sub_rev
- \+/\- *lemma* norm_neg
- \+/\- *lemma* dist_add_left
- \+/\- *lemma* dist_add_right
- \+/\- *lemma* dist_neg_neg
- \+/\- *lemma* dist_sub_left
- \+/\- *lemma* dist_sub_right
- \+/\- *lemma* norm_add_le
- \+/\- *lemma* norm_add_le_of_le
- \+/\- *lemma* dist_add_add_le
- \+/\- *lemma* dist_add_add_le_of_le
- \+/\- *lemma* dist_sub_sub_le
- \+/\- *lemma* dist_sub_sub_le_of_le
- \+/\- *lemma* abs_dist_sub_le_dist_add_add
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* norm_zero
- \+/\- *lemma* norm_of_subsingleton
- \+/\- *lemma* norm_sum_le
- \+/\- *lemma* norm_sum_le_of_le
- \+/\- *lemma* dist_sum_sum_le_of_le
- \+/\- *lemma* dist_sum_sum_le
- \+/\- *lemma* norm_sub_le
- \+/\- *lemma* norm_sub_le_of_le
- \+/\- *lemma* dist_le_norm_add_norm
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* norm_sub_norm_le
- \+/\- *lemma* dist_norm_norm_le
- \+/\- *lemma* norm_le_insert
- \+/\- *lemma* norm_le_insert'
- \+/\- *lemma* ball_zero_eq
- \+/\- *lemma* mem_ball_iff_norm
- \+/\- *lemma* add_mem_ball_iff_norm
- \+/\- *lemma* mem_ball_iff_norm'
- \+/\- *lemma* mem_ball_zero_iff
- \+/\- *lemma* mem_closed_ball_iff_norm
- \+/\- *lemma* add_mem_closed_ball_iff_norm
- \+/\- *lemma* mem_closed_ball_iff_norm'
- \+/\- *lemma* norm_le_of_mem_closed_ball
- \+/\- *lemma* norm_le_norm_add_const_of_dist_le
- \+/\- *lemma* norm_lt_of_mem_ball
- \+/\- *lemma* norm_lt_norm_add_const_of_dist_lt
- \+/\- *lemma* bounded_iff_forall_norm_le
- \+/\- *lemma* preimage_add_ball
- \+/\- *lemma* preimage_add_closed_ball
- \+/\- *lemma* mem_sphere_iff_norm
- \+/\- *lemma* mem_sphere_zero_iff_norm
- \+/\- *lemma* norm_eq_of_mem_sphere
- \+/\- *lemma* preimage_add_sphere
- \+/\- *lemma* ne_zero_of_norm_pos
- \+/\- *lemma* nonzero_of_mem_sphere
- \+/\- *lemma* nonzero_of_mem_unit_sphere
- \+/\- *lemma* coe_neg_sphere
- \+/\- *lemma* add_right_to_equiv
- \+/\- *lemma* coe_add_right
- \+/\- *lemma* add_right_apply
- \+/\- *lemma* add_right_symm
- \+/\- *lemma* add_left_to_equiv
- \+/\- *lemma* coe_add_left
- \+/\- *lemma* add_left_symm
- \+/\- *lemma* neg_symm
- \+/\- *lemma* neg_to_equiv
- \+/\- *lemma* coe_neg
- \+/\- *lemma* normed_group.tendsto_nhds_nhds
- \+/\- *lemma* normed_group.cauchy_seq_iff
- \+/\- *lemma* cauchy_seq.add
- \+/\- *lemma* cauchy_seq_sum_of_eventually_eq
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound
- \+/\- *lemma* lipschitz_on_with_iff_norm_sub_le
- \+/\- *lemma* lipschitz_on_with.norm_sub_le
- \+/\- *lemma* lipschitz_with_iff_norm_sub_le
- \+/\- *lemma* add_monoid_hom.continuous_of_bound
- \+/\- *lemma* is_compact.exists_bound_of_continuous_on
- \+/\- *lemma* add_monoid_hom.isometry_iff_norm
- \+/\- *lemma* add_monoid_hom.isometry_of_norm
- \+/\- *lemma* controlled_sum_of_mem_closure
- \+/\- *lemma* controlled_sum_of_mem_closure_range
- \+/\- *lemma* coe_nnnorm
- \+/\- *lemma* nndist_eq_nnnorm
- \+/\- *lemma* nnnorm_zero
- \+/\- *lemma* nnnorm_add_le
- \+/\- *lemma* nnnorm_neg
- \+/\- *lemma* nndist_nnnorm_nnnorm_le
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* mem_emetric_ball_zero_iff
- \+/\- *lemma* nndist_add_add_le
- \+/\- *lemma* edist_add_add_le
- \+/\- *lemma* nnnorm_sum_le
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \- *lemma* lipschitz_with.neg
- \- *lemma* lipschitz_with.add
- \- *lemma* lipschitz_with.sub
- \- *lemma* antilipschitz_with.add_lipschitz_with
- \- *lemma* antilipschitz_with.add_sub_lipschitz_with
- \+/\- *lemma* prod.semi_norm_def
- \+/\- *lemma* prod.nnsemi_norm_def
- \+/\- *lemma* semi_norm_fst_le
- \+/\- *lemma* semi_norm_snd_le
- \+/\- *lemma* semi_norm_prod_le_iff
- \+/\- *lemma* pi_semi_norm_const
- \+/\- *lemma* pi_nnsemi_norm_const
- \+/\- *lemma* tendsto_iff_norm_tendsto_zero
- \+/\- *lemma* is_bounded_under_of_tendsto
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+/\- *lemma* squeeze_zero_norm'
- \+/\- *lemma* squeeze_zero_norm
- \+/\- *lemma* tendsto_norm_sub_self
- \+/\- *lemma* tendsto_norm
- \+/\- *lemma* tendsto_norm_zero
- \+/\- *lemma* continuous_norm
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* lipschitz_with_one_norm
- \+/\- *lemma* uniform_continuous_norm
- \+/\- *lemma* uniform_continuous_nnnorm
- \+/\- *lemma* filter.tendsto.norm
- \+/\- *lemma* eventually_ne_of_tendsto_norm_at_top
- \+/\- *lemma* nat.norm_cast_le
- \+/\- *lemma* semi_normed_group.mem_closure_iff
- \+/\- *lemma* norm_le_zero_iff'
- \+/\- *lemma* norm_eq_zero_iff'
- \+/\- *lemma* norm_pos_iff'
- \+/\- *lemma* normed_group.core.to_semi_normed_group.core
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* eq_of_norm_sub_le_zero
- \+/\- *lemma* eq_of_norm_sub_eq_zero
- \+/\- *lemma* norm_sub_eq_zero_iff
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* prod.norm_def
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* norm_fst_le
- \+/\- *lemma* norm_snd_le
- \+/\- *lemma* norm_prod_le_iff
- \+/\- *lemma* pi_norm_const
- \+/\- *lemma* pi_nnnorm_const
- \+/\- *lemma* tendsto_norm_nhds_within_zero
- \+/\- *theorem* normed_group.tendsto_nhds_zero
- \+/\- *theorem* normed_group.tendsto_nhds_zero
- \+/\- *def* semi_normed_group.of_add_dist
- \+/\- *def* semi_normed_group.of_add_dist'
- \+/\- *def* semi_normed_group.induced
- \+/\- *def* normed_group.of_add_dist
- \+/\- *def* normed_group.induced
- \+/\- *def* semi_normed_group.of_add_dist
- \+/\- *def* semi_normed_group.of_add_dist'
- \+/\- *def* semi_normed_group.induced
- \+/\- *def* normed_group.of_add_dist
- \+/\- *def* normed_group.induced

modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.edist_lt_top
- \+ *lemma* antilipschitz_with.edist_ne_top

modified src/topology/metric_space/basic.lean
- \+/\- *def* pseudo_emetric_space.to_pseudo_metric_space
- \+/\- *def* pseudo_emetric_space.to_pseudo_metric_space



## [2021-10-11 04:03:51](https://github.com/leanprover-community/mathlib/commit/11117ec)
feat(topology/G_delta): a finite set is a Gδ-set ([#9644](https://github.com/leanprover-community/mathlib/pull/9644))
#### Estimated changes
modified src/topology/G_delta.lean
- \+ *lemma* is_Gδ_empty
- \+ *lemma* is_Gδ_singleton
- \+ *lemma* set.finite.is_Gδ

modified src/topology/separation.lean
- \+ *lemma* bInter_basis_nhds



## [2021-10-11 04:03:50](https://github.com/leanprover-community/mathlib/commit/c02a655)
feat(linear_algebra/affine_space/barycentric_coords): we can recover a point from its barycentric coordinates ([#9629](https://github.com/leanprover-community/mathlib/pull/9629))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* sum_barycentric_coord_apply_eq_one
- \+ *lemma* affine_combination_barycentric_coord_eq_self

modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* eq_affine_combination_of_mem_affine_span_of_fintype



## [2021-10-11 04:03:49](https://github.com/leanprover-community/mathlib/commit/0bd14ba)
feat(category_theory/limits/lattice): Add explicit formulas for limits in lattices ([#9608](https://github.com/leanprover-community/mathlib/pull/9608))
Add explicit descriptions of finite limits and colimits in complete lattices. In particular, the product and the pullback is equal to the infimum, while coproduct and pushout is the supremum. Furthermore, `limit_iso_infi` can be strengthened to an equality, as preorder categories are skeletal.
#### Estimated changes
modified src/category_theory/limits/lattice.lean
- \+ *lemma* finite_limit_eq_finset_univ_inf
- \+ *lemma* finite_colimit_eq_finset_univ_sup
- \+ *lemma* finite_product_eq_finset_inf
- \+ *lemma* finite_coproduct_eq_finset_sup
- \+ *lemma* prod_eq_inf
- \+ *lemma* coprod_eq_sup
- \+ *lemma* pullback_eq_inf
- \+ *lemma* pushout_eq_sup
- \+ *lemma* limit_eq_infi
- \+ *lemma* colimit_eq_supr
- \- *lemma* limit_iso_infi_hom
- \- *lemma* limit_iso_infi_inv
- \- *lemma* colimit_iso_supr_hom
- \- *lemma* colimit_iso_supr_inv
- \+ *def* finite_limit_cone
- \+ *def* finite_colimit_cocone
- \+/\- *def* limit_cone
- \+/\- *def* colimit_cocone
- \+/\- *def* limit_cone
- \+/\- *def* colimit_cocone
- \- *def* limit_iso_infi
- \- *def* colimit_iso_supr



## [2021-10-11 04:03:48](https://github.com/leanprover-community/mathlib/commit/c803c8d)
feat(algebra/gcd_monoid): trivial `gcd` on `comm_group_with_zero`s ([#9602](https://github.com/leanprover-community/mathlib/pull/9602))
This PR extends the `normalization_monoid` defined on `comm_group_with_zero`s (e.g. fields) to a `normalized_gcd_monoid`. This is useful if you need to take the gcd of two polynomials in a field.
#### Estimated changes
modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* coe_norm_unit
- \+ *lemma* normalize_eq_one
- \+/\- *lemma* coe_norm_unit

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* ufm_of_gcd_of_wf_dvd_monoid



## [2021-10-11 04:03:47](https://github.com/leanprover-community/mathlib/commit/ec5835d)
chore(order/*): use to_dual and of_dual in statements instead of implicit coercions between and `α` and  `order_dual α`  ([#9593](https://github.com/leanprover-community/mathlib/pull/9593))
Previously the meaning of the statement was hidden away in an invisible surprising typeclass argument.
Before this change, the docs suggested the nonsensical statement that `monotone f` implies `antitone f`!
![image](https://user-images.githubusercontent.com/425260/136348562-d3ecbb85-2a54-4c13-adda-806eb150b00a.png)
Most of the proof changes in this PR are a consequence of changing the interval lemmas, not the monotonicity or convexity ones.
#### Estimated changes
modified src/analysis/convex/function.lean
- \+/\- *lemma* convex_on.dual
- \+/\- *lemma* concave_on.dual
- \+/\- *lemma* strict_convex_on.dual
- \+/\- *lemma* strict_concave_on.dual
- \+/\- *lemma* convex_on.dual
- \+/\- *lemma* concave_on.dual
- \+/\- *lemma* strict_convex_on.dual
- \+/\- *lemma* strict_concave_on.dual

modified src/data/set/intervals/basic.lean
- \+/\- *lemma* dual_Ici
- \+/\- *lemma* dual_Iic
- \+/\- *lemma* dual_Ioi
- \+/\- *lemma* dual_Iio
- \+/\- *lemma* dual_Icc
- \+/\- *lemma* dual_Ioc
- \+/\- *lemma* dual_Ico
- \+/\- *lemma* dual_Ioo
- \+/\- *lemma* dual_Ici
- \+/\- *lemma* dual_Iic
- \+/\- *lemma* dual_Ioi
- \+/\- *lemma* dual_Iio
- \+/\- *lemma* dual_Icc
- \+/\- *lemma* dual_Ioc
- \+/\- *lemma* dual_Ico
- \+/\- *lemma* dual_Ioo

modified src/data/set/intervals/disjoint.lean

modified src/data/set/intervals/ord_connected.lean
- \+/\- *lemma* ord_connected.dual
- \+/\- *lemma* ord_connected_dual
- \+/\- *lemma* ord_connected.dual
- \+/\- *lemma* ord_connected_dual

modified src/data/set/intervals/surj_on.lean

modified src/order/bounded_lattice.lean
- \+/\- *lemma* to_order_dual
- \+/\- *lemma* to_order_dual

modified src/order/bounds.lean

modified src/order/filter/extr.lean
- \+/\- *lemma* is_min_filter_dual_iff
- \+/\- *lemma* is_max_filter_dual_iff
- \+/\- *lemma* is_extr_filter_dual_iff
- \+/\- *lemma* is_min_on_dual_iff
- \+/\- *lemma* is_max_on_dual_iff
- \+/\- *lemma* is_extr_on_dual_iff
- \+/\- *lemma* is_min_filter_dual_iff
- \+/\- *lemma* is_max_filter_dual_iff
- \+/\- *lemma* is_extr_filter_dual_iff
- \+/\- *lemma* is_min_on_dual_iff
- \+/\- *lemma* is_max_on_dual_iff
- \+/\- *lemma* is_extr_on_dual_iff

modified src/order/monotone.lean

modified src/order/order_dual.lean

modified src/set_theory/zfc.lean

modified src/topology/algebra/ordered/basic.lean

modified src/topology/opens.lean
- \+/\- *def* gi
- \+/\- *def* gi

modified src/topology/subset_properties.lean



## [2021-10-11 04:03:45](https://github.com/leanprover-community/mathlib/commit/ef46da8)
feat(category_theory/*): Curried yoneda lemma ([#9579](https://github.com/leanprover-community/mathlib/pull/9579))
Provided curried versions of the Yoneda lemma when the category is small.
#### Estimated changes
modified src/category_theory/closed/cartesian.lean

modified src/category_theory/closed/functor.lean

modified src/category_theory/closed/ideal.lean

modified src/category_theory/types.lean
- \+ *def* ulift_functor_trivial

modified src/category_theory/yoneda.lean
- \+ *def* curried_yoneda_lemma
- \+ *def* curried_yoneda_lemma'



## [2021-10-11 02:26:38](https://github.com/leanprover-community/mathlib/commit/e32154d)
feat(data/equiv/ring): add basic API lemmas for ring_equiv ([#9639](https://github.com/leanprover-community/mathlib/pull/9639))
This PR adds the lemmas `map_inv`, `map_div`, `map_pow` and `map_fpow` for `ring_equiv`. These lemmas were already available for `ring_hom`s. I'm very open to suggestions about where they should go; `map_fpow` in particular requires a new import in `algebra/field_power.lean`.
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* ring_equiv.map_fpow

modified src/data/equiv/ring.lean
- \+ *lemma* map_inv
- \+ *lemma* map_div
- \+ *lemma* map_pow



## [2021-10-10 21:07:28](https://github.com/leanprover-community/mathlib/commit/64255e2)
chore(analysis): move some code to `analysis.normed.group.basic` ([#9642](https://github.com/leanprover-community/mathlib/pull/9642))
#### Estimated changes
created src/analysis/normed/group/basic.lean
- \+ *lemma* punit.norm_eq_zero
- \+ *lemma* real.norm_eq_abs
- \+ *lemma* dist_eq_norm
- \+ *lemma* dist_eq_norm'
- \+ *lemma* dist_zero_right
- \+ *lemma* dist_zero_left
- \+ *lemma* tendsto_norm_cocompact_at_top
- \+ *lemma* norm_sub_rev
- \+ *lemma* norm_neg
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
- \+ *lemma* abs_dist_sub_le_dist_add_add
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_zero
- \+ *lemma* norm_of_subsingleton
- \+ *lemma* norm_sum_le
- \+ *lemma* norm_sum_le_of_le
- \+ *lemma* dist_sum_sum_le_of_le
- \+ *lemma* dist_sum_sum_le
- \+ *lemma* norm_sub_le
- \+ *lemma* norm_sub_le_of_le
- \+ *lemma* dist_le_norm_add_norm
- \+ *lemma* abs_norm_sub_norm_le
- \+ *lemma* norm_sub_norm_le
- \+ *lemma* dist_norm_norm_le
- \+ *lemma* norm_le_insert
- \+ *lemma* norm_le_insert'
- \+ *lemma* ball_zero_eq
- \+ *lemma* mem_ball_iff_norm
- \+ *lemma* add_mem_ball_iff_norm
- \+ *lemma* mem_ball_iff_norm'
- \+ *lemma* mem_ball_zero_iff
- \+ *lemma* mem_closed_ball_iff_norm
- \+ *lemma* add_mem_closed_ball_iff_norm
- \+ *lemma* mem_closed_ball_iff_norm'
- \+ *lemma* norm_le_of_mem_closed_ball
- \+ *lemma* norm_le_norm_add_const_of_dist_le
- \+ *lemma* norm_lt_of_mem_ball
- \+ *lemma* norm_lt_norm_add_const_of_dist_lt
- \+ *lemma* bounded_iff_forall_norm_le
- \+ *lemma* preimage_add_ball
- \+ *lemma* preimage_add_closed_ball
- \+ *lemma* mem_sphere_iff_norm
- \+ *lemma* mem_sphere_zero_iff_norm
- \+ *lemma* norm_eq_of_mem_sphere
- \+ *lemma* preimage_add_sphere
- \+ *lemma* ne_zero_of_norm_pos
- \+ *lemma* nonzero_of_mem_sphere
- \+ *lemma* nonzero_of_mem_unit_sphere
- \+ *lemma* coe_neg_sphere
- \+ *lemma* add_right_to_equiv
- \+ *lemma* coe_add_right
- \+ *lemma* add_right_apply
- \+ *lemma* add_right_symm
- \+ *lemma* add_left_to_equiv
- \+ *lemma* coe_add_left
- \+ *lemma* add_left_symm
- \+ *lemma* neg_symm
- \+ *lemma* neg_to_equiv
- \+ *lemma* coe_neg
- \+ *lemma* normed_group.tendsto_nhds_nhds
- \+ *lemma* normed_group.cauchy_seq_iff
- \+ *lemma* cauchy_seq.add
- \+ *lemma* cauchy_seq_sum_of_eventually_eq
- \+ *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* lipschitz_on_with_iff_norm_sub_le
- \+ *lemma* lipschitz_on_with.norm_sub_le
- \+ *lemma* lipschitz_with_iff_norm_sub_le
- \+ *lemma* add_monoid_hom.continuous_of_bound
- \+ *lemma* is_compact.exists_bound_of_continuous_on
- \+ *lemma* add_monoid_hom.isometry_iff_norm
- \+ *lemma* add_monoid_hom.isometry_of_norm
- \+ *lemma* controlled_sum_of_mem_closure
- \+ *lemma* controlled_sum_of_mem_closure_range
- \+ *lemma* coe_nnnorm
- \+ *lemma* nndist_eq_nnnorm
- \+ *lemma* nnnorm_zero
- \+ *lemma* nnnorm_add_le
- \+ *lemma* nnnorm_neg
- \+ *lemma* nndist_nnnorm_nnnorm_le
- \+ *lemma* of_real_norm_eq_coe_nnnorm
- \+ *lemma* edist_eq_coe_nnnorm_sub
- \+ *lemma* edist_eq_coe_nnnorm
- \+ *lemma* mem_emetric_ball_zero_iff
- \+ *lemma* nndist_add_add_le
- \+ *lemma* edist_add_add_le
- \+ *lemma* nnnorm_sum_le
- \+ *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+ *lemma* lipschitz_with.neg
- \+ *lemma* lipschitz_with.add
- \+ *lemma* lipschitz_with.sub
- \+ *lemma* antilipschitz_with.add_lipschitz_with
- \+ *lemma* antilipschitz_with.add_sub_lipschitz_with
- \+ *lemma* coe_norm_subgroup
- \+ *lemma* submodule.norm_coe
- \+ *lemma* submodule.norm_mk
- \+ *lemma* prod.semi_norm_def
- \+ *lemma* prod.nnsemi_norm_def
- \+ *lemma* semi_norm_fst_le
- \+ *lemma* semi_norm_snd_le
- \+ *lemma* semi_norm_prod_le_iff
- \+ *lemma* pi_semi_norm_le_iff
- \+ *lemma* pi_semi_norm_lt_iff
- \+ *lemma* semi_norm_le_pi_norm
- \+ *lemma* pi_semi_norm_const
- \+ *lemma* pi_nnsemi_norm_const
- \+ *lemma* tendsto_iff_norm_tendsto_zero
- \+ *lemma* is_bounded_under_of_tendsto
- \+ *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+ *lemma* squeeze_zero_norm'
- \+ *lemma* squeeze_zero_norm
- \+ *lemma* tendsto_norm_sub_self
- \+ *lemma* tendsto_norm
- \+ *lemma* tendsto_norm_zero
- \+ *lemma* continuous_norm
- \+ *lemma* continuous_nnnorm
- \+ *lemma* lipschitz_with_one_norm
- \+ *lemma* uniform_continuous_norm
- \+ *lemma* uniform_continuous_nnnorm
- \+ *lemma* filter.tendsto.norm
- \+ *lemma* filter.tendsto.nnnorm
- \+ *lemma* continuous.norm
- \+ *lemma* continuous.nnnorm
- \+ *lemma* continuous_at.norm
- \+ *lemma* continuous_at.nnnorm
- \+ *lemma* continuous_within_at.norm
- \+ *lemma* continuous_within_at.nnnorm
- \+ *lemma* continuous_on.norm
- \+ *lemma* continuous_on.nnnorm
- \+ *lemma* eventually_ne_of_tendsto_norm_at_top
- \+ *lemma* nat.norm_cast_le
- \+ *lemma* semi_normed_group.mem_closure_iff
- \+ *lemma* norm_le_zero_iff'
- \+ *lemma* norm_eq_zero_iff'
- \+ *lemma* norm_pos_iff'
- \+ *lemma* normed_group.core.to_semi_normed_group.core
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_pos_iff
- \+ *lemma* norm_le_zero_iff
- \+ *lemma* eq_of_norm_sub_le_zero
- \+ *lemma* eq_of_norm_sub_eq_zero
- \+ *lemma* norm_sub_eq_zero_iff
- \+ *lemma* nnnorm_eq_zero
- \+ *lemma* prod.norm_def
- \+ *lemma* prod.nnnorm_def
- \+ *lemma* norm_fst_le
- \+ *lemma* norm_snd_le
- \+ *lemma* norm_prod_le_iff
- \+ *lemma* pi_norm_le_iff
- \+ *lemma* pi_norm_lt_iff
- \+ *lemma* norm_le_pi_norm
- \+ *lemma* pi_norm_const
- \+ *lemma* pi_nnnorm_const
- \+ *lemma* tendsto_norm_nhds_within_zero
- \+ *theorem* normed_group.tendsto_nhds_zero
- \+ *def* semi_normed_group.of_add_dist
- \+ *def* semi_normed_group.of_add_dist'
- \+ *def* semi_normed_group.induced
- \+ *def* normed_group.of_add_dist
- \+ *def* normed_group.induced

modified src/analysis/normed_space/basic.lean
- \- *lemma* punit.norm_eq_zero
- \- *lemma* real.norm_eq_abs
- \- *lemma* dist_eq_norm
- \- *lemma* dist_eq_norm'
- \- *lemma* dist_zero_right
- \- *lemma* dist_zero_left
- \- *lemma* tendsto_norm_cocompact_at_top
- \- *lemma* norm_sub_rev
- \- *lemma* norm_neg
- \- *lemma* dist_add_left
- \- *lemma* dist_add_right
- \- *lemma* dist_neg_neg
- \- *lemma* dist_sub_left
- \- *lemma* dist_sub_right
- \- *lemma* norm_add_le
- \- *lemma* norm_add_le_of_le
- \- *lemma* dist_add_add_le
- \- *lemma* dist_add_add_le_of_le
- \- *lemma* dist_sub_sub_le
- \- *lemma* dist_sub_sub_le_of_le
- \- *lemma* abs_dist_sub_le_dist_add_add
- \- *lemma* norm_nonneg
- \- *lemma* norm_zero
- \- *lemma* norm_of_subsingleton
- \- *lemma* norm_sum_le
- \- *lemma* norm_sum_le_of_le
- \- *lemma* dist_sum_sum_le_of_le
- \- *lemma* dist_sum_sum_le
- \- *lemma* norm_sub_le
- \- *lemma* norm_sub_le_of_le
- \- *lemma* dist_le_norm_add_norm
- \- *lemma* abs_norm_sub_norm_le
- \- *lemma* norm_sub_norm_le
- \- *lemma* dist_norm_norm_le
- \- *lemma* norm_le_insert
- \- *lemma* norm_le_insert'
- \- *lemma* ball_zero_eq
- \- *lemma* mem_ball_iff_norm
- \- *lemma* add_mem_ball_iff_norm
- \- *lemma* mem_ball_iff_norm'
- \- *lemma* mem_ball_zero_iff
- \- *lemma* mem_closed_ball_iff_norm
- \- *lemma* add_mem_closed_ball_iff_norm
- \- *lemma* mem_closed_ball_iff_norm'
- \- *lemma* norm_le_of_mem_closed_ball
- \- *lemma* norm_le_norm_add_const_of_dist_le
- \- *lemma* norm_lt_of_mem_ball
- \- *lemma* norm_lt_norm_add_const_of_dist_lt
- \- *lemma* bounded_iff_forall_norm_le
- \- *lemma* preimage_add_ball
- \- *lemma* preimage_add_closed_ball
- \- *lemma* mem_sphere_iff_norm
- \- *lemma* mem_sphere_zero_iff_norm
- \- *lemma* norm_eq_of_mem_sphere
- \- *lemma* preimage_add_sphere
- \- *lemma* ne_zero_of_norm_pos
- \- *lemma* nonzero_of_mem_sphere
- \- *lemma* nonzero_of_mem_unit_sphere
- \- *lemma* coe_neg_sphere
- \- *lemma* add_right_to_equiv
- \- *lemma* coe_add_right
- \- *lemma* add_right_apply
- \- *lemma* add_right_symm
- \- *lemma* add_left_to_equiv
- \- *lemma* coe_add_left
- \- *lemma* add_left_symm
- \- *lemma* neg_symm
- \- *lemma* neg_to_equiv
- \- *lemma* coe_neg
- \- *lemma* normed_group.tendsto_nhds_nhds
- \- *lemma* normed_group.cauchy_seq_iff
- \- *lemma* cauchy_seq.add
- \- *lemma* cauchy_seq_sum_of_eventually_eq
- \- *lemma* add_monoid_hom.lipschitz_of_bound
- \- *lemma* lipschitz_on_with_iff_norm_sub_le
- \- *lemma* lipschitz_on_with.norm_sub_le
- \- *lemma* lipschitz_with_iff_norm_sub_le
- \- *lemma* add_monoid_hom.continuous_of_bound
- \- *lemma* is_compact.exists_bound_of_continuous_on
- \- *lemma* add_monoid_hom.isometry_iff_norm
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* controlled_sum_of_mem_closure
- \- *lemma* controlled_sum_of_mem_closure_range
- \- *lemma* coe_nnnorm
- \- *lemma* nndist_eq_nnnorm
- \- *lemma* nnnorm_zero
- \- *lemma* nnnorm_add_le
- \- *lemma* nnnorm_neg
- \- *lemma* nndist_nnnorm_nnnorm_le
- \- *lemma* of_real_norm_eq_coe_nnnorm
- \- *lemma* edist_eq_coe_nnnorm_sub
- \- *lemma* edist_eq_coe_nnnorm
- \- *lemma* mem_emetric_ball_zero_iff
- \- *lemma* nndist_add_add_le
- \- *lemma* edist_add_add_le
- \- *lemma* nnnorm_sum_le
- \- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \- *lemma* lipschitz_with.neg
- \- *lemma* lipschitz_with.add
- \- *lemma* lipschitz_with.sub
- \- *lemma* antilipschitz_with.add_lipschitz_with
- \- *lemma* antilipschitz_with.add_sub_lipschitz_with
- \- *lemma* coe_norm_subgroup
- \- *lemma* submodule.norm_coe
- \- *lemma* submodule.norm_mk
- \- *lemma* prod.semi_norm_def
- \- *lemma* prod.nnsemi_norm_def
- \- *lemma* semi_norm_fst_le
- \- *lemma* semi_norm_snd_le
- \- *lemma* semi_norm_prod_le_iff
- \- *lemma* pi_semi_norm_le_iff
- \- *lemma* pi_semi_norm_lt_iff
- \- *lemma* semi_norm_le_pi_norm
- \- *lemma* pi_semi_norm_const
- \- *lemma* pi_nnsemi_norm_const
- \- *lemma* tendsto_iff_norm_tendsto_zero
- \- *lemma* is_bounded_under_of_tendsto
- \- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \- *lemma* squeeze_zero_norm'
- \- *lemma* squeeze_zero_norm
- \- *lemma* tendsto_norm_sub_self
- \- *lemma* tendsto_norm
- \- *lemma* tendsto_norm_zero
- \- *lemma* continuous_norm
- \- *lemma* continuous_nnnorm
- \- *lemma* lipschitz_with_one_norm
- \- *lemma* uniform_continuous_norm
- \- *lemma* uniform_continuous_nnnorm
- \- *lemma* filter.tendsto.norm
- \- *lemma* filter.tendsto.nnnorm
- \- *lemma* continuous.norm
- \- *lemma* continuous.nnnorm
- \- *lemma* continuous_at.norm
- \- *lemma* continuous_at.nnnorm
- \- *lemma* continuous_within_at.norm
- \- *lemma* continuous_within_at.nnnorm
- \- *lemma* continuous_on.norm
- \- *lemma* continuous_on.nnnorm
- \- *lemma* eventually_ne_of_tendsto_norm_at_top
- \- *lemma* nat.norm_cast_le
- \- *lemma* semi_normed_group.mem_closure_iff
- \- *lemma* norm_le_zero_iff'
- \- *lemma* norm_eq_zero_iff'
- \- *lemma* norm_pos_iff'
- \- *lemma* normed_group.core.to_semi_normed_group.core
- \- *lemma* norm_eq_zero
- \- *lemma* norm_pos_iff
- \- *lemma* norm_le_zero_iff
- \- *lemma* eq_of_norm_sub_le_zero
- \- *lemma* eq_of_norm_sub_eq_zero
- \- *lemma* norm_sub_eq_zero_iff
- \- *lemma* nnnorm_eq_zero
- \- *lemma* prod.norm_def
- \- *lemma* prod.nnnorm_def
- \- *lemma* norm_fst_le
- \- *lemma* norm_snd_le
- \- *lemma* norm_prod_le_iff
- \- *lemma* pi_norm_le_iff
- \- *lemma* pi_norm_lt_iff
- \- *lemma* norm_le_pi_norm
- \- *lemma* pi_norm_const
- \- *lemma* pi_nnnorm_const
- \- *lemma* tendsto_norm_nhds_within_zero
- \- *theorem* normed_group.tendsto_nhds_zero
- \- *def* semi_normed_group.of_add_dist
- \- *def* semi_normed_group.of_add_dist'
- \- *def* semi_normed_group.induced
- \- *def* normed_group.of_add_dist
- \- *def* normed_group.induced



## [2021-10-10 21:07:27](https://github.com/leanprover-community/mathlib/commit/fa41436)
feat(algebra/*,group_theory/*): instances/lemmas about `is_scalar_tower` and `smul_comm_class` ([#9533](https://github.com/leanprover-community/mathlib/pull/9533))
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/group/prod.lean
- \+ *lemma* mul_def

modified src/algebra/module/basic.lean

modified src/algebra/opposites.lean
- \+/\- *lemma* op_smul_eq_mul
- \+/\- *lemma* op_smul_eq_mul

modified src/group_theory/group_action/defs.lean
- \+ *lemma* smul_one_mul
- \+ *lemma* mul_smul_one
- \+ *lemma* is_scalar_tower.of_smul_one_mul
- \+ *lemma* smul_comm_class.of_mul_smul_one

modified src/group_theory/group_action/prod.lean
- \+ *theorem* smul_def



## [2021-10-10 18:58:39](https://github.com/leanprover-community/mathlib/commit/0bba837)
chore(data/nat/factorial): use `n + 1` instead of `n.succ` in `nat.factorial_succ` ([#9645](https://github.com/leanprover-community/mathlib/pull/9645))
#### Estimated changes
modified src/data/nat/choose/basic.lean

modified src/data/nat/factorial/basic.lean
- \+/\- *theorem* factorial_succ
- \+/\- *theorem* factorial_succ

modified src/number_theory/liouville/liouville_constant.lean



## [2021-10-10 09:54:18](https://github.com/leanprover-community/mathlib/commit/3d438ba)
feat(probability_theory/density): add continuous uniform distribution ([#9385](https://github.com/leanprover-community/mathlib/pull/9385))
#### Estimated changes
modified src/algebra/indicator_function.lean
- \+ *lemma* mul_indicator_eq_one_iff

modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* _root_.set.mul_indicator_ae_eq_one

modified src/probability_theory/density.lean
- \+ *lemma* has_pdf_of_pdf_ne_zero
- \+ *lemma* has_pdf
- \+ *lemma* pdf_to_real_ae_eq
- \+ *lemma* mul_pdf_integrable
- \+ *lemma* integral_eq
- \+ *def* is_uniform



## [2021-10-09 16:48:06](https://github.com/leanprover-community/mathlib/commit/54a4c17)
feat(group_theory/sylow): `set_like` instance for `sylow` ([#9641](https://github.com/leanprover-community/mathlib/pull/9641))
Adds a `set_like` instance for `sylow p G`.
Coauthored by @jcommelin
#### Estimated changes
modified src/group_theory/sylow.lean
- \+ *lemma* to_subgroup_eq_coe
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \- *lemma* sylow.to_subgroup_eq_coe
- \- *lemma* sylow.ext
- \- *lemma* sylow.ext_iff



## [2021-10-09 14:56:51](https://github.com/leanprover-community/mathlib/commit/bb98444)
refactor(group_theory/congruence): remove old_structure_cmd ([#9622](https://github.com/leanprover-community/mathlib/pull/9622))
#### Estimated changes
modified src/group_theory/congruence.lean
- \+/\- *lemma* rel_mk
- \+/\- *lemma* Inf_def
- \+/\- *lemma* Sup_def
- \+/\- *lemma* rel_mk
- \- *lemma* coe_eq
- \+/\- *lemma* Inf_def
- \+/\- *lemma* Sup_def
- \+/\- *theorem* con_gen_le
- \+/\- *theorem* con_gen_le



## [2021-10-09 09:53:15](https://github.com/leanprover-community/mathlib/commit/7ed091d)
feat(group_theory/perm/concrete_cycle): computable cyclic perm notation ([#9470](https://github.com/leanprover-community/mathlib/pull/9470))
#### Estimated changes
modified src/group_theory/perm/concrete_cycle.lean
- \+ *lemma* is_cycle.exists_unique_cycle_nontrivial_subtype
- \+ *lemma* to_cycle_eq_to_list
- \+ *lemma* nodup_to_cycle
- \+ *lemma* nontrivial_to_cycle
- \+ *def* to_cycle
- \+ *def* iso_cycle
- \+ *def* iso_cycle'



## [2021-10-09 07:26:30](https://github.com/leanprover-community/mathlib/commit/ce50450)
chore(analysis/normed_space/linear_isometry): adjust `isometry` API ([#9635](https://github.com/leanprover-community/mathlib/pull/9635))
Now that we have the `linear_isometry` definition, it is better to pass through this definition rather then using a `linear_map` satisfying the `isometry` hypothesis.  To this end, convert old lemma `linear_map.norm_apply_of_isometry` to a new definition `linear_map.to_linear_isometry`, and delete old definition `continuous_linear_equiv.of_isometry`, whose use should be replaced by the pair of definitions`linear_map.to_linear_isometry`, `linear_isometry_equiv.of_surjective`.
#### Estimated changes
modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* linear_map.norm_apply_of_isometry
- \- *def* continuous_linear_equiv.of_isometry

modified src/analysis/normed_space/linear_isometry.lean
- \+ *def* linear_map.to_linear_isometry

modified src/analysis/normed_space/operator_norm.lean



## [2021-10-09 07:26:28](https://github.com/leanprover-community/mathlib/commit/a9643aa)
feat(order/min_max): min_cases and max_cases lemmata ([#9632](https://github.com/leanprover-community/mathlib/pull/9632))
These lemmata make the following type of argument work seamlessly:
```lean
example (h1 : 0 ≤ x) (h2 : x ≤ 1) : min 1 x ≤ max x 0 := by cases min_cases 1 x; cases max_cases x 0; linarith
```
See similar PR [#8124](https://github.com/leanprover-community/mathlib/pull/8124)
#### Estimated changes
modified src/order/min_max.lean
- \+ *lemma* min_cases
- \+ *lemma* max_cases



## [2021-10-09 07:26:25](https://github.com/leanprover-community/mathlib/commit/e0f80e7)
feat(analysis/convex/quasiconvex): Quasiconvexity of functions ([#9561](https://github.com/leanprover-community/mathlib/pull/9561))
A function is quasiconvex iff all its sublevels are convex. This generalizes unimodality to non-ordered spaces.
#### Estimated changes
created src/analysis/convex/quasiconvex.lean
- \+ *lemma* quasiconvex_on.dual
- \+ *lemma* quasiconcave_on.dual
- \+ *lemma* quasilinear_on.dual
- \+ *lemma* convex.quasiconvex_on_of_convex_le
- \+ *lemma* convex.quasiconcave_on_of_convex_ge
- \+ *lemma* quasiconvex_on.convex
- \+ *lemma* quasiconcave_on.convex
- \+ *lemma* quasiconvex_on.sup
- \+ *lemma* quasiconcave_on.inf
- \+ *lemma* quasiconvex_on_iff_le_max
- \+ *lemma* quasiconcave_on_iff_min_le
- \+ *lemma* quasilinear_on_iff_mem_interval
- \+ *lemma* quasiconvex_on.convex_lt
- \+ *lemma* quasiconcave_on.convex_gt
- \+ *lemma* convex_on.quasiconvex_on
- \+ *lemma* concave_on.quasiconcave_on
- \+ *lemma* monotone_on.quasiconvex_on
- \+ *lemma* monotone_on.quasiconcave_on
- \+ *lemma* monotone_on.quasilinear_on
- \+ *lemma* antitone_on.quasiconvex_on
- \+ *lemma* antitone_on.quasiconcave_on
- \+ *lemma* antitone_on.quasilinear_on
- \+ *lemma* monotone.quasiconvex_on
- \+ *lemma* monotone.quasiconcave_on
- \+ *lemma* monotone.quasilinear_on
- \+ *lemma* antitone.quasiconvex_on
- \+ *lemma* antitone.quasiconcave_on
- \+ *lemma* antitone.quasilinear_on
- \+ *def* quasiconvex_on
- \+ *def* quasiconcave_on
- \+ *def* quasilinear_on

modified src/data/set/basic.lean
- \+ *lemma* sep_inter_sep



## [2021-10-09 04:58:07](https://github.com/leanprover-community/mathlib/commit/7a7fada)
refactor(data/nat/basic): finish removing sub lemmas ([#9601](https://github.com/leanprover-community/mathlib/pull/9601))
* Follow-up of [#9544](https://github.com/leanprover-community/mathlib/pull/9544) to remove the remaining sub lemmas on `nat` that can be generalized to `has_ordered_sub`.
* The renamings of the lemmas in mathlib that occurred at least once:
```
nat.sub_eq_of_eq_add -> sub_eq_of_eq_add_rev
nat.add_sub_sub_cancel -> add_sub_sub_cancel'
nat.sub_le_self -> sub_le_self'
```
#### Estimated changes
modified archive/oxford_invariants/2021summer/week3_p1.lean

modified src/algebra/order/sub.lean
- \+ *lemma* sub_eq_of_eq_add_rev

modified src/data/multiset/basic.lean

modified src/data/nat/basic.lean
- \- *lemma* add_sub_sub_cancel
- \- *theorem* sub_le_left_iff_le_add
- \- *theorem* sub_le_right_iff_le_add

modified src/data/nat/choose/basic.lean

modified src/data/nat/sqrt.lean

modified src/data/polynomial/hasse_deriv.lean

modified src/data/polynomial/ring_division.lean

modified src/order/jordan_holder.lean

modified src/ring_theory/witt_vector/frobenius.lean



## [2021-10-09 02:44:04](https://github.com/leanprover-community/mathlib/commit/7aaa1b4)
chore(scripts): update nolints.txt ([#9636](https://github.com/leanprover-community/mathlib/pull/9636))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-10-08 21:56:11](https://github.com/leanprover-community/mathlib/commit/7e3fa4c)
chore(*): fix typos ([#9634](https://github.com/leanprover-community/mathlib/pull/9634))
#### Estimated changes
modified archive/miu_language/basic.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/ring/prod.lean

modified src/analysis/calculus/lhopital.lean

modified src/analysis/inner_product_space/basic.lean

modified src/analysis/p_series.lean

modified src/analysis/special_functions/trigonometric/complex.lean
- \+/\- *lemma* differentiable_at_tan
- \+/\- *lemma* differentiable_at_tan

modified src/category_theory/limits/fubini.lean

modified src/combinatorics/pigeonhole.lean

modified src/computability/epsilon_NFA.lean

modified src/control/traversable/basic.lean

modified src/control/traversable/equiv.lean

modified src/data/buffer/parser/basic.lean

modified src/data/equiv/set.lean

modified src/data/finset/lattice.lean

modified src/data/finset/noncomm_prod.lean

modified src/data/list/zip.lean

modified src/data/matrix/pequiv.lean

modified src/data/polynomial/iterated_deriv.lean

modified src/data/real/ennreal.lean

modified src/data/set/lattice.lean

modified src/group_theory/order_of_element.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/measure/content.lean

modified src/number_theory/padics/padic_norm.lean

modified src/ring_theory/witt_vector/is_poly.lean

modified src/ring_theory/witt_vector/teichmuller.lean

modified src/ring_theory/witt_vector/verschiebung.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/set_theory/pgame.lean

modified src/tactic/congr.lean

modified src/tactic/core.lean

modified src/tactic/lean_core_docs.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered/basic.lean

modified src/topology/algebra/valued_field.lean

modified src/topology/metric_space/basic.lean

modified src/topology/sheaves/sheaf_of_functions.lean

modified src/topology/urysohns_lemma.lean



## [2021-10-08 21:06:41](https://github.com/leanprover-community/mathlib/commit/70a9540)
refactor(group_theory/monoid_localization) remove old_structure_cmd ([#9621](https://github.com/leanprover-community/mathlib/pull/9621))
#### Estimated changes
modified src/group_theory/monoid_localization.lean



## [2021-10-08 20:24:14](https://github.com/leanprover-community/mathlib/commit/c37e3e7)
refactor(field_theory/intermediate_field): remove old_structure_cmd ([#9620](https://github.com/leanprover-community/mathlib/pull/9620))
#### Estimated changes
modified src/field_theory/intermediate_field.lean
- \+ *def* to_subfield



## [2021-10-08 20:24:12](https://github.com/leanprover-community/mathlib/commit/b39feab)
refactor(algebra/lie): reduce use of old_structure_cmd ([#9616](https://github.com/leanprover-community/mathlib/pull/9616))
#### Estimated changes
modified src/algebra/lie/basic.lean
- \- *lemma* coe_linear_mk
- \+ *def* simps.apply
- \+ *def* to_linear_equiv

modified src/algebra/lie/semisimple.lean

modified src/algebra/lie/subalgebra.lean

modified src/algebra/lie/submodule.lean



## [2021-10-08 17:52:23](https://github.com/leanprover-community/mathlib/commit/91ee8f1)
chore(data/equiv/ring): add big operator lemmas for ring equivs ([#9628](https://github.com/leanprover-community/mathlib/pull/9628))
This PR adds lemmas involving big operators (such as `map_sum`, `map_prod`, etc) for `ring_equiv`s.
#### Estimated changes
modified src/data/equiv/ring.lean
- \+ *lemma* map_list_prod
- \+ *lemma* map_list_sum
- \+ *lemma* map_multiset_prod
- \+ *lemma* map_multiset_sum
- \+ *lemma* map_prod
- \+ *lemma* map_sum



## [2021-10-08 16:13:52](https://github.com/leanprover-community/mathlib/commit/57cd1e9)
feat(analysis/normed_space/exponential): remove char_p assumption ([#9618](https://github.com/leanprover-community/mathlib/pull/9618))
Remove the `char_p` assumption from `exp_series_eq_exp_series_of_field_extension` as suggested by @urkud here : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Undergraduate.20math.20list/near/256679511
#### Estimated changes
modified src/analysis/normed_space/exponential.lean



## [2021-10-08 14:22:17](https://github.com/leanprover-community/mathlib/commit/5fd3664)
feat(algebra/graded_monoid): Split out graded monoids from graded rings ([#9586](https://github.com/leanprover-community/mathlib/pull/9586))
This cleans up the `direct_sum.gmonoid` typeclass to not contain a bundled morphism, which allows it to be used to describe graded monoids too, via the alias for `sigma` `graded_monoid`. Essentially, this:
* Renames:
  * `direct_sum.ghas_one` to `graded_monoid.has_one`
  * `direct_sum.ghas_mul` to `direct_sum.gnon_unital_non_assoc_semiring`
  * `direct_sum.gmonoid` to `direct_sum.gsemiring`
  * `direct_sum.gcomm_monoid` to `direct_sum.gcomm_semiring`
* Introduces new typeclasses which represent what the previous names should have been:
  * `graded_monoid.ghas_mul`
  * `graded_monoid.gmonoid`
  * `graded_monoid.gcomm_monoid` 
This doesn't do as much deduplication as I'd like, but it at least manages some.
There's not much in the way of new definitions here either, and most of the names are just copied from the graded ring case.
#### Estimated changes
modified src/algebra/direct_sum/algebra.lean

modified src/algebra/direct_sum/ring.lean
- \- *lemma* ghas_mul.of_add_submonoids_mul
- \- *lemma* ghas_mul.of_add_subgroups_mul
- \- *lemma* ghas_mul.of_submodules_mul
- \- *lemma* grade_zero.smul_eq_mul
- \- *lemma* semiring.direct_sum_mul
- \+ *def* gsemiring.of_add_submonoids
- \+ *def* gcomm_semiring.of_add_submonoids
- \+ *def* gsemiring.of_add_subgroups
- \+ *def* gcomm_semiring.of_add_subgroups
- \+ *def* gsemiring.of_submodules
- \+ *def* gcomm_semiring.of_submodules
- \+ *def* gmul_hom
- \- *def* ghas_one.to_sigma_has_one
- \- *def* ghas_mul.to_sigma_has_mul
- \- *def* ghas_one.of_add_submonoids
- \- *def* ghas_mul.of_add_submonoids
- \- *def* gmonoid.of_add_submonoids
- \- *def* gcomm_monoid.of_add_submonoids
- \- *def* ghas_one.of_add_subgroups
- \- *def* ghas_mul.of_add_subgroups
- \- *def* gmonoid.of_add_subgroups
- \- *def* gcomm_monoid.of_add_subgroups
- \- *def* ghas_one.of_submodules
- \- *def* ghas_mul.of_submodules
- \- *def* gmonoid.of_submodules
- \- *def* gcomm_monoid.of_submodules

created src/algebra/graded_monoid.lean
- \+ *lemma* mk_mul_mk
- \+ *lemma* mk_zero_smul
- \+ *lemma* grade_zero.smul_eq_mul
- \+ *def* graded_monoid
- \+ *def* mk
- \+ *def* mk_zero_monoid_hom
- \+ *def* ghas_one.of_subobjects
- \+ *def* ghas_mul.of_subobjects
- \+ *def* gmonoid.of_subobjects
- \+ *def* gcomm_monoid.of_subobjects

modified src/algebra/monoid_algebra/grading.lean

modified src/algebra/monoid_algebra/to_direct_sum.lean

modified src/ring_theory/polynomial/homogeneous.lean



## [2021-10-08 14:22:16](https://github.com/leanprover-community/mathlib/commit/745cbfc)
feat(data/polynomial): %ₘ as a linear map  ([#9532](https://github.com/leanprover-community/mathlib/pull/9532))
This PR bundles `(%ₘ) = polynomial.mod_by_monic` into a linear map. In a follow-up PR, I'll show this map descends to a linear map `adjoin_root q → polynomial R`, thereby (computably) assigning coefficients to each element in `adjoin_root q`.
#### Estimated changes
modified src/data/polynomial/ring_division.lean
- \+ *lemma* mod_by_monic_eq_of_dvd_sub
- \+ *lemma* add_mod_by_monic
- \+ *lemma* smul_mod_by_monic
- \+ *def* mod_by_monic_hom

modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* mem_ker_mod_by_monic
- \+ *lemma* ker_mod_by_monic_hom



## [2021-10-08 12:12:57](https://github.com/leanprover-community/mathlib/commit/99c3e22)
refactor(geometry/manifold): remove old_structure_cmd ([#9617](https://github.com/leanprover-community/mathlib/pull/9617))
#### Estimated changes
modified src/geometry/manifold/algebra/lie_group.lean

modified src/geometry/manifold/algebra/monoid.lean

modified src/geometry/manifold/algebra/structures.lean

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/charted_space.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean

modified src/topology/algebra/open_subgroup.lean



## [2021-10-08 12:12:56](https://github.com/leanprover-community/mathlib/commit/c107549)
refactor(ring_theory/valuation): remove unnecessary old_structure_cmd ([#9615](https://github.com/leanprover-community/mathlib/pull/9615))
#### Estimated changes
modified src/ring_theory/valuation/basic.lean

modified src/topology/algebra/valued_field.lean



## [2021-10-08 12:12:55](https://github.com/leanprover-community/mathlib/commit/7bdd10e)
refactor(order/category): remove old_structure_cmd ([#9614](https://github.com/leanprover-community/mathlib/pull/9614))
#### Estimated changes
modified src/order/category/NonemptyFinLinOrd.lean



## [2021-10-08 12:12:54](https://github.com/leanprover-community/mathlib/commit/af09d3f)
refactor(algebra/absolute_value): remove unnecessary old_structure_cmd ([#9613](https://github.com/leanprover-community/mathlib/pull/9613))
#### Estimated changes
modified src/algebra/order/absolute_value.lean

modified src/data/polynomial/degree/card_pow_degree.lean



## [2021-10-08 12:12:52](https://github.com/leanprover-community/mathlib/commit/25a45ab)
refactor(order/omega_complete_partial_order): remove old_structure_cmd ([#9612](https://github.com/leanprover-community/mathlib/pull/9612))
Removing a use of `old_structure_cmd`.
#### Estimated changes
modified src/order/category/omega_complete_partial_order.lean

modified src/order/omega_complete_partial_order.lean
- \+ *def* continuous_hom.simps.apply



## [2021-10-08 12:12:51](https://github.com/leanprover-community/mathlib/commit/cea97d9)
feat(*): add not_mem_of_not_mem_closure for anything with subset_closure ([#9595](https://github.com/leanprover-community/mathlib/pull/9595))
This is a goal I would expect library search to finish if I have something not in a closure and I want it not in the base set.
#### Estimated changes
modified src/field_theory/subfield.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/group_theory/submonoid/basic.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/model_theory/basic.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/order/closure.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/ring_theory/subring.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/ring_theory/subsemiring.lean
- \+ *lemma* not_mem_of_not_mem_closure

modified src/topology/basic.lean
- \+ *lemma* not_mem_of_not_mem_closure



## [2021-10-08 10:04:44](https://github.com/leanprover-community/mathlib/commit/6c9eee4)
refactor(data/finsupp/basic): remove sub lemmas ([#9603](https://github.com/leanprover-community/mathlib/pull/9603))
* Remove the finsupp sub lemmas that are special cases of lemmas in `algebra/order/sub`, namely:
  * `finsupp.nat_zero_sub`
  * `finsupp.nat_sub_self`
  * `finsupp.nat_add_sub_of_le`
  * `finsupp.nat_sub_add_cancel`
  * `finsupp.nat_add_sub_cancel`
  * `finsupp.nat_add_sub_cancel_left`
  * `finsupp.nat_add_sub_assoc`
* Rename the remaining lemmas to use `tsub`:
  * `finsupp.coe_nat_sub` → `finsupp.coe_tsub`
  * `finsupp.nat_sub_apply` → `finsupp.tsub_apply`
  Lemmas in `algebra/order/sub` will soon also use `tsub` (see [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_lt_mul''''))
#### Estimated changes
modified src/data/finsupp/antidiagonal.lean

modified src/data/finsupp/basic.lean
- \+ *lemma* coe_tsub
- \+ *lemma* tsub_apply
- \+ *lemma* single_tsub
- \- *lemma* coe_nat_sub
- \- *lemma* nat_sub_apply
- \- *lemma* single_nat_sub
- \- *lemma* nat_zero_sub
- \- *lemma* nat_sub_self
- \- *lemma* nat_add_sub_of_le
- \- *lemma* nat_sub_add_cancel
- \- *lemma* nat_add_sub_cancel
- \- *lemma* nat_add_sub_cancel_left
- \- *lemma* nat_add_sub_assoc

modified src/data/mv_polynomial/basic.lean

modified src/ring_theory/power_series/basic.lean



## [2021-10-08 10:04:43](https://github.com/leanprover-community/mathlib/commit/34145b7)
feat(group_theory/subgroup/basic): a new to_additive lemma, and remove a by hand proof ([#9594](https://github.com/leanprover-community/mathlib/pull/9594))
I needed `add_subgroup.smul_mem` which didn't seem to exist, and noticed that the `add_subgroup.gsmul_mem` version is proved by hand while to_additive generates it fine (now?)
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \- *lemma* gsmul_mem



## [2021-10-08 10:04:41](https://github.com/leanprover-community/mathlib/commit/d5146f4)
feat(ring_theory): `adjoin_root g ≃ S` if `S` has a power basis with the right minpoly ([#9529](https://github.com/leanprover-community/mathlib/pull/9529))
This is basically `power_basis.equiv'` with slightly different hypotheses, specialised to `adjoin_root`. It guarantees that even over non-fields, a monogenic extension of `R` can be given by the polynomials over `R` modulo the relevant minimal polynomial.
#### Estimated changes
modified src/field_theory/adjoin.lean

modified src/field_theory/normal.lean

modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* lift_mk
- \+ *lemma* lift_hom_mk
- \+ *lemma* lift_hom_root
- \+ *lemma* lift_hom_of
- \+ *lemma* equiv'_to_alg_hom
- \+ *lemma* equiv'_symm_to_alg_hom
- \+/\- *lemma* lift_mk
- \+ *def* equiv'



## [2021-10-08 10:04:40](https://github.com/leanprover-community/mathlib/commit/82e2b98)
feat(ring_theory): generalize `power_basis.equiv` ([#9528](https://github.com/leanprover-community/mathlib/pull/9528))
`power_basis.equiv'` is an alternate formulation of `power_basis.equiv` that is somewhat more general when not over a field: instead of requiring the minimal polynomials are equal, we only require the generators are the roots of each other's minimal polynomials.
This is not quite enough to show `adjoin_root (minpoly R (pb : power_basis R S).gen)` is isomorphic to `S`, since `minpoly R (adjoin_root.root g)` is not guaranteed to have the same exact roots as `g` itself. So in a follow-up PR I will strengthen `power_basis.equiv'` to `adjoin_root.equiv'` that requires the correct hypothesis.
#### Estimated changes
modified src/field_theory/adjoin.lean

modified src/ring_theory/power_basis.lean
- \+ *lemma* equiv_of_root_aeval
- \+ *lemma* equiv_of_root_gen
- \+ *lemma* equiv_of_root_symm
- \+ *lemma* equiv_of_minpoly_aeval
- \+ *lemma* equiv_of_minpoly_gen
- \+ *lemma* equiv_of_minpoly_symm
- \+ *lemma* equiv_of_root_map
- \+ *lemma* equiv_of_minpoly_map
- \- *lemma* equiv_aeval
- \- *lemma* equiv_gen
- \- *lemma* equiv_symm
- \- *lemma* equiv_map



## [2021-10-08 10:04:39](https://github.com/leanprover-community/mathlib/commit/179a495)
feat(algebra/star/algebra): generalize to modules ([#9484](https://github.com/leanprover-community/mathlib/pull/9484))
This means there is now a `star_module ℂ (ι → ℂ)` instance available.
This adds `star_add_monoid`, and renames `star_algebra` to `star_module` with significantly relaxed typeclass arguments.
This also uses `export` to cut away some unnecessary definitions, and adds the missing `pi.star_def` to match `pi.add_def` etc.
#### Estimated changes
modified src/algebra/ring_quot.lean

deleted src/algebra/star/algebra.lean
- \- *lemma* star_smul

modified src/algebra/star/basic.lean
- \+/\- *lemma* star_id_of_comm
- \+/\- *lemma* star_zero
- \- *lemma* star_mul
- \+/\- *lemma* star_id_of_comm
- \- *lemma* star_add
- \+/\- *lemma* star_zero
- \+/\- *def* star_add_equiv
- \- *def* star
- \+/\- *def* star_add_equiv

modified src/algebra/star/chsh.lean

modified src/algebra/star/pi.lean
- \+ *lemma* star_def



## [2021-10-08 07:33:10](https://github.com/leanprover-community/mathlib/commit/9ecdd38)
chore(algebra/order/sub): generalize 2 lemmas ([#9611](https://github.com/leanprover-community/mathlib/pull/9611))
* generalize `lt_sub_iff_left` and `lt_sub_iff_right`;
* use general lemmas in `data.real.ennreal`.
#### Estimated changes
modified src/algebra/order/sub.lean
- \+/\- *lemma* lt_sub_iff_right
- \+/\- *lemma* lt_sub_iff_left
- \+ *lemma* lt_sub_comm
- \+/\- *lemma* lt_sub_iff_right
- \+/\- *lemma* lt_sub_iff_left

modified src/data/real/ennreal.lean
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* lt_sub_comm
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* lt_sub_comm



## [2021-10-08 07:33:09](https://github.com/leanprover-community/mathlib/commit/639a7ef)
feat(algebra/order/ring): variants of mul_sub' ([#9604](https://github.com/leanprover-community/mathlib/pull/9604))
Add some variants of `mul_sub'` and `sub_mul'` and use them in `ennreal`. (Also sneaking in a tiny stylistic change in `topology/ennreal`.)
#### Estimated changes
modified src/algebra/order/ring.lean
- \+ *lemma* sub_mul_ge
- \+ *lemma* mul_sub_ge
- \+ *lemma* mul_sub'
- \+ *lemma* sub_mul'
- \- *lemma* _root_.mul_sub'
- \- *lemma* _root_.sub_mul'

modified src/data/real/ennreal.lean
- \- *lemma* sub_mul_ge

modified src/topology/instances/ennreal.lean



## [2021-10-08 07:33:08](https://github.com/leanprover-community/mathlib/commit/83a07ce)
feat(data/nat/log): add antitonicity lemmas for first argument ([#9597](https://github.com/leanprover-community/mathlib/pull/9597))
`log` and `clog` are only antitone on bases >1, so we include this as an
assumption in `log_le_log_of_left_ge` (resp. `clog_le_...`) and as a
domain restriction in `log_left_gt_one_anti` (resp. `clog_left_...`).
#### Estimated changes
modified src/data/nat/log.lean
- \+ *lemma* log_le_log_of_left_ge
- \+ *lemma* log_monotone
- \+ *lemma* log_antitone_left
- \+ *lemma* clog_le_clog_of_left_ge
- \+ *lemma* clog_monotone
- \+ *lemma* clog_antitone_left
- \- *lemma* log_mono
- \- *lemma* clog_mono



## [2021-10-08 07:33:06](https://github.com/leanprover-community/mathlib/commit/41dd4da)
feat(data/multiset/interval): Intervals as `multiset`s ([#9588](https://github.com/leanprover-community/mathlib/pull/9588))
This provides API for `multiset.Ixx` (except `multiset.Ico`).
#### Estimated changes
modified src/data/multiset/erase_dup.lean

created src/data/multiset/interval.lean
- \+ *lemma* Icc_eq_zero_iff
- \+ *lemma* Ioc_eq_zero_iff
- \+ *lemma* Ioo_eq_zero_iff
- \+ *lemma* Ioo_eq_zero
- \+ *lemma* Icc_eq_zero_of_lt
- \+ *lemma* Ioc_eq_zero_of_le
- \+ *lemma* Ioo_eq_zero_of_le
- \+ *lemma* Ioc_self
- \+ *lemma* Ioo_self
- \+ *lemma* Icc_self
- \+ *lemma* map_add_const_Icc
- \+ *lemma* map_add_const_Ioc
- \+ *lemma* map_add_const_Ioo



## [2021-10-08 07:33:05](https://github.com/leanprover-community/mathlib/commit/c3768cc)
refactor(data/multiset/basic): remove sub lemmas ([#9578](https://github.com/leanprover-community/mathlib/pull/9578))
* Remove the multiset sub lemmas that are special cases of lemmas in `algebra/order/sub`
* [This](https://github.com/leanprover-community/mathlib/blob/14c3324143beef6e538f63da9c48d45f4a949604/src/data/multiset/basic.lean#L1513-L1538) gives the list of renamings.
* Use `derive` in `pnat.factors`.
#### Estimated changes
modified src/algebra/associated.lean

modified src/data/finset/basic.lean

modified src/data/list/perm.lean

modified src/data/multiset/antidiagonal.lean

modified src/data/multiset/basic.lean
- \+/\- *theorem* le_union_left
- \+/\- *theorem* eq_union_left
- \- *theorem* add_sub_of_le
- \- *theorem* sub_add'
- \- *theorem* sub_add_cancel
- \- *theorem* add_sub_cancel_left
- \- *theorem* add_sub_cancel
- \- *theorem* sub_le_sub_right
- \- *theorem* sub_le_sub_left
- \- *theorem* le_sub_add
- \- *theorem* sub_le_self
- \+/\- *theorem* le_union_left
- \+/\- *theorem* eq_union_left

modified src/data/multiset/nodup.lean

modified src/data/pnat/factors.lean
- \- *theorem* add_sub_of_le

modified src/group_theory/perm/cycle_type.lean



## [2021-10-08 07:33:03](https://github.com/leanprover-community/mathlib/commit/c400677)
feat(algebra/module/basic): `module rat E` is a subsingleton ([#9570](https://github.com/leanprover-community/mathlib/pull/9570))
* allow different (semi)rings in `add_monoid_hom.map_int_cast_smul` and `add_monoid_hom.map_nat_cast_smul`;
* add `add_monoid_hom.map_inv_int_cast_smul` and `add_monoid_hom.map_inv_nat_cast_smul`;
* allow different division rings in `add_monoid_hom.map_rat_cast_smul`, drop `char_zero` assumption;
* prove `subsingleton (module rat M)`;
* add a few convenience lemmas.
#### Estimated changes
modified src/algebra/module/basic.lean
- \+/\- *lemma* map_int_cast_smul
- \+/\- *lemma* map_nat_cast_smul
- \+ *lemma* map_inv_int_cast_smul
- \+ *lemma* map_inv_nat_cast_smul
- \+/\- *lemma* map_rat_cast_smul
- \+ *lemma* subsingleton_rat_module
- \+ *lemma* inv_int_cast_smul_eq
- \+ *lemma* inv_nat_cast_smul_eq
- \+ *lemma* rat_cast_smul_eq
- \+/\- *lemma* map_int_cast_smul
- \+/\- *lemma* map_nat_cast_smul
- \+/\- *lemma* map_rat_cast_smul

modified src/data/rat/cast.lean
- \+ *theorem* cast_def
- \+ *theorem* cast_inv_nat
- \+ *theorem* cast_inv_int

modified src/number_theory/padics/padic_numbers.lean

modified src/topology/instances/real_vector_space.lean



## [2021-10-08 07:33:02](https://github.com/leanprover-community/mathlib/commit/eb3595e)
move(order/*): move from `algebra.order.` the files that aren't about algebra ([#9562](https://github.com/leanprover-community/mathlib/pull/9562))
`algebra.order.basic` and `algebra.order.functions` never mention `+`, `-` or `*`. Thus they belong under `order`.
#### Estimated changes
modified archive/arithcc.lean

modified src/algebra/covariant_and_contravariant.lean

deleted src/algebra/order/basic.lean
- \- *lemma* le_rfl
- \- *lemma* trans_le
- \- *lemma* not_lt
- \- *lemma* not_gt
- \- *lemma* trans_eq
- \- *lemma* lt_iff_ne
- \- *lemma* le_iff_eq
- \- *lemma* lt_or_le
- \- *lemma* le_or_lt
- \- *lemma* le_or_le
- \- *lemma* ne'
- \- *lemma* lt_or_lt
- \- *lemma* ge_iff_le
- \- *lemma* gt_iff_lt
- \- *lemma* not_le_of_lt
- \- *lemma* not_lt_of_le
- \- *lemma* le_iff_eq_or_lt
- \- *lemma* lt_iff_le_and_ne
- \- *lemma* eq_iff_le_not_lt
- \- *lemma* eq_or_lt_of_le
- \- *lemma* ne.le_iff_lt
- \- *lemma* ne_iff_lt_iff_le
- \- *lemma* lt_of_not_ge'
- \- *lemma* lt_iff_not_ge'
- \- *lemma* ne.lt_or_lt
- \- *lemma* not_lt_iff_eq_or_lt
- \- *lemma* exists_ge_of_linear
- \- *lemma* lt_imp_lt_of_le_imp_le
- \- *lemma* le_imp_le_iff_lt_imp_lt
- \- *lemma* lt_iff_lt_of_le_iff_le'
- \- *lemma* lt_iff_lt_of_le_iff_le
- \- *lemma* le_iff_le_iff_lt_iff_lt
- \- *lemma* eq_of_forall_le_iff
- \- *lemma* le_of_forall_le
- \- *lemma* le_of_forall_le'
- \- *lemma* le_of_forall_lt
- \- *lemma* forall_lt_iff_le
- \- *lemma* le_of_forall_lt'
- \- *lemma* forall_lt_iff_le'
- \- *lemma* eq_of_forall_ge_iff
- \- *lemma* le_implies_le_of_le_of_le
- \- *lemma* cmp_eq_lt_iff
- \- *lemma* cmp_eq_eq_iff
- \- *lemma* cmp_eq_gt_iff
- \- *lemma* cmp_self_eq_eq
- \- *lemma* cmp_eq_cmp_symm
- \- *lemma* lt_iff_lt_of_cmp_eq_cmp
- \- *lemma* le_iff_le_of_cmp_eq_cmp
- \- *theorem* ge_of_eq
- \- *theorem* cmp_le_swap
- \- *theorem* cmp_le_eq_cmp
- \- *theorem* compares_swap
- \- *theorem* swap_eq_iff_eq_swap
- \- *theorem* compares.eq_lt
- \- *theorem* compares.ne_lt
- \- *theorem* compares.eq_eq
- \- *theorem* compares.eq_gt
- \- *theorem* compares.ne_gt
- \- *theorem* compares.le_total
- \- *theorem* compares.le_antisymm
- \- *theorem* compares.inj
- \- *theorem* compares_iff_of_compares_impl
- \- *theorem* swap_or_else
- \- *theorem* or_else_eq_lt
- \- *theorem* cmp_compares
- \- *theorem* cmp_swap
- \- *def* cmp_le
- \- *def* compares
- \- *def* linear_order_of_compares

modified src/algebra/order/monoid.lean

modified src/computability/turing_machine.lean

modified src/data/int/basic.lean

modified src/order/basic.lean
- \+ *lemma* le_rfl
- \+/\- *lemma* lt_self_iff_false
- \+ *lemma* trans_le
- \+ *lemma* not_lt
- \+ *lemma* not_gt
- \+ *lemma* trans_eq
- \+ *lemma* lt_iff_ne
- \+ *lemma* le_iff_eq
- \+ *lemma* lt_or_le
- \+ *lemma* le_or_lt
- \+ *lemma* le_or_le
- \+ *lemma* ne'
- \+ *lemma* lt_or_lt
- \+ *lemma* ge_iff_le
- \+ *lemma* gt_iff_lt
- \+ *lemma* not_le_of_lt
- \+ *lemma* not_lt_of_le
- \+ *lemma* le_iff_eq_or_lt
- \+ *lemma* lt_iff_le_and_ne
- \+ *lemma* eq_iff_le_not_lt
- \+ *lemma* eq_or_lt_of_le
- \+ *lemma* ne.le_iff_lt
- \+ *lemma* ne_iff_lt_iff_le
- \+ *lemma* lt_of_not_ge'
- \+ *lemma* lt_iff_not_ge'
- \+ *lemma* ne.lt_or_lt
- \+ *lemma* not_lt_iff_eq_or_lt
- \+ *lemma* exists_ge_of_linear
- \+ *lemma* lt_imp_lt_of_le_imp_le
- \+ *lemma* le_imp_le_iff_lt_imp_lt
- \+ *lemma* lt_iff_lt_of_le_iff_le'
- \+ *lemma* lt_iff_lt_of_le_iff_le
- \+ *lemma* le_iff_le_iff_lt_iff_lt
- \+ *lemma* eq_of_forall_le_iff
- \+ *lemma* le_of_forall_le
- \+ *lemma* le_of_forall_le'
- \+ *lemma* le_of_forall_lt
- \+ *lemma* forall_lt_iff_le
- \+ *lemma* le_of_forall_lt'
- \+ *lemma* forall_lt_iff_le'
- \+ *lemma* eq_of_forall_ge_iff
- \+ *lemma* le_implies_le_of_le_of_le
- \+/\- *lemma* lt_self_iff_false
- \- *lemma* dual_compares
- \+ *theorem* ge_of_eq
- \- *theorem* cmp_le_flip

created src/order/compare.lean
- \+ *lemma* cmp_le_swap
- \+ *lemma* cmp_le_eq_cmp
- \+ *lemma* compares_swap
- \+ *lemma* swap_eq_iff_eq_swap
- \+ *lemma* compares.eq_lt
- \+ *lemma* compares.ne_lt
- \+ *lemma* compares.eq_eq
- \+ *lemma* compares.eq_gt
- \+ *lemma* compares.ne_gt
- \+ *lemma* compares.le_total
- \+ *lemma* compares.le_antisymm
- \+ *lemma* compares.inj
- \+ *lemma* compares_iff_of_compares_impl
- \+ *lemma* swap_or_else
- \+ *lemma* or_else_eq_lt
- \+ *lemma* order_dual.dual_compares
- \+ *lemma* cmp_compares
- \+ *lemma* cmp_swap
- \+ *lemma* order_dual.cmp_le_flip
- \+ *lemma* cmp_eq_lt_iff
- \+ *lemma* cmp_eq_eq_iff
- \+ *lemma* cmp_eq_gt_iff
- \+ *lemma* cmp_self_eq_eq
- \+ *lemma* cmp_eq_cmp_symm
- \+ *lemma* lt_iff_lt_of_cmp_eq_cmp
- \+ *lemma* le_iff_le_of_cmp_eq_cmp
- \+ *def* cmp_le
- \+ *def* compares
- \+ *def* linear_order_of_compares

renamed src/algebra/order/functions.lean to src/order/min_max.lean

modified src/order/monotone.lean

modified src/order/pilex.lean

modified src/tactic/push_neg.lean



## [2021-10-08 07:33:00](https://github.com/leanprover-community/mathlib/commit/8aa1893)
feat(group_theory/subgroup/basic): Analog of `mul_aut.conj` for normal subgroups. ([#9552](https://github.com/leanprover-community/mathlib/pull/9552))
Analog of `mul_aut.conj` for normal subgroups (pretty much just copying the code from `data/equiv/mul_add_aut.lean`).
#### Estimated changes
modified src/group_theory/group_action/conj_act.lean
- \+ *lemma* subgroup.coe_conj_smul
- \+ *lemma* _root_.mul_aut.conj_normal_apply
- \+ *lemma* _root_.mul_aut.conj_normal_symm_apply
- \+ *lemma* _root_.mul_aut.conj_normal_inv_apply
- \+ *def* _root_.mul_aut.conj_normal



## [2021-10-08 07:32:59](https://github.com/leanprover-community/mathlib/commit/1390b44)
feat(analysis/convex/function): API for strict convex functions ([#9437](https://github.com/leanprover-community/mathlib/pull/9437))
This provides all the basic API for `strict_convex_on` and `strict_concave_on`.
#### Estimated changes
modified src/analysis/convex/function.lean
- \+ *lemma* strict_convex_on.subset
- \+ *lemma* strict_concave_on.subset
- \+ *lemma* convex_on_iff_pairwise_on_pos
- \+ *lemma* concave_on_iff_pairwise_on_pos
- \+ *lemma* strict_convex_on.convex_on
- \+ *lemma* strict_concave_on.concave_on
- \+ *lemma* strict_convex_on.convex_lt
- \+ *lemma* strict_concave_on.convex_gt
- \+ *lemma* linear_order.strict_convex_on_of_lt
- \+ *lemma* linear_order.strict_concave_on_of_lt
- \+ *lemma* strict_convex_on.add
- \+ *lemma* strict_concave_on.add
- \+ *lemma* strict_convex_on.sup
- \+ *lemma* strict_concave_on.inf
- \+ *lemma* strict_convex_on.lt_on_open_segment'
- \+ *lemma* strict_concave_on.lt_on_open_segment'
- \+ *lemma* strict_convex_on.lt_on_open_segment
- \+ *lemma* strict_concave_on.lt_on_open_segment
- \+ *lemma* strict_convex_on.lt_left_of_right_lt'
- \+ *lemma* strict_concave_on.left_lt_of_lt_right'
- \+ *lemma* strict_convex_on.lt_right_of_left_lt'
- \+ *lemma* strict_concave_on.lt_right_of_left_lt'
- \+ *lemma* strict_convex_on.lt_left_of_right_lt
- \+ *lemma* strict_concave_on.left_lt_of_lt_right
- \+ *lemma* strict_convex_on.lt_right_of_left_lt
- \+ *lemma* strict_concave_on.lt_right_of_left_lt
- \+ *lemma* neg_strict_convex_on_iff
- \+ *lemma* neg_strict_concave_on_iff
- \+ *lemma* strict_convex_on.translate_right
- \+ *lemma* strict_concave_on.translate_right
- \+ *lemma* strict_convex_on.translate_left
- \+ *lemma* strict_concave_on.translate_left
- \+ *lemma* strict_convex_on_iff_div
- \+ *lemma* strict_concave_on_iff_div
- \- *lemma* convex_on_iff_forall_pos_ne
- \- *lemma* concave_on_iff_forall_pos_ne

modified src/analysis/convex/slope.lean
- \+ *lemma* strict_convex_on.slope_strict_mono_adjacent
- \+ *lemma* strict_concave_on.slope_anti_adjacent
- \+ *lemma* strict_convex_on_of_slope_strict_mono_adjacent
- \+ *lemma* strict_concave_on_of_slope_strict_anti_adjacent
- \+ *lemma* strict_convex_on_iff_slope_strict_mono_adjacent
- \+ *lemma* strict_concave_on_iff_slope_strict_anti_adjacent



## [2021-10-08 07:32:58](https://github.com/leanprover-community/mathlib/commit/a0504eb)
refactor(data/*/interval): generalize `finset.Ico` to locally finite orders ([#7987](https://github.com/leanprover-community/mathlib/pull/7987))
`finset.Ico` currently goes `ℕ → ℕ → finset ℕ`. This generalizes it to `α → α → finset α` where `locally_finite_order α`.
This also ports all the existing `finset.Ico` lemmas to the new API, which involves renaming and moving them to `data.finset.interval` or `data.nat.interval` depending on whether I could generalize them away from `ℕ` or not.
#### Estimated changes
modified src/algebra/big_operators/intervals.lean

modified src/algebra/geom_sum.lean

modified src/analysis/analytic/composition.lean

modified src/analysis/analytic/inverse.lean

modified src/analysis/p_series.lean

modified src/analysis/special_functions/exp_log.lean

modified src/data/fin/interval.lean
- \+ *lemma* Ico_eq_finset_subtype
- \+ *lemma* map_subtype_embedding_Ico
- \+ *lemma* card_Ico
- \+ *lemma* card_fintype_Ico

modified src/data/finset/default.lean

modified src/data/finset/interval.lean
- \+ *lemma* nonempty_Ico
- \+ *lemma* Ico_eq_empty_iff
- \+ *lemma* Ico_eq_empty_of_le
- \+ *lemma* Ico_self
- \+ *lemma* right_not_mem_Ico
- \+ *lemma* Ico_filter_lt_of_le_left
- \+ *lemma* Ico_filter_lt_of_right_le
- \+ *lemma* Ico_filter_lt_of_le_right
- \+ *lemma* Ico_filter_le_of_le_left
- \+ *lemma* Ico_filter_le_of_right_le
- \+ *lemma* Ico_filter_le_of_left_le
- \+ *lemma* Ico_insert_right
- \+ *lemma* Ioo_insert_left
- \+ *lemma* Ico_inter_Ico_consecutive
- \+ *lemma* Ico_disjoint_Ico_consecutive
- \+ *lemma* Ico_filter_le_left
- \+ *lemma* Ico_subset_Ico_iff
- \+ *lemma* Ico_union_Ico_eq_Ico
- \+ *lemma* Ico_union_Ico'
- \+ *lemma* Ico_union_Ico
- \+ *lemma* Ico_inter_Ico
- \+ *lemma* Ico_filter_lt
- \+ *lemma* Ico_filter_le
- \+ *lemma* Ico_diff_Ico_left
- \+ *lemma* Ico_diff_Ico_right
- \+ *lemma* image_add_const_Ico

deleted src/data/finset/intervals.lean
- \- *lemma* coe_eq_Ico
- \- *lemma* union_consecutive
- \- *lemma* union'
- \- *lemma* union
- \- *lemma* inter_consecutive
- \- *lemma* inter
- \- *lemma* disjoint_consecutive
- \- *lemma* filter_lt_of_top_le
- \- *lemma* filter_lt_of_le_bot
- \- *lemma* filter_Ico_bot
- \- *lemma* filter_lt_of_ge
- \- *lemma* filter_lt
- \- *lemma* filter_le_of_le_bot
- \- *lemma* filter_le_of_top_le
- \- *lemma* filter_le_of_le
- \- *lemma* filter_le
- \- *lemma* diff_left
- \- *lemma* diff_right
- \- *lemma* image_const_sub
- \- *lemma* range_eq_Ico
- \- *lemma* range_image_pred_top_sub
- \- *lemma* Ico_ℤ.mem
- \- *lemma* Ico_ℤ.card
- \- *theorem* val
- \- *theorem* to_finset
- \- *theorem* image_add
- \- *theorem* image_sub
- \- *theorem* zero_bot
- \- *theorem* card
- \- *theorem* mem
- \- *theorem* eq_empty_of_le
- \- *theorem* self_eq_empty
- \- *theorem* eq_empty_iff
- \- *theorem* subset_iff
- \- *theorem* succ_singleton
- \- *theorem* succ_top
- \- *theorem* succ_top'
- \- *theorem* insert_succ_bot
- \- *theorem* pred_singleton
- \- *theorem* not_mem_top
- \- *def* Ico
- \- *def* Ico_ℤ

deleted src/data/fintype/intervals.lean
- \- *lemma* Ico_ℕ_finite
- \- *lemma* Ioo_ℕ_finite
- \- *lemma* Icc_ℕ_finite
- \- *lemma* Ioc_ℕ_finite
- \- *lemma* Ico_ℕ_card
- \- *lemma* Ioo_ℕ_card
- \- *lemma* Icc_ℕ_card
- \- *lemma* Ioc_ℕ_card
- \- *lemma* Ico_pnat_card
- \- *lemma* Ico_ℤ_finite
- \- *lemma* Ioo_ℤ_finite
- \- *lemma* Icc_ℤ_finite
- \- *lemma* Ioc_ℤ_finite
- \- *lemma* Ico_ℤ_card
- \- *lemma* Ioo_ℤ_card
- \- *lemma* Icc_ℤ_card
- \- *lemma* Ioc_ℤ_card

modified src/data/int/interval.lean
- \+ *lemma* Ico_eq_finset_map
- \+ *lemma* card_Ico
- \+ *lemma* card_Ico_of_le
- \+ *lemma* card_fintype_Ico
- \+ *lemma* card_fintype_Ico_of_le

modified src/data/nat/interval.lean
- \+ *lemma* Ico_eq_range'
- \+ *lemma* Iio_eq_range
- \+ *lemma* Ico_zero_eq_range
- \+ *lemma* _root_.finset.range_eq_Ico
- \+ *lemma* card_Ico
- \+ *lemma* card_fintype_Ico
- \+ *lemma* Ico_succ_right
- \+ *lemma* Ico_succ_left
- \+ *lemma* Icc_pred_right
- \+ *lemma* Ico_succ_succ
- \+ *lemma* Ico_succ_singleton
- \+ *lemma* Ico_pred_singleton
- \+ *lemma* Ico_succ_right_eq_insert_Ico
- \+ *lemma* Ico_insert_succ_left
- \+ *lemma* image_sub_const_Ico
- \+ *lemma* Ico_image_const_sub_eq_Ico
- \+ *lemma* range_image_pred_top_sub

modified src/data/nat/multiplicity.lean

modified src/data/nat/totient.lean

modified src/data/pnat/interval.lean
- \+ *lemma* Ico_eq_finset_subtype
- \+ *lemma* map_subtype_embedding_Ico
- \+ *lemma* card_Ico
- \+ *lemma* card_fintype_Ico

deleted src/data/pnat/intervals.lean
- \- *lemma* Ico.mem
- \- *lemma* Ico.card
- \- *def* Ico

modified src/data/polynomial/inductions.lean

modified src/data/polynomial/iterated_deriv.lean

modified src/measure_theory/decomposition/unsigned_hahn.lean

modified src/number_theory/ADE_inequality.lean

modified src/number_theory/divisors.lean

modified src/number_theory/primorial.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/order/locally_finite.lean
- \+ *lemma* mem_Ico
- \+ *lemma* coe_Ico
- \+ *lemma* Iio_eq_Ico
- \+ *lemma* coe_Iio
- \+ *lemma* mem_Iio
- \+ *lemma* mem_Iio
- \+ *lemma* finite_Ico
- \+ *lemma* finite_Iio
- \+ *lemma* subtype_Ico_eq
- \+ *lemma* map_subtype_embedding_Ico
- \+ *theorem* Ico_subset_Ico
- \+ *def* Ico
- \+ *def* Iio
- \+ *def* Iio

modified src/probability_theory/independence.lean

modified src/ring_theory/henselian.lean

modified src/tactic/interval_cases.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/instances/nnreal.lean

modified src/topology/instances/real.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/emetric_space.lean

modified test/fin_cases.lean



## [2021-10-08 06:08:46](https://github.com/leanprover-community/mathlib/commit/ba2454e)
feat(ring_theory/coprime): two lemmas prereq for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9456](https://github.com/leanprover-community/mathlib/pull/9456))
Two variants of the fact that `¬ is_coprime 0 0`.
#### Estimated changes
modified src/ring_theory/coprime/basic.lean
- \+ *lemma* is_coprime.ne_zero
- \+ *lemma* sq_add_sq_ne_zero



## [2021-10-08 02:40:18](https://github.com/leanprover-community/mathlib/commit/235bfd7)
chore(scripts): update nolints.txt ([#9610](https://github.com/leanprover-community/mathlib/pull/9610))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-10-08 01:32:09](https://github.com/leanprover-community/mathlib/commit/9ea4568)
fix(topology/path_connected): add `continuity` to `path.continuous_extend` ([#9605](https://github.com/leanprover-community/mathlib/pull/9605))
#### Estimated changes
modified src/topology/path_connected.lean



## [2021-10-08 00:30:16](https://github.com/leanprover-community/mathlib/commit/fa3b622)
refactor(analysis/normed_space/linear_isometry): semilinear isometries ([#9551](https://github.com/leanprover-community/mathlib/pull/9551))
Generalize the theory of linear isometries to the semilinear setting.
#### Estimated changes
modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* to_linear_map_injective
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+ *lemma* map_smulₛₗ
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_eq_iff
- \+/\- *lemma* map_ne
- \+/\- *lemma* coe_comp
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_to_linear_equiv
- \+/\- *lemma* to_linear_equiv_injective
- \+/\- *lemma* ext
- \+/\- *lemma* range_eq_univ
- \+/\- *lemma* apply_symm_apply
- \+/\- *lemma* coe_trans
- \+/\- *lemma* trans_refl
- \+/\- *lemma* symm_trans
- \+/\- *lemma* coe_symm_trans
- \+/\- *lemma* trans_assoc
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_coe'
- \+/\- *lemma* coe_coe''
- \+ *lemma* map_smulₛₗ
- \+/\- *lemma* map_smul
- \+/\- *lemma* to_linear_map_injective
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_eq_iff
- \+/\- *lemma* map_ne
- \+/\- *lemma* coe_comp
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_to_linear_equiv
- \+/\- *lemma* to_linear_equiv_injective
- \+/\- *lemma* ext
- \+/\- *lemma* range_eq_univ
- \+/\- *lemma* apply_symm_apply
- \+/\- *lemma* coe_trans
- \+/\- *lemma* trans_refl
- \+/\- *lemma* symm_trans
- \+/\- *lemma* coe_symm_trans
- \+/\- *lemma* trans_assoc
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_coe'
- \+/\- *lemma* coe_coe''
- \+/\- *lemma* map_smul
- \+/\- *def* to_continuous_linear_map
- \+/\- *def* comp
- \+/\- *def* of_bounds
- \+/\- *def* to_linear_isometry
- \+/\- *def* to_isometric
- \+/\- *def* to_homeomorph
- \+/\- *def* to_continuous_linear_equiv
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* to_continuous_linear_map
- \+/\- *def* comp
- \+/\- *def* of_bounds
- \+/\- *def* to_linear_isometry
- \+/\- *def* to_isometric
- \+/\- *def* to_homeomorph
- \+/\- *def* to_continuous_linear_equiv
- \+/\- *def* symm
- \+/\- *def* trans

modified src/analysis/normed_space/multilinear.lean



## [2021-10-07 21:23:16](https://github.com/leanprover-community/mathlib/commit/9518ce1)
feat(topology/algebra): valued fields ([#9589](https://github.com/leanprover-community/mathlib/pull/9589))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* _root_.group_with_zero.eq_zero_or_unit

modified src/ring_theory/valuation/basic.lean
- \+ *def* lt_add_subgroup

modified src/topology/algebra/uniform_group.lean
- \+ *lemma* topological_add_group.separated_iff_zero_closed
- \+ *lemma* topological_add_group.separated_of_zero_sep

created src/topology/algebra/valuation.lean
- \+ *lemma* subgroups_basis
- \+ *lemma* mem_nhds
- \+ *lemma* mem_nhds_zero
- \+ *lemma* loc_const
- \+ *lemma* cauchy_iff

created src/topology/algebra/valued_field.lean
- \+ *lemma* valuation.inversion_estimate
- \+ *lemma* valued.continuous_valuation
- \+ *lemma* valued.continuous_extension
- \+ *lemma* valued.extension_extends

modified src/topology/basic.lean
- \+ *lemma* dense_range.mem_nhds



## [2021-10-07 19:09:56](https://github.com/leanprover-community/mathlib/commit/ebccce9)
feat(measure_theory/covering/besicovitch): the measurable Besicovitch covering theorem ([#9576](https://github.com/leanprover-community/mathlib/pull/9576))
The measurable Besicovitch theorem ensures that, in nice metric spaces, if at every point one considers a class of balls of arbitrarily small radii, called admissible balls, then one can cover almost all the space by a family of disjoint admissible balls. It is deduced from the topological Besicovitch theorem.
#### Estimated changes
modified src/measure_theory/covering/besicovitch.lean
- \+ *lemma* exist_finset_disjoint_balls_large_measure
- \+ *theorem* exists_disjoint_closed_ball_covering_of_finite_measure
- \+ *theorem* exists_disjoint_closed_ball_covering



## [2021-10-07 15:09:34](https://github.com/leanprover-community/mathlib/commit/8a60fd7)
refactor(data/ennreal/basic): prove has_ordered_sub instance ([#9582](https://github.com/leanprover-community/mathlib/pull/9582))
* Give `has_sub` and `has_ordered_sub` instances on `with_top α`.
* This gives a new subtraction on `ennreal`. The lemma `ennreal.sub_eq_Inf` proves that it is equal to the old value.
* Simplify many proofs about `sub` on `ennreal` 
* Proofs that are instantiations of more general lemmas will be removed in a subsequent PR
* Many lemmas that require `add_le_cancellable` in general are reformulated using `≠ ∞`
* Lemmas are reordered, but no lemmas are renamed, removed, or have a different type. Some `@[simp]` tags are removed if a more general simp lemma applies.
* Minor: generalize `preorder` to `has_le` in `has_ordered_sub` (not necessary for this PR, but useful in another (abandoned) branch).
#### Estimated changes
modified src/algebra/order/monoid.lean
- \+ *lemma* add_coe_eq_top_iff
- \+ *lemma* coe_add_eq_top_iff

modified src/algebra/order/sub.lean
- \+ *lemma* coe_sub
- \+ *lemma* top_sub_coe
- \+ *lemma* sub_top

modified src/data/real/ennreal.lean
- \+/\- *lemma* le_of_add_le_add_left
- \+/\- *lemma* le_of_add_le_add_right
- \+ *lemma* add_le_cancellable_iff_ne
- \+ *lemma* cancel_of_ne
- \+ *lemma* cancel_of_lt
- \+ *lemma* cancel_of_lt'
- \+ *lemma* cancel_coe
- \+/\- *lemma* add_right_inj
- \+/\- *lemma* add_left_inj
- \+ *lemma* sub_eq_Inf
- \+/\- *lemma* coe_sub
- \+/\- *lemma* top_sub_coe
- \+/\- *lemma* sub_top
- \+/\- *lemma* le_sub_add_self
- \+/\- *lemma* sub_eq_zero_of_le
- \+/\- *lemma* sub_self
- \+/\- *lemma* zero_sub
- \+/\- *lemma* sub_le_sub
- \+/\- *lemma* sub_add_self_eq_max
- \+/\- *lemma* sub_le_self
- \+/\- *lemma* sub_zero
- \+ *lemma* sub_eq_top_iff
- \+ *lemma* sub_ne_top
- \+/\- *lemma* sub_le_sub_add_sub
- \+/\- *lemma* add_sub_self
- \+/\- *lemma* add_sub_self'
- \+/\- *lemma* sub_eq_of_add_eq
- \+/\- *lemma* coe_sub
- \+/\- *lemma* top_sub_coe
- \+/\- *lemma* sub_eq_zero_of_le
- \+/\- *lemma* sub_self
- \+/\- *lemma* zero_sub
- \+/\- *lemma* sub_top
- \+/\- *lemma* sub_le_sub
- \+/\- *lemma* add_sub_self
- \+/\- *lemma* add_sub_self'
- \+/\- *lemma* add_right_inj
- \+/\- *lemma* add_left_inj
- \- *lemma* sub_add_cancel_of_le
- \- *lemma* add_sub_cancel_of_le
- \+/\- *lemma* sub_add_self_eq_max
- \+/\- *lemma* le_sub_add_self
- \+/\- *lemma* sub_eq_of_add_eq
- \+/\- *lemma* sub_le_self
- \+/\- *lemma* sub_zero
- \+/\- *lemma* sub_le_sub_add_sub
- \+/\- *lemma* le_of_add_le_add_left
- \+/\- *lemma* le_of_add_le_add_right

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/instances/ennreal.lean



## [2021-10-07 13:09:23](https://github.com/leanprover-community/mathlib/commit/bf76a1f)
feat(algebra/order/with_zero): add lt_of_mul_lt_mul_of_le₀ and mul_lt_mul_of_lt_of_le₀ ([#9596](https://github.com/leanprover-community/mathlib/pull/9596))
#### Estimated changes
modified src/algebra/order/with_zero.lean
- \+ *lemma* mul_lt_mul_of_lt_of_le₀
- \+/\- *lemma* mul_lt_mul₀
- \+ *lemma* lt_of_mul_lt_mul_of_le₀
- \+/\- *lemma* mul_lt_mul₀



## [2021-10-07 11:57:08](https://github.com/leanprover-community/mathlib/commit/18a42f3)
feat(src/category_theory/*): Yoneda preserves limits. ([#9580](https://github.com/leanprover-community/mathlib/pull/9580))
Shows that `yoneda` and `coyoneda` preserves and reflects limits.
#### Estimated changes
modified src/category_theory/limits/functor_category.lean
- \+ *def* preserves_limit_of_evaluation
- \+ *def* preserves_limits_of_shape_of_evaluation
- \+ *def* preserves_limits_of_evaluation
- \+ *def* preserves_colimit_of_evaluation
- \+ *def* preserves_colimits_of_shape_of_evaluation
- \+ *def* preserves_colimits_of_evaluation

modified src/category_theory/limits/yoneda.lean



## [2021-10-07 06:55:11](https://github.com/leanprover-community/mathlib/commit/f874783)
feat(data/multiset/erase_dup): Alias for `multiset.erase_dup_eq_self` ([#9587](https://github.com/leanprover-community/mathlib/pull/9587))
The new `multiset.nodup.erase_dup` allows dot notation.
#### Estimated changes
modified src/algebra/squarefree.lean

modified src/data/finset/basic.lean

modified src/data/finset/pi.lean

modified src/data/multiset/erase_dup.lean

modified src/number_theory/arithmetic_function.lean



## [2021-10-07 06:55:10](https://github.com/leanprover-community/mathlib/commit/cc46f31)
feat(analysis/normed_space/add_torsor_bases): the interior of the convex hull of a finite affine basis is the set of points with strictly positive barycentric coordinates ([#9583](https://github.com/leanprover-community/mathlib/pull/9583))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/convex/hull.lean
- \+ *lemma* convex_hull_univ

modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* interior_convex_hull_aff_basis

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* eq_univ_of_subsingleton_span_eq_top



## [2021-10-07 06:14:33](https://github.com/leanprover-community/mathlib/commit/a7784aa)
feat(category_theory/*): Yoneda extension is Kan ([#9574](https://github.com/leanprover-community/mathlib/pull/9574))
- Proved that `(F.elements)ᵒᵖ ≌ costructured_arrow yoneda F`.
- Verified that the yoneda extension is indeed the left Kan extension along the yoneda embedding.
#### Estimated changes
modified src/category_theory/elements.lean
- \+ *lemma* from_costructured_arrow_obj_mk
- \+ *lemma* from_to_costructured_arrow_eq
- \+ *lemma* to_from_costructured_arrow_eq
- \+ *lemma* costructured_arrow_yoneda_equivalence_naturality
- \+ *def* to_costructured_arrow
- \+ *def* from_costructured_arrow
- \+ *def* costructured_arrow_yoneda_equivalence

modified src/category_theory/limits/presheaf.lean
- \+ *lemma* extend_along_yoneda_map
- \+ *def* extend_along_yoneda_iso_Kan_app
- \+ *def* extend_along_yoneda_iso_Kan



## [2021-10-07 06:14:32](https://github.com/leanprover-community/mathlib/commit/b9097f1)
feat(analysis/asymptotics): Define superpolynomial decay of a function ([#9440](https://github.com/leanprover-community/mathlib/pull/9440))
Define superpolynomial decay of functions in terms of asymptotics.is_O.
#### Estimated changes
created src/analysis/asymptotics/superpolynomial_decay.lean
- \+ *lemma* superpolynomial_decay_iff_tendsto_zero
- \+ *lemma* is_O.trans_superpolynomial_decay
- \+ *lemma* superpolynomial_decay.mono
- \+ *lemma* superpolynomial_decay.eventually_mono
- \+ *lemma* superpolynomial_decay_zero
- \+ *lemma* superpolynomial_decay_zero'
- \+ *lemma* superpolynomial_decay.add
- \+ *lemma* superpolynomial_decay.const_mul
- \+ *lemma* superpolynomial_decay.mul_const
- \+ *lemma* superpolynomial_decay_const_mul_iff_of_ne_zero
- \+ *lemma* superpolynomial_decay_mul_const_iff_of_ne_zero
- \+ *lemma* superpolynomial_decay_const_mul_iff
- \+ *lemma* superpolynomial_decay_mul_const_iff
- \+ *lemma* superpolynomial_decay.algebra_map_mul
- \+ *lemma* superpolynomial_decay.algebra_map_pow_mul
- \+ *lemma* superpolynomial_decay.mul_is_O_polynomial
- \+ *lemma* superpolynomial_decay.mul_is_O
- \+ *lemma* superpolynomial_decay.mul
- \+ *lemma* superpolynomial_decay_of_eventually_is_O
- \+ *lemma* superpolynomial_decay_of_is_O_fpow_le
- \+ *lemma* superpolynomial_decay_of_is_O_fpow_lt
- \+ *lemma* superpolynomial_decay.tendsto_zero
- \+ *lemma* superpolynomial_decay.eventually_le
- \+ *lemma* superpolynomial_decay_const_iff
- \+ *theorem* superpolynomial_decay_iff_is_bounded_under
- \+ *theorem* superpolynomial_decay_iff_is_o
- \+ *theorem* superpolynomial_decay_iff_norm_tendsto_zero
- \+ *theorem* superpolynomial_decay.polynomial_mul
- \+ *def* superpolynomial_decay



## [2021-10-07 04:15:17](https://github.com/leanprover-community/mathlib/commit/0bc7c2d)
fix(algebra/group/{prod,pi}): fix non-defeq `has_scalar` diamonds ([#9584](https://github.com/leanprover-community/mathlib/pull/9584))
This fixes diamonds in the following instances for nat- and int- actions:
* `has_scalar ℕ (α × β)`
* `has_scalar ℤ (α × β)`
* `has_scalar ℤ (Π a, β a)`
The last one revealed a diamond caused by inconsistent use of `pi_instance_derive_field`:
```lean
-- fails before this change
example [Π a, group $ β a] : group.to_div_inv_monoid (Π a, β a) = pi.div_inv_monoid := rfl
```
#### Estimated changes
modified src/algebra/group/pi.lean

modified src/algebra/group/prod.lean

modified test/instance_diamonds.lean



## [2021-10-07 04:15:16](https://github.com/leanprover-community/mathlib/commit/cb3c844)
feat(category_theory/limits/*): Filtered colimits preserves finite limits ([#9522](https://github.com/leanprover-community/mathlib/pull/9522))
Restated `category_theory.limits.colimit_limit_to_limit_colimit_is_iso` in terms of limit preserving.
#### Estimated changes
modified src/category_theory/limits/colimit_limit.lean
- \+/\- *lemma* ι_colimit_limit_to_limit_colimit_π
- \+/\- *lemma* ι_colimit_limit_to_limit_colimit_π

modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean

modified src/category_theory/limits/functor_category.lean
- \+ *def* limit_iso_swap_comp_lim
- \+ *def* colimit_iso_swap_comp_colim



## [2021-10-07 02:14:30](https://github.com/leanprover-community/mathlib/commit/7a2696d)
feat(category_theory/limits/preserves/*): Show that whiskering left preserves limits. ([#9581](https://github.com/leanprover-community/mathlib/pull/9581))
#### Estimated changes
modified src/category_theory/limits/preserves/functor_category.lean



## [2021-10-07 02:14:29](https://github.com/leanprover-community/mathlib/commit/f37aeb0)
refactor(algebra/gcd_monoid): drop nontriviality assumptions  ([#9568](https://github.com/leanprover-community/mathlib/pull/9568))
#### Estimated changes
modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/gcd_monoid/finset.lean

modified src/algebra/gcd_monoid/multiset.lean

modified src/algebra/group/units.lean

modified src/ring_theory/unique_factorization_domain.lean



## [2021-10-06 21:14:59](https://github.com/leanprover-community/mathlib/commit/f63786b)
refactor(data/finsupp/basic): has_ordered_sub on finsupp ([#9577](https://github.com/leanprover-community/mathlib/pull/9577))
* Generalize `has_sub` and `canonically_ordered_add_monoid` instances for any finsupp with codomain a `canonically_ordered_add_monoid` & `has_ordered_sub`.
* Provide `has_ordered_sub` instance in the same situation
* Generalize lemmas about `nat` to this situation.
* Prove some lemmas as special cases of `has_ordered_sub` lemmas. These will be removed in a subsequent PR.
* Simplify some lemmas about `α →₀ ℕ` using `has_ordered_sub` lemmas.
* Prove `nat.one_le_iff_ne_zero` (it's the second time I want to use it this week)
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+/\- *lemma* coe_nat_sub
- \+/\- *lemma* nat_sub_apply
- \+/\- *lemma* single_nat_sub
- \+/\- *lemma* nat_zero_sub
- \+/\- *lemma* nat_sub_self
- \+/\- *lemma* nat_add_sub_of_le
- \+/\- *lemma* nat_sub_add_cancel
- \+/\- *lemma* nat_add_sub_cancel
- \+/\- *lemma* nat_add_sub_cancel_left
- \+/\- *lemma* nat_add_sub_assoc
- \+/\- *lemma* sub_single_one_add
- \+/\- *lemma* add_sub_single_one
- \+/\- *lemma* coe_nat_sub
- \+/\- *lemma* nat_sub_apply
- \+/\- *lemma* single_nat_sub
- \+/\- *lemma* sub_single_one_add
- \+/\- *lemma* add_sub_single_one
- \+/\- *lemma* nat_zero_sub
- \+/\- *lemma* nat_sub_self
- \+/\- *lemma* nat_add_sub_cancel
- \+/\- *lemma* nat_add_sub_cancel_left
- \+/\- *lemma* nat_add_sub_of_le
- \+/\- *lemma* nat_sub_add_cancel
- \+/\- *lemma* nat_add_sub_assoc

modified src/data/nat/basic.lean
- \+ *lemma* one_le_iff_ne_zero



## [2021-10-06 21:14:58](https://github.com/leanprover-community/mathlib/commit/b4a9767)
feat(data/multiset/basic): has_ordered_sub multiset ([#9566](https://github.com/leanprover-community/mathlib/pull/9566))
* Provide `instance : has_ordered_sub (multiset α)`
* Prove most multiset subtraction lemmas as special cases of `has_ordered_sub` lemmas
* In a subsequent PR I will remove the specialized multiset lemmas
#### Estimated changes
modified src/data/multiset/basic.lean
- \+/\- *theorem* sub_eq_fold_erase
- \+/\- *theorem* sub_eq_fold_erase
- \- *theorem* sub_zero
- \- *theorem* sub_le_iff_le_add



## [2021-10-06 21:14:56](https://github.com/leanprover-community/mathlib/commit/845d064)
feat(algebra/big_operators/finprod): add finprod.mem_dvd ([#9549](https://github.com/leanprover-community/mathlib/pull/9549))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* dvd_prod_of_mem

modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_mem_dvd



## [2021-10-06 19:23:08](https://github.com/leanprover-community/mathlib/commit/b2ae195)
move(data/fin/*): group `fin` files under a `fin` folder ([#9524](https://github.com/leanprover-community/mathlib/pull/9524))
#### Estimated changes
modified src/category_theory/Fintype.lean

modified src/control/functor/multivariate.lean

modified src/data/bitvec/basic.lean

modified src/data/equiv/fin.lean

renamed src/data/fin.lean to src/data/fin/basic.lean

renamed src/data/fin2.lean to src/data/fin/fin2.lean

modified src/data/fintype/fin.lean

modified src/data/list/duplicate.lean

modified src/data/list/nodup_equiv_fin.lean

modified src/data/list/of_fn.lean

modified src/data/typevec.lean

modified src/data/vector3.lean

modified src/number_theory/dioph.lean

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/jordan_holder.lean

modified src/set_theory/pgame.lean

modified src/system/random/basic.lean



## [2021-10-06 18:27:53](https://github.com/leanprover-community/mathlib/commit/5c3cdd2)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are open maps (in finite dimensions over a complete field) ([#9543](https://github.com/leanprover-community/mathlib/pull/9543))
Using the open mapping theorem with a one-dimensional codomain feels a bit ridiculous but I see no reason not to do so.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* is_open_map_barycentric_coord

modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* surjective_barycentric_coord



## [2021-10-06 17:48:50](https://github.com/leanprover-community/mathlib/commit/a7b4e78)
fix(computability/DFA): tighten regular pumping lemma to match standard textbooks ([#9585](https://github.com/leanprover-community/mathlib/pull/9585))
This PR slightly tightens the regular pumping lemma: the current version applies only to words that are of length at least the number of states in the DFA plus one. Here we remove the plus one.
#### Estimated changes
modified src/computability/DFA.lean
- \+/\- *lemma* eval_from_split
- \+/\- *lemma* eval_from_split

modified src/computability/NFA.lean

modified src/computability/epsilon_NFA.lean



## [2021-10-06 15:46:06](https://github.com/leanprover-community/mathlib/commit/bcd13a7)
refactor(data/equiv): split out `./set` from `./basic` ([#9560](https://github.com/leanprover-community/mathlib/pull/9560))
This move all the equivalences between sets-coerced-to-types to a new file, which makes `equiv/basic` a slightly more manageable size.
The only non-move change in this PR is the rewriting of `equiv.of_bijective` to not go via `equiv.of_injective`, as we already have all the fields available directly and this allows the latter to move to a separate file.
This will allow us to import `order_dual.lean` earlier, as we no longer have to define boolean algebras before equivalences are available.
This relates to [#4758](https://github.com/leanprover-community/mathlib/pull/4758).
#### Estimated changes
modified src/algebra/group/ulift.lean

modified src/data/equiv/basic.lean
- \- *lemma* range_eq_univ
- \- *lemma* _root_.set.mem_image_equiv
- \- *lemma* _root_.set.image_equiv_eq_preimage_symm
- \- *lemma* _root_.set.preimage_equiv_eq_image_symm
- \- *lemma* symm_image_image
- \- *lemma* eq_image_iff_symm_image_eq
- \- *lemma* image_symm_image
- \- *lemma* image_preimage
- \- *lemma* preimage_image
- \- *lemma* symm_preimage_preimage
- \- *lemma* preimage_symm_preimage
- \- *lemma* preimage_subset
- \- *lemma* image_subset
- \- *lemma* image_eq_iff_eq
- \- *lemma* preimage_eq_iff_eq_image
- \- *lemma* eq_preimage_iff_image_eq
- \- *lemma* prod_assoc_preimage
- \- *lemma* union_apply_left
- \- *lemma* union_apply_right
- \- *lemma* union_symm_apply_left
- \- *lemma* union_symm_apply_right
- \- *lemma* insert_symm_apply_inl
- \- *lemma* insert_symm_apply_inr
- \- *lemma* insert_apply_left
- \- *lemma* insert_apply_right
- \- *lemma* sum_compl_apply_inl
- \- *lemma* sum_compl_apply_inr
- \- *lemma* sum_compl_symm_apply_of_mem
- \- *lemma* sum_compl_symm_apply_of_not_mem
- \- *lemma* sum_compl_symm_apply
- \- *lemma* sum_compl_symm_apply_compl
- \- *lemma* sum_diff_subset_apply_inl
- \- *lemma* sum_diff_subset_apply_inr
- \- *lemma* sum_diff_subset_symm_apply_of_mem
- \- *lemma* sum_diff_subset_symm_apply_of_not_mem
- \- *lemma* image_symm_preimage
- \- *lemma* self_comp_of_injective_symm
- \- *lemma* of_left_inverse_eq_of_injective
- \- *lemma* of_left_inverse'_eq_of_injective
- \- *lemma* dite_comp_equiv_update
- \- *theorem* apply_of_injective_symm
- \- *theorem* of_injective_symm_apply
- \- *def* set_prod_equiv_sigma
- \- *def* set_congr
- \- *def* image
- \- *def* of_left_inverse

modified src/data/equiv/local_equiv.lean

modified src/data/equiv/mul_add.lean

created src/data/equiv/set.lean
- \+ *lemma* range_eq_univ
- \+ *lemma* _root_.set.mem_image_equiv
- \+ *lemma* _root_.set.image_equiv_eq_preimage_symm
- \+ *lemma* _root_.set.preimage_equiv_eq_image_symm
- \+ *lemma* symm_image_image
- \+ *lemma* eq_image_iff_symm_image_eq
- \+ *lemma* image_symm_image
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+ *lemma* symm_preimage_preimage
- \+ *lemma* preimage_symm_preimage
- \+ *lemma* preimage_subset
- \+ *lemma* image_subset
- \+ *lemma* image_eq_iff_eq
- \+ *lemma* preimage_eq_iff_eq_image
- \+ *lemma* eq_preimage_iff_image_eq
- \+ *lemma* prod_assoc_preimage
- \+ *lemma* union_apply_left
- \+ *lemma* union_apply_right
- \+ *lemma* union_symm_apply_left
- \+ *lemma* union_symm_apply_right
- \+ *lemma* insert_symm_apply_inl
- \+ *lemma* insert_symm_apply_inr
- \+ *lemma* insert_apply_left
- \+ *lemma* insert_apply_right
- \+ *lemma* sum_compl_apply_inl
- \+ *lemma* sum_compl_apply_inr
- \+ *lemma* sum_compl_symm_apply_of_mem
- \+ *lemma* sum_compl_symm_apply_of_not_mem
- \+ *lemma* sum_compl_symm_apply
- \+ *lemma* sum_compl_symm_apply_compl
- \+ *lemma* sum_diff_subset_apply_inl
- \+ *lemma* sum_diff_subset_apply_inr
- \+ *lemma* sum_diff_subset_symm_apply_of_mem
- \+ *lemma* sum_diff_subset_symm_apply_of_not_mem
- \+ *lemma* image_symm_preimage
- \+ *lemma* self_comp_of_injective_symm
- \+ *lemma* of_left_inverse_eq_of_injective
- \+ *lemma* of_left_inverse'_eq_of_injective
- \+ *lemma* dite_comp_equiv_update
- \+ *theorem* apply_of_injective_symm
- \+ *theorem* of_injective_symm_apply
- \+ *def* set_prod_equiv_sigma
- \+ *def* set_congr
- \+ *def* image
- \+ *def* of_left_inverse

modified src/data/part.lean

modified src/logic/embedding.lean

modified src/logic/small.lean

modified src/order/order_dual.lean

modified src/order/rel_iso.lean



## [2021-10-06 15:46:04](https://github.com/leanprover-community/mathlib/commit/0b356b0)
feat(analysis/normed_space/banach): open mapping theorem for maps between affine spaces ([#9540](https://github.com/leanprover-community/mathlib/pull/9540))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/normed_space/banach.lean
- \+ *lemma* open_mapping_affine

modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* surjective_iff_linear_surjective



## [2021-10-06 15:46:03](https://github.com/leanprover-community/mathlib/commit/5773bc6)
feat(group_theory/group_action/conj_act): conjugation action of groups ([#8627](https://github.com/leanprover-community/mathlib/pull/8627))
#### Estimated changes
modified src/data/equiv/mul_add_aut.lean

created src/group_theory/group_action/conj_act.lean
- \+ *lemma* card
- \+ *lemma* of_mul_symm_eq
- \+ *lemma* to_mul_symm_eq
- \+ *lemma* to_conj_act_of_conj_act
- \+ *lemma* of_conj_act_to_conj_act
- \+ *lemma* of_conj_act_one
- \+ *lemma* to_conj_act_one
- \+ *lemma* of_conj_act_inv
- \+ *lemma* to_conj_act_inv
- \+ *lemma* of_conj_act_mul
- \+ *lemma* to_conj_act_mul
- \+ *lemma* smul_def
- \+ *lemma* «forall»
- \+ *lemma* of_conj_act_zero
- \+ *lemma* to_conj_act_zero
- \+ *lemma* smul_eq_mul_aut_conj
- \+ *lemma* fixed_points_eq_center
- \+ *def* conj_act
- \+ *def* of_conj_act
- \+ *def* to_conj_act



## [2021-10-06 14:53:28](https://github.com/leanprover-community/mathlib/commit/6abd6f2)
chore(ring_theory/witt_vector): fix a docstring ([#9575](https://github.com/leanprover-community/mathlib/pull/9575))
#### Estimated changes
modified src/ring_theory/witt_vector/frobenius.lean

modified src/ring_theory/witt_vector/structure_polynomial.lean



## [2021-10-06 13:44:03](https://github.com/leanprover-community/mathlib/commit/850d5d2)
feat(analysis/convex/function): Dual lemmas ([#9571](https://github.com/leanprover-community/mathlib/pull/9571))
#### Estimated changes
modified src/analysis/convex/function.lean
- \+ *lemma* convex_on.dual
- \+ *lemma* concave_on.dual
- \+ *lemma* strict_convex_on.dual
- \+ *lemma* strict_concave_on.dual
- \+ *lemma* concave_on.convex_gt
- \+ *lemma* concave_on.ge_on_segment'
- \+ *lemma* concave_on.ge_on_segment
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* concave_on.smul
- \- *lemma* concave_on.convex_lt
- \- *lemma* concave_on.le_on_segment'
- \- *lemma* concave_on.le_on_segment
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* concave_on.smul



## [2021-10-06 10:12:02](https://github.com/leanprover-community/mathlib/commit/8c65781)
refactor(data/nat/basic): remove sub lemmas ([#9544](https://github.com/leanprover-community/mathlib/pull/9544))
* Remove the nat sub lemmas that are special cases of lemmas in `algebra/order/sub`
* This PR does 90% of the work, some lemmas require a bit more work (which will be done in a future PR)
* Protect `ordinal.add_sub_cancel_of_le`
* Most fixes in other files were abuses of the definitional equality of `n < m` and `nat.succ n \le m`.
* [This](https://github.com/leanprover-community/mathlib/blob/7a5d15a955a92a90e1d398b2281916b9c41270b2/src/data/nat/basic.lean#L498-L611) gives the list of renamings.
* The regex to find 90+% of the occurrences of removed lemmas. Some lemmas were not protected, so might not be found this way.
```
nat.(le_sub_add|add_sub_cancel'|sub_add_sub_cancel|sub_cancel|sub_sub_sub_cancel_right|sub_add_eq_add_sub|sub_sub_assoc|lt_of_sub_pos|lt_of_sub_lt_sub_right|lt_of_sub_lt_sub_left|sub_lt_self|le_sub_right_of_add_le|le_sub_left_of_add_le|lt_sub_right_of_add_lt|lt_sub_left_of_add_lt|add_lt_of_lt_sub_right|add_lt_of_lt_sub_left|le_add_of_sub_le_right|le_add_of_sub_le_left|lt_add_of_sub_lt_right|lt_add_of_sub_lt_left|sub_le_left_of_le_add|sub_le_right_of_le_add|sub_lt_left_iff_lt_add|le_sub_left_iff_add_le|le_sub_right_iff_add_le|lt_sub_left_iff_add_lt|lt_sub_right_iff_add_lt|sub_lt_right_iff_lt_add|sub_le_sub_left_iff|sub_lt_sub_right_iff|sub_lt_sub_left_iff|sub_le_iff|sub_lt_iff)[^_]
```
#### Estimated changes
modified archive/100-theorems-list/73_ascending_descending_sequences.lean

modified archive/imo/imo1977_q6.lean

modified archive/imo/imo1998_q2.lean

modified archive/oxford_invariants/2021summer/week3_p1.lean

modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/big_operators/intervals.lean

modified src/algebra/geom_sum.lean

modified src/algebra/linear_recurrence.lean

modified src/algebra/pointwise.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/combinatorics/composition.lean

modified src/combinatorics/derangements/exponential.lean

modified src/combinatorics/derangements/finite.lean

modified src/computability/DFA.lean

modified src/computability/turing_machine.lean

modified src/data/complex/exponential.lean

modified src/data/equiv/denumerable.lean

modified src/data/equiv/fin.lean

modified src/data/fin.lean

modified src/data/finset/basic.lean

modified src/data/finset/intervals.lean

modified src/data/finset/sort.lean

modified src/data/list/basic.lean

modified src/data/list/cycle.lean

modified src/data/list/intervals.lean

modified src/data/list/perm.lean

modified src/data/list/rotate.lean

modified src/data/matrix/notation.lean

modified src/data/multiset/basic.lean

modified src/data/nat/basic.lean
- \- *lemma* sub_sub_sub_cancel_right
- \- *theorem* sub_cancel
- \- *theorem* sub_sub_assoc

modified src/data/nat/choose/basic.lean

modified src/data/nat/dist.lean

modified src/data/nat/factorial/basic.lean

modified src/data/nat/interval.lean

modified src/data/nat/modeq.lean

modified src/data/nat/multiplicity.lean

modified src/data/nat/pairing.lean

modified src/data/nat/prime.lean

modified src/data/nat/sqrt.lean

modified src/data/nat/upto.lean

modified src/data/ordmap/ordset.lean

modified src/data/polynomial/hasse_deriv.lean

modified src/data/polynomial/mirror.lean

modified src/data/polynomial/reverse.lean

modified src/data/zmod/basic.lean

modified src/field_theory/finite/polynomial.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/list.lean

modified src/group_theory/specific_groups/alternating.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/matrix/nonsingular_inverse.lean

modified src/number_theory/bernoulli.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/class_number/admissible_card_pow_degree.lean

modified src/number_theory/padics/ring_homs.lean

modified src/order/filter/at_top_bot.lean

modified src/order/iterate.lean

modified src/order/well_founded_set.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/witt_vector/frobenius.lean

modified src/set_theory/game/state.lean

modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* add_sub_cancel_of_le

modified src/set_theory/ordinal_notation.lean

modified src/system/random/basic.lean

modified src/tactic/omega/coeffs.lean

modified src/testing/slim_check/gen.lean

modified src/testing/slim_check/sampleable.lean

modified test/general_recursion.lean



## [2021-10-06 10:12:00](https://github.com/leanprover-community/mathlib/commit/facc1d2)
feat(topology/algebra): topology on a linear_ordered_comm_group_with_zero ([#9537](https://github.com/leanprover-community/mathlib/pull/9537))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
modified src/algebra/order/with_zero.lean
- \+ *lemma* inv_mul_lt_of_lt_mul₀

created src/topology/algebra/with_zero_topology.lean
- \+ *lemma* directed_lt
- \+ *lemma* pure_le_nhds_fun
- \+ *lemma* nhds_fun_ok
- \+ *lemma* nhds_coe_units
- \+ *lemma* nhds_of_ne_zero
- \+ *lemma* singleton_nhds_of_units
- \+ *lemma* singleton_nhds_of_ne_zero
- \+ *lemma* has_basis_nhds_zero
- \+ *lemma* nhds_zero_of_units
- \+ *lemma* tendsto_zero
- \+ *lemma* nhds_zero_of_ne_zero
- \+ *lemma* has_basis_nhds_units
- \+ *lemma* has_basis_nhds_of_ne_zero
- \+ *lemma* tendsto_units
- \+ *lemma* tendsto_of_ne_zero
- \+ *def* nhds_fun

modified src/topology/basic.lean
- \+ *lemma* is_closed.compl_mem_nhds



## [2021-10-06 08:03:57](https://github.com/leanprover-community/mathlib/commit/b534fed)
refactor(analysis/{normed_space, inner_product_space}/dual): redefine using `linear_isometry` ([#9569](https://github.com/leanprover-community/mathlib/pull/9569))
Linear isometric embeddings appear naturally when studying the duals of normed spaces:  the map `λ y, ⟪x, y⟫` from an inner product space to its dual is a linear isometric embedding++, and so is the canonical map from a normed space to its double dual**.
When these natural maps were defined last year, we didn't have the definition `linear_isometry` (notation: `X →ₗᵢ[R] Y`), so they were defined as continuous linear maps which satisfied the predicate `isometry`, and several lemmas were proven ad-hoc which are now available as general lemmas about  `linear_isometry`.
This PR refactors to use the `linear_isometry` structure.  Lemmas deleted (I have been enthusiastic here, and can scale back if desired ...):
normed_space.inclusion_in_double_dual_isometry
inner_product_space.to_dual_map_isometry
inner_product_space.to_dual_map_injective
inner_product_space.ker_to_dual_map
inner_product_space.to_dual_map_eq_iff_eq 
inner_product_space.range_to_dual_map
inner_product_space.isometric.to_dual
inner_product_space.to_dual_eq_iff_eq
inner_product_space.to_dual_eq_iff_eq'
inner_product_space.norm_to_dual_apply
inner_product_space.norm_to_dual_symm_apply
++ (over `ℝ` -- over `ℂ` it's conjugate-linear, which will be dealt with in future PRs)
** over `ℝ` or `ℂ`
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/analysis/inner_product_space/dual.lean
- \+/\- *lemma* to_dual_map_apply
- \+/\- *lemma* to_dual_apply
- \+/\- *lemma* to_dual_map_apply
- \- *lemma* norm_to_dual_map_apply
- \- *lemma* to_dual_map_isometry
- \- *lemma* to_dual_map_injective
- \- *lemma* ker_to_dual_map
- \- *lemma* to_dual_map_eq_iff_eq
- \- *lemma* range_to_dual_map
- \+/\- *lemma* to_dual_apply
- \- *lemma* to_dual_eq_iff_eq
- \- *lemma* to_dual_eq_iff_eq'
- \- *lemma* norm_to_dual_apply
- \- *lemma* norm_to_dual_symm_apply
- \+/\- *def* to_dual_map
- \+/\- *def* to_dual
- \+/\- *def* to_dual_map
- \+/\- *def* to_dual
- \- *def* isometric.to_dual

modified src/analysis/normed_space/dual.lean
- \- *lemma* inclusion_in_double_dual_isometry
- \+ *def* inclusion_in_double_dual_li

modified src/analysis/normed_space/linear_isometry.lean



## [2021-10-06 08:03:56](https://github.com/leanprover-community/mathlib/commit/e52e533)
feat(order/bounds): Antitone lemmas ([#9556](https://github.com/leanprover-community/mathlib/pull/9556))
#### Estimated changes
modified src/order/bounds.lean
- \+ *lemma* mem_upper_bounds_image
- \+ *lemma* mem_lower_bounds_image
- \+ *lemma* image_lower_bounds_subset_upper_bounds_image
- \+ *lemma* image_upper_bounds_subset_lower_bounds_image
- \+ *lemma* map_bdd_above
- \+ *lemma* map_bdd_below
- \+ *lemma* map_is_greatest
- \+ *lemma* map_is_least
- \+ *lemma* is_lub_image_le
- \+ *lemma* le_is_glb_image



## [2021-10-06 06:05:04](https://github.com/leanprover-community/mathlib/commit/f811910)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are 1 in zero dimensions ([#9564](https://github.com/leanprover-community/mathlib/pull/9564))
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* subsingleton_of_univ_subsingleton
- \+ *lemma* subsingleton_univ_iff

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* subsingleton_of_subsingleton_span_eq_top

modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* coe_barycentric_coord_of_subsingleton_eq_one



## [2021-10-06 01:36:04](https://github.com/leanprover-community/mathlib/commit/db5ee76)
chore(linear_algebra/quadratic_form): squeeze simps ([#9572](https://github.com/leanprover-community/mathlib/pull/9572))
[#9567](https://github.com/leanprover-community/mathlib/pull/9567) speeds up the slowest declaration in the file, but many other declarations are also slow.
This PR squeezes all simps.
#### Estimated changes
modified src/linear_algebra/quadratic_form.lean



## [2021-10-05 21:57:44](https://github.com/leanprover-community/mathlib/commit/fdf8a71)
feat(topology/bases): a family of nonempty disjoint open sets is countable in a separable space ([#9557](https://github.com/leanprover-community/mathlib/pull/9557))
Together with unrelated small lemmas on balls and on `pairwise_on`.
#### Estimated changes
modified src/analysis/normed_space/riesz_lemma.lean

modified src/data/real/ennreal.lean
- \+ *theorem* sum_lt_sum_of_nonempty
- \+ *theorem* exists_le_of_sum_le

modified src/data/set/basic.lean
- \+ *lemma* pairwise_on_disjoint_on_mono

modified src/data/set/lattice.lean
- \+ *lemma* pairwise_on_Union

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/bases.lean
- \+ *lemma* countable_of_is_open_of_disjoint
- \+ *lemma* countable_of_nonempty_interior_of_disjoint

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* disjoint_closed_ball_of_lt_inf_edist
- \+ *lemma* disjoint_closed_ball_of_lt_inf_dist
- \+ *lemma* _root_.is_closed.mem_iff_inf_dist_zero
- \+ *lemma* _root_.is_closed.not_mem_iff_inf_dist_pos
- \+ *lemma* _root_.is_closed.Hausdorff_dist_zero_iff_eq
- \- *lemma* mem_iff_inf_dist_zero_of_closed
- \- *lemma* Hausdorff_dist_zero_iff_eq_of_closed



## [2021-10-05 21:57:43](https://github.com/leanprover-community/mathlib/commit/815eaca)
feat(analysis/normed_space/affine_isometry): affine maps are open iff their underlying linear maps are ([#9538](https://github.com/leanprover-community/mathlib/pull/9538))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* affine_map.is_open_map_linear_iff

modified src/topology/algebra/affine.lean

modified src/topology/homeomorph.lean
- \+ *lemma* comp_is_open_map_iff
- \+ *lemma* comp_is_open_map_iff'



## [2021-10-05 19:53:22](https://github.com/leanprover-community/mathlib/commit/63903f2)
doc(linear_algebra/free_module/strong_rank_condition): correct a typo ([#9565](https://github.com/leanprover-community/mathlib/pull/9565))
#### Estimated changes
modified src/linear_algebra/free_module/strong_rank_condition.lean



## [2021-10-05 19:53:21](https://github.com/leanprover-community/mathlib/commit/0b57520)
feat(order/bounds): Image under an `order_iso` and `upper_bounds` commute ([#9555](https://github.com/leanprover-community/mathlib/pull/9555))
#### Estimated changes
modified src/order/bounds.lean
- \+ *lemma* image_upper_bounds_subset_upper_bounds_image
- \+ *lemma* image_lower_bounds_subset_lower_bounds_image
- \+ *lemma* upper_bounds_image
- \+ *lemma* lower_bounds_image
- \+/\- *lemma* is_lub_image
- \+/\- *lemma* is_lub_image'
- \+/\- *lemma* is_glb_image
- \+/\- *lemma* is_glb_image'
- \+/\- *lemma* is_lub_preimage
- \+/\- *lemma* is_lub_preimage'
- \+/\- *lemma* is_glb_preimage
- \+/\- *lemma* is_glb_preimage'
- \+/\- *lemma* is_lub_image
- \+/\- *lemma* is_lub_image'
- \+/\- *lemma* is_glb_image
- \+/\- *lemma* is_glb_image'
- \+/\- *lemma* is_lub_preimage
- \+/\- *lemma* is_lub_preimage'
- \+/\- *lemma* is_glb_preimage
- \+/\- *lemma* is_glb_preimage'

modified src/order/galois_connection.lean
- \- *lemma* upper_bounds_image
- \- *lemma* lower_bounds_image



## [2021-10-05 19:53:20](https://github.com/leanprover-community/mathlib/commit/111d73b)
feat(data/int/interval): Finite intervals in ℤ ([#9526](https://github.com/leanprover-community/mathlib/pull/9526))
This proves that `ℤ` is a locally finite order.
#### Estimated changes
modified src/algebra/char_zero.lean
- \+ *def* cast_embedding

created src/data/int/interval.lean
- \+ *lemma* Icc_eq_finset_map
- \+ *lemma* Ioc_eq_finset_map
- \+ *lemma* Ioo_eq_finset_map
- \+ *lemma* card_Icc
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *lemma* card_Icc_of_le
- \+ *lemma* card_Ioc_of_le
- \+ *lemma* card_Ioo_of_lt
- \+ *lemma* card_fintype_Icc
- \+ *lemma* card_fintype_Ioc
- \+ *lemma* card_fintype_Ioo
- \+ *lemma* card_fintype_Icc_of_le
- \+ *lemma* card_fintype_Ioc_of_le
- \+ *lemma* card_fintype_Ioo_of_lt



## [2021-10-05 17:44:36](https://github.com/leanprover-community/mathlib/commit/7455f47)
chore(linear_algebra/quadratic_form): speed up quadratic_form.lin_mul_lin ([#9567](https://github.com/leanprover-community/mathlib/pull/9567))
In my single profiler run, this reduced elaboration time from 20s to 1.5s.
#### Estimated changes
modified src/linear_algebra/quadratic_form.lean



## [2021-10-05 11:41:22](https://github.com/leanprover-community/mathlib/commit/5926f10)
fix(data/equiv/basic): use `subtype p` not `coe_sort (set_of p)` ([#9559](https://github.com/leanprover-community/mathlib/pull/9559))
`↥{x | p x}` is just a clumsy way to write `{x // p x}`.
#### Estimated changes
modified src/data/equiv/basic.lean



## [2021-10-05 10:10:30](https://github.com/leanprover-community/mathlib/commit/da4d550)
chore(measure_theory/*): better names and notations, add easy lemmas ([#9554](https://github.com/leanprover-community/mathlib/pull/9554))
* Localize notation for absolutely continuous in the `measure_theory` namespace, and add separate notations for the case of measures and of vector measures.
* Standardize some names, using `measure` instead of `meas`.
* Add two lemmas on measures with density.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measure_interior_of_null_bdry
- \+ *lemma* measure_closure_of_null_bdry
- \- *lemma* meas_interior_of_null_bdry
- \- *lemma* meas_closure_of_null_bdry

modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/decomposition/radon_nikodym.lean

modified src/measure_theory/function/ess_sup.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* with_density_one
- \+ *lemma* with_density_mul
- \+ *lemma* exists_absolutely_continuous_is_finite_measure

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_diff_le_iff_le_add
- \+ *lemma* measure_eq_measure_of_null_diff
- \+ *lemma* measure_eq_measure_of_between_null_diff
- \+ *lemma* measure_eq_measure_smaller_of_between_null_diff
- \+ *lemma* measure_eq_measure_larger_of_between_null_diff
- \- *lemma* meas_eq_meas_of_null_diff
- \- *lemma* meas_eq_meas_of_between_null_diff
- \- *lemma* meas_eq_meas_smaller_of_between_null_diff
- \- *lemma* meas_eq_meas_larger_of_between_null_diff

modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_Union_fintype_le

modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* mk
- \+/\- *lemma* eq
- \+/\- *lemma* refl
- \+/\- *lemma* trans
- \+/\- *lemma* zero
- \+/\- *lemma* map
- \+/\- *lemma* mk
- \+/\- *lemma* eq
- \+/\- *lemma* refl
- \+/\- *lemma* trans
- \+/\- *lemma* zero
- \+/\- *lemma* map

modified src/measure_theory/measure/with_density_vector_measure.lean



## [2021-10-05 10:10:29](https://github.com/leanprover-community/mathlib/commit/e7ea02f)
feat(analysis/convex/basic): Levels of a monotone/antitone function ([#9547](https://github.com/leanprover-community/mathlib/pull/9547))
The set of points whose image under a monotone function is less than a fixed value is convex, when the space is linear.
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+ *lemma* segment_subset_interval
- \+ *lemma* convex.min_le_combo
- \+ *lemma* convex.combo_le_max
- \+ *lemma* monotone_on.convex_le
- \+ *lemma* monotone_on.convex_lt
- \+ *lemma* monotone_on.convex_ge
- \+ *lemma* monotone_on.convex_gt
- \+ *lemma* antitone_on.convex_le
- \+ *lemma* antitone_on.convex_lt
- \+ *lemma* antitone_on.convex_ge
- \+ *lemma* antitone_on.convex_gt
- \+ *lemma* monotone.convex_le
- \+ *lemma* monotone.convex_lt
- \+ *lemma* monotone.convex_ge
- \+ *lemma* monotone.convex_gt
- \+ *lemma* antitone.convex_le
- \+ *lemma* antitone.convex_lt
- \+ *lemma* antitone.convex_ge
- \+ *lemma* antitone.convex_gt



## [2021-10-05 10:10:28](https://github.com/leanprover-community/mathlib/commit/5b79319)
feat(ring_theory/polynomial/basic): add a lemma `polynomial_quotient_equiv_quotient_polynomial_map_mk` ([#9542](https://github.com/leanprover-community/mathlib/pull/9542))
#### Estimated changes
modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial_quotient_equiv_quotient_polynomial_symm_mk
- \+ *lemma* polynomial_quotient_equiv_quotient_polynomial_map_mk



## [2021-10-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/2666033)
refactor(algebra/gcd_monoid): don't require normalization ([#9443](https://github.com/leanprover-community/mathlib/pull/9443))
This will allow us to set up a gcd_monoid instance for all euclidean_domains and generalize the results in ring_theory/euclidean_domain.lean to PIDs.
#### Estimated changes
modified docs/overview.yaml

modified src/algebra/associated.lean
- \+ *lemma* associated_mul_unit_left
- \+ *lemma* associated_unit_mul_left
- \+ *lemma* associated_mul_unit_right
- \+ *lemma* associated_unit_mul_right
- \+ *lemma* units_eq_one

modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* dvd_gcd_mul_of_dvd_mul
- \+/\- *lemma* dvd_mul_gcd_of_dvd_mul
- \+/\- *lemma* exists_dvd_and_dvd_of_dvd_mul
- \+/\- *lemma* lcm_dvd_iff
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right
- \+/\- *lemma* lcm_dvd
- \+/\- *lemma* normalize_lcm
- \+/\- *lemma* lcm_eq_normalize
- \+/\- *lemma* dvd_gcd_mul_of_dvd_mul
- \+/\- *lemma* dvd_mul_gcd_of_dvd_mul
- \+/\- *lemma* exists_dvd_and_dvd_of_dvd_mul
- \+/\- *lemma* lcm_dvd_iff
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right
- \+/\- *lemma* lcm_dvd
- \+/\- *lemma* normalize_lcm
- \+/\- *lemma* lcm_eq_normalize
- \- *lemma* units_eq_one
- \+/\- *theorem* normalize_gcd
- \+/\- *theorem* gcd_mul_lcm
- \+/\- *theorem* dvd_gcd_iff
- \+/\- *theorem* gcd_comm
- \+ *theorem* gcd_comm'
- \+/\- *theorem* gcd_assoc
- \+ *theorem* gcd_assoc'
- \+/\- *theorem* gcd_eq_normalize
- \+/\- *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_left'
- \+/\- *theorem* gcd_zero_right
- \+ *theorem* gcd_zero_right'
- \+/\- *theorem* gcd_eq_zero_iff
- \+/\- *theorem* gcd_one_left
- \+ *theorem* gcd_one_left'
- \+/\- *theorem* gcd_one_right
- \+ *theorem* gcd_one_right'
- \+/\- *theorem* gcd_dvd_gcd
- \+/\- *theorem* gcd_same
- \+/\- *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_left'
- \+/\- *theorem* gcd_mul_right
- \+ *theorem* gcd_mul_right'
- \+/\- *theorem* gcd_eq_left_iff
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* gcd_dvd_gcd_mul_left
- \+/\- *theorem* gcd_dvd_gcd_mul_right
- \+/\- *theorem* gcd_dvd_gcd_mul_left_right
- \+/\- *theorem* gcd_dvd_gcd_mul_right_right
- \+/\- *theorem* associated.gcd_eq_left
- \+/\- *theorem* associated.gcd_eq_right
- \+/\- *theorem* gcd_mul_dvd_mul_gcd
- \+/\- *theorem* gcd_pow_right_dvd_pow_gcd
- \+/\- *theorem* gcd_pow_left_dvd_pow_gcd
- \+/\- *theorem* pow_dvd_of_mul_eq_pow
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow
- \+/\- *theorem* lcm_eq_zero_iff
- \+/\- *theorem* lcm_comm
- \+ *theorem* lcm_comm'
- \+/\- *theorem* lcm_assoc
- \+ *theorem* lcm_assoc'
- \+/\- *theorem* lcm_dvd_lcm
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_eq_one_iff
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_eq_left_iff
- \+/\- *theorem* lcm_eq_right_iff
- \+/\- *theorem* lcm_dvd_lcm_mul_left
- \+/\- *theorem* lcm_dvd_lcm_mul_right
- \+/\- *theorem* lcm_dvd_lcm_mul_left_right
- \+/\- *theorem* lcm_dvd_lcm_mul_right_right
- \+/\- *theorem* lcm_eq_of_associated_left
- \+/\- *theorem* lcm_eq_of_associated_right
- \+/\- *theorem* prime_of_irreducible
- \+/\- *theorem* irreducible_iff_prime
- \+/\- *theorem* normalize_gcd
- \+/\- *theorem* gcd_mul_lcm
- \+/\- *theorem* dvd_gcd_iff
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_assoc
- \+/\- *theorem* gcd_eq_normalize
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \+/\- *theorem* gcd_eq_zero_iff
- \+/\- *theorem* gcd_one_left
- \+/\- *theorem* gcd_one_right
- \+/\- *theorem* gcd_dvd_gcd
- \+/\- *theorem* gcd_same
- \+/\- *theorem* gcd_mul_left
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* gcd_eq_left_iff
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* gcd_dvd_gcd_mul_left
- \+/\- *theorem* gcd_dvd_gcd_mul_right
- \+/\- *theorem* gcd_dvd_gcd_mul_left_right
- \+/\- *theorem* gcd_dvd_gcd_mul_right_right
- \+/\- *theorem* associated.gcd_eq_left
- \+/\- *theorem* associated.gcd_eq_right
- \+/\- *theorem* gcd_mul_dvd_mul_gcd
- \+/\- *theorem* gcd_pow_right_dvd_pow_gcd
- \+/\- *theorem* gcd_pow_left_dvd_pow_gcd
- \+/\- *theorem* pow_dvd_of_mul_eq_pow
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow
- \+/\- *theorem* lcm_eq_zero_iff
- \+/\- *theorem* lcm_comm
- \+/\- *theorem* lcm_assoc
- \+/\- *theorem* lcm_dvd_lcm
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_eq_one_iff
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_eq_left_iff
- \+/\- *theorem* lcm_eq_right_iff
- \+/\- *theorem* lcm_dvd_lcm_mul_left
- \+/\- *theorem* lcm_dvd_lcm_mul_right
- \+/\- *theorem* lcm_dvd_lcm_mul_left_right
- \+/\- *theorem* lcm_dvd_lcm_mul_right_right
- \+/\- *theorem* lcm_eq_of_associated_left
- \+/\- *theorem* lcm_eq_of_associated_right
- \+/\- *theorem* prime_of_irreducible
- \+/\- *theorem* irreducible_iff_prime

modified src/algebra/gcd_monoid/finset.lean

modified src/algebra/gcd_monoid/multiset.lean

modified src/field_theory/minpoly.lean

modified src/ring_theory/int/basic.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* exists_mem_factors_of_dvd
- \+/\- *lemma* normalized_factors_zero
- \+/\- *lemma* sup_mul_inf
- \+/\- *lemma* factors_one
- \+/\- *lemma* count_pow
- \+ *lemma* associates.quot_out
- \+/\- *lemma* normalized_factors_zero
- \+/\- *lemma* sup_mul_inf
- \+/\- *lemma* factors_one
- \+/\- *lemma* count_pow
- \+ *theorem* factors_prod
- \+ *theorem* prime_of_factor
- \+ *theorem* irreducible_of_factor
- \+/\- *theorem* prod_le_prod_iff_le
- \+/\- *theorem* prod_factors
- \+/\- *theorem* eq_of_prod_eq_prod
- \+/\- *theorem* factors_mul
- \+/\- *theorem* factors_mono
- \+/\- *theorem* factors_le
- \+/\- *theorem* prod_le
- \+/\- *theorem* coprime_iff_inf_one
- \+/\- *theorem* factors_prime_pow
- \+/\- *theorem* prime_pow_dvd_iff_le
- \+/\- *theorem* le_of_count_ne_zero
- \+/\- *theorem* count_mul
- \+/\- *theorem* count_of_coprime
- \+/\- *theorem* count_mul_of_coprime
- \+/\- *theorem* count_mul_of_coprime'
- \+/\- *theorem* dvd_count_of_dvd_count_mul
- \+/\- *theorem* pow_factors
- \+/\- *theorem* dvd_count_pow
- \+/\- *theorem* is_pow_of_dvd_count
- \+/\- *theorem* eq_pow_of_mul_eq_pow
- \+/\- *theorem* prod_le_prod_iff_le
- \+/\- *theorem* prod_factors
- \+/\- *theorem* eq_of_prod_eq_prod
- \+/\- *theorem* factors_mul
- \+/\- *theorem* factors_mono
- \+/\- *theorem* factors_le
- \+/\- *theorem* prod_le
- \+/\- *theorem* coprime_iff_inf_one
- \+/\- *theorem* factors_prime_pow
- \+/\- *theorem* prime_pow_dvd_iff_le
- \+/\- *theorem* le_of_count_ne_zero
- \+/\- *theorem* count_mul
- \+/\- *theorem* count_of_coprime
- \+/\- *theorem* count_mul_of_coprime
- \+/\- *theorem* count_mul_of_coprime'
- \+/\- *theorem* dvd_count_of_dvd_count_mul
- \+/\- *theorem* pow_factors
- \+/\- *theorem* dvd_count_pow
- \+/\- *theorem* is_pow_of_dvd_count
- \+/\- *theorem* eq_pow_of_mul_eq_pow



## [2021-10-05 08:58:55](https://github.com/leanprover-community/mathlib/commit/def4814)
refactor(topology/algebra/module): continuous semilinear maps ([#9539](https://github.com/leanprover-community/mathlib/pull/9539))
Generalize the theory of continuous linear maps to the semilinear setting.
We introduce a notation `∘L` for composition of continuous linear (i.e., not semilinear) maps, used sporadically to help with unification.  See [#8857](https://github.com/leanprover-community/mathlib/pull/8857) for a discussion of a related problem and fix.
#### Estimated changes
modified src/analysis/complex/conformal.lean

modified src/analysis/normed_space/complemented.lean

modified src/topology/algebra/module.lean
- \+/\- *lemma* to_linear_map_eq_coe
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_mk'
- \+/\- *lemma* coe_inj
- \+/\- *lemma* map_zero
- \+ *lemma* map_smulₛₗ
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_sum
- \+/\- *lemma* coe_coe
- \+/\- *lemma* eq_on_closure_span
- \+/\- *lemma* ext_on
- \+/\- *lemma* _root_.submodule.topological_closure_map
- \+/\- *lemma* _root_.dense_range.topological_closure_map_submodule
- \+/\- *lemma* default_def
- \+/\- *lemma* zero_apply
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* one_def
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_id'
- \+/\- *lemma* coe_eq_id
- \+/\- *lemma* one_apply
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_sum
- \+/\- *lemma* coe_sum'
- \+/\- *lemma* sum_apply
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* comp_apply
- \+/\- *lemma* mul_def
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_apply
- \+/\- *lemma* coe_prod
- \+/\- *lemma* prod_apply
- \+/\- *lemma* inl_apply
- \+/\- *lemma* inr_apply
- \+/\- *lemma* coe_inl
- \+/\- *lemma* coe_inr
- \+/\- *lemma* ker_coe
- \+/\- *lemma* mem_ker
- \+/\- *lemma* is_closed_ker
- \+/\- *lemma* ker_prod
- \+/\- *lemma* range_coe
- \+/\- *lemma* mem_range
- \+/\- *lemma* mem_range_self
- \+/\- *lemma* range_prod_le
- \+/\- *lemma* coe_cod_restrict
- \+/\- *lemma* coe_cod_restrict_apply
- \+/\- *lemma* ker_cod_restrict
- \+/\- *lemma* coe_subtype_val
- \+/\- *lemma* subtype_val_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+/\- *lemma* fst_prod_snd
- \+/\- *lemma* fst_comp_prod
- \+/\- *lemma* snd_comp_prod
- \+/\- *lemma* coe_prod_map
- \+/\- *lemma* coe_prod_map'
- \+/\- *lemma* coe_coprod
- \+/\- *lemma* coprod_apply
- \+/\- *lemma* range_coprod
- \+/\- *lemma* smul_right_apply
- \+/\- *lemma* smul_right_one_one
- \+/\- *lemma* smul_right_comp
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_to_linear_equiv
- \+/\- *lemma* coe_coe
- \+/\- *lemma* to_linear_equiv_injective
- \+/\- *lemma* ext
- \+/\- *lemma* coe_injective
- \+/\- *lemma* coe_inj
- \+/\- *lemma* coe_to_homeomorph
- \+/\- *lemma* image_closure
- \+/\- *lemma* preimage_closure
- \+/\- *lemma* is_closed_image
- \+/\- *lemma* map_nhds_eq
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+ *lemma* map_smulₛₗ
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_eq_zero_iff
- \+/\- *lemma* ext₁
- \+/\- *lemma* symm_to_linear_equiv
- \+/\- *lemma* symm_to_homeomorph
- \+/\- *lemma* symm_map_nhds_eq
- \+/\- *lemma* trans_to_linear_equiv
- \+/\- *lemma* prod_apply
- \+/\- *lemma* coe_prod
- \+/\- *lemma* comp_coe
- \+/\- *lemma* symm_comp_self
- \+/\- *lemma* self_comp_symm
- \+/\- *lemma* symm_apply_eq
- \+/\- *lemma* eq_symm_apply
- \+/\- *lemma* equiv_of_inverse_apply
- \+/\- *lemma* symm_equiv_of_inverse
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* to_linear_map_eq_coe
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_mk'
- \+/\- *lemma* coe_inj
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_sum
- \+/\- *lemma* coe_coe
- \+/\- *lemma* eq_on_closure_span
- \+/\- *lemma* ext_on
- \+/\- *lemma* _root_.submodule.topological_closure_map
- \+/\- *lemma* _root_.dense_range.topological_closure_map_submodule
- \+/\- *lemma* default_def
- \+/\- *lemma* zero_apply
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* one_def
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_id'
- \+/\- *lemma* coe_eq_id
- \+/\- *lemma* one_apply
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_sum
- \+/\- *lemma* coe_sum'
- \+/\- *lemma* sum_apply
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* comp_apply
- \+/\- *lemma* mul_def
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_apply
- \+/\- *lemma* coe_prod
- \+/\- *lemma* prod_apply
- \+/\- *lemma* inl_apply
- \+/\- *lemma* inr_apply
- \+/\- *lemma* coe_inl
- \+/\- *lemma* coe_inr
- \+/\- *lemma* ker_coe
- \+/\- *lemma* mem_ker
- \+/\- *lemma* is_closed_ker
- \+/\- *lemma* ker_prod
- \+/\- *lemma* range_coe
- \+/\- *lemma* mem_range
- \+/\- *lemma* mem_range_self
- \+/\- *lemma* range_prod_le
- \+/\- *lemma* coe_cod_restrict
- \+/\- *lemma* coe_cod_restrict_apply
- \+/\- *lemma* ker_cod_restrict
- \+/\- *lemma* coe_subtype_val
- \+/\- *lemma* subtype_val_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+/\- *lemma* fst_prod_snd
- \+/\- *lemma* fst_comp_prod
- \+/\- *lemma* snd_comp_prod
- \+/\- *lemma* coe_prod_map
- \+/\- *lemma* coe_prod_map'
- \+/\- *lemma* coe_coprod
- \+/\- *lemma* coprod_apply
- \+/\- *lemma* range_coprod
- \+/\- *lemma* smul_right_apply
- \+/\- *lemma* smul_right_one_one
- \+/\- *lemma* smul_right_comp
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_to_linear_equiv
- \+/\- *lemma* coe_coe
- \+/\- *lemma* to_linear_equiv_injective
- \+/\- *lemma* ext
- \+/\- *lemma* coe_injective
- \+/\- *lemma* coe_inj
- \+/\- *lemma* coe_to_homeomorph
- \+/\- *lemma* image_closure
- \+/\- *lemma* preimage_closure
- \+/\- *lemma* is_closed_image
- \+/\- *lemma* map_nhds_eq
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_smul
- \+/\- *lemma* map_eq_zero_iff
- \+/\- *lemma* ext₁
- \+/\- *lemma* symm_to_linear_equiv
- \+/\- *lemma* symm_to_homeomorph
- \+/\- *lemma* symm_map_nhds_eq
- \+/\- *lemma* trans_to_linear_equiv
- \+/\- *lemma* prod_apply
- \+/\- *lemma* coe_prod
- \+/\- *lemma* comp_coe
- \+/\- *lemma* symm_comp_self
- \+/\- *lemma* self_comp_symm
- \+/\- *lemma* symm_apply_eq
- \+/\- *lemma* eq_symm_apply
- \+/\- *lemma* equiv_of_inverse_apply
- \+/\- *lemma* symm_equiv_of_inverse
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *theorem* coe_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext_ring
- \+/\- *theorem* ext_ring_iff
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_zero
- \+/\- *theorem* zero_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* coe_def_rev
- \+/\- *theorem* coe_apply
- \+/\- *theorem* bijective
- \+/\- *theorem* injective
- \+/\- *theorem* surjective
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* symm_trans_apply
- \+/\- *theorem* symm_image_image
- \+/\- *theorem* image_symm_image
- \+/\- *theorem* coe_comp_coe_symm
- \+/\- *theorem* coe_symm_comp_coe
- \+/\- *theorem* symm_symm
- \+/\- *theorem* symm_symm_apply
- \+/\- *theorem* coe_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext_ring
- \+/\- *theorem* ext_ring_iff
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* comp_zero
- \+/\- *theorem* zero_comp
- \+/\- *theorem* comp_assoc
- \+/\- *theorem* coe_def_rev
- \+/\- *theorem* coe_apply
- \+/\- *theorem* bijective
- \+/\- *theorem* injective
- \+/\- *theorem* surjective
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* symm_trans_apply
- \+/\- *theorem* symm_image_image
- \+/\- *theorem* image_symm_image
- \+/\- *theorem* coe_comp_coe_symm
- \+/\- *theorem* coe_symm_comp_coe
- \+/\- *theorem* symm_symm
- \+/\- *theorem* symm_symm_apply
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* ker
- \+/\- *def* range
- \+/\- *def* cod_restrict
- \+/\- *def* subtype_val
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* prod_map
- \+/\- *def* coprod
- \+/\- *def* smul_right
- \+/\- *def* proj_ker_of_right_inverse
- \+/\- *def* to_continuous_linear_map
- \+/\- *def* to_homeomorph
- \+/\- *def* prod
- \+/\- *def* equiv_of_inverse
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* ker
- \+/\- *def* range
- \+/\- *def* cod_restrict
- \+/\- *def* subtype_val
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* prod_map
- \+/\- *def* coprod
- \+/\- *def* smul_right
- \+/\- *def* proj_ker_of_right_inverse
- \+/\- *def* to_continuous_linear_map
- \+/\- *def* to_homeomorph
- \+/\- *def* prod
- \+/\- *def* equiv_of_inverse



## [2021-10-05 08:05:44](https://github.com/leanprover-community/mathlib/commit/fefd8a3)
refactor(analysis/convex/*): prove `convex_independent_iff_finset` without full Carathéodory ([#9550](https://github.com/leanprover-community/mathlib/pull/9550))
Also relax one `add_comm_group` to `add_comm_monoid` and two `𝕜` to `β` + `module 𝕜 β`, and simplify imports.
#### Estimated changes
modified src/analysis/convex/extreme.lean

modified src/analysis/convex/function.lean
- \+/\- *lemma* convex_on_id
- \+/\- *lemma* concave_on_id
- \+/\- *lemma* convex_on_id
- \+/\- *lemma* concave_on_id

modified src/analysis/convex/independent.lean



## [2021-10-05 08:05:43](https://github.com/leanprover-community/mathlib/commit/c42786f)
feat(topology/algebra): adic topology ([#9521](https://github.com/leanprover-community/mathlib/pull/9521))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
created src/topology/algebra/nonarchimedean/adic_topology.lean
- \+ *lemma* adic_basis
- \+ *lemma* nonarchimedean
- \+ *lemma* has_basis_nhds_zero_adic
- \+ *lemma* has_basis_nhds_adic
- \+ *lemma* adic_module_basis
- \+ *lemma* is_adic_iff
- \+ *lemma* is_ideal_adic_pow
- \+ *lemma* is_bot_adic_iff
- \+ *def* ring_filter_basis
- \+ *def* adic_topology
- \+ *def* adic_module_topology
- \+ *def* open_add_subgroup
- \+ *def* is_adic
- \+ *def* topological_space_module



## [2021-10-05 08:05:41](https://github.com/leanprover-community/mathlib/commit/61cd266)
ci(.github/workflows): automatically remove awaiting-CI label ([#9491](https://github.com/leanprover-community/mathlib/pull/9491))
This PR adds a job to our CI which removes the label "awaiting-CI" when the build finishes successfully.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/awaiting-CI.2C.20.23bors.2C.20and.20the.20PR.20.23queue/near/255754196)
#### Estimated changes
modified .github/workflows/bors.yml

modified .github/workflows/build.yml

modified .github/workflows/build.yml.in

modified .github/workflows/build_fork.yml



## [2021-10-05 03:31:26](https://github.com/leanprover-community/mathlib/commit/1536412)
refactor(data/polynomial): use `monic.ne_zero` and `nontriviality` ([#9530](https://github.com/leanprover-community/mathlib/pull/9530))
There is a pattern in `data/polynomial` to have both `(hq : q.monic) (hq0 : q ≠ 0)` as assumptions. I found this less convenient to work with than `[nontrivial R] (hq : q.monic)` and using `monic.ne_zero` to replace `hq0`.
The `nontriviality` tactic automates all the cases where previously `nontrivial R` (or similar) was manually derived from the hypotheses.
#### Estimated changes
modified src/data/polynomial/div.lean
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* mod_by_monic_eq_self_iff
- \+/\- *lemma* div_by_monic_eq_zero_iff
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* mod_by_monic_eq_self_iff
- \+/\- *lemma* div_by_monic_eq_zero_iff

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/ring_division.lean

modified src/field_theory/minpoly.lean

modified src/ring_theory/power_basis.lean



## [2021-10-05 02:21:57](https://github.com/leanprover-community/mathlib/commit/fd18953)
chore(scripts): update nolints.txt ([#9553](https://github.com/leanprover-community/mathlib/pull/9553))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2021-10-05 01:26:25](https://github.com/leanprover-community/mathlib/commit/0491621)
docs(ring_theory/adjoin_root): fix docstring ([#9546](https://github.com/leanprover-community/mathlib/pull/9546))
#### Estimated changes
modified src/ring_theory/adjoin_root.lean



## [2021-10-05 01:26:24](https://github.com/leanprover-community/mathlib/commit/7466424)
feat(number_theory/padics): add padic_norm lemmas ([#9527](https://github.com/leanprover-community/mathlib/pull/9527))
#### Estimated changes
modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/padic_numbers.lean
- \+ *lemma* norm_le_pow_iff_norm_lt_pow_add_one
- \+ *lemma* norm_lt_pow_iff_norm_le_pow_sub_one



## [2021-10-04 23:18:15](https://github.com/leanprover-community/mathlib/commit/3aac8e5)
fix(order/sub): make arguments explicit ([#9541](https://github.com/leanprover-community/mathlib/pull/9541))
* This makes some arguments of lemmas explicit.
* These lemmas were not used in places where the implicitness/explicitness of the arguments matters
* Providing the arguments is sometimes useful, especially in `rw ← ...`
* This follows the explicitness of similar lemmas (like the instantiations for `nat`).
#### Estimated changes
modified src/algebra/order/sub.lean
- \+/\- *lemma* add_sub_cancel_right
- \+/\- *lemma* add_sub_cancel_left
- \+/\- *lemma* add_sub_add_right_eq_sub'
- \+/\- *lemma* sub_self'
- \+/\- *lemma* sub_zero'
- \+/\- *lemma* zero_sub'
- \+/\- *lemma* add_sub_cancel_right
- \+/\- *lemma* add_sub_cancel_left
- \+/\- *lemma* add_sub_add_right_eq_sub'
- \+/\- *lemma* sub_self'
- \+/\- *lemma* sub_zero'
- \+/\- *lemma* zero_sub'



## [2021-10-04 19:37:54](https://github.com/leanprover-community/mathlib/commit/10da8e6)
feat(set_theory/cardinal,*): assorted lemmas ([#9516](https://github.com/leanprover-community/mathlib/pull/9516))
### New instances
* a denumerable type is infinite;
* `Prop` is (noncomputably) enumerable;
* `Prop` is nontrivial;
* `cardinal.can_lift_cardinal_Type`: lift `cardinal.{u}` to `Type u`.
### New lemmas / attrs
* `quotient.out_equiv_out` : `x.out ≈ y.out ↔ x = y`;
* `quotient.out_inj` : `x.out = y.out ↔ x = y`;
* `cardinal.lift_bit0`, `cardinal.lift_bit1`, `cardinal.lift_two`, `cardinal.lift_prod` :
  new lemmas about `cardinal.lift`;
* `cardinal.omega_le_lift` and `cardinal.lift_le_omega` : simplify `ω ≤ lift c` and `lift c ≤ ω`;
* `cardinal.omega_le_add_iff`, `cardinal.encodable_iff`, `cardinal.mk_le_omega`,
  `cardinal.mk_denumerable`: new lemmas about `cardinal.omega`;
* add `@[simp]` attribute to `cardinal.mk_univ`, add `cardinal.mk_insert`;
* generalize `cardinal.nat_power_eq` to `cardinal.power_eq_two_power` and `cardinal.prod_eq_two_power`.
#### Estimated changes
modified src/data/equiv/denumerable.lean

modified src/data/equiv/encodable/basic.lean

modified src/data/quot.lean
- \+ *lemma* quotient.out_equiv_out
- \+ *lemma* quotient.out_inj

modified src/data/rat/denumerable.lean
- \+/\- *lemma* mk_rat
- \+/\- *lemma* mk_rat

modified src/logic/nontrivial.lean

modified src/set_theory/cardinal.lean
- \+/\- *lemma* mk_nat
- \+ *lemma* omega_le_add_iff
- \+ *lemma* omega_le_mk
- \+ *lemma* encodable_iff
- \+ *lemma* mk_le_omega
- \+ *lemma* mk_denumerable
- \+/\- *lemma* mk_int
- \+/\- *lemma* mk_pnat
- \+/\- *lemma* mk_nat
- \+/\- *lemma* mk_int
- \+/\- *lemma* mk_pnat
- \+ *theorem* lift_bit0
- \+ *theorem* lift_bit1
- \+ *theorem* lift_two
- \+/\- *theorem* lift_two_power
- \+ *theorem* lift_prod
- \+ *theorem* omega_le_lift
- \+ *theorem* lift_le_omega
- \+/\- *theorem* mk_univ
- \+ *theorem* mk_insert
- \+/\- *theorem* lift_two_power
- \+/\- *theorem* mk_univ

modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* power_self_eq
- \+ *lemma* prod_eq_two_power
- \+ *lemma* power_eq_two_power
- \+/\- *lemma* nat_power_eq
- \+/\- *lemma* power_nat_le
- \+/\- *lemma* power_self_eq
- \+/\- *lemma* nat_power_eq
- \+/\- *lemma* power_nat_le
- \+/\- *theorem* pow_le
- \+/\- *theorem* pow_le



## [2021-10-04 19:37:52](https://github.com/leanprover-community/mathlib/commit/50b51c5)
refactor(group_theory/is_p_group): Generalize `is_p_group.comap_injective` ([#9509](https://github.com/leanprover-community/mathlib/pull/9509))
`is_p_group.comap_injective` (comap along injective preserves p-groups) can be generalized to `is_p_group.comap_ker_is_p_group` (comap with p-group kernel preserves p-groups). This also simplifies the proof of `is_p_group.to_sup_of_normal_right`
#### Estimated changes
modified src/group_theory/p_group.lean
- \+/\- *lemma* map
- \+ *lemma* comap_of_ker_is_p_group
- \+ *lemma* comap_of_injective
- \+/\- *lemma* map
- \- *lemma* comap_injective



## [2021-10-04 15:09:53](https://github.com/leanprover-community/mathlib/commit/7a5d15a)
feat(data/pnat/interval): Finite intervals in ℕ+ ([#9534](https://github.com/leanprover-community/mathlib/pull/9534))
This proves that `ℕ+` is a locally finite order.
#### Estimated changes
created src/data/pnat/interval.lean
- \+ *lemma* Icc_eq_finset_subtype
- \+ *lemma* Ioc_eq_finset_subtype
- \+ *lemma* Ioo_eq_finset_subtype
- \+ *lemma* map_subtype_embedding_Icc
- \+ *lemma* map_subtype_embedding_Ioc
- \+ *lemma* map_subtype_embedding_Ioo
- \+ *lemma* card_Icc
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *lemma* card_fintype_Icc
- \+ *lemma* card_fintype_Ioc
- \+ *lemma* card_fintype_Ioo



## [2021-10-04 15:09:52](https://github.com/leanprover-community/mathlib/commit/e998e4c)
feat(order/conditionally_complete_lattice): image and cSup commute ([#9510](https://github.com/leanprover-community/mathlib/pull/9510))
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_set
- \+ *lemma* cinfi_set
- \+ *lemma* l_cSup'
- \+ *lemma* u_cInf'
- \+ *lemma* map_cSup'
- \+ *lemma* map_cInf'



## [2021-10-04 15:09:51](https://github.com/leanprover-community/mathlib/commit/d8968ba)
feat(algebra/order/functions): recursors and images under monotone maps ([#9505](https://github.com/leanprover-community/mathlib/pull/9505))
#### Estimated changes
modified src/algebra/order/functions.lean
- \+ *lemma* monotone_on.map_max
- \+ *lemma* monotone_on.map_min
- \+ *lemma* antitone_on.map_max
- \+ *lemma* antitone_on.map_min
- \+ *lemma* min_rec
- \+ *lemma* max_rec
- \+ *lemma* min_rec'
- \+ *lemma* max_rec'



## [2021-10-04 15:09:50](https://github.com/leanprover-community/mathlib/commit/fa52067)
refactor(order/fixed_points): rewrite using bundled `preorder_hom`s ([#9497](https://github.com/leanprover-community/mathlib/pull/9497))
This way `fixed_points.complete_lattice` can be an instance.
#### Estimated changes
modified src/data/set/function.lean
- \+ *lemma* injective_piecewise_iff
- \+ *theorem* subsingleton.inj_on
- \+/\- *theorem* inj_on_empty
- \+ *theorem* inj_on_singleton
- \+ *theorem* inj_on_union
- \+/\- *theorem* inj_on_empty

modified src/logic/embedding.lean
- \- *theorem* injective

modified src/order/fixed_points.lean
- \+/\- *lemma* lfp_le
- \+ *lemma* lfp_le_fixed
- \+/\- *lemma* le_lfp
- \+ *lemma* map_le_lfp
- \+ *lemma* map_lfp
- \+ *lemma* is_fixed_pt_lfp
- \+ *lemma* lfp_le_map
- \+ *lemma* is_least_lfp_le
- \+ *lemma* is_least_lfp
- \+/\- *lemma* lfp_induction
- \+ *lemma* is_fixed_pt_gfp
- \+ *lemma* map_gfp
- \+ *lemma* map_le_gfp
- \+ *lemma* gfp_le_map
- \+ *lemma* is_greatest_gfp_le
- \+ *lemma* is_greatest_gfp
- \+/\- *lemma* gfp_induction
- \+ *lemma* map_lfp_comp
- \+ *lemma* map_gfp_comp
- \+/\- *lemma* lfp_lfp
- \+/\- *lemma* gfp_gfp
- \+ *lemma* gfp_const_inf_le
- \+ *lemma* prev_fixed_le
- \+ *lemma* le_next_fixed
- \+ *lemma* next_fixed_le
- \+ *lemma* next_fixed_le_iff
- \+ *lemma* le_prev_fixed_iff
- \+ *lemma* le_prev_fixed
- \+ *lemma* le_map_sup_fixed_points
- \+ *lemma* map_inf_fixed_points_le
- \+ *lemma* le_map_Sup_subset_fixed_points
- \+ *lemma* map_Inf_subset_fixed_points_le
- \+/\- *lemma* lfp_le
- \+/\- *lemma* le_lfp
- \- *lemma* lfp_fixed_point
- \+/\- *lemma* lfp_induction
- \- *lemma* monotone_lfp
- \- *lemma* gfp_fixed_point
- \+/\- *lemma* gfp_induction
- \- *lemma* monotone_gfp
- \- *lemma* lfp_comp
- \- *lemma* gfp_comp
- \+/\- *lemma* lfp_lfp
- \+/\- *lemma* gfp_gfp
- \- *lemma* prev_le
- \- *lemma* prev_eq
- \- *lemma* le_next
- \- *lemma* next_eq
- \- *lemma* sup_le_f_of_fixed_points
- \- *lemma* f_le_inf_of_fixed_points
- \- *lemma* Sup_le_f_of_fixed_points
- \- *lemma* f_le_Inf_of_fixed_points
- \+/\- *def* lfp
- \+/\- *def* gfp
- \+/\- *def* prev_fixed
- \+/\- *def* next_fixed
- \+/\- *def* lfp
- \+/\- *def* gfp
- \- *def* prev
- \- *def* next
- \+/\- *def* prev_fixed
- \+/\- *def* next_fixed

modified src/set_theory/schroeder_bernstein.lean



## [2021-10-04 15:09:49](https://github.com/leanprover-community/mathlib/commit/387ff6e)
feat(topology/homotopy): add `homotopy_with` ([#9252](https://github.com/leanprover-community/mathlib/pull/9252))
Added `homotopy_with` as in [`HOL-Analysis`](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html) extending `homotopy`. Furthermore, I've added `homotopy_rel`.
Also rename/moved the file. There is also some refactoring which is part of the suggestions from [#9141](https://github.com/leanprover-community/mathlib/pull/9141) .
#### Estimated changes
deleted src/topology/homotopy.lean
- \- *lemma* ext
- \- *lemma* apply_zero
- \- *lemma* apply_one
- \- *lemma* to_continuous_map_apply
- \- *lemma* extend_apply_zero
- \- *lemma* extend_apply_one
- \- *lemma* symm_apply
- \- *lemma* symm_symm
- \- *lemma* trans_apply
- \- *lemma* symm_trans
- \- *def* curry
- \- *def* extend
- \- *def* refl
- \- *def* symm
- \- *def* trans

created src/topology/homotopy/basic.lean
- \+ *lemma* coe_fn_injective
- \+ *lemma* ext
- \+ *lemma* apply_zero
- \+ *lemma* apply_one
- \+ *lemma* coe_to_continuous_map
- \+ *lemma* curry_apply
- \+ *lemma* extend_apply_of_le_zero
- \+ *lemma* extend_apply_of_one_le
- \+ *lemma* extend_apply_coe
- \+ *lemma* extend_apply_of_mem_I
- \+ *lemma* congr_fun
- \+ *lemma* congr_arg
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans
- \+ *lemma* coe_fn_injective
- \+ *lemma* ext
- \+ *lemma* apply_zero
- \+ *lemma* apply_one
- \+ *lemma* coe_to_continuous_map
- \+ *lemma* coe_to_homotopy
- \+ *lemma* prop
- \+ *lemma* extend_prop
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans
- \+ *lemma* eq_fst
- \+ *lemma* eq_snd
- \+ *lemma* fst_eq_snd
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans
- \+ *def* simps.apply
- \+ *def* curry
- \+ *def* extend
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* simps.apply
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans



## [2021-10-04 14:16:41](https://github.com/leanprover-community/mathlib/commit/f6c77be)
fix(ci): always use python3 executable ([#9531](https://github.com/leanprover-community/mathlib/pull/9531))
On many (particularly older) systems, the `python` command can refer to `python2` instead of `python3`.  Therefore we change all `python` calls to `python3` to prevent failures on some self-hosted runners.
#### Estimated changes
modified .github/workflows/bors.yml

modified .github/workflows/build.yml

modified .github/workflows/build.yml.in

modified .github/workflows/build_fork.yml



## [2021-10-04 14:16:40](https://github.com/leanprover-community/mathlib/commit/a07d1de)
feat(data/fin/interval): Finite intervals in `fin n` ([#9523](https://github.com/leanprover-community/mathlib/pull/9523))
#### Estimated changes
created src/data/fin/interval.lean
- \+ *lemma* Icc_eq_finset_subtype
- \+ *lemma* Ioc_eq_finset_subtype
- \+ *lemma* Ioo_eq_finset_subtype
- \+ *lemma* map_subtype_embedding_Icc
- \+ *lemma* map_subtype_embedding_Ioc
- \+ *lemma* map_subtype_embedding_Ioo
- \+ *lemma* card_Icc
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *lemma* card_fintype_Icc
- \+ *lemma* card_fintype_Ioc
- \+ *lemma* card_fintype_Ioo



## [2021-10-04 13:23:23](https://github.com/leanprover-community/mathlib/commit/15d987a)
feat(probability_theory/notation): add notations for expected value, conditional expectation ([#9469](https://github.com/leanprover-community/mathlib/pull/9469))
When working in probability theory, the measure on the space is most often implicit. With our current notations for measure spaces, that means writing `volume` in a lot of places. To avoid that and introduce notations closer to the usual practice, this PR defines
- `𝔼[X]` for the expected value (integral) of a function `X` over the volume measure,
- `P[X]` for the expected value over the measure `P`,
- `𝔼[X | hm]` for the conditional expectation with respect to the volume,
- `X =ₐₛ Y` for `X =ᵐ[volume] Y` and similarly for `X ≤ᵐ[volume] Y`,
- `∂P/∂Q` for `P.rn_deriv Q`
All notations are localized to the `probability_theory` namespace.
#### Estimated changes
created src/probability_theory/notation.lean



## [2021-10-04 09:48:18](https://github.com/leanprover-community/mathlib/commit/ab7d251)
feat(measure_theory/covering/besicovitch_vector_space): vector spaces satisfy the assumption of Besicovitch covering theorem ([#9461](https://github.com/leanprover-community/mathlib/pull/9461))
The Besicovitch covering theorem works in any metric space subject to a technical condition: there should be no satellite configuration of `N+1` points, for some `N`. We prove that this condition is satisfied in finite-dimensional real vector spaces. Moreover, we get the optimal bound for `N`: it coincides with the maximal number of `1`-separated points that fit in a ball of radius `2`, by [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994]
#### Estimated changes
created src/measure_theory/covering/besicovitch_vector_space.lean
- \+ *lemma* center_and_rescale_center
- \+ *lemma* center_and_rescale_radius
- \+ *lemma* card_le_of_separated
- \+ *lemma* multiplicity_le
- \+ *lemma* card_le_multiplicity
- \+ *lemma* exists_good_δ
- \+ *lemma* good_δ_lt_one
- \+ *lemma* one_lt_good_τ
- \+ *lemma* card_le_multiplicity_of_δ
- \+ *lemma* le_multiplicity_of_δ_of_fin
- \+ *lemma* exists_normalized_aux1
- \+ *lemma* exists_normalized_aux2
- \+ *lemma* exists_normalized_aux3
- \+ *lemma* exists_normalized
- \+ *theorem* is_empty_satellite_config_multiplicity
- \+ *def* center_and_rescale
- \+ *def* multiplicity
- \+ *def* good_δ
- \+ *def* good_τ



## [2021-10-04 09:48:17](https://github.com/leanprover-community/mathlib/commit/b6f94a9)
feat(analysis/special_functions): real derivs of `complex.exp` and `complex.log` ([#9422](https://github.com/leanprover-community/mathlib/pull/9422))
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* restrict_scalars_one_smul_right'
- \+ *lemma* restrict_scalars_one_smul_right

modified src/analysis/complex/real_deriv.lean
- \+ *lemma* has_strict_deriv_at.complex_to_real_fderiv'
- \+ *lemma* has_deriv_at.complex_to_real_fderiv'
- \+ *lemma* has_deriv_within_at.complex_to_real_fderiv'
- \+ *lemma* has_strict_deriv_at.complex_to_real_fderiv
- \+ *lemma* has_deriv_at.complex_to_real_fderiv
- \+ *lemma* has_deriv_within_at.complex_to_real_fderiv

modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* has_strict_fderiv_at_log_real
- \+ *lemma* has_strict_deriv_at.clog_real
- \+ *lemma* has_deriv_at.clog_real
- \+ *lemma* has_deriv_within_at.clog_real

modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* has_strict_fderiv_at_exp_real
- \+ *lemma* has_strict_deriv_at.cexp_real
- \+ *lemma* has_deriv_at.cexp_real
- \+ *lemma* has_deriv_within_at.cexp_real



## [2021-10-04 09:48:16](https://github.com/leanprover-community/mathlib/commit/1faf964)
feat(ring_theory/algebraic_independent): Existence of transcendence bases and rings are algebraic over transcendence basis ([#9377](https://github.com/leanprover-community/mathlib/pull/9377))
#### Estimated changes
modified src/ring_theory/algebraic_independent.lean
- \+ *lemma* algebraic_independent.algebra_map_aeval_equiv
- \+ *lemma* algebraic_independent.aeval_comp_mv_polynomial_option_equiv_polynomial_adjoin
- \+ *lemma* exists_is_transcendence_basis
- \+ *lemma* is_transcendence_basis.is_algebraic
- \+ *theorem* algebraic_independent.option_iff
- \+ *def* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin



## [2021-10-04 09:48:14](https://github.com/leanprover-community/mathlib/commit/8a05dca)
feat(order/jordan_holder): Jordan Hölder theorem ([#8976](https://github.com/leanprover-community/mathlib/pull/8976))
The Jordan Hoelder theorem proved for a Jordan Hölder lattice, instances of which include submodules of a module and subgroups of a group.
#### Estimated changes
created src/order/jordan_holder.lean
- \+ *lemma* is_maximal_inf_right_of_is_maximal_sup
- \+ *lemma* is_maximal_of_eq_inf
- \+ *lemma* second_iso_of_eq
- \+ *lemma* is_maximal.iso_refl
- \+ *lemma* step
- \+ *lemma* coe_fn_mk
- \+ *lemma* mem_def
- \+ *lemma* total
- \+ *lemma* ext_fun
- \+ *lemma* length_to_list
- \+ *lemma* to_list_ne_nil
- \+ *lemma* to_list_injective
- \+ *lemma* chain'_to_list
- \+ *lemma* to_list_sorted
- \+ *lemma* to_list_nodup
- \+ *lemma* mem_to_list
- \+ *lemma* length_of_list
- \+ *lemma* of_list_to_list
- \+ *lemma* of_list_to_list'
- \+ *lemma* to_list_of_list
- \+ *lemma* ext
- \+ *lemma* top_mem
- \+ *lemma* le_top
- \+ *lemma* le_top_of_mem
- \+ *lemma* bot_mem
- \+ *lemma* bot_le
- \+ *lemma* bot_le_of_mem
- \+ *lemma* length_pos_of_mem_ne
- \+ *lemma* forall_mem_eq_of_length_eq_zero
- \+ *lemma* top_erase_top
- \+ *lemma* erase_top_top_le
- \+ *lemma* bot_erase_top
- \+ *lemma* mem_erase_top_of_ne_of_mem
- \+ *lemma* mem_erase_top
- \+ *lemma* lt_top_of_mem_erase_top
- \+ *lemma* is_maximal_erase_top_top
- \+ *lemma* append_cast_add_aux
- \+ *lemma* append_succ_cast_add_aux
- \+ *lemma* append_nat_add_aux
- \+ *lemma* append_succ_nat_add_aux
- \+ *lemma* append_cast_add
- \+ *lemma* append_succ_cast_add
- \+ *lemma* append_nat_add
- \+ *lemma* append_succ_nat_add
- \+ *lemma* top_snoc
- \+ *lemma* snoc_last
- \+ *lemma* snoc_cast_succ
- \+ *lemma* bot_snoc
- \+ *lemma* mem_snoc
- \+ *lemma* eq_snoc_erase_top
- \+ *lemma* snoc_erase_top_top
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* append
- \+ *lemma* length_eq
- \+ *lemma* snoc_snoc_swap
- \+ *lemma* length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
- \+ *lemma* length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos
- \+ *lemma* eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
- \+ *lemma* exists_top_eq_snoc_equivalant
- \+ *theorem* lt_succ
- \+ *theorem* jordan_holder
- \+ *def* to_list
- \+ *def* of_list
- \+ *def* top
- \+ *def* bot
- \+ *def* erase_top
- \+ *def* append
- \+ *def* snoc
- \+ *def* equivalent



## [2021-10-04 09:48:13](https://github.com/leanprover-community/mathlib/commit/abe81bc)
feat(linear_algebra/matrix/general_linear_group): GL(n, R) ([#8466](https://github.com/leanprover-community/mathlib/pull/8466))
added this file which contains definition of the general linear group as well as the subgroup of matrices with positive determinant.
#### Estimated changes
created src/linear_algebra/general_linear_group.lean
- \+ *lemma* ext_iff
- \+ *lemma* ext
- \+ *lemma* coe_fn_eq_coe
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_inv
- \+ *lemma* mem_GL_pos
- \+ *lemma* GL_pos_coe_neg
- \+ *lemma* GL_pos_neg_elt
- \+ *lemma* coe_eq_to_GL_pos
- \+ *lemma* to_GL_pos_injective
- \+ *def* det
- \+ *def* to_lin
- \+ *def* mk'
- \+ *def* GL_pos
- \+ *def* to_GL_pos

modified src/ring_theory/subring.lean
- \+ *lemma* units.mem_pos_subgroup
- \+ *def* units.pos_subgroup

modified src/ring_theory/subsemiring.lean
- \+ *lemma* mem_pos_monoid
- \+ *def* pos_submonoid



## [2021-10-04 08:10:26](https://github.com/leanprover-community/mathlib/commit/edb22fe)
feat(topology/algebra): nonarchimedean filter bases ([#9511](https://github.com/leanprover-community/mathlib/pull/9511))
This is preparatory material for adic topology. It is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
created src/topology/algebra/nonarchimedean/bases.lean
- \+ *lemma* of_comm
- \+ *lemma* mem_add_group_filter_basis_iff
- \+ *lemma* mem_add_group_filter_basis
- \+ *lemma* has_basis_nhds_zero
- \+ *lemma* has_basis_nhds
- \+ *lemma* nonarchimedean
- \+ *lemma* to_ring_subgroups_basis
- \+ *lemma* nonarchimedean
- \+ *lemma* submodules_ring_basis.to_submodules_basis
- \+ *lemma* ring_filter_basis.submodules_basis_is_basis
- \+ *def* to_ring_filter_basis
- \+ *def* topology
- \+ *def* open_add_subgroup
- \+ *def* topology
- \+ *def* to_module_filter_basis
- \+ *def* topology
- \+ *def* open_add_subgroup
- \+ *def* ring_filter_basis.module_filter_basis



## [2021-10-04 08:10:24](https://github.com/leanprover-community/mathlib/commit/6bd6afa)
feat(data/nat/interval): finite intervals of naturals ([#9507](https://github.com/leanprover-community/mathlib/pull/9507))
This proves that `ℕ` is a `locally_finite_order`.
#### Estimated changes
modified src/data/list/erase_dup.lean

created src/data/nat/interval.lean
- \+ *lemma* Icc_eq_range'
- \+ *lemma* Ioc_eq_range'
- \+ *lemma* Ioo_eq_range'
- \+ *lemma* card_Icc
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *lemma* card_fintype_Icc
- \+ *lemma* card_fintype_Ioc
- \+ *lemma* card_fintype_Ioo
- \+ *lemma* Icc_succ_left



## [2021-10-04 08:10:23](https://github.com/leanprover-community/mathlib/commit/dc1b045)
feat(linear_algebra/free_module/strong_rank_condition): add `comm_ring_strong_rank_condition` ([#9486](https://github.com/leanprover-community/mathlib/pull/9486))
We add `comm_ring_strong_rank_condition`: any commutative ring satisfies the strong rank condition.
Because of a circular import, this can't be in `linear_algebra.invariant_basis_number`.
#### Estimated changes
modified src/linear_algebra/charpoly/basic.lean
- \+ *lemma* minpoly_coeff_zero_of_injective
- \- *lemma* charpoly_coeff_zero_of_injective

created src/linear_algebra/free_module/strong_rank_condition.lean

modified src/linear_algebra/invariant_basis_number.lean



## [2021-10-04 08:10:22](https://github.com/leanprover-community/mathlib/commit/6a6b4d0)
feat(category_theory/sites/*): Cover-lifting functors on sites ([#9431](https://github.com/leanprover-community/mathlib/pull/9431))
This PR defines cover-liftings functors between sites, and proves that `Ran F.op` maps sheaves to sheaves for cover-lifting functors `F`. 
This will probably be needed when we want to glue B-sheaves into sheaves.
#### Estimated changes
created src/category_theory/sites/cover_lifting.lean
- \+ *lemma* pulledback_family_apply
- \+ *lemma* get_section_is_amalgamation
- \+ *lemma* get_section_is_unique
- \+ *lemma* get_section_commute
- \+ *lemma* glued_limit_cone_π_app
- \+ *lemma* helper
- \+ *lemma* glued_section_is_amalgamation
- \+ *lemma* glued_section_is_unique
- \+ *theorem* Ran_is_sheaf_of_cover_lifting
- \+ *def* id_cover_lifting
- \+ *def* comp_cover_lifting
- \+ *def* pulledback_family
- \+ *def* get_section
- \+ *def* glued_limit_cone
- \+ *def* glued_section

modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* family_of_elements.compatible.functor_pullback
- \+ *lemma* family_of_elements.compatible.pullback
- \+ *lemma* family_of_elements.compatible.comp_presheaf_map
- \+ *def* family_of_elements.functor_pullback
- \+ *def* family_of_elements.pullback
- \+ *def* family_of_elements.comp_presheaf_map
- \+/\- *def* SheafOfTypes
- \+/\- *def* SheafOfTypes

modified src/category_theory/sites/sieves.lean
- \+ *lemma* functor_pullback_mem
- \+ *lemma* functor_pullback_id
- \+ *lemma* functor_pullback_id
- \+ *def* functor_pullback
- \+ *def* functor_pullback
- \+/\- *def* functor
- \+/\- *def* functor

modified src/category_theory/structured_arrow.lean
- \+ *def* hom_mk'



## [2021-10-04 05:54:42](https://github.com/leanprover-community/mathlib/commit/d677c29)
feat(field_theory/algebraic_closure): versions of exists_aeval_eq_zero for rings ([#9517](https://github.com/leanprover-community/mathlib/pull/9517))
#### Estimated changes
modified src/field_theory/is_alg_closed/basic.lean
- \+ *theorem* exists_eval₂_eq_zero_of_injective
- \+ *theorem* exists_aeval_eq_zero_of_injective



## [2021-10-03 20:33:50](https://github.com/leanprover-community/mathlib/commit/52495a0)
chore(data/set/lattice): fix name ([#9520](https://github.com/leanprover-community/mathlib/pull/9520))
`comp` is for composition, `compl` for complement. Fix names using `comp` instead of `compl`.
#### Estimated changes
modified src/data/set/lattice.lean
- \+ *theorem* Union_eq_compl_Inter_compl
- \+ *theorem* Inter_eq_compl_Union_compl
- \+ *theorem* sInter_eq_compl_sUnion_compl
- \- *theorem* Union_eq_comp_Inter_comp
- \- *theorem* Inter_eq_comp_Union_comp
- \- *theorem* sInter_eq_comp_sUnion_compl



## [2021-10-03 20:33:49](https://github.com/leanprover-community/mathlib/commit/465508f)
split(order/monotone): split off `order.basic` ([#9518](https://github.com/leanprover-community/mathlib/pull/9518))
#### Estimated changes
modified src/algebra/order/monoid_lemmas.lean

modified src/order/basic.lean
- \- *lemma* function.monotone_eval
- \- *lemma* monotone_on_univ
- \- *lemma* antitone_on_univ
- \- *lemma* strict_mono_on_univ
- \- *lemma* strict_anti_on_univ
- \- *lemma* monotone.strict_mono_of_injective
- \- *lemma* antitone.strict_anti_of_injective
- \- *lemma* monotone_id
- \- *lemma* strict_mono_id
- \- *lemma* strict_mono_of_le_iff_le
- \- *lemma* injective_of_lt_imp_ne
- \- *lemma* injective_of_le_imp_le
- \- *lemma* monotone.comp_antitone
- \- *lemma* antitone.comp_monotone
- \- *lemma* monotone.comp_antitone_on
- \- *lemma* antitone.comp_monotone_on
- \- *lemma* strict_mono.comp_strict_anti
- \- *lemma* strict_anti.comp_strict_mono
- \- *lemma* strict_mono.comp_strict_anti_on
- \- *lemma* strict_anti.comp_strict_mono_on
- \- *lemma* monotone.reflect_lt
- \- *lemma* antitone.reflect_lt
- \- *lemma* strict_mono_on.le_iff_le
- \- *lemma* strict_anti_on.le_iff_le
- \- *lemma* strict_mono_on.lt_iff_lt
- \- *lemma* strict_anti_on.lt_iff_lt
- \- *lemma* strict_mono.le_iff_le
- \- *lemma* strict_anti.le_iff_le
- \- *lemma* strict_mono.lt_iff_lt
- \- *lemma* strict_anti.lt_iff_lt
- \- *lemma* strict_mono.injective
- \- *lemma* strict_anti.injective
- \- *lemma* strict_mono.maximal_of_maximal_image
- \- *lemma* strict_mono.minimal_of_minimal_image
- \- *lemma* strict_anti.minimal_of_maximal_image
- \- *lemma* strict_anti.maximal_of_minimal_image
- \- *lemma* monotone.strict_mono_iff_injective
- \- *lemma* antitone.strict_anti_iff_injective
- \- *lemma* monotone_nat_of_le_succ
- \- *lemma* antitone_nat_of_succ_le
- \- *lemma* strict_mono_nat_of_lt_succ
- \- *lemma* strict_anti_nat_of_succ_lt
- \- *lemma* forall_ge_le_of_forall_le_succ
- \- *lemma* monotone.ne_of_lt_of_lt_nat
- \- *lemma* antitone.ne_of_lt_of_lt_nat
- \- *lemma* monotone.ne_of_lt_of_lt_int
- \- *lemma* antitone.ne_of_lt_of_lt_int
- \- *lemma* strict_mono.id_le
- \- *lemma* subtype.mono_coe
- \- *lemma* subtype.strict_mono_coe
- \- *lemma* monotone_fst
- \- *lemma* monotone_snd
- \- *theorem* monotone.comp_le_comp_left
- \- *theorem* monotone_lam
- \- *theorem* monotone_app
- \- *theorem* antitone_lam
- \- *theorem* antitone_app
- \- *theorem* monotone_const
- \- *theorem* antitone_const
- \- *def* monotone
- \- *def* antitone
- \- *def* monotone_on
- \- *def* antitone_on
- \- *def* strict_mono
- \- *def* strict_anti
- \- *def* strict_mono_on
- \- *def* strict_anti_on

modified src/order/closure.lean

modified src/order/iterate.lean

modified src/order/lattice.lean

created src/order/monotone.lean
- \+ *lemma* function.monotone_eval
- \+ *lemma* monotone_on_univ
- \+ *lemma* antitone_on_univ
- \+ *lemma* strict_mono_on_univ
- \+ *lemma* strict_anti_on_univ
- \+ *lemma* monotone.strict_mono_of_injective
- \+ *lemma* antitone.strict_anti_of_injective
- \+ *lemma* monotone_id
- \+ *lemma* strict_mono_id
- \+ *lemma* strict_mono_of_le_iff_le
- \+ *lemma* injective_of_lt_imp_ne
- \+ *lemma* injective_of_le_imp_le
- \+ *lemma* monotone.comp_antitone
- \+ *lemma* antitone.comp_monotone
- \+ *lemma* monotone.comp_antitone_on
- \+ *lemma* antitone.comp_monotone_on
- \+ *lemma* strict_mono.comp_strict_anti
- \+ *lemma* strict_anti.comp_strict_mono
- \+ *lemma* strict_mono.comp_strict_anti_on
- \+ *lemma* strict_anti.comp_strict_mono_on
- \+ *lemma* monotone.reflect_lt
- \+ *lemma* antitone.reflect_lt
- \+ *lemma* strict_mono_on.le_iff_le
- \+ *lemma* strict_anti_on.le_iff_le
- \+ *lemma* strict_mono_on.lt_iff_lt
- \+ *lemma* strict_anti_on.lt_iff_lt
- \+ *lemma* strict_mono.le_iff_le
- \+ *lemma* strict_anti.le_iff_le
- \+ *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_anti.lt_iff_lt
- \+ *lemma* strict_mono.injective
- \+ *lemma* strict_anti.injective
- \+ *lemma* strict_mono.maximal_of_maximal_image
- \+ *lemma* strict_mono.minimal_of_minimal_image
- \+ *lemma* strict_anti.minimal_of_maximal_image
- \+ *lemma* strict_anti.maximal_of_minimal_image
- \+ *lemma* monotone.strict_mono_iff_injective
- \+ *lemma* antitone.strict_anti_iff_injective
- \+ *lemma* monotone_nat_of_le_succ
- \+ *lemma* antitone_nat_of_succ_le
- \+ *lemma* strict_mono_nat_of_lt_succ
- \+ *lemma* strict_anti_nat_of_succ_lt
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+ *lemma* monotone.ne_of_lt_of_lt_nat
- \+ *lemma* antitone.ne_of_lt_of_lt_nat
- \+ *lemma* monotone.ne_of_lt_of_lt_int
- \+ *lemma* antitone.ne_of_lt_of_lt_int
- \+ *lemma* strict_mono.id_le
- \+ *lemma* subtype.mono_coe
- \+ *lemma* subtype.strict_mono_coe
- \+ *lemma* monotone_fst
- \+ *lemma* monotone_snd
- \+ *theorem* monotone.comp_le_comp_left
- \+ *theorem* monotone_lam
- \+ *theorem* monotone_app
- \+ *theorem* antitone_lam
- \+ *theorem* antitone_app
- \+ *theorem* monotone_const
- \+ *theorem* antitone_const
- \+ *def* monotone
- \+ *def* antitone
- \+ *def* monotone_on
- \+ *def* antitone_on
- \+ *def* strict_mono
- \+ *def* strict_anti
- \+ *def* strict_mono_on
- \+ *def* strict_anti_on

modified src/order/prime_ideal.lean



## [2021-10-03 20:33:48](https://github.com/leanprover-community/mathlib/commit/c0f7c56)
feat(algebra/order): exists_square_le ([#9513](https://github.com/leanprover-community/mathlib/pull/9513))
This is a modernized version of code from the perfectoid project.
#### Estimated changes
modified src/algebra/order/monoid_lemmas.lean
- \+ *lemma* exists_square_le



## [2021-10-03 20:33:47](https://github.com/leanprover-community/mathlib/commit/bc5a081)
feat(topology/algebra): Cauchy filters on groups ([#9512](https://github.com/leanprover-community/mathlib/pull/9512))
This adds a tiny file but putting this lemma in `topology/algebra/filter_basis.lean` would make that file import a lot of uniform spaces theory. This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
created src/topology/algebra/uniform_filter_basis.lean
- \+ *lemma* cauchy_iff



## [2021-10-03 20:33:46](https://github.com/leanprover-community/mathlib/commit/44f4d70)
chore(*): use dot-notation for is_conj.symm and is_conj.trans ([#9498](https://github.com/leanprover-community/mathlib/pull/9498))
renames:
* is_conj_refl -> is_conj.refl
* is_conj_symm -> is_conj.symm
* is_conj_trans -> is_conj.trans
#### Estimated changes
modified src/algebra/group/conj.lean
- \+ *lemma* is_conj.refl
- \+ *lemma* is_conj.symm
- \+ *lemma* is_conj.trans
- \+/\- *lemma* mem_conjugates_of_self
- \+/\- *lemma* mem_carrier_mk
- \- *lemma* is_conj_refl
- \- *lemma* is_conj_symm
- \- *lemma* is_conj_trans
- \+/\- *lemma* mem_conjugates_of_self
- \+/\- *lemma* mem_carrier_mk

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/subgroup/basic.lean



## [2021-10-03 20:33:45](https://github.com/leanprover-community/mathlib/commit/c1936c1)
feat(order/basic): define `is_top` and `is_bot` ([#9493](https://github.com/leanprover-community/mathlib/pull/9493))
These predicates allow us to formulate & prove some theorems
simultaneously for the cases `[order_top α]` and `[no_top_order α]`.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *lemma* set_of_eq_eq_singleton
- \+ *lemma* set_of_eq_eq_singleton'
- \+ *lemma* subsingleton_is_top
- \+ *lemma* subsingleton_is_bot
- \+/\- *lemma* set_of_eq_eq_singleton

modified src/data/set/countable.lean
- \+ *lemma* subsingleton.countable
- \+ *lemma* countable_is_top
- \+ *lemma* countable_is_bot

modified src/data/set/finite.lean
- \+ *lemma* finite_is_top
- \+ *lemma* finite_is_bot

modified src/order/basic.lean
- \+ *lemma* not_is_top
- \+ *lemma* is_top.unique
- \+ *lemma* not_is_bot
- \+ *lemma* is_bot.unique
- \+ *def* is_top
- \+ *def* is_bot

modified src/order/bounded_lattice.lean
- \+ *theorem* is_top_iff_eq_top
- \+ *theorem* is_bot_iff_eq_bot



## [2021-10-03 18:50:48](https://github.com/leanprover-community/mathlib/commit/e789ad3)
feat(group_theory/subgroup): mk lemmas ([#9514](https://github.com/leanprover-community/mathlib/pull/9514))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/set_like.20idiom
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+ *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk
- \- *lemma* mk_coe

modified src/field_theory/subfield.lean
- \+/\- *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk
- \+/\- *lemma* mem_mk

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk

modified src/group_theory/submonoid/basic.lean
- \+ *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk

modified src/ring_theory/subring.lean
- \+ *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk



## [2021-10-03 15:22:43](https://github.com/leanprover-community/mathlib/commit/d260894)
feat(analysis/convex/combination): lemmas connecting convex hull with affine combinations and barycentric coordinates ([#9499](https://github.com/leanprover-community/mathlib/pull/9499))
#### Estimated changes
modified src/analysis/convex/combination.lean
- \+ *lemma* affine_combination_mem_convex_hull
- \+ *lemma* convex_hull_range_eq_exists_affine_combination
- \+ *lemma* convex_hull_affine_basis_eq_nonneg_barycentric

modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* barycentric_coord_apply_combination_of_mem
- \+ *lemma* barycentric_coord_apply_combination_of_not_mem
- \- *lemma* barycentric_coord_apply_combination



## [2021-10-03 11:42:58](https://github.com/leanprover-community/mathlib/commit/cff9927)
refactor(ring_theory/unique_factorization_domain): rename unique_factorization_monoid.factors ([#9503](https://github.com/leanprover-community/mathlib/pull/9503))
This frees up the name for the non-normalizing version.
#### Estimated changes
modified src/algebra/squarefree.lean
- \+ *lemma* squarefree_iff_nodup_normalized_factors
- \- *lemma* squarefree_iff_nodup_factors

modified src/field_theory/splitting_field.lean

modified src/number_theory/arithmetic_function.lean

modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* prod_normalized_factors_eq_self
- \+ *lemma* normalized_factors_prod
- \+/\- *lemma* sup_eq_prod_inf_factors
- \- *lemma* prod_factors_eq_self
- \- *lemma* factors_prod_factors_eq_factors
- \+/\- *lemma* sup_eq_prod_inf_factors

modified src/ring_theory/int/basic.lean
- \+/\- *theorem* nat.factors_eq
- \+/\- *theorem* nat.factors_eq

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* normalized_factors_irreducible
- \+ *lemma* exists_mem_normalized_factors_of_dvd
- \+ *lemma* normalized_factors_zero
- \+ *lemma* normalized_factors_one
- \+ *lemma* normalized_factors_mul
- \+ *lemma* normalized_factors_pow
- \+ *lemma* dvd_iff_normalized_factors_le_normalized_factors
- \+ *lemma* zero_not_mem_normalized_factors
- \+ *lemma* dvd_of_mem_normalized_factors
- \+ *lemma* le_multiplicity_iff_repeat_le_normalized_factors
- \+ *lemma* multiplicity_eq_count_normalized_factors
- \- *lemma* factors_irreducible
- \- *lemma* exists_mem_factors_of_dvd
- \- *lemma* factors_zero
- \- *lemma* factors_one
- \- *lemma* factors_mul
- \- *lemma* factors_pow
- \- *lemma* dvd_iff_factors_le_factors
- \- *lemma* zero_not_mem_factors
- \- *lemma* dvd_of_mem_factors
- \- *lemma* le_multiplicity_iff_repeat_le_factors
- \- *lemma* multiplicity_eq_count_factors
- \+ *theorem* normalized_factors_prod
- \+ *theorem* prime_of_normalized_factor
- \+ *theorem* irreducible_of_normalized_factor
- \+ *theorem* normalize_normalized_factor
- \- *theorem* factors_prod
- \- *theorem* prime_of_factor
- \- *theorem* irreducible_of_factor
- \- *theorem* normalize_factor



## [2021-10-03 11:42:57](https://github.com/leanprover-community/mathlib/commit/18e7f91)
feat(group_theory/quotient_group): if a quotient is trivial then the subgroup is the whole group ([#9092](https://github.com/leanprover-community/mathlib/pull/9092))
#### Estimated changes
modified src/data/setoid/basic.lean
- \+ *lemma* top_def
- \+ *lemma* bot_def
- \+ *lemma* eq_top_iff
- \+ *lemma* quotient.subsingleton_iff
- \+ *lemma* quot.subsingleton_iff

modified src/group_theory/quotient_group.lean
- \+ *lemma* subsingleton_quotient_top
- \+ *lemma* subgroup_eq_top_of_subsingleton

modified src/logic/relation.lean
- \+ *lemma* eqv_gen_eq_of_equivalence



## [2021-10-03 10:10:01](https://github.com/leanprover-community/mathlib/commit/55c30c6)
feat(topology/basic): interior of finite intersection is intersection of interiors ([#9508](https://github.com/leanprover-community/mathlib/pull/9508))
And likewise for finite unions and closures.
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* finset.interior_Inter
- \+ *lemma* interior_Inter_of_fintype
- \+ *lemma* finset.closure_Union
- \+ *lemma* closure_Union_of_fintype



## [2021-10-03 09:15:42](https://github.com/leanprover-community/mathlib/commit/2807d83)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are continuous ([#9515](https://github.com/leanprover-community/mathlib/pull/9515))
#### Estimated changes
modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* continuous_barycentric_coord



## [2021-10-03 06:55:59](https://github.com/leanprover-community/mathlib/commit/7d83ff1)
feat(analysis/special_functions/exp_log): prove continuity of exp without derivatives ([#9501](https://github.com/leanprover-community/mathlib/pull/9501))
This is a first step towards making the definition of log and rpow independent of derivatives. The final goal is to avoid importing all of calculus in measure_theory/function/lp_space.lean .
#### Estimated changes
modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* exp_bound_sq
- \+ *lemma* locally_lipschitz_exp
- \+/\- *lemma* continuous_exp
- \+/\- *lemma* continuous_on_exp
- \+/\- *lemma* filter.tendsto.cexp
- \+/\- *lemma* continuous_within_at.cexp
- \+/\- *lemma* continuous_at.cexp
- \+/\- *lemma* continuous_on.cexp
- \+/\- *lemma* continuous.cexp
- \+/\- *lemma* continuous_exp
- \+/\- *lemma* continuous_on_exp
- \+/\- *lemma* continuous_exp
- \+/\- *lemma* continuous_on_exp
- \+/\- *lemma* filter.tendsto.cexp
- \+/\- *lemma* continuous_within_at.cexp
- \+/\- *lemma* continuous_at.cexp
- \+/\- *lemma* continuous_on.cexp
- \+/\- *lemma* continuous.cexp
- \+/\- *lemma* continuous_exp
- \+/\- *lemma* continuous_on_exp



## [2021-10-03 01:38:49](https://github.com/leanprover-community/mathlib/commit/5f803fa)
feat(analysis/convex/function): helper lemmas and general cleanup ([#9438](https://github.com/leanprover-community/mathlib/pull/9438))
This adds
* `convex_iff_pairwise_on_pos`
* `convex_on_iff_forall_pos`, `concave_on_iff_forall_pos`,
* `convex_on_iff_forall_pos_ne`, `concave_on_iff_forall_pos_ne`
* `convex_on.convex_strict_epigraph`, `concave_on.convex_strict_hypograph`
generalizes some instance assumptions:
* `convex_on.translate_` didn't need `module 𝕜 β` but `has_scalar 𝕜 β`.
* some proofs in `analysis.convex.exposed` were vestigially using `ℝ`.
 
and golfs proofs.
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+ *lemma* convex_iff_pairwise_on_pos

modified src/analysis/convex/exposed.lean
- \+/\- *lemma* exposed_points_subset_extreme_points
- \- *lemma* refl
- \- *lemma* antisymm
- \- *lemma* inter
- \- *lemma* is_closed
- \- *lemma* is_compact
- \+/\- *lemma* exposed_points_subset_extreme_points

modified src/analysis/convex/function.lean
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* concave_on.subset
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* concave_on.add
- \+ *lemma* concave_on.convex_ge
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* concave_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* concave_on.translate_left
- \+ *lemma* convex_on_iff_forall_pos
- \+ *lemma* concave_on_iff_forall_pos
- \+ *lemma* convex_on_iff_forall_pos_ne
- \+ *lemma* concave_on_iff_forall_pos_ne
- \+/\- *lemma* linear_map.convex_on
- \+/\- *lemma* linear_map.concave_on
- \+ *lemma* convex_on.convex_strict_epigraph
- \+ *lemma* concave_on.convex_strict_hypograph
- \+/\- *lemma* neg_convex_on_iff
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* concave_on.subset
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* concave_on.add
- \- *lemma* concave_on.concave_ge
- \+/\- *lemma* linear_map.convex_on
- \+/\- *lemma* linear_map.concave_on
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* concave_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* neg_convex_on_iff



## [2021-10-02 23:49:54](https://github.com/leanprover-community/mathlib/commit/7b02277)
chore(topology/*): more lemmas about `dense`/`dense_range` ([#9492](https://github.com/leanprover-community/mathlib/pull/9492))
#### Estimated changes
modified src/topology/bases.lean
- \+ *lemma* dense.exists_countable_dense_subset

modified src/topology/basic.lean
- \+ *lemma* dense.exists_mem_open
- \+ *lemma* dense.dense_range_coe
- \+ *lemma* dense_range.exists_mem_open

modified src/topology/dense_embedding.lean
- \+ *lemma* dense_image
- \+ *lemma* dense_image
- \+ *lemma* dense.dense_embedding_coe
- \+/\- *def* subtype_emb
- \+/\- *def* subtype_emb



## [2021-10-02 17:58:29](https://github.com/leanprover-community/mathlib/commit/c46a04a)
chore(measure_theory): move, deduplicate ([#9489](https://github.com/leanprover-community/mathlib/pull/9489))
* move lemmas like `is_compact.measure_lt_top` from `measure_theory.constructions.borel` to `measure_theory.measure.measure_space`;
* drop `is_compact.is_finite_measure` etc;
* add `measure_Ixx_lt_top`.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* is_compact.exists_open_superset_measure_lt_top'
- \- *lemma* is_compact.exists_open_superset_measure_lt_top
- \- *lemma* is_compact.measure_lt_top_of_nhds_within
- \- *lemma* is_compact.measure_lt_top
- \- *def* measure_theory.measure.finite_spanning_sets_in_compact
- \- *def* measure_theory.measure.finite_spanning_sets_in_open

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* exists_open_superset_measure_lt_top'
- \+ *lemma* exists_open_superset_measure_lt_top
- \+ *lemma* measure_lt_top_of_nhds_within
- \+ *lemma* measure_lt_top
- \+ *lemma* measure_Icc_lt_top
- \+ *lemma* measure_Ico_lt_top
- \+ *lemma* measure_Ioc_lt_top
- \+ *lemma* measure_Ioo_lt_top
- \+ *lemma* metric.bounded.measure_lt_top
- \- *lemma* is_finite_measure_of_nhds_within
- \- *lemma* is_finite_measure
- \- *lemma* metric.bounded.is_finite_measure
- \+ *def* measure_theory.measure.finite_spanning_sets_in_compact
- \+ *def* measure_theory.measure.finite_spanning_sets_in_open



## [2021-10-02 17:58:27](https://github.com/leanprover-community/mathlib/commit/a97e86a)
chore(ring_theory/ideal): some simp attributes ([#9487](https://github.com/leanprover-community/mathlib/pull/9487))
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+/\- *theorem* mul_bot
- \+/\- *theorem* bot_mul
- \+/\- *theorem* mul_top
- \+/\- *theorem* top_mul
- \+/\- *theorem* mul_bot
- \+/\- *theorem* bot_mul
- \+/\- *theorem* mul_top
- \+/\- *theorem* top_mul



## [2021-10-02 16:08:36](https://github.com/leanprover-community/mathlib/commit/e60dc2b)
docs(measure_theory/integral/lebesgue): Add "Markov's inequality" to the doc string of `mul_meas_ge_le_lintegral` ([#9506](https://github.com/leanprover-community/mathlib/pull/9506))
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean



## [2021-10-02 16:08:34](https://github.com/leanprover-community/mathlib/commit/110c740)
refactor(linear_algebra/charpoly): split in two files ([#9485](https://github.com/leanprover-community/mathlib/pull/9485))
We split `linear_algebra/charpoly` in `linear_algebra/charpoly/basic` and `linear_algebra/charpoly/to_matrix`.
Currently in `linear_algebra/charpoly/to_matrix` we only prove `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. This needs to be in a separate file then the definition of `f.charpoly` since it needs the invariant basis number property for commutative rings and in a future PR I will prove this as a special case of the fact that any commutative ring satisfies the strong rank condition, but the proof of this uses the characteristic polynomial.
We plan to add ohter results regarding the characteristic polynomial in the future.
#### Estimated changes
created src/linear_algebra/charpoly/basic.lean
- \+ *lemma* charpoly_def
- \+ *lemma* charpoly_monic
- \+ *lemma* aeval_self_charpoly
- \+ *lemma* is_integral
- \+ *lemma* minpoly_dvd_charpoly
- \+ *lemma* charpoly_coeff_zero_of_injective
- \+ *def* charpoly

renamed src/linear_algebra/charpoly.lean to src/linear_algebra/charpoly/to_matrix.lean
- \- *lemma* charpoly_def
- \- *lemma* charpoly_monic
- \- *lemma* aeval_self_charpoly
- \- *lemma* is_integral
- \- *lemma* minpoly_dvd_charpoly
- \- *lemma* charpoly_coeff_zero_of_injective
- \- *def* charpoly

modified src/linear_algebra/eigenspace.lean



## [2021-10-02 16:08:33](https://github.com/leanprover-community/mathlib/commit/1ceebca)
refactor(linear_algebra/free_module_pid): move linear_algebra/free_module_pid to linear_algebra/free_module/pid ([#9482](https://github.com/leanprover-community/mathlib/pull/9482))
We move `linear_algebra/free_module_pid` to `linear_algebra/free_module/pid`.
#### Estimated changes
modified src/linear_algebra/determinant.lean

renamed src/linear_algebra/free_module_pid.lean to src/linear_algebra/free_module/pid.lean

modified src/number_theory/class_number/finite.lean



## [2021-10-02 16:08:31](https://github.com/leanprover-community/mathlib/commit/fa7fdca)
feat(measure_theory/function/ae_eq_of_integral): two ennreal-valued function are a.e. equal if their integrals agree ([#9372](https://github.com/leanprover-community/mathlib/pull/9372))
#### Estimated changes
modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* ae_measurable.ae_eq_of_forall_set_lintegral_eq

modified src/order/filter/basic.lean
- \+ *lemma* eventually.ne_of_lt
- \+ *lemma* eventually.ne_top_of_lt
- \+ *lemma* eventually.lt_top_of_ne
- \+ *lemma* eventually.lt_top_iff_ne_top

modified src/topology/instances/ennreal.lean
- \+ *lemma* eventually_eq_of_to_real_eventually_eq



## [2021-10-02 13:51:01](https://github.com/leanprover-community/mathlib/commit/241aad7)
feat(data/finset/interval): API for `finset.Ixx` ([#9495](https://github.com/leanprover-community/mathlib/pull/9495))
This proves basic results about `finset.Ixx` & co. Lemma names (should) match their `set` counterparts.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* coe_eq_singleton

created src/data/finset/interval.lean
- \+ *lemma* nonempty_Icc
- \+ *lemma* nonempty_Ioc
- \+ *lemma* nonempty_Ioo
- \+ *lemma* Icc_eq_empty_iff
- \+ *lemma* Ioc_eq_empty_iff
- \+ *lemma* Ioo_eq_empty_iff
- \+ *lemma* Ioo_eq_empty
- \+ *lemma* Icc_eq_empty_of_lt
- \+ *lemma* Ioc_eq_empty_of_le
- \+ *lemma* Ioo_eq_empty_of_le
- \+ *lemma* Ioc_self
- \+ *lemma* Ioo_self
- \+ *lemma* Icc_self
- \+ *lemma* image_add_const_Icc
- \+ *lemma* image_add_const_Ioc
- \+ *lemma* image_add_const_Ioo



## [2021-10-02 12:12:09](https://github.com/leanprover-community/mathlib/commit/f3746ea)
chore(src/analysis/special_functions/trigonometric/basic) : prove continuity of sin/cos/sinh/cosh without derivatives ([#9502](https://github.com/leanprover-community/mathlib/pull/9502))
In a future PR, I want to split all files in the special_functions folder to avoid importing calculus when not needed (the goal is to avoid importing it in the definition of lp_space in measure_theory). This PR changes the proofs of continuity of trigonometric functions.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* continuous_sin
- \+/\- *lemma* continuous_cos
- \+/\- *lemma* continuous_sinh
- \+/\- *lemma* continuous_cosh
- \+/\- *lemma* continuous_sin
- \+/\- *lemma* continuous_cos
- \+/\- *lemma* continuous_sinh
- \+/\- *lemma* continuous_cosh
- \+/\- *lemma* continuous_sin
- \+/\- *lemma* continuous_cos
- \+/\- *lemma* continuous_sinh
- \+/\- *lemma* continuous_cosh
- \+/\- *lemma* continuous_sin
- \+/\- *lemma* continuous_cos
- \+/\- *lemma* continuous_sinh
- \+/\- *lemma* continuous_cosh



## [2021-10-02 09:30:39](https://github.com/leanprover-community/mathlib/commit/e26a9e5)
feat(measure_theory/covering/besicovitch): the Besicovitch covering theorem ([#9462](https://github.com/leanprover-community/mathlib/pull/9462))
The Besicovitch covering theorem: in a nice metric space (e.g. real vector spaces), from any family of balls one can extract `N` subfamilies made of disjoint balls, covering all the centers of the balls in the family. The number `N` only depends on the metric space.
#### Estimated changes
modified docs/references.bib

created src/measure_theory/covering/besicovitch.lean
- \+ *lemma* inter'
- \+ *lemma* hlast'
- \+ *lemma* monotone_Union_up_to
- \+ *lemma* last_step_nonempty
- \+ *lemma* mem_Union_up_to_last_step
- \+ *lemma* color_lt
- \+ *theorem* exist_disjoint_covering_families
- \+ *def* unit_ball_package
- \+ *def* Union_up_to
- \+ *def* R
- \+ *def* last_step



## [2021-10-02 09:30:37](https://github.com/leanprover-community/mathlib/commit/9e54ad0)
feat(ring_theory/algebraic_independent): algebraic independence ([#9229](https://github.com/leanprover-community/mathlib/pull/9229))
#### Estimated changes
created src/ring_theory/algebraic_independent.lean
- \+ *lemma* algebraic_independent_empty_type_iff
- \+ *lemma* algebra_map_injective
- \+ *lemma* linear_independent
- \+ *lemma* ne_zero
- \+ *lemma* comp
- \+ *lemma* coe_range
- \+ *lemma* map
- \+ *lemma* map'
- \+ *lemma* of_comp
- \+ *lemma* alg_hom.algebraic_independent_iff
- \+ *lemma* algebraic_independent_of_subsingleton
- \+ *lemma* algebraic_independent_adjoin
- \+ *lemma* algebraic_independent.restrict_scalars
- \+ *lemma* algebraic_independent_finset_map_embedding_subtype
- \+ *lemma* algebraic_independent_bounded_of_finset_algebraic_independent_bounded
- \+ *lemma* algebraic_independent.restrict_of_comp_subtype
- \+ *lemma* algebraic_independent_empty_iff
- \+ *lemma* algebraic_independent.mono
- \+ *lemma* algebraic_independent_of_finite
- \+ *lemma* algebraic_independent_Union_of_directed
- \+ *lemma* algebraic_independent_sUnion_of_directed
- \+ *lemma* exists_maximal_algebraic_independent
- \+ *lemma* algebraic_independent.aeval_repr
- \+ *lemma* algebraic_independent.aeval_comp_repr
- \+ *lemma* algebraic_independent.repr_ker
- \+ *lemma* algebraic_independent.is_transcendence_basis_iff
- \+ *lemma* algebraic_independent_empty_type
- \+ *lemma* algebraic_independent_empty
- \+ *theorem* algebraic_independent_iff_ker_eq_bot
- \+ *theorem* algebraic_independent_iff
- \+ *theorem* algebraic_independent.eq_zero_of_aeval_eq_zero
- \+ *theorem* algebraic_independent_iff_injective_aeval
- \+ *theorem* algebraic_independent_equiv
- \+ *theorem* algebraic_independent_equiv'
- \+ *theorem* algebraic_independent_subtype_range
- \+ *theorem* algebraic_independent_image
- \+ *theorem* algebraic_independent.to_subtype_range
- \+ *theorem* algebraic_independent.to_subtype_range'
- \+ *theorem* algebraic_independent_comp_subtype
- \+ *theorem* algebraic_independent_subtype
- \+ *theorem* algebraic_independent.image_of_comp
- \+ *theorem* algebraic_independent.image
- \+ *def* algebraic_independent
- \+ *def* algebraic_independent.aeval_equiv
- \+ *def* algebraic_independent.repr
- \+ *def* is_transcendence_basis



## [2021-10-02 07:33:19](https://github.com/leanprover-community/mathlib/commit/709b449)
chore(algebra/star/basic): provide automorphisms in commutative rings ([#9483](https://github.com/leanprover-community/mathlib/pull/9483))
This adds `star_mul_aut` and `star_ring_aut`, which are the versions of `star_mul_equiv` and `star_ring_equiv` which avoid needing `opposite` due to commutativity.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *def* star_mul_aut
- \+ *def* star_ring_aut



## [2021-10-02 07:33:18](https://github.com/leanprover-community/mathlib/commit/fc7f9f3)
feat(algebra/algebra): the range of `algebra_map (S : subalgebra R A) A` ([#9450](https://github.com/leanprover-community/mathlib/pull/9450))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* map_eq_id
- \+/\- *lemma* map_eq_self
- \+/\- *lemma* map_eq_self

modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* to_subsemiring_subtype
- \+ *lemma* to_subring_subtype
- \+ *lemma* algebra_map_eq
- \+ *lemma* srange_algebra_map
- \+ *lemma* range_algebra_map



## [2021-10-02 07:33:17](https://github.com/leanprover-community/mathlib/commit/a59876f)
feat(ring_theory): quotients of a noetherian ring are noetherian ([#9449](https://github.com/leanprover-community/mathlib/pull/9449))
#### Estimated changes
modified src/ring_theory/noetherian.lean
- \- *theorem* is_noetherian_of_quotient_of_noetherian



## [2021-10-02 04:58:50](https://github.com/leanprover-community/mathlib/commit/37f43bf)
feat(linear_algebra/affine_space/barycentric_coords): define barycentric coordinates ([#9472](https://github.com/leanprover-community/mathlib/pull/9472))
#### Estimated changes
created src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* basis_of_aff_ind_span_eq_top_apply
- \+ *lemma* barycentric_coord_apply_eq
- \+ *lemma* barycentric_coord_apply_neq
- \+ *lemma* barycentric_coord_apply
- \+ *lemma* barycentric_coord_apply_combination

modified src/linear_algebra/affine_space/basic.lean

modified src/linear_algebra/basis.lean
- \+ *lemma* coe_sum_coords
- \+ *lemma* coe_sum_coords_eq_finsum
- \+ *lemma* coe_sum_coords_of_fintype
- \+ *lemma* sum_coords_self_apply
- \+/\- *def* coord
- \+/\- *def* coord



## [2021-10-01 23:08:54](https://github.com/leanprover-community/mathlib/commit/06b184f)
refactor(analysis/convex/caratheodory): generalize ℝ to an arbitrary linearly ordered field ([#9479](https://github.com/leanprover-community/mathlib/pull/9479))
As a result; `convex_independent_iff_finset` also gets generalized.
#### Estimated changes
modified src/analysis/convex/caratheodory.lean
- \+/\- *theorem* eq_pos_convex_span_of_mem_convex_hull
- \+/\- *theorem* eq_pos_convex_span_of_mem_convex_hull

modified src/analysis/convex/extreme.lean

modified src/analysis/convex/independent.lean
- \+/\- *lemma* convex_independent_iff_finset
- \+/\- *lemma* convex_independent_iff_finset



## [2021-10-01 20:36:04](https://github.com/leanprover-community/mathlib/commit/118d45a)
doc(ring_theory/subring): fix docstring of `subring.center` ([#9494](https://github.com/leanprover-community/mathlib/pull/9494))
#### Estimated changes
modified src/ring_theory/subring.lean



## [2021-10-01 20:36:02](https://github.com/leanprover-community/mathlib/commit/e6f8ad7)
refactor(analysis/convex/cone): generalize ℝ to an ordered semiring ([#9481](https://github.com/leanprover-community/mathlib/pull/9481))
Currently, `convex_cone` is only defined in ℝ-modules. This generalizes ℝ to an arbitray ordered semiring. `convex_cone E` is now spelt `convex_cone 𝕜 E`. Similarly, `positive_cone E` becomes `positive_cone 𝕜 E`.
#### Estimated changes
modified src/analysis/convex/cone.lean
- \+/\- *lemma* mem_mk
- \+/\- *lemma* smul_mem
- \+/\- *lemma* coe_inf
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_bot
- \+/\- *lemma* mem_top
- \+/\- *lemma* smul_mem_iff
- \+/\- *lemma* map_map
- \+/\- *lemma* map_id
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_comap
- \+/\- *lemma* mem_comap
- \+/\- *lemma* to_ordered_smul
- \+/\- *lemma* pointed_iff_not_blunt
- \+ *lemma* blunt_iff_not_pointed
- \+/\- *lemma* salient_iff_not_flat
- \+ *lemma* flat.pointed
- \+ *lemma* blunt.salient
- \+ *lemma* salient_positive_cone
- \+ *lemma* pointed_positive_cone
- \+/\- *lemma* mem_to_cone
- \+/\- *lemma* mem_to_cone'
- \+/\- *lemma* to_cone_is_least
- \+/\- *lemma* to_cone_eq_Inf
- \+/\- *lemma* mem_mk
- \+/\- *lemma* smul_mem
- \+/\- *lemma* smul_mem_iff
- \- *lemma* convex
- \+/\- *lemma* coe_inf
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_bot
- \+/\- *lemma* mem_top
- \+/\- *lemma* map_map
- \+/\- *lemma* map_id
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_comap
- \+/\- *lemma* mem_comap
- \+/\- *lemma* to_ordered_smul
- \+/\- *lemma* pointed_iff_not_blunt
- \+/\- *lemma* salient_iff_not_flat
- \- *lemma* salient_of_blunt
- \- *lemma* salient_of_positive_cone
- \- *lemma* pointed_of_positive_cone
- \+/\- *lemma* mem_to_cone
- \+/\- *lemma* mem_to_cone'
- \+/\- *lemma* to_cone_is_least
- \+/\- *lemma* to_cone_eq_Inf
- \+/\- *theorem* ext'
- \+/\- *theorem* ext
- \+/\- *theorem* riesz_extension
- \+/\- *theorem* ext'
- \+/\- *theorem* ext
- \+/\- *theorem* riesz_extension
- \+/\- *def* map
- \+/\- *def* comap
- \+/\- *def* pointed
- \+/\- *def* blunt
- \+/\- *def* flat
- \+/\- *def* salient
- \+/\- *def* to_preorder
- \+/\- *def* to_partial_order
- \+/\- *def* to_ordered_add_comm_group
- \+/\- *def* positive_cone
- \+/\- *def* to_cone
- \+/\- *def* map
- \+/\- *def* comap
- \+/\- *def* pointed
- \+/\- *def* blunt
- \+/\- *def* flat
- \+/\- *def* salient
- \+/\- *def* to_preorder
- \+/\- *def* to_partial_order
- \+/\- *def* to_ordered_add_comm_group
- \+/\- *def* positive_cone
- \+/\- *def* to_cone



## [2021-10-01 20:36:00](https://github.com/leanprover-community/mathlib/commit/05ee42c)
feat(order/circular): define circular orders ([#9413](https://github.com/leanprover-community/mathlib/pull/9413))
A circular order is the way to formalize positions on a circle. This is very foundational, as a good lot of the order-algebra-topology hierarchy has a circular analog.
#### Estimated changes
created src/order/circular.lean
- \+ *lemma* btw_rfl
- \+ *lemma* has_btw.btw.cyclic_left
- \+ *lemma* btw_cyclic_right
- \+ *lemma* btw_cyclic
- \+ *lemma* sbtw_iff_btw_not_btw
- \+ *lemma* btw_of_sbtw
- \+ *lemma* not_btw_of_sbtw
- \+ *lemma* not_sbtw_of_btw
- \+ *lemma* sbtw_of_btw_not_btw
- \+ *lemma* sbtw_cyclic_left
- \+ *lemma* sbtw_cyclic_right
- \+ *lemma* sbtw_cyclic
- \+ *lemma* has_sbtw.sbtw.trans_left
- \+ *lemma* sbtw_trans_right
- \+ *lemma* sbtw_asymm
- \+ *lemma* sbtw_irrefl_left_right
- \+ *lemma* sbtw_irrefl_left
- \+ *lemma* sbtw_irrefl_right
- \+ *lemma* sbtw_irrefl
- \+ *lemma* has_btw.btw.antisymm
- \+ *lemma* btw_refl_left_right
- \+ *lemma* btw_rfl_left_right
- \+ *lemma* btw_refl_left
- \+ *lemma* btw_rfl_left
- \+ *lemma* btw_refl_right
- \+ *lemma* btw_rfl_right
- \+ *lemma* sbtw_iff_not_btw
- \+ *lemma* btw_iff_not_sbtw
- \+ *lemma* mem_cIcc
- \+ *lemma* mem_cIoo
- \+ *lemma* left_mem_cIcc
- \+ *lemma* right_mem_cIcc
- \+ *lemma* compl_cIcc
- \+ *lemma* compl_cIoo
- \+ *def* cIcc
- \+ *def* cIoo
- \+ *def* has_le.to_has_btw
- \+ *def* has_lt.to_has_sbtw
- \+ *def* preorder.to_circular_preorder
- \+ *def* partial_order.to_circular_partial_order
- \+ *def* linear_order.to_circular_order



## [2021-10-01 20:35:59](https://github.com/leanprover-community/mathlib/commit/5c92eb0)
feat(measure_theory/function/conditional_expectation): conditional expectation on real functions equal Radon-Nikodym derivative ([#9378](https://github.com/leanprover-community/mathlib/pull/9378))
#### Estimated changes
modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* rn_deriv_ae_eq_condexp

modified src/measure_theory/measure/with_density_vector_measure.lean
- \+ *lemma* integrable.with_densityᵥ_trim_eq_integral
- \+ *lemma* integrable.with_densityᵥ_trim_absolutely_continuous



## [2021-10-01 20:35:58](https://github.com/leanprover-community/mathlib/commit/75d022b)
feat(probability_theory/density): define probability density functions ([#9323](https://github.com/leanprover-community/mathlib/pull/9323))
This PR also proves some elementary properties about probability density function such as the law of the unconscious statistician.
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* set_lintegral_mono_ae
- \+ *lemma* set_lintegral_mono
- \+ *lemma* set_lintegral_lt_top_of_bdd_above
- \+ *lemma* set_lintegral_lt_top_of_is_compact
- \+ *lemma* with_density_eq_zero

created src/probability_theory/density.lean
- \+ *lemma* has_pdf.measurable
- \+ *lemma* pdf_undef
- \+ *lemma* pdf_eq_zero_of_not_measurable
- \+ *lemma* measurable_of_pdf_ne_zero
- \+ *lemma* measurable_pdf
- \+ *lemma* map_eq_with_density_pdf
- \+ *lemma* map_eq_set_lintegral_pdf
- \+ *lemma* lintegral_eq_measure_univ
- \+ *lemma* ae_lt_top
- \+ *lemma* of_real_to_real_ae_eq
- \+ *lemma* integrable_iff_integrable_mul_pdf
- \+ *lemma* integral_fun_mul_eq_integral
- \+ *lemma* map_absolutely_continuous
- \+ *lemma* to_quasi_measure_preserving
- \+ *lemma* have_lebesgue_decomposition_of_has_pdf
- \+ *lemma* has_pdf_iff
- \+ *lemma* has_pdf_iff_of_measurable
- \+ *lemma* quasi_measure_preserving_has_pdf
- \+ *lemma* quasi_measure_preserving_has_pdf'
- \+ *lemma* real.has_pdf_iff_of_measurable
- \+ *lemma* real.has_pdf_iff
- \+ *lemma* integral_mul_eq_integral
- \+ *lemma* has_finite_integral_mul
- \+ *def* pdf



## [2021-10-01 18:34:46](https://github.com/leanprover-community/mathlib/commit/6354fe9)
feat(topology/algebra): discrete group criterion ([#9488](https://github.com/leanprover-community/mathlib/pull/9488))
#### Estimated changes
modified src/topology/algebra/group.lean
- \+ *lemma* discrete_topology_iff_open_singleton_one



## [2021-10-01 18:34:45](https://github.com/leanprover-community/mathlib/commit/a5fc0a3)
feat(topology/algebra): filters bases for algebra ([#9480](https://github.com/leanprover-community/mathlib/pull/9480))
This is modernized version of code from the perfectoid spaces project.
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* mem_smul_of_mem

modified src/order/filter/bases.lean

created src/topology/algebra/filter_basis.lean
- \+ *lemma* one
- \+ *lemma* mul
- \+ *lemma* inv
- \+ *lemma* conj
- \+ *lemma* prod_subset_self
- \+ *lemma* N_one
- \+ *lemma* nhds_eq
- \+ *lemma* nhds_one_eq
- \+ *lemma* nhds_has_basis
- \+ *lemma* nhds_one_has_basis
- \+ *lemma* mem_nhds_one
- \+ *lemma* mul
- \+ *lemma* mul_left
- \+ *lemma* mul_right
- \+ *lemma* smul
- \+ *lemma* smul_left
- \+ *lemma* smul_right
- \+ *def* group_filter_basis_of_comm
- \+ *def* N
- \+ *def* topology
- \+ *def* topology
- \+ *def* topology
- \+ *def* topology'
- \+ *def* of_bases

modified src/topology/algebra/ring.lean
- \+ *lemma* topological_ring.of_add_group_of_nhds_zero
- \+ *lemma* topological_ring.of_nhds_zero



## [2021-10-01 17:21:37](https://github.com/leanprover-community/mathlib/commit/db6d862)
split(analysis/convex/basic): split off `analysis.convex.hull` ([#9477](https://github.com/leanprover-community/mathlib/pull/9477))
#### Estimated changes
modified src/analysis/convex/basic.lean
- \- *lemma* subset_convex_hull
- \- *lemma* convex_convex_hull
- \- *lemma* convex_hull_min
- \- *lemma* convex_hull_mono
- \- *lemma* convex.convex_hull_eq
- \- *lemma* convex_hull_empty
- \- *lemma* convex_hull_empty_iff
- \- *lemma* convex_hull_nonempty_iff
- \- *lemma* convex_hull_singleton
- \- *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \- *lemma* is_linear_map.image_convex_hull
- \- *lemma* linear_map.image_convex_hull
- \- *lemma* is_linear_map.convex_hull_image
- \- *lemma* linear_map.convex_hull_image
- \- *lemma* affine_map.image_convex_hull
- \- *def* convex_hull

modified src/analysis/convex/combination.lean

modified src/analysis/convex/cone.lean

modified src/analysis/convex/extreme.lean

created src/analysis/convex/hull.lean
- \+ *lemma* subset_convex_hull
- \+ *lemma* convex_convex_hull
- \+ *lemma* convex_hull_min
- \+ *lemma* convex_hull_mono
- \+ *lemma* convex.convex_hull_eq
- \+ *lemma* convex_hull_empty
- \+ *lemma* convex_hull_empty_iff
- \+ *lemma* convex_hull_nonempty_iff
- \+ *lemma* convex_hull_singleton
- \+ *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \+ *lemma* is_linear_map.image_convex_hull
- \+ *lemma* linear_map.image_convex_hull
- \+ *lemma* is_linear_map.convex_hull_image
- \+ *lemma* linear_map.convex_hull_image
- \+ *lemma* affine_map.image_convex_hull
- \+ *def* convex_hull



## [2021-10-01 15:54:07](https://github.com/leanprover-community/mathlib/commit/249a015)
chore(ring_theory/coprime): split out imports into a new file so that `is_coprime` can be used earlier. ([#9403](https://github.com/leanprover-community/mathlib/pull/9403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Use.20of.20is_coprime.20in.20rat.2Ebasic/near/254942750)
#### Estimated changes
modified src/data/polynomial/field_division.lean

modified src/number_theory/fermat4.lean

renamed src/ring_theory/coprime.lean to src/ring_theory/coprime/basic.lean
- \- *theorem* nat.is_coprime_iff_coprime
- \- *theorem* is_coprime.prod_left
- \- *theorem* is_coprime.prod_right
- \- *theorem* finset.prod_dvd_of_coprime
- \- *theorem* fintype.prod_dvd_of_coprime
- \- *theorem* is_coprime.prod_left_iff
- \- *theorem* is_coprime.prod_right_iff
- \- *theorem* is_coprime.of_prod_left
- \- *theorem* is_coprime.of_prod_right
- \- *theorem* is_coprime.pow_left
- \- *theorem* is_coprime.pow_right
- \- *theorem* is_coprime.pow
- \- *theorem* is_coprime.pow_left_iff
- \- *theorem* is_coprime.pow_right_iff
- \- *theorem* is_coprime.pow_iff

created src/ring_theory/coprime/lemmas.lean
- \+ *theorem* nat.is_coprime_iff_coprime
- \+ *theorem* is_coprime.prod_left
- \+ *theorem* is_coprime.prod_right
- \+ *theorem* is_coprime.prod_left_iff
- \+ *theorem* is_coprime.prod_right_iff
- \+ *theorem* is_coprime.of_prod_left
- \+ *theorem* is_coprime.of_prod_right
- \+ *theorem* finset.prod_dvd_of_coprime
- \+ *theorem* fintype.prod_dvd_of_coprime
- \+ *theorem* is_coprime.pow_left
- \+ *theorem* is_coprime.pow_right
- \+ *theorem* is_coprime.pow
- \+ *theorem* is_coprime.pow_left_iff
- \+ *theorem* is_coprime.pow_right_iff
- \+ *theorem* is_coprime.pow_iff

modified src/ring_theory/euclidean_domain.lean

modified src/ring_theory/int/basic.lean



## [2021-10-01 15:54:06](https://github.com/leanprover-community/mathlib/commit/102ce30)
feat(linear_algebra/direct_sum): `submodule_is_internal_iff_independent_and_supr_eq_top` ([#9214](https://github.com/leanprover-community/mathlib/pull/9214))
This shows that a grade decomposition into submodules is bijective iff and only iff the submodules are independent and span the whole module.
The key proofs are:
* `complete_lattice.independent_of_dfinsupp_lsum_injective`
* `complete_lattice.independent.dfinsupp_lsum_injective`
Everything else is just glue.
This replaces parts of [#8246](https://github.com/leanprover-community/mathlib/pull/8246), and uses what is probably a similar proof strategy, but without unfolding down to finsets.
Unlike the proof there, this requires only `add_comm_monoid` for the `complete_lattice.independent_of_dfinsupp_lsum_injective` direction of the proof. I was not able to find a proof of `complete_lattice.independent.dfinsupp_lsum_injective` with the same weak assumptions, as it is not true! A counter-example is included,
#### Estimated changes
created counterexamples/direct_sum_is_internal.lean
- \+ *lemma* units_int.one_ne_neg_one
- \+ *lemma* mem_with_sign_one
- \+ *lemma* mem_with_sign_neg_one
- \+ *lemma* with_sign.is_compl
- \+ *lemma* with_sign.supr
- \+ *lemma* with_sign.not_injective
- \+ *lemma* with_sign.not_internal
- \+ *def* with_sign
- \+ *def* with_sign.independent

modified src/algebra/direct_sum/module.lean
- \+ *lemma* submodule_is_internal.independent
- \+ *lemma* submodule_is_internal_of_independent_of_supr_eq_top
- \+ *lemma* submodule_is_internal_iff_independent_and_supr_eq_top

modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* lsum_single
- \+ *lemma* independent_iff_forall_dfinsupp
- \+ *lemma* independent_of_dfinsupp_lsum_injective
- \+ *lemma* independent.dfinsupp_lsum_injective
- \+ *lemma* independent_iff_dfinsupp_lsum_injective



## [2021-10-01 13:24:12](https://github.com/leanprover-community/mathlib/commit/9be12dd)
feat(order/locally_finite): introduce locally finite orders ([#9464](https://github.com/leanprover-community/mathlib/pull/9464))
The new typeclass `locally_finite_order` homogeneizes treatment of intervals as `finset`s and `multiset`s. `finset.Ico` is now available for all locally finite orders (instead of being ℕ-specialized), rendering `finset.Ico_ℤ` and `pnat.Ico` useless.
This PR also introduces the long-awaited `finset.Icc`, `finset.Ioc`, `finset.Ioo`, and `finset.Ici`, `finset.Ioi` (for `order_top`s) and `finset.Iic`, `finset.Iio` (for `order_bot`s), and the `multiset` variations thereof.
#### Estimated changes
modified src/logic/basic.lean
- \+ *lemma* and_and_and_comm

created src/order/locally_finite.lean
- \+ *lemma* exists_min_greater
- \+ *lemma* mem_Icc
- \+ *lemma* mem_Ioc
- \+ *lemma* mem_Ioo
- \+ *lemma* coe_Icc
- \+ *lemma* coe_Ioc
- \+ *lemma* coe_Ioo
- \+ *lemma* Ici_eq_Icc
- \+ *lemma* Ioi_eq_Ioc
- \+ *lemma* coe_Ici
- \+ *lemma* coe_Ioi
- \+ *lemma* mem_Ici
- \+ *lemma* mem_Ioi
- \+ *lemma* Iic_eq_Icc
- \+ *lemma* coe_Iic
- \+ *lemma* mem_Iic
- \+ *lemma* mem_Icc
- \+ *lemma* mem_Ioc
- \+ *lemma* mem_Ioo
- \+ *lemma* mem_Ici
- \+ *lemma* mem_Ioi
- \+ *lemma* mem_Iic
- \+ *lemma* finite_Icc
- \+ *lemma* finite_Ioc
- \+ *lemma* finite_Ioo
- \+ *lemma* finite_Ici
- \+ *lemma* finite_Ioi
- \+ *lemma* finite_Iic
- \+ *lemma* subtype_Icc_eq
- \+ *lemma* subtype_Ioc_eq
- \+ *lemma* subtype_Ioo_eq
- \+ *lemma* map_subtype_embedding_Icc
- \+ *lemma* map_subtype_embedding_Ioc
- \+ *lemma* map_subtype_embedding_Ioo
- \+ *def* locally_finite_order.of_Icc'
- \+ *def* locally_finite_order.of_Icc
- \+ *def* Icc
- \+ *def* Ioc
- \+ *def* Ioo
- \+ *def* Ici
- \+ *def* Ioi
- \+ *def* Iic
- \+ *def* Icc
- \+ *def* Ioc
- \+ *def* Ioo
- \+ *def* Ici
- \+ *def* Ioi
- \+ *def* Iic



## [2021-10-01 13:24:10](https://github.com/leanprover-community/mathlib/commit/62b8c1f)
feat(order/basic): Antitone functions ([#9119](https://github.com/leanprover-community/mathlib/pull/9119))
Define `antitone` and `strict_anti`. Use them where they already were used in expanded form. Rename lemmas accordingly.
Provide a few more `order_dual` results, and rename `monotone.order_dual` to `monotone.dual`.
Restructure `order.basic`. Now, monotone stuff can easily be singled out to go in a new file `order.monotone` if wanted. It represents 587 out of the 965 lines.
#### Estimated changes
modified src/algebra/order/functions.lean
- \+ *lemma* antitone.map_max
- \+ *lemma* antitone.map_min

modified src/algebra/order/monoid_lemmas.lean
- \+/\- *lemma* strict_mono.mul'
- \+/\- *lemma* monotone.mul_strict_mono'
- \+/\- *lemma* strict_mono.mul'
- \+/\- *lemma* monotone.mul_strict_mono'

modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.strict_mono_on_of_deriv_pos
- \+ *theorem* monotone_of_deriv_nonneg
- \+ *theorem* convex.strict_anti_on_of_deriv_neg
- \+ *theorem* convex.antitone_on_of_deriv_nonpos
- \+/\- *theorem* antitone_of_deriv_nonpos
- \+ *theorem* convex_on_of_deriv_monotone_on
- \+ *theorem* concave_on_of_deriv_antitone_on
- \+ *theorem* convex_on_univ_of_deriv_monotone
- \- *theorem* convex.strict_mono_of_deriv_pos
- \- *theorem* monotone_on_of_deriv_nonneg
- \- *theorem* convex.strict_anti_of_deriv_neg
- \+/\- *theorem* antitone_of_deriv_nonpos
- \- *theorem* convex_on_of_deriv_mono
- \- *theorem* concave_on_of_deriv_antitone
- \- *theorem* convex_on_univ_of_deriv_mono

modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_sin_pow_antitone

modified src/data/complex/exponential.lean
- \- *lemma* forall_ge_le_of_forall_le_succ

modified src/data/set/function.lean
- \+ *lemma* strict_mono_on.comp_strict_anti_on
- \+ *lemma* strict_anti_on.comp
- \+ *lemma* strict_anti_on.comp_strict_mono_on
- \- *lemma* strict_mono.comp_strict_mono_on

modified src/data/set/intervals/surj_on.lean

modified src/data/setoid/basic.lean

modified src/group_theory/nilpotent.lean
- \+/\- *lemma* lower_central_series_antitone
- \+/\- *lemma* lower_central_series_antitone

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* monotone_on.integrable_on_compact
- \+/\- *lemma* antitone_on.integrable_on_compact
- \+/\- *lemma* antitone.integrable_on_compact
- \+/\- *lemma* monotone_on.integrable_on_compact
- \+/\- *lemma* antitone_on.integrable_on_compact
- \+/\- *lemma* antitone.integrable_on_compact

modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* monotone_on.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* antitone.interval_integrable
- \+/\- *lemma* monotone_on.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* antitone.interval_integrable

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/measure_space.lean

modified src/number_theory/pell.lean
- \+ *theorem* strict_mono_y
- \+ *theorem* strict_mono_x
- \- *theorem* y_increasing
- \- *theorem* x_increasing

modified src/order/basic.lean
- \+/\- *lemma* pi.le_def
- \+/\- *lemma* pi.lt_def
- \+/\- *lemma* le_update_iff
- \+/\- *lemma* update_le_iff
- \+/\- *lemma* update_le_update_iff
- \+/\- *lemma* function.monotone_eval
- \+ *lemma* monotone_on_univ
- \+ *lemma* antitone_on_univ
- \+ *lemma* strict_mono_on_univ
- \+ *lemma* strict_anti_on_univ
- \+/\- *lemma* monotone.strict_mono_of_injective
- \+ *lemma* antitone.strict_anti_of_injective
- \+ *lemma* monotone_id
- \+/\- *lemma* strict_mono_id
- \+/\- *lemma* strict_mono_of_le_iff_le
- \+ *lemma* monotone.comp_antitone
- \+ *lemma* antitone.comp_monotone
- \+ *lemma* monotone.comp_antitone_on
- \+ *lemma* antitone.comp_monotone_on
- \+ *lemma* strict_mono.comp_strict_anti
- \+ *lemma* strict_anti.comp_strict_mono
- \+ *lemma* strict_mono.comp_strict_anti_on
- \+ *lemma* strict_anti.comp_strict_mono_on
- \+/\- *lemma* monotone.reflect_lt
- \+ *lemma* antitone.reflect_lt
- \+ *lemma* strict_mono_on.le_iff_le
- \+ *lemma* strict_anti_on.le_iff_le
- \+ *lemma* strict_mono_on.lt_iff_lt
- \+ *lemma* strict_anti_on.lt_iff_lt
- \+ *lemma* strict_mono.le_iff_le
- \+ *lemma* strict_anti.le_iff_le
- \+ *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_anti.lt_iff_lt
- \+ *lemma* strict_mono.injective
- \+ *lemma* strict_anti.injective
- \+ *lemma* strict_mono.maximal_of_maximal_image
- \+ *lemma* strict_mono.minimal_of_minimal_image
- \+ *lemma* strict_anti.minimal_of_maximal_image
- \+ *lemma* strict_anti.maximal_of_minimal_image
- \+/\- *lemma* monotone.strict_mono_iff_injective
- \+ *lemma* antitone.strict_anti_iff_injective
- \+/\- *lemma* monotone_nat_of_le_succ
- \+ *lemma* antitone_nat_of_succ_le
- \+/\- *lemma* strict_mono_nat_of_lt_succ
- \+ *lemma* strict_anti_nat_of_succ_lt
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+/\- *lemma* monotone.ne_of_lt_of_lt_nat
- \+ *lemma* antitone.ne_of_lt_of_lt_nat
- \+/\- *lemma* monotone.ne_of_lt_of_lt_int
- \+ *lemma* antitone.ne_of_lt_of_lt_int
- \+ *lemma* strict_mono.id_le
- \+/\- *lemma* monotone_nat_of_le_succ
- \+/\- *lemma* monotone.reflect_lt
- \+/\- *lemma* monotone.ne_of_lt_of_lt_nat
- \+/\- *lemma* monotone.ne_of_lt_of_lt_int
- \+/\- *lemma* strict_mono_id
- \- *lemma* le_iff_le
- \- *lemma* lt_iff_lt
- \- *lemma* le_iff_le
- \- *lemma* lt_iff_lt
- \- *lemma* comp
- \- *lemma* id_le
- \- *lemma* lt_iff_lt
- \- *lemma* injective
- \- *lemma* le_iff_le
- \- *lemma* maximal_preimage_top
- \- *lemma* minimal_preimage_bot
- \- *lemma* monotone
- \+/\- *lemma* strict_mono_nat_of_lt_succ
- \+/\- *lemma* monotone.strict_mono_of_injective
- \+/\- *lemma* monotone.strict_mono_iff_injective
- \+/\- *lemma* strict_mono_of_le_iff_le
- \+/\- *lemma* function.monotone_eval
- \+/\- *lemma* pi.le_def
- \+/\- *lemma* pi.lt_def
- \+/\- *lemma* le_update_iff
- \+/\- *lemma* update_le_iff
- \+/\- *lemma* update_le_update_iff
- \+ *theorem* monotone.comp_le_comp_left
- \+/\- *theorem* monotone_lam
- \+/\- *theorem* monotone_app
- \+ *theorem* antitone_lam
- \+ *theorem* antitone_app
- \+/\- *theorem* monotone_const
- \+ *theorem* antitone_const
- \- *theorem* monotone_id
- \+/\- *theorem* monotone_const
- \- *theorem* comp_le_comp_left_of_monotone
- \+/\- *theorem* monotone_lam
- \+/\- *theorem* monotone_app
- \- *theorem* strict_mono.order_dual
- \+/\- *def* monotone
- \+ *def* antitone
- \+ *def* monotone_on
- \+ *def* antitone_on
- \+/\- *def* strict_mono
- \+ *def* strict_anti
- \+/\- *def* strict_mono_on
- \+/\- *def* strict_anti_on
- \+/\- *def* monotone
- \+/\- *def* strict_mono
- \+/\- *def* strict_mono_on
- \+/\- *def* strict_anti_on

modified src/order/bounded_lattice.lean
- \+ *lemma* strict_mono.maximal_preimage_top
- \+ *lemma* strict_mono.minimal_preimage_bot
- \- *lemma* strict_mono.maximal_preimage_top'
- \- *lemma* strict_mono.minimal_preimage_bot'

modified src/order/complete_lattice.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/at_top_bot.lean

modified src/order/filter/ennreal.lean

modified src/order/filter/extr.lean

modified src/order/filter/indicator_function.lean

modified src/order/galois_connection.lean

modified src/order/iterate.lean

modified src/order/lattice.lean
- \+/\- *theorem* monotone.forall_le_of_antitone
- \+/\- *theorem* monotone.forall_le_of_antitone

modified src/order/modular_lattice.lean

modified src/order/ord_continuous.lean

modified src/order/preorder_hom.lean

modified src/testing/slim_check/functions.lean

modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem'
- \+ *lemma* is_glb.exists_seq_antitone_tendsto'
- \+ *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem
- \+ *lemma* is_glb.exists_seq_antitone_tendsto
- \+ *lemma* exists_seq_strict_anti_tendsto'
- \+ *lemma* exists_seq_strict_anti_tendsto
- \+/\- *lemma* tendsto_at_bot_is_lub
- \+/\- *lemma* tendsto_at_top_is_glb
- \+/\- *lemma* tendsto_at_bot_csupr
- \+/\- *lemma* tendsto_at_top_cinfi
- \+/\- *lemma* tendsto_at_bot_supr
- \+/\- *lemma* tendsto_at_top_infi
- \- *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem'
- \- *lemma* is_glb.exists_seq_monotone_tendsto'
- \- *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem
- \- *lemma* is_glb.exists_seq_monotone_tendsto
- \- *lemma* exists_seq_strict_antitone_tendsto'
- \- *lemma* exists_seq_strict_antitone_tendsto
- \+/\- *lemma* tendsto_at_bot_is_lub
- \+/\- *lemma* tendsto_at_top_is_glb
- \+/\- *lemma* tendsto_at_bot_csupr
- \+/\- *lemma* tendsto_at_top_cinfi
- \+/\- *lemma* tendsto_at_bot_supr
- \+/\- *lemma* tendsto_at_top_infi

modified src/topology/local_extr.lean

modified src/topology/semicontinuous.lean



## [2021-10-01 13:24:08](https://github.com/leanprover-community/mathlib/commit/d6bf2dd)
refactor(*): replace `abs` with vertical bar notation ([#8891](https://github.com/leanprover-community/mathlib/pull/8891))
The notion of an "absolute value" occurs both in algebra (e.g. lattice ordered groups) and analysis (e.g. GM and GL-spaces). I introduced a `has_abs` notation class in [#9172](https://github.com/leanprover-community/mathlib/pull/9172), along with the  conventional mathematical vertical bar notation `|.|` for `abs`.
The notation vertical bar notation was already in use in some files as a local notation. This PR replaces `abs` with the vertical bar notation throughout mathlib.
#### Estimated changes
modified archive/imo/imo2006_q3.lean

modified archive/imo/imo2008_q4.lean
- \+/\- *lemma* abs_eq_one_of_pow_eq_one
- \+/\- *lemma* abs_eq_one_of_pow_eq_one

modified archive/sensitivity.lean

modified counterexamples/phillips.lean

modified src/algebra/archimedean.lean
- \+/\- *lemma* abs_sub_round
- \+/\- *lemma* abs_sub_round

modified src/algebra/big_operators/order.lean

modified src/algebra/continued_fractions/computation/approximation_corollaries.lean

modified src/algebra/continued_fractions/computation/approximations.lean

modified src/algebra/field_power.lean

modified src/algebra/floor.lean

modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* abs_pow
- \+/\- *lemma* abs_pow

modified src/algebra/group_power/order.lean
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *theorem* sq_abs
- \+/\- *theorem* abs_sq
- \+/\- *theorem* sq_lt_sq
- \+/\- *theorem* sq_le_sq
- \+/\- *theorem* abs_lt_abs_of_sq_lt_sq
- \+/\- *theorem* abs_lt_of_sq_lt_sq
- \+/\- *theorem* abs_le_abs_of_sq_le_sq
- \+/\- *theorem* abs_le_of_sq_le_sq
- \+/\- *theorem* sq_abs
- \+/\- *theorem* abs_sq
- \+/\- *theorem* sq_lt_sq
- \+/\- *theorem* sq_le_sq
- \+/\- *theorem* abs_lt_abs_of_sq_lt_sq
- \+/\- *theorem* abs_lt_of_sq_lt_sq
- \+/\- *theorem* abs_le_abs_of_sq_le_sq
- \+/\- *theorem* abs_le_of_sq_le_sq

modified src/algebra/order/field.lean
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_one_div
- \+/\- *lemma* abs_inv
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_one_div
- \+/\- *lemma* abs_inv

modified src/algebra/order/group.lean
- \+/\- *lemma* abs_choice
- \+/\- *lemma* abs_le'
- \+/\- *lemma* le_abs
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* neg_le_abs_self
- \+/\- *lemma* lt_abs
- \+/\- *lemma* abs_by_cases
- \+/\- *lemma* abs_neg
- \+/\- *lemma* eq_or_eq_neg_of_abs_eq
- \+/\- *lemma* abs_eq_abs
- \+/\- *lemma* abs_sub_comm
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* neg_abs_le_self
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_eq_zero
- \+/\- *lemma* abs_nonpos_iff
- \+/\- *lemma* abs_lt
- \+/\- *lemma* neg_lt_of_abs_lt
- \+/\- *lemma* lt_of_abs_lt
- \+/\- *lemma* max_sub_min_eq_abs'
- \+/\- *lemma* max_sub_min_eq_abs
- \+/\- *lemma* abs_le
- \+/\- *lemma* neg_le_of_abs_le
- \+/\- *lemma* le_of_abs_le
- \+/\- *lemma* abs_add
- \+/\- *lemma* abs_sub_le_iff
- \+/\- *lemma* abs_sub_lt_iff
- \+/\- *lemma* sub_le_of_abs_sub_le_left
- \+/\- *lemma* sub_le_of_abs_sub_le_right
- \+/\- *lemma* sub_lt_of_abs_sub_lt_left
- \+/\- *lemma* sub_lt_of_abs_sub_lt_right
- \+/\- *lemma* abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_eq
- \+/\- *lemma* abs_le_max_abs_abs
- \+/\- *lemma* eq_of_abs_sub_eq_zero
- \+/\- *lemma* abs_sub_le
- \+/\- *lemma* abs_add_three
- \+/\- *lemma* eq_of_abs_sub_nonpos
- \+/\- *lemma* abs_max_sub_max_le_abs
- \+/\- *lemma* abs_choice
- \+/\- *lemma* abs_le'
- \+/\- *lemma* le_abs
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* neg_le_abs_self
- \+/\- *lemma* lt_abs
- \+/\- *lemma* abs_by_cases
- \+/\- *lemma* abs_neg
- \+/\- *lemma* eq_or_eq_neg_of_abs_eq
- \+/\- *lemma* abs_eq_abs
- \+/\- *lemma* abs_sub_comm
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* neg_abs_le_self
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_eq_zero
- \+/\- *lemma* abs_nonpos_iff
- \+/\- *lemma* abs_lt
- \+/\- *lemma* neg_lt_of_abs_lt
- \+/\- *lemma* lt_of_abs_lt
- \+/\- *lemma* max_sub_min_eq_abs'
- \+/\- *lemma* max_sub_min_eq_abs
- \+/\- *lemma* abs_le
- \+/\- *lemma* neg_le_of_abs_le
- \+/\- *lemma* le_of_abs_le
- \+/\- *lemma* abs_add
- \+/\- *lemma* abs_sub_le_iff
- \+/\- *lemma* abs_sub_lt_iff
- \+/\- *lemma* sub_le_of_abs_sub_le_left
- \+/\- *lemma* sub_le_of_abs_sub_le_right
- \+/\- *lemma* sub_lt_of_abs_sub_lt_left
- \+/\- *lemma* sub_lt_of_abs_sub_lt_right
- \+/\- *lemma* abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_eq
- \+/\- *lemma* abs_le_max_abs_abs
- \+/\- *lemma* eq_of_abs_sub_eq_zero
- \+/\- *lemma* abs_sub_le
- \+/\- *lemma* abs_add_three
- \+/\- *lemma* eq_of_abs_sub_nonpos
- \+/\- *lemma* abs_max_sub_max_le_abs
- \+/\- *theorem* abs_le_abs
- \+/\- *theorem* abs_le_abs

modified src/algebra/order/ring.lean
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_two
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+/\- *lemma* abs_eq_self
- \+/\- *lemma* abs_eq_neg_self
- \+/\- *lemma* abs_cases
- \+/\- *lemma* abs_eq_iff_mul_self_eq
- \+/\- *lemma* abs_lt_iff_mul_self_lt
- \+/\- *lemma* abs_le_iff_mul_self_le
- \+/\- *lemma* abs_le_one_iff_mul_self_le_one
- \+/\- *lemma* abs_sub_sq
- \+/\- *lemma* abs_dvd
- \+/\- *lemma* abs_dvd_self
- \+/\- *lemma* dvd_abs
- \+/\- *lemma* self_dvd_abs
- \+/\- *lemma* abs_dvd_abs
- \+/\- *lemma* even_abs
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_two
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+/\- *lemma* abs_eq_self
- \+/\- *lemma* abs_eq_neg_self
- \+/\- *lemma* abs_cases
- \+/\- *lemma* abs_eq_iff_mul_self_eq
- \+/\- *lemma* abs_lt_iff_mul_self_lt
- \+/\- *lemma* abs_le_iff_mul_self_le
- \+/\- *lemma* abs_le_one_iff_mul_self_le_one
- \+/\- *lemma* abs_sub_sq
- \+/\- *lemma* abs_dvd
- \+/\- *lemma* abs_dvd_self
- \+/\- *lemma* dvd_abs
- \+/\- *lemma* self_dvd_abs
- \+/\- *lemma* abs_dvd_abs
- \+/\- *lemma* even_abs

modified src/analysis/analytic/basic.lean

modified src/analysis/calculus/parametric_integral.lean

modified src/analysis/complex/basic.lean
- \+/\- *lemma* norm_int
- \+/\- *lemma* norm_int

modified src/analysis/convex/topology.lean

modified src/analysis/mean_inequalities.lean

modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* real.norm_eq_abs
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* int.norm_eq_abs
- \+/\- *lemma* abs_norm_eq_norm
- \+/\- *lemma* real.norm_eq_abs
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* int.norm_eq_abs
- \+/\- *lemma* abs_norm_eq_norm

modified src/analysis/normed_space/normed_group_hom.lean

modified src/analysis/special_functions/bernstein.lean

modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* log_of_ne_zero
- \+/\- *lemma* exp_log_eq_abs
- \+/\- *lemma* log_abs
- \+/\- *lemma* abs_log_sub_add_sum_range_le
- \+/\- *lemma* log_of_ne_zero
- \+/\- *lemma* exp_log_eq_abs
- \+/\- *lemma* log_abs
- \+/\- *lemma* abs_log_sub_add_sum_range_le
- \+/\- *theorem* has_sum_pow_div_log_of_abs_lt_1
- \+/\- *theorem* has_sum_pow_div_log_of_abs_lt_1

modified src/analysis/special_functions/polynomials.lean

modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* abs_rpow_le_abs_rpow
- \+/\- *lemma* abs_rpow_le_exp_log_mul
- \+/\- *lemma* abs_rpow_of_nonneg
- \+/\- *lemma* abs_rpow_le_abs_rpow
- \+/\- *lemma* abs_rpow_le_exp_log_mul
- \+/\- *lemma* abs_rpow_of_nonneg

modified src/analysis/special_functions/trigonometric/basic.lean

modified src/analysis/specific_limits.lean
- \+/\- *lemma* is_o_pow_pow_of_abs_lt_left
- \+/\- *lemma* tendsto_pow_const_mul_const_pow_of_abs_lt_one
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_abs_lt_1
- \+/\- *lemma* has_sum_geometric_of_abs_lt_1
- \+/\- *lemma* summable_geometric_of_abs_lt_1
- \+/\- *lemma* tsum_geometric_of_abs_lt_1
- \+/\- *lemma* is_o_pow_pow_of_abs_lt_left
- \+/\- *lemma* tendsto_pow_const_mul_const_pow_of_abs_lt_one
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_abs_lt_1
- \+/\- *lemma* has_sum_geometric_of_abs_lt_1
- \+/\- *lemma* summable_geometric_of_abs_lt_1
- \+/\- *lemma* tsum_geometric_of_abs_lt_1

modified src/data/complex/basic.lean
- \+/\- *lemma* abs_of_real
- \+/\- *lemma* abs_re_le_abs
- \+/\- *lemma* abs_im_le_abs
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_abs_sub_le_abs_sub
- \+/\- *lemma* abs_le_abs_re_add_abs_im
- \+/\- *lemma* abs_re_div_abs_le_one
- \+/\- *lemma* abs_im_div_abs_le_one
- \+/\- *lemma* int_cast_abs
- \+/\- *lemma* abs_of_real
- \+/\- *lemma* abs_re_le_abs
- \+/\- *lemma* abs_im_le_abs
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_abs_sub_le_abs_sub
- \+/\- *lemma* abs_le_abs_re_add_abs_im
- \+/\- *lemma* abs_re_div_abs_le_one
- \+/\- *lemma* abs_im_div_abs_le_one
- \+/\- *lemma* int_cast_abs

modified src/data/complex/exponential.lean
- \+/\- *lemma* is_cau_of_decreasing_bounded
- \+/\- *lemma* is_cau_of_mono_bounded
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* abs_sin_le_one
- \+/\- *lemma* abs_cos_le_one
- \+/\- *lemma* abs_exp
- \+/\- *lemma* exp_bound
- \+/\- *lemma* cos_bound
- \+/\- *lemma* sin_bound
- \+/\- *lemma* cos_pos_of_le_one
- \+/\- *lemma* is_cau_of_decreasing_bounded
- \+/\- *lemma* is_cau_of_mono_bounded
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* abs_sin_le_one
- \+/\- *lemma* abs_cos_le_one
- \+/\- *lemma* abs_exp
- \+/\- *lemma* exp_bound
- \+/\- *lemma* cos_bound
- \+/\- *lemma* sin_bound
- \+/\- *lemma* cos_pos_of_le_one

modified src/data/int/basic.lean
- \+/\- *lemma* eq_zero_iff_abs_lt_one
- \+/\- *lemma* eq_zero_iff_abs_lt_one
- \+/\- *theorem* abs_eq_nat_abs
- \+/\- *theorem* nat_abs_abs
- \+/\- *theorem* sign_mul_abs
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* div_eq_zero_of_lt_abs
- \+/\- *theorem* mod_abs
- \+/\- *theorem* mod_lt
- \+/\- *theorem* abs_div_le_abs
- \+/\- *theorem* abs_eq_nat_abs
- \+/\- *theorem* nat_abs_abs
- \+/\- *theorem* sign_mul_abs
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* div_eq_zero_of_lt_abs
- \+/\- *theorem* mod_abs
- \+/\- *theorem* mod_lt
- \+/\- *theorem* abs_div_le_abs

modified src/data/int/cast.lean
- \+/\- *lemma* cast_nat_abs
- \+/\- *lemma* cast_nat_abs

modified src/data/int/modeq.lean

modified src/data/nat/cast.lean

modified src/data/polynomial/denoms_clearable.lean

modified src/data/rat/cast.lean

modified src/data/rat/order.lean
- \+/\- *theorem* abs_def
- \+/\- *theorem* abs_def

modified src/data/rat/sqrt.lean
- \+/\- *theorem* sqrt_eq
- \+/\- *theorem* sqrt_eq

modified src/data/real/basic.lean
- \+/\- *theorem* is_cau_seq_iff_lift
- \+/\- *theorem* is_cau_seq_iff_lift

modified src/data/real/hyperreal.lean
- \+/\- *lemma* coe_abs
- \+/\- *lemma* infinite_pos_abs_iff_infinite_abs
- \+/\- *lemma* infinite_iff_infinite_pos_abs
- \+/\- *lemma* infinite_iff_infinite_abs
- \+/\- *lemma* infinite_iff_abs_lt_abs
- \+/\- *lemma* coe_abs
- \+/\- *lemma* infinite_pos_abs_iff_infinite_abs
- \+/\- *lemma* infinite_iff_infinite_pos_abs
- \+/\- *lemma* infinite_iff_infinite_abs
- \+/\- *lemma* infinite_iff_abs_lt_abs

modified src/data/real/nnreal.lean
- \+/\- *lemma* abs_eq
- \+/\- *lemma* coe_nnabs
- \+/\- *lemma* coe_to_nnreal_le
- \+/\- *lemma* abs_eq
- \+/\- *lemma* coe_nnabs
- \+/\- *lemma* coe_to_nnreal_le

modified src/data/real/sqrt.lean
- \+/\- *theorem* sqrt_mul_self_eq_abs
- \+/\- *theorem* sqrt_sq_eq_abs
- \+/\- *theorem* abs_le_sqrt
- \+/\- *theorem* sqrt_mul_self_eq_abs
- \+/\- *theorem* sqrt_sq_eq_abs
- \+/\- *theorem* abs_le_sqrt

modified src/data/set/intervals/basic.lean

modified src/data/set/intervals/unordered_interval.lean
- \+/\- *lemma* abs_sub_le_of_subinterval
- \+/\- *lemma* abs_sub_left_of_mem_interval
- \+/\- *lemma* abs_sub_right_of_mem_interval
- \+/\- *lemma* abs_sub_le_of_subinterval
- \+/\- *lemma* abs_sub_left_of_mem_interval
- \+/\- *lemma* abs_sub_right_of_mem_interval

modified src/geometry/euclidean/basic.lean

modified src/geometry/euclidean/circumcenter.lean

modified src/geometry/euclidean/sphere.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* norm_integral_le_abs_integral_norm
- \+/\- *lemma* norm_integral_le_abs_integral_norm

modified src/measure_theory/measure/lebesgue.lean
- \+/\- *lemma* volume_interval
- \+/\- *lemma* volume_interval

modified src/number_theory/liouville/basic.lean
- \+/\- *def* liouville
- \+/\- *def* liouville

modified src/number_theory/liouville/liouville_constant.lean

modified src/number_theory/primes_congruent_one.lean

modified src/number_theory/zsqrtd/gaussian_int.lean
- \+/\- *lemma* norm_sq_le_norm_sq_of_re_le_of_im_le
- \+/\- *lemma* norm_sq_le_norm_sq_of_re_le_of_im_le

modified src/order/filter/filter_product.lean
- \+/\- *lemma* abs_def
- \+/\- *lemma* abs_def

modified src/testing/slim_check/sampleable.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered/basic.lean

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* min_eq_half_add_sub_abs_sub
- \+/\- *lemma* max_eq_half_add_add_abs_sub
- \+/\- *lemma* min_eq_half_add_sub_abs_sub
- \+/\- *lemma* max_eq_half_add_add_abs_sub

modified src/topology/continuous_function/bounded.lean

modified src/topology/continuous_function/weierstrass.lean

modified src/topology/instances/real.lean
- \+/\- *lemma* real.uniform_continuous_inv
- \+/\- *lemma* real.uniform_continuous_inv
- \+/\- *theorem* rat.dist_eq
- \+/\- *theorem* dist_eq
- \+/\- *theorem* rat.dist_eq
- \+/\- *theorem* dist_eq

modified src/topology/metric_space/algebra.lean

modified src/topology/metric_space/basic.lean
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *theorem* abs_dist_sub_le
- \+/\- *theorem* abs_dist
- \+/\- *theorem* real.dist_eq
- \+/\- *theorem* real.dist_0_eq_abs
- \+/\- *theorem* abs_dist_sub_le
- \+/\- *theorem* abs_dist
- \+/\- *theorem* real.dist_eq
- \+/\- *theorem* real.dist_0_eq_abs

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/kuratowski.lean

modified test/push_neg.lean



## [2021-10-01 12:27:23](https://github.com/leanprover-community/mathlib/commit/c33407a)
feat(algebraic_geometry/*): Proved Spec ⋙ Γ ≅ 𝟭 ([#9416](https://github.com/leanprover-community/mathlib/pull/9416))
- Specialied `algebraic_geometry.structure_sheaf.basic_open_iso` into global sections, proving that the map `structure_sheaf.to_open R ⊤` is an isomorphism in `algebraic_geometry.is_iso_to_global`.
- Proved that the map `R ⟶ Γ(Spec R)` is natural, and presents the fact above as an natural isomorphism `Spec.right_op ⋙ Γ ≅ 𝟭 _` in `algebraic_geometry.Spec_Γ_identity`.
#### Estimated changes
modified src/algebraic_geometry/Spec.lean
- \+ *lemma* Spec_Γ_naturality
- \+ *def* to_Spec_Γ
- \+ *def* Spec_Γ_identity

modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* to_global_factors
- \+ *lemma* global_sections_iso_hom
- \+ *def* global_sections_iso



## [2021-10-01 10:38:53](https://github.com/leanprover-community/mathlib/commit/38395ed)
chore(bors): bors should block on label awaiting-CI ([#9478](https://github.com/leanprover-community/mathlib/pull/9478))
#### Estimated changes
modified bors.toml

modified docs/contribute/bors.md



## [2021-10-01 10:38:52](https://github.com/leanprover-community/mathlib/commit/5936f53)
feat(topology/maps): for a continuous open map, preimage and interior commute ([#9471](https://github.com/leanprover-community/mathlib/pull/9471))
#### Estimated changes
modified src/topology/basic.lean

modified src/topology/maps.lean
- \+ *lemma* interior_preimage_subset_preimage_interior
- \+ *lemma* preimage_interior_eq_interior_preimage



## [2021-10-01 10:38:51](https://github.com/leanprover-community/mathlib/commit/265345c)
feat(linear_algebra/{bilinear,quadratic}_form): remove non-degeneracy requirement from `exists_orthogonal_basis` and Sylvester's law of inertia ([#9465](https://github.com/leanprover-community/mathlib/pull/9465))
This removes the `nondegenerate` hypothesis from `bilin_form.exists_orthogonal_basis`, and removes the `∀ i, B (v i) (v i) ≠ 0` statement from the goal. This property can be recovered in the case of a nondegenerate form with `is_Ortho.not_is_ortho_basis_self_of_nondegenerate`.
This also swaps the order of the binders in `is_Ortho` to make it expressible with `pairwise`.
#### Estimated changes
modified docs/undergrad.yaml

modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* is_Ortho.not_is_ortho_basis_self_of_nondegenerate
- \+ *lemma* is_Ortho.nondegenerate_iff_not_is_ortho_basis_self

modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* to_quadratic_form_zero
- \+ *lemma* exists_quadratic_form_ne_zero
- \+ *lemma* to_linear_equiv_eq_coe
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* exists_bilin_form_self_ne_zero
- \+ *lemma* exists_orthogonal_basis
- \+ *lemma* basis_repr_eq_of_is_Ortho
- \+ *lemma* equivalent_weighted_sum_squares
- \+ *lemma* equivalent_weighted_sum_squares_units_of_nondegenerate'
- \- *lemma* exists_quadratic_form_neq_zero
- \- *lemma* exists_bilin_form_self_neq_zero
- \- *lemma* exists_orthogonal_basis'
- \- *lemma* isometry_of_is_Ortho_apply
- \- *lemma* equivalent_weighted_sum_squares_of_nondegenerate'
- \+ *theorem* equivalent_one_zero_neg_one_weighted_sum_squared
- \- *theorem* exists_orthogonal_basis



## [2021-10-01 10:38:49](https://github.com/leanprover-community/mathlib/commit/74457cb)
feat(data/polynomial,field_theory): `(minpoly A x).map f ≠ 1` ([#9451](https://github.com/leanprover-community/mathlib/pull/9451))
We use this result to generalize `minpoly.not_is_unit` from integral domains to nontrivial `comm_ring`s.
#### Estimated changes
modified src/data/polynomial/monic.lean
- \+ *lemma* eq_one_of_map_eq_one

modified src/field_theory/minpoly.lean
- \+ *lemma* ne_one
- \+ *lemma* map_ne_one
- \+/\- *lemma* not_is_unit
- \+/\- *lemma* not_is_unit



## [2021-10-01 08:55:56](https://github.com/leanprover-community/mathlib/commit/f7d7a91)
feat(algebraic_geometry/ringed_space): Define basic opens for ringed spaces. ([#9358](https://github.com/leanprover-community/mathlib/pull/9358))
Defines the category of ringed spaces, as an alias for `SheafedSpace CommRing`. We provide basic lemmas about sections being units in the stalk and define basic opens in this context.
#### Estimated changes
modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* to_RingedSpace

created src/algebraic_geometry/ringed_space.lean
- \+ *lemma* is_unit_res_of_is_unit_germ
- \+ *lemma* is_unit_of_is_unit_germ
- \+ *lemma* mem_basic_open
- \+ *lemma* is_unit_res_basic_open
- \+ *def* basic_open



## [2021-10-01 08:55:55](https://github.com/leanprover-community/mathlib/commit/9235c8a)
feat(data/polynomial/basic): polynomial.update ([#9020](https://github.com/leanprover-community/mathlib/pull/9020))
#### Estimated changes
modified src/data/polynomial/basic.lean
- \+ *lemma* coeff_update
- \+ *lemma* coeff_update_apply
- \+ *lemma* coeff_update_same
- \+ *lemma* coeff_update_ne
- \+ *lemma* update_zero_eq_erase
- \+ *lemma* support_update
- \+ *lemma* support_update_zero
- \+ *lemma* support_update_ne_zero
- \+ *def* update

modified src/data/polynomial/coeff.lean
- \+ *lemma* update_eq_add_sub_coeff

modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* degree_update_le



## [2021-10-01 06:05:13](https://github.com/leanprover-community/mathlib/commit/e0f7d0e)
feat(group_theory/complement): is_complement_iff_card_mul_and_disjoint ([#9476](https://github.com/leanprover-community/mathlib/pull/9476))
Adds the converse to an existing lemma `is_complement_of_disjoint` (renamed `is_complement_of_card_mul_and_disjoint`).
#### Estimated changes
modified src/group_theory/complement.lean
- \+ *lemma* is_complement.card_mul
- \+ *lemma* is_complement.disjoint
- \+ *lemma* is_complement_of_card_mul_and_disjoint
- \+ *lemma* is_complement_iff_card_mul_and_disjoint
- \- *lemma* is_complement_of_disjoint



## [2021-10-01 06:05:12](https://github.com/leanprover-community/mathlib/commit/57fa903)
refactor(group_theory/complement): Split `complement.lean` ([#9474](https://github.com/leanprover-community/mathlib/pull/9474))
Splits off Schur-Zassenhaus from `complement.lean`. In the new file, we can replace `fintype.card (quotient_group.quotient H)` with `H.index`.
Advantages: We can avoid importing `cardinal.lean` in `complement.lean`. Later (once full SZ is proved), we can avoid importing `sylow.lean` in `complement.lean`.
#### Estimated changes
modified src/group_theory/complement.lean
- \- *lemma* smul_symm_apply_eq_mul_symm_apply_inv_smul
- \- *lemma* diff_mul_diff
- \- *lemma* diff_self
- \- *lemma* diff_inv
- \- *lemma* smul_diff_smul
- \- *lemma* smul_diff
- \- *lemma* exists_smul_eq
- \- *lemma* smul_left_injective
- \- *lemma* is_complement_stabilizer_of_coprime
- \- *theorem* exists_right_complement_of_coprime
- \- *theorem* exists_left_complement_of_coprime
- \- *def* quotient_diff

created src/group_theory/schur_zassenhaus.lean
- \+ *lemma* smul_symm_apply_eq_mul_symm_apply_inv_smul
- \+ *lemma* diff_mul_diff
- \+ *lemma* diff_self
- \+ *lemma* diff_inv
- \+ *lemma* smul_diff_smul
- \+ *lemma* smul_diff
- \+ *lemma* exists_smul_eq
- \+ *lemma* smul_left_injective
- \+ *lemma* is_complement_stabilizer_of_coprime
- \+ *theorem* exists_right_complement_of_coprime
- \+ *theorem* exists_left_complement_of_coprime
- \+ *def* quotient_diff



## [2021-10-01 06:05:11](https://github.com/leanprover-community/mathlib/commit/76ddb2b)
feat(analysis/normed_space/lattice_ordered_group): introduce normed lattice ordered groups ([#9274](https://github.com/leanprover-community/mathlib/pull/9274))
Motivated by Banach Lattices, this PR introduces normed lattice ordered groups and proves that they are topological lattices. To support this `has_continuous_inf` and `has_continuous_sup` mixin classes are also defined.
#### Estimated changes
modified docs/references.bib

modified src/algebra/order/group.lean
- \+ *lemma* abs_eq_sup_neg
- \+/\- *lemma* abs_eq_max_neg
- \+/\- *lemma* abs_eq_max_neg

created src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* solid
- \+ *lemma* dual_solid
- \+ *lemma* norm_abs_eq_norm

created src/topology/order/lattice.lean
- \+ *lemma* continuous_inf
- \+ *lemma* continuous.inf
- \+ *lemma* continuous_sup
- \+ *lemma* continuous.sup



## [2021-10-01 03:25:37](https://github.com/leanprover-community/mathlib/commit/812d6bb)
chore(scripts): update nolints.txt ([#9475](https://github.com/leanprover-community/mathlib/pull/9475))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2021-10-01 03:25:36](https://github.com/leanprover-community/mathlib/commit/125dac8)
feat(group_theory/sylow): The number of Sylow subgroups equals the index of the normalizer ([#9455](https://github.com/leanprover-community/mathlib/pull/9455))
This PR adds further consequences of Sylow's theorems (still for infinite groups, more will be PRed later).
#### Estimated changes
modified src/group_theory/sylow.lean
- \+ *lemma* sylow.orbit_eq_top
- \+ *lemma* sylow.stabilizer_eq_normalizer
- \+ *lemma* card_sylow_eq_card_quotient_normalizer
- \+ *lemma* card_sylow_eq_index_normalizer
- \+ *lemma* card_sylow_dvd_index



## [2021-10-01 03:25:35](https://github.com/leanprover-community/mathlib/commit/b786443)
chore(algebra/category/*): Added `of_hom` to all of the algebraic categories. ([#9454](https://github.com/leanprover-community/mathlib/pull/9454))
As suggested in the comments of [#9416](https://github.com/leanprover-community/mathlib/pull/9416).
#### Estimated changes
modified src/algebra/category/Algebra/basic.lean
- \+ *def* of_hom

modified src/algebra/category/CommRing/basic.lean
- \+ *def* of_hom
- \+ *def* of_hom
- \+ *def* of_hom
- \+ *def* of_hom

modified src/algebra/category/Group/basic.lean
- \+ *def* of_hom
- \+ *def* of_hom

modified src/algebra/category/Module/basic.lean
- \+ *def* of_hom

modified src/algebra/category/Mon/basic.lean
- \+ *def* of_hom

modified src/algebra/category/Semigroup/basic.lean
- \+ *def* of_hom
- \+ *def* of_hom



## [2021-10-01 03:25:34](https://github.com/leanprover-community/mathlib/commit/babca8e)
refactor(algebra/group_with_zero): rename lemmas to use ₀ instead of ' ([#9424](https://github.com/leanprover-community/mathlib/pull/9424))
We currently have lots of lemmas for `group_with_zero` that already have a corresponding lemma for `group`. We've dealt with name collisions so far just by adding a prime.
This PR renames these lemmas to use a `₀` suffix instead of a `'`.
In part this is out of desire to reduce our overuse of primes in mathlib names (putting the burden on users to know names, rather than relying on naming conventions).
But it may also help with a problem Daniel Selsam ran into at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mathport.20depending.20on.20mathlib. (Briefly, mathport is also adding primes to names when it encounters name collisions, and these particular primes were causing problems. There are are other potential fixes in the works, but everything helps.)
#### Estimated changes
modified archive/100-theorems-list/70_perfect_numbers.lean

modified src/algebra/algebra/bilinear.lean

modified src/algebra/archimedean.lean

modified src/algebra/associated.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/field.lean
- \+/\- *lemma* neg_div'
- \+/\- *lemma* map_inv
- \+/\- *lemma* neg_div'
- \+/\- *lemma* map_inv

modified src/algebra/gcd_monoid/basic.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group/conj.lean
- \+ *lemma* is_conj_iff₀
- \- *lemma* is_conj_iff'

modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_right_inj'
- \+ *lemma* mul_inv_cancel_right₀
- \+ *lemma* mul_inv_cancel_left₀
- \+ *lemma* inv_mul_cancel_right₀
- \+ *lemma* inv_mul_cancel_left₀
- \+ *lemma* inv_inv₀
- \+ *lemma* inv_involutive₀
- \+ *lemma* inv_injective₀
- \+ *lemma* inv_inj₀
- \+ *lemma* inv_eq_one₀
- \+ *lemma* eq_mul_inv_iff_mul_eq₀
- \+ *lemma* eq_inv_mul_iff_mul_eq₀
- \+ *lemma* inv_mul_eq_iff_eq_mul₀
- \+ *lemma* mul_inv_eq_iff_eq_mul₀
- \+ *lemma* mul_inv_eq_one₀
- \+ *lemma* inv_mul_eq_one₀
- \+ *lemma* mul_eq_one_iff_eq_inv₀
- \+ *lemma* mul_eq_one_iff_inv_eq₀
- \+ *lemma* mul_inv_rev₀
- \+ *lemma* mul_inv₀
- \+ *lemma* inv_symm_left_iff₀
- \+ *lemma* inv_symm_left₀
- \+ *lemma* inv_right₀
- \+ *lemma* inv_right_iff₀
- \+ *lemma* map_inv
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_right_inj'
- \- *lemma* mul_inv_cancel_right'
- \- *lemma* mul_inv_cancel_left'
- \- *lemma* inv_mul_cancel_right'
- \- *lemma* inv_mul_cancel_left'
- \- *lemma* inv_inv'
- \- *lemma* inv_involutive'
- \- *lemma* inv_injective'
- \- *lemma* inv_inj'
- \- *lemma* inv_eq_one'
- \- *lemma* eq_mul_inv_iff_mul_eq'
- \- *lemma* eq_inv_mul_iff_mul_eq'
- \- *lemma* inv_mul_eq_iff_eq_mul'
- \- *lemma* mul_inv_eq_iff_eq_mul'
- \- *lemma* mul_inv_eq_one'
- \- *lemma* inv_mul_eq_one'
- \- *lemma* mul_eq_one_iff_eq_inv'
- \- *lemma* mul_eq_one_iff_inv_eq'
- \- *lemma* mul_inv_rev'
- \- *lemma* mul_inv'
- \- *lemma* inv_symm_left_iff'
- \- *lemma* inv_symm_left'
- \- *lemma* inv_right'
- \- *lemma* inv_right_iff'
- \- *lemma* map_inv'
- \+ *theorem* inv_left_iff₀
- \+ *theorem* inv_left₀
- \+ *theorem* inv_right_iff₀
- \+ *theorem* inv_right₀
- \+ *theorem* inv_inv₀
- \- *theorem* inv_left_iff'
- \- *theorem* inv_left'
- \- *theorem* inv_right_iff'
- \- *theorem* inv_right'
- \- *theorem* inv_inv'

modified src/algebra/group_with_zero/defs.lean
- \+ *lemma* mul_left_cancel₀
- \+ *lemma* mul_right_cancel₀
- \+ *lemma* mul_right_injective₀
- \+ *lemma* mul_left_injective₀
- \- *lemma* mul_left_cancel'
- \- *lemma* mul_right_cancel'
- \- *lemma* mul_right_injective'
- \- *lemma* mul_left_injective'

modified src/algebra/group_with_zero/power.lean
- \+ *lemma* units.coe_gpow₀
- \- *lemma* units.coe_gpow'
- \+ *theorem* inv_pow₀
- \+ *theorem* pow_sub₀
- \+ *theorem* pow_inv_comm₀
- \- *theorem* inv_pow'
- \- *theorem* pow_sub'
- \- *theorem* pow_inv_comm'

modified src/algebra/module/pi.lean
- \+/\- *lemma* single_smul'
- \+ *lemma* single_smul₀
- \- *lemma* single_smul''
- \+/\- *lemma* single_smul'

modified src/algebra/module/pointwise_pi.lean
- \+ *lemma* smul_pi₀
- \- *lemma* smul_pi'

modified src/algebra/opposites.lean

modified src/algebra/order/absolute_value.lean

modified src/algebra/order/field.lean
- \+ *def* order_iso.mul_left₀
- \+ *def* order_iso.mul_right₀
- \- *def* order_iso.mul_left'
- \- *def* order_iso.mul_right'

modified src/algebra/order/smul.lean

modified src/algebra/order/with_zero.lean
- \+ *lemma* zero_lt_one₀
- \+ *lemma* div_le_div₀
- \+ *lemma* mul_lt_mul₀
- \+ *lemma* mul_inv_lt_of_lt_mul₀
- \+ *lemma* mul_lt_right₀
- \+ *lemma* pow_lt_pow₀
- \+ *lemma* inv_lt_inv₀
- \+ *lemma* inv_le_inv₀
- \- *lemma* zero_lt_one''
- \- *lemma* div_le_div'
- \- *lemma* mul_lt_mul''''
- \- *lemma* mul_inv_lt_of_lt_mul'
- \- *lemma* mul_lt_right'
- \- *lemma* pow_lt_pow'
- \- *lemma* inv_lt_inv''
- \- *lemma* inv_le_inv''

modified src/algebra/periodic.lean
- \+ *lemma* periodic.const_smul₀
- \+ *lemma* periodic.const_inv_smul₀
- \+ *lemma* antiperiodic.const_smul₀
- \+ *lemma* antiperiodic.const_inv_smul₀
- \- *lemma* periodic.const_smul'
- \- *lemma* periodic.const_inv_smul'
- \- *lemma* antiperiodic.const_smul'
- \- *lemma* antiperiodic.const_inv_smul'

modified src/algebra/pointwise.lean
- \+ *lemma* smul_set_inter₀
- \+ *lemma* smul_mem_smul_set_iff₀
- \+ *lemma* mem_smul_set_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_smul_set_iff₀
- \+ *lemma* preimage_smul₀
- \+ *lemma* preimage_smul_inv₀
- \+ *lemma* set_smul_subset_set_smul_iff₀
- \+ *lemma* set_smul_subset_iff₀
- \+ *lemma* subset_set_smul_iff₀
- \- *lemma* smul_set_inter'
- \- *lemma* smul_mem_smul_set_iff'
- \- *lemma* mem_smul_set_iff_inv_smul_mem'
- \- *lemma* mem_inv_smul_set_iff'
- \- *lemma* preimage_smul'
- \- *lemma* preimage_smul_inv'
- \- *lemma* set_smul_subset_set_smul_iff'
- \- *lemma* set_smul_subset_iff'
- \- *lemma* subset_set_smul_iff'

modified src/algebra/quadratic_discriminant.lean

modified src/algebra/quaternion.lean

modified src/algebra/star/chsh.lean

modified src/algebra/support.lean
- \+ *lemma* mul_support_inv₀
- \- *lemma* mul_support_inv'

modified src/analysis/analytic/basic.lean

modified src/analysis/asymptotics/asymptotic_equivalent.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv_symmetric.lean

modified src/analysis/calculus/lhopital.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/convex/basic.lean

modified src/analysis/convex/function.lean

modified src/analysis/convex/jensen.lean

modified src/analysis/convex/topology.lean

modified src/analysis/hofer.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/enorm.lean

modified src/analysis/normed_space/exponential.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/units.lean

modified src/analysis/p_series.lean

modified src/analysis/seminorm.lean

modified src/analysis/special_functions/integrals.lean

modified src/analysis/special_functions/trigonometric/basic.lean

modified src/analysis/specific_limits.lean

modified src/data/complex/basic.lean

modified src/data/complex/exponential.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/equiv/mul_add.lean

modified src/data/int/basic.lean

modified src/data/int/gcd.lean

modified src/data/nat/choose/basic.lean

modified src/data/nat/factorial/basic.lean

modified src/data/polynomial/field_division.lean

modified src/data/rat/basic.lean

modified src/data/rat/cast.lean

modified src/data/real/ennreal.lean

modified src/data/real/hyperreal.lean
- \+/\- *lemma* inv_epsilon_eq_omega
- \+/\- *lemma* inv_epsilon_eq_omega

modified src/data/real/irrational.lean

modified src/data/real/nnreal.lean

modified src/data/real/sqrt.lean
- \+/\- *lemma* sqrt_inv
- \+/\- *lemma* sqrt_inv

modified src/data/set/intervals/image_preimage.lean

modified src/data/set/intervals/unordered_interval.lean

modified src/field_theory/perfect_closure.lean

modified src/geometry/euclidean/sphere.lean

modified src/geometry/euclidean/triangle.lean

modified src/group_theory/group_action/group.lean
- \+ *lemma* inv_smul_smul₀
- \+ *lemma* smul_inv_smul₀
- \+ *lemma* inv_smul_eq_iff₀
- \+ *lemma* eq_inv_smul_iff₀
- \- *lemma* inv_smul_smul'
- \- *lemma* smul_inv_smul'
- \- *lemma* inv_smul_eq_iff'
- \- *lemma* eq_inv_smul_iff'

modified src/group_theory/specific_groups/cyclic.lean

modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀
- \- *lemma* smul_mem_pointwise_smul_iff'
- \- *lemma* mem_pointwise_smul_iff_inv_smul_mem'
- \- *lemma* mem_inv_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_iff'
- \- *lemma* le_pointwise_smul_iff'
- \- *lemma* smul_mem_pointwise_smul_iff'
- \- *lemma* mem_pointwise_smul_iff_inv_smul_mem'
- \- *lemma* mem_inv_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_iff'
- \- *lemma* le_pointwise_smul_iff'

modified src/group_theory/submonoid/center.lean
- \+ *lemma* inv_mem_center₀
- \+ *lemma* div_mem_center₀
- \- *lemma* inv_mem_center'
- \- *lemma* div_mem_center'

modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀
- \+ *lemma* smul_mem_pointwise_smul_iff₀
- \+ *lemma* mem_pointwise_smul_iff_inv_smul_mem₀
- \+ *lemma* mem_inv_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_pointwise_smul_iff₀
- \+ *lemma* pointwise_smul_le_iff₀
- \+ *lemma* le_pointwise_smul_iff₀
- \- *lemma* smul_mem_pointwise_smul_iff'
- \- *lemma* mem_pointwise_smul_iff_inv_smul_mem'
- \- *lemma* mem_inv_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_iff'
- \- *lemma* le_pointwise_smul_iff'
- \- *lemma* smul_mem_pointwise_smul_iff'
- \- *lemma* mem_pointwise_smul_iff_inv_smul_mem'
- \- *lemma* mem_inv_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_pointwise_smul_iff'
- \- *lemma* pointwise_smul_le_iff'
- \- *lemma* le_pointwise_smul_iff'

modified src/linear_algebra/affine_space/ordered.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/eigenspace.lean

modified src/linear_algebra/free_module_pid.lean

modified src/linear_algebra/quadratic_form.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_inv_iff₀
- \+ *lemma* ae_measurable_inv_iff₀
- \+ *lemma* measurable_const_smul_iff₀
- \+ *lemma* ae_measurable_const_smul_iff₀
- \- *lemma* measurable_inv_iff'
- \- *lemma* ae_measurable_inv_iff'
- \- *lemma* measurable_const_smul_iff'
- \- *lemma* ae_measurable_const_smul_iff'

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/mean_inequalities.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/l_series.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/order/filter/at_top_bot.lean

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/integral_domain.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/perfection.lean

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/polynomial/dickson.lean

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/subring.lean

modified src/ring_theory/valuation/basic.lean

modified src/ring_theory/valuation/integers.lean

modified src/ring_theory/valuation/integral.lean

modified src/ring_theory/witt_vector/defs.lean

modified src/ring_theory/witt_vector/frobenius.lean

modified src/tactic/cancel_denoms.lean

modified src/tactic/norm_num.lean

modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* tendsto_inv₀
- \+ *lemma* continuous_on_inv₀
- \+ *lemma* filter.tendsto.inv₀
- \+ *lemma* continuous_within_at.inv₀
- \+ *lemma* continuous_at.inv₀
- \+ *lemma* continuous.inv₀
- \+ *lemma* continuous_on.inv₀
- \+ *lemma* coe_mul_left₀
- \+ *lemma* mul_left₀_symm_apply
- \+ *lemma* coe_mul_right₀
- \+ *lemma* mul_right₀_symm_apply
- \- *lemma* tendsto_inv'
- \- *lemma* continuous_on_inv'
- \- *lemma* filter.tendsto.inv'
- \- *lemma* continuous_within_at.inv'
- \- *lemma* continuous_at.inv'
- \- *lemma* continuous.inv'
- \- *lemma* continuous_on.inv'
- \- *lemma* coe_mul_left'
- \- *lemma* mul_left'_symm_apply
- \- *lemma* coe_mul_right'
- \- *lemma* mul_right'_symm_apply

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/mul_action.lean
- \+ *lemma* tendsto_const_smul_iff₀
- \+ *lemma* continuous_within_at_const_smul_iff₀
- \+ *lemma* continuous_on_const_smul_iff₀
- \+ *lemma* continuous_at_const_smul_iff₀
- \+ *lemma* continuous_const_smul_iff₀
- \+ *lemma* is_open_map_smul₀
- \+ *lemma* is_closed_map_smul₀
- \- *lemma* tendsto_const_smul_iff'
- \- *lemma* continuous_within_at_const_smul_iff'
- \- *lemma* continuous_on_const_smul_iff'
- \- *lemma* continuous_at_const_smul_iff'
- \- *lemma* continuous_const_smul_iff'
- \- *lemma* is_open_map_smul'
- \- *lemma* is_closed_map_smul'

modified src/topology/continuous_function/algebra.lean

modified src/topology/instances/nnreal.lean



## [2021-10-01 01:14:03](https://github.com/leanprover-community/mathlib/commit/540fb94)
feat(data/fintype/basic): bijection preserves cardinality ([#9473](https://github.com/leanprover-community/mathlib/pull/9473))
We don't seem to have this lemma yet, so I've added it.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* card_of_bijective



## [2021-10-01 01:14:02](https://github.com/leanprover-community/mathlib/commit/456db24)
feat(topology/algebra/module): has_continuous_smul ([#9468](https://github.com/leanprover-community/mathlib/pull/9468))
in terms of nice neighborhoods of zero
#### Estimated changes
modified src/topology/algebra/module.lean
- \+ *lemma* has_continuous_smul.of_nhds_zero



## [2021-10-01 01:14:00](https://github.com/leanprover-community/mathlib/commit/2b23d2e)
chore(topology/algebra): remove dead code ([#9467](https://github.com/leanprover-community/mathlib/pull/9467))
This code wasn't used and its historically intended use will soon be redone much better. The second file is only a dead import and a misleading comment (referring to the dead code of the *other* file).
#### Estimated changes
modified src/topology/algebra/group.lean
- \- *lemma* neg_Z
- \- *lemma* add_Z
- \- *lemma* exists_Z_half
- \- *lemma* nhds_eq
- \- *lemma* nhds_zero_eq_Z

modified src/topology/algebra/uniform_group.lean



## [2021-10-01 01:13:59](https://github.com/leanprover-community/mathlib/commit/5b02571)
chore(measure_theory/decomposition/lebesgue): make measurable_space implicit ([#9463](https://github.com/leanprover-community/mathlib/pull/9463))
Whenever the `measurable_space` can be inferred from a `measure` argument, it should be implicit. This PR applies that rule to the Lebesgue decomposition file.
#### Estimated changes
modified src/measure_theory/decomposition/lebesgue.lean
- \+/\- *lemma* have_lebesgue_decomposition_spec
- \+/\- *lemma* have_lebesgue_decomposition_add
- \+/\- *lemma* not_have_lebesgue_decomposition_iff
- \+/\- *lemma* singular_part_mutually_singular
- \+/\- *lemma* singular_part_total_variation
- \+/\- *lemma* mutually_singular_singular_part
- \+/\- *lemma* have_lebesgue_decomposition_mk
- \+/\- *lemma* singular_part_smul
- \+/\- *lemma* rn_deriv_neg
- \+/\- *lemma* rn_deriv_smul
- \+/\- *lemma* rn_deriv_add
- \+/\- *lemma* rn_deriv_sub
- \+/\- *lemma* have_lebesgue_decomposition_spec
- \+/\- *lemma* have_lebesgue_decomposition_add
- \+/\- *lemma* not_have_lebesgue_decomposition_iff
- \+/\- *lemma* singular_part_mutually_singular
- \+/\- *lemma* singular_part_total_variation
- \+/\- *lemma* mutually_singular_singular_part
- \+/\- *lemma* have_lebesgue_decomposition_mk
- \+/\- *lemma* singular_part_smul
- \+/\- *lemma* rn_deriv_neg
- \+/\- *lemma* rn_deriv_smul
- \+/\- *lemma* rn_deriv_add
- \+/\- *lemma* rn_deriv_sub
- \+/\- *theorem* eq_singular_part
- \+/\- *theorem* eq_rn_deriv
- \+/\- *theorem* have_lebesgue_decomposition_of_finite_measure
- \+/\- *theorem* eq_singular_part
- \+/\- *theorem* eq_rn_deriv
- \+/\- *theorem* eq_singular_part
- \+/\- *theorem* eq_rn_deriv
- \+/\- *theorem* have_lebesgue_decomposition_of_finite_measure
- \+/\- *theorem* eq_singular_part
- \+/\- *theorem* eq_rn_deriv
- \+ *def* singular_part(s
- \- *def* singular_part

