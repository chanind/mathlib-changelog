## [2021-10-31 23:00:49](https://github.com/leanprover-community/mathlib/commit/932e954)
feat(data/finset): some simple finset lemmas ([#10079](https://github.com/leanprover-community/mathlib/pull/10079))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.diag_empty
- \+ *lemma* finset.off_diag_empty
- \+ *lemma* finset.product_subset_product
- \+ *lemma* finset.product_subset_product_left
- \+ *lemma* finset.product_subset_product_right



## [2021-10-31 23:00:48](https://github.com/leanprover-community/mathlib/commit/60cb2cf)
feat(data/list): length_filter_lt_length_iff_exists ([#10074](https://github.com/leanprover-community/mathlib/pull/10074))
Also moved a lemma about filter_map that was placed in the wrong file
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.filter_map_cons
- \+ *theorem* list.length_eq_countp_add_countp
- \+ *theorem* list.length_filter_lt_length_iff_exists

Modified src/data/list/forall2.lean
- \- *theorem* list.filter_map_cons



## [2021-10-31 23:00:47](https://github.com/leanprover-community/mathlib/commit/af4f4df)
feat(list/init): simplifier lemmas for list.init ([#10061](https://github.com/leanprover-community/mathlib/pull/10061))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.init_append_of_ne_nil
- \+ *lemma* list.init_cons_of_ne_nil



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
Modified src/data/list/basic.lean
- \- *theorem* list.cons_sublist_cons
- \+ *theorem* list.infix.length_le
- \+ *theorem* list.infix_insert
- \- *theorem* list.infix_of_prefix
- \- *theorem* list.infix_of_suffix
- \+/\- *theorem* list.infix_refl
- \+ *theorem* list.is_prefix.is_infix
- \+ *theorem* list.is_suffix.is_infix
- \- *theorem* list.length_le_of_infix
- \+/\- *theorem* list.nil_infix
- \+/\- *theorem* list.repeat_sublist_repeat
- \+/\- *theorem* list.reverse_prefix
- \+/\- *theorem* list.reverse_suffix
- \+/\- *theorem* list.singleton_sublist
- \+ *theorem* list.sublist.cons_cons
- \+ *theorem* list.sublist_insert
- \- *theorem* list.sublist_of_infix
- \- *theorem* list.sublist_of_prefix
- \- *theorem* list.sublist_of_suffix
- \+ *theorem* list.subset_insert
- \+/\- *lemma* list.tail_sublist

Modified src/data/list/forall2.lean


Modified src/data/list/lattice.lean


Modified src/data/list/nodup.lean


Modified src/data/list/pairwise.lean


Modified src/data/list/sublists.lean


Modified src/data/multiset/finset_ops.lean




## [2021-10-31 23:00:44](https://github.com/leanprover-community/mathlib/commit/76f13b3)
feat(algebra/star/basic): `ring.inverse_star` ([#10039](https://github.com/leanprover-community/mathlib/pull/10039))
Also adds `is_unit.star` and `is_unit_star`.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* is_unit.star
- \+ *lemma* is_unit_star
- \+ *lemma* ring.inverse_star



## [2021-10-31 21:28:18](https://github.com/leanprover-community/mathlib/commit/106dc57)
chore(ring_theory/ideal/operations): generalize typeclass in map_map and comap_comap ([#10077](https://github.com/leanprover-community/mathlib/pull/10077))
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024) which is hitting timeouts somewhere more irritating.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.comap_comap
- \+/\- *lemma* ideal.map_map



## [2021-10-31 21:28:17](https://github.com/leanprover-community/mathlib/commit/233eb66)
feat(data/real/ennreal): more on integer powers on ennreal ([#10071](https://github.com/leanprover-community/mathlib/pull/10071))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* zpow_two

Modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_mem_Ico_zpow
- \+ *lemma* exists_mem_Ioc_zpow
- \- *lemma* exists_zpow_near'
- \- *lemma* exists_zpow_near

Modified src/analysis/normed_space/basic.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.Ioo_zero_top_eq_Union_Ico_zpow
- \+ *lemma* ennreal.add_div
- \+ *lemma* ennreal.coe_zpow
- \+ *lemma* ennreal.exists_mem_Ico_zpow
- \+ *lemma* ennreal.exists_mem_Ioc_zpow
- \+ *lemma* ennreal.monotone_zpow
- \+ *lemma* ennreal.one_le_pow_of_one_le
- \+ *lemma* ennreal.zpow_add
- \+ *lemma* ennreal.zpow_le_of_le
- \+ *lemma* ennreal.zpow_lt_top
- \+ *lemma* ennreal.zpow_pos

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_zpow
- \+ *lemma* nnreal.exists_mem_Ico_zpow
- \+ *lemma* nnreal.exists_mem_Ioc_zpow
- \+ *lemma* nnreal.inv_lt_one
- \+ *lemma* nnreal.inv_lt_one_iff
- \+ *lemma* nnreal.zpow_pos

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.continuous_pow



## [2021-10-31 18:58:21](https://github.com/leanprover-community/mathlib/commit/5ca3c5e)
chore(data/set/intervals): add some lemmas ([#10062](https://github.com/leanprover-community/mathlib/pull/10062))
Add several lemma lemmas about intersection/difference of intervals.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ico_inter_Ici
- \+/\- *lemma* set.Iic_inter_Ioc_of_le
- \+ *lemma* set.Ioc_diff_Iic
- \+ *lemma* set.Ioc_inter_Iic



## [2021-10-31 18:58:20](https://github.com/leanprover-community/mathlib/commit/05bd61d)
chore(analysis): move more code out of `analysis.normed_space.basic` ([#10055](https://github.com/leanprover-community/mathlib/pull/10055))
#### Estimated changes
Added src/analysis/normed/group/completion.lean
- \+ *lemma* uniform_space.completion.norm_coe

Modified src/analysis/normed/group/hom_completion.lean


Added src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_finset_iff_vanishing_norm
- \+ *lemma* cauchy_seq_finset_of_norm_bounded
- \+ *lemma* cauchy_seq_finset_of_summable_norm
- \+ *lemma* has_sum.norm_le_of_bounded
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable_norm
- \+ *lemma* has_sum_of_subseq_of_summable
- \+ *lemma* nnnorm_tsum_le
- \+ *lemma* norm_tsum_le_tsum_norm
- \+ *lemma* summable_iff_vanishing_norm
- \+ *lemma* summable_of_nnnorm_bounded
- \+ *lemma* summable_of_norm_bounded
- \+ *lemma* summable_of_norm_bounded_eventually
- \+ *lemma* summable_of_summable_nnnorm
- \+ *lemma* summable_of_summable_norm
- \+ *lemma* tsum_of_nnnorm_bounded
- \+ *lemma* tsum_of_norm_bounded

Modified src/analysis/normed_space/basic.lean
- \- *lemma* cauchy_seq_finset_iff_vanishing_norm
- \- *lemma* cauchy_seq_finset_of_norm_bounded
- \- *lemma* cauchy_seq_finset_of_summable_norm
- \- *lemma* has_sum.norm_le_of_bounded
- \- *lemma* has_sum_iff_tendsto_nat_of_summable_norm
- \- *lemma* has_sum_of_subseq_of_summable
- \- *lemma* nnnorm_tsum_le
- \- *lemma* norm_tsum_le_tsum_norm
- \- *lemma* summable_iff_vanishing_norm
- \- *lemma* summable_of_nnnorm_bounded
- \- *lemma* summable_of_norm_bounded
- \- *lemma* summable_of_norm_bounded_eventually
- \- *lemma* summable_of_summable_nnnorm
- \- *lemma* summable_of_summable_norm
- \- *lemma* tsum_of_nnnorm_bounded
- \- *lemma* tsum_of_norm_bounded
- \- *lemma* uniform_space.completion.norm_coe

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* uniform_space.completion.extension_coe



## [2021-10-31 18:58:19](https://github.com/leanprover-community/mathlib/commit/8390325)
fix(data/pequiv): fix lint ([#10043](https://github.com/leanprover-community/mathlib/pull/10043))
#### Estimated changes
Modified src/data/pequiv.lean




## [2021-10-31 18:58:18](https://github.com/leanprover-community/mathlib/commit/66f7114)
feat(measure_theory/group): add `measurable_set.const_smul` ([#10025](https://github.com/leanprover-community/mathlib/pull/10025))
Partially based on lemmas from [#2819](https://github.com/leanprover-community/mathlib/pull/2819).
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* subsingleton_zero_smul_set
- \+ *lemma* zero_smul_subset

Added src/measure_theory/group/pointwise.lean
- \+ *lemma* measurable_set.const_smul
- \+ *lemma* measurable_set.const_smul_of_ne_zero
- \+ *lemma* measurable_set.const_smul₀

Modified src/measure_theory/measurable_space_def.lean
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
Modified src/data/W/cardinal.lean


Modified src/data/array/lemmas.lean
- \- *def* equiv.vector_equiv_fin

Modified src/data/vector/basic.lean
- \+ *def* equiv.vector_equiv_fin

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/free_module/finite/rank.lean


Modified src/linear_algebra/free_module/rank.lean
- \+/\- *lemma* module.free.rank_prod

Modified src/set_theory/cardinal.lean
- \- *lemma* cardinal.add
- \+/\- *theorem* cardinal.add_def
- \+/\- *theorem* cardinal.cantor
- \+ *def* cardinal.lift_order_embedding
- \+ *theorem* cardinal.lift_umax'
- \+ *theorem* cardinal.lift_uzero
- \+/\- *theorem* cardinal.mk_Prop
- \+ *theorem* cardinal.mk_arrow
- \+/\- *theorem* cardinal.mk_empty
- \+ *lemma* cardinal.mk_eq_one
- \+/\- *theorem* cardinal.mk_list_eq_sum_pow
- \+/\- *theorem* cardinal.mk_pempty
- \+ *theorem* cardinal.mk_pi
- \+ *theorem* cardinal.mk_plift_false
- \- *theorem* cardinal.mk_plift_of_false
- \- *theorem* cardinal.mk_plift_of_true
- \+ *theorem* cardinal.mk_plift_true
- \+ *lemma* cardinal.mk_prod
- \- *theorem* cardinal.mk_prod
- \+ *lemma* cardinal.mk_psum
- \+/\- *theorem* cardinal.mk_punit
- \+/\- *theorem* cardinal.mk_set
- \+ *theorem* cardinal.mk_sigma
- \+ *lemma* cardinal.mk_sum
- \+/\- *theorem* cardinal.mk_unit
- \+ *theorem* cardinal.mk_vector
- \- *lemma* cardinal.mul
- \+/\- *theorem* cardinal.mul_def
- \+/\- *lemma* cardinal.omega_le_mk
- \+/\- *lemma* cardinal.omega_mul_omega
- \+/\- *theorem* cardinal.power_def
- \+ *theorem* cardinal.prod_const'
- \+/\- *theorem* cardinal.prod_const
- \+/\- *theorem* cardinal.prod_eq_zero
- \- *theorem* cardinal.prod_mk
- \- *theorem* cardinal.prop_eq_two
- \+ *theorem* cardinal.sum_const'
- \+/\- *theorem* cardinal.sum_const
- \- *theorem* cardinal.sum_const_eq_lift_mul
- \- *theorem* cardinal.sum_mk

Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *theorem* cardinal.mk_finset_eq_mk
- \+/\- *theorem* cardinal.mk_list_eq_mk
- \+ *theorem* cardinal.mul_omega_eq
- \+ *theorem* cardinal.omega_mul_eq

Modified src/set_theory/cofinality.lean




## [2021-10-31 14:01:29](https://github.com/leanprover-community/mathlib/commit/4ef3fcd)
chore(algebra/group/inj_surj): add 2 missing `def`s ([#10068](https://github.com/leanprover-community/mathlib/pull/10068))
`function.injective.right_cancel_monoid` and `function.injective.cancel_monoid` were missing.
`function.injective.sub_neg_monoid` was also misnamed `function.injective.sub_neg_add_monoid`.
#### Estimated changes
Modified src/algebra/group/inj_surj.lean




## [2021-10-31 14:01:28](https://github.com/leanprover-community/mathlib/commit/36de1ef)
chore(ring_theory/noetherian): generalize to semiring ([#10032](https://github.com/leanprover-community/mathlib/pull/10032))
This weakens some typeclasses on some results about `is_noetherian` (which already permits modules over semirings), and relaxes `is_noetherian_ring` to permit semirings.
This does not actually try changing any of the proofs, it just relaxes assumptions that were stronger than what was actually used.
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_tower
- \+/\- *theorem* is_noetherian_ring_iff
- \+/\- *lemma* is_noetherian_ring_iff_ideal_fg
- \+/\- *theorem* ring.is_noetherian_of_zero_eq_one
- \+/\- *lemma* well_founded_submodule_gt



## [2021-10-31 13:18:04](https://github.com/leanprover-community/mathlib/commit/ca7fee8)
feat(category_theory/limits): Results about pullbacks ([#9984](https://github.com/leanprover-community/mathlib/pull/9984))
- Provided the explicit isomorphism `X ×[Z] Y ≅ Y ×[Z] X`.
- Provided the pullback of f g when either one is iso or when both are mono.
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.fst_eq_snd_of_mono_eq
- \+ *lemma* category_theory.limits.has_pullback_of_left_iso
- \+ *lemma* category_theory.limits.has_pullback_of_right_iso
- \+ *lemma* category_theory.limits.has_pullback_symmetry
- \+ *lemma* category_theory.limits.has_pushout_of_left_iso
- \+ *lemma* category_theory.limits.has_pushout_of_right_iso
- \+ *lemma* category_theory.limits.has_pushout_symmetry
- \+ *lemma* category_theory.limits.inl_comp_pushout_symmetry_hom
- \+ *lemma* category_theory.limits.inl_comp_pushout_symmetry_inv
- \+ *lemma* category_theory.limits.inl_eq_inr_of_epi_eq
- \+ *lemma* category_theory.limits.inr_comp_pushout_symmetry_hom
- \+ *lemma* category_theory.limits.inr_comp_pushout_symmetry_inv
- \+ *def* category_theory.limits.pullback_cone_of_left_iso
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_X
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_fst
- \+ *def* category_theory.limits.pullback_cone_of_left_iso_is_limit
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_snd
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_π_app_left
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_π_app_none
- \+ *lemma* category_theory.limits.pullback_cone_of_left_iso_π_app_right
- \+ *def* category_theory.limits.pullback_cone_of_right_iso
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_X
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_fst
- \+ *def* category_theory.limits.pullback_cone_of_right_iso_is_limit
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_snd
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_π_app_left
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_π_app_none
- \+ *lemma* category_theory.limits.pullback_cone_of_right_iso_π_app_right
- \+ *def* category_theory.limits.pullback_symmetry
- \+ *lemma* category_theory.limits.pullback_symmetry_hom_comp_fst
- \+ *lemma* category_theory.limits.pullback_symmetry_hom_comp_snd
- \+ *lemma* category_theory.limits.pullback_symmetry_hom_of_epi_eq
- \+ *lemma* category_theory.limits.pullback_symmetry_hom_of_mono_eq
- \+ *lemma* category_theory.limits.pullback_symmetry_inv_comp_fst
- \+ *lemma* category_theory.limits.pullback_symmetry_inv_comp_snd
- \+ *lemma* category_theory.limits.pushout_cocone.epi_of_is_colimit_mk_id_id
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_mk_id_id
- \+ *def* category_theory.limits.pushout_cocone_of_left_iso
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_X
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_inl
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_inr
- \+ *def* category_theory.limits.pushout_cocone_of_left_iso_is_limit
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_ι_app_left
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_ι_app_none
- \+ *lemma* category_theory.limits.pushout_cocone_of_left_iso_ι_app_right
- \+ *def* category_theory.limits.pushout_cocone_of_right_iso
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_X
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_inl
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_inr
- \+ *def* category_theory.limits.pushout_cocone_of_right_iso_is_limit
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_ι_app_left
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_ι_app_none
- \+ *lemma* category_theory.limits.pushout_cocone_of_right_iso_ι_app_right
- \+ *def* category_theory.limits.pushout_is_pushout
- \+ *def* category_theory.limits.pushout_symmetry



## [2021-10-31 11:57:21](https://github.com/leanprover-community/mathlib/commit/be0a4af)
chore(analysis): move `real.angle` to a dedicated file ([#10065](https://github.com/leanprover-community/mathlib/pull/10065))
We don't use this type anywhere else.
#### Estimated changes
Added src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.angle_eq_iff_two_pi_dvd_sub
- \+ *lemma* real.angle.coe_add
- \+ *lemma* real.angle.coe_coe_hom
- \+ *def* real.angle.coe_hom
- \+ *lemma* real.angle.coe_int_mul_eq_zsmul
- \+ *lemma* real.angle.coe_nat_mul_eq_nsmul
- \+ *lemma* real.angle.coe_neg
- \+ *lemma* real.angle.coe_sub
- \+ *lemma* real.angle.coe_two_pi
- \+ *lemma* real.angle.coe_zero
- \+ *theorem* real.angle.cos_eq_iff_eq_or_eq_neg
- \+ *theorem* real.angle.cos_sin_inj
- \+ *theorem* real.angle.sin_eq_iff_eq_or_add_eq_pi
- \+ *def* real.angle

Modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* real.angle.angle_eq_iff_two_pi_dvd_sub
- \- *lemma* real.angle.coe_add
- \- *lemma* real.angle.coe_int_mul_eq_zsmul
- \- *lemma* real.angle.coe_nat_mul_eq_nsmul
- \- *lemma* real.angle.coe_neg
- \- *lemma* real.angle.coe_sub
- \- *lemma* real.angle.coe_two_pi
- \- *lemma* real.angle.coe_zero
- \- *theorem* real.angle.cos_eq_iff_eq_or_eq_neg
- \- *theorem* real.angle.cos_sin_inj
- \- *theorem* real.angle.sin_eq_iff_eq_or_add_eq_pi
- \- *def* real.angle



## [2021-10-31 11:57:20](https://github.com/leanprover-community/mathlib/commit/0433eb6)
doc(topology/uniform_space/uniform_embedding): add some docs ([#10045](https://github.com/leanprover-community/mathlib/pull/10045))
#### Estimated changes
Modified src/topology/uniform_space/uniform_embedding.lean
- \- *theorem* uniform_inducing.uniform_embedding



## [2021-10-31 11:57:19](https://github.com/leanprover-community/mathlib/commit/e5f9bec)
chore(linear_algebra/basic): relax ring to semiring ([#10030](https://github.com/leanprover-community/mathlib/pull/10030))
This relaxes a random selection of lemmas from `ring R` to `semiring R`, and cleans up some unused `variables` nearby.
Probably the most useful of these are `submodule.mem_map_equiv`, `map_subtype.rel_iso`, and `submodule.disjoint_iff_comap_eq_bot`
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_map.iterate_ker
- \+/\- *def* linear_map.iterate_range
- \+/\- *def* submodule.map_subtype.order_embedding
- \+/\- *def* submodule.map_subtype.rel_iso



## [2021-10-31 11:57:18](https://github.com/leanprover-community/mathlib/commit/35cf154)
feat(linear_algebra/eigenspace): define `eigenvalues` of an endomorphism ([#10027](https://github.com/leanprover-community/mathlib/pull/10027))
Prerequisites in `linear_algebra/eigenspace` for [#9995](https://github.com/leanprover-community/mathlib/pull/9995), including a definition `module.End.eigenvalues`, the eigenvalues of an endomorphism considered as a subtype of the scalar ring.
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.eigenspace_restrict_eq_bot
- \+ *lemma* module.End.eigenspace_restrict_le_eigenspace
- \+ *def* module.End.eigenvalues
- \+ *lemma* module.End.has_eigenvalue.exists_has_eigenvector



## [2021-10-31 10:19:07](https://github.com/leanprover-community/mathlib/commit/175ac2c)
chore(algebra/group/defs): golf a proof ([#10067](https://github.com/leanprover-community/mathlib/pull/10067))
Use `monoid.ext` to golf `div_inv_monoid.ext`.
#### Estimated changes
Modified src/algebra/group/defs.lean




## [2021-10-31 10:19:06](https://github.com/leanprover-community/mathlib/commit/31c8aa5)
chore(algebra/group_with_zero/basic): zero, one, and pow lemmas for `ring.inverse` ([#10049](https://github.com/leanprover-community/mathlib/pull/10049))
This adds:
* `ring.inverse_zero`
* `ring.inverse_one`
* `ring.inverse_pow` (to match `inv_pow`, `inv_pow₀`)
* `commute.ring_inverse_ring_inverse` (to match `commute.inv_inv`)
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* commute.ring_inverse_ring_inverse
- \+ *lemma* monoid_with_zero_hom.map_units_inv
- \+ *lemma* ring.inverse_one
- \+ *lemma* ring.inverse_zero
- \+ *lemma* ring.mul_inverse_rev'
- \+/\- *lemma* ring.mul_inverse_rev

Modified src/algebra/group_with_zero/power.lean
- \+ *lemma* ring.inverse_pow



## [2021-10-31 09:46:36](https://github.com/leanprover-community/mathlib/commit/43e7d1b)
feat(order/antichain): Antichains ([#9926](https://github.com/leanprover-community/mathlib/pull/9926))
This defines antichains mimicking the definition of chains.
#### Estimated changes
Added src/order/antichain.lean
- \+ *lemma* is_antichain.eq_of_related
- \+ *lemma* is_antichain.image
- \+ *lemma* is_antichain.insert_of_symmetric
- \+ *lemma* is_antichain.mk_is_antichain
- \+ *lemma* is_antichain.mk_max
- \+ *lemma* is_antichain.mk_subset
- \+ *lemma* is_antichain.mono
- \+ *lemma* is_antichain.mono_on
- \+ *lemma* is_antichain.preimage
- \+ *lemma* is_antichain.swap
- \+ *def* is_antichain
- \+ *lemma* is_antichain_insert
- \+ *lemma* is_antichain_insert_of_symmetric
- \+ *lemma* set.subsingleton.is_antichain



## [2021-10-31 07:34:51](https://github.com/leanprover-community/mathlib/commit/b7f120f)
chore(*): clean up the library using to_additive ([#9790](https://github.com/leanprover-community/mathlib/pull/9790))
Since [#9138](https://github.com/leanprover-community/mathlib/pull/9138) and [#5487](https://github.com/leanprover-community/mathlib/pull/5487) to_additive got a lot better, so a lot of duplication in the library becomes unnecessary and makes maintenence a burden. So we remove a large number of copy-pasted declarations that can now be generated automatically.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.pow_eq_prod_const
- \+/\- *lemma* finset.prod_const
- \- *lemma* finset.sum_const
- \- *lemma* finset.sum_nsmul
- \- *lemma* finset.sum_update_of_mem

Modified src/algebra/group/defs.lean
- \- *lemma* nsmul_one'

Modified src/algebra/group/hom_instances.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/lemmas.lean
- \- *theorem* add_monoid_hom.map_zsmul
- \- *theorem* add_one_zsmul
- \- *theorem* add_zsmul
- \- *theorem* bit0_zsmul
- \- *theorem* bit1_zsmul
- \+/\- *lemma* commute.units_zpow_left
- \+/\- *lemma* commute.units_zpow_right
- \+/\- *theorem* monoid_hom.map_zpow
- \- *theorem* mul_zsmul
- \- *theorem* one_add_zsmul
- \+/\- *lemma* semiconj_by.units_zpow_right
- \- *lemma* sub_zsmul
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_zpow
- \- *theorem* zsmul_add_comm
- \- *theorem* zsmul_mul'

Modified src/algebra/iterate_hom.lean
- \- *lemma* add_left_iterate
- \- *lemma* add_right_iterate
- \- *lemma* add_right_iterate_apply_zero
- \+/\- *lemma* mul_left_iterate
- \+/\- *lemma* mul_right_iterate

Modified src/data/equiv/mul_add.lean


Modified src/data/fintype/card.lean
- \- *lemma* list.sum_take_of_fn

Modified src/data/int/gcd.lean


Modified src/data/list/basic.lean
- \- *lemma* list.length_pos_of_sum_ne_zero

Modified src/deprecated/submonoid.lean
- \- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* is_add_submonoid.smul_mem
- \- *lemma* multiples.add_mem
- \- *lemma* multiples.self_mem
- \- *lemma* multiples.zero_mem
- \- *def* multiples

Modified src/group_theory/coset.lean
- \- *def* quotient_add_group.quotient

Modified src/group_theory/order_of_element.lean
- \- *lemma* add_order_eq_card_zmultiples
- \- *lemma* add_order_of_dvd_card_univ
- \- *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \- *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \- *lemma* add_order_of_eq_add_order_of_iff
- \- *lemma* add_order_of_eq_card_multiples
- \- *lemma* add_order_of_eq_one_iff
- \- *lemma* add_order_of_eq_prime_pow
- \- *lemma* add_order_of_injective
- \- *lemma* add_order_of_le_card_univ
- \- *lemma* add_order_of_le_of_nsmul_eq_zero
- \- *lemma* add_order_of_nsmul''
- \- *lemma* add_order_of_nsmul'
- \- *lemma* add_order_of_nsmul
- \- *lemma* add_order_of_nsmul_eq_zero
- \- *lemma* add_order_of_pos
- \- *lemma* add_order_of_zero
- \- *lemma* card_nsmul_eq_zero
- \- *lemma* exists_nsmul_eq_self_of_coprime
- \- *lemma* exists_nsmul_eq_zero
- \- *lemma* exists_zsmul_eq_zero
- \- *lemma* fin_equiv_multiples_apply
- \- *lemma* fin_equiv_multiples_symm_apply
- \+/\- *lemma* fin_equiv_powers_apply
- \+/\- *lemma* fin_equiv_powers_symm_apply
- \- *lemma* fin_equiv_zmultiples_apply
- \- *lemma* fin_equiv_zmultiples_symm_apply
- \+/\- *lemma* fin_equiv_zpowers_apply
- \+/\- *lemma* fin_equiv_zpowers_symm_apply
- \- *lemma* gcd_nsmul_card_eq_zero_iff
- \- *lemma* mem_multiples_iff_mem_range_add_order_of
- \- *lemma* mem_multiples_iff_mem_zmultiples
- \- *lemma* mem_zmultiples_iff_mem_range_add_order_of
- \- *lemma* multiples_eq_zmultiples
- \- *lemma* multiples_equiv_multiples_apply
- \- *lemma* nsmul_eq_mod_add_order_of
- \- *lemma* nsmul_inj_mod
- \- *lemma* nsmul_injective_aux
- \- *lemma* nsmul_injective_of_lt_add_order_of
- \- *lemma* nsmul_ne_zero_of_lt_add_order_of'
- \+/\- *lemma* order_of_eq_one_iff
- \+/\- *lemma* order_of_one
- \+/\- *lemma* pow_card_eq_one
- \- *lemma* sum_card_add_order_of_eq_card_nsmul_eq_zero
- \- *lemma* zmultiples_equiv_zmultiples_apply
- \- *lemma* zsmul_eq_mod_add_order_of

Modified src/group_theory/subgroup/basic.lean
- \- *lemma* add_subgroup.closure_singleton_zero
- \- *lemma* add_subgroup.coe_smul
- \- *lemma* add_subgroup.coe_zsmul
- \- *lemma* add_subgroup.mem_closure_singleton
- \- *lemma* add_subgroup.zmultiples_subset
- \+/\- *lemma* monoid_hom.of_left_inverse_apply
- \+/\- *lemma* monoid_hom.of_left_inverse_symm_apply
- \+/\- *lemma* subgroup.coe_copy
- \+/\- *lemma* subgroup.coe_pow
- \+/\- *lemma* subgroup.coe_zpow



## [2021-10-31 03:19:22](https://github.com/leanprover-community/mathlib/commit/236f395)
chore(topology/compacts): add a missing simp lemma ([#10063](https://github.com/leanprover-community/mathlib/pull/10063))
#### Estimated changes
Modified src/topology/compacts.lean
- \+ *lemma* topological_space.positive_compacts_univ_val



## [2021-10-31 01:33:41](https://github.com/leanprover-community/mathlib/commit/c952017)
chore(logic/embedding): docs, fixes ([#10047](https://github.com/leanprover-community/mathlib/pull/10047))
* generalize `function.extend` and some lemmas from `Type*` to `Sort*`.
* add missing docs in `logic.embedding`;
* swap `function.embedding.arrow_congr_left` and `function.embedding.arrow_congr_right`;
* use `function.extend` to define the new `function.embedding.arrow_congr_left`.
#### Estimated changes
Modified src/algebra/module/pi.lean
- \+/\- *lemma* function.extend_smul

Modified src/logic/basic.lean
- \+/\- *theorem* exists_apply_eq_apply'
- \+/\- *theorem* exists_apply_eq_apply
- \+/\- *theorem* exists_eq

Modified src/logic/embedding.lean
- \+/\- *def* function.embedding.Pi_congr_right
- \- *def* function.embedding.arrow_congr_left
- \+ *def* function.embedding.arrow_congr_right
- \+ *lemma* function.embedding.arrow_congr_right_apply

Modified src/logic/function/basic.lean


Modified src/set_theory/cardinal.lean




## [2021-10-31 00:02:40](https://github.com/leanprover-community/mathlib/commit/951c063)
chore(data/set/pairwise): rename `set.pairwise_on` to `set.pairwise` to match `list.pairwise` and `multiset.pairwise` ([#10035](https://github.com/leanprover-community/mathlib/pull/10035))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_mem_sUnion

Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/box_integral/partition/split.lean


Modified src/analysis/convex/basic.lean
- \- *lemma* convex_iff_pairwise_on_pos
- \+ *lemma* convex_iff_pairwise_pos

Modified src/analysis/convex/function.lean
- \- *lemma* concave_on_iff_pairwise_on_pos
- \+ *lemma* concave_on_iff_pairwise_pos
- \- *lemma* convex_on_iff_pairwise_on_pos
- \+ *lemma* convex_on_iff_pairwise_pos

Modified src/data/list/nodup.lean
- \+ *lemma* list.nodup.pairwise_of_set_pairwise
- \- *lemma* list.nodup.pairwise_of_set_pairwise_on

Modified src/data/list/pairwise.lean
- \+ *lemma* list.pairwise.set_pairwise
- \- *lemma* list.pairwise.set_pairwise_on

Modified src/data/polynomial/field_division.lean


Modified src/data/set/pairwise.lean
- \- *lemma* pairwise.pairwise_on
- \+ *lemma* pairwise.set_pairwise
- \+ *lemma* set.inj_on.pairwise_image
- \- *lemma* set.inj_on.pairwise_on_image
- \+ *lemma* set.nonempty.pairwise_eq_iff_exists_eq
- \+ *lemma* set.nonempty.pairwise_iff_exists_forall
- \- *lemma* set.nonempty.pairwise_on_eq_iff_exists_eq
- \- *lemma* set.nonempty.pairwise_on_iff_exists_forall
- \+ *lemma* set.pairwise.imp
- \+ *lemma* set.pairwise.imp_on
- \+ *lemma* set.pairwise.mono'
- \+ *lemma* set.pairwise.mono
- \+ *lemma* set.pairwise.on_injective
- \+ *lemma* set.pairwise_Union
- \+ *lemma* set.pairwise_disjoint_fiber
- \+ *lemma* set.pairwise_disjoint_on_mono
- \+ *lemma* set.pairwise_empty
- \+ *lemma* set.pairwise_eq_iff_exists_eq
- \+ *lemma* set.pairwise_iff_exists_forall
- \+ *lemma* set.pairwise_insert
- \+ *lemma* set.pairwise_insert_of_symmetric
- \+ *lemma* set.pairwise_of_forall
- \- *lemma* set.pairwise_on.imp
- \- *lemma* set.pairwise_on.imp_on
- \- *lemma* set.pairwise_on.mono'
- \- *lemma* set.pairwise_on.mono
- \- *lemma* set.pairwise_on.on_injective
- \- *def* set.pairwise_on
- \- *lemma* set.pairwise_on_Union
- \- *lemma* set.pairwise_on_disjoint_fiber
- \- *lemma* set.pairwise_on_disjoint_on_mono
- \- *lemma* set.pairwise_on_empty
- \- *lemma* set.pairwise_on_eq_iff_exists_eq
- \- *lemma* set.pairwise_on_iff_exists_forall
- \- *lemma* set.pairwise_on_insert
- \- *lemma* set.pairwise_on_insert_of_symmetric
- \- *lemma* set.pairwise_on_of_forall
- \- *lemma* set.pairwise_on_pair
- \- *lemma* set.pairwise_on_pair_of_symmetric
- \- *lemma* set.pairwise_on_sUnion
- \- *lemma* set.pairwise_on_singleton
- \- *lemma* set.pairwise_on_top
- \- *lemma* set.pairwise_on_union
- \- *lemma* set.pairwise_on_union_of_symmetric
- \- *lemma* set.pairwise_on_univ
- \+ *lemma* set.pairwise_pair
- \+ *lemma* set.pairwise_pair_of_symmetric
- \+ *lemma* set.pairwise_sUnion
- \+ *lemma* set.pairwise_singleton
- \+ *lemma* set.pairwise_top
- \+ *lemma* set.pairwise_union
- \+ *lemma* set.pairwise_union_of_symmetric
- \+ *lemma* set.pairwise_univ

Modified src/geometry/euclidean/circumcenter.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/besicovitch_vector_space.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure_bUnion_finset

Modified src/order/zorn.lean
- \+/\- *def* zorn.chain

Modified src/ring_theory/coprime/lemmas.lean


Modified src/topology/bases.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.is_closed_of_pairwise_le_dist
- \- *lemma* metric.is_closed_of_pairwise_on_le_dist

Modified src/topology/uniform_space/separation.lean




## [2021-10-30 23:31:00](https://github.com/leanprover-community/mathlib/commit/7ef3262)
ci(.github/workflows/bors.yml): "bors" label for staging builds ([#10064](https://github.com/leanprover-community/mathlib/pull/10064))
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/mk_build_yml.sh




## [2021-10-30 20:45:45](https://github.com/leanprover-community/mathlib/commit/bdf38cf)
chore(*): rename int_pow to zpow ([#10058](https://github.com/leanprover-community/mathlib/pull/10058))
Leftovers of [#9989](https://github.com/leanprover-community/mathlib/pull/9989)
#### Estimated changes
Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/order/archimedean.lean
- \- *lemma* exists_int_pow_near'
- \- *lemma* exists_int_pow_near
- \+ *lemma* exists_zpow_near'
- \+ *lemma* exists_zpow_near

Modified src/analysis/normed_space/basic.lean


Modified src/linear_algebra/matrix/zpow.lean


Modified src/set_theory/surreal/dyadic.lean
- \- *lemma* surreal.nsmul_int_pow_two_pow_half
- \+ *lemma* surreal.zsmul_pow_two_pow_half



## [2021-10-30 09:45:40](https://github.com/leanprover-community/mathlib/commit/5ff850b)
feat(algebra/module/submodule_lattice): add `add_subgroup.to_int_submodule` ([#10051](https://github.com/leanprover-community/mathlib/pull/10051))
This converts an `add_subgroup M` to a `submodule ℤ M`. We already have the analogous construction for `add_submonoid M`.
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* add_subgroup.coe_to_int_submodule
- \+ *def* add_subgroup.to_int_submodule
- \+ *lemma* add_subgroup.to_int_submodule_symm
- \+ *lemma* add_subgroup.to_int_submodule_to_add_subgroup
- \+ *lemma* submodule.to_add_subgroup_to_int_submodule



## [2021-10-30 08:28:49](https://github.com/leanprover-community/mathlib/commit/d06bd9a)
feat(algebra/big_operators/finprod): add finprod_eq_of_bijective ([#10048](https://github.com/leanprover-community/mathlib/pull/10048))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_comp
- \+ *lemma* finprod_eq_of_bijective



## [2021-10-30 06:04:06](https://github.com/leanprover-community/mathlib/commit/06b1d87)
feat(algebra/group): add `commute.is_unit_mul_iff` ([#10042](https://github.com/leanprover-community/mathlib/pull/10042))
#### Estimated changes
Modified src/algebra/group/commute.lean
- \+ *lemma* commute.is_unit_mul_iff
- \+ *lemma* is_unit_mul_self_iff

Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* is_unit_pos_pow_iff
- \+ *lemma* is_unit_pow_succ_iff



## [2021-10-30 01:45:12](https://github.com/leanprover-community/mathlib/commit/fcc158e)
chore(*): update to Lean-3.35.0c ([#9988](https://github.com/leanprover-community/mathlib/pull/9988))
Move `stream`, `rbtree`, and `rbmap` from core to `mathlib` and reflows some long lines. Rename some files to avoid name clashes.
#### Estimated changes
Modified leanpkg.toml


Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt


Modified src/data/list/defs.lean


Added src/data/rbmap/basic.lean
- \+ *def* mk_rbmap
- \+ *def* rbmap.contains
- \+ *def* rbmap.empty
- \+ *def* rbmap.find
- \+ *def* rbmap.find_entry
- \+ *def* rbmap.fold
- \+ *def* rbmap.from_list
- \+ *def* rbmap.insert
- \+ *def* rbmap.max
- \+ *def* rbmap.min
- \+ *def* rbmap.rbmap_lt_dec
- \+ *def* rbmap.rev_fold
- \+ *def* rbmap.to_list
- \+ *def* rbmap.to_value
- \+ *def* rbmap
- \+ *def* rbmap_lt
- \+ *def* rbmap_of

Added src/data/rbmap/default.lean
- \+ *lemma* rbmap.constains_correct
- \+ *lemma* rbmap.eq_leaf_of_max_eq_none
- \+ *lemma* rbmap.eq_leaf_of_min_eq_none
- \+ *lemma* rbmap.eq_none_of_to_value_eq_none
- \+ *lemma* rbmap.eq_of_find_entry_some
- \+ *lemma* rbmap.eq_or_mem_of_mem_ins
- \+ *lemma* rbmap.eq_some_of_to_value_eq_some
- \+ *lemma* rbmap.equiv_or_mem_of_mem_insert
- \+ *lemma* rbmap.eqv_of_find_entry_some
- \+ *lemma* rbmap.find_correct
- \+ *lemma* rbmap.find_entry_correct
- \+ *lemma* rbmap.find_entry_eq_find_entry_of_eqv
- \+ *lemma* rbmap.find_entry_insert
- \+ *lemma* rbmap.find_entry_insert_of_disj
- \+ *lemma* rbmap.find_entry_insert_of_eqv
- \+ *lemma* rbmap.find_entry_insert_of_ne
- \+ *lemma* rbmap.find_entry_insert_of_not_eqv
- \+ *lemma* rbmap.find_eq_find_of_eqv
- \+ *lemma* rbmap.find_insert
- \+ *lemma* rbmap.find_insert_of_disj
- \+ *lemma* rbmap.find_insert_of_eqv
- \+ *lemma* rbmap.find_insert_of_ne
- \+ *lemma* rbmap.find_insert_of_not_eqv
- \+ *lemma* rbmap.incomp_or_mem_of_mem_ins
- \+ *lemma* rbmap.max_is_maximal
- \+ *lemma* rbmap.max_is_maximal_of_total
- \+ *lemma* rbmap.mem_insert
- \+ *lemma* rbmap.mem_insert_of_equiv
- \+ *lemma* rbmap.mem_insert_of_incomp
- \+ *lemma* rbmap.mem_insert_of_mem
- \+ *lemma* rbmap.mem_of_find_entry_some
- \+ *lemma* rbmap.mem_of_find_some
- \+ *lemma* rbmap.mem_of_max_eq
- \+ *lemma* rbmap.mem_of_mem_of_eqv
- \+ *lemma* rbmap.mem_of_min_eq
- \+ *lemma* rbmap.min_is_minimal
- \+ *lemma* rbmap.min_is_minimal_of_total
- \+ *lemma* rbmap.not_mem_mk_rbmap
- \+ *lemma* rbmap.not_mem_of_empty
- \+ *lemma* rbmap.not_mem_of_find_entry_none
- \+ *lemma* rbmap.not_mem_of_find_none

Added src/data/rbtree/basic.lean
- \+ *lemma* rbnode.balanced
- \+ *lemma* rbnode.depth_max'
- \+ *lemma* rbnode.depth_max
- \+ *lemma* rbnode.depth_min
- \+ *inductive* rbnode.is_node_of
- \+ *inductive* rbnode.is_red_black
- \+ *inductive* rbnode.is_searchable
- \+ *lemma* rbnode.is_searchable_none_high_of_is_searchable_some_high
- \+ *lemma* rbnode.is_searchable_none_low_of_is_searchable_some_low
- \+ *lemma* rbnode.is_searchable_of_incomp_of_is_searchable
- \+ *lemma* rbnode.is_searchable_of_is_searchable_of_incomp
- \+ *lemma* rbnode.is_searchable_some_high_of_is_searchable_of_lt
- \+ *lemma* rbnode.is_searchable_some_low_of_is_searchable_of_lt
- \+ *def* rbnode.lift
- \+ *lemma* rbnode.lo_lt_hi
- \+ *lemma* rbnode.lt_of_mem_left
- \+ *lemma* rbnode.lt_of_mem_left_right
- \+ *lemma* rbnode.lt_of_mem_right
- \+ *lemma* rbnode.range

Added src/data/rbtree/default.lean


Added src/data/rbtree/default_lt.lean


Added src/data/rbtree/find.lean
- \+ *lemma* rbnode.eqv_of_find_some
- \+ *lemma* rbnode.find.induction
- \+ *lemma* rbnode.find_correct
- \+ *lemma* rbnode.find_correct_exact
- \+ *lemma* rbnode.find_eq_find_of_eqv
- \+ *lemma* rbnode.mem_of_mem_exact

Added src/data/rbtree/init.lean
- \+ *def* mk_rbtree
- \+ *def* rbnode.balance1
- \+ *def* rbnode.balance1_node
- \+ *def* rbnode.balance2
- \+ *def* rbnode.balance2_node
- \+ *inductive* rbnode.color
- \+ *def* rbnode.depth
- \+ *def* rbnode.find
- \+ *def* rbnode.fold
- \+ *def* rbnode.get_color
- \+ *def* rbnode.ins
- \+ *def* rbnode.insert
- \+ *def* rbnode.mem
- \+ *def* rbnode.mem_exact
- \+ *def* rbnode.mk_insert_result
- \+ *def* rbnode.rev_fold
- \+ *inductive* rbnode.well_formed
- \+ *inductive* rbnode
- \+ *def* rbtree.contains
- \+ *def* rbtree.depth
- \+ *def* rbtree.empty
- \+ *def* rbtree.find
- \+ *def* rbtree.fold
- \+ *def* rbtree.from_list
- \+ *def* rbtree.insert
- \+ *def* rbtree.mem_exact
- \+ *def* rbtree.rev_fold
- \+ *def* rbtree.to_list
- \+ *def* rbtree
- \+ *def* rbtree_of

Added src/data/rbtree/insert.lean
- \+ *lemma* rbnode.balance.cases
- \+ *lemma* rbnode.balance1_eq₁
- \+ *lemma* rbnode.balance1_eq₂
- \+ *lemma* rbnode.balance1_eq₃
- \+ *lemma* rbnode.balance1_ne_leaf
- \+ *lemma* rbnode.balance1_node_ne_leaf
- \+ *lemma* rbnode.balance1_node_rb
- \+ *lemma* rbnode.balance1_rb
- \+ *lemma* rbnode.balance2_eq₁
- \+ *lemma* rbnode.balance2_eq₂
- \+ *lemma* rbnode.balance2_eq₃
- \+ *lemma* rbnode.balance2_ne_leaf
- \+ *lemma* rbnode.balance2_node_ne_leaf
- \+ *lemma* rbnode.balance2_node_rb
- \+ *lemma* rbnode.balance2_rb
- \+ *lemma* rbnode.equiv_or_mem_of_mem_ins
- \+ *lemma* rbnode.equiv_or_mem_of_mem_insert
- \+ *lemma* rbnode.find_balance1_eqv
- \+ *lemma* rbnode.find_balance1_gt
- \+ *lemma* rbnode.find_balance1_lt
- \+ *lemma* rbnode.find_balance1_node
- \+ *lemma* rbnode.find_balance1_node_eqv
- \+ *lemma* rbnode.find_balance1_node_gt
- \+ *lemma* rbnode.find_balance1_node_lt
- \+ *lemma* rbnode.find_balance2_eqv
- \+ *lemma* rbnode.find_balance2_gt
- \+ *lemma* rbnode.find_balance2_lt
- \+ *lemma* rbnode.find_balance2_node
- \+ *lemma* rbnode.find_balance2_node_eqv
- \+ *lemma* rbnode.find_balance2_node_gt
- \+ *lemma* rbnode.find_balance2_node_lt
- \+ *lemma* rbnode.find_black_eq_find_red
- \+ *lemma* rbnode.find_ins_of_disj
- \+ *lemma* rbnode.find_ins_of_eqv
- \+ *lemma* rbnode.find_insert_of_disj
- \+ *lemma* rbnode.find_insert_of_eqv
- \+ *lemma* rbnode.find_insert_of_not_eqv
- \+ *lemma* rbnode.find_mk_insert_result
- \+ *lemma* rbnode.find_red_of_gt
- \+ *lemma* rbnode.find_red_of_incomp
- \+ *lemma* rbnode.find_red_of_lt
- \+ *lemma* rbnode.ins.induction
- \+ *lemma* rbnode.ins_ne_leaf
- \+ *lemma* rbnode.ins_rb
- \+ *def* rbnode.ins_rb_result
- \+ *lemma* rbnode.insert_is_red_black
- \+ *lemma* rbnode.insert_ne_leaf
- \+ *lemma* rbnode.insert_rb
- \+ *def* rbnode.insert_rb_result
- \+ *inductive* rbnode.is_bad_red_black
- \+ *lemma* rbnode.is_searchable_balance1
- \+ *lemma* rbnode.is_searchable_balance1_node
- \+ *lemma* rbnode.is_searchable_balance2
- \+ *lemma* rbnode.is_searchable_balance2_node
- \+ *lemma* rbnode.is_searchable_ins
- \+ *lemma* rbnode.is_searchable_insert
- \+ *lemma* rbnode.is_searchable_mk_insert_result
- \+ *lemma* rbnode.ite_eq_of_not_lt
- \+ *lemma* rbnode.mem_balance1_node_of_incomp
- \+ *lemma* rbnode.mem_balance1_node_of_mem_left
- \+ *lemma* rbnode.mem_balance1_node_of_mem_right
- \+ *lemma* rbnode.mem_balance2_node_of_incomp
- \+ *lemma* rbnode.mem_balance2_node_of_mem_left
- \+ *lemma* rbnode.mem_balance2_node_of_mem_right
- \+ *lemma* rbnode.mem_exact_balance1_node_of_mem_exact
- \+ *lemma* rbnode.mem_exact_balance2_node_of_mem_exact
- \+ *lemma* rbnode.mem_ins_of_incomp
- \+ *lemma* rbnode.mem_ins_of_mem
- \+ *lemma* rbnode.mem_insert_of_incomp
- \+ *lemma* rbnode.mem_insert_of_mem
- \+ *lemma* rbnode.mem_mk_insert_result
- \+ *lemma* rbnode.mem_of_mem_mk_insert_result
- \+ *lemma* rbnode.of_get_color_eq_red
- \+ *lemma* rbnode.of_get_color_ne_red
- \+ *lemma* rbnode.of_mem_balance1_node
- \+ *lemma* rbnode.of_mem_balance2_node
- \+ *lemma* rbnode.weak_trichotomous

Added src/data/rbtree/main.lean
- \+ *lemma* rbnode.is_red_black_of_well_formed
- \+ *lemma* rbnode.is_searchable_of_well_formed
- \+ *lemma* rbtree.balanced
- \+ *lemma* rbtree.contains_correct
- \+ *lemma* rbtree.eq_leaf_of_max_eq_none
- \+ *lemma* rbtree.eq_leaf_of_min_eq_none
- \+ *lemma* rbtree.eq_of_find_some
- \+ *lemma* rbtree.eq_or_mem_of_mem_ins
- \+ *lemma* rbtree.equiv_or_mem_of_mem_insert
- \+ *lemma* rbtree.eqv_of_find_some
- \+ *lemma* rbtree.find_correct
- \+ *lemma* rbtree.find_correct_exact
- \+ *lemma* rbtree.find_correct_of_total
- \+ *lemma* rbtree.find_eq_find_of_eqv
- \+ *lemma* rbtree.find_insert
- \+ *lemma* rbtree.find_insert_of_disj
- \+ *lemma* rbtree.find_insert_of_eqv
- \+ *lemma* rbtree.find_insert_of_ne
- \+ *lemma* rbtree.find_insert_of_not_eqv
- \+ *lemma* rbtree.incomp_or_mem_of_mem_ins
- \+ *lemma* rbtree.insert_ne_mk_rbtree
- \+ *lemma* rbtree.max_is_maximal
- \+ *lemma* rbtree.mem_insert
- \+ *lemma* rbtree.mem_insert_of_equiv
- \+ *lemma* rbtree.mem_insert_of_incomp
- \+ *lemma* rbtree.mem_insert_of_mem
- \+ *lemma* rbtree.mem_of_find_some
- \+ *lemma* rbtree.mem_of_max_eq
- \+ *lemma* rbtree.mem_of_mem_of_eqv
- \+ *lemma* rbtree.mem_of_min_eq
- \+ *lemma* rbtree.min_is_minimal
- \+ *lemma* rbtree.not_mem_mk_rbtree
- \+ *lemma* rbtree.not_mem_of_empty
- \+ *lemma* rbtree.not_mem_of_find_none

Added src/data/rbtree/min_max.lean
- \+ *lemma* rbnode.eq_leaf_of_max_eq_none
- \+ *lemma* rbnode.eq_leaf_of_min_eq_none
- \+ *lemma* rbnode.max_is_maximal
- \+ *lemma* rbnode.mem_of_max_eq
- \+ *lemma* rbnode.mem_of_min_eq
- \+ *lemma* rbnode.min_is_minimal

Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/stream/basic.lean


Added src/data/stream/init.lean
- \+ *def* stream.all
- \+ *theorem* stream.all_def
- \+ *def* stream.any
- \+ *theorem* stream.any_def
- \+ *theorem* stream.append_append_stream
- \+ *theorem* stream.append_approx_drop
- \+ *def* stream.append_stream
- \+ *theorem* stream.append_stream_head_tail
- \+ *def* stream.apply
- \+ *def* stream.approx
- \+ *theorem* stream.approx_succ
- \+ *theorem* stream.approx_zero
- \+ *theorem* stream.bisim_simple
- \+ *theorem* stream.coinduction
- \+ *theorem* stream.composition
- \+ *def* stream.cons
- \+ *theorem* stream.cons_append_stream
- \+ *theorem* stream.cons_nth_inits_core
- \+ *def* stream.const
- \+ *theorem* stream.const_eq
- \+ *def* stream.corec'
- \+ *theorem* stream.corec'_eq
- \+ *def* stream.corec
- \+ *theorem* stream.corec_def
- \+ *theorem* stream.corec_eq
- \+ *theorem* stream.corec_id_f_eq_iterate
- \+ *theorem* stream.corec_id_id_eq_const
- \+ *def* stream.corec_on
- \+ *def* stream.cycle
- \+ *theorem* stream.cycle_eq
- \+ *theorem* stream.cycle_singleton
- \+ *def* stream.drop
- \+ *theorem* stream.drop_append_stream
- \+ *theorem* stream.drop_const
- \+ *theorem* stream.drop_drop
- \+ *theorem* stream.drop_map
- \+ *theorem* stream.drop_succ
- \+ *theorem* stream.drop_zip
- \+ *theorem* stream.eq_of_bisim
- \+ *theorem* stream.eq_or_mem_of_mem_cons
- \+ *def* stream.even
- \+ *theorem* stream.even_cons_cons
- \+ *theorem* stream.even_interleave
- \+ *theorem* stream.even_tail
- \+ *theorem* stream.exists_of_mem_map
- \+ *def* stream.head
- \+ *theorem* stream.head_cons
- \+ *theorem* stream.head_even
- \+ *theorem* stream.head_iterate
- \+ *theorem* stream.head_map
- \+ *theorem* stream.head_zip
- \+ *theorem* stream.homomorphism
- \+ *theorem* stream.identity
- \+ *def* stream.inits
- \+ *def* stream.inits_core
- \+ *theorem* stream.inits_core_eq
- \+ *theorem* stream.inits_eq
- \+ *theorem* stream.inits_tail
- \+ *theorem* stream.interchange
- \+ *def* stream.interleave
- \+ *theorem* stream.interleave_eq
- \+ *theorem* stream.interleave_even_odd
- \+ *theorem* stream.interleave_tail_tail
- \+ *def* stream.is_bisimulation
- \+ *def* stream.iterate
- \+ *theorem* stream.iterate_eq
- \+ *theorem* stream.iterate_id
- \+ *def* stream.map
- \+ *theorem* stream.map_append_stream
- \+ *theorem* stream.map_cons
- \+ *theorem* stream.map_const
- \+ *theorem* stream.map_eq
- \+ *theorem* stream.map_eq_apply
- \+ *theorem* stream.map_id
- \+ *theorem* stream.map_iterate
- \+ *theorem* stream.map_map
- \+ *theorem* stream.map_tail
- \+ *theorem* stream.mem_append_stream_left
- \+ *theorem* stream.mem_append_stream_right
- \+ *theorem* stream.mem_cons
- \+ *theorem* stream.mem_cons_of_mem
- \+ *theorem* stream.mem_const
- \+ *theorem* stream.mem_cycle
- \+ *theorem* stream.mem_interleave_left
- \+ *theorem* stream.mem_interleave_right
- \+ *theorem* stream.mem_map
- \+ *theorem* stream.mem_of_mem_even
- \+ *theorem* stream.mem_of_mem_odd
- \+ *theorem* stream.mem_of_nth_eq
- \+ *def* stream.nats
- \+ *theorem* stream.nats_eq
- \+ *theorem* stream.nil_append_stream
- \+ *def* stream.nth
- \+ *theorem* stream.nth_approx
- \+ *theorem* stream.nth_const
- \+ *theorem* stream.nth_drop
- \+ *theorem* stream.nth_even
- \+ *theorem* stream.nth_inits
- \+ *theorem* stream.nth_interleave_left
- \+ *theorem* stream.nth_interleave_right
- \+ *theorem* stream.nth_map
- \+ *theorem* stream.nth_nats
- \+ *theorem* stream.nth_odd
- \+ *theorem* stream.nth_of_bisim
- \+ *theorem* stream.nth_succ
- \+ *theorem* stream.nth_succ_iterate
- \+ *theorem* stream.nth_tails
- \+ *theorem* stream.nth_unfolds_head_tail
- \+ *theorem* stream.nth_zero_cons
- \+ *theorem* stream.nth_zero_iterate
- \+ *theorem* stream.nth_zip
- \+ *def* stream.odd
- \+ *theorem* stream.odd_eq
- \+ *def* stream.pure
- \+ *def* stream.tail
- \+ *theorem* stream.tail_cons
- \+ *theorem* stream.tail_const
- \+ *theorem* stream.tail_drop
- \+ *theorem* stream.tail_eq_drop
- \+ *theorem* stream.tail_even
- \+ *theorem* stream.tail_inits
- \+ *theorem* stream.tail_interleave
- \+ *theorem* stream.tail_iterate
- \+ *theorem* stream.tail_map
- \+ *theorem* stream.tail_zip
- \+ *def* stream.tails
- \+ *theorem* stream.tails_eq
- \+ *theorem* stream.tails_eq_iterate
- \+ *theorem* stream.take_theorem
- \+ *def* stream.unfolds
- \+ *theorem* stream.unfolds_eq
- \+ *theorem* stream.unfolds_head_eq
- \+ *def* stream.zip
- \+ *theorem* stream.zip_eq
- \+ *theorem* stream.zip_inits_tails
- \+ *def* stream

Modified src/data/tree.lean


Modified src/tactic/derive_inhabited.lean


Modified test/coinductive.lean




## [2021-10-29 19:43:29](https://github.com/leanprover-community/mathlib/commit/c722dae)
chore(data/fintype/basic): add a few `infinite` instances ([#10037](https://github.com/leanprover-community/mathlib/pull/10037))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \- *lemma* infinite.nonempty

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.repeat_injective



## [2021-10-29 19:43:27](https://github.com/leanprover-community/mathlib/commit/4f053a5)
feat(data/list): chain'_drop lemma ([#10028](https://github.com/leanprover-community/mathlib/pull/10028))
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* list.chain'.drop



## [2021-10-29 17:12:04](https://github.com/leanprover-community/mathlib/commit/c545660)
chore(algebra/group_with_zero/basic): move `ring.inverse`, generalize and rename `inverse_eq_has_inv` ([#10033](https://github.com/leanprover-community/mathlib/pull/10033))
This moves `ring.inverse` earlier in the import graph, since it's not about rings at all.
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* inverse_eq_has_inv

Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* ring.inverse_eq_inv'
- \+ *lemma* ring.inverse_eq_inv
- \+ *lemma* ring.inverse_mul_cancel
- \+ *lemma* ring.inverse_mul_cancel_left
- \+ *lemma* ring.inverse_mul_cancel_right
- \+ *lemma* ring.inverse_non_unit
- \+ *lemma* ring.inverse_unit
- \+ *lemma* ring.mul_inverse_cancel
- \+ *lemma* ring.mul_inverse_cancel_left
- \+ *lemma* ring.mul_inverse_cancel_right
- \+ *lemma* ring.mul_inverse_rev

Modified src/algebra/ring/basic.lean
- \- *lemma* ring.inverse_mul_cancel
- \- *lemma* ring.inverse_mul_cancel_left
- \- *lemma* ring.inverse_mul_cancel_right
- \- *lemma* ring.inverse_non_unit
- \- *lemma* ring.inverse_unit
- \- *lemma* ring.mul_inverse_cancel
- \- *lemma* ring.mul_inverse_cancel_left
- \- *lemma* ring.mul_inverse_cancel_right
- \- *lemma* ring.mul_inverse_rev

Modified src/analysis/calculus/times_cont_diff.lean




## [2021-10-29 14:39:48](https://github.com/leanprover-community/mathlib/commit/e1bafaa)
feat(category_theory/limits/shapes/images): some explicit instances of has_image_map ([#9977](https://github.com/leanprover-community/mathlib/pull/9977))
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.inv_left
- \+ *lemma* category_theory.arrow.inv_right

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.has_image.of_arrow_iso
- \+ *def* category_theory.limits.image_factorisation.of_arrow_iso
- \+/\- *lemma* category_theory.limits.is_image.fac_lift
- \+ *def* category_theory.limits.is_image.of_arrow_iso
- \+ *def* category_theory.limits.mono_factorisation.of_arrow_iso



## [2021-10-29 13:53:07](https://github.com/leanprover-community/mathlib/commit/4f3443a)
feat(measure_theory/group/arithmetic): add a section about `opposite` ([#10026](https://github.com/leanprover-community/mathlib/pull/10026))
#### Estimated changes
Modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_op
- \+ *lemma* measurable_unop



## [2021-10-29 08:04:41](https://github.com/leanprover-community/mathlib/commit/3f6174b)
fix(tactic/norm_cast): make push_cast discharger match the others ([#10021](https://github.com/leanprover-community/mathlib/pull/10021))
closes [#9822](https://github.com/leanprover-community/mathlib/pull/9822)
#### Estimated changes
Modified src/tactic/norm_cast.lean


Modified test/linarith.lean
- \+ *lemma* mytest



## [2021-10-29 01:24:36](https://github.com/leanprover-community/mathlib/commit/4ce2a5f)
chore(algebra/module/submodule_lattice): lemmas about the trivial submodule ([#10022](https://github.com/leanprover-community/mathlib/pull/10022))
Lemmas about the trivial submodule.  Also move an existing lemma `exists_mem_ne_zero_of_ne_bot` about the trivial submodule from `linear_algebra/dimension` to `algebra/module/submodule_lattice`, since it doesn't use any facts about dimension.
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* submodule.eq_bot_of_subsingleton
- \+ *lemma* submodule.exists_mem_ne_zero_of_ne_bot
- \+/\- *lemma* submodule.nonzero_mem_of_bot_lt

Modified src/linear_algebra/dimension.lean
- \- *lemma* exists_mem_ne_zero_of_ne_bot

Modified src/linear_algebra/eigenspace.lean




## [2021-10-29 01:24:35](https://github.com/leanprover-community/mathlib/commit/7538f9b)
feat(data/list/defs): map_with_prefix_suffix and map_with_complement ([#10020](https://github.com/leanprover-community/mathlib/pull/10020))
Adds two list definitions: one that will be useful to me, and a generalization which may be useful to @semorrison
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* list.map_with_complement
- \+ *def* list.map_with_prefix_suffix
- \+ *def* list.map_with_prefix_suffix_aux



## [2021-10-29 01:24:33](https://github.com/leanprover-community/mathlib/commit/c7f5139)
chore(measure_theory): drop a few `measurable_set` assumptions ([#9999](https://github.com/leanprover-community/mathlib/pull/9999))
We had an extra `measurable_set` assumption in (one of the copies of) Caratheodory. Also remove `measurable f` assumption in `is_finite_measure (map f μ)` and make it an instance.
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.is_finite_measure_map
- \+/\- *lemma* measure_theory.measure.restrict_union_add_inter
- \- *lemma* measure_theory.measure_eq_inter_diff
- \+ *lemma* measure_theory.measure_inter_add_diff
- \+ *lemma* measure_theory.measure_union_add_inter'
- \+/\- *lemma* measure_theory.measure_union_add_inter

Modified src/probability_theory/density.lean




## [2021-10-29 00:33:15](https://github.com/leanprover-community/mathlib/commit/bdcb731)
feat(linear_algebra/matrix/adjugate): det_adjugate and adjugate_adjugate ([#9991](https://github.com/leanprover-community/mathlib/pull/9991))
This also adds `matrix.mv_polynomial_X`
#### Estimated changes
Modified src/linear_algebra/matrix/adjugate.lean
- \+ *lemma* alg_hom.map_adjugate
- \+ *lemma* matrix.adjugate_adjugate'
- \+ *lemma* matrix.adjugate_adjugate
- \+ *lemma* matrix.det_adjugate
- \- *lemma* matrix.det_adjugate_eq_one
- \- *lemma* matrix.det_adjugate_of_cancel
- \- *lemma* matrix.det_adjugate_of_is_unit
- \+ *lemma* matrix.det_smul_adjugate_adjugate

Added src/linear_algebra/matrix/mv_polynomial.lean
- \+ *lemma* matrix.det_mv_polynomial_X_ne_zero
- \+ *lemma* matrix.mv_polynomial_X_map_eval₂
- \+ *lemma* matrix.mv_polynomial_X_map_matrix_aeval
- \+ *lemma* matrix.mv_polynomial_X_map_matrix_eval

Modified src/linear_algebra/special_linear_group.lean




## [2021-10-28 20:48:25](https://github.com/leanprover-community/mathlib/commit/415da22)
chore(topology,measure_theory): generalize a few instances ([#9967](https://github.com/leanprover-community/mathlib/pull/9967))
* Prove that `Π i : ι, π i` has second countable topology if `ι` is encodable and each `π i` has second countable topology.
* Similarly for `borel_space`.
* Preserve old instances about `fintype` because we don't have (and can't have) an instance `fintype ι → encodable ι`.
#### Estimated changes
Modified src/data/subtype.lean
- \+ *lemma* subtype.surjective_restrict

Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/bases.lean




## [2021-10-28 20:48:24](https://github.com/leanprover-community/mathlib/commit/0cfae43)
feat(archive/imo): IMO 2021 Q1 ([#8432](https://github.com/leanprover-community/mathlib/pull/8432))
Formalised solution to IMO 2021 Q1
#### Estimated changes
Added archive/imo/imo2021_q1.lean
- \+ *theorem* IMO_2021_Q1
- \+ *lemma* exists_finset_3_le_card_with_pairs_summing_to_squares
- \+ *lemma* exists_numbers_in_interval
- \+ *lemma* exists_triplet_summing_to_squares
- \+ *lemma* lower_bound
- \+ *lemma* radical_inequality
- \+ *lemma* upper_bound

Modified src/algebra/order/monoid.lean
- \+ *lemma* lt_or_lt_of_add_lt_add

Modified src/data/finset/basic.lean
- \+ *lemma* finset.exists_subset_or_subset_of_two_mul_lt_card



## [2021-10-28 18:57:48](https://github.com/leanprover-community/mathlib/commit/99a2d5b)
feat(ring_theory/adjoin_root): golf and generalize the algebra structure on `adjoin_root` ([#10019](https://github.com/leanprover-community/mathlib/pull/10019))
We already have a more general version of this instance elsewhere, lets just reuse it.
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* adjoin_root.algebra_map_eq'



## [2021-10-28 18:57:46](https://github.com/leanprover-community/mathlib/commit/18dce13)
feat(data/finset/interval): Bounded intervals in locally finite orders are finite ([#9960](https://github.com/leanprover-community/mathlib/pull/9960))
A set which is bounded above and below is finite. A set which is bounded below in an `order_top` is finite. A set which is bounded above in an `order_bot` is finite.
Also provide the `order_dual` constructions for `bdd_stuff` and `locally_finite_order`.
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+ *lemma* bdd_above.finite
- \+ *lemma* bdd_below.finite
- \+ *lemma* bdd_below.finite_of_bdd_above
- \+ *def* set.fintype_of_mem_bounds

Modified src/order/bounds.lean
- \+ *lemma* bdd_above.dual
- \+ *lemma* bdd_below.dual
- \+ *lemma* is_glb.dual
- \+/\- *lemma* is_glb.lower_bounds_eq
- \+/\- *lemma* is_glb.nonempty
- \+/\- *lemma* is_glb_lt_iff
- \+ *lemma* is_greatest.dual
- \+ *lemma* is_least.dual
- \+ *lemma* is_lub.dual
- \+/\- *lemma* lt_is_glb_iff

Modified src/order/locally_finite.lean
- \+ *lemma* Icc_to_dual
- \+ *lemma* Ico_to_dual
- \+ *lemma* Ioc_to_dual
- \+ *lemma* Ioo_to_dual



## [2021-10-28 18:57:45](https://github.com/leanprover-community/mathlib/commit/1733920)
feat(list): add some lemmas ([#9873](https://github.com/leanprover-community/mathlib/pull/9873))
Add a few lemmas about lists.
These are helpful when manipulating lists.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.head'_append
- \+ *theorem* list.last'_cons_cons
- \+ *theorem* list.last'_eq_last_of_ne_nil
- \+ *theorem* list.mem_last'_cons

Modified src/data/list/pairwise.lean
- \+ *theorem* list.pairwise.drop



## [2021-10-28 17:00:22](https://github.com/leanprover-community/mathlib/commit/e927aa4)
feat(data/set/function): restrict `dite/ite/piecewise/extend` ([#10017](https://github.com/leanprover-community/mathlib/pull/10017))
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.restrict_dite
- \+ *lemma* set.restrict_dite_compl
- \+ *lemma* set.restrict_extend_compl_range
- \+ *lemma* set.restrict_extend_range
- \+ *lemma* set.restrict_ite
- \+ *lemma* set.restrict_ite_compl
- \+ *lemma* set.restrict_piecewise
- \+ *lemma* set.restrict_piecewise_compl



## [2021-10-28 17:00:20](https://github.com/leanprover-community/mathlib/commit/0d6548f)
chore(*): a few lemmas about `range_splitting ([#10016](https://github.com/leanprover-community/mathlib/pull/10016))
#### Estimated changes
Modified src/data/equiv/set.lean
- \+ *lemma* equiv.coe_of_injective_symm

Modified src/data/set/basic.lean
- \+ *lemma* set.coe_comp_range_factorization
- \+ *lemma* set.preimage_range_splitting
- \+ *lemma* set.right_inverse_range_splitting

Modified src/logic/function/basic.lean
- \+ *theorem* function.left_inverse.right_inverse_of_injective
- \+ *theorem* function.left_inverse.right_inverse_of_surjective



## [2021-10-28 17:00:18](https://github.com/leanprover-community/mathlib/commit/b9ff26b)
chore(measure_theory/measure/measure_space): reorder, golf ([#10015](https://github.com/leanprover-community/mathlib/pull/10015))
Move `restrict_apply'` up and use it to golf some proofs. Drop an unneeded `measurable_set` assumption in 1 proof.
#### Estimated changes
Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.ae_of_ae_restrict_of_ae_restrict_compl
- \+/\- *lemma* measure_theory.measure.restrict_apply'
- \+/\- *lemma* measure_theory.measure.restrict_empty
- \+ *lemma* measure_theory.measure.restrict_eq_self'
- \- *lemma* measure_theory.measure.restrict_eq_self_of_measurable_subset
- \- *lemma* measure_theory.measure.restrict_eq_self_of_subset_of_measurable



## [2021-10-28 17:00:16](https://github.com/leanprover-community/mathlib/commit/fd6f681)
feat(order/bounded_lattice): add `is_compl.le_sup_right_iff_inf_left_le` ([#10014](https://github.com/leanprover-community/mathlib/pull/10014))
This lemma is a generalization of `is_compl.inf_left_eq_bot_iff`.
Also drop `inf_eq_bot_iff_le_compl` in favor of
`is_compl.inf_left_eq_bot_iff` and add
`set.subset_union_compl_iff_inter_subset`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.subset_union_compl_iff_inter_subset

Modified src/order/bounded_lattice.lean
- \- *lemma* inf_eq_bot_iff_le_compl
- \+ *lemma* is_compl.inf_left_le_of_le_sup_right
- \+ *lemma* is_compl.le_sup_right_iff_inf_left_le

Modified src/topology/uniform_space/separation.lean




## [2021-10-28 17:00:14](https://github.com/leanprover-community/mathlib/commit/22d32dc)
fix(field_theory/intermediate_field): use a better `algebra.smul` definition, and generalize ([#10012](https://github.com/leanprover-community/mathlib/pull/10012))
Previously coe_smul was not true by `rfl`
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.coe_smul
- \+ *lemma* intermediate_field.lift2_algebra_map

Modified src/ring_theory/trace.lean




## [2021-10-28 17:00:12](https://github.com/leanprover-community/mathlib/commit/fe76b5c)
feat(group_theory/subgroup/basic): `mul_mem_sup` ([#10007](https://github.com/leanprover-community/mathlib/pull/10007))
Adds `mul_mem_sup` and golfs a couple proofs that reprove this result.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mul_mem_sup

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mul_mem_sup

Modified src/group_theory/sylow.lean




## [2021-10-28 17:00:10](https://github.com/leanprover-community/mathlib/commit/c495ed6)
move(data/set/pairwise): Move `set.pairwise_on` ([#9986](https://github.com/leanprover-community/mathlib/pull/9986))
This moves `set.pairwise_on` to `data.set.pairwise`, where `pairwise` and `set.pairwise_disjoint` already are.
#### Estimated changes
Modified src/analysis/box_integral/partition/basic.lean


Modified src/data/list/pairwise.lean


Modified src/data/set/basic.lean
- \- *theorem* set.nonempty.pairwise_on_eq_iff_exists_eq
- \- *theorem* set.nonempty.pairwise_on_iff_exists_forall
- \- *lemma* set.pairwise_on.imp
- \- *lemma* set.pairwise_on.imp_on
- \- *theorem* set.pairwise_on.mono'
- \- *theorem* set.pairwise_on.mono
- \- *def* set.pairwise_on
- \- *lemma* set.pairwise_on_disjoint_on_mono
- \- *lemma* set.pairwise_on_empty
- \- *lemma* set.pairwise_on_eq_iff_exists_eq
- \- *lemma* set.pairwise_on_iff_exists_forall
- \- *lemma* set.pairwise_on_insert
- \- *lemma* set.pairwise_on_insert_of_symmetric
- \- *lemma* set.pairwise_on_of_forall
- \- *lemma* set.pairwise_on_pair
- \- *lemma* set.pairwise_on_pair_of_symmetric
- \- *lemma* set.pairwise_on_singleton
- \- *theorem* set.pairwise_on_top
- \- *lemma* set.pairwise_on_union
- \- *lemma* set.pairwise_on_union_of_symmetric

Modified src/data/set/function.lean
- \- *lemma* set.inj_on.pairwise_on_image

Modified src/data/set/lattice.lean
- \- *lemma* set.bUnion_diff_bUnion_eq
- \- *lemma* set.pairwise_on_Union
- \- *theorem* set.pairwise_on_disjoint_fiber
- \- *lemma* set.pairwise_on_sUnion

Modified src/data/set/pairwise.lean
- \+ *lemma* pairwise.mono
- \- *theorem* pairwise.mono
- \+ *lemma* pairwise.pairwise_on
- \- *theorem* pairwise.pairwise_on
- \+/\- *def* pairwise
- \+ *lemma* pairwise_disjoint_fiber
- \- *theorem* pairwise_disjoint_fiber
- \+ *lemma* pairwise_disjoint_on
- \- *theorem* pairwise_disjoint_on
- \+ *lemma* pairwise_disjoint_on_bool
- \- *theorem* pairwise_disjoint_on_bool
- \+ *lemma* pairwise_on_bool
- \- *theorem* pairwise_on_bool
- \+ *lemma* set.bUnion_diff_bUnion_eq
- \+ *lemma* set.inj_on.pairwise_on_image
- \+ *lemma* set.nonempty.pairwise_on_eq_iff_exists_eq
- \+ *lemma* set.nonempty.pairwise_on_iff_exists_forall
- \+ *lemma* set.pairwise_on.imp
- \+ *lemma* set.pairwise_on.imp_on
- \+ *lemma* set.pairwise_on.mono'
- \+ *lemma* set.pairwise_on.mono
- \+ *lemma* set.pairwise_on.on_injective
- \- *theorem* set.pairwise_on.on_injective
- \+ *def* set.pairwise_on
- \+ *lemma* set.pairwise_on_Union
- \+ *lemma* set.pairwise_on_disjoint_fiber
- \+ *lemma* set.pairwise_on_disjoint_on_mono
- \+ *lemma* set.pairwise_on_empty
- \+ *lemma* set.pairwise_on_eq_iff_exists_eq
- \+ *lemma* set.pairwise_on_iff_exists_forall
- \+ *lemma* set.pairwise_on_insert
- \+ *lemma* set.pairwise_on_insert_of_symmetric
- \+ *lemma* set.pairwise_on_of_forall
- \+ *lemma* set.pairwise_on_pair
- \+ *lemma* set.pairwise_on_pair_of_symmetric
- \+ *lemma* set.pairwise_on_sUnion
- \+ *lemma* set.pairwise_on_singleton
- \+ *lemma* set.pairwise_on_top
- \+ *lemma* set.pairwise_on_union
- \+ *lemma* set.pairwise_on_union_of_symmetric
- \+ *lemma* set.pairwise_on_univ
- \- *theorem* set.pairwise_on_univ
- \+/\- *lemma* symmetric.pairwise_on

Modified src/order/zorn.lean




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
Modified src/computability/tm_to_partrec.lean
- \+ *def* turing.partrec_to_TM2.code_supp'
- \+ *theorem* turing.partrec_to_TM2.code_supp'_self
- \+ *theorem* turing.partrec_to_TM2.code_supp'_supports
- \+ *def* turing.partrec_to_TM2.code_supp
- \+ *theorem* turing.partrec_to_TM2.code_supp_case
- \+ *theorem* turing.partrec_to_TM2.code_supp_comp
- \+ *theorem* turing.partrec_to_TM2.code_supp_cons
- \+ *theorem* turing.partrec_to_TM2.code_supp_fix
- \+ *theorem* turing.partrec_to_TM2.code_supp_self
- \+ *theorem* turing.partrec_to_TM2.code_supp_succ
- \+ *theorem* turing.partrec_to_TM2.code_supp_supports
- \+ *theorem* turing.partrec_to_TM2.code_supp_tail
- \+ *theorem* turing.partrec_to_TM2.code_supp_zero
- \+ *def* turing.partrec_to_TM2.cont_supp
- \+ *theorem* turing.partrec_to_TM2.cont_supp_comp
- \+ *theorem* turing.partrec_to_TM2.cont_supp_cons₁
- \+ *theorem* turing.partrec_to_TM2.cont_supp_cons₂
- \+ *theorem* turing.partrec_to_TM2.cont_supp_fix
- \+ *theorem* turing.partrec_to_TM2.cont_supp_halt
- \+ *theorem* turing.partrec_to_TM2.cont_supp_supports
- \+ *theorem* turing.partrec_to_TM2.head_supports
- \+ *theorem* turing.partrec_to_TM2.ret_supports
- \+ *def* turing.partrec_to_TM2.supports
- \+ *theorem* turing.partrec_to_TM2.supports_bUnion
- \+ *theorem* turing.partrec_to_TM2.supports_insert
- \+ *theorem* turing.partrec_to_TM2.supports_singleton
- \+ *theorem* turing.partrec_to_TM2.supports_union
- \+ *theorem* turing.partrec_to_TM2.tr_normal_supports
- \+ *def* turing.partrec_to_TM2.tr_stmts₁
- \+ *theorem* turing.partrec_to_TM2.tr_stmts₁_self
- \+ *theorem* turing.partrec_to_TM2.tr_stmts₁_supports'
- \+ *theorem* turing.partrec_to_TM2.tr_stmts₁_supports
- \+ *theorem* turing.partrec_to_TM2.tr_stmts₁_trans
- \+ *theorem* turing.partrec_to_TM2.tr_supports
- \+ *def* turing.partrec_to_TM2.Λ'.supports

Modified src/computability/turing_machine.lean


Modified src/data/finset/basic.lean
- \+ *theorem* finset.bUnion_subset
- \+ *theorem* finset.inter_left_idem
- \+ *theorem* finset.inter_right_idem
- \+ *theorem* finset.union_left_idem
- \+ *theorem* finset.union_right_idem
- \+ *theorem* finset.union_subset_left
- \+ *theorem* finset.union_subset_right



## [2021-10-28 15:13:55](https://github.com/leanprover-community/mathlib/commit/c8d1429)
feat(data/{finset,multiset}/locally_finite): Simple interval lemmas ([#9877](https://github.com/leanprover-community/mathlib/pull/9877))
`(finset/multiset).image_add_(left/right)_Ixx` and `multiset.nodup_Ixx`
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+/\- *lemma* finset.prod_Ico_add
- \+/\- *lemma* finset.sum_Ico_add

Modified src/data/finset/locally_finite.lean
- \- *lemma* finset.image_add_const_Icc
- \- *lemma* finset.image_add_const_Ico
- \- *lemma* finset.image_add_const_Ioc
- \- *lemma* finset.image_add_const_Ioo
- \+ *lemma* finset.image_add_left_Icc
- \+ *lemma* finset.image_add_left_Ico
- \+ *lemma* finset.image_add_left_Ioc
- \+ *lemma* finset.image_add_left_Ioo
- \+ *lemma* finset.image_add_right_Icc
- \+ *lemma* finset.image_add_right_Ico
- \+ *lemma* finset.image_add_right_Ioc
- \+ *lemma* finset.image_add_right_Ioo

Modified src/data/multiset/locally_finite.lean
- \- *lemma* multiset.map_add_const_Icc
- \- *lemma* multiset.map_add_const_Ioc
- \- *lemma* multiset.map_add_const_Ioo
- \+ *lemma* multiset.map_add_left_Icc
- \+ *lemma* multiset.map_add_left_Ioc
- \+ *lemma* multiset.map_add_left_Ioo
- \+ *lemma* multiset.map_add_right_Icc
- \+ *lemma* multiset.map_add_right_Ioc
- \+ *lemma* multiset.map_add_right_Ioo
- \+ *lemma* multiset.nodup_Icc
- \+ *lemma* multiset.nodup_Ioc
- \+ *lemma* multiset.nodup_Ioo



## [2021-10-28 12:41:11](https://github.com/leanprover-community/mathlib/commit/acbb2a5)
feat(analysis/normed_space/pi_Lp): use typeclass inference for `1 ≤ p` ([#9922](https://github.com/leanprover-community/mathlib/pull/9922))
In `measure_theory.Lp`, the exponent `(p : ℝ≥0∞)` is an explicit hypothesis, and typeclass inference finds `[fact (1 ≤ p)]` silently (with the help of some pre-built `fact_one_le_two_ennreal` etc for specific use cases).
Currently, in `pi_Lp`, the fact that `(hp : 1 ≤ p)` must be provided explicitly.  I propose changing over to the `fact` system as used `measure_theory.Lp` -- I think it looks a bit prettier in typical use cases.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* fact_one_le_one_real
- \+ *lemma* fact_one_le_two_real
- \+/\- *def* pi_Lp.emetric_aux
- \+/\- *lemma* pi_Lp.lipschitz_with_equiv
- \+/\- *lemma* pi_Lp.norm_eq
- \+/\- *lemma* pi_Lp.norm_eq_of_nat
- \+/\- *def* pi_Lp.pseudo_emetric_aux
- \+/\- *def* pi_Lp

Modified src/geometry/manifold/instances/real.lean




## [2021-10-28 09:24:44](https://github.com/leanprover-community/mathlib/commit/b0349aa)
chore(measure_theory): a `continuous_map` is measurable ([#9998](https://github.com/leanprover-community/mathlib/pull/9998))
Also move the proof of `homeomorph.measurable` up and use it in the
definition of `homeomorph.to_measurable_equiv`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous_map.measurable
- \- *lemma* homeomorph.measurable



## [2021-10-28 09:24:43](https://github.com/leanprover-community/mathlib/commit/73423cf)
feat(measure/measurable_space): add `measurable_equiv.of_unique_of_unique` ([#9968](https://github.com/leanprover-community/mathlib/pull/9968))
Also fix a typo in a lemma name: `measurable_equiv.measurable_coe_iff` → `measurable_comp_iff`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *def* measurable_equiv.of_unique_of_unique



## [2021-10-28 09:24:41](https://github.com/leanprover-community/mathlib/commit/7f2b806)
feat(analysis/inner_product_space/dual): complex Riesz representation theorem ([#9924](https://github.com/leanprover-community/mathlib/pull/9924))
Now that we have conjugate-linear maps, the Riesz representation theorem can be stated in a form that works over both `ℝ` and `ℂ`, as the construction of a conjugate-linear isometric equivalence from a complete inner product space `E` to its dual.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean
- \- *lemma* inner_product_space.norm_to_dual'_apply
- \- *def* inner_product_space.to_dual'
- \- *lemma* inner_product_space.to_dual'_apply
- \- *lemma* inner_product_space.to_dual'_isometry
- \- *lemma* inner_product_space.to_dual'_surjective
- \+/\- *def* inner_product_space.to_dual
- \+/\- *lemma* inner_product_space.to_dual_apply
- \+/\- *def* inner_product_space.to_dual_map
- \+/\- *lemma* inner_product_space.to_dual_map_apply



## [2021-10-28 06:57:32](https://github.com/leanprover-community/mathlib/commit/f78b739)
feat(category_theory/arrow): is_iso, mono, epi instances for maps between arrows ([#9976](https://github.com/leanprover-community/mathlib/pull/9976))
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.is_iso_of_iso_left_of_is_iso_right



## [2021-10-28 06:57:30](https://github.com/leanprover-community/mathlib/commit/8159af6)
feat(measure_theory/construction/borel_space): two measures are equal if they agree on closed-open intervals ([#9396](https://github.com/leanprover-community/mathlib/pull/9396))
#### Estimated changes
Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* set.Union_Ico_eq_Iio_self_iff
- \+ *lemma* set.Union_Ioc_eq_Ioi_self_iff
- \+ *lemma* set.bUnion_Ico_eq_Iio_self_iff
- \+ *lemma* set.bUnion_Ioc_eq_Ioi_self_iff

Modified src/data/set/lattice.lean


Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* borel_eq_generate_Iio
- \- *lemma* borel_eq_generate_Ioi
- \+ *lemma* borel_eq_generate_from_Ico
- \+ *lemma* borel_eq_generate_from_Iio
- \+ *lemma* borel_eq_generate_from_Ioc
- \+ *lemma* borel_eq_generate_from_Ioi
- \+ *lemma* bsupr_measure_Iic
- \+ *lemma* dense.borel_eq_generate_from_Ico_mem
- \+ *lemma* dense.borel_eq_generate_from_Ico_mem_aux
- \+ *lemma* dense.borel_eq_generate_from_Ioc_mem
- \+ *lemma* dense.borel_eq_generate_from_Ioc_mem_aux
- \+ *lemma* generate_from_Ico_mem_le_borel
- \- *lemma* is_pi_system_Ioo
- \- *lemma* is_pi_system_Ioo_mem
- \+ *lemma* measure_theory.measure.ext_of_Ici
- \+ *lemma* measure_theory.measure.ext_of_Ico'
- \+ *lemma* measure_theory.measure.ext_of_Ico
- \+ *lemma* measure_theory.measure.ext_of_Ico_finite
- \+ *lemma* measure_theory.measure.ext_of_Iic
- \+ *lemma* measure_theory.measure.ext_of_Ioc'
- \+ *lemma* measure_theory.measure.ext_of_Ioc
- \+ *lemma* measure_theory.measure.ext_of_Ioc_finite

Modified src/measure_theory/measurable_space.lean
- \- *lemma* measurable_space.generate_from_le_generate_from
- \+ *lemma* measurable_space.generate_from_mono

Modified src/measure_theory/measure/stieltjes.lean


Modified src/measure_theory/pi_system.lean
- \+ *lemma* is_pi_system_Icc
- \+ *lemma* is_pi_system_Icc_mem
- \+ *lemma* is_pi_system_Ico
- \+ *lemma* is_pi_system_Ico_mem
- \+ *lemma* is_pi_system_Iio
- \+ *lemma* is_pi_system_Ioc
- \+ *lemma* is_pi_system_Ioc_mem
- \+ *lemma* is_pi_system_Ioi
- \+ *lemma* is_pi_system_Ioo
- \+ *lemma* is_pi_system_Ioo_mem
- \+ *lemma* is_pi_system_Ixx
- \+ *lemma* is_pi_system_Ixx_mem
- \+ *lemma* is_pi_system_image_Iio
- \+ *lemma* is_pi_system_image_Ioi

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* dense.exists_between
- \+ *lemma* dense.exists_ge'
- \+ *lemma* dense.exists_ge
- \+ *lemma* dense.exists_gt
- \+ *lemma* dense.exists_le'
- \+ *lemma* dense.exists_le
- \+ *lemma* dense.exists_lt
- \+ *lemma* dense.order_dual

Modified src/topology/bases.lean
- \+ *lemma* dense.exists_countable_dense_subset_bot_top
- \+ *lemma* exists_countable_dense_bot_top



## [2021-10-28 04:50:38](https://github.com/leanprover-community/mathlib/commit/468a9d5)
chore(scripts): update nolints.txt ([#10013](https://github.com/leanprover-community/mathlib/pull/10013))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-10-28 04:50:37](https://github.com/leanprover-community/mathlib/commit/bcaeb57)
fix(data/equiv/encodable): turn `unique.encodable` into a `def` ([#10006](https://github.com/leanprover-community/mathlib/pull/10006))
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean
- \+ *def* unique.encodable



## [2021-10-28 02:37:00](https://github.com/leanprover-community/mathlib/commit/9db7270)
chore(*): rename gsmul to zsmul and gmultiples to zmultiples ([#10010](https://github.com/leanprover-community/mathlib/pull/10010))
This is consistent with an earlier rename from `gpow` to `zpow`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/subalgebra.lean
- \- *theorem* subalgebra.gsmul_mem
- \+ *theorem* subalgebra.zsmul_mem

Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.gsmul_sum
- \+ *lemma* finset.zsmul_sum

Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/group/defs.lean
- \- *def* gsmul_rec
- \+ *def* zsmul_rec

Modified src/algebra/group/hom_instances.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group_power/basic.lean
- \- *lemma* of_add_gsmul
- \+ *lemma* of_add_zsmul

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* abs_gsmul
- \+ *lemma* abs_zsmul
- \- *theorem* add_gsmul
- \- *theorem* add_monoid_hom.map_gsmul
- \+ *theorem* add_monoid_hom.map_zsmul
- \- *theorem* add_one_gsmul
- \+ *theorem* add_one_zsmul
- \+ *theorem* add_zsmul
- \- *theorem* bit0_gsmul
- \+ *theorem* bit0_zsmul
- \- *theorem* bit1_gsmul
- \+ *theorem* bit1_zsmul
- \- *def* gmultiples_add_hom
- \- *lemma* gmultiples_add_hom_apply
- \- *lemma* gmultiples_add_hom_symm_apply
- \- *def* gmultiples_hom
- \- *lemma* gmultiples_hom_apply
- \- *lemma* gmultiples_hom_symm_apply
- \- *theorem* gsmul_add_comm
- \- *lemma* gsmul_eq_gsmul_iff'
- \- *theorem* gsmul_eq_mul'
- \- *theorem* gsmul_eq_mul
- \- *lemma* gsmul_int_int
- \- *lemma* gsmul_int_one
- \- *theorem* gsmul_le_gsmul'
- \- *theorem* gsmul_le_gsmul
- \- *theorem* gsmul_le_gsmul_iff'
- \- *theorem* gsmul_le_gsmul_iff
- \- *theorem* gsmul_lt_gsmul'
- \- *theorem* gsmul_lt_gsmul
- \- *theorem* gsmul_lt_gsmul_iff'
- \- *theorem* gsmul_lt_gsmul_iff
- \- *theorem* gsmul_mono_left
- \- *lemma* gsmul_mono_right
- \- *theorem* gsmul_mul'
- \- *theorem* gsmul_one
- \- *lemma* gsmul_pos
- \- *lemma* gsmul_right_inj
- \- *lemma* gsmul_right_injective
- \- *theorem* gsmul_strict_mono_left
- \- *lemma* gsmul_strict_mono_right
- \- *theorem* mul_gsmul
- \- *theorem* mul_gsmul_assoc
- \- *theorem* mul_gsmul_left
- \+ *theorem* mul_zsmul
- \+ *theorem* mul_zsmul_assoc
- \+ *theorem* mul_zsmul_left
- \- *theorem* one_add_gsmul
- \+ *theorem* one_add_zsmul
- \- *lemma* sub_gsmul
- \+ *lemma* sub_zsmul
- \+ *def* zmultiples_add_hom
- \+ *lemma* zmultiples_add_hom_apply
- \+ *lemma* zmultiples_add_hom_symm_apply
- \+ *def* zmultiples_hom
- \+ *lemma* zmultiples_hom_apply
- \+ *lemma* zmultiples_hom_symm_apply
- \+ *theorem* zsmul_add_comm
- \+ *theorem* zsmul_eq_mul'
- \+ *theorem* zsmul_eq_mul
- \+ *lemma* zsmul_eq_zsmul_iff'
- \+ *lemma* zsmul_int_int
- \+ *lemma* zsmul_int_one
- \+ *theorem* zsmul_le_zsmul'
- \+ *theorem* zsmul_le_zsmul
- \+ *theorem* zsmul_le_zsmul_iff'
- \+ *theorem* zsmul_le_zsmul_iff
- \+ *theorem* zsmul_lt_zsmul'
- \+ *theorem* zsmul_lt_zsmul
- \+ *theorem* zsmul_lt_zsmul_iff'
- \+ *theorem* zsmul_lt_zsmul_iff
- \+ *theorem* zsmul_mono_left
- \+ *lemma* zsmul_mono_right
- \+ *theorem* zsmul_mul'
- \+ *theorem* zsmul_one
- \+ *lemma* zsmul_pos
- \+ *lemma* zsmul_right_inj
- \+ *lemma* zsmul_right_injective
- \+ *theorem* zsmul_strict_mono_left
- \+ *lemma* zsmul_strict_mono_right

Modified src/algebra/group_power/order.lean


Modified src/algebra/homology/additive.lean


Modified src/algebra/iterate_hom.lean
- \- *theorem* add_monoid_hom.iterate_map_gsmul
- \+ *theorem* add_monoid_hom.iterate_map_zsmul
- \- *theorem* ring_hom.iterate_map_gsmul
- \+ *theorem* ring_hom.iterate_map_zsmul

Modified src/algebra/lie/basic.lean
- \- *lemma* gsmul_lie
- \- *lemma* lie_gsmul
- \+ *lemma* lie_zsmul
- \+ *lemma* zsmul_lie

Modified src/algebra/module/basic.lean
- \- *lemma* gsmul_eq_smul_cast
- \- *lemma* int_smul_eq_gsmul
- \+ *lemma* int_smul_eq_zsmul
- \+ *lemma* zsmul_eq_smul_cast

Modified src/algebra/module/linear_map.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/periodic.lean
- \- *lemma* function.periodic.gsmul
- \- *lemma* function.periodic.gsmul_eq
- \- *lemma* function.periodic.gsmul_sub_eq
- \- *lemma* function.periodic.sub_gsmul_eq
- \+ *lemma* function.periodic.sub_zsmul_eq
- \+ *lemma* function.periodic.zsmul
- \+ *lemma* function.periodic.zsmul_eq
- \+ *lemma* function.periodic.zsmul_sub_eq

Modified src/algebra/quaternion.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebra/star/basic.lean
- \- *lemma* star_gsmul
- \+ *lemma* star_zsmul

Modified src/algebra/star/chsh.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/normed_space/basic.lean
- \- *lemma* nnnorm_gsmul_le
- \+ *lemma* nnnorm_zsmul_le
- \- *lemma* norm_gsmul_le
- \+ *lemma* norm_zsmul_le

Modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* real.angle.coe_int_mul_eq_gsmul
- \+ *lemma* real.angle.coe_int_mul_eq_zsmul

Modified src/category_theory/linear/default.lean


Modified src/category_theory/linear/linear_functor.lean


Modified src/category_theory/preadditive/additive_functor.lean
- \- *lemma* category_theory.functor.map_gsmul
- \+ *lemma* category_theory.functor.map_zsmul

Modified src/category_theory/preadditive/default.lean
- \- *lemma* category_theory.preadditive.comp_gsmul
- \+ *lemma* category_theory.preadditive.comp_zsmul
- \- *lemma* category_theory.preadditive.gsmul_comp
- \+ *lemma* category_theory.preadditive.zsmul_comp

Modified src/category_theory/preadditive/functor_category.lean
- \- *lemma* category_theory.nat_trans.app_gsmul
- \+ *lemma* category_theory.nat_trans.app_zsmul

Modified src/data/complex/basic.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp/basic.lean


Modified src/data/holor.lean


Modified src/data/int/basic.lean


Modified src/data/polynomial/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/quotient.lean
- \- *def* int.quotient_gmultiples_equiv_zmod
- \- *def* int.quotient_gmultiples_nat_equiv_zmod
- \+ *def* int.quotient_zmultiples_equiv_zmod
- \+ *def* int.quotient_zmultiples_nat_equiv_zmod

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/intermediate_field.lean
- \- *lemma* intermediate_field.gsmul_mem
- \+ *lemma* intermediate_field.zsmul_mem

Modified src/field_theory/subfield.lean
- \- *lemma* subfield.gsmul_mem
- \+ *lemma* subfield.zsmul_mem

Modified src/group_theory/archimedean.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_abelian_group_finsupp.lean
- \- *lemma* free_abelian_group.support_gsmul
- \+ *lemma* free_abelian_group.support_zsmul

Modified src/group_theory/order_of_element.lean
- \- *lemma* add_order_eq_card_gmultiples
- \+ *lemma* add_order_eq_card_zmultiples
- \- *lemma* exists_gsmul_eq_zero
- \+ *lemma* exists_zsmul_eq_zero
- \- *lemma* fin_equiv_gmultiples_apply
- \- *lemma* fin_equiv_gmultiples_symm_apply
- \+ *lemma* fin_equiv_zmultiples_apply
- \+ *lemma* fin_equiv_zmultiples_symm_apply
- \- *lemma* gmultiples_equiv_gmultiples_apply
- \- *lemma* gsmul_eq_mod_add_order_of
- \- *lemma* mem_gmultiples_iff_mem_range_add_order_of
- \- *lemma* mem_multiples_iff_mem_gmultiples
- \+ *lemma* mem_multiples_iff_mem_zmultiples
- \+ *lemma* mem_zmultiples_iff_mem_range_add_order_of
- \- *lemma* multiples_eq_gmultiples
- \+ *lemma* multiples_eq_zmultiples
- \+ *lemma* zmultiples_equiv_zmultiples_apply
- \+ *lemma* zsmul_eq_mod_add_order_of

Modified src/group_theory/specific_groups/quaternion.lean


Modified src/group_theory/subgroup/basic.lean
- \- *lemma* add_subgroup.coe_gsmul
- \+ *lemma* add_subgroup.coe_zsmul
- \- *def* add_subgroup.gmultiples
- \- *lemma* add_subgroup.gmultiples_subset
- \- *lemma* add_subgroup.range_gmultiples_hom
- \+ *lemma* add_subgroup.range_zmultiples_hom
- \+ *def* add_subgroup.zmultiples
- \+ *lemma* add_subgroup.zmultiples_subset
- \- *lemma* int.mem_gmultiples_iff
- \+ *lemma* int.mem_zmultiples_iff
- \- *lemma* of_add_image_gmultiples_eq_zpowers_of_add
- \+ *lemma* of_add_image_zmultiples_eq_zpowers_of_add
- \- *lemma* of_mul_image_zpowers_eq_gmultiples_of_mul
- \+ *lemma* of_mul_image_zpowers_eq_zmultiples_of_mul

Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/quotient.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/ring_theory/int/basic.lean
- \- *lemma* int.gmultiples_nat_abs
- \+ *lemma* int.zmultiples_nat_abs

Modified src/ring_theory/integral_closure.lean
- \- *lemma* is_integral.gsmul
- \+ *lemma* is_integral.zsmul

Modified src/ring_theory/localization.lean


Modified src/ring_theory/subring.lean
- \- *lemma* subring.gsmul_mem
- \+ *lemma* subring.zsmul_mem

Modified src/set_theory/surreal/dyadic.lean


Modified src/tactic/abel.lean
- \- *theorem* tactic.abel.unfold_gsmul
- \+ *theorem* tactic.abel.unfold_zsmul

Modified src/tactic/noncomm_ring.lean


Modified src/topology/algebra/module.lean
- \- *lemma* continuous_linear_map.continuous.gsmul
- \+ *lemma* continuous_linear_map.continuous.zsmul
- \- *lemma* continuous_linear_map.continuous_gsmul
- \+ *lemma* continuous_linear_map.continuous_zsmul



## [2021-10-27 20:21:14](https://github.com/leanprover-community/mathlib/commit/d360f3c)
feat(linear_algebra/free_module/finite/rank): add linear_algebra/free_module/finite/rank ([#9832](https://github.com/leanprover-community/mathlib/pull/9832))
A basic API for rank of free modules.
- [x] depends on: [#9821](https://github.com/leanprover-community/mathlib/pull/9821)
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_self

Modified src/linear_algebra/finite_dimensional.lean


Added src/linear_algebra/free_module/finite/rank.lean
- \+ *lemma* module.free.finrank_direct_sum
- \+ *lemma* module.free.finrank_eq_card_choose_basis_index
- \+ *lemma* module.free.finrank_eq_rank
- \+ *lemma* module.free.finrank_finsupp
- \+ *lemma* module.free.finrank_linear_hom
- \+ *lemma* module.free.finrank_matrix
- \+ *lemma* module.free.finrank_pi
- \+ *lemma* module.free.finrank_pi_fintype
- \+ *lemma* module.free.finrank_prod
- \+ *lemma* module.free.finrank_tensor_product
- \+ *lemma* module.free.rank_lt_omega

Modified src/linear_algebra/free_module/rank.lean
- \+/\- *lemma* module.free.rank_direct_sum
- \+ *lemma* module.free.rank_matrix''
- \+ *lemma* module.free.rank_matrix'
- \+ *lemma* module.free.rank_matrix
- \+ *lemma* module.free.rank_pi_fintype

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.to_nat_add_of_lt_omega
- \+/\- *lemma* cardinal.to_nat_mul



## [2021-10-27 17:47:32](https://github.com/leanprover-community/mathlib/commit/8ce5da4)
feat(algebra/order/archimedean): a few more lemmas ([#9997](https://github.com/leanprover-community/mathlib/pull/9997))
Prove that `a + m • b ∈ Ioc c (c + b)` for some `m : ℤ`, and similarly for `Ico`.
Also move some lemmas out of a namespace.
#### Estimated changes
Modified src/algebra/order/archimedean.lean
- \+ *lemma* exists_add_int_smul_mem_Ico
- \+ *lemma* exists_add_int_smul_mem_Ioc
- \+ *lemma* exists_int_smul_near_of_pos'
- \+ *lemma* exists_int_smul_near_of_pos
- \- *lemma* linear_ordered_add_comm_group.exists_int_smul_near_of_pos'
- \- *lemma* linear_ordered_add_comm_group.exists_int_smul_near_of_pos

Modified src/algebra/periodic.lean
- \+ *lemma* function.periodic.exists_mem_Ico₀
- \+ *lemma* function.periodic.exists_mem_Ioc

Modified src/topology/instances/real.lean




## [2021-10-27 17:47:31](https://github.com/leanprover-community/mathlib/commit/ec51fb7)
chore(algebra/order/floor): prove `subsingleton`s ([#9996](https://github.com/leanprover-community/mathlib/pull/9996))
#### Estimated changes
Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/order/floor.lean
- \- *lemma* floor_ring_unique
- \- *lemma* floor_semiring_unique
- \+ *lemma* subsingleton_floor_ring
- \+ *lemma* subsingleton_floor_semiring



## [2021-10-27 17:47:29](https://github.com/leanprover-community/mathlib/commit/eaec1da)
feat(group_theory/group_action/conj_act): A characteristic subgroup of a normal subgroup is normal ([#9992](https://github.com/leanprover-community/mathlib/pull/9992))
Uses `mul_aut.conj_normal` to prove an instance stating that a characteristic subgroup of a normal subgroup is normal.
#### Estimated changes
Modified src/group_theory/group_action/conj_act.lean




## [2021-10-27 17:47:27](https://github.com/leanprover-community/mathlib/commit/c529711)
refactor(*): rename fpow and gpow to zpow ([#9989](https://github.com/leanprover-community/mathlib/pull/9989))
Historically, we had two notions of integer power, one on groups called `gpow` and the other one on fields called `fpow`. Since the introduction of `div_inv_monoid` and `group_with_zero`, these definitions have been merged into one, and the boundaries are not clear any more. We rename both of them to `zpow`, adding a subscript `0` to disambiguate lemma names when there is a collision, where the subscripted version is for groups with zeroes (as is already done for inv lemmas).
To limit the scope of the change. this PR does not rename `gsmul` to `zsmul` or `gmultiples` to `zmultiples`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \- *lemma* abs_fpow_bit0
- \+ *lemma* abs_zpow_bit0
- \- *lemma* even.abs_fpow
- \+ *lemma* even.abs_zpow
- \- *lemma* even.fpow_abs
- \- *lemma* even.fpow_neg
- \- *lemma* even.fpow_nonneg
- \- *theorem* even.fpow_pos
- \+ *lemma* even.zpow_abs
- \+ *lemma* even.zpow_neg
- \+ *lemma* even.zpow_nonneg
- \+ *theorem* even.zpow_pos
- \- *lemma* fpow_bit0_abs
- \- *lemma* fpow_bit0_neg
- \- *theorem* fpow_bit0_nonneg
- \- *theorem* fpow_bit0_pos
- \- *lemma* fpow_bit1_neg
- \- *theorem* fpow_bit1_neg_iff
- \- *theorem* fpow_bit1_nonneg_iff
- \- *theorem* fpow_bit1_nonpos_iff
- \- *theorem* fpow_bit1_pos_iff
- \- *lemma* fpow_eq_zero_iff
- \- *lemma* fpow_inj
- \- *lemma* fpow_injective
- \- *lemma* fpow_le_iff_le
- \- *lemma* fpow_le_of_le
- \- *lemma* fpow_le_one_of_nonpos
- \- *lemma* fpow_lt_iff_lt
- \- *lemma* fpow_nonneg
- \- *lemma* fpow_pos_of_pos
- \- *lemma* fpow_strict_mono
- \- *theorem* fpow_two_nonneg
- \- *theorem* fpow_two_pos_of_ne_zero
- \- *lemma* nat.fpow_ne_zero_of_pos
- \- *lemma* nat.fpow_pos_of_pos
- \+ *lemma* nat.zpow_ne_zero_of_pos
- \+ *lemma* nat.zpow_pos_of_pos
- \- *theorem* odd.fpow_neg
- \- *theorem* odd.fpow_nonneg
- \- *theorem* odd.fpow_nonpos
- \- *theorem* odd.fpow_pos
- \+ *theorem* odd.zpow_neg
- \+ *theorem* odd.zpow_nonneg
- \+ *theorem* odd.zpow_nonpos
- \+ *theorem* odd.zpow_pos
- \- *lemma* one_le_fpow_of_nonneg
- \+ *lemma* one_le_zpow_of_nonneg
- \- *lemma* one_lt_fpow
- \+ *lemma* one_lt_zpow
- \- *theorem* rat.cast_fpow
- \+ *theorem* rat.cast_zpow
- \- *lemma* ring_equiv.map_fpow
- \+ *lemma* ring_equiv.map_zpow
- \- *lemma* ring_hom.map_fpow
- \+ *lemma* ring_hom.map_zpow
- \+ *lemma* zpow_bit0_abs
- \+ *lemma* zpow_bit0_neg
- \+ *theorem* zpow_bit0_nonneg
- \+ *theorem* zpow_bit0_pos
- \+ *lemma* zpow_bit1_neg
- \+ *theorem* zpow_bit1_neg_iff
- \+ *theorem* zpow_bit1_nonneg_iff
- \+ *theorem* zpow_bit1_nonpos_iff
- \+ *theorem* zpow_bit1_pos_iff
- \+ *lemma* zpow_eq_zero_iff
- \+ *lemma* zpow_inj
- \+ *lemma* zpow_injective
- \+ *lemma* zpow_le_iff_le
- \+ *lemma* zpow_le_of_le
- \+ *lemma* zpow_le_one_of_nonpos
- \+ *lemma* zpow_lt_iff_lt
- \+ *lemma* zpow_nonneg
- \+ *lemma* zpow_pos_of_pos
- \+ *lemma* zpow_strict_mono
- \+ *theorem* zpow_two_nonneg
- \+ *theorem* zpow_two_pos_of_ne_zero

Modified src/algebra/group/conj.lean
- \- *lemma* conj_gpow
- \+ *lemma* conj_zpow

Modified src/algebra/group/defs.lean
- \- *def* gpow_rec
- \+ *def* zpow_rec

Modified src/algebra/group/hom_instances.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/basic.lean
- \- *lemma* commute.gpow_gpow
- \- *theorem* commute.gpow_gpow_self
- \- *lemma* commute.gpow_left
- \- *lemma* commute.gpow_right
- \- *theorem* commute.gpow_self
- \- *theorem* commute.mul_gpow
- \+ *theorem* commute.mul_zpow
- \- *theorem* commute.self_gpow
- \+ *theorem* commute.self_zpow
- \+ *lemma* commute.zpow_left
- \+ *lemma* commute.zpow_right
- \+ *theorem* commute.zpow_self
- \+ *lemma* commute.zpow_zpow
- \+ *theorem* commute.zpow_zpow_self
- \- *theorem* div_gpow
- \+ *theorem* div_zpow
- \- *theorem* gpow_coe_nat
- \- *lemma* gpow_eq_pow
- \- *def* gpow_group_hom
- \- *theorem* gpow_neg
- \- *theorem* gpow_neg_one
- \- *theorem* gpow_neg_succ_of_nat
- \- *theorem* gpow_of_nat
- \- *theorem* gpow_one
- \- *theorem* gpow_zero
- \- *theorem* inv_gpow
- \+ *theorem* inv_zpow
- \- *theorem* mul_gpow
- \- *lemma* mul_gpow_neg_one
- \+ *theorem* mul_zpow
- \+ *lemma* mul_zpow_neg_one
- \- *lemma* of_mul_gpow
- \+ *lemma* of_mul_zpow
- \- *theorem* one_gpow
- \+ *theorem* one_zpow
- \- *lemma* semiconj_by.gpow_right
- \+ *lemma* semiconj_by.zpow_right
- \+ *theorem* zpow_coe_nat
- \+ *lemma* zpow_eq_pow
- \+ *def* zpow_group_hom
- \+ *theorem* zpow_neg
- \+ *theorem* zpow_neg_one
- \+ *theorem* zpow_neg_succ_of_nat
- \+ *theorem* zpow_of_nat
- \+ *theorem* zpow_one
- \+ *theorem* zpow_zero

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* commute.units_gpow_left
- \- *lemma* commute.units_gpow_right
- \+ *lemma* commute.units_zpow_left
- \+ *lemma* commute.units_zpow_right
- \- *lemma* gpow_add
- \- *lemma* gpow_add_one
- \- *theorem* gpow_bit0
- \- *theorem* gpow_bit1
- \- *theorem* gpow_mul'
- \- *theorem* gpow_mul
- \- *theorem* gpow_mul_comm
- \- *theorem* gpow_one_add
- \- *lemma* gpow_sub
- \- *lemma* gpow_sub_one
- \- *def* gpowers_hom
- \- *lemma* gpowers_hom_apply
- \- *lemma* gpowers_hom_symm_apply
- \- *def* gpowers_mul_hom
- \- *lemma* gpowers_mul_hom_apply
- \- *lemma* gpowers_mul_hom_symm_apply
- \- *lemma* int.to_add_gpow
- \+ *lemma* int.to_add_zpow
- \- *theorem* monoid_hom.map_gpow
- \+ *theorem* monoid_hom.map_zpow
- \- *lemma* mul_gpow_self
- \- *lemma* mul_self_gpow
- \+ *lemma* mul_self_zpow
- \+ *lemma* mul_zpow_self
- \- *lemma* opposite.op_gpow
- \+ *lemma* opposite.op_zpow
- \- *lemma* opposite.unop_gpow
- \+ *lemma* opposite.unop_zpow
- \- *lemma* semiconj_by.units_gpow_right
- \+ *lemma* semiconj_by.units_zpow_right
- \- *lemma* units.coe_gpow
- \+ *lemma* units.coe_zpow
- \+ *lemma* zpow_add
- \+ *lemma* zpow_add_one
- \+ *theorem* zpow_bit0
- \+ *theorem* zpow_bit1
- \+ *theorem* zpow_mul'
- \+ *theorem* zpow_mul
- \+ *theorem* zpow_mul_comm
- \+ *theorem* zpow_one_add
- \+ *lemma* zpow_sub
- \+ *lemma* zpow_sub_one
- \+ *def* zpowers_hom
- \+ *lemma* zpowers_hom_apply
- \+ *lemma* zpowers_hom_symm_apply
- \+ *def* zpowers_mul_hom
- \+ *lemma* zpowers_mul_hom_apply
- \+ *lemma* zpowers_mul_hom_symm_apply

Modified src/algebra/group_power/order.lean
- \- *theorem* one_le_gpow
- \+ *theorem* one_le_zpow

Modified src/algebra/group_with_zero/power.lean
- \- *theorem* commute.fpow_fpow
- \- *theorem* commute.fpow_fpow_self
- \- *theorem* commute.fpow_left
- \- *theorem* commute.fpow_right
- \- *theorem* commute.fpow_self
- \- *lemma* commute.mul_fpow
- \+ *lemma* commute.mul_zpow₀
- \- *theorem* commute.self_fpow
- \+ *theorem* commute.self_zpow₀
- \+ *theorem* commute.zpow_left₀
- \+ *theorem* commute.zpow_right₀
- \+ *theorem* commute.zpow_self₀
- \+ *theorem* commute.zpow_zpow_self₀
- \+ *theorem* commute.zpow_zpow₀
- \- *theorem* div_fpow
- \+ *theorem* div_zpow₀
- \- *lemma* fpow_add'
- \- *lemma* fpow_add
- \- *lemma* fpow_add_one
- \- *theorem* fpow_bit0'
- \- *theorem* fpow_bit0
- \- *theorem* fpow_bit1'
- \- *theorem* fpow_bit1
- \- *lemma* fpow_eq_zero
- \- *theorem* fpow_mul'
- \- *theorem* fpow_mul
- \- *lemma* fpow_ne_zero
- \- *lemma* fpow_ne_zero_of_ne_zero
- \- *theorem* fpow_neg
- \- *theorem* fpow_neg_mul_fpow_self
- \- *theorem* fpow_neg_one
- \- *theorem* fpow_one_add
- \- *lemma* fpow_sub
- \- *lemma* fpow_sub_one
- \- *lemma* inv_fpow'
- \- *theorem* inv_fpow
- \+ *lemma* inv_zpow'
- \+ *theorem* inv_zpow₀
- \- *lemma* monoid_with_zero_hom.map_fpow
- \+ *lemma* monoid_with_zero_hom.map_zpow
- \- *lemma* mul_fpow
- \+ *lemma* mul_zpow₀
- \- *theorem* one_div_fpow
- \+ *theorem* one_div_zpow
- \- *theorem* one_fpow
- \+ *theorem* one_zpow₀
- \- *theorem* semiconj_by.fpow_right
- \+ *theorem* semiconj_by.zpow_right₀
- \- *lemma* units.coe_gpow₀
- \+ *lemma* units.coe_zpow₀
- \- *lemma* zero_fpow
- \+ *lemma* zero_zpow
- \+ *lemma* zpow_add'
- \+ *lemma* zpow_add_one₀
- \+ *lemma* zpow_add₀
- \+ *theorem* zpow_bit0'
- \+ *theorem* zpow_bit0₀
- \+ *theorem* zpow_bit1'
- \+ *theorem* zpow_bit1₀
- \+ *lemma* zpow_eq_zero
- \+ *theorem* zpow_mul₀'
- \+ *theorem* zpow_mul₀
- \+ *lemma* zpow_ne_zero
- \+ *lemma* zpow_ne_zero_of_ne_zero
- \+ *theorem* zpow_neg_mul_zpow_self
- \+ *theorem* zpow_neg_one₀
- \+ *theorem* zpow_neg₀
- \+ *theorem* zpow_one_add₀
- \+ *lemma* zpow_sub_one₀
- \+ *lemma* zpow_sub₀

Modified src/algebra/iterate_hom.lean
- \- *theorem* monoid_hom.iterate_map_gpow
- \+ *theorem* monoid_hom.iterate_map_zpow

Modified src/algebra/opposites.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/star/basic.lean
- \- *lemma* star_fpow
- \- *lemma* star_gpow
- \+ *lemma* star_zpow
- \+ *lemma* star_zpow₀

Modified src/analysis/asymptotics/specific_asymptotics.lean
- \- *lemma* tendsto_fpow_at_top_at_top
- \+ *lemma* tendsto_zpow_at_top_at_top

Modified src/analysis/asymptotics/superpolynomial_decay.lean
- \- *lemma* asymptotics.superpolynomial_decay_of_is_O_fpow_le
- \- *lemma* asymptotics.superpolynomial_decay_of_is_O_fpow_lt
- \+ *lemma* asymptotics.superpolynomial_decay_of_is_O_zpow_le
- \+ *lemma* asymptotics.superpolynomial_decay_of_is_O_zpow_lt

Modified src/analysis/calculus/deriv.lean
- \- *lemma* deriv_fpow'
- \- *lemma* deriv_fpow
- \- *lemma* deriv_within_fpow
- \+ *lemma* deriv_within_zpow
- \+ *lemma* deriv_zpow'
- \+ *lemma* deriv_zpow
- \- *lemma* differentiable_at_fpow
- \+ *lemma* differentiable_at_zpow
- \- *lemma* differentiable_on_fpow
- \+ *lemma* differentiable_on_zpow
- \- *lemma* differentiable_within_at_fpow
- \+ *lemma* differentiable_within_at_zpow
- \- *lemma* has_deriv_at_fpow
- \+ *lemma* has_deriv_at_zpow
- \- *theorem* has_deriv_within_at_fpow
- \+ *theorem* has_deriv_within_at_zpow
- \- *lemma* has_strict_deriv_at_fpow
- \+ *lemma* has_strict_deriv_at_zpow
- \- *lemma* iter_deriv_fpow'
- \- *lemma* iter_deriv_fpow
- \+ *lemma* iter_deriv_zpow'
- \+ *lemma* iter_deriv_zpow

Modified src/analysis/convex/specific_functions.lean
- \- *lemma* convex_on_fpow
- \+ *lemma* convex_on_zpow

Modified src/analysis/fourier.lean


Modified src/analysis/mean_inequalities.lean
- \- *theorem* real.fpow_arith_mean_le_arith_mean_fpow
- \+ *theorem* real.zpow_arith_mean_le_arith_mean_zpow

Modified src/analysis/normed_space/basic.lean
- \- *lemma* normed_field.nnnorm_fpow
- \+ *lemma* normed_field.nnnorm_zpow
- \- *lemma* normed_field.norm_fpow
- \+ *lemma* normed_field.norm_zpow

Modified src/analysis/special_functions/exp.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/specific_limits.lean
- \- *lemma* normed_field.continuous_at_fpow
- \+ *lemma* normed_field.continuous_at_zpow
- \- *lemma* normed_field.tendsto_norm_fpow_nhds_within_0_at_top
- \+ *lemma* normed_field.tendsto_norm_zpow_nhds_within_0_at_top

Modified src/category_theory/conj.lean
- \- *lemma* category_theory.iso.conj_Aut_gpow
- \+ *lemma* category_theory.iso.conj_Aut_zpow

Modified src/category_theory/endomorphism.lean


Modified src/data/complex/basic.lean
- \- *lemma* complex.I_fpow_bit0
- \- *lemma* complex.I_fpow_bit1
- \+ *lemma* complex.I_zpow_bit0
- \+ *lemma* complex.I_zpow_bit1
- \- *lemma* complex.of_real_fpow
- \+ *lemma* complex.of_real_zpow

Modified src/data/complex/is_R_or_C.lean
- \- *lemma* is_R_or_C.of_real_fpow
- \+ *lemma* is_R_or_C.of_real_zpow

Modified src/data/equiv/mul_add_aut.lean


Modified src/data/equiv/ring_aut.lean


Modified src/data/int/gcd.lean


Modified src/data/real/irrational.lean
- \- *theorem* irrational.of_fpow
- \+ *theorem* irrational.of_zpow

Modified src/deprecated/subfield.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean
- \- *lemma* circle_deg1_lift.translate_gpow
- \+ *lemma* circle_deg1_lift.translate_zpow
- \- *lemma* circle_deg1_lift.translation_number_gpow
- \+ *lemma* circle_deg1_lift.translation_number_zpow

Modified src/field_theory/finite/basic.lean


Modified src/field_theory/intermediate_field.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/group_action/group.lean
- \- *lemma* smul_gpow
- \+ *lemma* smul_zpow

Modified src/group_theory/order_of_element.lean
- \- *lemma* exists_gpow_eq_one
- \+ *lemma* exists_zpow_eq_one
- \- *lemma* fin_equiv_gpowers_apply
- \- *lemma* fin_equiv_gpowers_symm_apply
- \+ *lemma* fin_equiv_zpowers_apply
- \+ *lemma* fin_equiv_zpowers_symm_apply
- \- *lemma* gpow_eq_mod_card
- \- *lemma* gpow_eq_mod_order_of
- \- *lemma* gpowers_equiv_gpowers_apply
- \- *lemma* mem_gpowers_iff_mem_range_order_of
- \- *lemma* mem_powers_iff_mem_gpowers
- \+ *lemma* mem_powers_iff_mem_zpowers
- \+ *lemma* mem_zpowers_iff_mem_range_order_of
- \- *lemma* order_eq_card_gpowers
- \+ *lemma* order_eq_card_zpowers
- \- *lemma* order_of_dvd_iff_gpow_eq_one
- \+ *lemma* order_of_dvd_iff_zpow_eq_one
- \- *lemma* powers_eq_gpowers
- \+ *lemma* powers_eq_zpowers
- \+ *lemma* zpow_eq_mod_card
- \+ *lemma* zpow_eq_mod_order_of
- \+ *lemma* zpowers_equiv_zpowers_apply

Modified src/group_theory/perm/basic.lean
- \- *lemma* equiv.perm.gpow_apply_comm
- \+ *lemma* equiv.perm.zpow_apply_comm

Modified src/group_theory/perm/concrete_cycle.lean


Modified src/group_theory/perm/cycles.lean
- \- *lemma* equiv.perm.cycle_of_apply_apply_gpow_self
- \+ *lemma* equiv.perm.cycle_of_apply_apply_zpow_self
- \- *lemma* equiv.perm.cycle_of_gpow_apply_self
- \- *lemma* equiv.perm.cycle_of_self_apply_gpow
- \+ *lemma* equiv.perm.cycle_of_self_apply_zpow
- \+ *lemma* equiv.perm.cycle_of_zpow_apply_self
- \- *lemma* equiv.perm.is_cycle.exists_gpow_eq
- \+ *lemma* equiv.perm.is_cycle.exists_zpow_eq
- \- *lemma* equiv.perm.is_cycle.gpowers_equiv_support_apply
- \- *lemma* equiv.perm.is_cycle.gpowers_equiv_support_symm_apply
- \+ *lemma* equiv.perm.is_cycle.zpowers_equiv_support_apply
- \+ *lemma* equiv.perm.is_cycle.zpowers_equiv_support_symm_apply
- \- *lemma* equiv.perm.is_cycle_of_is_cycle_gpow
- \+ *lemma* equiv.perm.is_cycle_of_is_cycle_zpow
- \- *lemma* equiv.perm.same_cycle_gpow_left_iff
- \+ *lemma* equiv.perm.same_cycle_zpow_left_iff

Modified src/group_theory/perm/fin.lean


Modified src/group_theory/perm/list.lean
- \- *lemma* list.form_perm_gpow_apply_mem_imp_mem
- \+ *lemma* list.form_perm_zpow_apply_mem_imp_mem

Modified src/group_theory/perm/support.lean
- \- *lemma* equiv.perm.disjoint.gpow_disjoint_gpow
- \+ *lemma* equiv.perm.disjoint.zpow_disjoint_zpow
- \- *lemma* equiv.perm.gpow_apply_eq_of_apply_apply_eq_self
- \- *lemma* equiv.perm.gpow_apply_eq_self_of_apply_eq_self
- \- *lemma* equiv.perm.gpow_apply_mem_support
- \- *lemma* equiv.perm.set_support_gpow_subset
- \+ *lemma* equiv.perm.set_support_zpow_subset
- \- *lemma* equiv.perm.support_gpow_le
- \+ *lemma* equiv.perm.support_zpow_le
- \+ *lemma* equiv.perm.zpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* equiv.perm.zpow_apply_eq_self_of_apply_eq_self
- \+ *lemma* equiv.perm.zpow_apply_mem_support

Modified src/group_theory/quotient_group.lean
- \- *lemma* quotient_group.coe_gpow
- \+ *lemma* quotient_group.coe_zpow

Modified src/group_theory/specific_groups/cyclic.lean
- \+/\- *lemma* is_cyclic.image_range_card
- \+/\- *lemma* is_cyclic.image_range_order_of
- \- *lemma* order_of_eq_card_of_forall_mem_gpowers
- \+ *lemma* order_of_eq_card_of_forall_mem_zpowers

Modified src/group_theory/subgroup/basic.lean
- \- *lemma* of_add_image_gmultiples_eq_gpowers_of_add
- \+ *lemma* of_add_image_gmultiples_eq_zpowers_of_add
- \- *lemma* of_mul_image_gpowers_eq_gmultiples_of_mul
- \+ *lemma* of_mul_image_zpowers_eq_gmultiples_of_mul
- \- *lemma* subgroup.coe_gpow
- \+ *lemma* subgroup.coe_zpow
- \- *lemma* subgroup.exists_gpowers
- \- *lemma* subgroup.exists_mem_gpowers
- \+ *lemma* subgroup.exists_mem_zpowers
- \+ *lemma* subgroup.exists_zpowers
- \- *lemma* subgroup.forall_gpowers
- \- *lemma* subgroup.forall_mem_gpowers
- \+ *lemma* subgroup.forall_mem_zpowers
- \+ *lemma* subgroup.forall_zpowers
- \- *lemma* subgroup.gpow_mem
- \- *def* subgroup.gpowers
- \- *lemma* subgroup.gpowers_eq_closure
- \- *lemma* subgroup.gpowers_subset
- \- *lemma* subgroup.mem_gpowers
- \- *lemma* subgroup.mem_gpowers_iff
- \+ *lemma* subgroup.mem_zpowers
- \+ *lemma* subgroup.mem_zpowers_iff
- \- *lemma* subgroup.range_gpowers_hom
- \+ *lemma* subgroup.range_zpowers_hom
- \- *lemma* subgroup.saturated_iff_gpow
- \+ *lemma* subgroup.saturated_iff_zpow
- \+ *lemma* subgroup.zpow_mem
- \+ *def* subgroup.zpowers
- \+ *lemma* subgroup.zpowers_eq_closure
- \+ *lemma* subgroup.zpowers_subset

Modified src/group_theory/sylow.lean


Renamed src/linear_algebra/matrix/fpow.lean to src/linear_algebra/matrix/zpow.lean
- \- *lemma* is_unit.det_fpow
- \+ *lemma* is_unit.det_zpow
- \- *theorem* matrix.commute.fpow_fpow
- \- *theorem* matrix.commute.fpow_fpow_self
- \- *theorem* matrix.commute.fpow_left
- \- *theorem* matrix.commute.fpow_right
- \- *theorem* matrix.commute.fpow_self
- \- *lemma* matrix.commute.mul_fpow
- \+ *lemma* matrix.commute.mul_zpow
- \- *theorem* matrix.commute.self_fpow
- \+ *theorem* matrix.commute.self_zpow
- \+ *theorem* matrix.commute.zpow_left
- \+ *theorem* matrix.commute.zpow_right
- \+ *theorem* matrix.commute.zpow_self
- \+ *theorem* matrix.commute.zpow_zpow
- \+ *theorem* matrix.commute.zpow_zpow_self
- \- *lemma* matrix.fpow_add
- \- *lemma* matrix.fpow_add_of_nonneg
- \- *lemma* matrix.fpow_add_of_nonpos
- \- *lemma* matrix.fpow_add_one
- \- *lemma* matrix.fpow_add_one_of_ne_neg_one
- \- *theorem* matrix.fpow_bit0'
- \- *theorem* matrix.fpow_bit0
- \- *theorem* matrix.fpow_bit1'
- \- *theorem* matrix.fpow_bit1
- \- *theorem* matrix.fpow_coe_nat
- \- *theorem* matrix.fpow_mul'
- \- *theorem* matrix.fpow_mul
- \- *lemma* matrix.fpow_ne_zero_of_is_unit_det
- \- *theorem* matrix.fpow_neg
- \- *theorem* matrix.fpow_neg_coe_nat
- \- *theorem* matrix.fpow_neg_mul_fpow_self
- \- *lemma* matrix.fpow_neg_one
- \- *theorem* matrix.fpow_one_add
- \- *lemma* matrix.fpow_sub
- \- *lemma* matrix.fpow_sub_one
- \- *lemma* matrix.inv_fpow'
- \- *theorem* matrix.inv_fpow
- \+ *lemma* matrix.inv_zpow'
- \+ *theorem* matrix.inv_zpow
- \- *lemma* matrix.is_unit_det_fpow_iff
- \+ *lemma* matrix.is_unit_det_zpow_iff
- \- *theorem* matrix.one_div_fpow
- \+ *theorem* matrix.one_div_zpow
- \- *theorem* matrix.one_fpow
- \+ *theorem* matrix.one_zpow
- \- *theorem* matrix.semiconj_by.fpow_right
- \+ *theorem* matrix.semiconj_by.zpow_right
- \- *lemma* matrix.units.coe_fpow
- \+ *lemma* matrix.units.coe_zpow
- \- *lemma* matrix.zero_fpow
- \- *lemma* matrix.zero_fpow_eq
- \+ *lemma* matrix.zero_zpow
- \+ *lemma* matrix.zero_zpow_eq
- \+ *lemma* matrix.zpow_add
- \+ *lemma* matrix.zpow_add_of_nonneg
- \+ *lemma* matrix.zpow_add_of_nonpos
- \+ *lemma* matrix.zpow_add_one
- \+ *lemma* matrix.zpow_add_one_of_ne_neg_one
- \+ *theorem* matrix.zpow_bit0'
- \+ *theorem* matrix.zpow_bit0
- \+ *theorem* matrix.zpow_bit1'
- \+ *theorem* matrix.zpow_bit1
- \+ *theorem* matrix.zpow_coe_nat
- \+ *theorem* matrix.zpow_mul'
- \+ *theorem* matrix.zpow_mul
- \+ *lemma* matrix.zpow_ne_zero_of_is_unit_det
- \+ *theorem* matrix.zpow_neg
- \+ *theorem* matrix.zpow_neg_coe_nat
- \+ *theorem* matrix.zpow_neg_mul_zpow_self
- \+ *lemma* matrix.zpow_neg_one
- \+ *theorem* matrix.zpow_one_add
- \+ *lemma* matrix.zpow_sub
- \+ *lemma* matrix.zpow_sub_one

Modified src/measure_theory/group/arithmetic.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/roots_of_unity.lean
- \- *lemma* is_primitive_root.fpow_eq_one
- \- *lemma* is_primitive_root.fpow_eq_one_iff_dvd
- \- *lemma* is_primitive_root.fpow_of_gcd_eq_one
- \- *lemma* is_primitive_root.gpow_eq_one
- \- *lemma* is_primitive_root.gpow_eq_one_iff_dvd
- \- *lemma* is_primitive_root.gpow_of_gcd_eq_one
- \- *lemma* is_primitive_root.gpowers_eq
- \- *def* is_primitive_root.zmod_equiv_gpowers
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_apply_coe_int
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_apply_coe_nat
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_gpow'
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_gpow
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_pow'
- \- *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_pow
- \+ *def* is_primitive_root.zmod_equiv_zpowers
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_apply_coe_int
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_apply_coe_nat
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_symm_apply_pow'
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_symm_apply_pow
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_symm_apply_zpow'
- \+ *lemma* is_primitive_root.zmod_equiv_zpowers_symm_apply_zpow
- \+ *lemma* is_primitive_root.zpow_eq_one
- \+ *lemma* is_primitive_root.zpow_eq_one_iff_dvd
- \+ *lemma* is_primitive_root.zpow_eq_one_iff_dvd₀
- \+ *lemma* is_primitive_root.zpow_eq_one₀
- \+ *lemma* is_primitive_root.zpow_of_gcd_eq_one
- \+ *lemma* is_primitive_root.zpow_of_gcd_eq_one₀
- \+ *lemma* is_primitive_root.zpowers_eq

Modified src/tactic/group.lean
- \- *lemma* tactic.group.gpow_trick
- \- *lemma* tactic.group.gpow_trick_one'
- \- *lemma* tactic.group.gpow_trick_one
- \- *lemma* tactic.group.gpow_trick_sub
- \+ *lemma* tactic.group.zpow_trick
- \+ *lemma* tactic.group.zpow_trick_one'
- \+ *lemma* tactic.group.zpow_trick_one
- \+ *lemma* tactic.group.zpow_trick_sub

Modified src/topology/algebra/group_with_zero.lean
- \- *lemma* continuous.fpow
- \+ *lemma* continuous.zpow
- \- *lemma* continuous_at.fpow
- \+ *lemma* continuous_at.zpow
- \- *lemma* continuous_at_fpow
- \+ *lemma* continuous_at_zpow
- \- *lemma* continuous_on.fpow
- \+ *lemma* continuous_on.zpow
- \- *lemma* continuous_on_fpow
- \+ *lemma* continuous_on_zpow
- \- *lemma* continuous_within_at.fpow
- \+ *lemma* continuous_within_at.zpow
- \- *lemma* filter.tendsto.fpow
- \+ *lemma* filter.tendsto.zpow

Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* tendsto_const_mul_fpow_at_top_zero
- \- *lemma* tendsto_const_mul_fpow_at_top_zero_iff
- \+ *lemma* tendsto_const_mul_zpow_at_top_zero
- \+ *lemma* tendsto_const_mul_zpow_at_top_zero_iff
- \- *lemma* tendsto_fpow_at_top_zero
- \+ *lemma* tendsto_zpow_at_top_zero

Modified test/refine_struct.lean




## [2021-10-27 17:47:26](https://github.com/leanprover-community/mathlib/commit/9e4609b)
chore(data/fintype/card): add `fin.prod_univ_{one,two}` ([#9987](https://github.com/leanprover-community/mathlib/pull/9987))
Sometimes Lean fails to simplify `(default : fin 1)` to `0` and
`0.succ` to `1` in complex expressions. These lemmas explicitly use
`f 0` and `f 1` in the output.
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *theorem* fin.prod_univ_one
- \+ *theorem* fin.prod_univ_two



## [2021-10-27 17:47:25](https://github.com/leanprover-community/mathlib/commit/29079ba)
feat(tactic/lint): linter improvements ([#9901](https://github.com/leanprover-community/mathlib/pull/9901))
* Make the linter framework easier to use on projects outside mathlib with the new `lint_project` (replacing `lint_mathlib`). Also replace `lint_mathlib_decls` by `lint_project_decls`.
* Make most declarations in the frontend not-private (I want to use them in other projects)
* The unused argument linter does not report declarations that contain `sorry`. It will still report declarations that use other declarations that contain sorry. I did not add a test for this, since it's hard to do that while keeping the test suite silent (but I did test locally).
* Some minor changes in the test suite (not important, but they cannot hurt).
#### Estimated changes
Modified scripts/lint_mathlib.lean


Modified src/tactic/core.lean


Modified src/tactic/lint/frontend.lean


Modified src/tactic/lint/misc.lean


Added src/tactic/project_dir.lean
- \+ *lemma* mathlib_dir_locator

Modified test/lint.lean




## [2021-10-27 15:13:53](https://github.com/leanprover-community/mathlib/commit/25718c2)
feat(data/nat/basic): Add two lemmas two nat/basic which are necessary for the count PR ([#10001](https://github.com/leanprover-community/mathlib/pull/10001))
Add two lemmas proved by refl to data/nat/basic. They are needed for the count PR, and are changing a file low enogh in the import hierarchy to be a separate PR.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.sub_succ'
- \+ *lemma* nat.subtype.coe_bot



## [2021-10-27 15:13:51](https://github.com/leanprover-community/mathlib/commit/4e29dc7)
chore(topology/algebra/module): add `continuous_linear_equiv.arrow_congr_equiv` ([#9982](https://github.com/leanprover-community/mathlib/pull/9982))
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_equiv.arrow_congr_equiv



## [2021-10-27 15:13:50](https://github.com/leanprover-community/mathlib/commit/a3f4a02)
chore(analysis/normed_space/is_R_or_C + data/complex/is_R_or_C): make some proof steps standalone lemmas ([#9933](https://github.com/leanprover-community/mathlib/pull/9933))
Separate some proof steps from `linear_map.bound_of_sphere_bound` as standalone lemmas to golf them a little bit.
#### Estimated changes
Modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_coe_norm

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_of_nonneg



## [2021-10-27 15:13:49](https://github.com/leanprover-community/mathlib/commit/d7c689d)
feat(algebraic_geometry/prime_spectrum): Closed points in prime spectrum ([#9861](https://github.com/leanprover-community/mathlib/pull/9861))
This PR adds lemmas about the correspondence between closed points in `prime_spectrum R` and maximal ideals of `R`.
In order to import and talk about integral maps I had to move some lemmas from `noetherian.lean` to `prime_spectrum.lean` to prevent cyclic import dependencies.
#### Estimated changes
Renamed src/algebraic_geometry/prime_spectrum.lean to src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* prime_spectrum.comap_injective_of_surjective
- \+ *lemma* prime_spectrum.comap_singleton_is_closed_of_is_integral
- \+ *lemma* prime_spectrum.comap_singleton_is_closed_of_surjective
- \+ *lemma* prime_spectrum.is_closed_singleton_iff_is_maximal
- \+ *lemma* prime_spectrum.t1_space_iff_is_field

Renamed src/algebraic_geometry/is_open_comap_C.lean to src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean


Added src/algebraic_geometry/prime_spectrum/noetherian.lean
- \+ *lemma* prime_spectrum.exists_prime_spectrum_prod_le
- \+ *lemma* prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain

Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/noetherian.lean
- \- *lemma* exists_prime_spectrum_prod_le
- \- *lemma* exists_prime_spectrum_prod_le_and_ne_bot_of_domain

Modified src/ring_theory/nullstellensatz.lean




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
Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/locally_ringed_space.lean
- \+/\- *def* algebraic_geometry.LocallyRingedSpace.restrict

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_c
- \+ *lemma* algebraic_geometry.PresheafedSpace.hext
- \+ *lemma* algebraic_geometry.PresheafedSpace.of_restrict_top_c
- \+ *lemma* algebraic_geometry.PresheafedSpace.restrict_top_presheaf

Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/stalks.lean
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_hom_eq_germ
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_germ

Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *lemma* algebraic_geometry.structure_sheaf.to_open_comp_comap

Modified src/category_theory/whiskering.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* topological_space.opens.inclusion_top_functor
- \+ *def* topological_space.opens.inclusion_top_iso
- \+ *lemma* topological_space.opens.map_comp_eq
- \+ *lemma* topological_space.opens.map_eq
- \+ *lemma* topological_space.opens.map_id_eq
- \+ *lemma* topological_space.opens.map_supr

Added src/topology/sheaves/functors.lean
- \+ *lemma* Top.presheaf.sheaf_condition_pairwise_intersections.map_cocone
- \+ *lemma* Top.presheaf.sheaf_condition_pairwise_intersections.map_diagram
- \+ *theorem* Top.presheaf.sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf
- \+ *def* Top.sheaf.pushforward
- \+ *theorem* Top.sheaf.pushforward_sheaf_of_sheaf

Modified src/topology/sheaves/presheaf.lean
- \+ *lemma* Top.presheaf.id_pushforward
- \+ *lemma* Top.presheaf.pushforward.comp_eq
- \+ *lemma* Top.presheaf.pushforward.id_eq
- \+ *def* Top.presheaf.pushforward
- \+ *lemma* Top.presheaf.pushforward_eq'



## [2021-10-27 04:25:01](https://github.com/leanprover-community/mathlib/commit/996ece5)
feat(tactic/suggest): add a flag to disable "Try this" lines ([#9820](https://github.com/leanprover-community/mathlib/pull/9820))
#### Estimated changes
Modified src/tactic/suggest.lean




## [2021-10-27 02:40:26](https://github.com/leanprover-community/mathlib/commit/62edbe5)
chore(scripts): update nolints.txt ([#9994](https://github.com/leanprover-community/mathlib/pull/9994))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-10-26 22:41:21](https://github.com/leanprover-community/mathlib/commit/b592589)
refactor(order/boolean_algebra): factor out pi.sdiff and pi.compl ([#9955](https://github.com/leanprover-community/mathlib/pull/9955))
Provide definitional lemmas about sdiff and compl on pi types.
This allows usage later on even without a whole `boolean_algebra` instance.
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* pi.compl_apply
- \+ *lemma* pi.compl_def
- \+ *lemma* pi.sdiff_apply
- \+ *lemma* pi.sdiff_def



## [2021-10-26 22:41:20](https://github.com/leanprover-community/mathlib/commit/120cf5b)
doc(topology) add a library note about continuity lemmas ([#9954](https://github.com/leanprover-community/mathlib/pull/9954))
* This is a note with some tips how to formulate a continuity (or measurability, differentiability, ...) lemma.
* I wanted to write this up after formulating `continuous.strans` in many "wrong" ways before discovering the "right" way.
* I think many lemmas are not following this principle, and could be improved in generality and/or convenience by following this advice.
* Based on experience from the sphere eversion project.
* The note mentions a lemma that will be added in [#9959](https://github.com/leanprover-community/mathlib/pull/9959), but I don't think we necessarily have to wait for that PR.
#### Estimated changes
Modified src/topology/basic.lean




## [2021-10-26 21:02:25](https://github.com/leanprover-community/mathlib/commit/36a2015)
feat(topology/[separation, dense_embedding]): a function to a T1 space which has a limit at x is continuous at x ([#9934](https://github.com/leanprover-community/mathlib/pull/9934))
We prove that, for a function `f` with values in a T1 space, knowing that `f` admits *any* limit at `x` suffices to prove that `f` is continuous at `x`.
We then use it to give a variant of `dense_inducing.extend_eq` with the same assumption required for continuity of the extension, which makes using both `extend_eq` and `continuous_extend` easier, and also brings us closer to Bourbaki who makes no explicit continuity assumption on the function to extend.
#### Estimated changes
Modified src/topology/algebra/uniform_field.lean


Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_inducing.extend_eq'
- \+ *lemma* dense_inducing.extend_eq_at'
- \+/\- *lemma* dense_inducing.extend_eq_at

Modified src/topology/separation.lean
- \+ *lemma* continuous_at_of_tendsto_nhds
- \+ *lemma* eq_of_tendsto_nhds

Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-10-26 20:05:59](https://github.com/leanprover-community/mathlib/commit/92e9078)
fix(linear_algebra/matrix/determinant): remove coercions ([#9975](https://github.com/leanprover-community/mathlib/pull/9975))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean




## [2021-10-26 20:05:58](https://github.com/leanprover-community/mathlib/commit/2a32c70)
refactor(linear_algebra/matrix/nonsingular_inverse): split out files for adjugate and nondegenerate ([#9974](https://github.com/leanprover-community/mathlib/pull/9974))
This breaks the file roughly in two, and rescues lost lemmas that ended up in the wrong sections of the file.
The module docstrings have been tweaked a little, but all the lemmas have just been moved around.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean


Added src/linear_algebra/matrix/adjugate.lean
- \+ *def* matrix.adjugate
- \+ *lemma* matrix.adjugate_apply
- \+ *lemma* matrix.adjugate_conj_transpose
- \+ *lemma* matrix.adjugate_def
- \+ *lemma* matrix.adjugate_eq_one_of_card_eq_one
- \+ *lemma* matrix.adjugate_fin_one
- \+ *lemma* matrix.adjugate_fin_two'
- \+ *lemma* matrix.adjugate_fin_two
- \+ *lemma* matrix.adjugate_fin_zero
- \+ *lemma* matrix.adjugate_mul
- \+ *lemma* matrix.adjugate_mul_distrib
- \+ *lemma* matrix.adjugate_mul_distrib_aux
- \+ *lemma* matrix.adjugate_one
- \+ *lemma* matrix.adjugate_pow
- \+ *lemma* matrix.adjugate_smul
- \+ *lemma* matrix.adjugate_subsingleton
- \+ *lemma* matrix.adjugate_transpose
- \+ *lemma* matrix.adjugate_zero
- \+ *def* matrix.cramer
- \+ *lemma* matrix.cramer_apply
- \+ *lemma* matrix.cramer_eq_adjugate_mul_vec
- \+ *lemma* matrix.cramer_is_linear
- \+ *def* matrix.cramer_map
- \+ *lemma* matrix.cramer_map_is_linear
- \+ *lemma* matrix.cramer_one
- \+ *lemma* matrix.cramer_row_self
- \+ *lemma* matrix.cramer_smul
- \+ *lemma* matrix.cramer_subsingleton_apply
- \+ *lemma* matrix.cramer_transpose_row_self
- \+ *lemma* matrix.cramer_zero
- \+ *lemma* matrix.det_adjugate_eq_one
- \+ *lemma* matrix.det_adjugate_of_cancel
- \+ *lemma* matrix.det_adjugate_of_is_unit
- \+ *lemma* matrix.is_regular_of_is_left_regular_det
- \+ *lemma* matrix.mul_adjugate
- \+ *lemma* matrix.mul_adjugate_apply
- \+ *lemma* matrix.mul_vec_cramer
- \+ *lemma* matrix.sum_cramer
- \+ *lemma* matrix.sum_cramer_apply
- \+ *lemma* ring_hom.map_adjugate

Added src/linear_algebra/matrix/nondegenerate.lean
- \+ *theorem* matrix.eq_zero_of_mul_vec_eq_zero
- \+ *theorem* matrix.eq_zero_of_vec_mul_eq_zero
- \+ *lemma* matrix.nondegenerate.eq_zero_of_ortho
- \+ *lemma* matrix.nondegenerate.exists_not_ortho_of_ne_zero
- \+ *def* matrix.nondegenerate
- \+ *theorem* matrix.nondegenerate_of_det_ne_zero

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \- *def* matrix.adjugate
- \- *lemma* matrix.adjugate_apply
- \- *lemma* matrix.adjugate_conj_transpose
- \- *lemma* matrix.adjugate_def
- \- *lemma* matrix.adjugate_eq_one_of_card_eq_one
- \- *lemma* matrix.adjugate_fin_one
- \- *lemma* matrix.adjugate_fin_two'
- \- *lemma* matrix.adjugate_fin_two
- \- *lemma* matrix.adjugate_fin_zero
- \- *lemma* matrix.adjugate_mul
- \- *lemma* matrix.adjugate_mul_distrib
- \- *lemma* matrix.adjugate_mul_distrib_aux
- \- *lemma* matrix.adjugate_one
- \- *lemma* matrix.adjugate_pow
- \- *lemma* matrix.adjugate_smul
- \- *lemma* matrix.adjugate_subsingleton
- \- *lemma* matrix.adjugate_transpose
- \- *lemma* matrix.adjugate_zero
- \- *def* matrix.cramer
- \- *lemma* matrix.cramer_apply
- \- *lemma* matrix.cramer_eq_adjugate_mul_vec
- \- *lemma* matrix.cramer_is_linear
- \- *def* matrix.cramer_map
- \- *lemma* matrix.cramer_map_is_linear
- \- *lemma* matrix.cramer_one
- \- *lemma* matrix.cramer_row_self
- \- *lemma* matrix.cramer_smul
- \- *lemma* matrix.cramer_subsingleton_apply
- \- *lemma* matrix.cramer_transpose_row_self
- \- *lemma* matrix.cramer_zero
- \- *lemma* matrix.det_adjugate_eq_one
- \- *lemma* matrix.det_adjugate_of_cancel
- \- *lemma* matrix.det_adjugate_of_is_unit
- \- *theorem* matrix.eq_zero_of_mul_vec_eq_zero
- \- *theorem* matrix.eq_zero_of_vec_mul_eq_zero
- \- *lemma* matrix.is_regular_of_is_left_regular_det
- \- *lemma* matrix.mul_adjugate
- \- *lemma* matrix.mul_adjugate_apply
- \- *lemma* matrix.mul_vec_cramer
- \- *lemma* matrix.nondegenerate.eq_zero_of_ortho
- \- *lemma* matrix.nondegenerate.exists_not_ortho_of_ne_zero
- \- *def* matrix.nondegenerate
- \- *theorem* matrix.nondegenerate_of_det_ne_zero
- \- *lemma* matrix.sum_cramer
- \- *lemma* matrix.sum_cramer_apply
- \- *lemma* ring_hom.map_adjugate

Modified src/linear_algebra/matrix/to_linear_equiv.lean




## [2021-10-26 17:54:26](https://github.com/leanprover-community/mathlib/commit/ce164e2)
chore(data/{finset,multiset}/locally_finite): rename from `.interval` ([#9980](https://github.com/leanprover-community/mathlib/pull/9980))
The pattern is `data.stuff.interval` for files about `locally_finite_order stuff` and... `finset α` and `multiset α` are locally finite orders. This thus makes space for this theory.
#### Estimated changes
Modified src/data/finset/default.lean


Renamed src/data/finset/interval.lean to src/data/finset/locally_finite.lean


Renamed src/data/multiset/interval.lean to src/data/multiset/locally_finite.lean


Modified src/data/nat/interval.lean




## [2021-10-26 17:54:24](https://github.com/leanprover-community/mathlib/commit/3aa5749)
feat(group_theory/subgroup/basic): Define characteristic subgroups ([#9921](https://github.com/leanprover-community/mathlib/pull/9921))
This PR defines characteristic subgroups and builds the basic API.
Getting `@[to_additive]` to work correctly was a bit tricky, so I mostly just copied the setup for `subgroup.normal`.
#### Estimated changes
Modified src/data/equiv/mul_add_aut.lean
- \+/\- *lemma* add_aut.conj_apply

Modified src/group_theory/nilpotent.lean


Modified src/group_theory/solvable.lean


Modified src/group_theory/subgroup/basic.lean
- \+ *structure* add_subgroup.characteristic
- \+ *structure* subgroup.characteristic
- \+ *lemma* subgroup.characteristic_iff_comap_eq
- \+ *lemma* subgroup.characteristic_iff_comap_le
- \+ *lemma* subgroup.characteristic_iff_le_comap
- \+ *lemma* subgroup.characteristic_iff_le_map
- \+ *lemma* subgroup.characteristic_iff_map_eq
- \+ *lemma* subgroup.characteristic_iff_map_le



## [2021-10-26 16:22:50](https://github.com/leanprover-community/mathlib/commit/50c6094)
feat(topology/uniform_space/basic): add lemma `comp_open_symm_mem_uniformity_sets` ([#9981](https://github.com/leanprover-community/mathlib/pull/9981))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* comp_open_symm_mem_uniformity_sets



## [2021-10-26 12:23:43](https://github.com/leanprover-community/mathlib/commit/d2b1221)
feat(algebra/order/group|order/filter): add two lemmas ([#9956](https://github.com/leanprover-community/mathlib/pull/9956))
* Also open `function` namespace in `order.filter.basic`
* From the sphere eversion project
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* le_div_self_iff

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_map
- \+/\- *lemma* filter.image_mem_map_iff
- \+/\- *theorem* filter.map_comap_of_surjective
- \+/\- *lemma* filter.map_inf
- \+/\- *lemma* filter.map_inj
- \+/\- *lemma* filter.mem_comap_iff
- \+/\- *lemma* filter.pure_injective
- \+ *lemma* function.surjective.filter_map_top



## [2021-10-26 09:49:59](https://github.com/leanprover-community/mathlib/commit/41df5b3)
docs(data/sigma/basic): Add module docstring ([#9908](https://github.com/leanprover-community/mathlib/pull/9908))
#### Estimated changes
Modified src/data/sigma/basic.lean




## [2021-10-26 09:09:15](https://github.com/leanprover-community/mathlib/commit/6b47ccb)
feat(group_theory/p_group): Center of a p-group is nontrivial ([#9973](https://github.com/leanprover-community/mathlib/pull/9973))
The center of a p-group is nontrivial, stated in two different ways.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.bot_lt_center
- \+ *lemma* is_p_group.center_nontrivial



## [2021-10-26 07:25:48](https://github.com/leanprover-community/mathlib/commit/f229c83)
chore(*): move 2 lemmas to reorder imports ([#9969](https://github.com/leanprover-community/mathlib/pull/9969))
I want to use `measure_theory.measure_preserving` in various files, including `measure_theory.integral.lebesgue`. The file about measure preserving map had two lemmas about product measures. I move them to `measure_theory.constructions.prod`. I also golfed (and made it more readable at the same time!) the proof of `measure_theory.measure.prod_prod_le` using `to_measurable_set`.
#### Estimated changes
Modified src/dynamics/ergodic/conservative.lean


Modified src/dynamics/ergodic/measure_preserving.lean
- \- *lemma* measure_theory.measure_preserving.prod
- \- *lemma* measure_theory.measure_preserving.skew_product

Modified src/measure_theory/constructions/prod.lean
- \+ *lemma* measure_theory.measure_preserving.skew_product



## [2021-10-26 07:25:47](https://github.com/leanprover-community/mathlib/commit/367d71e)
chore(order/iterate): review, add docs ([#9965](https://github.com/leanprover-community/mathlib/pull/9965))
* reorder sections;
* add section docs;
* use inequalities between functions in a few statements;
* add a few lemmas about `strict_mono` functions.
#### Estimated changes
Modified src/order/iterate.lean
- \+ *lemma* function.antitone_iterate_of_le_id
- \+/\- *lemma* function.id_le_iterate_of_id_le
- \+/\- *lemma* function.iterate_le_id_of_le_id
- \- *lemma* function.iterate_le_iterate_of_id_le
- \- *lemma* function.iterate_le_iterate_of_le_id
- \+ *lemma* function.monotone_iterate_of_id_le
- \+ *lemma* monotone.antitone_iterate_of_map_le
- \+/\- *lemma* monotone.iterate_comp_le_of_le
- \- *lemma* monotone.iterate_ge_of_ge
- \+/\- *lemma* monotone.iterate_le_of_le
- \+/\- *lemma* monotone.le_iterate_comp_of_le
- \+ *lemma* monotone.le_iterate_of_le
- \+ *lemma* monotone.monotone_iterate_of_le_map
- \+ *lemma* strict_mono.strict_anti_iterate_of_map_lt
- \+ *lemma* strict_mono.strict_mono_iterate_of_lt_map



## [2021-10-26 07:25:45](https://github.com/leanprover-community/mathlib/commit/717de02)
refactor(linear_algebra/free_module/pid): move lemmas ([#9962](https://github.com/leanprover-community/mathlib/pull/9962))
`linear_algebra/free_module/pid` contains several results not directly related to PID. We move them in more appropriate files.
Except for small golfing and easy generalization, the statements and the proofs are untouched.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.ne_zero_of_ortho
- \+ *lemma* submodule.not_mem_of_ortho

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.mem_submodule_image
- \+ *lemma* linear_map.mem_submodule_image_of_le
- \+ *def* linear_map.submodule_image
- \+ *lemma* linear_map.submodule_image_apply_of_le

Modified src/linear_algebra/basis.lean
- \+ *lemma* eq_bot_of_rank_eq_zero
- \+ *def* submodule.induction_on_rank_aux

Modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.card_le_card_of_le
- \+ *lemma* basis.card_le_card_of_linear_independent
- \+ *lemma* basis.card_le_card_of_linear_independent_aux
- \+ *lemma* basis.card_le_card_of_submodule
- \+ *lemma* ideal.rank_eq
- \+ *def* submodule.induction_on_rank

Modified src/linear_algebra/free_module/pid.lean
- \- *lemma* basis.card_le_card_of_le
- \- *lemma* basis.card_le_card_of_linear_independent
- \- *lemma* basis.card_le_card_of_linear_independent_aux
- \- *lemma* basis.card_le_card_of_submodule
- \- *lemma* eq_bot_of_rank_eq_zero
- \- *lemma* generator_map_dvd_of_mem
- \- *lemma* generator_submodule_image_dvd_of_mem
- \- *lemma* ideal.rank_eq
- \- *lemma* linear_map.mem_submodule_image
- \- *lemma* linear_map.mem_submodule_image_of_le
- \- *def* linear_map.submodule_image
- \- *lemma* linear_map.submodule_image_apply_of_le
- \- *lemma* ne_zero_of_ortho
- \- *lemma* not_mem_of_ortho
- \- *def* submodule.induction_on_rank
- \- *def* submodule.induction_on_rank_aux

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* submodule.is_principal.generator_map_dvd_of_mem
- \+ *lemma* submodule.is_principal.generator_submodule_image_dvd_of_mem



## [2021-10-26 05:22:54](https://github.com/leanprover-community/mathlib/commit/5227f53)
chore(data/equiv/encodable): a `[unique]` type is encodable ([#9970](https://github.com/leanprover-community/mathlib/pull/9970))
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean


Modified src/data/equiv/encodable/small.lean




## [2021-10-26 02:28:08](https://github.com/leanprover-community/mathlib/commit/a8e6442)
chore(scripts): update nolints.txt ([#9971](https://github.com/leanprover-community/mathlib/pull/9971))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-10-26 01:01:18](https://github.com/leanprover-community/mathlib/commit/e88b4ed)
chore(measure_theory/constructions/pi): add `pi_of_empty` ([#9937](https://github.com/leanprover-community/mathlib/pull/9937))
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.measure.pi_of_empty
- \+ *lemma* measure_theory.measure.pi_univ



## [2021-10-25 22:55:58](https://github.com/leanprover-community/mathlib/commit/56de12a)
refactor(data/mv_polynomial): upgrade `monomial` to a `linear_map` ([#9870](https://github.com/leanprover-community/mathlib/pull/9870))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.C_eq_smul_one
- \+ *lemma* mv_polynomial.X_pow_eq_monomial
- \- *lemma* mv_polynomial.X_pow_eq_single
- \+ *lemma* mv_polynomial.eval₂_mul_C
- \+ *lemma* mv_polynomial.finsupp_support_eq_support
- \+/\- *def* mv_polynomial.monomial
- \- *lemma* mv_polynomial.monomial_add
- \+ *lemma* mv_polynomial.monomial_finsupp_sum_index
- \+ *def* mv_polynomial.monomial_one_hom
- \+ *lemma* mv_polynomial.monomial_one_hom_apply
- \+ *lemma* mv_polynomial.monomial_pow
- \+ *lemma* mv_polynomial.monomial_sum_index
- \+ *lemma* mv_polynomial.monomial_sum_one
- \+ *lemma* mv_polynomial.monomial_zero'
- \+/\- *lemma* mv_polynomial.sum_monomial_eq

Modified src/data/mv_polynomial/comm_ring.lean
- \- *lemma* mv_polynomial.monomial_neg
- \- *lemma* mv_polynomial.monomial_sub

Modified src/data/mv_polynomial/monad.lean


Modified src/data/mv_polynomial/pderiv.lean


Modified src/data/mv_polynomial/rename.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/polynomial/symmetric.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-10-25 22:55:56](https://github.com/leanprover-community/mathlib/commit/34b9933)
feat(number_theory/liouville): the set of Liouville numbers has measure zero ([#9702](https://github.com/leanprover-community/mathlib/pull/9702))
As a corollary, the filters `residual ℝ` and `volume.ae` are disjoint.
#### Estimated changes
Added src/number_theory/liouville/liouville_with.lean
- \+ *lemma* forall_liouville_with_iff
- \+ *lemma* liouville.frequently_exists_num
- \+ *lemma* liouville_with.add_int
- \+ *lemma* liouville_with.add_int_iff
- \+ *lemma* liouville_with.add_nat
- \+ *lemma* liouville_with.add_nat_iff
- \+ *lemma* liouville_with.add_rat
- \+ *lemma* liouville_with.add_rat_iff
- \+ *lemma* liouville_with.exists_pos
- \+ *lemma* liouville_with.frequently_lt_rpow_neg
- \+ *lemma* liouville_with.int_add
- \+ *lemma* liouville_with.int_add_iff
- \+ *lemma* liouville_with.int_mul
- \+ *lemma* liouville_with.int_mul_iff
- \+ *lemma* liouville_with.int_sub
- \+ *lemma* liouville_with.int_sub_iff
- \+ *lemma* liouville_with.mono
- \+ *lemma* liouville_with.mul_int
- \+ *lemma* liouville_with.mul_int_iff
- \+ *lemma* liouville_with.mul_nat
- \+ *lemma* liouville_with.mul_nat_iff
- \+ *lemma* liouville_with.mul_rat
- \+ *lemma* liouville_with.mul_rat_iff
- \+ *lemma* liouville_with.nat_add
- \+ *lemma* liouville_with.nat_add_iff
- \+ *lemma* liouville_with.nat_mul
- \+ *lemma* liouville_with.nat_mul_iff
- \+ *lemma* liouville_with.nat_sub
- \+ *lemma* liouville_with.nat_sub_iff
- \+ *lemma* liouville_with.ne_cast_int
- \+ *lemma* liouville_with.neg_iff
- \+ *lemma* liouville_with.rat_add
- \+ *lemma* liouville_with.rat_add_iff
- \+ *lemma* liouville_with.rat_mul
- \+ *lemma* liouville_with.rat_mul_iff
- \+ *lemma* liouville_with.rat_sub
- \+ *lemma* liouville_with.rat_sub_iff
- \+ *lemma* liouville_with.sub_int
- \+ *lemma* liouville_with.sub_int_iff
- \+ *lemma* liouville_with.sub_nat
- \+ *lemma* liouville_with.sub_nat_iff
- \+ *lemma* liouville_with.sub_rat
- \+ *lemma* liouville_with.sub_rat_iff
- \+ *def* liouville_with
- \+ *lemma* liouville_with_one

Added src/number_theory/liouville/measure.lean
- \+ *lemma* ae_not_liouville
- \+ *lemma* ae_not_liouville_with
- \+ *lemma* real.disjoint_residual_ae
- \+ *lemma* set_of_liouville_with_subset_aux
- \+ *lemma* volume_Union_set_of_liouville_with
- \+ *lemma* volume_set_of_liouville

Modified src/order/filter/basic.lean
- \+ *lemma* filter.disjoint_of_disjoint_of_mem
- \+ *lemma* filter.eventually.and_frequently

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* filter.eventually.exists_gt
- \+ *lemma* filter.eventually.exists_lt



## [2021-10-25 22:55:55](https://github.com/leanprover-community/mathlib/commit/c363ad6)
feat(category_theory/sites/*): Cover preserving functors ([#9691](https://github.com/leanprover-community/mathlib/pull/9691))
Split from [#9650](https://github.com/leanprover-community/mathlib/pull/9650)
- Defined `cover_preserving` functors as functors that push covering sieves to covering sieves.
- Defined `compatible_preserving` functors as functors that push compatible families to compatible families.
- Proved that functors that are both `cover_preserving` and `compatible_preserving` pulls sheaves to sheaves.
#### Estimated changes
Added src/category_theory/sites/cover_preserving.lean
- \+ *lemma* category_theory.compatible_preserving.apply_map
- \+ *structure* category_theory.compatible_preserving
- \+ *lemma* category_theory.cover_preserving.comp
- \+ *structure* category_theory.cover_preserving
- \+ *lemma* category_theory.id_cover_preserving
- \+ *lemma* category_theory.presieve.family_of_elements.compatible.functor_pushforward
- \+ *theorem* category_theory.pullback_is_sheaf_of_cover_preserving
- \+ *def* category_theory.pullback_sheaf
- \+ *def* category_theory.sites.pullback

Modified src/category_theory/sites/sheaf.lean
- \+ *abbreviation* category_theory.sheaf_over

Modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* category_theory.presieve.family_of_elements.comp_of_compatible
- \+ *def* category_theory.presieve.family_of_elements.functor_pushforward

Modified src/category_theory/sites/sieves.lean
- \+ *structure* category_theory.presieve.functor_pushforward_structure



## [2021-10-25 20:31:21](https://github.com/leanprover-community/mathlib/commit/5421200)
feat(group_theory/index): Small values of `subgroup.index` ([#9893](https://github.com/leanprover-community/mathlib/pull/9893))
`H.index = 1 ↔ H = ⊤` and related results.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_eq_one
- \+ *lemma* subgroup.index_ne_zero_of_fintype
- \+ *lemma* subgroup.one_lt_index_of_ne_top



## [2021-10-25 20:31:20](https://github.com/leanprover-community/mathlib/commit/880c7bd)
chore(linear_algebra/matrix): add fin expansions for trace and adjugate, and some trace lemmas ([#9884](https://github.com/leanprover-community/mathlib/pull/9884))
We have these expansions for `det` already, I figured we may as well have them for these.
This adds some other trivial trace lemmas while I'm touching the same file.
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_fin_one
- \+ *lemma* matrix.adjugate_fin_zero

Modified src/linear_algebra/matrix/trace.lean
- \+ *lemma* matrix.diag_col_mul_row
- \+ *lemma* matrix.trace_col_mul_row
- \+ *lemma* matrix.trace_fin_one
- \+ *lemma* matrix.trace_fin_three
- \+ *lemma* matrix.trace_fin_two
- \+ *lemma* matrix.trace_fin_zero
- \+ *lemma* matrix.trace_mul_cycle'
- \+ *lemma* matrix.trace_mul_cycle



## [2021-10-25 20:31:19](https://github.com/leanprover-community/mathlib/commit/e808b41)
feat(data/matrix/basic): lemmas about transpose and conj_transpose on sums and products ([#9880](https://github.com/leanprover-community/mathlib/pull/9880))
This also generalizes some previous results from `star_ring` to `star_add_monoid` now that the latter exists.
To help prove the non-commutative statements, this adds `monoid_hom.unop_map_list_prod` and similar.
This could probably used for proving `star_list_prod` in future.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* ring_hom.unop_map_list_prod

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.unop_map_list_prod

Modified src/data/list/basic.lean
- \+ *theorem* list.prod_concat
- \+ *lemma* monoid_hom.unop_map_list_prod
- \+ *lemma* opposite.op_list_prod
- \+ *lemma* opposite.unop_list_prod

Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.conj_transpose_add
- \+ *def* matrix.conj_transpose_add_equiv
- \+ *lemma* matrix.conj_transpose_add_equiv_symm
- \+ *lemma* matrix.conj_transpose_list_prod
- \+ *lemma* matrix.conj_transpose_list_sum
- \+ *lemma* matrix.conj_transpose_multiset_sum
- \+ *def* matrix.conj_transpose_ring_equiv
- \+/\- *lemma* matrix.conj_transpose_sub
- \+ *lemma* matrix.conj_transpose_sum
- \+ *def* matrix.transpose_add_equiv
- \+ *lemma* matrix.transpose_add_equiv_symm
- \+ *lemma* matrix.transpose_list_prod
- \+ *lemma* matrix.transpose_list_sum
- \+ *lemma* matrix.transpose_multiset_sum
- \+ *def* matrix.transpose_ring_equiv
- \+ *lemma* matrix.transpose_sum



## [2021-10-25 17:43:11](https://github.com/leanprover-community/mathlib/commit/87fa12a)
chore(linear_algebra/matrix/nonsingular_inverse): replace `1 < fintype.card n` with `nontrivial n` ([#9953](https://github.com/leanprover-community/mathlib/pull/9953))
This likely makes this a better simp lemma
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* matrix.adjugate_zero



## [2021-10-25 17:43:10](https://github.com/leanprover-community/mathlib/commit/0d131fe)
chore(group_theory/submonoid): move a lemma to reduce imports ([#9951](https://github.com/leanprover-community/mathlib/pull/9951))
Currently, `algebra.pointwise` is a relatively "heavy" import (e.g., it depends on `data.set.finite`) and I want to use submonoid closures a bit earlier than that.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/membership.lean
- \- *lemma* submonoid.mem_closure_inv

Modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* submonoid.mem_closure_inv

Modified src/ring_theory/subsemiring.lean




## [2021-10-25 17:43:09](https://github.com/leanprover-community/mathlib/commit/374885a)
feat(linear_algebra/matrix/nonsingular_inverse): lemmas about adjugate ([#9947](https://github.com/leanprover-community/mathlib/pull/9947))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_update_column_smul'
- \+ *lemma* matrix.det_update_row_smul'

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_conj_transpose
- \+ *lemma* matrix.adjugate_smul
- \+ *lemma* matrix.cramer_smul
- \- *lemma* matrix.ring_hom.map_adjugate
- \+ *lemma* ring_hom.map_adjugate

Modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* multilinear_map.map_update_smul



## [2021-10-25 17:43:06](https://github.com/leanprover-community/mathlib/commit/c693682)
chore(analysis/normed/group/basic): make various norm instances computable ([#9946](https://github.com/leanprover-community/mathlib/pull/9946))
Instead of defining the default `edist` as `ennreal.of_real` which introduces an `ite` on an undecidable equality, this constructs the `ennreal` directly using a proof of non-negativity.
This removes `noncomputable theory` from some files so as to make it obvious from the source alone which definitions are and are not computable.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *def* normed_group.of_core
- \+ *def* semi_normed_group.of_core

Modified src/topology/metric_space/basic.lean
- \- *def* metric.diam



## [2021-10-25 17:43:03](https://github.com/leanprover-community/mathlib/commit/5fcbd2b)
chore(linear_algebra/matrix/nonsingular_inverse): use pi.single instead of ite ([#9944](https://github.com/leanprover-community/mathlib/pull/9944))
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *def* matrix.adjugate



## [2021-10-25 17:43:01](https://github.com/leanprover-community/mathlib/commit/5778df8)
chore(analysis/complex/circle): upgrade `exp_map_circle` to `continuous_map` ([#9942](https://github.com/leanprover-community/mathlib/pull/9942))
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+/\- *def* exp_map_circle
- \+ *lemma* exp_map_circle_add
- \+ *lemma* exp_map_circle_zero



## [2021-10-25 17:43:00](https://github.com/leanprover-community/mathlib/commit/2026a5f)
feat(measure_theory/measure): better `measure.restrict_singleton` ([#9936](https://github.com/leanprover-community/mathlib/pull/9936))
With new `restrict_singleton`, `simp` can simplify `∫ x in {a}, f x ∂μ`
to `(μ {a}).to_real • f a`.
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.integral_dirac'
- \+/\- *lemma* measure_theory.integral_dirac

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.restrict_singleton'
- \+ *lemma* measure_theory.measure.restrict_singleton



## [2021-10-25 17:42:59](https://github.com/leanprover-community/mathlib/commit/8eb1c02)
feat(analysis/special_functions/pow): Equivalent conditions for zero powers ([#9897](https://github.com/leanprover-community/mathlib/pull/9897))
Lemmas for 0^x in the reals and complex numbers.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.eq_zero_cpow_iff
- \+ *lemma* complex.zero_cpow_eq_iff
- \+ *lemma* real.eq_zero_rpow_iff
- \+ *lemma* real.zero_rpow_eq_iff



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
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/imo/imo1977_q6.lean


Modified archive/imo/imo1981_q3.lean


Modified archive/miu_language/decision_suf.lean


Modified archive/oxford_invariants/2021summer/week3_p1.lean


Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/intervals.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/continued_fractions/terminated_stable.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/order/ring.lean
- \- *lemma* mul_sub'
- \+ *lemma* mul_tsub
- \- *lemma* sub_mul'
- \+ *lemma* tsub_mul

Modified src/algebra/order/sub.lean
- \+ *lemma* add_tsub_add_eq_tsub_right
- \- *lemma* add_tsub_add_right_eq_tsub
- \+/\- *lemma* tsub_add_eq_tsub_tsub
- \+/\- *lemma* tsub_add_eq_tsub_tsub_swap

Modified src/algebra/pointwise.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/composition.lean


Modified src/combinatorics/derangements/finite.lean


Modified src/combinatorics/hall/finite.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/computability/DFA.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/bitvec/core.lean


Modified src/data/buffer/parser/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/list.lean


Modified src/data/fin/basic.lean


Modified src/data/finset/basic.lean


Modified src/data/hash_map.lean


Modified src/data/int/basic.lean


Modified src/data/int/cast.lean


Modified src/data/list/basic.lean


Modified src/data/list/cycle.lean


Modified src/data/list/intervals.lean


Modified src/data/list/nat_antidiagonal.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/list/perm.lean


Modified src/data/list/range.lean


Modified src/data/list/rotate.lean


Modified src/data/list/zip.lean


Modified src/data/multiset/nodup.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/pderiv.lean


Modified src/data/nat/basic.lean
- \+ *lemma* has_lt.lt.nat_succ_le

Modified src/data/nat/bitwise.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/choose/basic.lean


Modified src/data/nat/choose/cast.lean


Modified src/data/nat/choose/dvd.lean


Modified src/data/nat/choose/sum.lean


Modified src/data/nat/dist.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/nat/factorial/cast.lean


Modified src/data/nat/interval.lean


Modified src/data/nat/log.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/pow.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/psub.lean


Modified src/data/nat/totient.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial/cancel_leads.lean


Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/data/polynomial/denoms_clearable.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/hasse_deriv.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/polynomial/mirror.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/sym/card.lean


Modified src/data/vector/basic.lean


Modified src/data/zmod/basic.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/dynamics/ergodic/measure_preserving.lean


Modified src/dynamics/periodic_pts.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/group_theory/nilpotent.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/concrete_cycle.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/list.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/matrix/fpow.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/vandermonde.lean


Modified src/measure_theory/decomposition/signed_hahn.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/admissible_card_pow_degree.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/liouville/liouville_constant.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/primorial.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/jordan_holder.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/pochhammer.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean


Modified src/ring_theory/witt_vector/teichmuller.lean


Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/game/domineering.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/tactic/group.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/suggest.lean


Modified src/testing/slim_check/sampleable.lean


Modified test/library_search/basic.lean




## [2021-10-25 17:42:56](https://github.com/leanprover-community/mathlib/commit/f298c55)
refactor(linear_algebra/finite_dimensional): define finite_dimensional using module.finite ([#9854](https://github.com/leanprover-community/mathlib/pull/9854))
`finite_dimensional K V` is by definition `is_noetherian K V`. We refactor this to use everywhere `finite K V` instead.
To keep the PR reasonably small, we don't delete `finite_dimension`, but we define it as `module.finite`. In a future PR we will remove it.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/geometry/manifold/whitney_embedding.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *def* finite_dimensional.fintype_basis_index

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/topology/metric_space/hausdorff_dimension.lean




## [2021-10-25 13:43:52](https://github.com/leanprover-community/mathlib/commit/3d457a2)
chore(topology/continuous_function): review API ([#9950](https://github.com/leanprover-community/mathlib/pull/9950))
* add `simps` config for `α →ᵇ β`;
* use better variable names in `topology.continuous_function.compact`;
* weaken some TC assumptions in `topology.continuous_function.compact`;
* migrate more API from `α →ᵇ β` to `C(α, β)`.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \- *lemma* bounded_continuous_function.coe_const
- \+/\- *def* bounded_continuous_function.const
- \+ *lemma* bounded_continuous_function.const_apply'
- \- *lemma* bounded_continuous_function.const_apply
- \+/\- *def* bounded_continuous_function.mk_of_discrete
- \- *lemma* bounded_continuous_function.mk_of_discrete_apply
- \+ *def* bounded_continuous_function.simps.apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* bounded_continuous_function.dist_forget_boundedness
- \+ *lemma* bounded_continuous_function.dist_mk_of_compact
- \+/\- *lemma* bounded_continuous_function.norm_forget_boundedness_eq
- \+ *lemma* bounded_continuous_function.norm_mk_of_compact
- \+/\- *def* continuous_map.add_equiv_bounded_of_compact
- \- *lemma* continuous_map.add_equiv_bounded_of_compact_apply_apply
- \- *lemma* continuous_map.add_equiv_bounded_of_compact_to_equiv
- \+ *lemma* continuous_map.continuous_coe
- \+ *lemma* continuous_map.continuous_eval
- \+ *lemma* continuous_map.continuous_evalx
- \+ *lemma* continuous_map.dist_apply_le_dist
- \+/\- *lemma* continuous_map.dist_lt_of_nonempty
- \+/\- *def* continuous_map.equiv_bounded_of_compact
- \+/\- *lemma* continuous_map.linear_isometry_bounded_of_compact_apply_apply
- \+/\- *lemma* continuous_map.linear_isometry_bounded_of_compact_symm_apply

Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-10-25 13:43:51](https://github.com/leanprover-community/mathlib/commit/f23354d)
feat(linear_algebra/basic, ring_theory/ideal/basic): add span_insert ([#9941](https://github.com/leanprover-community/mathlib/pull/9941))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_insert

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.span_insert



## [2021-10-25 10:59:45](https://github.com/leanprover-community/mathlib/commit/26c838f)
refactor(data/real/ennreal): remove ordered sub simp lemmas ([#9902](https://github.com/leanprover-community/mathlib/pull/9902))
* They are now simp lemmas in `algebra/order/sub`
* Squeeze some simps
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+/\- *lemma* add_tsub_cancel_of_le
- \+/\- *lemma* tsub_eq_zero_iff_le
- \+ *lemma* tsub_eq_zero_of_le
- \+/\- *lemma* tsub_pos_iff_lt

Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/specific_limits.lean


Modified src/computability/halting.lean


Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.sub_eq_zero_of_le

Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/regular.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/emetric_space.lean




## [2021-10-25 08:37:22](https://github.com/leanprover-community/mathlib/commit/dc1484e)
feat(ring_theory/polynomial/cyclotomic): add lemmas about evaluation of cyclotomic polynomials at one ([#9910](https://github.com/leanprover-community/mathlib/pull/9910))
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* polynomial.eval_one_cyclotomic_prime
- \+ *lemma* polynomial.eval_one_cyclotomic_prime_pow
- \+ *lemma* polynomial.eval₂_one_cyclotomic_prime
- \+ *lemma* polynomial.eval₂_one_cyclotomic_prime_pow



## [2021-10-25 06:51:07](https://github.com/leanprover-community/mathlib/commit/7e53203)
chore(group_theory/submonoid/operations): golf a few proofs ([#9948](https://github.com/leanprover-community/mathlib/pull/9948))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.mk_mul_mk
- \+ *lemma* submonoid.mul_def
- \+ *lemma* submonoid.one_def



## [2021-10-25 06:51:05](https://github.com/leanprover-community/mathlib/commit/bfcbe68)
feat(group_theory/subgroup/basic): `normalizer_eq_top` ([#9917](https://github.com/leanprover-community/mathlib/pull/9917))
The normalizer is the whole group if and only if the subgroup is normal.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.normalizer_eq_top



## [2021-10-25 06:51:03](https://github.com/leanprover-community/mathlib/commit/41b90d7)
feat(group_theory/index): Second isomorphism theorem in terms of `relindex` ([#9915](https://github.com/leanprover-community/mathlib/pull/9915))
Restates the second isomorphism theorem in terms of `relindex`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.inf_relindex_eq_relindex_sup
- \+ *lemma* subgroup.relindex_eq_relindex_sup



## [2021-10-25 05:13:27](https://github.com/leanprover-community/mathlib/commit/b9260f2)
feat(group_theory/subgroup/basic): `map_subtype_le` ([#9916](https://github.com/leanprover-community/mathlib/pull/9916))
A subgroup of a subgroup is `≤`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.map_subtype_le



## [2021-10-25 01:28:17](https://github.com/leanprover-community/mathlib/commit/951a60e)
chore(data/list/basic): golf a proof ([#9949](https://github.com/leanprover-community/mathlib/pull/9949))
Prove `list.mem_map` directly, get `list.exists_of_mem_map` and
`list.mem_map_of_mem` as corollaries.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *theorem* list.exists_of_mem_map
- \+/\- *theorem* list.pmap_eq_map



## [2021-10-25 01:28:16](https://github.com/leanprover-community/mathlib/commit/264d33e)
docs(control/traversable/lemmas): Add module docstring ([#9927](https://github.com/leanprover-community/mathlib/pull/9927))
#### Estimated changes
Modified docs/references.bib


Modified src/control/traversable/lemmas.lean
- \+/\- *lemma* traversable.id_sequence
- \+/\- *theorem* traversable.map_traverse
- \+/\- *theorem* traversable.pure_transformation_apply
- \+/\- *lemma* traversable.pure_traverse
- \+/\- *lemma* traversable.traverse_eq_map_id'
- \+/\- *lemma* traversable.traverse_id



## [2021-10-24 22:52:58](https://github.com/leanprover-community/mathlib/commit/c4760b9)
feat(algebra/big_operators/basic): prod/sum over an empty type ([#9939](https://github.com/leanprover-community/mathlib/pull/9939))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* fintype.prod_empty

Modified src/linear_algebra/multilinear/basic.lean




## [2021-10-24 22:52:57](https://github.com/leanprover-community/mathlib/commit/f9da68c)
feat(*): a few more `fun_unique`s ([#9938](https://github.com/leanprover-community/mathlib/pull/9938))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.fun_unique

Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.fun_unique

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.coe_fun_unique
- \+ *lemma* continuous_linear_equiv.coe_fun_unique_symm
- \+ *def* continuous_linear_equiv.fun_unique

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.fun_unique



## [2021-10-24 22:52:56](https://github.com/leanprover-community/mathlib/commit/942e60f)
chore(algebra/*/pi): add missing lemmas about function.update and set.piecewise ([#9935](https://github.com/leanprover-community/mathlib/pull/9935))
This adds `function.update_{zero,one,add,mul,sub,div,neg,inv,smul,vadd}`, and moves `pi.piecewise_{sub,div,neg,inv}` into the `set` namespace to match `set.piecewise_{add,mul}`.
This also adds `finset.piecewise_erase_univ`, as this is tangentially related.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* function.update_div
- \+ *lemma* function.update_inv
- \+ *lemma* function.update_mul
- \+ *lemma* function.update_one
- \- *lemma* pi.piecewise_div
- \- *lemma* pi.piecewise_inv
- \+ *lemma* set.piecewise_div
- \+ *lemma* set.piecewise_inv

Modified src/algebra/module/pi.lean
- \+ *lemma* function.update_smul
- \+ *lemma* set.piecewise_smul

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.compl_singleton
- \+ *lemma* finset.piecewise_erase_univ

Modified src/logic/function/basic.lean
- \+ *lemma* function.apply_update₂



## [2021-10-24 22:52:55](https://github.com/leanprover-community/mathlib/commit/1e7f6b9)
docs(control/bitraversable/instances): Add def docstrings ([#9931](https://github.com/leanprover-community/mathlib/pull/9931))
#### Estimated changes
Modified src/control/bitraversable/instances.lean
- \+/\- *def* const.bitraverse



## [2021-10-24 22:52:54](https://github.com/leanprover-community/mathlib/commit/5d1e8f7)
docs(control/applicative): Add module docstring ([#9930](https://github.com/leanprover-community/mathlib/pull/9930))
#### Estimated changes
Modified src/control/applicative.lean
- \+/\- *lemma* applicative.pure_seq_eq_map'



## [2021-10-24 22:52:53](https://github.com/leanprover-community/mathlib/commit/6f1d45d)
docs(control/bitraversable/basic): Add defs docstrings ([#9929](https://github.com/leanprover-community/mathlib/pull/9929))
#### Estimated changes
Modified src/control/bitraversable/basic.lean




## [2021-10-24 22:52:52](https://github.com/leanprover-community/mathlib/commit/5642c62)
docs(control/traversable/equiv): Add module docstring ([#9928](https://github.com/leanprover-community/mathlib/pull/9928))
#### Estimated changes
Modified src/control/traversable/equiv.lean




## [2021-10-24 22:52:51](https://github.com/leanprover-community/mathlib/commit/8c0b8c7)
feat(group_theory/subgroup/basic): Contrapositive of `card_le_one_iff_eq_bot` ([#9918](https://github.com/leanprover-community/mathlib/pull/9918))
Adds contrapositive of `card_le_one_iff_eq_bot`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.one_lt_card_iff_ne_bot



## [2021-10-24 22:52:50](https://github.com/leanprover-community/mathlib/commit/4468231)
feat(data/nat/log): Equivalent conditions for logarithms to equal zero and one ([#9903](https://github.com/leanprover-community/mathlib/pull/9903))
Add equivalent conditions for a `nat.log` to equal 0 or 1.
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *lemma* nat.log_eq_one_iff
- \+ *lemma* nat.log_eq_zero_iff
- \+ *lemma* nat.log_of_one_lt_of_le



## [2021-10-24 22:52:49](https://github.com/leanprover-community/mathlib/commit/12515db)
feat(data/list): product of list.update_nth in terms of inverses ([#9800](https://github.com/leanprover-community/mathlib/pull/9800))
Expression for the product of `l.update_nth n x` in terms of inverses instead of `take` and `drop`, assuming a group instead of a monoid.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.prod_drop_succ
- \+ *lemma* list.prod_update_nth'
- \- *lemma* list.sum_take_add_sum_drop
- \- *lemma* list.sum_take_succ

Modified src/data/list/zip.lean
- \+ *lemma* list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop
- \+ *lemma* list.prod_mul_prod_eq_prod_zip_with_of_length_eq

Modified src/data/vector/basic.lean
- \+ *lemma* vector.prod_update_nth'
- \+ *lemma* vector.prod_update_nth
- \+ *lemma* vector.to_list_update_nth

Modified src/data/vector/zip.lean
- \+ *lemma* vector.prod_mul_prod_eq_prod_zip_with



## [2021-10-24 22:06:49](https://github.com/leanprover-community/mathlib/commit/c20f08e)
feat(dynamics/ergodic/measure_preserving): add `measure_preserving.symm` ([#9940](https://github.com/leanprover-community/mathlib/pull/9940))
Also make the proof of `measure_preserving.skew_product` a bit more readable.
#### Estimated changes
Modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.symm



## [2021-10-24 22:06:48](https://github.com/leanprover-community/mathlib/commit/4ea8de9)
feat(measure_theory/integral): Divergence theorem for Bochner integral ([#9811](https://github.com/leanprover-community/mathlib/pull/9811))
#### Estimated changes
Added src/measure_theory/integral/divergence_theorem.lean
- \+ *lemma* measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable



## [2021-10-24 21:16:31](https://github.com/leanprover-community/mathlib/commit/a30e190)
split(analysis/normed_space/exponential): split file to minimize dependencies ([#9932](https://github.com/leanprover-community/mathlib/pull/9932))
As suggested by @urkud, this moves all the results depending on derivatives, `complex.exp` and `real.exp` to a new file `analysis/special_function/exponential`. That way the definitions of `exp` and `[complex, real].exp` are independent, which means we could eventually redefine the latter in terms of the former without breaking the import tree.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \- *lemma* complex.exp_eq_exp_ℂ_ℂ
- \- *lemma* has_deriv_at_exp
- \- *lemma* has_deriv_at_exp_of_mem_ball
- \- *lemma* has_deriv_at_exp_zero
- \- *lemma* has_deriv_at_exp_zero_of_radius_pos
- \- *lemma* has_fderiv_at_exp
- \- *lemma* has_fderiv_at_exp_of_mem_ball
- \- *lemma* has_fderiv_at_exp_zero
- \- *lemma* has_fderiv_at_exp_zero_of_radius_pos
- \- *lemma* has_strict_deriv_at_exp
- \- *lemma* has_strict_deriv_at_exp_of_mem_ball
- \- *lemma* has_strict_deriv_at_exp_zero
- \- *lemma* has_strict_deriv_at_exp_zero_of_radius_pos
- \- *lemma* has_strict_fderiv_at_exp
- \- *lemma* has_strict_fderiv_at_exp_of_mem_ball
- \- *lemma* has_strict_fderiv_at_exp_zero
- \- *lemma* has_strict_fderiv_at_exp_zero_of_radius_pos
- \- *lemma* real.exp_eq_exp_ℝ_ℝ

Added src/analysis/special_functions/exponential.lean
- \+ *lemma* complex.exp_eq_exp_ℂ_ℂ
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* has_deriv_at_exp_of_mem_ball
- \+ *lemma* has_deriv_at_exp_zero
- \+ *lemma* has_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_fderiv_at_exp
- \+ *lemma* has_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_fderiv_at_exp_zero
- \+ *lemma* has_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* has_strict_deriv_at_exp
- \+ *lemma* has_strict_deriv_at_exp_of_mem_ball
- \+ *lemma* has_strict_deriv_at_exp_zero
- \+ *lemma* has_strict_deriv_at_exp_zero_of_radius_pos
- \+ *lemma* has_strict_fderiv_at_exp
- \+ *lemma* has_strict_fderiv_at_exp_of_mem_ball
- \+ *lemma* has_strict_fderiv_at_exp_zero
- \+ *lemma* has_strict_fderiv_at_exp_zero_of_radius_pos
- \+ *lemma* real.exp_eq_exp_ℝ_ℝ

Modified src/combinatorics/derangements/exponential.lean




## [2021-10-24 16:04:22](https://github.com/leanprover-community/mathlib/commit/dc6b8e1)
feat(topology): add some lemmas ([#9907](https://github.com/leanprover-community/mathlib/pull/9907))
* From the sphere eversion project
* Add compositional version `continuous.fst` of `continuous_fst`, compare `measurable.fst`.
* Add `comp_continuous_at_iff` and `comp_continuous_at_iff'` for `homeomorph` (and for `inducing`).
* Add some variants of these (requested by review).
#### Estimated changes
Modified src/topology/constructions.lean
- \+ *lemma* continuous.fst
- \+ *lemma* continuous.snd
- \+ *lemma* continuous_at.fst
- \+ *lemma* continuous_at.snd

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.fst
- \+ *lemma* continuous_on.snd
- \+ *lemma* inducing.continuous_within_at_iff

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.comp_continuous_at_iff'
- \+ *lemma* homeomorph.comp_continuous_at_iff
- \+ *lemma* homeomorph.comp_continuous_within_at_iff

Modified src/topology/maps.lean
- \+ *lemma* inducing.continuous_at_iff'
- \+ *lemma* inducing.continuous_at_iff



## [2021-10-24 13:34:54](https://github.com/leanprover-community/mathlib/commit/696f07f)
split(data/list/lattice): split off `data.list.basic` ([#9906](https://github.com/leanprover-community/mathlib/pull/9906))
#### Estimated changes
Deleted src/data/list/bag_inter.lean
- \- *theorem* list.bag_inter_nil
- \- *theorem* list.bag_inter_nil_iff_inter_nil
- \- *theorem* list.bag_inter_sublist_left
- \- *theorem* list.cons_bag_inter_of_neg
- \- *theorem* list.cons_bag_inter_of_pos
- \- *theorem* list.count_bag_inter
- \- *theorem* list.mem_bag_inter
- \- *theorem* list.nil_bag_inter

Modified src/data/list/basic.lean
- \- *theorem* list.cons_union
- \- *theorem* list.disjoint.symm
- \- *theorem* list.disjoint_append_left
- \- *theorem* list.disjoint_append_right
- \- *theorem* list.disjoint_comm
- \- *theorem* list.disjoint_cons_left
- \- *theorem* list.disjoint_cons_right
- \- *theorem* list.disjoint_iff_ne
- \- *theorem* list.disjoint_left
- \- *theorem* list.disjoint_nil_left
- \- *theorem* list.disjoint_nil_right
- \- *theorem* list.disjoint_of_disjoint_append_left_left
- \- *theorem* list.disjoint_of_disjoint_append_left_right
- \- *theorem* list.disjoint_of_disjoint_append_right_left
- \- *theorem* list.disjoint_of_disjoint_append_right_right
- \- *theorem* list.disjoint_of_disjoint_cons_left
- \- *theorem* list.disjoint_of_disjoint_cons_right
- \- *theorem* list.disjoint_of_subset_left
- \- *theorem* list.disjoint_of_subset_right
- \- *theorem* list.disjoint_right
- \- *theorem* list.disjoint_singleton
- \- *theorem* list.disjoint_take_drop
- \- *theorem* list.forall_mem_inter_of_forall_left
- \- *theorem* list.forall_mem_inter_of_forall_right
- \- *theorem* list.forall_mem_of_forall_mem_union_left
- \- *theorem* list.forall_mem_of_forall_mem_union_right
- \- *theorem* list.forall_mem_union
- \- *theorem* list.inter_cons_of_mem
- \- *theorem* list.inter_cons_of_not_mem
- \- *theorem* list.inter_eq_nil_iff_disjoint
- \- *theorem* list.inter_nil
- \- *lemma* list.inter_reverse
- \- *theorem* list.inter_subset_left
- \- *theorem* list.inter_subset_right
- \- *theorem* list.mem_inter
- \- *theorem* list.mem_inter_of_mem_of_mem
- \- *theorem* list.mem_of_mem_inter_left
- \- *theorem* list.mem_of_mem_inter_right
- \- *theorem* list.mem_union
- \- *theorem* list.mem_union_left
- \- *theorem* list.mem_union_right
- \- *theorem* list.nil_union
- \- *theorem* list.singleton_disjoint
- \- *theorem* list.sublist_suffix_of_union
- \- *theorem* list.subset_inter
- \- *theorem* list.suffix_union_right
- \- *theorem* list.union_sublist_append

Modified src/data/list/default.lean


Modified src/data/list/intervals.lean


Added src/data/list/lattice.lean
- \+ *lemma* list.bag_inter_nil
- \+ *lemma* list.bag_inter_nil_iff_inter_nil
- \+ *lemma* list.bag_inter_sublist_left
- \+ *lemma* list.cons_bag_inter_of_neg
- \+ *lemma* list.cons_bag_inter_of_pos
- \+ *lemma* list.cons_union
- \+ *lemma* list.count_bag_inter
- \+ *lemma* list.disjoint.symm
- \+ *lemma* list.disjoint_append_left
- \+ *lemma* list.disjoint_append_right
- \+ *lemma* list.disjoint_comm
- \+ *lemma* list.disjoint_cons_left
- \+ *lemma* list.disjoint_cons_right
- \+ *lemma* list.disjoint_iff_ne
- \+ *lemma* list.disjoint_left
- \+ *lemma* list.disjoint_nil_left
- \+ *lemma* list.disjoint_nil_right
- \+ *lemma* list.disjoint_of_disjoint_append_left_left
- \+ *lemma* list.disjoint_of_disjoint_append_left_right
- \+ *lemma* list.disjoint_of_disjoint_append_right_left
- \+ *lemma* list.disjoint_of_disjoint_append_right_right
- \+ *lemma* list.disjoint_of_disjoint_cons_left
- \+ *lemma* list.disjoint_of_disjoint_cons_right
- \+ *lemma* list.disjoint_of_subset_left
- \+ *lemma* list.disjoint_of_subset_right
- \+ *lemma* list.disjoint_right
- \+ *lemma* list.disjoint_singleton
- \+ *lemma* list.disjoint_take_drop
- \+ *lemma* list.forall_mem_inter_of_forall_left
- \+ *lemma* list.forall_mem_inter_of_forall_right
- \+ *lemma* list.forall_mem_of_forall_mem_union_left
- \+ *lemma* list.forall_mem_of_forall_mem_union_right
- \+ *lemma* list.forall_mem_union
- \+ *lemma* list.inter_cons_of_mem
- \+ *lemma* list.inter_cons_of_not_mem
- \+ *lemma* list.inter_eq_nil_iff_disjoint
- \+ *lemma* list.inter_nil
- \+ *lemma* list.inter_reverse
- \+ *lemma* list.inter_subset_left
- \+ *lemma* list.inter_subset_right
- \+ *lemma* list.mem_bag_inter
- \+ *lemma* list.mem_inter
- \+ *lemma* list.mem_inter_of_mem_of_mem
- \+ *lemma* list.mem_of_mem_inter_left
- \+ *lemma* list.mem_of_mem_inter_right
- \+ *lemma* list.mem_union
- \+ *lemma* list.mem_union_left
- \+ *lemma* list.mem_union_right
- \+ *lemma* list.nil_bag_inter
- \+ *lemma* list.nil_union
- \+ *lemma* list.singleton_disjoint
- \+ *lemma* list.sublist_suffix_of_union
- \+ *lemma* list.subset_inter
- \+ *lemma* list.suffix_union_right
- \+ *lemma* list.union_sublist_append

Modified src/data/list/nodup.lean


Modified src/data/list/perm.lean




## [2021-10-24 13:34:52](https://github.com/leanprover-community/mathlib/commit/9dc3b4d)
feat(topology/algebra/group): continuous div lemmas ([#9905](https://github.com/leanprover-community/mathlib/pull/9905))
* From the sphere eversion project
* There were already some lemmas about `sub`, now they also have multiplicative versions
* Add more lemmas about `div` being continuous
* Add `continuous_at.inv`
* Rename `nhds_translation` -> `nhds_translation_sub`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* continuous.div'
- \- *lemma* continuous.sub
- \+ *lemma* continuous_at.div'
- \+ *lemma* continuous_at.inv
- \+ *lemma* continuous_div_left'
- \+ *lemma* continuous_div_right'
- \+ *lemma* continuous_on.div'
- \- *lemma* continuous_on.sub
- \+ *lemma* continuous_within_at.div'
- \- *lemma* continuous_within_at.sub
- \+ *lemma* filter.tendsto.const_div'
- \+ *lemma* filter.tendsto.div'
- \+ *lemma* filter.tendsto.div_const'
- \- *lemma* filter.tendsto.sub
- \- *lemma* nhds_translation
- \+ *lemma* nhds_translation_div

Modified src/topology/algebra/uniform_group.lean




## [2021-10-24 10:50:08](https://github.com/leanprover-community/mathlib/commit/be94800)
feat(data/real/nnreal): use the nonneg instance ([#9701](https://github.com/leanprover-community/mathlib/pull/9701))
... to show that `nnreal` forms a conditionally complete linear order with bot.
This requires some fixes in the order hierarchy.
* orders on subtypes are now obtained by lifting `coe` instead of `subtype.val`. This has the nice side benefit that some proofs became simpler.
* `subset_conditionally_complete_linear_order` is now reducible
#### Estimated changes
Modified src/algebra/order/nonneg.lean


Modified src/algebraic_geometry/ringed_space.lean


Modified src/data/equiv/denumerable.lean
- \+/\- *lemma* nat.subtype.exists_succ

Modified src/data/real/nnreal.lean


Modified src/order/basic.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean


Modified src/topology/sheaves/stalks.lean




## [2021-10-24 08:26:39](https://github.com/leanprover-community/mathlib/commit/416edee)
feat(analysis/normed_space/is_R_or_C): add three lemmas on bounds of linear maps over is_R_or_C. ([#9827](https://github.com/leanprover-community/mathlib/pull/9827))
Adding lemmas `linear_map.bound_of_sphere_bound`, `linear_map.bound_of_ball_bound`, `continuous_linear_map.op_norm_bound_of_ball_bound` as a preparation of a PR on Banach-Alaoglu theorem.
#### Estimated changes
Added src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* continuous_linear_map.op_norm_bound_of_ball_bound
- \+ *lemma* linear_map.bound_of_ball_bound
- \+ *lemma* linear_map.bound_of_sphere_bound



## [2021-10-24 03:33:39](https://github.com/leanprover-community/mathlib/commit/ecc544e)
chore(scripts): update nolints.txt ([#9923](https://github.com/leanprover-community/mathlib/pull/9923))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-10-24 03:33:38](https://github.com/leanprover-community/mathlib/commit/e836a72)
feat(order/galois_connection): add `exists_eq_{l,u}`, tidy up lemmas ([#9904](https://github.com/leanprover-community/mathlib/pull/9904))
This makes some arguments implicit to `compose` as these are inferrable from the other arguments, and changes `u_l_u_eq_u` and `l_u_l_eq_l` to be applied rather than unapplied, which shortens both the proof and the places where the lemma is used.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/model_theory/basic.lean


Modified src/order/closure.lean


Modified src/order/galois_connection.lean
- \+ *lemma* galois_connection.exists_eq_l
- \+ *lemma* galois_connection.exists_eq_u
- \+ *lemma* galois_connection.l_u_l_eq_l'
- \+/\- *lemma* galois_connection.l_u_l_eq_l
- \+ *lemma* galois_connection.u_l_u_eq_u'
- \+/\- *lemma* galois_connection.u_l_u_eq_u

Modified src/ring_theory/ideal/operations.lean




## [2021-10-24 03:33:37](https://github.com/leanprover-community/mathlib/commit/49c6841)
chore(topology): generalize `real.image_Icc` etc ([#9784](https://github.com/leanprover-community/mathlib/pull/9784))
* add lemmas about `Ici`/`Iic`/`Icc` in `α × β`;
* introduce a typeclass for `is_compact_Icc` so that the same lemma works for `ℝ` and `ℝⁿ`;
* generalize `real.image_Icc` etc to a conditionally complete linear order (e.g., now it works for `nnreal`, `ennreal`, `ereal`), move these lemmas to the `continuous_on` namespace.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/box_integral/basic.lean


Modified src/analysis/box_integral/box/basic.lean


Modified src/analysis/box_integral/divergence_theorem.lean


Modified src/analysis/box_integral/partition/measure.lean


Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_prod_Icc
- \+ *lemma* set.Icc_prod_eq
- \+ *lemma* set.Ici_prod_Ici
- \+ *lemma* set.Ici_prod_eq
- \+ *lemma* set.Iic_prod_Iic
- \+ *lemma* set.Iic_prod_eq

Modified src/measure_theory/integral/interval_integral.lean


Modified src/topology/algebra/ordered/compact.lean
- \+/\- *lemma* continuous.exists_forall_ge
- \+/\- *lemma* continuous.exists_forall_le
- \+ *lemma* continuous_on.image_Icc
- \+ *lemma* continuous_on.image_interval
- \+ *lemma* continuous_on.image_interval_eq_Icc
- \+/\- *lemma* is_compact.exists_Inf_image_eq
- \+/\- *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* is_compact.exists_forall_ge
- \+/\- *lemma* is_compact.exists_forall_le
- \- *lemma* is_compact_Icc
- \+/\- *lemma* is_compact_interval
- \- *lemma* is_compact_pi_Icc

Modified src/topology/algebra/ordered/intermediate_value.lean
- \+ *lemma* continuous_on.surj_on_Icc
- \+ *lemma* continuous_on.surj_on_interval

Modified src/topology/instances/real.lean
- \- *lemma* real.image_Icc
- \- *lemma* real.image_interval
- \- *lemma* real.image_interval_eq_Icc
- \- *lemma* real.interval_subset_image_interval



## [2021-10-24 01:53:46](https://github.com/leanprover-community/mathlib/commit/55a1160)
feat(linear_algebra): add notation for star-linear maps ([#9875](https://github.com/leanprover-community/mathlib/pull/9875))
This PR adds the notation `M →ₗ⋆[R] N`, `M ≃ₗ⋆[R] N`, etc, to denote star-linear maps/equivalences, i.e. semilinear maps where the ring hom is `star`. A special case of this are conjugate-linear maps when `R = ℂ`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/data/equiv/module.lean


Modified src/topology/algebra/module.lean


Added test/semilinear.lean




## [2021-10-24 00:37:39](https://github.com/leanprover-community/mathlib/commit/5ec1572)
feat(nat/choose/central): definition of the central binomial coefficient, and bounds ([#9753](https://github.com/leanprover-community/mathlib/pull/9753))
Two exponential lower bounds on the central binomial coefficient.
#### Estimated changes
Added src/data/nat/choose/central.lean
- \+ *def* nat.central_binom
- \+ *lemma* nat.central_binom_eq_two_mul_choose
- \+ *lemma* nat.central_binom_ne_zero
- \+ *lemma* nat.central_binom_pos
- \+ *lemma* nat.central_binom_zero
- \+ *lemma* nat.choose_le_central_binom
- \+ *lemma* nat.four_pow_le_two_mul_self_mul_central_binom
- \+ *lemma* nat.four_pow_lt_mul_central_binom
- \+ *lemma* nat.succ_mul_central_binom_succ
- \+ *lemma* nat.two_le_central_binom



## [2021-10-24 00:37:37](https://github.com/leanprover-community/mathlib/commit/d788647)
feat(ring_theory): generalize `adjoin_root.power_basis` ([#9536](https://github.com/leanprover-community/mathlib/pull/9536))
Now we only need that `g` is monic to state that `adjoin_root g` has a power basis. Note that this does not quite imply the result of [#9529](https://github.com/leanprover-community/mathlib/pull/9529): this is phrased in terms of `minpoly R (root g)` and the other PR in terms of `g` itself, so I don't have a direct use for the current PR. However, it seems useful enough to have this statement, so I PR'd it anyway.
#### Estimated changes
Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.sum_fin
- \+ *lemma* polynomial.sum_mod_by_monic_coeff

Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* adjoin_root.is_integral_root'
- \+ *lemma* adjoin_root.mk_eq_mk
- \+ *lemma* adjoin_root.mk_left_inverse
- \+ *lemma* adjoin_root.mk_surjective
- \+ *def* adjoin_root.mod_by_monic_hom
- \+ *lemma* adjoin_root.mod_by_monic_hom_mk
- \+ *def* adjoin_root.power_basis'
- \+ *def* adjoin_root.power_basis_aux'



## [2021-10-23 22:10:47](https://github.com/leanprover-community/mathlib/commit/928d0e0)
docs(data/dlist/instances): Add module docstring ([#9912](https://github.com/leanprover-community/mathlib/pull/9912))
#### Estimated changes
Modified src/control/traversable/equiv.lean


Modified src/data/dlist/instances.lean




## [2021-10-23 22:10:46](https://github.com/leanprover-community/mathlib/commit/15161e9)
docs(data/list/sigma): Add missing def dosctrings, expand module docs ([#9909](https://github.com/leanprover-community/mathlib/pull/9909))
#### Estimated changes
Modified src/data/list/sigma.lean
- \+/\- *def* list.keys
- \+/\- *theorem* list.keys_cons
- \+/\- *theorem* list.keys_nil
- \+/\- *def* list.nodupkeys



## [2021-10-23 22:10:45](https://github.com/leanprover-community/mathlib/commit/75b1a94)
refactor(analysis/special_functions/exp_log): split into 4 files ([#9882](https://github.com/leanprover-community/mathlib/pull/9882))
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/complex/log.lean


Added src/analysis/special_functions/exp.lean
- \+ *lemma* complex.continuous_exp
- \+ *lemma* complex.continuous_on_exp
- \+ *lemma* complex.exp_bound_sq
- \+ *lemma* complex.locally_lipschitz_exp
- \+ *lemma* continuous.cexp
- \+ *lemma* continuous.exp
- \+ *lemma* continuous_at.cexp
- \+ *lemma* continuous_at.exp
- \+ *lemma* continuous_on.cexp
- \+ *lemma* continuous_on.exp
- \+ *lemma* continuous_within_at.cexp
- \+ *lemma* continuous_within_at.exp
- \+ *lemma* filter.tendsto.cexp
- \+ *lemma* filter.tendsto.exp
- \+ *lemma* real.coe_comp_exp_order_iso
- \+ *lemma* real.coe_exp_order_iso_apply
- \+ *lemma* real.comap_exp_at_top
- \+ *lemma* real.comap_exp_nhds_within_Ioi_zero
- \+ *lemma* real.continuous_exp
- \+ *lemma* real.continuous_on_exp
- \+ *def* real.exp_order_iso
- \+ *lemma* real.map_exp_at_bot
- \+ *lemma* real.map_exp_at_top
- \+ *lemma* real.range_exp
- \+ *lemma* real.tendsto_comp_exp_at_bot
- \+ *lemma* real.tendsto_comp_exp_at_top
- \+ *lemma* real.tendsto_div_pow_mul_exp_add_at_top
- \+ *lemma* real.tendsto_exp_at_bot
- \+ *lemma* real.tendsto_exp_at_bot_nhds_within
- \+ *lemma* real.tendsto_exp_at_top
- \+ *lemma* real.tendsto_exp_comp_at_top
- \+ *lemma* real.tendsto_exp_div_pow_at_top
- \+ *lemma* real.tendsto_exp_neg_at_top_nhds_0
- \+ *lemma* real.tendsto_exp_nhds_0_nhds_1
- \+ *lemma* real.tendsto_mul_exp_add_div_pow_at_top
- \+ *lemma* real.tendsto_pow_mul_exp_neg_at_top_nhds_0

Added src/analysis/special_functions/exp_deriv.lean
- \+ *lemma* complex.deriv_exp
- \+ *lemma* complex.differentiable_at_exp
- \+ *lemma* complex.differentiable_exp
- \+ *lemma* complex.has_deriv_at_exp
- \+ *lemma* complex.has_strict_deriv_at_exp
- \+ *lemma* complex.has_strict_fderiv_at_exp_real
- \+ *lemma* complex.is_open_map_exp
- \+ *lemma* complex.iter_deriv_exp
- \+ *lemma* complex.times_cont_diff_exp
- \+ *lemma* deriv_cexp
- \+ *lemma* deriv_exp
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_within_exp
- \+ *lemma* differentiable.cexp
- \+ *lemma* differentiable.exp
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* fderiv_exp
- \+ *lemma* fderiv_within_exp
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_at.cexp_real
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* has_deriv_within_at.cexp_real
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* has_fderiv_at.cexp
- \+ *lemma* has_fderiv_at.exp
- \+ *lemma* has_fderiv_within_at.cexp
- \+ *lemma* has_fderiv_within_at.exp
- \+ *lemma* has_strict_deriv_at.cexp
- \+ *lemma* has_strict_deriv_at.cexp_real
- \+ *lemma* has_strict_deriv_at.exp
- \+ *lemma* has_strict_fderiv_at.cexp
- \+ *lemma* has_strict_fderiv_at.exp
- \+ *lemma* real.deriv_exp
- \+ *lemma* real.differentiable_at_exp
- \+ *lemma* real.differentiable_exp
- \+ *lemma* real.has_deriv_at_exp
- \+ *lemma* real.has_strict_deriv_at_exp
- \+ *lemma* real.iter_deriv_exp
- \+ *lemma* real.times_cont_diff_exp
- \+ *lemma* times_cont_diff.cexp
- \+ *lemma* times_cont_diff.exp
- \+ *lemma* times_cont_diff_at.cexp
- \+ *lemma* times_cont_diff_at.exp
- \+ *lemma* times_cont_diff_on.cexp
- \+ *lemma* times_cont_diff_on.exp
- \+ *lemma* times_cont_diff_within_at.cexp
- \+ *lemma* times_cont_diff_within_at.exp

Deleted src/analysis/special_functions/exp_log.lean
- \- *lemma* complex.continuous_exp
- \- *lemma* complex.continuous_on_exp
- \- *lemma* complex.deriv_exp
- \- *lemma* complex.differentiable_at_exp
- \- *lemma* complex.differentiable_exp
- \- *lemma* complex.exp_bound_sq
- \- *lemma* complex.has_deriv_at_exp
- \- *lemma* complex.has_strict_deriv_at_exp
- \- *lemma* complex.has_strict_fderiv_at_exp_real
- \- *lemma* complex.is_open_map_exp
- \- *lemma* complex.iter_deriv_exp
- \- *lemma* complex.locally_lipschitz_exp
- \- *lemma* complex.times_cont_diff_exp
- \- *lemma* continuous.cexp
- \- *lemma* continuous.log
- \- *lemma* continuous_at.cexp
- \- *lemma* continuous_at.log
- \- *lemma* continuous_on.cexp
- \- *lemma* continuous_on.log
- \- *lemma* continuous_within_at.cexp
- \- *lemma* continuous_within_at.log
- \- *lemma* deriv.log
- \- *lemma* deriv_cexp
- \- *lemma* deriv_exp
- \- *lemma* deriv_within.log
- \- *lemma* deriv_within_cexp
- \- *lemma* deriv_within_exp
- \- *lemma* differentiable.cexp
- \- *lemma* differentiable.exp
- \- *lemma* differentiable.log
- \- *lemma* differentiable_at.cexp
- \- *lemma* differentiable_at.exp
- \- *lemma* differentiable_at.log
- \- *lemma* differentiable_on.cexp
- \- *lemma* differentiable_on.exp
- \- *lemma* differentiable_on.log
- \- *lemma* differentiable_within_at.cexp
- \- *lemma* differentiable_within_at.exp
- \- *lemma* differentiable_within_at.log
- \- *lemma* fderiv.log
- \- *lemma* fderiv_exp
- \- *lemma* fderiv_within.log
- \- *lemma* fderiv_within_exp
- \- *lemma* filter.tendsto.cexp
- \- *lemma* filter.tendsto.log
- \- *lemma* has_deriv_at.cexp
- \- *lemma* has_deriv_at.cexp_real
- \- *lemma* has_deriv_at.exp
- \- *lemma* has_deriv_at.log
- \- *lemma* has_deriv_within_at.cexp
- \- *lemma* has_deriv_within_at.cexp_real
- \- *lemma* has_deriv_within_at.exp
- \- *lemma* has_deriv_within_at.log
- \- *lemma* has_fderiv_at.cexp
- \- *lemma* has_fderiv_at.exp
- \- *lemma* has_fderiv_at.log
- \- *lemma* has_fderiv_within_at.cexp
- \- *lemma* has_fderiv_within_at.exp
- \- *lemma* has_fderiv_within_at.log
- \- *lemma* has_strict_deriv_at.cexp
- \- *lemma* has_strict_deriv_at.cexp_real
- \- *lemma* has_strict_deriv_at.exp
- \- *lemma* has_strict_deriv_at.log
- \- *lemma* has_strict_fderiv_at.cexp
- \- *lemma* has_strict_fderiv_at.exp
- \- *lemma* has_strict_fderiv_at.log
- \- *lemma* real.abs_log_sub_add_sum_range_le
- \- *lemma* real.coe_comp_exp_order_iso
- \- *lemma* real.coe_exp_order_iso_apply
- \- *lemma* real.comap_exp_at_top
- \- *lemma* real.comap_exp_nhds_within_Ioi_zero
- \- *lemma* real.continuous_at_log
- \- *lemma* real.continuous_at_log_iff
- \- *lemma* real.continuous_exp
- \- *lemma* real.continuous_log'
- \- *lemma* real.continuous_log
- \- *lemma* real.continuous_on_exp
- \- *lemma* real.continuous_on_log
- \- *lemma* real.deriv_exp
- \- *lemma* real.deriv_log'
- \- *lemma* real.deriv_log
- \- *lemma* real.differentiable_at_exp
- \- *lemma* real.differentiable_at_log
- \- *lemma* real.differentiable_at_log_iff
- \- *lemma* real.differentiable_exp
- \- *lemma* real.differentiable_on_log
- \- *lemma* real.eq_one_of_pos_of_log_eq_zero
- \- *lemma* real.exp_log
- \- *lemma* real.exp_log_eq_abs
- \- *lemma* real.exp_log_of_neg
- \- *def* real.exp_order_iso
- \- *lemma* real.has_deriv_at_exp
- \- *lemma* real.has_deriv_at_log
- \- *lemma* real.has_strict_deriv_at_exp
- \- *lemma* real.has_strict_deriv_at_log
- \- *lemma* real.has_strict_deriv_at_log_of_pos
- \- *theorem* real.has_sum_pow_div_log_of_abs_lt_1
- \- *lemma* real.iter_deriv_exp
- \- *lemma* real.log_abs
- \- *lemma* real.log_div
- \- *lemma* real.log_eq_zero
- \- *lemma* real.log_exp
- \- *lemma* real.log_inj_on_pos
- \- *lemma* real.log_inv
- \- *lemma* real.log_le_log
- \- *lemma* real.log_lt_log
- \- *lemma* real.log_lt_log_iff
- \- *lemma* real.log_mul
- \- *lemma* real.log_ne_zero_of_pos_of_ne_one
- \- *lemma* real.log_neg
- \- *lemma* real.log_neg_eq_log
- \- *lemma* real.log_neg_iff
- \- *lemma* real.log_nonneg
- \- *lemma* real.log_nonneg_iff
- \- *lemma* real.log_nonpos
- \- *lemma* real.log_nonpos_iff'
- \- *lemma* real.log_nonpos_iff
- \- *lemma* real.log_of_ne_zero
- \- *lemma* real.log_of_pos
- \- *lemma* real.log_one
- \- *lemma* real.log_pos
- \- *lemma* real.log_pos_iff
- \- *lemma* real.log_surjective
- \- *lemma* real.log_zero
- \- *lemma* real.map_exp_at_bot
- \- *lemma* real.map_exp_at_top
- \- *lemma* real.range_exp
- \- *lemma* real.range_log
- \- *lemma* real.strict_anti_on_log
- \- *lemma* real.strict_mono_on_log
- \- *lemma* real.surj_on_log'
- \- *lemma* real.surj_on_log
- \- *lemma* real.tendsto_comp_exp_at_bot
- \- *lemma* real.tendsto_comp_exp_at_top
- \- *lemma* real.tendsto_div_pow_mul_exp_add_at_top
- \- *lemma* real.tendsto_exp_at_bot
- \- *lemma* real.tendsto_exp_at_bot_nhds_within
- \- *lemma* real.tendsto_exp_at_top
- \- *lemma* real.tendsto_exp_comp_at_top
- \- *lemma* real.tendsto_exp_div_pow_at_top
- \- *lemma* real.tendsto_exp_neg_at_top_nhds_0
- \- *lemma* real.tendsto_exp_nhds_0_nhds_1
- \- *lemma* real.tendsto_log_at_top
- \- *lemma* real.tendsto_log_nhds_within_zero
- \- *lemma* real.tendsto_mul_exp_add_div_pow_at_top
- \- *lemma* real.tendsto_mul_log_one_plus_div_at_top
- \- *lemma* real.tendsto_pow_mul_exp_neg_at_top_nhds_0
- \- *lemma* real.times_cont_diff_at_log
- \- *lemma* real.times_cont_diff_exp
- \- *lemma* real.times_cont_diff_on_log
- \- *lemma* times_cont_diff.cexp
- \- *lemma* times_cont_diff.exp
- \- *lemma* times_cont_diff.log
- \- *lemma* times_cont_diff_at.cexp
- \- *lemma* times_cont_diff_at.exp
- \- *lemma* times_cont_diff_at.log
- \- *lemma* times_cont_diff_on.cexp
- \- *lemma* times_cont_diff_on.exp
- \- *lemma* times_cont_diff_on.log
- \- *lemma* times_cont_diff_within_at.cexp
- \- *lemma* times_cont_diff_within_at.exp
- \- *lemma* times_cont_diff_within_at.log

Added src/analysis/special_functions/log.lean
- \+ *lemma* continuous.log
- \+ *lemma* continuous_at.log
- \+ *lemma* continuous_on.log
- \+ *lemma* continuous_within_at.log
- \+ *lemma* filter.tendsto.log
- \+ *lemma* real.continuous_at_log
- \+ *lemma* real.continuous_at_log_iff
- \+ *lemma* real.continuous_log'
- \+ *lemma* real.continuous_log
- \+ *lemma* real.continuous_on_log
- \+ *lemma* real.eq_one_of_pos_of_log_eq_zero
- \+ *lemma* real.exp_log
- \+ *lemma* real.exp_log_eq_abs
- \+ *lemma* real.exp_log_of_neg
- \+ *lemma* real.log_abs
- \+ *lemma* real.log_div
- \+ *lemma* real.log_eq_zero
- \+ *lemma* real.log_exp
- \+ *lemma* real.log_inj_on_pos
- \+ *lemma* real.log_inv
- \+ *lemma* real.log_le_log
- \+ *lemma* real.log_lt_log
- \+ *lemma* real.log_lt_log_iff
- \+ *lemma* real.log_mul
- \+ *lemma* real.log_ne_zero_of_pos_of_ne_one
- \+ *lemma* real.log_neg
- \+ *lemma* real.log_neg_eq_log
- \+ *lemma* real.log_neg_iff
- \+ *lemma* real.log_nonneg
- \+ *lemma* real.log_nonneg_iff
- \+ *lemma* real.log_nonpos
- \+ *lemma* real.log_nonpos_iff'
- \+ *lemma* real.log_nonpos_iff
- \+ *lemma* real.log_of_ne_zero
- \+ *lemma* real.log_of_pos
- \+ *lemma* real.log_one
- \+ *lemma* real.log_pos
- \+ *lemma* real.log_pos_iff
- \+ *lemma* real.log_surjective
- \+ *lemma* real.log_zero
- \+ *lemma* real.range_log
- \+ *lemma* real.strict_anti_on_log
- \+ *lemma* real.strict_mono_on_log
- \+ *lemma* real.surj_on_log'
- \+ *lemma* real.surj_on_log
- \+ *lemma* real.tendsto_log_at_top
- \+ *lemma* real.tendsto_log_nhds_within_zero

Added src/analysis/special_functions/log_deriv.lean
- \+ *lemma* deriv.log
- \+ *lemma* deriv_within.log
- \+ *lemma* differentiable.log
- \+ *lemma* differentiable_at.log
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* fderiv.log
- \+ *lemma* fderiv_within.log
- \+ *lemma* has_deriv_at.log
- \+ *lemma* has_deriv_within_at.log
- \+ *lemma* has_fderiv_at.log
- \+ *lemma* has_fderiv_within_at.log
- \+ *lemma* has_strict_deriv_at.log
- \+ *lemma* has_strict_fderiv_at.log
- \+ *lemma* real.abs_log_sub_add_sum_range_le
- \+ *lemma* real.deriv_log'
- \+ *lemma* real.deriv_log
- \+ *lemma* real.differentiable_at_log
- \+ *lemma* real.differentiable_at_log_iff
- \+ *lemma* real.differentiable_on_log
- \+ *lemma* real.has_deriv_at_log
- \+ *lemma* real.has_strict_deriv_at_log
- \+ *lemma* real.has_strict_deriv_at_log_of_pos
- \+ *theorem* real.has_sum_pow_div_log_of_abs_lt_1
- \+ *lemma* real.tendsto_mul_log_one_plus_div_at_top
- \+ *lemma* real.times_cont_diff_at_log
- \+ *lemma* real.times_cont_diff_on_log
- \+ *lemma* times_cont_diff.log
- \+ *lemma* times_cont_diff_at.log
- \+ *lemma* times_cont_diff_on.log
- \+ *lemma* times_cont_diff_within_at.log

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/data/complex/exponential_bounds.lean
- \+/\- *lemma* real.exp_one_near_10
- \+/\- *lemma* real.exp_one_near_20
- \+/\- *lemma* real.log_two_near_10

Modified test/differentiable.lean


Modified test/library_search/exp_le_exp.lean




## [2021-10-23 22:10:44](https://github.com/leanprover-community/mathlib/commit/59db903)
feat(topology/metric_space/lipschitz): continuity on product of continuity in 1 var and Lipschitz continuity in another ([#9758](https://github.com/leanprover-community/mathlib/pull/9758))
Also apply the new lemma to `continuous_bounded_map`s and add a few lemmas there.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.continuous_coe
- \+ *lemma* bounded_continuous_function.lipschitz_evalx
- \+ *theorem* bounded_continuous_function.uniform_continuous_coe

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* continuous_on_prod_of_continuous_on_lipschitz_on
- \+ *lemma* continuous_prod_of_continuous_lipschitz
- \+ *lemma* lipschitz_on_with.edist_lt_of_edist_lt_div
- \+ *lemma* lipschitz_with.edist_lt_of_edist_lt_div



## [2021-10-23 20:04:35](https://github.com/leanprover-community/mathlib/commit/939e8b9)
docs(control/traversable/instances): Add module docstring ([#9913](https://github.com/leanprover-community/mathlib/pull/9913))
#### Estimated changes
Modified src/control/traversable/instances.lean




## [2021-10-23 20:04:34](https://github.com/leanprover-community/mathlib/commit/14b998b)
docs(control/bifunctor): Add module and defs docstrings ([#9911](https://github.com/leanprover-community/mathlib/pull/9911))
#### Estimated changes
Modified src/control/bifunctor.lean
- \+/\- *def* bifunctor.fst
- \+/\- *def* bifunctor.snd



## [2021-10-23 20:04:33](https://github.com/leanprover-community/mathlib/commit/78252a3)
chore(data/real/sqrt): A couple of lemmas about sqrt ([#9892](https://github.com/leanprover-community/mathlib/pull/9892))
Add a couple of lemmas about `sqrt x / x`.
#### Estimated changes
Modified src/data/real/sqrt.lean
- \+ *theorem* real.sqrt_div_self'
- \+ *theorem* real.sqrt_div_self



## [2021-10-23 20:04:32](https://github.com/leanprover-community/mathlib/commit/3f58dc7)
feat(linear_algebra/free_module/pid): golf basis.card_le_card_of_linear_independent_aux ([#9813](https://github.com/leanprover-community/mathlib/pull/9813))
We go from a 70 lines proof to a one line proof.
#### Estimated changes
Modified src/linear_algebra/free_module/pid.lean




## [2021-10-23 20:04:31](https://github.com/leanprover-community/mathlib/commit/fc3c056)
chore(data/real): make more instances on real, nnreal, and ennreal computable ([#9806](https://github.com/leanprover-community/mathlib/pull/9806))
This makes it possible to talk about the add_monoid structure of nnreal and ennreal without worrying about computability.
To make it clear exactly which operations are computable, we remove `noncomputable theory`.
#### Estimated changes
Modified src/algebra/order/nonneg.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_smul
- \- *def* ennreal.of_nnreal_hom

Modified src/data/real/nnreal.lean
- \- *def* real.nnabs
- \- *def* real.to_nnreal



## [2021-10-23 17:11:13](https://github.com/leanprover-community/mathlib/commit/5c5d818)
chore(data/fintype/basic): make units.fintype computable ([#9846](https://github.com/leanprover-community/mathlib/pull/9846))
This also:
* renames `equiv.units_equiv_ne_zero` to `units_equiv_ne_zero`, and resolves the TODO comment about generalization
* renames and generalizes `finite_field.card_units` to `fintype.card_units`, and proves it right next to the fintype instance
* generalizes some typeclass assumptions in `finite_field.basic` as the linter already required me to tweak them
#### Estimated changes
Modified src/data/equiv/ring.lean
- \- *lemma* equiv.coe_units_equiv_ne_zero
- \- *def* equiv.units_equiv_ne_zero

Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_subtype_eq'
- \+/\- *lemma* fintype.card_subtype_eq
- \+ *lemma* fintype.card_units
- \+ *def* units_equiv_ne_zero
- \+ *def* units_equiv_prod_subtype

Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/finite/basic.lean
- \- *lemma* finite_field.card_units
- \+/\- *lemma* finite_field.prod_univ_units_id_eq_neg_one
- \+/\- *lemma* finite_field.sum_pow_units

Modified src/field_theory/finite/polynomial.lean


Modified src/ring_theory/integral_domain.lean




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
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/calculus/parametric_integral.lean


Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* measure_theory.ae_cover.integrable_of_integral_norm_tendsto
- \+/\- *lemma* measure_theory.ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
- \+/\- *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_tendsto'
- \+/\- *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_tendsto
- \+/\- *lemma* measure_theory.ae_cover.integral_eq_of_tendsto
- \+/\- *lemma* measure_theory.ae_cover.integral_eq_of_tendsto_of_nonneg_ae
- \+/\- *lemma* measure_theory.ae_cover.integral_tendsto_of_countably_generated
- \+/\- *lemma* measure_theory.ae_cover.lintegral_eq_of_tendsto
- \+/\- *lemma* measure_theory.ae_cover.lintegral_tendsto_of_countably_generated
- \+/\- *lemma* measure_theory.ae_cover.supr_lintegral_eq_of_countably_generated

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/order/filter/archimedean.lean
- \- *lemma* at_bot_countably_generated
- \- *lemma* at_top_countably_generated_of_archimedean

Modified src/order/filter/at_top_bot.lean
- \- *lemma* filter.is_countably_generated.subseq_tendsto
- \- *lemma* filter.is_countably_generated.tendsto_iff_seq_tendsto
- \- *lemma* filter.is_countably_generated.tendsto_of_seq_tendsto
- \- *lemma* filter.is_countably_generated_at_bot
- \- *lemma* filter.is_countably_generated_at_top
- \+ *lemma* filter.subseq_tendsto_of_ne_bot
- \+ *lemma* filter.tendsto_iff_seq_tendsto
- \+ *lemma* filter.tendsto_of_seq_tendsto

Modified src/order/filter/bases.lean
- \+ *lemma* filter.exists_antitone_basis
- \+ *lemma* filter.exists_antitone_eq_infi_principal
- \+ *lemma* filter.exists_antitone_seq
- \+ *lemma* filter.has_basis.exists_antitone_subbasis
- \- *def* filter.is_countably_generated.countable_filter_basis
- \- *lemma* filter.is_countably_generated.countable_generating_set
- \- *lemma* filter.is_countably_generated.eq_generate
- \- *lemma* filter.is_countably_generated.exists_antitone_basis
- \- *lemma* filter.is_countably_generated.exists_antitone_seq'
- \- *lemma* filter.is_countably_generated.exists_antitone_subbasis
- \- *lemma* filter.is_countably_generated.exists_countable_infi_principal
- \- *lemma* filter.is_countably_generated.exists_seq
- \- *lemma* filter.is_countably_generated.filter_basis_filter
- \- *def* filter.is_countably_generated.generating_set
- \- *lemma* filter.is_countably_generated.has_countable_basis
- \- *lemma* filter.is_countably_generated.inf
- \- *lemma* filter.is_countably_generated.inf_principal
- \- *def* filter.is_countably_generated
- \+ *lemma* filter.is_countably_generated_bot
- \+/\- *lemma* filter.is_countably_generated_principal
- \+/\- *lemma* filter.is_countably_generated_seq
- \+ *lemma* filter.is_countably_generated_top

Modified src/order/filter/basic.lean
- \+ *lemma* filter.generate_eq_binfi

Modified src/topology/G_delta.lean
- \+/\- *lemma* is_Gδ_set_of_continuous_at
- \- *lemma* is_Gδ_set_of_continuous_at_of_countably_generated_uniformity
- \- *lemma* is_closed.is_Gδ'
- \+/\- *lemma* is_closed.is_Gδ

Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* is_glb.exists_seq_antitone_tendsto'
- \+/\- *lemma* is_glb.exists_seq_antitone_tendsto
- \- *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem'
- \+/\- *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem
- \- *lemma* is_lub.exists_seq_monotone_tendsto'
- \+/\- *lemma* is_lub.exists_seq_monotone_tendsto
- \- *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem'
- \+/\- *lemma* is_lub.exists_seq_strict_mono_tendsto_of_not_mem

Modified src/topology/bases.lean
- \- *lemma* topological_space.is_countably_generated_nhds
- \- *lemma* topological_space.is_countably_generated_nhds_within

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \- *lemma* emetric.second_countable_of_separable
- \- *theorem* emetric.uniformity_has_countable_basis

Modified src/topology/sequences.lean
- \+/\- *lemma* lebesgue_number_lemma_seq
- \- *lemma* metric.compact_iff_seq_compact
- \- *lemma* metric.compact_space_iff_seq_compact_space
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_space.has_seq_basis

Modified src/topology/uniform_space/cauchy.lean




## [2021-10-23 17:11:11](https://github.com/leanprover-community/mathlib/commit/d0d1520)
chore(ring_theory/derivation): add `leibniz_pow` and `leibniz_inv` ([#9837](https://github.com/leanprover-community/mathlib/pull/9837))
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+ *lemma* derivation.leibniz_inv
- \+ *lemma* derivation.leibniz_inv_of
- \+ *lemma* derivation.leibniz_of_mul_eq_one
- \+ *lemma* derivation.leibniz_pow



## [2021-10-23 17:11:09](https://github.com/leanprover-community/mathlib/commit/1ebea89)
feat(field_theory/finite/galois_field): finite fields with the same cardinality are isomorphic ([#9834](https://github.com/leanprover-community/mathlib/pull/9834))
Added the isomorphism of finite fields of the same cardinality.
#### Estimated changes
Modified src/field_theory/finite/galois_field.lean
- \+ *def* finite_field.alg_equiv_of_card_eq
- \+ *def* finite_field.ring_equiv_of_card_eq



## [2021-10-23 17:11:08](https://github.com/leanprover-community/mathlib/commit/0411b1e)
feat(ring_theory/ideal): `simp` lemmas for `ideal.quotient.mk` + `algebra_map` ([#9829](https://github.com/leanprover-community/mathlib/pull/9829))
Some `simp` lemmas I needed for combining `algebra_map` with `ideal.quotient.mk`. This also allowed me to golf two existing proofs.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.quotient.algebra_map_eq
- \+ *lemma* ideal.quotient.mk_algebra_map
- \+ *lemma* ideal.quotient.mk_comp_algebra_map
- \+ *lemma* ideal.quotient_map_algebra_map



## [2021-10-23 17:11:07](https://github.com/leanprover-community/mathlib/commit/44ab28e)
refactor(linear_algebra/free_module/finite): move to a new folder ([#9821](https://github.com/leanprover-community/mathlib/pull/9821))
We move `linear_algebra/free_module/finite` to `linear_algebra/free_module/finite/basic`.
We also move two lemmas from `linear_algebra/free_module/finite/basic` to `linear_algebra/free_module/basic`, since they don't need any finiteness assumption on the modules.
#### Estimated changes
Modified src/linear_algebra/charpoly/basic.lean


Modified src/linear_algebra/free_module/basic.lean


Renamed src/linear_algebra/free_module/finite.lean to src/linear_algebra/free_module/finite/basic.lean




## [2021-10-23 14:30:44](https://github.com/leanprover-community/mathlib/commit/a58ae54)
chore(algebra/big_operators/finprod): remove outdated todo ([#9900](https://github.com/leanprover-community/mathlib/pull/9900))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean




## [2021-10-23 14:30:43](https://github.com/leanprover-community/mathlib/commit/bd81d55)
feat(data/finsupp): add lemmas about `single` ([#9894](https://github.com/leanprover-community/mathlib/pull/9894))
These are subset versions of the four lemmas related to `support_eq_singleton`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.card_support_le_one'
- \+ *lemma* finsupp.card_support_le_one
- \+ *lemma* finsupp.support_subset_singleton'
- \+ *lemma* finsupp.support_subset_singleton



## [2021-10-23 14:30:42](https://github.com/leanprover-community/mathlib/commit/95535a3)
refactor(ring_theory/unique_factorization_domain): golf some factor_set lemmas ([#9889](https://github.com/leanprover-community/mathlib/pull/9889))
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* associates.factor_set.prod_eq_zero_iff
- \+ *theorem* associates.factor_set.unique
- \+/\- *theorem* associates.factors'_cong
- \+/\- *theorem* associates.prod_factors



## [2021-10-23 14:30:41](https://github.com/leanprover-community/mathlib/commit/e1c0dbc)
feat(set_theory/cardinal): add `add_le_omega` ([#9887](https://github.com/leanprover-community/mathlib/pull/9887))
* simplify `c₁ + c₂ ≤ ω` to `c₁ ≤ ω ∧ c₂ ≤ ω`;
* simplify `ω + ω` to `ω`;
* simplify `#s ≤ ω` to `s.countable`;
* simplify `(s ∪ t).countable` and `(insert a s).countable`.
Motivated by lemmas from flypitch.
#### Estimated changes
Modified src/data/real/cardinality.lean


Modified src/data/set/countable.lean
- \+ *lemma* set.countable_insert
- \+ *lemma* set.countable_union

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.add_le_omega
- \- *lemma* cardinal.countable_iff
- \+ *lemma* cardinal.mk_set_le_omega
- \+ *lemma* cardinal.mk_union_le_omega
- \+ *lemma* cardinal.omega_add_omega
- \+ *lemma* cardinal.omega_mul_omega

Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.succ_omega

Modified src/set_theory/cofinality.lean
- \+ *lemma* cardinal.is_regular.ord_pos
- \+ *lemma* cardinal.is_regular.pos



## [2021-10-23 14:30:40](https://github.com/leanprover-community/mathlib/commit/82896b5)
feat(topology): add a few lemmas ([#9885](https://github.com/leanprover-community/mathlib/pull/9885))
Add `is_topological_basis.is_open_map_iff`,
`is_topological_basis.exists_nonempty_subset`, and
`interior_{s,b,}Inter_subset`.
Motivated by lemmas from `flypitch`.
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* topological_space.is_topological_basis.exists_nonempty_subset
- \+ *lemma* topological_space.is_topological_basis.is_open_map_iff

Modified src/topology/basic.lean
- \+ *lemma* interior_Inter_subset
- \+ *lemma* interior_bInter_subset
- \+ *lemma* interior_sInter_subset



## [2021-10-23 14:30:39](https://github.com/leanprover-community/mathlib/commit/1e0661c)
feat(ring_theory/noetherian): generalize to semiring ([#9881](https://github.com/leanprover-community/mathlib/pull/9881))
We generalize some of the results in `ring_theory/noetherian` to `semiring`.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* module.finite.of_injective

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* fg_of_injective
- \+ *lemma* fg_of_ker_bot
- \+/\- *lemma* is_noetherian_of_injective
- \+ *lemma* is_noetherian_of_ker_bot
- \+ *lemma* submodule.fg_of_fg_map_injective
- \+/\- *lemma* submodule.fg_top



## [2021-10-23 14:30:38](https://github.com/leanprover-community/mathlib/commit/bb71667)
feat(topology/instances/irrational): new file ([#9872](https://github.com/leanprover-community/mathlib/pull/9872))
* move `is_Gδ_irrational` etc to a new file `topology.instances.irrational`;
* prove that a small ball around an irrational number is disjoint with the set of rational numbers with bounded denominators;
* prove `order_topology`, `no_top_order`, `no_bot_order`, and `densely_ordered` instances for `{x // irrational x}`.
#### Estimated changes
Modified src/number_theory/liouville/residual.lean
- \- *lemma* dense_irrational
- \- *lemma* eventually_residual_irrational
- \- *lemma* is_Gδ_irrational

Added src/topology/instances/irrational.lean
- \+ *lemma* dense_irrational
- \+ *lemma* eventually_residual_irrational
- \+ *lemma* irrational.eventually_forall_le_dist_cast_div
- \+ *lemma* irrational.eventually_forall_le_dist_cast_div_of_denom_le
- \+ *lemma* irrational.eventually_forall_le_dist_cast_rat_of_denom_le
- \+ *lemma* is_Gδ_irrational



## [2021-10-23 14:30:37](https://github.com/leanprover-community/mathlib/commit/b877f6b)
chore(analysis/normed/group): generalize `cauchy_seq.add` ([#9868](https://github.com/leanprover-community/mathlib/pull/9868))
Also golf a few proofs.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \- *lemma* cauchy_seq.add
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_pos_iff

Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* cauchy_seq.add



## [2021-10-23 14:30:36](https://github.com/leanprover-community/mathlib/commit/29c7266)
refactor(linear_algebra/matrix/nonsingular_inverse): use ring.inverse in matrix.has_inv ([#9863](https://github.com/leanprover-community/mathlib/pull/9863))
This makes some of the proofs a little shorter.
Independently, this removes an assumption from `matrix.transpose_nonsing_inv`.
This adds the missing `units.is_unit_units_mul` to complement the existing `units.is_unit_mul_units`, even though it ultimately was not used in this PR.
This removes the def `matrix.nonsing_inv` in favor of just using `has_inv.inv` directly. Having two ways to spell the same thing isn't helpful here.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/group/units.lean
- \+ *theorem* units.is_unit_units_mul

Modified src/algebra/ring/basic.lean
- \+ *lemma* ring.mul_inverse_rev

Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/matrix/fpow.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* matrix.inv_def
- \+/\- *lemma* matrix.transpose_nonsing_inv



## [2021-10-23 14:30:35](https://github.com/leanprover-community/mathlib/commit/2a1f454)
refactor(algebra/algebra): choose `coe` as the normal form for the map `alg_equiv → ring_equiv` ([#9848](https://github.com/leanprover-community/mathlib/pull/9848))
We never chose a `simp`-normal form for this map, resulting in some duplicate work and annoying `show _ = _, from rfl` when rewriting. I picked this choice because it matches the convention for the map `alg_hom → ring_hom`.
Very surprisingly, there were absolutely no CI failures due to this choice.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* alg_equiv.coe_ring_equiv'
- \+ *lemma* alg_equiv.to_ring_equiv_eq_coe



## [2021-10-23 14:30:34](https://github.com/leanprover-community/mathlib/commit/5f11361)
refactor(algebra/continued_fractions): remove use of open ... as ([#9847](https://github.com/leanprover-community/mathlib/pull/9847))
Lean 4 doesn't support the use of `open ... as ...`, so let's get rid of the few uses from mathlib rather than automating it in mathport.
#### Estimated changes
Modified src/algebra/continued_fractions/basic.lean
- \+/\- *lemma* continued_fraction.coe_to_generalized_continued_fraction
- \+/\- *lemma* continued_fraction.coe_to_simple_continued_fraction
- \+/\- *def* continued_fraction.of_integer
- \+/\- *lemma* generalized_continued_fraction.coe_to_generalized_continued_fraction
- \+/\- *def* generalized_continued_fraction.continuants
- \+/\- *def* generalized_continued_fraction.continuants_aux
- \+/\- *def* generalized_continued_fraction.convergents'
- \+/\- *def* generalized_continued_fraction.convergents'_aux
- \+/\- *def* generalized_continued_fraction.convergents
- \+/\- *def* generalized_continued_fraction.denominators
- \+/\- *def* generalized_continued_fraction.next_continuants
- \+/\- *def* generalized_continued_fraction.numerators
- \+/\- *def* generalized_continued_fraction.of_integer
- \+/\- *def* generalized_continued_fraction.pair.map
- \+/\- *def* generalized_continued_fraction.partial_denominators
- \+/\- *def* generalized_continued_fraction.partial_numerators
- \+/\- *def* generalized_continued_fraction.terminated_at
- \+/\- *def* generalized_continued_fraction.terminates
- \+/\- *lemma* simple_continued_fraction.coe_to_generalized_continued_fraction
- \+/\- *def* simple_continued_fraction.of_integer

Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean
- \+/\- *lemma* generalized_continued_fraction.of_convergents_eq_convergents'

Modified src/algebra/continued_fractions/computation/approximations.lean
- \+/\- *theorem* generalized_continued_fraction.abs_sub_convergents_le
- \+/\- *lemma* generalized_continued_fraction.determinant
- \+/\- *lemma* generalized_continued_fraction.determinant_aux
- \+/\- *lemma* generalized_continued_fraction.fib_le_of_continuants_aux_b
- \+/\- *theorem* generalized_continued_fraction.of_denom_mono
- \+/\- *lemma* generalized_continued_fraction.of_part_num_eq_one
- \+/\- *lemma* generalized_continued_fraction.of_part_num_eq_one_and_exists_int_part_denom_eq
- \+/\- *lemma* generalized_continued_fraction.succ_nth_fib_le_of_nth_denom
- \+/\- *lemma* generalized_continued_fraction.zero_le_of_continuants_aux_b
- \+/\- *lemma* generalized_continued_fraction.zero_le_of_denom

Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean
- \+/\- *lemma* generalized_continued_fraction.of_correctness_at_top_of_terminates
- \+/\- *theorem* generalized_continued_fraction.of_correctness_of_terminated_at
- \+/\- *lemma* generalized_continued_fraction.of_correctness_of_terminates

Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean
- \+/\- *lemma* generalized_continued_fraction.coe_of_h_rat_eq
- \+/\- *lemma* generalized_continued_fraction.coe_of_rat_eq
- \+/\- *lemma* generalized_continued_fraction.coe_of_s_rat_eq
- \+/\- *lemma* generalized_continued_fraction.exists_rat_eq_nth_convergent
- \+/\- *lemma* generalized_continued_fraction.exists_rat_eq_nth_denominator
- \+/\- *lemma* generalized_continued_fraction.exists_rat_eq_nth_numerator
- \+/\- *theorem* generalized_continued_fraction.exists_rat_eq_of_terminates
- \+/\- *theorem* generalized_continued_fraction.terminates_iff_rat
- \+/\- *theorem* generalized_continued_fraction.terminates_of_rat

Modified src/algebra/continued_fractions/computation/translations.lean
- \+/\- *lemma* generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some
- \+/\- *lemma* generalized_continued_fraction.of_h_eq_floor
- \+/\- *lemma* generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b

Modified src/algebra/continued_fractions/continuants_recurrence.lean
- \+/\- *lemma* generalized_continued_fraction.continuants_aux_recurrence
- \+/\- *theorem* generalized_continued_fraction.continuants_recurrence
- \+/\- *lemma* generalized_continued_fraction.continuants_recurrence_aux
- \+/\- *lemma* generalized_continued_fraction.denominators_recurrence
- \+/\- *lemma* generalized_continued_fraction.numerators_recurrence

Modified src/algebra/continued_fractions/convergents_equiv.lean
- \+/\- *theorem* continued_fraction.convergents_eq_convergents'
- \+/\- *def* generalized_continued_fraction.squash_gcf
- \+/\- *def* generalized_continued_fraction.squash_seq
- \+/\- *lemma* generalized_continued_fraction.squash_seq_nth_of_not_terminated

Modified src/algebra/continued_fractions/terminated_stable.lean
- \+/\- *lemma* generalized_continued_fraction.convergents'_aux_stable_of_terminated
- \+/\- *lemma* generalized_continued_fraction.convergents'_aux_stable_step_of_terminated

Modified src/algebra/continued_fractions/translations.lean
- \+/\- *lemma* generalized_continued_fraction.first_continuant_eq
- \+/\- *lemma* generalized_continued_fraction.first_denominator_eq
- \+/\- *lemma* generalized_continued_fraction.first_numerator_eq
- \+/\- *lemma* generalized_continued_fraction.part_denom_eq_s_b
- \+/\- *lemma* generalized_continued_fraction.part_num_eq_s_a
- \+/\- *lemma* generalized_continued_fraction.second_continuant_aux_eq
- \+/\- *lemma* generalized_continued_fraction.zeroth_convergent'_aux_eq_zero



## [2021-10-23 13:13:59](https://github.com/leanprover-community/mathlib/commit/7b979aa)
move(algebra/order/*): More algebraic order files in the correct place ([#9899](https://github.com/leanprover-community/mathlib/pull/9899))
`algebra.module.ordered` and `algebra.algebra.ordered` were really continuations of `algebra.order.smul` (the first being quite literally the same with additive inverses), so it makes sense to bring them closer. `algebra.floor` and `algebra.archimedean` also perfectly qualify for the subfolder.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/basic.lean


Renamed src/algebra/algebra/ordered.lean to src/algebra/order/algebra.lean


Renamed src/algebra/archimedean.lean to src/algebra/order/archimedean.lean


Renamed src/algebra/floor.lean to src/algebra/order/floor.lean


Renamed src/algebra/module/ordered.lean to src/algebra/order/module.lean


Modified src/algebra/order/nonneg.lean


Modified src/algebra/periodic.lean


Modified src/algebra/star/chsh.lean


Modified src/analysis/convex/basic.lean


Modified src/data/complex/module.lean


Modified src/data/rat/floor.lean


Modified src/data/real/basic.lean


Modified src/data/real/pointwise.lean


Modified src/group_theory/archimedean.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/order/filter/archimedean.lean


Modified src/topology/algebra/floor_ring.lean




## [2021-10-23 08:22:49](https://github.com/leanprover-community/mathlib/commit/eb1e037)
doc(algebra/ring): correct docs for surjective pushforwards ([#9896](https://github.com/leanprover-community/mathlib/pull/9896))
#### Estimated changes
Modified src/algebra/ring/basic.lean




## [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/a75f762)
feat(ring_theory/localization): generalize `exist_integer_multiples` to finite families ([#9859](https://github.com/leanprover-community/mathlib/pull/9859))
This PR shows we can clear denominators of finitely-indexed collections of fractions (i.e. elements of `S` where `is_localization M S`), with the existing result about finite sets of fractions as a special case.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.exist_integer_multiples
- \+ *lemma* is_localization.exist_integer_multiples_of_fintype



## [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/294ce35)
fix(algebra/module/submodule): fix incorrectly generalized arguments to `smul_mem_iff'` and `smul_of_tower_mem` ([#9851](https://github.com/leanprover-community/mathlib/pull/9851))
These put unnecessary requirements on `S`.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+/\- *lemma* submodule.coe_smul_of_tower
- \+/\- *lemma* submodule.smul_mem_iff'
- \+/\- *lemma* submodule.smul_of_tower_mem

Modified src/group_theory/group_action/sub_mul_action.lean
- \+/\- *lemma* sub_mul_action.smul_mem_iff'
- \+/\- *lemma* sub_mul_action.smul_of_tower_mem

Modified src/topology/algebra/module.lean




## [2021-10-23 08:22:47](https://github.com/leanprover-community/mathlib/commit/2cbd4ba)
feat(group_theory/index): `relindex_dvd_of_le_left` ([#9835](https://github.com/leanprover-community/mathlib/pull/9835))
If `H ≤ K`, then `K.relindex L ∣ H.relindex L`.
Caution: `relindex_dvd_of_le_right` is not true. `relindex_le_of_le_right` is true, but it is harder to prove, and harder to state (because you have to be careful about `relindex = 0`).
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.inf_relindex_left
- \+ *lemma* subgroup.inf_relindex_right
- \+ *lemma* subgroup.relindex_dvd_of_le_left



## [2021-10-23 05:53:41](https://github.com/leanprover-community/mathlib/commit/183b8c8)
refactor(data/list/defs): move defs about rb_map ([#9844](https://github.com/leanprover-community/mathlib/pull/9844))
There is nothing intrinsically `meta` about `rb_map`, but in practice in mathlib we prove nothing about it and only use it in tactic infrastructure. This PR moves a definition involving `rb_map` out of `data.list.defs` and into `meta.rb_map` (where many others already exist).
(motivated by mathport; rb_map is of course disappearing/changing, so better to quarantine this stuff off with other things that aren't being automatically ported)
`rbmap` is not related to `rb_map`. It can likely be moved from core to mathlib entirely.
#### Estimated changes
Modified src/data/list/defs.lean
- \+/\- *def* list.to_rbmap

Modified src/meta/rb_map.lean




## [2021-10-23 02:55:56](https://github.com/leanprover-community/mathlib/commit/45ba2ad)
chore(scripts): update nolints.txt ([#9895](https://github.com/leanprover-community/mathlib/pull/9895))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-10-22 22:06:02](https://github.com/leanprover-community/mathlib/commit/7690e0a)
chore(order/complete_lattice): add `(supr|infi)_option_elim` ([#9886](https://github.com/leanprover-community/mathlib/pull/9886))
Motivated by `supr_option'` and `infi_option'` from `flypitch`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* infi_option_elim
- \+ *lemma* supr_option_elim



## [2021-10-22 20:15:57](https://github.com/leanprover-community/mathlib/commit/72c20fa)
feat(analysis/special_functions/exp_log): Classify when log is zero ([#9815](https://github.com/leanprover-community/mathlib/pull/9815))
Classify when the real `log` function is zero.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.log_eq_zero



## [2021-10-22 15:58:28](https://github.com/leanprover-community/mathlib/commit/d23b833)
chore(data/set/lattice): add `@[simp]` to a few lemmas ([#9883](https://github.com/leanprover-community/mathlib/pull/9883))
Add `@[simp]` to `Union_subset_iff`, `subset_Inter_iff`,
`sUnion_subset_iff`, and `subset_sInter_iff` (new lemma).
#### Estimated changes
Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Union_subset_iff
- \+/\- *theorem* set.sUnion_subset_iff
- \+/\- *theorem* set.subset_Inter_iff
- \+ *theorem* set.subset_sInter_iff



## [2021-10-22 15:58:26](https://github.com/leanprover-community/mathlib/commit/3d237db)
feat(linear_algebra/matrix/determinant): det_conj_transpose ([#9879](https://github.com/leanprover-community/mathlib/pull/9879))
Also:
* Makes the arguments of `ring_hom.map_det` and `alg_hom.map_det` explicit, and removes them from the `matrix` namespace to enable dot notation.
* Adds `ring_equiv.map_det` and `alg_equiv.map_det`
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* alg_equiv.map_det
- \+ *lemma* alg_hom.map_det
- \- *lemma* matrix.alg_hom.map_det
- \+ *lemma* matrix.det_conj_transpose
- \- *lemma* matrix.ring_hom.map_det
- \+ *lemma* ring_equiv.map_det
- \+ *lemma* ring_hom.map_det

Modified src/ring_theory/trace.lean




## [2021-10-22 15:58:25](https://github.com/leanprover-community/mathlib/commit/20bb02f)
feat(data/fintype/basic): `fintype.card_pos` ([#9876](https://github.com/leanprover-community/mathlib/pull/9876))
Two lemmas `fintype.card_pos` and `fintype.card_ne_zero` that are often easier to use than `fintype.card_pos_iff`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_ne_zero
- \+ *lemma* fintype.card_pos



## [2021-10-22 15:58:24](https://github.com/leanprover-community/mathlib/commit/22c7474)
feat(algebra/module/basic): a few more instances ([#9871](https://github.com/leanprover-community/mathlib/pull/9871))
* generalize `is_scalar_tower.rat`;
* add `smul_comm_class.rat` and `smul_comm_class.rat'`;
* golf a few proofs.
#### Estimated changes
Modified src/algebra/algebra/tower.lean


Modified src/algebra/module/basic.lean




## [2021-10-22 15:58:23](https://github.com/leanprover-community/mathlib/commit/87ea780)
chore(set_theory/cardinal): use `protected` instead of `private` ([#9869](https://github.com/leanprover-community/mathlib/pull/9869))
Also use `mk_congr`.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.mk_emptyc



## [2021-10-22 15:58:21](https://github.com/leanprover-community/mathlib/commit/d8b9259)
feat(*): add various divisibility-related lemmas ([#9866](https://github.com/leanprover-community/mathlib/pull/9866))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* associates.mk_ne_zero
- \+ *lemma* irreducible.dvd_irreducible_iff_associated
- \+ *theorem* prime.dvd_prime_iff_associated

Modified src/algebra/ring/basic.lean
- \+ *lemma* is_unit.neg_iff

Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.eq_of_associated_of_nonneg
- \+ *lemma* int.nonneg_iff_normalize_eq_self
- \+ *lemma* int.nonneg_of_normalize_eq_self

Modified src/ring_theory/prime.lean
- \+ *lemma* prime.abs
- \+ *lemma* prime.neg



## [2021-10-22 15:58:20](https://github.com/leanprover-community/mathlib/commit/2955306)
feat(ring_theory/finiteness): generalize module.finite to noncommutative setting ([#9860](https://github.com/leanprover-community/mathlib/pull/9860))
An almost for free generalization of `module.finite` to `semiring`.
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+/\- *def* algebra.finite_presentation
- \+/\- *lemma* module.finite.of_injective
- \+/\- *lemma* module.finite.of_restrict_scalars_finite
- \+/\- *lemma* module.finite.trans
- \+/\- *lemma* module.finite_def



## [2021-10-22 15:58:19](https://github.com/leanprover-community/mathlib/commit/0a7f448)
chore(group_theory/congruence): lower priority for `con.quotient.decidable_eq` ([#9826](https://github.com/leanprover-community/mathlib/pull/9826))
I was debugging some slow typeclass searches, and it turns out (`add_`)`con.quotient.decidable_eq` wants to be applied to all quotient types, causing a search for a `has_mul` instance before the elaborator can try unifying the `con.to_setoid` relation with the quotient type's relation, so e.g. `decidable_eq (multiset α)` first tries going all the way up to searching for a `linear_ordered_normed_etc_field (list α)` before even trying `multiset.decidable_eq`.
Another approach would be to make `multiset` and/or `con.quotient` irreducible, but that would require a lot more work to ensure we don't break the irreducibility barrier.
#### Estimated changes
Modified src/group_theory/congruence.lean




## [2021-10-22 15:58:17](https://github.com/leanprover-community/mathlib/commit/03ba4cc)
feat(algebra/floor): Floor semirings ([#9592](https://github.com/leanprover-community/mathlib/pull/9592))
A floor semiring is a semiring equipped with a `floor` and a `ceil` function.
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *lemma* floor_semiring_unique
- \+ *lemma* int.ceil_to_nat
- \+ *lemma* int.floor_nonpos
- \+ *lemma* int.floor_to_nat
- \+/\- *def* nat.ceil
- \+/\- *lemma* nat.ceil_eq_zero
- \+/\- *lemma* nat.ceil_le
- \+/\- *lemma* nat.ceil_mono
- \+/\- *def* nat.floor
- \+ *lemma* nat.floor_eq_iff
- \+ *lemma* nat.floor_eq_on_Ico'
- \+ *lemma* nat.floor_eq_on_Ico
- \+ *lemma* nat.floor_eq_zero
- \- *lemma* nat.floor_eq_zero_iff
- \+/\- *lemma* nat.floor_le
- \+ *lemma* nat.floor_lt'
- \+ *lemma* nat.floor_lt
- \- *lemma* nat.floor_lt_iff
- \+/\- *lemma* nat.floor_mono
- \+ *lemma* nat.floor_one
- \+ *lemma* nat.gc_ceil_coe
- \+ *lemma* nat.le_floor
- \+ *lemma* nat.le_floor_iff'
- \+/\- *lemma* nat.le_floor_iff
- \- *lemma* nat.le_floor_of_le
- \+/\- *lemma* nat.lt_ceil
- \+/\- *lemma* nat.lt_floor_add_one
- \+ *lemma* nat.lt_of_floor_lt
- \+ *lemma* nat.lt_succ_floor
- \+/\- *lemma* nat.sub_one_lt_floor

Modified src/data/int/basic.lean
- \+ *lemma* int.le_to_nat_iff

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2021-10-22 13:16:18](https://github.com/leanprover-community/mathlib/commit/bee8d4a)
chore(order/filter/basic): golf a proof ([#9874](https://github.com/leanprover-community/mathlib/pull/9874))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_coe_set
- \+ *theorem* set.Inter_subtype
- \+ *lemma* set.Union_coe_set
- \+ *theorem* set.Union_subtype
- \- *lemma* set.Union_subtype

Modified src/measure_theory/measure/measure_space_def.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.mem_infi_finset

Modified src/topology/metric_space/hausdorff_dimension.lean


Modified src/topology/paracompact.lean




## [2021-10-22 13:16:16](https://github.com/leanprover-community/mathlib/commit/b812fb9)
refactor(ring_theory/ideal): split off `quotient.lean` ([#9850](https://github.com/leanprover-community/mathlib/pull/9850))
Both `ring_theory/ideal/basic.lean` and `ring_theory/ideal/operations.lean` were starting to get a bit long, so I split off the definition of `ideal.quotient` and the results that had no further dependencies.
I also went through all the imports for files depending on either `ideal/basic.lean` or `ideal/operations.lean` to check whether they shouldn't depend on `ideal/quotient.lean` instead.
#### Estimated changes
Modified src/algebra/ring_quot.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/smodeq.lean


Modified src/number_theory/basic.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/basic.lean
- \- *lemma* ideal.map_pi
- \- *def* ideal.quot_equiv_of_eq
- \- *lemma* ideal.quot_equiv_of_eq_mk
- \- *lemma* ideal.quotient.eq_zero_iff_mem
- \- *lemma* ideal.quotient.exists_inv
- \- *def* ideal.quotient.factor
- \- *lemma* ideal.quotient.factor_comp_mk
- \- *lemma* ideal.quotient.factor_mk
- \- *lemma* ideal.quotient.is_domain_iff_prime
- \- *def* ideal.quotient.lift
- \- *lemma* ideal.quotient.lift_mk
- \- *theorem* ideal.quotient.maximal_ideal_iff_is_field_quotient
- \- *theorem* ideal.quotient.maximal_of_is_field
- \- *def* ideal.quotient.mk
- \- *theorem* ideal.quotient.mk_eq_mk
- \- *lemma* ideal.quotient.mk_surjective
- \- *lemma* ideal.quotient.quotient_ring_saturate
- \- *lemma* ideal.quotient.ring_hom_ext
- \- *theorem* ideal.quotient.zero_eq_one_iff
- \- *theorem* ideal.quotient.zero_ne_one_iff
- \- *def* ideal.quotient

Modified src/ring_theory/ideal/local_ring.lean


Modified src/ring_theory/ideal/operations.lean
- \- *theorem* ideal.exists_sub_mem
- \- *theorem* ideal.exists_sub_one_mem_and_mem
- \- *def* ideal.quotient_inf_to_pi_quotient
- \- *theorem* ideal.quotient_inf_to_pi_quotient_bijective

Added src/ring_theory/ideal/quotient.lean
- \+ *theorem* ideal.exists_sub_mem
- \+ *theorem* ideal.exists_sub_one_mem_and_mem
- \+ *lemma* ideal.map_pi
- \+ *def* ideal.quot_equiv_of_eq
- \+ *lemma* ideal.quot_equiv_of_eq_mk
- \+ *lemma* ideal.quotient.eq_zero_iff_mem
- \+ *lemma* ideal.quotient.exists_inv
- \+ *def* ideal.quotient.factor
- \+ *lemma* ideal.quotient.factor_comp_mk
- \+ *lemma* ideal.quotient.factor_mk
- \+ *lemma* ideal.quotient.is_domain_iff_prime
- \+ *def* ideal.quotient.lift
- \+ *lemma* ideal.quotient.lift_mk
- \+ *theorem* ideal.quotient.maximal_ideal_iff_is_field_quotient
- \+ *theorem* ideal.quotient.maximal_of_is_field
- \+ *def* ideal.quotient.mk
- \+ *theorem* ideal.quotient.mk_eq_mk
- \+ *lemma* ideal.quotient.mk_surjective
- \+ *lemma* ideal.quotient.quotient_ring_saturate
- \+ *lemma* ideal.quotient.ring_hom_ext
- \+ *theorem* ideal.quotient.zero_eq_one_iff
- \+ *theorem* ideal.quotient.zero_ne_one_iff
- \+ *def* ideal.quotient
- \+ *def* ideal.quotient_inf_to_pi_quotient
- \+ *theorem* ideal.quotient_inf_to_pi_quotient_bijective

Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/topology/algebra/nonarchimedean/adic_topology.lean


Modified src/topology/algebra/ring.lean




## [2021-10-22 13:16:15](https://github.com/leanprover-community/mathlib/commit/e6c516d)
feat(topology/maps): Characterize open/closed maps in terms of images of interior/closure ([#9814](https://github.com/leanprover-community/mathlib/pull/9814))
Also provide the docstring for `inducing`.
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* is_closed_map.closure_image_subset
- \+ *lemma* is_closed_map_iff_closure_image
- \+ *lemma* is_open_map_iff_interior



## [2021-10-22 10:49:49](https://github.com/leanprover-community/mathlib/commit/43cd79f)
feat(data/finset/basic): Simple `finset.erase` lemmas ([#9878](https://github.com/leanprover-community/mathlib/pull/9878))
`finset.erase.singleton` and `finset.(map/image)_erase`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_singleton
- \+ *lemma* finset.image_erase
- \+ *lemma* finset.map_erase



## [2021-10-22 06:47:53](https://github.com/leanprover-community/mathlib/commit/76212e6)
feat(measure_theory/integral/set_integral): integral of a `is_R_or_C` function equals integral of real part + integral of imaginary part ([#9735](https://github.com/leanprover-community/mathlib/pull/9735))
#### Estimated changes
Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_of_real

Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.of_real
- \+ *lemma* measure_theory.integrable.re_im_iff

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* continuous_linear_map.comp_mem_ℒp'
- \+ *lemma* continuous_linear_map.comp_mem_ℒp
- \+ *lemma* lipschitz_with.comp_mem_ℒp
- \+ *lemma* measure_theory.mem_ℒp.of_comp_antilipschitz_with
- \+ *lemma* measure_theory.mem_ℒp.of_real
- \+ *lemma* measure_theory.mem_ℒp_re_im_iff

Modified src/measure_theory/function/special_functions.lean
- \+ *lemma* ae_measurable_of_re_im
- \+ *lemma* is_R_or_C.measurable_of_real
- \+ *lemma* measurable_of_re_im

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* integral_coe_re_add_coe_im
- \+ *lemma* integral_re_add_im
- \+ *lemma* set_integral_re_add_im

Modified test/measurability.lean




## [2021-10-22 01:15:49](https://github.com/leanprover-community/mathlib/commit/c4c71d2)
feat(topology): define class `[noncompact_space]` ([#9839](https://github.com/leanprover-community/mathlib/pull/9839))
#### Estimated changes
Modified src/topology/alexandroff.lean
- \+/\- *lemma* alexandroff.dense_embedding_coe
- \+/\- *lemma* alexandroff.dense_range_coe

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.diam_univ_of_noncompact
- \+ *lemma* metric.ediam_univ_eq_top_iff_noncompact
- \+ *lemma* metric.ediam_univ_of_noncompact

Modified src/topology/subset_properties.lean
- \+ *lemma* filter.cocompact_ne_bot_iff
- \- *lemma* filter.cocompact_ne_bot_tfae
- \+/\- *lemma* filter.coprod_cocompact
- \+ *lemma* noncompact_space_of_ne_bot
- \+ *lemma* not_compact_space_iff
- \+ *lemma* prod.noncompact_space_iff



## [2021-10-21 23:04:20](https://github.com/leanprover-community/mathlib/commit/6f837a6)
feat(data/polynomial): generalize and rename `polynomial.normalize_monic` ([#9853](https://github.com/leanprover-community/mathlib/pull/9853))
This PR renames `polynomial.normalize_monic` to `polynomial.monic.normalize_eq_self` (more dot notation!) and generalizes it from fields to `normalization_monoid`s.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.monic.normalize_eq_self
- \- *lemma* polynomial.normalize_monic



## [2021-10-21 23:04:19](https://github.com/leanprover-community/mathlib/commit/16a9031)
refactor(data/complex/*): replace `complex.conj` and `is_R_or_C.conj` with star ([#9640](https://github.com/leanprover-community/mathlib/pull/9640))
This PR replaces `complex.conj` and `is_R_or_C.conj` by the star operation defined in `algebra/star`. Both of these are replaced with `star_ring_aut`, which is also made available under the notation `conj` defined in the locale `complex_conjugate`. This effectively also upgrades conj from a `ring_hom` to a `ring_aut`.
Fixes [#9421](https://github.com/leanprover-community/mathlib/pull/9421)
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* star_ring_aut_apply
- \+ *lemma* star_ring_aut_self_apply

Modified src/analysis/complex/basic.lean
- \+/\- *lemma* complex.conj_cle_apply
- \+/\- *lemma* complex.continuous_conj
- \- *lemma* is_R_or_C.conj_to_complex

Modified src/analysis/complex/circle.lean
- \+/\- *lemma* coe_inv_circle_eq_conj

Modified src/analysis/complex/conformal.lean


Modified src/analysis/complex/isometry.lean


Modified src/analysis/complex/real_deriv.lean


Modified src/analysis/fourier.lean
- \+/\- *lemma* fourier_neg

Modified src/analysis/inner_product_space/basic.lean
- \+/\- *lemma* real_inner_comm

Modified src/analysis/inner_product_space/dual.lean


Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/data/complex/basic.lean
- \- *def* complex.conj
- \- *lemma* complex.conj_bijective
- \- *lemma* complex.conj_conj
- \- *lemma* complex.conj_eq_zero
- \- *lemma* complex.conj_inj
- \- *lemma* complex.conj_involutive
- \+/\- *lemma* complex.conj_of_real
- \- *lemma* complex.conj_one
- \- *lemma* complex.conj_sub

Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.abs_sq_re_add_conj'
- \+/\- *lemma* is_R_or_C.abs_sq_re_add_conj
- \- *lemma* is_R_or_C.conj_bijective
- \- *lemma* is_R_or_C.conj_conj
- \- *lemma* is_R_or_C.conj_div
- \- *lemma* is_R_or_C.conj_eq_zero
- \- *lemma* is_R_or_C.conj_inj
- \- *lemma* is_R_or_C.conj_inv
- \- *lemma* is_R_or_C.conj_involutive
- \+/\- *lemma* is_R_or_C.conj_mul_eq_norm_sq_left
- \+/\- *lemma* is_R_or_C.conj_to_real
- \+ *abbreviation* is_R_or_C.conj_to_ring_equiv
- \- *def* is_R_or_C.conj_to_ring_equiv
- \- *lemma* is_R_or_C.ring_equiv_apply

Modified src/data/complex/module.lean


Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+/\- *lemma* clifford_algebra_complex.of_complex_conj

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_conj



## [2021-10-21 20:06:24](https://github.com/leanprover-community/mathlib/commit/912039d)
feat(algebra/group_power/lemmas): Positivity of an odd/even power ([#9796](https://github.com/leanprover-community/mathlib/pull/9796))
This adds `odd.pow_nonneg` and co and `pow_right_comm`.
This also deletes `pow_odd_nonneg` and `pow_odd_pos` as they are special cases of `pow_nonneg` and `pow_pos`.
To make dot notation work, this renames `(pow/fpow)_(odd/even)_(nonneg/nonpos/pos/neg/abs)` to `(odd/even).(pow/fpow)_(nonneg/nonpos/pos/neg/abs)`
#### Estimated changes
Modified src/algebra/field_power.lean
- \- *lemma* abs_fpow_even
- \+ *lemma* even.abs_fpow
- \+ *lemma* even.fpow_abs
- \+ *lemma* even.fpow_neg
- \+ *lemma* even.fpow_nonneg
- \+ *theorem* even.fpow_pos
- \+/\- *lemma* fpow_bit0_abs
- \- *lemma* fpow_even_abs
- \- *lemma* fpow_even_neg
- \- *lemma* fpow_even_nonneg
- \- *theorem* fpow_even_pos
- \- *theorem* fpow_odd_neg
- \- *theorem* fpow_odd_nonneg
- \- *theorem* fpow_odd_nonpos
- \- *theorem* fpow_odd_pos
- \+ *theorem* odd.fpow_neg
- \+ *theorem* odd.fpow_nonneg
- \+ *theorem* odd.fpow_nonpos
- \+ *theorem* odd.fpow_pos

Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_right_comm

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* even.pow_abs
- \+ *lemma* even.pow_nonneg
- \+ *lemma* even.pow_pos
- \+ *lemma* even.pow_pos_iff
- \+ *lemma* odd.pow_neg
- \+ *lemma* odd.pow_neg_iff
- \+ *lemma* odd.pow_nonneg_iff
- \+ *lemma* odd.pow_nonpos
- \+ *lemma* odd.pow_nonpos_iff
- \+ *lemma* odd.pow_pos_iff
- \+/\- *lemma* pow_bit0_abs
- \- *lemma* pow_even_abs
- \- *theorem* pow_even_nonneg
- \- *theorem* pow_even_pos
- \- *theorem* pow_odd_neg
- \- *theorem* pow_odd_nonneg
- \- *theorem* pow_odd_nonpos
- \- *theorem* pow_odd_pos



## [2021-10-21 18:28:20](https://github.com/leanprover-community/mathlib/commit/15d4e5f)
refactor(data/real/ennreal): remove sub lemmas ([#9857](https://github.com/leanprover-community/mathlib/pull/9857))
* Remove all lemmas about subtraction on `ennreal` that are special cases of `has_ordered_sub` lemmas.
* [This](https://github.com/leanprover-community/mathlib/blob/fe5ddaf42c5d61ecc740e815d63ac38f5e94a2e8/src/data/real/ennreal.lean#L734-L795) gives a list of renamings.
* The lemmas that have a `@[simp]` attribute will be done in a separate PR
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/box_integral/integrability.lean


Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.le_sub_add_self
- \- *lemma* ennreal.lt_sub_comm
- \- *lemma* ennreal.lt_sub_iff_add_lt
- \+/\- *lemma* ennreal.mul_sub
- \- *lemma* ennreal.sub_add_self_eq_max
- \- *lemma* ennreal.sub_le_self
- \- *lemma* ennreal.sub_le_sub
- \- *lemma* ennreal.sub_le_sub_add_sub
- \- *lemma* ennreal.sub_self
- \- *lemma* ennreal.sub_zero
- \- *lemma* ennreal.zero_sub

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/content.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/regular.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/contracting.lean




## [2021-10-21 18:28:19](https://github.com/leanprover-community/mathlib/commit/5b72c4e)
feat(linear_algebra/quotient): `S.restrict_scalars.quotient` is `S.quotient` ([#9535](https://github.com/leanprover-community/mathlib/pull/9535))
This PR adds a more general module instance on submodule quotients, in order to show that `(S.restrict_scalars R).quotient` is equivalent to `S.quotient`. If we decide this instance is not a good idea, I can write it instead as `S.quotient.restrict_scalars`, but that is a bit less convenient to work with.
#### Estimated changes
Modified src/linear_algebra/quotient.lean
- \- *theorem* submodule.quotient.mk_nsmul
- \+/\- *theorem* submodule.quotient.mk_smul
- \+ *def* submodule.quotient.restrict_scalars_equiv
- \+ *lemma* submodule.quotient.restrict_scalars_equiv_mk
- \+ *lemma* submodule.quotient.restrict_scalars_equiv_symm_mk

Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean




## [2021-10-21 15:43:25](https://github.com/leanprover-community/mathlib/commit/9be8247)
feat(logic/function/embedding): add `function.embedding.option_elim` ([#9841](https://github.com/leanprover-community/mathlib/pull/9841))
* add `option.injective_iff`;
* add `function.embedding.option_elim`;
* use it in the proof of `cardinal.add_one_le_succ`;
* add `function.embedding.cardinal_le`, `cardinal.succ_pos`;
* add `@[simp]` to `cardinal.lt_succ`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* option.injective_iff

Modified src/logic/embedding.lean
- \+ *def* function.embedding.option_elim

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.add_one_le_succ
- \+/\- *theorem* cardinal.lt_succ
- \+/\- *lemma* cardinal.succ_ne_zero
- \+ *lemma* cardinal.succ_pos
- \+ *theorem* function.embedding.cardinal_le



## [2021-10-21 15:43:23](https://github.com/leanprover-community/mathlib/commit/14ec1c8)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate of a 2x2 matrix ([#9830](https://github.com/leanprover-community/mathlib/pull/9830))
Since we have `det_fin_two`, let's have `adjugate_fin_two` as well.
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_fin_two'
- \+ *lemma* matrix.adjugate_fin_two



## [2021-10-21 15:43:20](https://github.com/leanprover-community/mathlib/commit/9c240b5)
feat(analysis/inner_product_space): define `orthogonal_family` of subspaces ([#9718](https://github.com/leanprover-community/mathlib/pull/9718))
Define `orthogonal_family` on `V : ι → submodule 𝕜 E` to mean that any two vectors from distinct subspaces are orthogonal.  Prove that an orthogonal family of subspaces is `complete_lattice.independent`.
Also prove that in finite dimension an orthogonal family `V` satisifies `direct_sum.submodule_is_internal` (i.e., it provides an internal direct sum decomposition of `E`) if and only if their joint orthogonal complement is trivial, `(supr V)ᗮ = ⊥`, and that in this case, the identification of `E` with the direct sum of `V` is an isometry.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.eq_ite
- \+ *lemma* orthogonal_family.independent
- \+ *lemma* orthogonal_family.inner_right_dfinsupp
- \+ *lemma* orthogonal_family.inner_right_fintype
- \+ *def* orthogonal_family

Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *def* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family

Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* orthogonal_family.submodule_is_internal_iff



## [2021-10-21 13:16:18](https://github.com/leanprover-community/mathlib/commit/d8096aa)
fix(ring_theory/subring): `inclusion` is a ring_hom! ([#9849](https://github.com/leanprover-community/mathlib/pull/9849))
#### Estimated changes
Modified src/ring_theory/subring.lean
- \+/\- *def* subring.inclusion



## [2021-10-21 13:16:17](https://github.com/leanprover-community/mathlib/commit/d8b0d1a)
chore(algebra/big_operators): avoid 'abel' tactic ([#9833](https://github.com/leanprover-community/mathlib/pull/9833))
I'd like to add an import ` algebra.euclidean_domain` → `algebra.associated` in [#9606](https://github.com/leanprover-community/mathlib/pull/9606), so this removes the dependency in the other direction (`algebra.associated` → `algebra.big_operators.basic` → `tactic.abel` → `tactic.norm_num` → `data.rat.cast` → `data.rat.order` → `data.rat.basic` → ` algebra.euclidean_domain`). Fortunately, the dependency on `abel` was quite shallow here.
#### Estimated changes
Modified archive/oxford_invariants/2021summer/week3_p1.lean


Modified src/algebra/algebra/basic.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/homology/homotopy.lean


Modified src/algebra/module/basic.lean


Modified src/data/int/interval.lean


Modified src/data/pnat/interval.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/ring_theory/ideal/basic.lean




## [2021-10-21 13:16:16](https://github.com/leanprover-community/mathlib/commit/de13786)
chore(topology/algebra/ordered): move IVT to a new file ([#9792](https://github.com/leanprover-community/mathlib/pull/9792))
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* continuous.surjective'
- \- *lemma* continuous.surjective
- \- *lemma* continuous_on.surj_on_of_tendsto'
- \- *lemma* continuous_on.surj_on_of_tendsto
- \- *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \- *lemma* intermediate_value_Icc'
- \- *lemma* intermediate_value_Icc
- \- *lemma* intermediate_value_Ico'
- \- *lemma* intermediate_value_Ico
- \- *lemma* intermediate_value_Ioc'
- \- *lemma* intermediate_value_Ioc
- \- *lemma* intermediate_value_Ioo'
- \- *lemma* intermediate_value_Ioo
- \- *lemma* intermediate_value_interval
- \- *lemma* intermediate_value_univ
- \- *lemma* intermediate_value_univ₂
- \- *lemma* intermediate_value_univ₂_eventually₁
- \- *lemma* intermediate_value_univ₂_eventually₂
- \- *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \- *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within
- \- *lemma* is_closed.mem_of_ge_of_forall_exists_gt
- \- *lemma* is_connected.Icc_subset
- \- *lemma* is_connected.Ioo_cInf_cSup_subset
- \- *lemma* is_preconnected.Icc_subset
- \- *lemma* is_preconnected.Iio_cSup_subset
- \- *lemma* is_preconnected.Ioi_cInf_subset
- \- *lemma* is_preconnected.eq_univ_of_unbounded
- \- *lemma* is_preconnected.intermediate_value
- \- *lemma* is_preconnected.intermediate_value_Ici
- \- *lemma* is_preconnected.intermediate_value_Ico
- \- *lemma* is_preconnected.intermediate_value_Iic
- \- *lemma* is_preconnected.intermediate_value_Iii
- \- *lemma* is_preconnected.intermediate_value_Iio
- \- *lemma* is_preconnected.intermediate_value_Ioc
- \- *lemma* is_preconnected.intermediate_value_Ioi
- \- *lemma* is_preconnected.intermediate_value_Ioo
- \- *lemma* is_preconnected.intermediate_value₂
- \- *lemma* is_preconnected.intermediate_value₂_eventually₁
- \- *lemma* is_preconnected.intermediate_value₂_eventually₂
- \- *lemma* is_preconnected.mem_intervals
- \- *lemma* is_preconnected.ord_connected
- \- *lemma* is_preconnected_Icc
- \- *lemma* is_preconnected_Ici
- \- *lemma* is_preconnected_Ico
- \- *lemma* is_preconnected_Iic
- \- *lemma* is_preconnected_Iio
- \- *lemma* is_preconnected_Ioc
- \- *lemma* is_preconnected_Ioi
- \- *lemma* is_preconnected_Ioo
- \- *lemma* is_preconnected_iff_ord_connected
- \- *lemma* is_preconnected_interval
- \- *lemma* mem_range_of_exists_le_of_exists_ge
- \- *lemma* set.ord_connected.is_preconnected
- \- *lemma* set_of_is_preconnected_eq_of_ordered
- \- *lemma* set_of_is_preconnected_subset_of_ordered

Modified src/topology/algebra/ordered/compact.lean


Added src/topology/algebra/ordered/intermediate_value.lean
- \+ *lemma* continuous.surjective'
- \+ *lemma* continuous.surjective
- \+ *lemma* continuous_on.surj_on_of_tendsto'
- \+ *lemma* continuous_on.surj_on_of_tendsto
- \+ *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \+ *lemma* intermediate_value_Icc'
- \+ *lemma* intermediate_value_Icc
- \+ *lemma* intermediate_value_Ico'
- \+ *lemma* intermediate_value_Ico
- \+ *lemma* intermediate_value_Ioc'
- \+ *lemma* intermediate_value_Ioc
- \+ *lemma* intermediate_value_Ioo'
- \+ *lemma* intermediate_value_Ioo
- \+ *lemma* intermediate_value_interval
- \+ *lemma* intermediate_value_univ
- \+ *lemma* intermediate_value_univ₂
- \+ *lemma* intermediate_value_univ₂_eventually₁
- \+ *lemma* intermediate_value_univ₂_eventually₂
- \+ *lemma* is_closed.Icc_subset_of_forall_exists_gt
- \+ *lemma* is_closed.Icc_subset_of_forall_mem_nhds_within
- \+ *lemma* is_closed.mem_of_ge_of_forall_exists_gt
- \+ *lemma* is_connected.Icc_subset
- \+ *lemma* is_connected.Ioo_cInf_cSup_subset
- \+ *lemma* is_preconnected.Icc_subset
- \+ *lemma* is_preconnected.Iio_cSup_subset
- \+ *lemma* is_preconnected.Ioi_cInf_subset
- \+ *lemma* is_preconnected.eq_univ_of_unbounded
- \+ *lemma* is_preconnected.intermediate_value
- \+ *lemma* is_preconnected.intermediate_value_Ici
- \+ *lemma* is_preconnected.intermediate_value_Ico
- \+ *lemma* is_preconnected.intermediate_value_Iic
- \+ *lemma* is_preconnected.intermediate_value_Iii
- \+ *lemma* is_preconnected.intermediate_value_Iio
- \+ *lemma* is_preconnected.intermediate_value_Ioc
- \+ *lemma* is_preconnected.intermediate_value_Ioi
- \+ *lemma* is_preconnected.intermediate_value_Ioo
- \+ *lemma* is_preconnected.intermediate_value₂
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₁
- \+ *lemma* is_preconnected.intermediate_value₂_eventually₂
- \+ *lemma* is_preconnected.mem_intervals
- \+ *lemma* is_preconnected.ord_connected
- \+ *lemma* is_preconnected_Icc
- \+ *lemma* is_preconnected_Ici
- \+ *lemma* is_preconnected_Ico
- \+ *lemma* is_preconnected_Iic
- \+ *lemma* is_preconnected_Iio
- \+ *lemma* is_preconnected_Ioc
- \+ *lemma* is_preconnected_Ioi
- \+ *lemma* is_preconnected_Ioo
- \+ *lemma* is_preconnected_iff_ord_connected
- \+ *lemma* is_preconnected_interval
- \+ *lemma* mem_range_of_exists_le_of_exists_ge
- \+ *lemma* set.ord_connected.is_preconnected
- \+ *lemma* set_of_is_preconnected_eq_of_ordered
- \+ *lemma* set_of_is_preconnected_subset_of_ordered



## [2021-10-21 13:16:14](https://github.com/leanprover-community/mathlib/commit/d9daf54)
feat(topology/metric_space/isometry): add simps config ([#9757](https://github.com/leanprover-community/mathlib/pull/9757))
Also make `isometric.complete_space` take `complete_space β` as an instance argument.
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *def* isometric.simps.apply
- \+ *def* isometric.simps.symm_apply
- \- *lemma* isometric.to_homeomorph_to_equiv
- \- *lemma* isometry.isometric_on_range_apply



## [2021-10-21 11:25:37](https://github.com/leanprover-community/mathlib/commit/fe5ddaf)
feat(ring_theory/polynomial/cyclotomic): add cyclotomic_prime_pow_eq_geom_sum and supporting lemmas ([#9845](https://github.com/leanprover-community/mathlib/pull/9845))
Clean up a little bit in src/number_theory/divisors.lean using to_additive too.
#### Estimated changes
Modified src/number_theory/divisors.lean
- \+ *lemma* nat.mem_proper_divisors_prime_pow
- \+ *lemma* nat.prime.prod_divisors
- \+ *lemma* nat.prime.prod_proper_divisors
- \- *lemma* nat.prime.sum_divisors
- \- *lemma* nat.prime.sum_proper_divisors
- \- *lemma* nat.prod_divisors_prime
- \+ *lemma* nat.prod_proper_divisors_prime_pow
- \+ *lemma* nat.proper_divisors_prime_pow
- \- *lemma* nat.sum_divisors_prime_pow

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* polynomial.cyclotomic_prime_pow_eq_geom_sum



## [2021-10-21 11:25:35](https://github.com/leanprover-community/mathlib/commit/edd801f)
chore(set_theory/cardinal): ensure `c ^ ↑n = c ^ n` is definitional ([#9842](https://github.com/leanprover-community/mathlib/pull/9842))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.pow_cast_right



## [2021-10-21 11:25:33](https://github.com/leanprover-community/mathlib/commit/777f11c)
feat(group_theory/index): Special cases of relindex ([#9831](https://github.com/leanprover-community/mathlib/pull/9831))
Adds special cases of relindex. Also refactors the file to use `nat.card`, rather than the equivalent `(# _).to_nat`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+/\- *lemma* subgroup.index_bot
- \+ *lemma* subgroup.relindex_bot_left
- \+ *lemma* subgroup.relindex_bot_left_eq_card
- \+ *lemma* subgroup.relindex_bot_right
- \+ *lemma* subgroup.relindex_self
- \+ *lemma* subgroup.relindex_top_left
- \+ *lemma* subgroup.relindex_top_right



## [2021-10-21 11:25:32](https://github.com/leanprover-community/mathlib/commit/bfa4010)
feat(data/nat/modeq): `modeq.le_of_lt_add` ([#9816](https://github.com/leanprover-community/mathlib/pull/9816))
If `a ≡ b [MOD m]` and `a < b + m`, then `a ≤ b`.
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* nat.modeq.add_le_of_lt
- \+ *lemma* nat.modeq.le_of_lt_add



## [2021-10-21 08:38:42](https://github.com/leanprover-community/mathlib/commit/da01792)
refactor(*): remove integral_domain, rename domain to is_domain ([#9748](https://github.com/leanprover-community/mathlib/pull/9748))
#### Estimated changes
Modified archive/imo/imo1962_q4.lean
- \+/\- *lemma* formula

Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* no_zero_smul_divisors.iff_algebra_map_injective

Modified src/algebra/algebra/bilinear.lean


Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/char_p/algebra.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq

Modified src/algebra/opposites.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/ring/basic.lean
- \- *lemma* integral_domain.to_is_integral_domain
- \- *theorem* is_integral_domain.to_integral_domain
- \- *structure* is_integral_domain

Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/mv_polynomial/funext.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/polynomial/cancel_leads.lean
- \+/\- *lemma* polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree

Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* polynomial.irreducible_of_mirror
- \+/\- *lemma* polynomial.mirror_mul_of_domain
- \+/\- *lemma* polynomial.mirror_smul

Modified src/data/polynomial/reverse.lean
- \+/\- *lemma* polynomial.reverse_mul_of_domain
- \+/\- *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean
- \- *lemma* is_integral_domain.polynomial
- \+/\- *lemma* polynomial.eq_of_infinite_eval_eq
- \+/\- *lemma* polynomial.leading_coeff_div_by_monic_of_monic
- \+/\- *def* polynomial.nth_roots_finset
- \+/\- *def* polynomial.root_set
- \+/\- *lemma* polynomial.root_set_C
- \+/\- *lemma* polynomial.root_set_def
- \+/\- *lemma* polynomial.root_set_zero

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* char_p.sq_add_sq

Modified src/field_theory/fixed.lean


Modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* is_alg_closed.algebra_map_surjective_of_is_algebraic
- \+/\- *lemma* is_alg_closed.algebra_map_surjective_of_is_integral

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.gcd_domain_eq_field_fractions

Modified src/field_theory/perfect_closure.lean
- \+/\- *theorem* perfect_closure.eq_iff

Modified src/field_theory/separable.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/determinant.lean
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* matrix.det_comm'
- \+/\- *lemma* matrix.det_conj
- \+/\- *def* matrix.index_equiv_of_inv

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/free_module/pid.lean
- \+/\- *lemma* ideal.rank_eq

Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+/\- *lemma* matrix.exists_mul_vec_eq_zero_iff
- \+/\- *lemma* matrix.exists_vec_mul_eq_zero_iff
- \+/\- *theorem* matrix.nondegenerate_iff_det_ne_zero

Modified src/linear_algebra/sesquilinear_form.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/function_field.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/class_group.lean


Modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* ring.dimension_le_one.integral_closure
- \+/\- *lemma* ring.dimension_le_one.is_integral_closure

Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *theorem* discrete_valuation_ring.iff_pid_with_one_nonzero_prime
- \+/\- *lemma* discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization

Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* hahn_series.order_mul

Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* ideal.bot_prime
- \+/\- *lemma* ideal.factors_decreasing
- \+ *lemma* ideal.quotient.is_domain_iff_prime
- \- *lemma* ideal.quotient.is_integral_domain_iff_prime
- \+/\- *lemma* ideal.span_singleton_eq_span_singleton
- \+/\- *lemma* ideal.span_singleton_lt_span_singleton

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.mul_eq_bot
- \+/\- *lemma* ideal.prod_eq_bot
- \- *lemma* ideal.radical_bot_of_integral_domain
- \+ *lemma* ideal.radical_bot_of_is_domain
- \+/\- *lemma* ring_hom.ker_is_prime

Modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* ideal.comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* ideal.comap_ne_bot_of_integral_mem
- \+/\- *lemma* ideal.comap_ne_bot_of_root_mem
- \+/\- *lemma* ideal.eq_bot_of_comap_eq_bot
- \+/\- *lemma* ideal.exists_ideal_over_maximal_of_is_integral

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/integral_domain.lean
- \- *def* division_ring_of_domain
- \+ *def* division_ring_of_is_domain
- \- *def* field_of_integral_domain
- \+ *def* field_of_is_domain
- \- *lemma* is_cyclic_of_subgroup_integral_domain
- \+ *lemma* is_cyclic_of_subgroup_is_domain

Modified src/ring_theory/integrally_closed.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \- *theorem* is_fraction_ring.to_integral_domain
- \- *theorem* is_localization.integral_domain_localization
- \- *theorem* is_localization.integral_domain_of_le_non_zero_divisors
- \+ *theorem* is_localization.is_domain_localization
- \+ *theorem* is_localization.is_domain_of_le_non_zero_divisors

Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/norm.lean
- \+/\- *lemma* algebra.norm_eq_zero_iff_of_basis
- \+/\- *lemma* algebra.norm_ne_zero_iff_of_basis

Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* ideal.is_domain_map_C_quotient
- \- *lemma* ideal.is_integral_domain_map_C_quotient
- \- *theorem* mv_polynomial.integral_domain_fintype
- \+ *lemma* mv_polynomial.is_domain_fin
- \+ *lemma* mv_polynomial.is_domain_fin_zero
- \+ *lemma* mv_polynomial.is_domain_fintype
- \- *lemma* mv_polynomial.is_integral_domain_fin
- \- *lemma* mv_polynomial.is_integral_domain_fin_zero
- \- *lemma* mv_polynomial.is_integral_domain_fintype

Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *def* polynomial.cyclotomic'
- \+/\- *lemma* polynomial.roots_of_cyclotomic

Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/power_basis.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* is_prime.to_maximal_ideal

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *def* primitive_roots

Modified src/ring_theory/subring.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/integral.lean




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
Modified counterexamples/phillips.lean


Modified leanpkg.toml


Modified src/algebra/algebra/basic.lean
- \+ *theorem* alg_hom.coe_fn_inj

Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/FinVect.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Module/adjunctions.lean
- \+ *lemma* Module.free.associativity
- \+ *lemma* Module.free.left_unitality
- \+ *lemma* Module.free.right_unitality
- \+ *def* Module.free.ε
- \+ *def* Module.free.μ
- \+ *lemma* Module.free.μ_natural

Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/direct_sum/basic.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group_action_hom.lean


Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/tensor_product.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/non_unital_alg_hom.lean


Modified src/algebra/order/absolute_value.lean


Modified src/algebra/quandle.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/ring/basic.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/algebraic_topology/topological_simplex.lean


Modified src/analysis/box_integral/partition/additive.lean


Modified src/analysis/calculus/specific_functions.lean
- \+/\- *lemma* times_cont_diff_bump.support_eq
- \+/\- *lemma* times_cont_diff_bump_of_inner.support_eq

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed/group/SemiNormedGroup.lean
- \+ *lemma* SemiNormedGroup₁.coe_comp'

Modified src/analysis/normed/group/SemiNormedGroup/completion.lean


Modified src/analysis/normed/group/hom.lean
- \+/\- *lemma* normed_group_hom.coe_inj
- \+/\- *lemma* normed_group_hom.coe_inj_iff

Modified src/analysis/normed_space/affine_isometry.lean
- \+/\- *lemma* affine_isometry.coe_one

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/enorm.lean
- \+/\- *lemma* enorm.coe_fn_injective
- \+/\- *lemma* enorm.coe_inj

Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry.coe_id
- \+/\- *lemma* linear_isometry.coe_one

Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/seminorm.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/abelian/pseudoelements.lean
- \+/\- *def* category_theory.abelian.pseudoelement.hom_to_fun
- \+/\- *def* category_theory.abelian.pseudoelement.object_to_sort

Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Quiv.lean


Modified src/category_theory/concrete_category/basic.lean
- \+/\- *def* category_theory.concrete_category.has_coe_to_fun

Modified src/category_theory/concrete_category/bundled.lean
- \+/\- *lemma* category_theory.bundled.coe_mk

Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/linear/yoneda.lean


Modified src/category_theory/monad/products.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/category_theory/simple.lean


Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sieves.lean


Modified src/combinatorics/derangements/basic.lean


Modified src/combinatorics/hales_jewett.lean


Modified src/combinatorics/quiver.lean


Modified src/computability/partrec_code.lean


Modified src/computability/turing_machine.lean


Modified src/control/traversable/basic.lean


Modified src/data/analysis/filter.lean


Modified src/data/analysis/topology.lean


Modified src/data/complex/basic.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/equiv/module.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/set.lean


Modified src/data/finset/basic.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card_embedding.lean


Modified src/data/int/gcd.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/nat/prime.lean


Modified src/data/num/lemmas.lean


Modified src/data/pequiv.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/set/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set_like/basic.lean
- \+/\- *theorem* set_like.coe_sort_coe

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/dynamics/flow.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/algebra/left_invariant_derivation.lean


Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/bump_function.lean


Modified src/geometry/manifold/derivation_bundle.lean


Modified src/geometry/manifold/diffeomorph.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff_map.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* affine_equiv.coe_fn_inj

Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/alternating.lean
- \+/\- *theorem* alternating_map.coe_inj
- \+ *theorem* alternating_map.coe_injective

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/multilinear/basic.lean
- \+/\- *theorem* multilinear_map.coe_inj
- \+ *theorem* multilinear_map.coe_injective

Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/linear_algebra/unitary_group.lean


Modified src/logic/basic.lean
- \+ *theorem* coe_fn_coe_base'
- \+ *theorem* coe_fn_coe_trans'

Modified src/logic/embedding.lean


Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.simple_func.coe_injective

Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/content.lean


Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/measure_space_def.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/meta/coinductive_predicates.lean


Modified src/meta/expr.lean


Modified src/model_theory/basic.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/fermat4.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/order/category/LinearOrder.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/category/PartialOrder.lean


Modified src/order/category/Preorder.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/order/closure.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* order_iso.map_at_bot
- \+/\- *lemma* order_iso.map_at_top

Modified src/order/jordan_holder.lean


Modified src/order/lexicographic.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/preorder_hom.lean


Modified src/order/rel_iso.lean


Modified src/ring_theory/algebraic_independent.lean
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_C
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_none
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_some
- \+ *lemma* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply

Modified src/ring_theory/derivation.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/flat.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/ring_invo.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/pgame.lean
- \+/\- *theorem* pgame.lt_mk_of_le

Modified src/set_theory/zfc.lean
- \+/\- *theorem* Set.mem_powerset

Modified src/tactic/abel.lean


Modified src/tactic/cache.lean


Modified src/tactic/converter/interactive.lean


Modified src/tactic/core.lean


Modified src/tactic/elementwise.lean


Modified src/tactic/elide.lean


Modified src/tactic/explode.lean


Modified src/tactic/explode_widget.lean


Modified src/tactic/field_simp.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/finish.lean


Modified src/tactic/generalize_proofs.lean


Modified src/tactic/generalizes.lean


Modified src/tactic/group.lean


Modified src/tactic/hint.lean


Modified src/tactic/interactive.lean


Modified src/tactic/lift.lean


Modified src/tactic/linarith/preprocessing.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/norm_fin.lean


Modified src/tactic/norm_swap.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/replacer.lean


Modified src/tactic/rewrite.lean


Modified src/tactic/ring.lean


Modified src/tactic/simp_result.lean


Modified src/tactic/simpa.lean


Modified src/tactic/simps.lean


Modified src/tactic/slice.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/subtype_instance.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tfae.lean


Modified src/tactic/tidy.lean


Modified src/tactic/trunc_cases.lean


Modified src/tactic/wlog.lean


Modified src/testing/slim_check/functions.lean


Modified src/testing/slim_check/testable.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/weak_dual_topology.lean


Modified src/topology/category/CompHaus/default.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/category/Profinite/default.lean


Modified src/topology/category/Top/basic.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/connected.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/basic.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/fiber_bundle.lean


Modified src/topology/homeomorph.lean


Modified src/topology/homotopy/basic.lean


Modified src/topology/homotopy/path.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/locally_constant/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/partition_of_unity.lean


Modified src/topology/path_connected.lean


Modified src/topology/shrinking_lemma.lean


Modified src/topology/subset_properties.lean


Modified src/topology/vector_bundle.lean


Modified test/delta_instance.lean
- \+/\- *def* X

Modified test/lint_coe_to_fun.lean


Modified test/lint_simp_nf.lean


Modified test/norm_cast_coe_fn.lean


Modified test/simps.lean




## [2021-10-20 19:43:22](https://github.com/leanprover-community/mathlib/commit/8366f93)
feat(ring_theory/integral_domain): finite domains are division rings ([#9823](https://github.com/leanprover-community/mathlib/pull/9823))
TODO: Prove Wedderburn's little theorem
which shows a finite domain is in fact commutative, hence a field.
#### Estimated changes
Modified src/ring_theory/integral_domain.lean
- \+ *def* division_ring_of_domain
- \+ *lemma* mul_left_bijective₀
- \+ *lemma* mul_right_bijective₀



## [2021-10-20 18:03:33](https://github.com/leanprover-community/mathlib/commit/4ebeb05)
chore(group_theory/submonoid/center): add decidable_mem_center ([#9825](https://github.com/leanprover-community/mathlib/pull/9825))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/center.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-10-20 18:03:31](https://github.com/leanprover-community/mathlib/commit/3d00081)
feat(group_theory/index): Index of top and bottom subgroups ([#9819](https://github.com/leanprover-community/mathlib/pull/9819))
This PR computes the index of the top and bottom subgroups.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_bot
- \+ *lemma* subgroup.index_bot_eq_card
- \+ *lemma* subgroup.index_top

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.one_to_nat
- \+ *lemma* cardinal.to_nat_eq_one
- \+ *lemma* cardinal.to_nat_eq_one_iff_unique
- \+/\- *lemma* cardinal.zero_to_nat



## [2021-10-20 15:39:06](https://github.com/leanprover-community/mathlib/commit/68a674e)
refactor(algebra/order/sub): rename sub -> tsub ([#9793](https://github.com/leanprover-community/mathlib/pull/9793))
* Renames lemmas in the file `algebra/order/sub` to use `tsub` instead of `sub` in the name
* Remove primes from lemma names where possible
* [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_lt_mul'''')
* Remove `sub_mul_ge`, `mul_sub_ge` and `lt_sub_iff_lt_sub`. They were special cases of `le_sub_mul`, `le_mul_sub` and `lt_sub_comm`, respectively.
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified archive/imo/imo1977_q6.lean


Modified archive/imo/imo1998_q2.lean


Modified archive/oxford_invariants/2021summer/week3_p1.lean


Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/intervals.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/order/ring.lean
- \- *lemma* mul_sub_ge
- \- *lemma* sub_mul_ge

Modified src/algebra/order/sub.lean
- \- *lemma* add_hom.le_map_sub
- \+ *lemma* add_hom.le_map_tsub
- \- *lemma* add_le_add_add_sub
- \+ *lemma* add_le_add_add_tsub
- \- *lemma* add_le_of_le_sub_left_of_le
- \- *lemma* add_le_of_le_sub_right_of_le
- \+ *lemma* add_le_of_le_tsub_left_of_le
- \+ *lemma* add_le_of_le_tsub_right_of_le
- \- *lemma* add_monoid_hom.le_map_sub
- \+ *lemma* add_monoid_hom.le_map_tsub
- \- *lemma* add_sub_add_eq_sub_left'
- \- *lemma* add_sub_add_right_eq_sub'
- \- *lemma* add_sub_assoc_of_le
- \- *lemma* add_sub_cancel_iff_le
- \- *lemma* add_sub_cancel_left
- \- *lemma* add_sub_cancel_of_le
- \- *lemma* add_sub_cancel_right
- \- *lemma* add_sub_eq_max
- \- *lemma* add_sub_le_assoc
- \- *lemma* add_sub_le_left
- \- *lemma* add_sub_le_right
- \- *lemma* add_sub_sub_cancel'
- \+ *lemma* add_tsub_add_eq_tsub_left
- \+ *lemma* add_tsub_add_right_eq_tsub
- \+ *lemma* add_tsub_assoc_of_le
- \+ *lemma* add_tsub_cancel_iff_le
- \+ *lemma* add_tsub_cancel_left
- \+ *lemma* add_tsub_cancel_of_le
- \+ *lemma* add_tsub_cancel_right
- \+ *lemma* add_tsub_eq_max
- \+ *lemma* add_tsub_le_assoc
- \+ *lemma* add_tsub_le_left
- \+ *lemma* add_tsub_le_right
- \+ *lemma* add_tsub_tsub_cancel
- \- *lemma* eq_sub_iff_add_eq_of_le
- \- *lemma* eq_sub_of_add_eq''
- \+ *lemma* eq_tsub_iff_add_eq_of_le
- \+ *lemma* eq_tsub_of_add_eq
- \- *lemma* le_add_sub'
- \- *lemma* le_add_sub
- \- *lemma* le_add_sub_swap
- \+ *lemma* le_add_tsub'
- \+ *lemma* le_add_tsub
- \+ *lemma* le_add_tsub_swap
- \- *lemma* le_mul_sub
- \+ *lemma* le_mul_tsub
- \- *lemma* le_sub_add
- \- *lemma* le_sub_add_add
- \- *lemma* le_sub_iff_le_sub
- \- *lemma* le_sub_iff_left
- \- *lemma* le_sub_iff_right
- \- *lemma* le_sub_mul
- \- *lemma* le_sub_of_add_le_left'
- \- *lemma* le_sub_of_add_le_right'
- \+ *lemma* le_tsub_add
- \+ *lemma* le_tsub_add_add
- \+ *lemma* le_tsub_iff_le_tsub
- \+ *lemma* le_tsub_iff_left
- \+ *lemma* le_tsub_iff_right
- \+ *lemma* le_tsub_mul
- \+ *lemma* le_tsub_of_add_le_left
- \+ *lemma* le_tsub_of_add_le_right
- \- *lemma* lt_add_of_sub_lt_left'
- \- *lemma* lt_add_of_sub_lt_right'
- \+ *lemma* lt_add_of_tsub_lt_left
- \+ *lemma* lt_add_of_tsub_lt_right
- \- *lemma* lt_of_sub_lt_sub_left
- \- *lemma* lt_of_sub_lt_sub_left_of_le
- \- *lemma* lt_of_sub_lt_sub_right
- \- *lemma* lt_of_sub_lt_sub_right_of_le
- \+ *lemma* lt_of_tsub_lt_tsub_left
- \+ *lemma* lt_of_tsub_lt_tsub_left_of_le
- \+ *lemma* lt_of_tsub_lt_tsub_right
- \+ *lemma* lt_of_tsub_lt_tsub_right_of_le
- \- *lemma* lt_sub_comm
- \- *lemma* lt_sub_iff_left
- \- *lemma* lt_sub_iff_left_of_le
- \- *lemma* lt_sub_iff_lt_sub
- \- *lemma* lt_sub_iff_right
- \- *lemma* lt_sub_iff_right_of_le
- \- *lemma* lt_sub_of_add_lt_left
- \- *lemma* lt_sub_of_add_lt_right
- \+ *lemma* lt_tsub_comm
- \+ *lemma* lt_tsub_iff_left
- \+ *lemma* lt_tsub_iff_left_of_le
- \+ *lemma* lt_tsub_iff_right
- \+ *lemma* lt_tsub_iff_right_of_le
- \+ *lemma* lt_tsub_of_add_lt_left
- \+ *lemma* lt_tsub_of_add_lt_right
- \- *lemma* order_iso.map_sub
- \+ *lemma* order_iso.map_tsub
- \- *lemma* sub_add_cancel_iff_le
- \- *lemma* sub_add_cancel_of_le
- \- *lemma* sub_add_eq_add_sub'
- \- *lemma* sub_add_eq_max
- \- *lemma* sub_add_eq_sub_sub'
- \- *lemma* sub_add_eq_sub_sub_swap'
- \- *lemma* sub_add_min
- \- *lemma* sub_add_sub_cancel''
- \- *lemma* sub_eq_iff_eq_add_of_le
- \- *lemma* sub_eq_of_eq_add''
- \- *lemma* sub_eq_of_eq_add_rev
- \- *lemma* sub_eq_sub_min
- \- *lemma* sub_eq_zero_iff_le
- \- *lemma* sub_inj_left
- \- *lemma* sub_inj_right
- \- *lemma* sub_le_iff_left
- \- *lemma* sub_le_iff_right
- \- *lemma* sub_le_iff_sub_le
- \- *lemma* sub_le_self'
- \- *lemma* sub_le_sub'
- \- *lemma* sub_le_sub_add_sub
- \- *lemma* sub_le_sub_iff_left'
- \- *lemma* sub_le_sub_iff_right'
- \- *lemma* sub_le_sub_left'
- \- *lemma* sub_le_sub_right'
- \- *lemma* sub_left_inj'
- \- *lemma* sub_lt_iff_left
- \- *lemma* sub_lt_iff_right
- \- *lemma* sub_lt_iff_sub_lt
- \- *lemma* sub_lt_self'
- \- *lemma* sub_lt_self_iff'
- \- *lemma* sub_lt_sub_iff_left_of_le
- \- *lemma* sub_lt_sub_iff_left_of_le_of_le
- \- *lemma* sub_lt_sub_iff_right'
- \- *lemma* sub_lt_sub_right_of_le
- \- *lemma* sub_min
- \- *lemma* sub_pos_iff_lt
- \- *lemma* sub_pos_iff_not_le
- \- *lemma* sub_pos_of_lt'
- \- *lemma* sub_right_comm'
- \- *lemma* sub_right_inj'
- \- *lemma* sub_self'
- \- *lemma* sub_self_add
- \- *lemma* sub_sub'
- \- *lemma* sub_sub_assoc
- \- *lemma* sub_sub_cancel_of_le
- \- *lemma* sub_sub_le
- \- *lemma* sub_sub_sub_cancel_right'
- \- *lemma* sub_sub_sub_le_sub
- \- *lemma* sub_zero'
- \+ *lemma* tsub_add_cancel_iff_le
- \+ *lemma* tsub_add_cancel_of_le
- \+ *lemma* tsub_add_eq_add_tsub
- \+ *lemma* tsub_add_eq_max
- \+ *lemma* tsub_add_eq_tsub_tsub
- \+ *lemma* tsub_add_eq_tsub_tsub_swap
- \+ *lemma* tsub_add_min
- \+ *lemma* tsub_add_tsub_cancel
- \+ *lemma* tsub_eq_iff_eq_add_of_le
- \+ *lemma* tsub_eq_of_eq_add
- \+ *lemma* tsub_eq_of_eq_add_rev
- \+ *lemma* tsub_eq_tsub_min
- \+ *lemma* tsub_eq_zero_iff_le
- \+ *lemma* tsub_inj_left
- \+ *lemma* tsub_inj_right
- \+ *lemma* tsub_le_iff_left
- \+ *lemma* tsub_le_iff_right
- \+ *lemma* tsub_le_iff_tsub_le
- \+ *lemma* tsub_le_self
- \+ *lemma* tsub_le_tsub
- \+ *lemma* tsub_le_tsub_add_tsub
- \+ *lemma* tsub_le_tsub_iff_left
- \+ *lemma* tsub_le_tsub_iff_right
- \+ *lemma* tsub_le_tsub_left
- \+ *lemma* tsub_le_tsub_right
- \+ *lemma* tsub_left_inj
- \+ *lemma* tsub_lt_iff_left
- \+ *lemma* tsub_lt_iff_right
- \+ *lemma* tsub_lt_iff_tsub_lt
- \+ *lemma* tsub_lt_self
- \+ *lemma* tsub_lt_self_iff
- \+ *lemma* tsub_lt_tsub_iff_left_of_le
- \+ *lemma* tsub_lt_tsub_iff_left_of_le_of_le
- \+ *lemma* tsub_lt_tsub_iff_right
- \+ *lemma* tsub_lt_tsub_right_of_le
- \+ *lemma* tsub_min
- \+ *lemma* tsub_pos_iff_lt
- \+ *lemma* tsub_pos_iff_not_le
- \+ *lemma* tsub_pos_of_lt
- \+ *lemma* tsub_right_comm
- \+ *lemma* tsub_right_inj
- \+ *lemma* tsub_self
- \+ *lemma* tsub_self_add
- \+ *lemma* tsub_tsub
- \+ *lemma* tsub_tsub_assoc
- \+ *lemma* tsub_tsub_cancel_of_le
- \+ *lemma* tsub_tsub_le
- \+ *lemma* tsub_tsub_tsub_cancel_right
- \+ *lemma* tsub_tsub_tsub_le_tsub
- \+ *lemma* tsub_zero
- \- *lemma* zero_sub'
- \+ *lemma* zero_tsub

Modified src/algebra/pointwise.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/normed/group/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/composition.lean


Modified src/combinatorics/derangements/exponential.lean


Modified src/combinatorics/derangements/finite.lean


Modified src/computability/DFA.lean


Modified src/computability/turing_machine.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/fin.lean


Modified src/data/fin/basic.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/sort.lean


Modified src/data/finsupp/antidiagonal.lean


Modified src/data/finsupp/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/cycle.lean


Modified src/data/list/intervals.lean


Modified src/data/list/perm.lean


Modified src/data/list/rotate.lean


Modified src/data/matrix/notation.lean


Modified src/data/multiset/antidiagonal.lean


Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.eq_union_left
- \+/\- *theorem* multiset.le_union_left

Modified src/data/multiset/nodup.lean


Modified src/data/multiset/powerset.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/choose/basic.lean


Modified src/data/nat/dist.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/nat/interval.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/nat/succ_pred.lean


Modified src/data/nat/upto.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial/hasse_deriv.lean


Modified src/data/polynomial/mirror.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.lt_sub_comm
- \+/\- *lemma* ennreal.lt_sub_iff_add_lt

Modified src/data/vector/basic.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/list.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/admissible_card_pow_degree.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/iterate.lean


Modified src/order/jordan_holder.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/set_theory/game/state.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/system/random/basic.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/omega/coeffs.lean


Modified src/testing/slim_check/gen.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified test/general_recursion.lean




## [2021-10-20 13:23:09](https://github.com/leanprover-community/mathlib/commit/5223e26)
feat(field_theory/finite/galois_field): uniqueness of finite fields ([#9817](https://github.com/leanprover-community/mathlib/pull/9817))
Every finite field is isomorphic to some Galois field. Closes [#9599](https://github.com/leanprover-community/mathlib/pull/9599)
#### Estimated changes
Modified src/field_theory/finite/basic.lean
- \+/\- *theorem* finite_field.card'

Modified src/field_theory/finite/galois_field.lean
- \+ *def* galois_field.alg_equiv_galois_field
- \+ *lemma* galois_field.is_splitting_field_of_card_eq
- \+ *theorem* galois_field.splits_X_pow_card_sub_X



## [2021-10-20 11:46:43](https://github.com/leanprover-community/mathlib/commit/49ab444)
fix(algebra/module/submodule_lattice): correct bad lemma ([#9809](https://github.com/leanprover-community/mathlib/pull/9809))
This lemma was accidentally stating that inf and inter are the same on sets, and wasn't about submodule at all.
The old statement was `↑p ⊓ ↑q = ↑p ∩ ↑q`, the new one is `↑(p ⊓ q) = ↑p ∩ ↑q`
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean
- \+/\- *theorem* submodule.inf_coe



## [2021-10-20 09:53:23](https://github.com/leanprover-community/mathlib/commit/24901dd)
feat(linear_algebra/free_module/rank): rank of free modules  ([#9810](https://github.com/leanprover-community/mathlib/pull/9810))
This file contains a basic API for the rank of free modules.
We will add the results for finite free modules in a future PR.
#### Estimated changes
Added src/linear_algebra/free_module/rank.lean
- \+ *lemma* module.free.rank_direct_sum
- \+ *lemma* module.free.rank_eq_card_choose_basis_index
- \+ *lemma* module.free.rank_finsupp'
- \+ *lemma* module.free.rank_finsupp
- \+ *lemma* module.free.rank_prod'
- \+ *lemma* module.free.rank_prod
- \+ *lemma* module.free.rank_tensor_product'
- \+ *lemma* module.free.rank_tensor_product



## [2021-10-20 09:53:22](https://github.com/leanprover-community/mathlib/commit/2f54840)
refactor(*): replace comm_ring/integral_domain with ring/domain where possible ([#9739](https://github.com/leanprover-community/mathlib/pull/9739))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* polynomial.mirror_mul_of_domain
- \+/\- *lemma* polynomial.mirror_smul

Modified src/data/polynomial/reverse.lean
- \+/\- *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean


Modified src/data/real/cau_seq.lean


Modified src/field_theory/fixed.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/free_module/pid.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* hahn_series.order_mul

Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* ideal.bot_prime

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ring_hom.ker_is_prime

Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-10-20 08:19:58](https://github.com/leanprover-community/mathlib/commit/a6d5ba8)
chore(set_theory/cardinal): add `map`, `induction_on` etc ([#9812](https://github.com/leanprover-community/mathlib/pull/9812))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.induction_on
- \+ *lemma* cardinal.induction_on₂
- \+ *lemma* cardinal.induction_on₃
- \+/\- *theorem* cardinal.lift_id'
- \+/\- *theorem* cardinal.lift_id
- \+/\- *theorem* cardinal.lift_umax
- \+/\- *theorem* cardinal.lift_zero
- \+ *def* cardinal.map
- \+ *lemma* cardinal.map_mk
- \+ *def* cardinal.map₂
- \+ *lemma* cardinal.mk_congr
- \+/\- *lemma* cardinal.succ_ne_zero

Modified src/set_theory/ordinal.lean




## [2021-10-20 04:15:08](https://github.com/leanprover-community/mathlib/commit/9dafdf7)
feat(group_theory/subgroup/basic): `subgroup_of_self` ([#9818](https://github.com/leanprover-community/mathlib/pull/9818))
A subgroup is the top subgroup of itself.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.subgroup_of_self



## [2021-10-20 04:15:07](https://github.com/leanprover-community/mathlib/commit/6898728)
feat(analysis/complex/basic): a complex-valued function `has_sum` iff its real part and imaginary part `has_sum` ([#9648](https://github.com/leanprover-community/mathlib/pull/9648))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *def* complex.equiv_real_prod_add_hom
- \+ *def* complex.equiv_real_prod_add_hom_lm
- \+ *def* complex.equiv_real_prodₗ
- \+ *lemma* complex.has_sum_iff

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.prod_mk



## [2021-10-20 01:45:58](https://github.com/leanprover-community/mathlib/commit/cd34347)
chore(*): remove uses of `universe variable` ([#9794](https://github.com/leanprover-community/mathlib/pull/9794))
Most of these uses are relics of when the distinction between `universe` and `universe variable` was more significant. There is still a difference inside sections, but it's an edge case and I don't think any of these uses are consciously trying to handle the edge case.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/control/applicative.lean


Modified src/control/functor.lean


Modified src/control/traversable/lemmas.lean


Modified src/data/equiv/fin.lean


Modified src/data/fin_enum.lean


Modified src/data/list/perm.lean


Modified src/data/list/sort.lean


Modified src/data/set/basic.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/free_algebra.lean


Modified src/logic/basic.lean
- \+/\- *lemma* classical.nonempty_pi
- \+/\- *lemma* nonempty.exists
- \+/\- *lemma* nonempty.forall
- \+/\- *lemma* nonempty.map
- \+/\- *lemma* nonempty_plift
- \+/\- *lemma* nonempty_pprod
- \+/\- *lemma* nonempty_psigma
- \+/\- *lemma* nonempty_psum
- \+/\- *lemma* nonempty_subtype

Modified src/logic/relator.lean


Modified src/measure_theory/measure/content.lean


Modified src/model_theory/basic.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/copy.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/flat.lean


Modified src/ring_theory/henselian.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/tactic/core.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/weak_dual_topology.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/category/Profinite/default.lean


Modified src/topology/category/Profinite/projective.lean


Modified test/simps.lean




## [2021-10-19 23:43:31](https://github.com/leanprover-community/mathlib/commit/2d17c5a)
feat(group_theory/index): Relative index ([#9780](https://github.com/leanprover-community/mathlib/pull/9780))
Defines relative index between subgroups, and proves that relative index is multiplicative in towers.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_comap
- \- *lemma* subgroup.index_eq_mul_of_le
- \+ *lemma* subgroup.relindex_mul_index
- \+ *lemma* subgroup.relindex_mul_relindex
- \+ *lemma* subgroup.relindex_subgroup_of



## [2021-10-19 20:59:45](https://github.com/leanprover-community/mathlib/commit/72cb2e8)
refactor(*): rename some declarations ending with '' ([#9504](https://github.com/leanprover-community/mathlib/pull/9504))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* algebra.smul_def''

Modified src/algebra/algebra/tower.lean


Modified src/algebra/free.lean
- \- *def* free_magma.rec_on'
- \+ *def* free_magma.rec_on_mul
- \- *def* free_semigroup.rec_on'
- \+ *def* free_semigroup.rec_on_pure

Modified src/algebra/group_power/order.lean
- \- *theorem* pow_lt_pow''
- \+ *theorem* pow_lt_pow'

Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/support.lean
- \- *lemma* function.mul_support_inv''
- \+ *lemma* function.mul_support_inv'

Modified src/category_theory/abelian/exact.lean
- \- *theorem* category_theory.abelian.exact_iff''
- \+ *theorem* category_theory.abelian.exact_iff_image_eq_kernel

Modified src/category_theory/monoidal/natural_transformation.lean
- \- *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans''
- \- *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans'
- \+ *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans
- \+ *lemma* category_theory.monoidal_nat_trans.comp_to_nat_trans_lax

Modified src/data/matrix/basic.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.eq_of_irreducible
- \+ *theorem* minpoly.eq_of_irreducible_of_monic
- \- *lemma* minpoly.unique''
- \- *theorem* minpoly.unique'

Modified src/ring_theory/derivation.lean


Modified src/ring_theory/polynomial_algebra.lean




## [2021-10-19 16:49:58](https://github.com/leanprover-community/mathlib/commit/65eef74)
fix(data/int/basic): ensure the additive group structure on integers is computable ([#9803](https://github.com/leanprover-community/mathlib/pull/9803))
This prevents the following failure:
```lean
import analysis.normed_space.basic
instance whoops : add_comm_group ℤ := by apply_instance
-- definition 'whoops' is noncomputable, it depends on 'int.normed_comm_ring'
```
#### Estimated changes
Modified src/data/int/basic.lean




## [2021-10-19 15:18:56](https://github.com/leanprover-community/mathlib/commit/e61584d)
fix(topology/sheaves/*): Fix docstrings ([#9807](https://github.com/leanprover-community/mathlib/pull/9807))
As noted by @alreadydone in [#9607](https://github.com/leanprover-community/mathlib/pull/9607), I forgot propagate naming changes to docstrings. This PR fixes that.
#### Estimated changes
Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean


Modified src/topology/sheaves/sheaf_of_functions.lean




## [2021-10-19 12:47:04](https://github.com/leanprover-community/mathlib/commit/34aa23a)
feat(ring_theory/dedekind_domain): connect (/) and (⁻¹) on fractional ideals ([#9808](https://github.com/leanprover-community/mathlib/pull/9808))
Turns out we never actually proved the `div_eq_mul_inv` lemma on fractional ideals, which motivated the entire definition of `div_inv_monoid`. So here it is, along with some useful supporting lemmas.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* fractional_ideal.mul_left_le_iff
- \+ *lemma* fractional_ideal.mul_left_strict_mono
- \+ *lemma* fractional_ideal.mul_right_le_iff
- \+ *lemma* fractional_ideal.mul_right_strict_mono



## [2021-10-19 11:59:41](https://github.com/leanprover-community/mathlib/commit/065a708)
refactor(analysis/inner_product_space/projection): speedup proof ([#9804](https://github.com/leanprover-community/mathlib/pull/9804))
Speed up slow proof that caused a timeout on another branch.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *def* reflection_linear_equiv



## [2021-10-19 09:31:15](https://github.com/leanprover-community/mathlib/commit/b961b68)
feat(topology/connected): product of connected spaces is a connected space ([#9789](https://github.com/leanprover-community/mathlib/pull/9789))
* prove more in the RHS of `filter.mem_infi'`;
* prove that the product of (pre)connected sets is a (pre)connected set;
* prove a similar statement about indexed product `set.pi set.univ _`;
* add instances for `prod.preconnected_space`, `prod.connected_space`, `pi.preconnected_space`, and `pi.connected_space`.
#### Estimated changes
Modified src/order/filter/basic.lean


Modified src/topology/connected.lean
- \+ *theorem* is_connected.prod
- \+ *theorem* is_connected_univ_pi
- \+ *theorem* is_preconnected.prod
- \+ *theorem* is_preconnected_Union
- \+ *theorem* is_preconnected_singleton
- \+ *theorem* is_preconnected_univ_pi
- \+ *theorem* set.subsingleton.is_preconnected

Modified src/topology/constructions.lean
- \+ *lemma* exists_finset_piecewise_mem_of_mem_nhds

Modified src/topology/continuous_on.lean




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
Modified archive/imo/imo1962_q4.lean
- \+/\- *lemma* formula

Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* no_zero_smul_divisors.iff_algebra_map_injective

Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/char_p/algebra.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq

Modified src/algebra/opposites.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/ring/basic.lean
- \+/\- *lemma* integral_domain.to_is_integral_domain
- \+ *theorem* is_integral_domain.to_integral_domain
- \- *def* is_integral_domain.to_integral_domain

Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/mv_polynomial/funext.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/polynomial/cancel_leads.lean
- \+/\- *lemma* polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree

Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.root_multiplicity_eq_zero
- \+ *lemma* polynomial.root_multiplicity_pos
- \+ *lemma* polynomial.root_multiplicity_zero

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* polynomial.irreducible_of_mirror
- \+/\- *lemma* polynomial.mirror_mul_of_domain
- \+/\- *lemma* polynomial.mirror_smul

Modified src/data/polynomial/reverse.lean
- \+/\- *lemma* polynomial.reverse_mul_of_domain
- \+/\- *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.eq_of_infinite_eval_eq
- \+/\- *lemma* polynomial.leading_coeff_div_by_monic_of_monic
- \+/\- *def* polynomial.nth_roots_finset
- \- *lemma* polynomial.root_multiplicity_eq_zero
- \- *lemma* polynomial.root_multiplicity_pos
- \- *lemma* polynomial.root_multiplicity_zero
- \+/\- *def* polynomial.root_set
- \+/\- *lemma* polynomial.root_set_C
- \+/\- *lemma* polynomial.root_set_def
- \+/\- *lemma* polynomial.root_set_finite
- \+/\- *lemma* polynomial.root_set_zero

Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* char_p.sq_add_sq

Modified src/field_theory/finite/galois_field.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* is_alg_closed.algebra_map_surjective_of_is_algebraic
- \+/\- *lemma* is_alg_closed.algebra_map_surjective_of_is_integral'
- \+/\- *lemma* is_alg_closed.algebra_map_surjective_of_is_integral

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.gcd_domain_eq_field_fractions

Modified src/field_theory/perfect_closure.lean
- \+/\- *theorem* perfect_closure.eq_iff

Modified src/field_theory/separable.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/determinant.lean
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* matrix.det_comm'
- \+/\- *lemma* matrix.det_conj
- \+/\- *def* matrix.index_equiv_of_inv

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/free_module/pid.lean
- \+/\- *theorem* ideal.exists_smith_normal_form
- \+/\- *lemma* ideal.rank_eq

Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean
- \+/\- *lemma* matrix.exists_mul_vec_eq_zero_iff'
- \+/\- *lemma* matrix.exists_mul_vec_eq_zero_iff
- \+/\- *lemma* matrix.exists_vec_mul_eq_zero_iff
- \+/\- *theorem* matrix.nondegenerate_iff_det_ne_zero

Modified src/linear_algebra/sesquilinear_form.lean


Modified src/number_theory/class_number/finite.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/class_group.lean


Modified src/ring_theory/dedekind_domain.lean
- \+/\- *lemma* mul_generator_self_inv
- \+/\- *lemma* ring.dimension_le_one.integral_closure
- \+/\- *lemma* ring.dimension_le_one.is_integral_closure

Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *def* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization
- \+/\- *theorem* discrete_valuation_ring.iff_pid_with_one_nonzero_prime
- \+/\- *lemma* discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
- \+/\- *lemma* discrete_valuation_ring.of_ufd_of_unique_irreducible

Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* hahn_series.is_pwo_Union_support_powers
- \+/\- *lemma* hahn_series.order_mul

Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* ideal.bot_prime
- \+/\- *lemma* ideal.factors_decreasing
- \+/\- *lemma* ideal.span_singleton_eq_span_singleton
- \+/\- *lemma* ideal.span_singleton_lt_span_singleton

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.mul_eq_bot
- \+/\- *lemma* ideal.prod_eq_bot
- \+/\- *lemma* ideal.radical_bot_of_integral_domain
- \+/\- *lemma* ring_hom.ker_is_prime

Modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* ideal.comap_lt_comap_of_integral_mem_sdiff
- \+/\- *lemma* ideal.comap_ne_bot_of_algebraic_mem
- \+/\- *lemma* ideal.comap_ne_bot_of_integral_mem
- \+/\- *lemma* ideal.comap_ne_bot_of_root_mem
- \+/\- *lemma* ideal.eq_bot_of_comap_eq_bot
- \+/\- *lemma* ideal.exists_coeff_ne_zero_mem_comap_of_root_mem
- \+/\- *lemma* ideal.exists_ideal_over_maximal_of_is_integral
- \+/\- *lemma* ideal.is_maximal_comap_of_is_integral_of_is_maximal'
- \+/\- *lemma* ideal.is_maximal_of_is_integral_of_is_maximal_comap'

Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_field_of_is_integral_of_is_field

Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/integrally_closed.lean


Modified src/ring_theory/jacobson.lean
- \+/\- *lemma* ideal.mv_polynomial.comp_C_integral_of_surjective_of_jacobson
- \+/\- *lemma* ideal.mv_polynomial.quotient_mk_comp_C_is_integral_of_jacobson
- \+/\- *lemma* ideal.polynomial.is_maximal_comap_C_of_is_jacobson
- \+/\- *lemma* ideal.polynomial.is_maximal_comap_C_of_is_maximal
- \+/\- *lemma* ideal.polynomial.jacobson_bot_of_integral_localization

Modified src/ring_theory/localization.lean
- \+ *theorem* is_fraction_ring.to_integral_domain
- \- *def* is_fraction_ring.to_integral_domain
- \+ *theorem* is_localization.integral_domain_localization
- \- *def* is_localization.integral_domain_localization
- \+ *theorem* is_localization.integral_domain_of_le_non_zero_divisors
- \- *def* is_localization.integral_domain_of_le_non_zero_divisors
- \+/\- *lemma* localization_map_bijective_of_field

Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/norm.lean
- \+/\- *lemma* algebra.norm_eq_zero_iff_of_basis
- \+/\- *lemma* algebra.norm_ne_zero_iff_of_basis

Modified src/ring_theory/polynomial/basic.lean
- \+ *theorem* mv_polynomial.integral_domain_fintype
- \- *def* mv_polynomial.integral_domain_fintype
- \+/\- *theorem* polynomial.exists_irreducible_of_degree_pos
- \+/\- *theorem* polynomial.exists_irreducible_of_nat_degree_ne_zero
- \+/\- *theorem* polynomial.exists_irreducible_of_nat_degree_pos

Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* polynomial.cyclotomic'.monic
- \+/\- *def* polynomial.cyclotomic'
- \+/\- *lemma* polynomial.cyclotomic'_ne_zero
- \+/\- *lemma* polynomial.cyclotomic'_one
- \+/\- *lemma* polynomial.cyclotomic'_two
- \+/\- *lemma* polynomial.cyclotomic'_zero
- \+/\- *lemma* polynomial.roots_of_cyclotomic

Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/power_basis.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* is_field.is_principal_ideal_ring
- \+/\- *lemma* is_prime.to_maximal_ideal
- \+/\- *lemma* principal_ideal_ring.ne_zero_of_mem_factors

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *def* primitive_roots

Modified src/ring_theory/subring.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/integral.lean




## [2021-10-19 07:46:18](https://github.com/leanprover-community/mathlib/commit/a7bc717)
feat(algebra/big_operators/order): Upper bound on the cardinality of `finset.bUnion` ([#9797](https://github.com/leanprover-community/mathlib/pull/9797))
Also fix notation in all the additivized statements docstrings.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.card_bUnion_le_card_mul



## [2021-10-19 07:46:17](https://github.com/leanprover-community/mathlib/commit/4df649c)
feat(data/nat/modeq): Upper bound for `chinese_remainder` ([#9783](https://github.com/leanprover-community/mathlib/pull/9783))
Proves that `chinese_remainder' < lcm n m` and `chinese_remainder < n * m`, as claimed by the doc-strings.
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *lemma* nat.chinese_remainder'_lt_lcm
- \+ *lemma* nat.chinese_remainder_lt_mul



## [2021-10-19 07:05:07](https://github.com/leanprover-community/mathlib/commit/1f8c96b)
feat(data/nat/succ_pred): `ℕ` is succ- and pred- archimedean ([#9730](https://github.com/leanprover-community/mathlib/pull/9730))
This provides the instances `succ_order ℕ`, `pred_order ℕ`, `is_succ_archimedean ℕ`, `is_pred_archimedean ℕ`.
#### Estimated changes
Added src/data/nat/succ_pred.lean
- \+ *lemma* nat.pred_iterate
- \+ *lemma* nat.succ_iterate

Modified src/order/succ_pred.lean
- \+/\- *lemma* succ_order.succ_lt_succ_iff



## [2021-10-19 04:41:01](https://github.com/leanprover-community/mathlib/commit/1ec385d)
chore(scripts): update nolints.txt ([#9799](https://github.com/leanprover-community/mathlib/pull/9799))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-10-19 02:24:00](https://github.com/leanprover-community/mathlib/commit/04094c4)
feat(analysis/box_integral): Divergence thm for a Henstock-style integral ([#9496](https://github.com/leanprover-community/mathlib/pull/9496))
* Define integrals of Riemann, McShane, and Henstock (plus a few
  variations).
* Prove basic properties.
* Prove a version of the divergence theorem for one of these integrals.
* Prove that a Bochner integrable function is McShane integrable.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/order/field.lean
- \+ *lemma* add_div_two_lt_right
- \+ *lemma* exists_pos_mul_lt
- \+ *lemma* left_lt_add_div_two

Added src/analysis/box_integral/basic.lean
- \+ *lemma* box_integral.has_integral.add
- \+ *lemma* box_integral.has_integral.integrable
- \+ *lemma* box_integral.has_integral.integral_eq
- \+ *lemma* box_integral.has_integral.mono
- \+ *lemma* box_integral.has_integral.neg
- \+ *lemma* box_integral.has_integral.smul
- \+ *lemma* box_integral.has_integral.sub
- \+ *lemma* box_integral.has_integral.tendsto
- \+ *lemma* box_integral.has_integral.unique
- \+ *def* box_integral.has_integral
- \+ *lemma* box_integral.has_integral_McShane_of_forall_is_o
- \+ *lemma* box_integral.has_integral_const
- \+ *lemma* box_integral.has_integral_iff
- \+ *lemma* box_integral.has_integral_of_bRiemann_eq_ff_of_forall_is_o
- \+ *lemma* box_integral.has_integral_of_le_Henstock_of_forall_is_o
- \+ *lemma* box_integral.has_integral_of_mul
- \+ *lemma* box_integral.has_integral_sum
- \+ *lemma* box_integral.has_integral_zero
- \+ *lemma* box_integral.integrable.add
- \+ *lemma* box_integral.integrable.cauchy_map_integral_sum_to_filter_Union
- \+ *def* box_integral.integrable.convergence_r
- \+ *lemma* box_integral.integrable.convergence_r_cond
- \+ *lemma* box_integral.integrable.dist_integral_sum_integral_le_of_mem_base_set
- \+ *lemma* box_integral.integrable.dist_integral_sum_le_of_mem_base_set
- \+ *lemma* box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set
- \+ *lemma* box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq
- \+ *lemma* box_integral.integrable.mono
- \+ *lemma* box_integral.integrable.neg
- \+ *lemma* box_integral.integrable.of_neg
- \+ *lemma* box_integral.integrable.of_smul
- \+ *lemma* box_integral.integrable.smul
- \+ *lemma* box_integral.integrable.sub
- \+ *lemma* box_integral.integrable.sum_integral_congr
- \+ *lemma* box_integral.integrable.tendsto_integral_sum_sum_integral
- \+ *lemma* box_integral.integrable.tendsto_integral_sum_to_filter_Union_single
- \+ *lemma* box_integral.integrable.tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity
- \+ *def* box_integral.integrable.to_box_additive
- \+ *lemma* box_integral.integrable.to_subbox
- \+ *lemma* box_integral.integrable.to_subbox_aux
- \+ *def* box_integral.integrable
- \+ *lemma* box_integral.integrable_const
- \+ *lemma* box_integral.integrable_iff_cauchy
- \+ *lemma* box_integral.integrable_iff_cauchy_basis
- \+ *lemma* box_integral.integrable_neg
- \+ *lemma* box_integral.integrable_of_continuous_on
- \+ *lemma* box_integral.integrable_zero
- \+ *def* box_integral.integral
- \+ *lemma* box_integral.integral_add
- \+ *lemma* box_integral.integral_const
- \+ *lemma* box_integral.integral_neg
- \+ *lemma* box_integral.integral_nonneg
- \+ *lemma* box_integral.integral_smul
- \+ *lemma* box_integral.integral_sub
- \+ *def* box_integral.integral_sum
- \+ *lemma* box_integral.integral_sum_add
- \+ *lemma* box_integral.integral_sum_bUnion_partition
- \+ *lemma* box_integral.integral_sum_bUnion_tagged
- \+ *lemma* box_integral.integral_sum_disj_union
- \+ *lemma* box_integral.integral_sum_fiberwise
- \+ *lemma* box_integral.integral_sum_inf_partition
- \+ *lemma* box_integral.integral_sum_neg
- \+ *lemma* box_integral.integral_sum_smul
- \+ *lemma* box_integral.integral_sum_sub_partitions
- \+ *lemma* box_integral.integral_zero
- \+ *lemma* box_integral.norm_integral_le_of_le_const
- \+ *lemma* box_integral.norm_integral_le_of_norm_le

Added src/analysis/box_integral/box/basic.lean
- \+ *lemma* box_integral.box.Icc_def
- \+ *lemma* box_integral.box.Icc_eq_pi
- \+ *lemma* box_integral.box.antitone_lower
- \+ *lemma* box_integral.box.bUnion_coe_eq_coe
- \+ *lemma* box_integral.box.coe_bot
- \+ *lemma* box_integral.box.coe_coe
- \+ *lemma* box_integral.box.coe_eq_pi
- \+ *lemma* box_integral.box.coe_inf
- \+ *lemma* box_integral.box.coe_inj
- \+ *lemma* box_integral.box.coe_mk'
- \+ *lemma* box_integral.box.coe_ne_empty
- \+ *lemma* box_integral.box.coe_subset_Icc
- \+ *lemma* box_integral.box.coe_subset_coe
- \+ *lemma* box_integral.box.continuous_on_face_Icc
- \+ *lemma* box_integral.box.diam_Icc_le_of_distortion_le
- \+ *lemma* box_integral.box.disjoint_coe
- \+ *lemma* box_integral.box.disjoint_with_bot_coe
- \+ *lemma* box_integral.box.dist_le_distortion_mul
- \+ *def* box_integral.box.distortion
- \+ *lemma* box_integral.box.distortion_eq_of_sub_eq_div
- \+ *lemma* box_integral.box.empty_ne_coe
- \+ *lemma* box_integral.box.exists_mem
- \+ *lemma* box_integral.box.ext
- \+ *def* box_integral.box.face
- \+ *lemma* box_integral.box.face_mk
- \+ *lemma* box_integral.box.face_mono
- \+ *lemma* box_integral.box.injective_coe
- \+ *lemma* box_integral.box.is_some_iff
- \+ *lemma* box_integral.box.le_def
- \+ *lemma* box_integral.box.le_iff_Icc
- \+ *lemma* box_integral.box.le_iff_bounds
- \+ *lemma* box_integral.box.le_tfae
- \+ *lemma* box_integral.box.lower_le_upper
- \+ *lemma* box_integral.box.lower_mem_Icc
- \+ *lemma* box_integral.box.maps_to_insert_nth_face
- \+ *lemma* box_integral.box.maps_to_insert_nth_face_Icc
- \+ *lemma* box_integral.box.mem_coe
- \+ *lemma* box_integral.box.mem_def
- \+ *lemma* box_integral.box.mem_mk
- \+ *lemma* box_integral.box.mem_univ_Ioc
- \+ *def* box_integral.box.mk'
- \+ *lemma* box_integral.box.mk'_eq_bot
- \+ *lemma* box_integral.box.mk'_eq_coe
- \+ *lemma* box_integral.box.monotone_upper
- \+ *lemma* box_integral.box.ne_of_disjoint_coe
- \+ *lemma* box_integral.box.nndist_le_distortion_mul
- \+ *lemma* box_integral.box.nonempty_coe
- \+ *lemma* box_integral.box.not_disjoint_coe_iff_nonempty_inter
- \+ *lemma* box_integral.box.upper_mem
- \+ *lemma* box_integral.box.upper_mem_Icc
- \+ *lemma* box_integral.box.with_bot_coe_inj
- \+ *lemma* box_integral.box.with_bot_coe_subset_iff
- \+ *structure* box_integral.box

Added src/analysis/box_integral/box/subbox_induction.lean
- \+ *lemma* box_integral.box.Union_coe_split_center_box
- \+ *lemma* box_integral.box.disjoint_split_center_box
- \+ *lemma* box_integral.box.exists_mem_split_center_box
- \+ *lemma* box_integral.box.injective_split_center_box
- \+ *lemma* box_integral.box.mem_split_center_box
- \+ *def* box_integral.box.split_center_box
- \+ *def* box_integral.box.split_center_box_emb
- \+ *lemma* box_integral.box.split_center_box_le
- \+ *lemma* box_integral.box.subbox_induction_on'
- \+ *lemma* box_integral.box.upper_sub_lower_split_center_box

Added src/analysis/box_integral/divergence_theorem.lean
- \+ *lemma* box_integral.has_integral_bot_divergence_of_forall_has_deriv_within_at
- \+ *lemma* box_integral.has_integral_bot_pderiv
- \+ *lemma* box_integral.norm_volume_sub_integral_face_upper_sub_lower_smul_le

Added src/analysis/box_integral/integrability.lean
- \+ *lemma* box_integral.has_integral.congr_ae
- \+ *lemma* box_integral.has_integral_indicator_const
- \+ *lemma* box_integral.has_integral_zero_of_ae_eq_zero
- \+ *lemma* measure_theory.integrable_on.has_box_integral
- \+ *lemma* measure_theory.simple_func.box_integral_eq_integral
- \+ *lemma* measure_theory.simple_func.has_box_integral

Added src/analysis/box_integral/partition/additive.lean
- \+ *lemma* box_integral.box_additive_map.coe_inj
- \+ *lemma* box_integral.box_additive_map.coe_injective
- \+ *lemma* box_integral.box_additive_map.coe_mk
- \+ *def* box_integral.box_additive_map.map
- \+ *lemma* box_integral.box_additive_map.map_split_add
- \+ *def* box_integral.box_additive_map.of_map_split_add
- \+ *def* box_integral.box_additive_map.restrict
- \+ *lemma* box_integral.box_additive_map.sum_boxes_congr
- \+ *lemma* box_integral.box_additive_map.sum_partition_boxes
- \+ *lemma* box_integral.box_additive_map.to_fun_eq_coe
- \+ *def* box_integral.box_additive_map.to_smul
- \+ *lemma* box_integral.box_additive_map.to_smul_apply
- \+ *def* box_integral.box_additive_map.{u}
- \+ *structure* box_integral.box_additive_map

Added src/analysis/box_integral/partition/basic.lean
- \+ *lemma* box_integral.prepartition.Union_bUnion
- \+ *lemma* box_integral.prepartition.Union_bUnion_partition
- \+ *lemma* box_integral.prepartition.Union_bot
- \+ *lemma* box_integral.prepartition.Union_def'
- \+ *lemma* box_integral.prepartition.Union_def
- \+ *lemma* box_integral.prepartition.Union_disj_union
- \+ *lemma* box_integral.prepartition.Union_eq_empty
- \+ *lemma* box_integral.prepartition.Union_filter_not
- \+ *lemma* box_integral.prepartition.Union_inf
- \+ *lemma* box_integral.prepartition.Union_mono
- \+ *lemma* box_integral.prepartition.Union_of_with_bot
- \+ *lemma* box_integral.prepartition.Union_restrict
- \+ *lemma* box_integral.prepartition.Union_single
- \+ *lemma* box_integral.prepartition.Union_subset
- \+ *lemma* box_integral.prepartition.Union_top
- \+ *def* box_integral.prepartition.bUnion
- \+ *lemma* box_integral.prepartition.bUnion_assoc
- \+ *lemma* box_integral.prepartition.bUnion_congr
- \+ *lemma* box_integral.prepartition.bUnion_congr_of_le
- \+ *def* box_integral.prepartition.bUnion_index
- \+ *lemma* box_integral.prepartition.bUnion_index_le
- \+ *lemma* box_integral.prepartition.bUnion_index_mem
- \+ *lemma* box_integral.prepartition.bUnion_index_of_mem
- \+ *lemma* box_integral.prepartition.bUnion_le
- \+ *lemma* box_integral.prepartition.bUnion_le_iff
- \+ *lemma* box_integral.prepartition.bUnion_top
- \+ *lemma* box_integral.prepartition.bot_boxes
- \+ *lemma* box_integral.prepartition.card_filter_mem_Icc_le
- \+ *def* box_integral.prepartition.disj_union
- \+ *lemma* box_integral.prepartition.disjoint_boxes_of_disjoint_Union
- \+ *lemma* box_integral.prepartition.disjoint_coe_of_mem
- \+ *def* box_integral.prepartition.distortion
- \+ *lemma* box_integral.prepartition.distortion_bUnion
- \+ *lemma* box_integral.prepartition.distortion_bot
- \+ *lemma* box_integral.prepartition.distortion_disj_union
- \+ *lemma* box_integral.prepartition.distortion_le_iff
- \+ *lemma* box_integral.prepartition.distortion_le_of_mem
- \+ *lemma* box_integral.prepartition.distortion_of_const
- \+ *lemma* box_integral.prepartition.distortion_top
- \+ *lemma* box_integral.prepartition.eq_of_boxes_subset_Union_superset
- \+ *lemma* box_integral.prepartition.eq_of_le
- \+ *lemma* box_integral.prepartition.eq_of_le_of_le
- \+ *lemma* box_integral.prepartition.eq_of_mem_of_mem
- \+ *lemma* box_integral.prepartition.ext
- \+ *def* box_integral.prepartition.filter
- \+ *lemma* box_integral.prepartition.filter_le
- \+ *lemma* box_integral.prepartition.filter_of_true
- \+ *lemma* box_integral.prepartition.filter_true
- \+ *lemma* box_integral.prepartition.inf_def
- \+ *lemma* box_integral.prepartition.inj_on_set_of_mem_Icc_set_of_lower_eq
- \+ *lemma* box_integral.prepartition.injective_boxes
- \+ *lemma* box_integral.prepartition.is_partition.Union_eq
- \+ *lemma* box_integral.prepartition.is_partition.Union_subset
- \+ *lemma* box_integral.prepartition.is_partition.eq_of_boxes_subset
- \+ *lemma* box_integral.prepartition.is_partition.le_iff
- \+ *lemma* box_integral.prepartition.is_partition.nonempty_boxes
- \+ *def* box_integral.prepartition.is_partition
- \+ *lemma* box_integral.prepartition.is_partition_disj_union_of_eq_diff
- \+ *lemma* box_integral.prepartition.is_partition_iff_Union_eq
- \+ *lemma* box_integral.prepartition.is_partition_single_iff
- \+ *lemma* box_integral.prepartition.is_partition_top
- \+ *lemma* box_integral.prepartition.le_bUnion_iff
- \+ *lemma* box_integral.prepartition.le_bUnion_index
- \+ *lemma* box_integral.prepartition.le_def
- \+ *lemma* box_integral.prepartition.le_iff_nonempty_imp_le_and_Union_subset
- \+ *lemma* box_integral.prepartition.le_of_mem
- \+ *lemma* box_integral.prepartition.le_of_with_bot
- \+ *lemma* box_integral.prepartition.lower_le_lower
- \+ *lemma* box_integral.prepartition.mem_Union
- \+ *lemma* box_integral.prepartition.mem_bUnion
- \+ *lemma* box_integral.prepartition.mem_bUnion_index
- \+ *lemma* box_integral.prepartition.mem_boxes
- \+ *lemma* box_integral.prepartition.mem_disj_union
- \+ *lemma* box_integral.prepartition.mem_filter
- \+ *lemma* box_integral.prepartition.mem_inf
- \+ *lemma* box_integral.prepartition.mem_mk
- \+ *lemma* box_integral.prepartition.mem_of_with_bot
- \+ *lemma* box_integral.prepartition.mem_restrict'
- \+ *lemma* box_integral.prepartition.mem_restrict
- \+ *lemma* box_integral.prepartition.mem_single
- \+ *lemma* box_integral.prepartition.mem_top
- \+ *lemma* box_integral.prepartition.monotone_restrict
- \+ *lemma* box_integral.prepartition.not_mem_bot
- \+ *def* box_integral.prepartition.of_with_bot
- \+ *lemma* box_integral.prepartition.of_with_bot_le
- \+ *lemma* box_integral.prepartition.of_with_bot_mono
- \+ *def* box_integral.prepartition.restrict
- \+ *lemma* box_integral.prepartition.restrict_bUnion
- \+ *lemma* box_integral.prepartition.restrict_boxes_of_le
- \+ *lemma* box_integral.prepartition.restrict_mono
- \+ *lemma* box_integral.prepartition.restrict_self
- \+ *def* box_integral.prepartition.single
- \+ *lemma* box_integral.prepartition.subset_Union
- \+ *lemma* box_integral.prepartition.sum_bUnion_boxes
- \+ *lemma* box_integral.prepartition.sum_disj_union_boxes
- \+ *lemma* box_integral.prepartition.sum_fiberwise
- \+ *lemma* box_integral.prepartition.sum_of_with_bot
- \+ *lemma* box_integral.prepartition.top_boxes
- \+ *lemma* box_integral.prepartition.upper_le_upper
- \+ *structure* box_integral.prepartition

Added src/analysis/box_integral/partition/filter.lean
- \+ *def* box_integral.integration_params.Henstock
- \+ *lemma* box_integral.integration_params.Henstock_le_McShane
- \+ *lemma* box_integral.integration_params.Henstock_le_Riemann
- \+ *def* box_integral.integration_params.McShane
- \+ *def* box_integral.integration_params.Riemann
- \+ *lemma* box_integral.integration_params.bUnion_tagged_mem_base_set
- \+ *def* box_integral.integration_params.equiv_prod
- \+ *lemma* box_integral.integration_params.eventually_is_partition
- \+ *lemma* box_integral.integration_params.exists_mem_base_set_is_partition
- \+ *lemma* box_integral.integration_params.exists_mem_base_set_le_Union_eq
- \+ *lemma* box_integral.integration_params.has_basis_to_filter
- \+ *lemma* box_integral.integration_params.has_basis_to_filter_Union
- \+ *lemma* box_integral.integration_params.has_basis_to_filter_Union_top
- \+ *lemma* box_integral.integration_params.has_basis_to_filter_distortion
- \+ *lemma* box_integral.integration_params.has_basis_to_filter_distortion_Union
- \+ *def* box_integral.integration_params.iso_prod
- \+ *lemma* box_integral.integration_params.mem_base_set.exists_common_compl
- \+ *lemma* box_integral.integration_params.mem_base_set.mono'
- \+ *lemma* box_integral.integration_params.mem_base_set.mono
- \+ *structure* box_integral.integration_params.mem_base_set
- \+ *lemma* box_integral.integration_params.r_cond.min
- \+ *lemma* box_integral.integration_params.r_cond.mono
- \+ *def* box_integral.integration_params.r_cond
- \+ *lemma* box_integral.integration_params.r_cond_of_bRiemann_eq_ff
- \+ *lemma* box_integral.integration_params.tendsto_embed_box_to_filter_Union_top
- \+ *def* box_integral.integration_params.to_filter
- \+ *def* box_integral.integration_params.to_filter_Union
- \+ *lemma* box_integral.integration_params.to_filter_Union_congr
- \+ *lemma* box_integral.integration_params.to_filter_Union_mono
- \+ *def* box_integral.integration_params.to_filter_distortion
- \+ *def* box_integral.integration_params.to_filter_distortion_Union
- \+ *lemma* box_integral.integration_params.to_filter_distortion_Union_ne_bot
- \+ *lemma* box_integral.integration_params.to_filter_distortion_mono
- \+ *lemma* box_integral.integration_params.to_filter_inf_Union_eq
- \+ *lemma* box_integral.integration_params.to_filter_mono
- \+ *structure* box_integral.integration_params

Added src/analysis/box_integral/partition/measure.lean
- \+ *lemma* box_integral.box.measurable_set_Icc
- \+ *lemma* box_integral.box.measurable_set_coe
- \+ *lemma* box_integral.box.measure_Icc_lt_top
- \+ *lemma* box_integral.box.measure_coe_lt_top
- \+ *lemma* box_integral.box.volume_apply
- \+ *lemma* box_integral.box.volume_face_mul
- \+ *lemma* box_integral.box_additive_map.volume_apply
- \+ *lemma* box_integral.prepartition.measure_Union_to_real
- \+ *def* measure_theory.measure.to_box_additive

Added src/analysis/box_integral/partition/split.lean
- \+ *lemma* box_integral.box.coe_split_lower
- \+ *lemma* box_integral.box.coe_split_upper
- \+ *lemma* box_integral.box.disjoint_split_lower_split_upper
- \+ *def* box_integral.box.split_lower
- \+ *lemma* box_integral.box.split_lower_def
- \+ *lemma* box_integral.box.split_lower_eq_bot
- \+ *lemma* box_integral.box.split_lower_eq_self
- \+ *lemma* box_integral.box.split_lower_le
- \+ *lemma* box_integral.box.split_lower_ne_split_upper
- \+ *def* box_integral.box.split_upper
- \+ *lemma* box_integral.box.split_upper_def
- \+ *lemma* box_integral.box.split_upper_eq_bot
- \+ *lemma* box_integral.box.split_upper_eq_self
- \+ *lemma* box_integral.box.split_upper_le
- \+ *lemma* box_integral.prepartition.Union_compl
- \+ *lemma* box_integral.prepartition.Union_split
- \+ *lemma* box_integral.prepartition.Union_split_many
- \+ *lemma* box_integral.prepartition.coe_eq_of_mem_split_of_lt_mem
- \+ *lemma* box_integral.prepartition.coe_eq_of_mem_split_of_mem_le
- \+ *def* box_integral.prepartition.compl
- \+ *lemma* box_integral.prepartition.compl_congr
- \+ *lemma* box_integral.prepartition.compl_top
- \+ *lemma* box_integral.prepartition.eventually_not_disjoint_imp_le_of_mem_split_many
- \+ *lemma* box_integral.prepartition.eventually_split_many_inf_eq_filter
- \+ *lemma* box_integral.prepartition.exists_Union_eq_diff
- \+ *lemma* box_integral.prepartition.exists_split_many_inf_eq_filter_of_finite
- \+ *lemma* box_integral.prepartition.inf_split
- \+ *lemma* box_integral.prepartition.inf_split_many
- \+ *lemma* box_integral.prepartition.is_partition.compl_eq_bot
- \+ *lemma* box_integral.prepartition.is_partition.exists_split_many_le
- \+ *lemma* box_integral.prepartition.is_partition_split
- \+ *lemma* box_integral.prepartition.is_partition_split_many
- \+ *lemma* box_integral.prepartition.mem_split_iff'
- \+ *lemma* box_integral.prepartition.mem_split_iff
- \+ *lemma* box_integral.prepartition.not_disjoint_imp_le_of_subset_of_mem_split_many
- \+ *lemma* box_integral.prepartition.restrict_split
- \+ *def* box_integral.prepartition.split
- \+ *def* box_integral.prepartition.split_many
- \+ *lemma* box_integral.prepartition.split_many_empty
- \+ *lemma* box_integral.prepartition.split_many_insert
- \+ *lemma* box_integral.prepartition.split_many_le_split
- \+ *lemma* box_integral.prepartition.split_of_not_mem_Ioo
- \+ *lemma* box_integral.prepartition.sum_split_boxes

Added src/analysis/box_integral/partition/subbox_induction.lean
- \+ *lemma* box_integral.box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic
- \+ *lemma* box_integral.box.subbox_induction_on
- \+ *lemma* box_integral.prepartition.Union_to_subordinate
- \+ *lemma* box_integral.prepartition.distortion_to_subordinate
- \+ *lemma* box_integral.prepartition.exists_tagged_le_is_Henstock_is_subordinate_Union_eq
- \+ *lemma* box_integral.prepartition.is_Henstock_to_subordinate
- \+ *lemma* box_integral.prepartition.is_partition_split_center
- \+ *lemma* box_integral.prepartition.is_subordinate_to_subordinate
- \+ *lemma* box_integral.prepartition.mem_split_center
- \+ *def* box_integral.prepartition.split_center
- \+ *def* box_integral.prepartition.to_subordinate
- \+ *lemma* box_integral.prepartition.to_subordinate_to_prepartition_le
- \+ *lemma* box_integral.prepartition.upper_sub_lower_of_mem_split_center
- \+ *lemma* box_integral.tagged_prepartition.Union_union_compl_to_subordinate_boxes
- \+ *lemma* box_integral.tagged_prepartition.distortion_union_compl_to_subordinate
- \+ *lemma* box_integral.tagged_prepartition.is_partition_union_compl_to_subordinate
- \+ *def* box_integral.tagged_prepartition.union_compl_to_subordinate
- \+ *lemma* box_integral.tagged_prepartition.union_compl_to_subordinate_boxes

Added src/analysis/box_integral/partition/tagged.lean
- \+ *lemma* box_integral.prepartition.Union_bUnion_tagged
- \+ *def* box_integral.prepartition.bUnion_tagged
- \+ *lemma* box_integral.prepartition.distortion_bUnion_tagged
- \+ *lemma* box_integral.prepartition.forall_bUnion_tagged
- \+ *lemma* box_integral.prepartition.is_partition.bUnion_tagged
- \+ *lemma* box_integral.prepartition.mem_bUnion_tagged
- \+ *lemma* box_integral.prepartition.tag_bUnion_tagged
- \+ *def* box_integral.tagged_prepartition.Union
- \+ *lemma* box_integral.tagged_prepartition.Union_def
- \+ *lemma* box_integral.tagged_prepartition.Union_disj_union
- \+ *lemma* box_integral.tagged_prepartition.Union_filter_not
- \+ *lemma* box_integral.tagged_prepartition.Union_mk
- \+ *lemma* box_integral.tagged_prepartition.Union_single
- \+ *lemma* box_integral.tagged_prepartition.Union_subset
- \+ *lemma* box_integral.tagged_prepartition.Union_to_prepartition
- \+ *def* box_integral.tagged_prepartition.bUnion_prepartition
- \+ *def* box_integral.tagged_prepartition.disj_union
- \+ *lemma* box_integral.tagged_prepartition.disj_union_boxes
- \+ *lemma* box_integral.tagged_prepartition.disj_union_tag_of_mem_left
- \+ *lemma* box_integral.tagged_prepartition.disj_union_tag_of_mem_right
- \+ *def* box_integral.tagged_prepartition.distortion
- \+ *lemma* box_integral.tagged_prepartition.distortion_bUnion_prepartition
- \+ *lemma* box_integral.tagged_prepartition.distortion_disj_union
- \+ *lemma* box_integral.tagged_prepartition.distortion_filter_le
- \+ *lemma* box_integral.tagged_prepartition.distortion_le_iff
- \+ *lemma* box_integral.tagged_prepartition.distortion_le_of_mem
- \+ *lemma* box_integral.tagged_prepartition.distortion_of_const
- \+ *lemma* box_integral.tagged_prepartition.distortion_single
- \+ *def* box_integral.tagged_prepartition.embed_box
- \+ *def* box_integral.tagged_prepartition.filter
- \+ *lemma* box_integral.tagged_prepartition.forall_mem_single
- \+ *def* box_integral.tagged_prepartition.inf_prepartition
- \+ *lemma* box_integral.tagged_prepartition.inf_prepartition_to_prepartition
- \+ *lemma* box_integral.tagged_prepartition.is_Henstock.card_filter_tag_eq_le
- \+ *lemma* box_integral.tagged_prepartition.is_Henstock.disj_union
- \+ *def* box_integral.tagged_prepartition.is_Henstock
- \+ *lemma* box_integral.tagged_prepartition.is_Henstock_bUnion_tagged
- \+ *lemma* box_integral.tagged_prepartition.is_Henstock_single
- \+ *lemma* box_integral.tagged_prepartition.is_Henstock_single_iff
- \+ *lemma* box_integral.tagged_prepartition.is_partition.bUnion_prepartition
- \+ *lemma* box_integral.tagged_prepartition.is_partition.inf_prepartition
- \+ *def* box_integral.tagged_prepartition.is_partition
- \+ *lemma* box_integral.tagged_prepartition.is_partition_iff_Union_eq
- \+ *lemma* box_integral.tagged_prepartition.is_partition_single
- \+ *lemma* box_integral.tagged_prepartition.is_partition_single_iff
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.diam_le
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.disj_union
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.inf_prepartition
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.mono'
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate.mono
- \+ *def* box_integral.tagged_prepartition.is_subordinate
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate_bUnion_tagged
- \+ *lemma* box_integral.tagged_prepartition.is_subordinate_single
- \+ *lemma* box_integral.tagged_prepartition.mem_Union
- \+ *lemma* box_integral.tagged_prepartition.mem_disj_union
- \+ *lemma* box_integral.tagged_prepartition.mem_filter
- \+ *lemma* box_integral.tagged_prepartition.mem_inf_prepartition_comm
- \+ *lemma* box_integral.tagged_prepartition.mem_mk
- \+ *lemma* box_integral.tagged_prepartition.mem_single
- \+ *lemma* box_integral.tagged_prepartition.mem_to_prepartition
- \+ *def* box_integral.tagged_prepartition.single
- \+ *lemma* box_integral.tagged_prepartition.subset_Union
- \+ *structure* box_integral.tagged_prepartition

Modified src/data/set/lattice.lean
- \+ *lemma* set.bUnion_diff_bUnion_eq
- \+ *lemma* set.bUnion_diff_bUnion_subset

Modified src/logic/function/basic.lean
- \+ *lemma* function.exists_update_iff

Modified src/topology/metric_space/basic.lean
- \+ *lemma* real.dist_le_of_mem_pi_Icc



## [2021-10-18 23:50:42](https://github.com/leanprover-community/mathlib/commit/5eee6a2)
refactor(ring_theory/adjoin/fg): replace a fragile convert with rewrites ([#9786](https://github.com/leanprover-community/mathlib/pull/9786))
#### Estimated changes
Modified src/ring_theory/adjoin/fg.lean




## [2021-10-18 23:50:41](https://github.com/leanprover-community/mathlib/commit/98d07d3)
refactor(algebra/order): replace typeclasses with constructors ([#9725](https://github.com/leanprover-community/mathlib/pull/9725))
This RFC suggests removing some unused classes for the ordered algebra hierarchy, replacing them with constructors
We have `nonneg_add_comm_group extends add_comm_group`, and an instance from this to `ordered_add_comm_group`. The intention is to be able to construct an `ordered_add_comm_group` by specifying its positive cone, rather than directly its order.
There are then `nonneg_ring` and `linear_nonneg_ring`, similarly.
(None of these are actually used later in mathlib at this point.)
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *structure* add_comm_group.positive_cone
- \+ *structure* add_comm_group.total_positive_cone
- \+ *def* linear_ordered_add_comm_group.mk_of_positive_cone
- \- *theorem* nonneg_add_comm_group.nonneg_def
- \- *theorem* nonneg_add_comm_group.nonneg_total_iff
- \- *theorem* nonneg_add_comm_group.not_zero_pos
- \- *theorem* nonneg_add_comm_group.pos_def
- \- *def* nonneg_add_comm_group.to_linear_ordered_add_comm_group
- \- *theorem* nonneg_add_comm_group.zero_lt_iff_nonneg_nonneg
- \+ *def* ordered_add_comm_group.mk_of_positive_cone

Modified src/algebra/order/ring.lean
- \- *def* linear_nonneg_ring.to_linear_order
- \- *def* linear_nonneg_ring.to_linear_ordered_comm_ring
- \- *def* linear_nonneg_ring.to_linear_ordered_ring
- \+ *def* linear_ordered_ring.mk_of_positive_cone
- \- *def* nonneg_ring.to_linear_nonneg_ring
- \+ *def* ordered_ring.mk_of_positive_cone
- \+ *structure* ring.positive_cone
- \+ *structure* ring.total_positive_cone



## [2021-10-18 23:50:40](https://github.com/leanprover-community/mathlib/commit/442382d)
feat(tactic/to_additive): Improvements to to_additive ([#5487](https://github.com/leanprover-community/mathlib/pull/5487))
Change a couple of things in to_additive:
- First add a `tactic.copy_attribute'` intended for user attributes with parameters very similar to `tactic.copy_attribute` that just copies the parameter over when setting the attribute. This allows to_additive after many other attributes to transfer those attributes properly (e.g. norm_cast)
- Have to additive register generated equation lemmas as such, this necessitates a bit of restructuring, first all declarations must be generated (including equational lemmas), then the equational lemmas need their attributes, then they are registered as equation lemmas, finally the attributes are added to the main declaration.
- I also fixup the library in many places to account for these changes simplifying the source files, only one new lemma was added, in src/analysis/normed/group/quotient.lean `quotient_norm_mk_le'` to replace the unprimed version in the proof of `norm_normed_mk_le` as simp got better thanks to the new simp lemmas introduced by this PR. Probably many more handwritten additive versions can now be deleted in a future PR, especially defs and instances.
- All other library changes are just simplifications by using to additive for some hand generated declarations, and many more attributes on the generated lemmas.
- The attribute mono is trickier as it contains for its parameter not actual exprs containing names but exprs making names from strings, so I don't see how to handle it right now. We now warn the user about this, and fix the library in a couple of places.
#### Estimated changes
Modified src/algebra/big_operators/order.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/filtered_colimits.lean


Modified src/algebra/free.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/order/monoid.lean
- \+/\- *lemma* with_top.coe_eq_one
- \+/\- *lemma* with_top.coe_one
- \+/\- *theorem* with_top.one_eq_coe

Modified src/analysis/normed/group/quotient.lean
- \+ *lemma* quotient_norm_mk_le'
- \+/\- *lemma* quotient_norm_sub_rev

Modified src/data/dfinsupp.lean
- \- *def* dfinsupp.sum

Modified src/data/equiv/mul_add.lean
- \- *def* add_monoid_hom.to_add_equiv

Modified src/data/equiv/mul_add_aut.lean


Modified src/data/finsupp/basic.lean
- \- *def* finsupp.sum

Modified src/data/multiset/basic.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/coset.lean
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* one_left_coset
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* right_coset_one

Modified src/group_theory/group_action/defs.lean


Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* submonoid.localization_map.ext

Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.to_submonoid_strict_mono

Modified src/group_theory/submonoid/basic.lean
- \+/\- *lemma* monoid_hom.coe_of_mdense

Modified src/group_theory/submonoid/membership.lean


Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* submonoid.coe_mul
- \+/\- *lemma* submonoid.coe_one

Modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_div

Modified src/order/filter/germ.lean


Modified src/tactic/transform_decl.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* open_subgroup.coe_inf
- \+/\- *lemma* open_subgroup.coe_subgroup_le
- \+/\- *lemma* open_subgroup.coe_subset
- \+/\- *lemma* open_subgroup.mem_coe
- \+/\- *lemma* open_subgroup.mem_coe_opens

Modified src/topology/tactic.lean


Modified test/to_additive.lean
- \- *def* foo0
- \- *def* foo1
- \- *def* foo2
- \- *def* foo3
- \- *lemma* foo4_test
- \- *def* foo5
- \- *def* foo6
- \- *def* foo7
- \- *def* foo_mul
- \- *def* nat_pi_has_one
- \- *def* pi_nat_has_one
- \- *def* some_def.in_namespace
- \- *def* some_def
- \+ *def* test.foo0
- \+ *def* test.foo1
- \+ *def* test.foo2
- \+ *def* test.foo3
- \+ *lemma* test.foo4_test
- \+ *def* test.foo5
- \+ *def* test.foo6
- \+ *def* test.foo7
- \+ *def* test.foo_mul
- \+ *def* test.nat_pi_has_one
- \+ *def* test.pi_nat_has_one
- \+ *def* test.some_def.in_namespace
- \+ *def* test.some_def
- \+ *def* test.{a
- \- *def* {a



## [2021-10-18 21:08:15](https://github.com/leanprover-community/mathlib/commit/8b7e16f)
feat(tactic/lint): improve check_univs linter ([#9698](https://github.com/leanprover-community/mathlib/pull/9698))
* `check_univs` now only checks the type of `d` and ignores `d._proof_i` subterms
* move `expr.univ_params_grouped` to the linter file (it seems increasingly unlikely that this has a use in other applications)
* We now don't test automatically generated declarations anymore.
#### Estimated changes
Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Groupoid.lean


Modified src/category_theory/category/Quiv.lean


Modified src/meta/expr.lean


Modified src/model_theory/basic.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/zfc.lean


Modified src/tactic/lint/misc.lean




## [2021-10-18 17:55:59](https://github.com/leanprover-community/mathlib/commit/b112d4d)
refactor(ring_theory/ideal/operations): generalize various definitions to remove negation and commutativity ([#9737](https://github.com/leanprover-community/mathlib/pull/9737))
Mostly this just weakens assumptions in `variable`s lines, but occasionally this moves lemmas to a more appropriate section too.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+/\- *theorem* ideal.comap_is_maximal_of_surjective
- \+/\- *lemma* ideal.comap_le_iff_le_map
- \+/\- *theorem* ideal.comap_map_of_surjective
- \+/\- *theorem* ideal.map.is_maximal
- \+/\- *theorem* ideal.map_eq_top_or_is_maximal_of_surjective
- \+/\- *def* ideal.rel_iso_of_surjective
- \+/\- *theorem* ideal.subset_union
- \+/\- *theorem* ideal.subset_union_prime'
- \+/\- *theorem* ideal.subset_union_prime

Modified src/ring_theory/jacobson.lean




## [2021-10-18 16:41:10](https://github.com/leanprover-community/mathlib/commit/71c203a)
feat(analysis/normed/group/SemiNormedGroup/completion): add SemiNormedGroup.Completion ([#9788](https://github.com/leanprover-community/mathlib/pull/9788))
From LTE.
#### Estimated changes
Added src/analysis/normed/group/SemiNormedGroup/completion.lean
- \+ *def* SemiNormedGroup.Completion.incl
- \+ *def* SemiNormedGroup.Completion.lift
- \+ *lemma* SemiNormedGroup.Completion.lift_comp_incl
- \+ *lemma* SemiNormedGroup.Completion.lift_unique
- \+ *def* SemiNormedGroup.Completion.map_hom
- \+ *lemma* SemiNormedGroup.Completion.map_norm_noninc
- \+ *lemma* SemiNormedGroup.Completion.map_zero
- \+ *lemma* SemiNormedGroup.Completion.norm_incl_eq
- \+ *def* SemiNormedGroup.Completion

Modified src/analysis/normed/group/hom_completion.lean
- \+ *def* normed_group_hom.extension
- \+ *lemma* normed_group_hom.extension_coe
- \+ *lemma* normed_group_hom.extension_coe_to_fun
- \+ *lemma* normed_group_hom.extension_def
- \+ *lemma* normed_group_hom.extension_unique



## [2021-10-18 16:41:09](https://github.com/leanprover-community/mathlib/commit/80071d4)
refactor(algebra/floor): Add `ceil` as a field of `floor_ring` ([#9591](https://github.com/leanprover-community/mathlib/pull/9591))
This allows more control on definitional equality.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/floor.lean
- \+ *def* floor_ring.of_ceil
- \+ *def* floor_ring.of_floor
- \+/\- *def* int.ceil
- \+/\- *lemma* int.ceil_eq_iff
- \+/\- *lemma* int.ceil_le
- \+/\- *lemma* int.ceil_mono
- \+/\- *lemma* int.ceil_neg
- \+/\- *lemma* int.ceil_nonneg
- \+/\- *lemma* int.ceil_pos
- \+/\- *lemma* int.floor_eq_iff
- \+/\- *lemma* int.floor_le
- \+/\- *lemma* int.floor_lt
- \+/\- *lemma* int.floor_mono
- \+/\- *lemma* int.floor_neg
- \+/\- *lemma* int.floor_nonneg
- \+ *lemma* int.floor_ring_ceil_eq
- \+ *lemma* int.floor_ring_floor_eq
- \+ *lemma* int.gc_ceil_coe
- \+ *lemma* int.gc_coe_floor
- \+/\- *lemma* int.le_ceil
- \+/\- *lemma* int.le_floor
- \+/\- *lemma* int.lt_ceil
- \+/\- *lemma* int.preimage_Ici
- \+/\- *lemma* int.preimage_Iic
- \+/\- *lemma* int.preimage_Iio
- \+/\- *lemma* int.preimage_Ioi
- \+/\- *lemma* nat.ceil_add_nat
- \+/\- *lemma* nat.ceil_add_one
- \+/\- *lemma* nat.ceil_lt_add_one
- \+/\- *lemma* nat.floor_add_one
- \+/\- *lemma* nat.le_of_ceil_le
- \+/\- *lemma* nat.lt_of_ceil_lt

Modified src/data/rat/floor.lean


Modified src/topology/algebra/floor_ring.lean




## [2021-10-18 14:15:51](https://github.com/leanprover-community/mathlib/commit/5ea384e)
refactor(ring_theory/finiteness): replace fragile convert with rewrites ([#9787](https://github.com/leanprover-community/mathlib/pull/9787))
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* subalgebra.coe_restrict_scalars

Modified src/ring_theory/finiteness.lean




## [2021-10-18 14:15:49](https://github.com/leanprover-community/mathlib/commit/6f4aea4)
feat(data/set/pairwise): Simple `pairwise_disjoint` lemmas ([#9764](https://github.com/leanprover-community/mathlib/pull/9764))
#### Estimated changes
Modified src/algebra/support.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.disjoint_singleton
- \- *theorem* finset.disjoint_singleton
- \+ *theorem* finset.disjoint_singleton_left
- \+ *theorem* finset.disjoint_singleton_right
- \- *theorem* finset.singleton_disjoint

Modified src/data/finsupp/basic.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_singleton

Modified src/data/set/pairwise.lean
- \+/\- *lemma* set.pairwise_disjoint.elim'
- \+/\- *lemma* set.pairwise_disjoint.elim
- \+ *lemma* set.pairwise_disjoint.image_of_le
- \+ *lemma* set.pairwise_disjoint.insert
- \+/\- *lemma* set.pairwise_disjoint.range
- \+/\- *lemma* set.pairwise_disjoint.subset
- \+ *lemma* set.pairwise_disjoint_empty
- \+ *lemma* set.pairwise_disjoint_insert
- \+ *lemma* set.pairwise_disjoint_range_singleton
- \+ *lemma* set.pairwise_disjoint_singleton

Modified src/geometry/euclidean/circumcenter.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/separation.lean




## [2021-10-18 12:53:50](https://github.com/leanprover-community/mathlib/commit/116e426)
chore(group_theory/order_of_element): order_of_units ([#9777](https://github.com/leanprover-community/mathlib/pull/9777))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_units



## [2021-10-18 12:53:48](https://github.com/leanprover-community/mathlib/commit/a7ac699)
feat(topology/metric_space): dimH is the supr of local dimH ([#9741](https://github.com/leanprover-community/mathlib/pull/9741))
#### Estimated changes
Modified src/topology/metric_space/hausdorff_dimension.lean
- \+ *lemma* bsupr_limsup_dimH
- \+ *lemma* exists_mem_nhds_within_lt_dimH_of_lt_dimH
- \+ *lemma* supr_limsup_dimH



## [2021-10-18 12:53:47](https://github.com/leanprover-community/mathlib/commit/06179ca)
feat(data/real/pointwise): Inf and Sup of `a • s` for `s : set ℝ` ([#9707](https://github.com/leanprover-community/mathlib/pull/9707))
This relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.
#### Estimated changes
Added src/data/real/pointwise.lean
- \+ *lemma* real.Inf_smul_of_nonneg
- \+ *lemma* real.Inf_smul_of_nonpos
- \+ *lemma* real.Sup_smul_of_nonneg
- \+ *lemma* real.Sup_smul_of_nonpos



## [2021-10-18 11:21:22](https://github.com/leanprover-community/mathlib/commit/e841325)
feat(linear_algebra/dfinsupp): cardinality lemmas for `complete_lattice.independent` ([#9705](https://github.com/leanprover-community/mathlib/pull/9705))
If `p` is a system of independent subspaces of a vector space `V`, and `v` is a system of nonzero vectors each contained in the corresponding subspace, then `v` is linearly independent.
Consequently, if `p` is a system of independent subspaces of `V`, then no more than `dim V` many can be nontrivial.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_map.to_span_singleton

Modified src/linear_algebra/dfinsupp.lean
- \+/\- *lemma* complete_lattice.independent.dfinsupp_lsum_injective
- \+ *lemma* complete_lattice.independent.linear_independent
- \+/\- *lemma* complete_lattice.independent_iff_dfinsupp_lsum_injective
- \+/\- *lemma* complete_lattice.independent_iff_forall_dfinsupp
- \+/\- *lemma* complete_lattice.independent_of_dfinsupp_lsum_injective
- \+ *lemma* complete_lattice.lsum_comp_map_range_to_span_singleton

Modified src/linear_algebra/dimension.lean
- \+ *lemma* cardinal_lift_le_dim_of_linear_independent'
- \+ *lemma* complete_lattice.independent.subtype_ne_bot_le_rank

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* complete_lattice.independent.subtype_ne_bot_le_finrank
- \+ *lemma* complete_lattice.independent.subtype_ne_bot_le_finrank_aux



## [2021-10-18 09:32:36](https://github.com/leanprover-community/mathlib/commit/39db98c)
feat(analysis/normed_space/add_torsor_bases): the convex hull has non-empty interior iff the affine span is top ([#9727](https://github.com/leanprover-community/mathlib/pull/9727))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* affine_subspace.convex

Modified src/analysis/convex/hull.lean
- \+ *lemma* affine_span_convex_hull
- \+/\- *lemma* convex_hull_mono
- \+ *lemma* convex_hull_subset_affine_span

Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* interior_convex_hull_nonempty_iff_aff_span_eq_top

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_map.line_map_mem
- \+ *lemma* affine_span_le

Modified src/topology/basic.lean
- \+/\- *lemma* interior_mono



## [2021-10-18 08:20:00](https://github.com/leanprover-community/mathlib/commit/2e62b33)
chore(field_theory/galois): speedup a slow convert ([#9782](https://github.com/leanprover-community/mathlib/pull/9782))
This was broken by a deterministic timeout in another branch. This replaces a `convert` with an explicit `simp`.
#### Estimated changes
Modified src/field_theory/galois.lean




## [2021-10-18 08:19:59](https://github.com/leanprover-community/mathlib/commit/27d28a8)
feat(linear_algebra/affine_space/independent): affine equivalences preserve affine independence of sets of points ([#9776](https://github.com/leanprover-community/mathlib/pull/9776))
The key addition is `affine_equiv.affine_independent_set_of_eq_iff`.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_equiv.affine_independent_set_of_eq_iff
- \+ *lemma* affine_independent_equiv
- \- *lemma* affine_map.homothety_affine_independent_iff



## [2021-10-18 08:19:58](https://github.com/leanprover-community/mathlib/commit/fb5c0be)
feat(topology/metric_space): closed if spaced out ([#9754](https://github.com/leanprover-community/mathlib/pull/9754))
If pairwise distances between the points of a set are bounded from below by a positive number, then the set is closed.
Also prove some theorems about `uniform_inducing` and `uniform_embedding` and show that `coe : int → real` is a closed embedding.
#### Estimated changes
Modified src/number_theory/liouville/residual.lean


Modified src/topology/instances/real.lean
- \- *theorem* continuous_of_rat
- \- *theorem* dense_embedding_of_rat
- \- *theorem* embedding_of_rat
- \+ *lemma* int.closed_embedding_coe_rat
- \+ *lemma* int.closed_embedding_coe_real
- \+ *lemma* int.pairwise_one_le_dist
- \+ *lemma* int.uniform_embedding_coe_rat
- \+ *theorem* rat.continuous_coe_real
- \+ *theorem* rat.dense_embedding_coe_real
- \+/\- *lemma* rat.dist_cast
- \+/\- *theorem* rat.dist_eq
- \+ *theorem* rat.embedding_coe_real
- \+ *theorem* rat.uniform_continuous_coe_real
- \+ *theorem* rat.uniform_embedding_coe_real
- \- *theorem* uniform_continuous_of_rat
- \- *theorem* uniform_embedding_of_rat

Modified src/topology/instances/real_vector_space.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.closed_embedding_of_pairwise_le_dist
- \+ *lemma* metric.is_closed_of_pairwise_on_le_dist
- \+ *lemma* metric.uniform_embedding_bot_of_pairwise_le_dist

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* mem_uniformity_of_eq

Modified src/topology/uniform_space/compare_reals.lean


Modified src/topology/uniform_space/separation.lean
- \+ *lemma* is_closed_range_of_spaced_out

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* closed_embedding_of_spaced_out
- \+ *lemma* comap_uniformity_of_spaced_out
- \+ *lemma* uniform_embedding_of_spaced_out
- \+ *lemma* uniform_inducing.basis_uniformity
- \+ *theorem* uniform_inducing.uniform_embedding



## [2021-10-18 05:53:11](https://github.com/leanprover-community/mathlib/commit/6cd6ff4)
split(data/list/permutation): split off `data.list.basic` ([#9749](https://github.com/leanprover-community/mathlib/pull/9749))
This moves all the `list.permutations` definitions and lemmas not involving `list.perm` to a new file.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *theorem* list.foldr_permutations_aux2
- \- *theorem* list.length_foldr_permutations_aux2'
- \- *theorem* list.length_foldr_permutations_aux2
- \- *theorem* list.length_permutations_aux2
- \- *theorem* list.map_map_permutations'_aux
- \- *theorem* list.map_map_permutations_aux2
- \- *theorem* list.map_permutations'
- \- *theorem* list.map_permutations
- \- *theorem* list.map_permutations_aux2'
- \- *theorem* list.map_permutations_aux2
- \- *theorem* list.map_permutations_aux
- \- *theorem* list.mem_foldr_permutations_aux2
- \- *theorem* list.mem_permutations_aux2'
- \- *theorem* list.mem_permutations_aux2
- \- *theorem* list.permutations'_aux_eq_permutations_aux2
- \- *theorem* list.permutations_append
- \- *theorem* list.permutations_aux2_append
- \- *theorem* list.permutations_aux2_comp_append
- \- *theorem* list.permutations_aux2_fst
- \- *theorem* list.permutations_aux2_snd_cons
- \- *lemma* list.permutations_aux2_snd_eq
- \- *theorem* list.permutations_aux2_snd_nil
- \- *theorem* list.permutations_aux_append
- \- *theorem* list.permutations_aux_cons
- \- *theorem* list.permutations_aux_nil
- \- *theorem* list.permutations_nil

Modified src/data/list/defs.lean


Modified src/data/list/perm.lean


Added src/data/list/permutation.lean
- \+ *lemma* list.foldr_permutations_aux2
- \+ *lemma* list.length_foldr_permutations_aux2'
- \+ *lemma* list.length_foldr_permutations_aux2
- \+ *lemma* list.length_permutations_aux2
- \+ *lemma* list.map_map_permutations'_aux
- \+ *lemma* list.map_map_permutations_aux2
- \+ *lemma* list.map_permutations'
- \+ *lemma* list.map_permutations
- \+ *lemma* list.map_permutations_aux2'
- \+ *lemma* list.map_permutations_aux2
- \+ *lemma* list.map_permutations_aux
- \+ *lemma* list.mem_foldr_permutations_aux2
- \+ *lemma* list.mem_permutations_aux2'
- \+ *lemma* list.mem_permutations_aux2
- \+ *lemma* list.permutations'_aux_eq_permutations_aux2
- \+ *lemma* list.permutations_append
- \+ *lemma* list.permutations_aux2_append
- \+ *lemma* list.permutations_aux2_comp_append
- \+ *lemma* list.permutations_aux2_fst
- \+ *lemma* list.permutations_aux2_snd_cons
- \+ *lemma* list.permutations_aux2_snd_eq
- \+ *lemma* list.permutations_aux2_snd_nil
- \+ *lemma* list.permutations_aux_append
- \+ *lemma* list.permutations_aux_cons
- \+ *lemma* list.permutations_aux_nil
- \+ *lemma* list.permutations_nil



## [2021-10-18 02:28:14](https://github.com/leanprover-community/mathlib/commit/5b527bd)
refactor(linear_algebra/quadratic_form): split file ([#9781](https://github.com/leanprover-community/mathlib/pull/9781))
The section on quadratic forms over complex numbers required pulling in the developing of the complex power function, which significantly increases the import depth. Splitting this file allows `clifford_algebra` to be compiled much earlier.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/basic.lean


Renamed src/linear_algebra/quadratic_form.lean to src/linear_algebra/quadratic_form/basic.lean
- \- *theorem* quadratic_form.equivalent_one_neg_one_weighted_sum_squared
- \- *theorem* quadratic_form.equivalent_one_zero_neg_one_weighted_sum_squared
- \- *theorem* quadratic_form.equivalent_sum_squares

Added src/linear_algebra/quadratic_form/complex.lean
- \+ *theorem* quadratic_form.equivalent_sum_squares

Added src/linear_algebra/quadratic_form/real.lean
- \+ *theorem* quadratic_form.equivalent_one_neg_one_weighted_sum_squared
- \+ *theorem* quadratic_form.equivalent_one_zero_neg_one_weighted_sum_squared



## [2021-10-17 21:55:29](https://github.com/leanprover-community/mathlib/commit/27a777b)
feat(data/nat/gcd): `coprime.lcm_eq_mul` ([#9761](https://github.com/leanprover-community/mathlib/pull/9761))
Surprisingly, this result doesn't seem to be present yet.
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+/\- *theorem* nat.coprime.gcd_eq_one
- \+ *theorem* nat.coprime.lcm_eq_mul



## [2021-10-17 20:43:58](https://github.com/leanprover-community/mathlib/commit/5dbe8c4)
feat(topology/metric_space): a map with a contracting iterate has a fixed pt ([#9760](https://github.com/leanprover-community/mathlib/pull/9760))
#### Estimated changes
Modified src/topology/metric_space/contracting.lean
- \+ *lemma* contracting_with.is_fixed_pt_fixed_point_iterate



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
Modified src/algebra/order/field.lean
- \+/\- *lemma* div_le_div_of_le_left

Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* exp_eq_exp
- \- *lemma* exp_eq_exp_of_field_extension
- \+ *lemma* exp_series_eq_exp_series
- \- *lemma* exp_series_eq_exp_series_of_field_extension

Modified src/analysis/specific_limits.lean
- \+ *lemma* real.summable_pow_div_factorial
- \+ *lemma* real.tendsto_pow_div_factorial_at_top

Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.cast_lt
- \+/\- *theorem* nat.mono_cast



## [2021-10-17 13:18:35](https://github.com/leanprover-community/mathlib/commit/376bba8)
chore(data/finset/lattice): fix infi docstrings ([#9775](https://github.com/leanprover-community/mathlib/pull/9775))
#### Estimated changes
Modified src/data/finset/lattice.lean




## [2021-10-17 13:18:34](https://github.com/leanprover-community/mathlib/commit/41b5645)
chore(topology/algebra/ordered/basic): move code out of `basic` ([#9772](https://github.com/leanprover-community/mathlib/pull/9772))
#### Estimated changes
Modified src/data/real/sqrt.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* tendsto_inv_nhds_within_Ici
- \+ *lemma* tendsto_inv_nhds_within_Ici_inv
- \+ *lemma* tendsto_inv_nhds_within_Iic
- \+ *lemma* tendsto_inv_nhds_within_Iic_inv
- \+ *lemma* tendsto_inv_nhds_within_Iio
- \+ *lemma* tendsto_inv_nhds_within_Iio_inv
- \+ *lemma* tendsto_inv_nhds_within_Ioi
- \+ *lemma* tendsto_inv_nhds_within_Ioi_inv

Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* continuous.exists_forall_ge
- \- *lemma* continuous.exists_forall_le
- \- *lemma* continuous_at_iff_continuous_left'_right'
- \- *lemma* continuous_at_iff_continuous_left_right
- \- *lemma* continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_left_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_left_of_monotone_on_of_image_mem_nhds_within
- \- *lemma* continuous_at_of_monotone_on_of_closure_image_mem_nhds
- \- *lemma* continuous_at_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_of_monotone_on_of_image_mem_nhds
- \- *lemma* continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
- \- *lemma* continuous_at_right_of_monotone_on_of_exists_between
- \- *lemma* continuous_at_right_of_monotone_on_of_image_mem_nhds_within
- \- *lemma* continuous_within_at_Iio_iff_Iic
- \- *lemma* continuous_within_at_Ioi_iff_Ici
- \- *lemma* eq_Icc_of_connected_compact
- \- *lemma* is_compact.Inf_mem
- \- *lemma* is_compact.Sup_mem
- \- *lemma* is_compact.exists_Inf_image_eq
- \- *lemma* is_compact.exists_Sup_image_eq
- \- *lemma* is_compact.exists_forall_ge
- \- *lemma* is_compact.exists_forall_le
- \- *lemma* is_compact.exists_is_glb
- \- *lemma* is_compact.exists_is_greatest
- \- *lemma* is_compact.exists_is_least
- \- *lemma* is_compact.exists_is_lub
- \- *lemma* is_compact.is_glb_Inf
- \- *lemma* is_compact.is_greatest_Sup
- \- *lemma* is_compact.is_least_Inf
- \- *lemma* is_compact.is_lub_Sup
- \- *lemma* is_compact_Icc
- \- *lemma* is_compact_interval
- \- *lemma* is_compact_pi_Icc
- \- *lemma* monotone.continuous_of_dense_range
- \- *lemma* monotone.continuous_of_surjective
- \- *lemma* nhds_left'_sup_nhds_right
- \- *lemma* nhds_left_sup_nhds_right'
- \- *lemma* nhds_left_sup_nhds_right
- \- *lemma* order_iso.coe_to_homeomorph
- \- *lemma* order_iso.coe_to_homeomorph_symm
- \- *def* order_iso.to_homeomorph
- \- *lemma* strict_mono_on.continuous_at_left_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_left_of_exists_between
- \- *lemma* strict_mono_on.continuous_at_left_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_left_of_surj_on
- \- *lemma* strict_mono_on.continuous_at_of_closure_image_mem_nhds
- \- *lemma* strict_mono_on.continuous_at_of_exists_between
- \- *lemma* strict_mono_on.continuous_at_of_image_mem_nhds
- \- *lemma* strict_mono_on.continuous_at_right_of_closure_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_right_of_exists_between
- \- *lemma* strict_mono_on.continuous_at_right_of_image_mem_nhds_within
- \- *lemma* strict_mono_on.continuous_at_right_of_surj_on
- \- *lemma* tendsto_inv_nhds_within_Ici
- \- *lemma* tendsto_inv_nhds_within_Ici_inv
- \- *lemma* tendsto_inv_nhds_within_Iic
- \- *lemma* tendsto_inv_nhds_within_Iic_inv
- \- *lemma* tendsto_inv_nhds_within_Iio
- \- *lemma* tendsto_inv_nhds_within_Iio_inv
- \- *lemma* tendsto_inv_nhds_within_Ioi
- \- *lemma* tendsto_inv_nhds_within_Ioi_inv

Added src/topology/algebra/ordered/compact.lean
- \+ *lemma* continuous.exists_forall_ge
- \+ *lemma* continuous.exists_forall_le
- \+ *lemma* eq_Icc_of_connected_compact
- \+ *lemma* is_compact.Inf_mem
- \+ *lemma* is_compact.Sup_mem
- \+ *lemma* is_compact.exists_Inf_image_eq
- \+ *lemma* is_compact.exists_Sup_image_eq
- \+ *lemma* is_compact.exists_forall_ge
- \+ *lemma* is_compact.exists_forall_le
- \+ *lemma* is_compact.exists_is_glb
- \+ *lemma* is_compact.exists_is_greatest
- \+ *lemma* is_compact.exists_is_least
- \+ *lemma* is_compact.exists_is_lub
- \+ *lemma* is_compact.is_glb_Inf
- \+ *lemma* is_compact.is_greatest_Sup
- \+ *lemma* is_compact.is_least_Inf
- \+ *lemma* is_compact.is_lub_Sup
- \+ *lemma* is_compact_Icc
- \+ *lemma* is_compact_interval
- \+ *lemma* is_compact_pi_Icc

Added src/topology/algebra/ordered/left_right.lean
- \+ *lemma* continuous_at_iff_continuous_left'_right'
- \+ *lemma* continuous_at_iff_continuous_left_right
- \+ *lemma* continuous_within_at_Iio_iff_Iic
- \+ *lemma* continuous_within_at_Ioi_iff_Ici
- \+ *lemma* nhds_left'_sup_nhds_right
- \+ *lemma* nhds_left_sup_nhds_right'
- \+ *lemma* nhds_left_sup_nhds_right

Added src/topology/algebra/ordered/monotone_continuity.lean
- \+ *lemma* continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_left_of_monotone_on_of_image_mem_nhds_within
- \+ *lemma* continuous_at_of_monotone_on_of_closure_image_mem_nhds
- \+ *lemma* continuous_at_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_of_monotone_on_of_image_mem_nhds
- \+ *lemma* continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_monotone_on_of_exists_between
- \+ *lemma* continuous_at_right_of_monotone_on_of_image_mem_nhds_within
- \+ *lemma* monotone.continuous_of_dense_range
- \+ *lemma* monotone.continuous_of_surjective
- \+ *lemma* order_iso.coe_to_homeomorph
- \+ *lemma* order_iso.coe_to_homeomorph_symm
- \+ *def* order_iso.to_homeomorph
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

Modified src/topology/instances/ereal.lean


Modified src/topology/metric_space/basic.lean




## [2021-10-17 13:18:32](https://github.com/leanprover-community/mathlib/commit/1432c30)
feat(topology/algebra/mul_action): `λ x, c • x` is a closed map for all `c` ([#9756](https://github.com/leanprover-community/mathlib/pull/9756))
* rename old `is_closed_map_smul₀` to `is_closed_map_smul_of_ne_zero`;
* add a new `is_closed_map_smul₀` that assumes more about typeclasses
  but works for `c = 0`.
#### Estimated changes
Modified src/topology/algebra/mul_action.lean
- \+ *lemma* is_closed_map_smul_of_ne_zero
- \+/\- *lemma* is_closed_map_smul₀



## [2021-10-17 13:18:31](https://github.com/leanprover-community/mathlib/commit/48dc249)
feat(measure_theory/measure): +1 version of Borel-Cantelli, drop an assumption ([#9678](https://github.com/leanprover-community/mathlib/pull/9678))
* In all versions of Borel-Cantelli lemma, do not require that the
  sets are measurable.
* Add +1 version.
* Golf proofs.
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.ae_eventually_not_mem
- \+/\- *lemma* measure_theory.measure_limsup_eq_zero
- \+ *lemma* measure_theory.measure_set_of_frequently_eq_zero



## [2021-10-17 11:01:38](https://github.com/leanprover-community/mathlib/commit/3f15148)
chore(analysis/p_series): use `lift` tactic ([#9773](https://github.com/leanprover-community/mathlib/pull/9773))
#### Estimated changes
Modified src/analysis/p_series.lean




## [2021-10-17 11:01:37](https://github.com/leanprover-community/mathlib/commit/9fec8f3)
feat(group_theory/index): `index_comap_of_surjective` ([#9768](https://github.com/leanprover-community/mathlib/pull/9768))
`subgroup.index` is preserved by `subgroup.comap`, provided that the homomorphism is surjective.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_comap_of_surjective



## [2021-10-17 11:01:36](https://github.com/leanprover-community/mathlib/commit/85f3640)
feat(topology/instances/ennreal): `{f | lipschitz_with K f}` is a closed set ([#9766](https://github.com/leanprover-community/mathlib/pull/9766))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+/\- *theorem* continuous.edist
- \+ *lemma* is_closed_set_of_lipschitz_on_with
- \+ *lemma* is_closed_set_of_lipschitz_with



## [2021-10-17 11:01:35](https://github.com/leanprover-community/mathlib/commit/678d7ed)
chore(data/equiv/mul_add): add missing `to_equiv_mk` ([#9765](https://github.com/leanprover-community/mathlib/pull/9765))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.to_equiv_mk



## [2021-10-17 11:01:34](https://github.com/leanprover-community/mathlib/commit/24ebeec)
feat(data/nat/gcd): Add `iff` version of `coprime.dvd_of_dvd_mul` ([#9759](https://github.com/leanprover-community/mathlib/pull/9759))
Adds `iff` versions of `coprime.dvd_of_dvd_mul_right` and `coprime.dvd_of_dvd_mul_left`.
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime.dvd_mul_left
- \+ *theorem* nat.coprime.dvd_mul_right



## [2021-10-17 11:01:33](https://github.com/leanprover-community/mathlib/commit/1558a76)
feat(group_theory/subgroup/basic): Special cases of `subgroup_of` ([#9755](https://github.com/leanprover-community/mathlib/pull/9755))
Add four lemmas regarding special cases of `subgroup_of`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.bot_subgroup_of
- \+ *lemma* subgroup.subgroup_of_bot_eq_bot
- \+ *lemma* subgroup.subgroup_of_bot_eq_top
- \+ *lemma* subgroup.top_subgroup_of



## [2021-10-17 11:01:31](https://github.com/leanprover-community/mathlib/commit/4b00aa2)
refactor(ring_theory/jacobson): avoid shadowing hypothesis ([#9736](https://github.com/leanprover-community/mathlib/pull/9736))
This PR postpones a `rw` in a proof, which was creating a shadowed hypothesis. At present, this shadowing was not a big deal, but in another branch it caused a hard-to-diagnose error.
#### Estimated changes
Modified src/ring_theory/jacobson.lean




## [2021-10-17 11:01:30](https://github.com/leanprover-community/mathlib/commit/5eb47c0)
feat(topology/homotopy): Define the fundamental groupoid of a topological space ([#9683](https://github.com/leanprover-community/mathlib/pull/9683))
#### Estimated changes
Modified src/topology/homotopy/basic.lean
- \+ *def* continuous_map.homotopy.cast
- \+ *def* continuous_map.homotopy_rel.cast
- \+ *def* continuous_map.homotopy_with.cast

Added src/topology/homotopy/fundamental_groupoid.lean
- \+ *def* fundamental_groupoid
- \+ *lemma* path.homotopy.continuous_refl_trans_symm_aux
- \+ *lemma* path.homotopy.continuous_trans_assoc_reparam_aux
- \+ *lemma* path.homotopy.continuous_trans_refl_reparam_aux
- \+ *def* path.homotopy.refl_symm_trans
- \+ *def* path.homotopy.refl_trans
- \+ *def* path.homotopy.refl_trans_symm
- \+ *def* path.homotopy.refl_trans_symm_aux
- \+ *lemma* path.homotopy.refl_trans_symm_aux_mem_I
- \+ *def* path.homotopy.trans_assoc
- \+ *lemma* path.homotopy.trans_assoc_reparam
- \+ *def* path.homotopy.trans_assoc_reparam_aux
- \+ *lemma* path.homotopy.trans_assoc_reparam_aux_mem_I
- \+ *lemma* path.homotopy.trans_assoc_reparam_aux_one
- \+ *lemma* path.homotopy.trans_assoc_reparam_aux_zero
- \+ *def* path.homotopy.trans_refl
- \+ *lemma* path.homotopy.trans_refl_reparam
- \+ *def* path.homotopy.trans_refl_reparam_aux
- \+ *lemma* path.homotopy.trans_refl_reparam_aux_mem_I
- \+ *lemma* path.homotopy.trans_refl_reparam_aux_one
- \+ *lemma* path.homotopy.trans_refl_reparam_aux_zero

Modified src/topology/homotopy/path.lean
- \+ *def* path.homotopy.cast
- \+ *def* path.homotopy.reparam
- \+ *def* path.homotopy.symm₂

Modified src/topology/path_connected.lean
- \+ *lemma* path.symm_symm
- \+ *lemma* path.trans_apply
- \+ *lemma* path.trans_symm



## [2021-10-17 08:53:58](https://github.com/leanprover-community/mathlib/commit/f171c61)
feat(linear_algebra/affine_space/independent): add `exists_affine_independent` ([#9747](https://github.com/leanprover-community/mathlib/pull/9747))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/data/equiv/set.lean


Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* exists_affine_independent

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_insert_zero

Modified src/order/countable_dense_linear_order.lean




## [2021-10-17 06:23:24](https://github.com/leanprover-community/mathlib/commit/ff8a35d)
feat(group_theory/subgroup/basic): Kernel of `subtype` and `inclusion` ([#9763](https://github.com/leanprover-community/mathlib/pull/9763))
`subtype` and `inculusion` are injective, so they have trivial kernel.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.ker_inclusion
- \+ *lemma* subgroup.ker_subtype



## [2021-10-17 03:34:30](https://github.com/leanprover-community/mathlib/commit/7aa431c)
chore(group_theory/quotient_group): Tag lemmas with `@[to_additive]` ([#9771](https://github.com/leanprover-community/mathlib/pull/9771))
Adds `@[to_additive]` to a couple lemmas.
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* quotient_group.subgroup_eq_top_of_subsingleton
- \+/\- *lemma* quotient_group.subsingleton_quotient_top



## [2021-10-17 03:34:29](https://github.com/leanprover-community/mathlib/commit/a1a05ad)
chore(measure_theory/*): don't require the codomain to be a normed group ([#9769](https://github.com/leanprover-community/mathlib/pull/9769))
Lemmas like `continuous_on.ae_measurable` are true for any codomain. Also add `continuous.integrable_on_Ioc` and `continuous.integrable_on_interval_oc`.
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* continuous.integrable_on_Ioc
- \+ *lemma* continuous.integrable_on_interval_oc
- \+/\- *lemma* continuous_on.ae_measurable

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* continuous.measurable_at_filter
- \+/\- *lemma* continuous_on.measurable_at_filter_nhds_within



## [2021-10-17 03:34:28](https://github.com/leanprover-community/mathlib/commit/08a070b)
chore(topology/instances/ennreal): golf a proof ([#9767](https://github.com/leanprover-community/mathlib/pull/9767))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* continuous_of_const
- \+ *lemma* filter.eventually_eq.continuous_at

Modified src/topology/instances/ennreal.lean




## [2021-10-17 02:23:49](https://github.com/leanprover-community/mathlib/commit/4a837fb)
chore(analysis/normed/group): add a few convenience lemmas ([#9770](https://github.com/leanprover-community/mathlib/pull/9770))
Add `lipschitz_on_with.norm_sub_le_of_le`,
`lipschitz_with.norm_sub_le`, and `lipschitz_with.norm_sub_le_of_le`.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* lipschitz_on_with.norm_sub_le_of_le
- \+ *lemma* lipschitz_with.norm_sub_le_of_le



## [2021-10-16 23:11:25](https://github.com/leanprover-community/mathlib/commit/cf72eff)
refactor(group_theory/quotient_group): Fix typo ([#9746](https://github.com/leanprover-community/mathlib/pull/9746))
Fix typo in `quotient_bot`.
#### Estimated changes
Modified src/group_theory/quotient_group.lean




## [2021-10-16 21:46:54](https://github.com/leanprover-community/mathlib/commit/ad7000b)
feat(set_theory/cardinal): cardinal.to_nat_congr ([#9726](https://github.com/leanprover-community/mathlib/pull/9726))
If `e : α ≃ β`, then `(cardinal.mk α).to_nat = (cardinal.mk β).to_nat`.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.to_nat_congr
- \+ *lemma* cardinal.to_nat_lift



## [2021-10-16 20:32:52](https://github.com/leanprover-community/mathlib/commit/b97bb92)
feat(set_theory/cardinal): lemmas ([#9690](https://github.com/leanprover-community/mathlib/pull/9690))
* swap sides of `cardinal.lift_mk`, rename it to `cardinal.mk_ulift`;
* add `cardinal.out_mk_equiv`.
#### Estimated changes
Modified src/data/W/cardinal.lean


Modified src/data/mv_polynomial/cardinal.lean


Modified src/linear_algebra/dimension.lean


Modified src/set_theory/cardinal.lean
- \- *theorem* cardinal.lift_mk
- \+ *theorem* cardinal.mk_ulift

Modified src/set_theory/cardinal_ordinal.lean




## [2021-10-16 18:01:16](https://github.com/leanprover-community/mathlib/commit/3fe67d6)
feat(analysis/special_functions/integrals): integral of `|x - a| ^ n` over `Ι a b` ([#9752](https://github.com/leanprover-community/mathlib/pull/9752))
Also use notation for `interval a b` and `interval_oc a b`.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* integral_inv
- \+/\- *lemma* integral_log
- \+/\- *lemma* integral_one_div
- \+ *lemma* integral_pow_abs_sub_interval_oc
- \+/\- *lemma* interval_integral.interval_integrable_inv
- \+/\- *lemma* interval_integral.interval_integrable_log
- \+/\- *lemma* interval_integral.interval_integrable_one_div



## [2021-10-16 18:01:15](https://github.com/leanprover-community/mathlib/commit/54e9e12)
chore(topology/maps): add `is_closed_map.closed_range` ([#9751](https://github.com/leanprover-community/mathlib/pull/9751))
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* is_closed_map.closed_range



## [2021-10-16 18:01:14](https://github.com/leanprover-community/mathlib/commit/998ab78)
chore(data/list/lex): make data.list.lex not depend on data.list.basic ([#9750](https://github.com/leanprover-community/mathlib/pull/9750))
Another simplification in list related dependencies, if this commit breaks external code the fix is to add `import data.list.basic` to the broken file.
#### Estimated changes
Modified src/data/list/lex.lean




## [2021-10-16 18:01:13](https://github.com/leanprover-community/mathlib/commit/066a168)
feat(topology/G_delta): add lemmas, minor golf ([#9742](https://github.com/leanprover-community/mathlib/pull/9742))
* the complement to a countable set is a Gδ set;
* a closed set is a Gδ set;
* finite union of Gδ sets is a Gδ set;
* generalize some universe levels in `topology.basic`;
* golf a few proofs in `topology.uniform_space.basic`;
* add `filter.has_basis.bInter_bUnion_ball`.
#### Estimated changes
Modified src/topology/G_delta.lean
- \+ *lemma* finset.is_Gδ_compl
- \+/\- *lemma* is_Gδ_Inter
- \+ *lemma* is_Gδ_bUnion
- \+ *lemma* is_Gδ_compl_singleton
- \+/\- *lemma* is_Gδ_empty
- \+/\- *lemma* is_Gδ_set_of_continuous_at
- \+/\- *lemma* is_Gδ_univ
- \+ *lemma* is_closed.is_Gδ'
- \+ *lemma* is_closed.is_Gδ
- \+ *lemma* set.countable.is_Gδ_compl
- \+ *lemma* set.finite.is_Gδ_compl
- \+ *lemma* set.subsingleton.is_Gδ_compl

Modified src/topology/basic.lean
- \+/\- *theorem* mem_closure_iff_nhds_basis'
- \+/\- *theorem* mem_closure_iff_nhds_basis

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.has_basis.bInter_bUnion_ball
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* nhds_basis_uniformity



## [2021-10-16 18:01:11](https://github.com/leanprover-community/mathlib/commit/aa0d0d4)
feat(group_theory/subgroup/basic): Range of inclusion ([#9732](https://github.com/leanprover-community/mathlib/pull/9732))
If `H ≤ K`, then the range of `inclusion : H → K` is `H` (viewed as a subgroup of `K`).
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.inclusion_range



## [2021-10-16 18:01:10](https://github.com/leanprover-community/mathlib/commit/155f8e6)
feat(data/int/succ_pred): `ℤ` is succ- and pred- archimedean ([#9731](https://github.com/leanprover-community/mathlib/pull/9731))
This provides the instances `succ_order ℤ`, `pred_order ℤ`, `is_succ_archimedean ℤ`, `is_pred_archimedean ℤ`.
#### Estimated changes
Added src/data/int/succ_pred.lean
- \+ *lemma* int.pred_iterate
- \+ *lemma* int.succ_iterate

Modified src/order/succ_pred.lean
- \+ *def* pred_order.of_le_pred_iff
- \+ *def* pred_order.of_le_pred_iff_of_pred_le_pred
- \- *def* pred_order.pred_order_of_le_pred_iff
- \- *def* pred_order.pred_order_of_le_pred_iff_of_pred_le_pred
- \+ *def* succ_order.of_succ_le_iff
- \+ *def* succ_order.of_succ_le_iff_of_le_lt_succ
- \- *def* succ_order.succ_order_of_succ_le_iff
- \- *def* succ_order.succ_order_of_succ_le_iff_of_le_lt_succ



## [2021-10-16 18:01:09](https://github.com/leanprover-community/mathlib/commit/e744033)
feat(data/finset/basic, lattice): Simple lemmas ([#9723](https://github.com/leanprover-community/mathlib/pull/9723))
This proves lemmas about `finset.sup`/`finset.inf` and `finset.singleton`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.nonempty.cons_induction
- \+ *lemma* finset.not_disjoint_iff
- \+ *lemma* finset.singleton_injective

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf_attach
- \+ *lemma* finset.inf_erase_top
- \+/\- *lemma* finset.inf_image
- \+ *lemma* finset.inf_inf
- \+ *lemma* finset.inf_sdiff_left
- \+ *lemma* finset.inf_sdiff_right
- \+ *lemma* finset.sup_attach
- \+ *lemma* finset.sup_erase_bot
- \+/\- *lemma* finset.sup_image
- \+ *lemma* finset.sup_sdiff_left
- \+ *lemma* finset.sup_sdiff_right
- \+ *lemma* finset.sup_singleton'
- \+ *lemma* finset.sup_sup

Modified src/order/lattice.lean
- \+ *lemma* inf_inf_inf_comm
- \+ *lemma* sup_sup_sup_comm



## [2021-10-16 18:01:08](https://github.com/leanprover-community/mathlib/commit/bf34d9b)
feat(analysis/normed/group/SemiNormedGroup/kernels): add explicit_cokernel.map ([#9712](https://github.com/leanprover-community/mathlib/pull/9712))
From LTE.
#### Estimated changes
Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *lemma* SemiNormedGroup.explicit_coker.map_desc



## [2021-10-16 18:01:07](https://github.com/leanprover-community/mathlib/commit/686b363)
feat(analysis/normed/group/SemiNormedGroup/kernels): add kernels ([#9711](https://github.com/leanprover-community/mathlib/pull/9711))
From LTE.
#### Estimated changes
Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *def* SemiNormedGroup.parallel_pair_cone



## [2021-10-16 18:01:06](https://github.com/leanprover-community/mathlib/commit/3d99926)
feat(analysis/normed/group/SemiNormedGroup): add iso_isometry_of_norm_noninc ([#9710](https://github.com/leanprover-community/mathlib/pull/9710))
From LTE.
#### Estimated changes
Modified src/analysis/normed/group/SemiNormedGroup.lean
- \+ *lemma* SemiNormedGroup.iso_isometry_of_norm_noninc



## [2021-10-16 18:01:05](https://github.com/leanprover-community/mathlib/commit/5ac586a)
feat(algebra/group_power/order): When a power is less than one ([#9700](https://github.com/leanprover-community/mathlib/pull/9700))
This proves a bunch of simple order lemmas relating `1`, `a` and `a ^ n`. I also move `pow_le_one` upstream as it could already be proved in `algebra.group_power.order` and remove `[nontrivial R]` from `one_lt_pow`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* pow_le_of_le_one
- \- *lemma* pow_le_one
- \+/\- *lemma* pow_le_pow_of_le_one
- \+ *lemma* sq_le

Modified src/algebra/group_power/order.lean
- \+ *lemma* one_le_pow_iff_of_nonneg
- \+ *lemma* one_le_sq_iff
- \+/\- *lemma* one_lt_pow
- \+ *lemma* one_lt_pow_iff_of_nonneg
- \+ *lemma* one_lt_sq_iff
- \+ *lemma* pow_le_one
- \+ *lemma* pow_le_one_iff_of_nonneg
- \+ *lemma* pow_lt_one
- \+ *lemma* pow_lt_one_iff_of_nonneg
- \+ *lemma* sq_le_one_iff
- \+ *lemma* sq_lt_one_iff



## [2021-10-16 16:46:55](https://github.com/leanprover-community/mathlib/commit/99b2d40)
feat(algebra/floor): Floor and ceil of `-a` ([#9715](https://github.com/leanprover-community/mathlib/pull/9715))
This proves `floor_neg : ⌊-a⌋ = -⌈a⌉` and `ceil_neg : ⌈-a⌉ = -⌊a⌋` and uses them to remove explicit dependency on the definition of `int.ceil` in prevision of [#9591](https://github.com/leanprover-community/mathlib/pull/9591). This also proves `⌊a + 1⌋ = ⌊a⌋ + 1` and variants.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/floor.lean
- \+ *lemma* int.ceil_add_one
- \+ *lemma* int.ceil_neg
- \+ *lemma* int.floor_add_one
- \+ *lemma* int.floor_neg
- \+ *lemma* nat.ceil_add_one
- \+ *lemma* nat.ceil_lt_add_one
- \- *theorem* nat.ceil_lt_add_one
- \+ *lemma* nat.floor_add_one



## [2021-10-16 09:26:55](https://github.com/leanprover-community/mathlib/commit/9ac2aa2)
feat(topology/metric_space/lipschitz): add `lipschitz_with.min` and `lipschitz_with.max` ([#9744](https://github.com/leanprover-community/mathlib/pull/9744))
Also change assumptions in some lemmas in `algebra.order.group` from
 `[add_comm_group α] [linear_order α] [covariant_class α α (+) (≤)]`
to `[linear_ordered_add_comm_group α]`. These two sets of assumptions
are equivalent but the latter is more readable.
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* abs_max_sub_max_le_max
- \+ *lemma* abs_min_sub_min_le_max
- \+ *lemma* max_sub_max_le_max

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_with.const_max
- \+ *lemma* lipschitz_with.const_min
- \+ *lemma* lipschitz_with.max_const
- \+ *lemma* lipschitz_with.min_const
- \+ *lemma* lipschitz_with.subtype_mk
- \+ *lemma* lipschitz_with_max
- \+ *lemma* lipschitz_with_min



## [2021-10-16 09:26:54](https://github.com/leanprover-community/mathlib/commit/96ba8b6)
chore(topology/uniform_space/pi): add `uniform_continuous_pi` ([#9743](https://github.com/leanprover-community/mathlib/pull/9743))
#### Estimated changes
Modified src/topology/uniform_space/pi.lean
- \+ *lemma* uniform_continuous_pi



## [2021-10-16 08:44:20](https://github.com/leanprover-community/mathlib/commit/e362293)
refactor(ring_theory/fractional_ideal): speedup a proof ([#9738](https://github.com/leanprover-community/mathlib/pull/9738))
This was timing out on another branch. Just replaces a `simp only []` with a `rw []`.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean




## [2021-10-16 07:32:33](https://github.com/leanprover-community/mathlib/commit/f40cd88)
chore(topology/algebra/ordered): move some lemmas to a new file ([#9745](https://github.com/leanprover-community/mathlib/pull/9745))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* infi_eq_infi_subseq_of_monotone
- \- *lemma* infi_eq_of_tendsto
- \- *lemma* is_glb_of_tendsto
- \- *lemma* is_lub_of_tendsto
- \- *lemma* monotone.ge_of_tendsto
- \- *lemma* monotone.le_of_tendsto
- \- *lemma* supr_eq_of_tendsto
- \- *lemma* supr_eq_supr_subseq_of_monotone
- \- *lemma* tendsto_at_bot_cinfi
- \- *lemma* tendsto_at_bot_csupr
- \- *lemma* tendsto_at_bot_infi
- \- *lemma* tendsto_at_bot_is_glb
- \- *lemma* tendsto_at_bot_is_lub
- \- *lemma* tendsto_at_bot_supr
- \- *lemma* tendsto_at_top_cinfi
- \- *lemma* tendsto_at_top_csupr
- \- *lemma* tendsto_at_top_infi
- \- *lemma* tendsto_at_top_is_glb
- \- *lemma* tendsto_at_top_is_lub
- \- *lemma* tendsto_at_top_supr
- \- *lemma* tendsto_iff_tendsto_subseq_of_monotone
- \- *lemma* tendsto_of_monotone

Added src/topology/algebra/ordered/monotone_convergence.lean
- \+ *lemma* infi_eq_infi_subseq_of_monotone
- \+ *lemma* infi_eq_of_tendsto
- \+ *lemma* is_glb_of_tendsto
- \+ *lemma* is_lub_of_tendsto
- \+ *lemma* monotone.ge_of_tendsto
- \+ *lemma* monotone.le_of_tendsto
- \+ *lemma* supr_eq_of_tendsto
- \+ *lemma* supr_eq_supr_subseq_of_monotone
- \+ *lemma* tendsto_at_bot_cinfi
- \+ *lemma* tendsto_at_bot_csupr
- \+ *lemma* tendsto_at_bot_infi
- \+ *lemma* tendsto_at_bot_is_glb
- \+ *lemma* tendsto_at_bot_is_lub
- \+ *lemma* tendsto_at_bot_supr
- \+ *lemma* tendsto_at_top_cinfi
- \+ *lemma* tendsto_at_top_csupr
- \+ *lemma* tendsto_at_top_infi
- \+ *lemma* tendsto_at_top_is_glb
- \+ *lemma* tendsto_at_top_is_lub
- \+ *lemma* tendsto_at_top_supr
- \+ *lemma* tendsto_iff_tendsto_subseq_of_monotone
- \+ *lemma* tendsto_of_monotone



## [2021-10-16 04:16:34](https://github.com/leanprover-community/mathlib/commit/150bbea)
feat(group_theory/subgroup/basic): Bottom subgroup has unique element ([#9734](https://github.com/leanprover-community/mathlib/pull/9734))
Adds instance for `unique (⊥ : subgroup G)`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean




## [2021-10-16 01:17:29](https://github.com/leanprover-community/mathlib/commit/1766588)
feat(measure_theory/covering/vitali): Vitali covering theorems ([#9680](https://github.com/leanprover-community/mathlib/pull/9680))
The topological and measurable Vitali covering theorems.
* topological version: if a space is covered by balls `(B (x_i, r_i))_{i \in I}`, one can extract a disjointed subfamily indexed by `J` such that the space is covered by the balls `B (x_j, 5 r_j)`.
* measurable version: if additionally the measure has a doubling-like property, and the covering contains balls of arbitrarily small radius at every point, then the disjointed subfamily one obtains above covers almost all the space.
These two statements are particular cases of more general statements that are proved in this PR.
#### Estimated changes
Added src/measure_theory/covering/vitali.lean
- \+ *theorem* vitali.exists_disjoint_covering_ae
- \+ *theorem* vitali.exists_disjoint_subfamily_covering_enlargment
- \+ *theorem* vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball



## [2021-10-15 22:57:51](https://github.com/leanprover-community/mathlib/commit/ea22ce3)
chore(data/list): move lemmas from data.list.basic that require algebra.group_power to a new file ([#9728](https://github.com/leanprover-community/mathlib/pull/9728))
Hopefully ease the dependencies on anyone importing data.list.basic, if your code broke after this change adding `import data.list.prod_monoid` should fix it.
Lemmas moved:
- `list.prod_repeat`
- `list.sum_repeat`
- `list.prod_le_of_forall_le`
- `list.sum_le_of_forall_le`
#### Estimated changes
Modified src/data/list/basic.lean
- \- *lemma* list.prod_le_of_forall_le
- \- *theorem* list.prod_repeat

Added src/data/list/prod_monoid.lean
- \+ *lemma* list.prod_le_of_forall_le
- \+ *theorem* list.prod_repeat

Modified src/data/multiset/basic.lean


Modified test/lint_unused_haves_suffices.lean




## [2021-10-15 21:35:25](https://github.com/leanprover-community/mathlib/commit/711aa75)
refactor(algebra/gcd_monoid): remove superfluous old_structure_cmd ([#9720](https://github.com/leanprover-community/mathlib/pull/9720))
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean




## [2021-10-15 16:38:20](https://github.com/leanprover-community/mathlib/commit/b3f602b)
feat(linear_algebra/linear_independent): add variant of `exists_linear_independent` ([#9708](https://github.com/leanprover-community/mathlib/pull/9708))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* exists_linear_independent
- \+ *lemma* exists_linear_independent_extension



## [2021-10-15 15:08:13](https://github.com/leanprover-community/mathlib/commit/d6fd5f5)
feat(linear_algebra/dimension): generalize dim_zero_iff_forall_zero ([#9713](https://github.com/leanprover-community/mathlib/pull/9713))
We generalize `dim_zero_iff_forall_zero` to `[nontrivial R] [no_zero_smul_divisors R M]`.
If you see a more general class to consider let me know.
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_pos
- \+/\- *lemma* dim_pos_iff_exists_ne_zero
- \+/\- *lemma* dim_pos_iff_nontrivial
- \+/\- *lemma* dim_zero_iff
- \+/\- *lemma* dim_zero_iff_forall_zero

Modified src/linear_algebra/finite_dimensional.lean




## [2021-10-15 12:10:59](https://github.com/leanprover-community/mathlib/commit/ad6d476)
refactor(ring_theory/derivation): remove old_structure_cmd ([#9724](https://github.com/leanprover-community/mathlib/pull/9724))
#### Estimated changes
Modified src/geometry/manifold/derivation_bundle.lean


Modified src/ring_theory/derivation.lean
- \+/\- *lemma* derivation.mk_coe
- \- *lemma* derivation.to_fun_eq_coe



## [2021-10-15 12:10:58](https://github.com/leanprover-community/mathlib/commit/a2737b4)
chore(data/set_like/basic): remove superfluous old_structure_cmd ([#9722](https://github.com/leanprover-community/mathlib/pull/9722))
#### Estimated changes
Modified src/data/set_like/basic.lean




## [2021-10-15 11:28:36](https://github.com/leanprover-community/mathlib/commit/6bc2a1a)
refactor(algebra/lie/basic): remove old_structure_cmd ([#9721](https://github.com/leanprover-community/mathlib/pull/9721))
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/basic.lean
- \+/\- *lemma* lie_module_equiv.coe_mk
- \+ *lemma* lie_module_equiv.injective
- \+ *def* lie_module_equiv.to_equiv
- \+ *def* lie_module_equiv.to_linear_equiv
- \+/\- *structure* lie_module_equiv
- \+/\- *lemma* lie_module_hom.coe_linear_mk
- \+/\- *lemma* lie_module_hom.coe_mk
- \+/\- *lemma* lie_module_hom.mk_coe

Modified src/algebra/lie/tensor_product.lean


Modified src/algebra/lie/weights.lean
- \+ *def* lie_algebra.root_space_weight_space_product_aux



## [2021-10-15 06:28:08](https://github.com/leanprover-community/mathlib/commit/7707036)
feat(tactic/by_contra): add by_contra' tactic ([#9619](https://github.com/leanprover-community/mathlib/pull/9619))
#### Estimated changes
Added src/tactic/by_contra.lean


Modified src/tactic/core.lean


Modified src/tactic/norm_num.lean


Added test/by_contra.lean




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
Modified src/algebra/floor.lean
- \+/\- *lemma* int.abs_sub_lt_one_of_floor_eq_floor
- \+/\- *def* int.ceil
- \+ *lemma* int.ceil_add_int
- \- *theorem* int.ceil_add_int
- \+ *lemma* int.ceil_coe
- \- *theorem* int.ceil_coe
- \+/\- *lemma* int.ceil_eq_iff
- \+/\- *lemma* int.ceil_eq_on_Ioc'
- \+/\- *lemma* int.ceil_eq_on_Ioc
- \+ *lemma* int.ceil_le
- \- *theorem* int.ceil_le
- \+ *lemma* int.ceil_le_floor_add_one
- \- *theorem* int.ceil_le_floor_add_one
- \+ *lemma* int.ceil_lt_add_one
- \- *theorem* int.ceil_lt_add_one
- \+ *lemma* int.ceil_mono
- \- *theorem* int.ceil_mono
- \+/\- *lemma* int.ceil_nonneg
- \+/\- *lemma* int.ceil_pos
- \+ *lemma* int.ceil_sub_int
- \- *theorem* int.ceil_sub_int
- \+ *lemma* int.ceil_zero
- \- *theorem* int.ceil_zero
- \- *theorem* int.floor_add
- \+/\- *lemma* int.floor_add_fract
- \+ *lemma* int.floor_add_int
- \- *theorem* int.floor_add_int
- \+ *lemma* int.floor_add_nat
- \- *theorem* int.floor_add_nat
- \+ *lemma* int.floor_coe
- \- *theorem* int.floor_coe
- \+/\- *lemma* int.floor_eq_iff
- \+/\- *lemma* int.floor_eq_on_Ico'
- \+/\- *lemma* int.floor_eq_on_Ico
- \+/\- *lemma* int.floor_fract
- \+ *lemma* int.floor_int_add
- \- *theorem* int.floor_int_add
- \+ *lemma* int.floor_le
- \- *theorem* int.floor_le
- \+ *lemma* int.floor_lt
- \- *theorem* int.floor_lt
- \+/\- *lemma* int.floor_lt_ceil_of_lt
- \+ *lemma* int.floor_mono
- \- *theorem* int.floor_mono
- \+ *lemma* int.floor_nat_add
- \+ *lemma* int.floor_nonneg
- \- *theorem* int.floor_nonneg
- \+ *lemma* int.floor_one
- \- *theorem* int.floor_one
- \+ *lemma* int.floor_sub_int
- \- *theorem* int.floor_sub_int
- \+ *lemma* int.floor_sub_nat
- \- *theorem* int.floor_sub_nat
- \+ *lemma* int.floor_zero
- \- *theorem* int.floor_zero
- \+/\- *def* int.fract
- \+ *lemma* int.fract_add
- \- *theorem* int.fract_add
- \+/\- *lemma* int.fract_add_floor
- \+ *lemma* int.fract_eq_fract
- \- *theorem* int.fract_eq_fract
- \+ *lemma* int.fract_eq_iff
- \- *theorem* int.fract_eq_iff
- \+/\- *lemma* int.fract_floor
- \+/\- *lemma* int.fract_fract
- \+ *lemma* int.fract_lt_one
- \- *theorem* int.fract_lt_one
- \+ *lemma* int.fract_mul_nat
- \- *theorem* int.fract_mul_nat
- \+ *lemma* int.fract_nonneg
- \- *theorem* int.fract_nonneg
- \+/\- *lemma* int.fract_zero
- \+ *lemma* int.le_ceil
- \- *theorem* int.le_ceil
- \+ *lemma* int.le_floor
- \- *theorem* int.le_floor
- \+ *lemma* int.lt_ceil
- \- *theorem* int.lt_ceil
- \+ *lemma* int.lt_floor_add_one
- \- *theorem* int.lt_floor_add_one
- \+ *lemma* int.lt_succ_floor
- \- *theorem* int.lt_succ_floor
- \+/\- *lemma* int.preimage_Icc
- \+/\- *lemma* int.preimage_Ici
- \+/\- *lemma* int.preimage_Ico
- \+/\- *lemma* int.preimage_Iic
- \+/\- *lemma* int.preimage_Iio
- \+/\- *lemma* int.preimage_Ioc
- \+/\- *lemma* int.preimage_Ioi
- \+/\- *lemma* int.preimage_Ioo
- \+ *lemma* int.sub_one_lt_floor
- \- *theorem* int.sub_one_lt_floor
- \+ *lemma* nat.ceil_add_nat
- \- *theorem* nat.ceil_add_nat
- \+ *lemma* nat.ceil_coe
- \- *theorem* nat.ceil_coe
- \+ *lemma* nat.ceil_eq_zero
- \- *theorem* nat.ceil_eq_zero
- \+ *lemma* nat.ceil_le
- \- *theorem* nat.ceil_le
- \+ *lemma* nat.ceil_mono
- \- *theorem* nat.ceil_mono
- \+ *lemma* nat.ceil_zero
- \- *theorem* nat.ceil_zero
- \+ *lemma* nat.floor_add_nat
- \- *theorem* nat.floor_add_nat
- \+ *lemma* nat.floor_coe
- \- *theorem* nat.floor_coe
- \+/\- *lemma* nat.floor_lt_ceil_of_lt_of_pos
- \+ *lemma* nat.floor_lt_iff
- \- *theorem* nat.floor_lt_iff
- \+ *lemma* nat.floor_mono
- \- *theorem* nat.floor_mono
- \+ *lemma* nat.floor_zero
- \- *theorem* nat.floor_zero
- \+ *lemma* nat.le_ceil
- \- *theorem* nat.le_ceil
- \+ *lemma* nat.le_floor_iff
- \- *theorem* nat.le_floor_iff
- \+/\- *lemma* nat.le_of_ceil_le
- \+ *lemma* nat.lt_ceil
- \- *theorem* nat.lt_ceil
- \+/\- *lemma* nat.lt_of_ceil_lt
- \+/\- *lemma* nat.sub_one_lt_floor



## [2021-10-14 23:10:05](https://github.com/leanprover-community/mathlib/commit/c37ea53)
feat(order/succ_pred): `succ`-Archimedean orders ([#9714](https://github.com/leanprover-community/mathlib/pull/9714))
This defines `succ`-Archimedean orders: orders in which `a ≤ b` means that `succ^[n] a = b` for some `n`.
#### Estimated changes
Modified src/logic/function/iterate.lean
- \+ *def* function.iterate.rec
- \+ *lemma* function.iterate.rec_zero

Modified src/order/succ_pred.lean
- \+ *lemma* exists_pred_iterate_iff_le
- \+ *lemma* exists_pred_iterate_or
- \+ *lemma* exists_succ_iterate_iff_le
- \+ *lemma* exists_succ_iterate_or
- \+ *lemma* has_le.le.exists_pred_iterate
- \+ *lemma* has_le.le.exists_succ_iterate
- \+ *lemma* pred.rec
- \+ *lemma* pred.rec_iff
- \+ *lemma* pred.rec_linear
- \+ *lemma* pred.rec_top
- \+ *lemma* succ.rec
- \+ *lemma* succ.rec_bot
- \+ *lemma* succ.rec_iff
- \+ *lemma* succ.rec_linear



## [2021-10-14 21:12:58](https://github.com/leanprover-community/mathlib/commit/c12aced)
feat(algebra/star): star_linear_equiv ([#9426](https://github.com/leanprover-community/mathlib/pull/9426))
#### Estimated changes
Modified src/algebra/ring/comp_typeclasses.lean
- \+ *lemma* ring_hom_inv_pair.of_ring_equiv
- \+ *lemma* ring_hom_inv_pair.symm

Modified src/algebra/star/basic.lean


Added src/algebra/star/module.lean
- \+ *def* star_linear_equiv



## [2021-10-14 19:54:19](https://github.com/leanprover-community/mathlib/commit/158fbc5)
refactor(algebra/module/order): Make space argument explicit in the `order_iso` ([#9706](https://github.com/leanprover-community/mathlib/pull/9706))
Explicitly providing `M` in `order_iso.smul_left` and `order_iso.smul_left_dual` turns out to work much better with dot notation on `order_iso`. This allows golfing half the proofs introduced in [#9078](https://github.com/leanprover-community/mathlib/pull/9078).
#### Estimated changes
Modified src/algebra/module/ordered.lean
- \+/\- *lemma* bdd_above.smul_of_nonneg
- \+/\- *lemma* bdd_above.smul_of_nonpos
- \+/\- *lemma* bdd_above_smul_iff_of_neg
- \+/\- *lemma* bdd_above_smul_iff_of_pos
- \+/\- *lemma* bdd_below.smul_of_nonneg
- \+/\- *lemma* bdd_below.smul_of_nonpos
- \+/\- *lemma* bdd_below_smul_iff_of_neg
- \+/\- *lemma* bdd_below_smul_iff_of_pos
- \+/\- *lemma* lower_bounds_smul_of_neg
- \+/\- *lemma* lower_bounds_smul_of_pos
- \+/\- *lemma* upper_bounds_smul_of_neg
- \+/\- *lemma* upper_bounds_smul_of_pos

Modified src/algebra/order/smul.lean




## [2021-10-14 18:49:52](https://github.com/leanprover-community/mathlib/commit/72789f5)
feat(linear_algebra/affine_space/affine_subspace): add lemma `affine_equiv.span_eq_top_iff` ([#9695](https://github.com/leanprover-community/mathlib/pull/9695))
Together with supporting lemmas.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* set.mem_vsub

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.image_vsub_image

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_equiv.span_eq_top_iff
- \+ *lemma* affine_map.map_top_of_surjective
- \+ *lemma* affine_map.span_eq_top_of_surjective
- \+ *lemma* affine_map.vector_span_image_eq_submodule_map
- \+ *def* affine_subspace.map
- \+ *lemma* affine_subspace.map_bot
- \+ *lemma* affine_subspace.map_coe
- \+ *lemma* affine_subspace.map_direction
- \+ *lemma* affine_subspace.map_span



## [2021-10-14 18:06:10](https://github.com/leanprover-community/mathlib/commit/cef78dd)
feat(archive/abel_ruffini): speedup by squeezing  ([#9709](https://github.com/leanprover-community/mathlib/pull/9709))
30s->9s elaboration for me, hopefully stop [#9705](https://github.com/leanprover-community/mathlib/pull/9705) timing out
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean




## [2021-10-14 16:25:51](https://github.com/leanprover-community/mathlib/commit/393fe70)
chore(analysis/p_series): add 2 more versions ([#9703](https://github.com/leanprover-community/mathlib/pull/9703))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/p_series.lean
- \- *lemma* nnreal.summable_one_rpow_inv
- \+ *lemma* nnreal.summable_rpow
- \+ *lemma* nnreal.summable_rpow_inv
- \+ *lemma* real.summable_nat_rpow



## [2021-10-14 13:24:56](https://github.com/leanprover-community/mathlib/commit/aff49a6)
feat(data/equiv/basic): prop_equiv_pempty ([#9689](https://github.com/leanprover-community/mathlib/pull/9689))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.prop_equiv_pempty



## [2021-10-14 13:24:54](https://github.com/leanprover-community/mathlib/commit/dc23dfa)
feat(data/equiv/basic): subtype_equiv_psigma ([#9688](https://github.com/leanprover-community/mathlib/pull/9688))
- [x] depends on: [#9687](https://github.com/leanprover-community/mathlib/pull/9687)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.psigma_equiv_subtype
- \+ *def* equiv.sigma_plift_equiv_subtype
- \+ *def* equiv.sigma_ulift_plift_equiv_subtype



## [2021-10-14 13:24:52](https://github.com/leanprover-community/mathlib/commit/9da33a8)
refactor(algebra/floor): Rename floor and ceil functions ([#9590](https://github.com/leanprover-community/mathlib/pull/9590))
This renames
* `floor` -> `int.floor`
* `ceil` -> `int.ceil`
* `fract` -> `int.fract`
* `nat_floor` -> `nat.floor`
* `nat_ceil` -> `nat.ceil`
#### Estimated changes
Modified archive/imo/imo2013_q5.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/floor.lean
- \- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \- *def* ceil
- \- *theorem* ceil_add_int
- \- *theorem* ceil_coe
- \- *lemma* ceil_eq_iff
- \- *lemma* ceil_eq_on_Ioc'
- \- *lemma* ceil_eq_on_Ioc
- \- *theorem* ceil_le
- \- *theorem* ceil_le_floor_add_one
- \- *theorem* ceil_lt_add_one
- \- *theorem* ceil_mono
- \- *lemma* ceil_nonneg
- \- *lemma* ceil_pos
- \- *theorem* ceil_sub_int
- \- *theorem* ceil_zero
- \- *def* floor
- \- *lemma* floor_add_fract
- \- *theorem* floor_add_int
- \- *theorem* floor_add_nat
- \- *theorem* floor_coe
- \- *lemma* floor_eq_iff
- \- *lemma* floor_eq_on_Ico'
- \- *lemma* floor_eq_on_Ico
- \- *lemma* floor_fract
- \- *theorem* floor_int_add
- \- *theorem* floor_le
- \- *theorem* floor_lt
- \- *lemma* floor_lt_ceil_of_lt
- \- *theorem* floor_mono
- \- *theorem* floor_nat_add
- \- *theorem* floor_nonneg
- \- *theorem* floor_one
- \- *lemma* floor_pos
- \- *theorem* floor_sub_int
- \- *theorem* floor_sub_nat
- \- *theorem* floor_zero
- \- *def* fract
- \- *theorem* fract_add
- \- *lemma* fract_add_floor
- \- *lemma* fract_coe
- \- *theorem* fract_eq_fract
- \- *theorem* fract_eq_iff
- \- *lemma* fract_floor
- \- *lemma* fract_fract
- \- *theorem* fract_lt_one
- \- *theorem* fract_mul_nat
- \- *theorem* fract_nonneg
- \- *lemma* fract_zero
- \+ *lemma* int.abs_sub_lt_one_of_floor_eq_floor
- \+ *def* int.ceil
- \+ *theorem* int.ceil_add_int
- \+ *theorem* int.ceil_coe
- \+ *lemma* int.ceil_eq_iff
- \+ *lemma* int.ceil_eq_on_Ioc'
- \+ *lemma* int.ceil_eq_on_Ioc
- \+ *theorem* int.ceil_le
- \+ *theorem* int.ceil_le_floor_add_one
- \+ *theorem* int.ceil_lt_add_one
- \+ *theorem* int.ceil_mono
- \+ *lemma* int.ceil_nonneg
- \+ *lemma* int.ceil_pos
- \+ *theorem* int.ceil_sub_int
- \+ *theorem* int.ceil_zero
- \+ *def* int.floor
- \+ *theorem* int.floor_add
- \+ *lemma* int.floor_add_fract
- \+ *theorem* int.floor_add_int
- \+ *theorem* int.floor_add_nat
- \+ *theorem* int.floor_coe
- \+ *lemma* int.floor_eq_iff
- \+ *lemma* int.floor_eq_on_Ico'
- \+ *lemma* int.floor_eq_on_Ico
- \+ *lemma* int.floor_fract
- \+ *theorem* int.floor_int_add
- \+ *theorem* int.floor_le
- \+ *theorem* int.floor_lt
- \+ *lemma* int.floor_lt_ceil_of_lt
- \+ *theorem* int.floor_mono
- \+ *theorem* int.floor_nonneg
- \+ *theorem* int.floor_one
- \+ *lemma* int.floor_pos
- \+ *theorem* int.floor_sub_int
- \+ *theorem* int.floor_sub_nat
- \+ *theorem* int.floor_zero
- \+ *def* int.fract
- \+ *theorem* int.fract_add
- \+ *lemma* int.fract_add_floor
- \+ *lemma* int.fract_coe
- \+ *theorem* int.fract_eq_fract
- \+ *theorem* int.fract_eq_iff
- \+ *lemma* int.fract_floor
- \+ *lemma* int.fract_fract
- \+ *theorem* int.fract_lt_one
- \+ *theorem* int.fract_mul_nat
- \+ *theorem* int.fract_nonneg
- \+ *lemma* int.fract_zero
- \+ *theorem* int.le_ceil
- \+ *theorem* int.le_floor
- \+ *theorem* int.lt_ceil
- \+ *theorem* int.lt_floor_add_one
- \+ *theorem* int.lt_succ_floor
- \+ *theorem* int.sub_one_lt_floor
- \- *theorem* le_ceil
- \- *theorem* le_floor
- \- *theorem* le_nat_ceil
- \- *theorem* le_nat_floor_iff
- \- *lemma* le_nat_floor_of_le
- \- *lemma* le_of_nat_ceil_le
- \- *theorem* lt_ceil
- \- *theorem* lt_floor_add_one
- \- *theorem* lt_nat_ceil
- \- *lemma* lt_nat_floor_add_one
- \- *lemma* lt_of_lt_nat_floor
- \- *lemma* lt_of_nat_ceil_lt
- \- *theorem* lt_succ_floor
- \+ *def* nat.ceil
- \+ *theorem* nat.ceil_add_nat
- \+ *theorem* nat.ceil_coe
- \+ *theorem* nat.ceil_eq_zero
- \+ *theorem* nat.ceil_le
- \+ *theorem* nat.ceil_lt_add_one
- \+ *theorem* nat.ceil_mono
- \+ *theorem* nat.ceil_zero
- \+ *def* nat.floor
- \+ *theorem* nat.floor_add_nat
- \+ *theorem* nat.floor_coe
- \+ *lemma* nat.floor_eq_zero_iff
- \+ *lemma* nat.floor_le
- \+ *lemma* nat.floor_lt_ceil_of_lt_of_pos
- \+ *theorem* nat.floor_lt_iff
- \+ *theorem* nat.floor_mono
- \+ *lemma* nat.floor_of_nonpos
- \+ *lemma* nat.floor_pos
- \+ *theorem* nat.floor_zero
- \+ *theorem* nat.le_ceil
- \+ *theorem* nat.le_floor_iff
- \+ *lemma* nat.le_floor_of_le
- \+ *lemma* nat.le_of_ceil_le
- \+ *theorem* nat.lt_ceil
- \+ *lemma* nat.lt_floor_add_one
- \+ *lemma* nat.lt_of_ceil_lt
- \+ *lemma* nat.lt_of_lt_floor
- \+ *lemma* nat.pos_of_floor_pos
- \+ *lemma* nat.sub_one_lt_floor
- \- *def* nat_ceil
- \- *theorem* nat_ceil_add_nat
- \- *theorem* nat_ceil_coe
- \- *theorem* nat_ceil_eq_zero
- \- *theorem* nat_ceil_le
- \- *theorem* nat_ceil_lt_add_one
- \- *theorem* nat_ceil_mono
- \- *theorem* nat_ceil_zero
- \- *def* nat_floor
- \- *theorem* nat_floor_add_nat
- \- *theorem* nat_floor_coe
- \- *lemma* nat_floor_eq_zero_iff
- \- *lemma* nat_floor_le
- \- *theorem* nat_floor_lt_iff
- \- *lemma* nat_floor_lt_nat_ceil_of_lt_of_pos
- \- *theorem* nat_floor_mono
- \- *lemma* nat_floor_of_nonpos
- \- *lemma* nat_floor_pos
- \- *theorem* nat_floor_zero
- \- *lemma* pos_of_nat_floor_pos
- \- *theorem* sub_one_lt_floor
- \- *lemma* sub_one_lt_nat_floor

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/specific_limits.lean


Modified src/data/rat/floor.lean


Modified src/data/real/basic.lean


Modified src/data/real/pi/wallis.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/number_theory/class_number/admissible_abs.lean


Modified src/number_theory/class_number/admissible_card_pow_degree.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2021-10-14 07:51:21](https://github.com/leanprover-community/mathlib/commit/264ff90)
refactor(analysis/special_functions): generalise nth-root lemmas ([#9704](https://github.com/leanprover-community/mathlib/pull/9704))
`exists_pow_nat_eq` and `exists_eq_mul_self` both hold for any algebraically closed field, so pull them out into `is_alg_closed/basic` and generalise appropriately
Closes [#4674](https://github.com/leanprover-community/mathlib/pull/4674)
#### Estimated changes
Modified src/analysis/special_functions/complex/log.lean
- \- *lemma* complex.exists_eq_mul_self
- \- *lemma* complex.exists_pow_nat_eq

Modified src/analysis/special_functions/trigonometric/complex.lean


Modified src/field_theory/is_alg_closed/basic.lean
- \+ *lemma* is_alg_closed.exists_eq_mul_self
- \+ *lemma* is_alg_closed.exists_pow_nat_eq



## [2021-10-14 07:51:19](https://github.com/leanprover-community/mathlib/commit/8d67d9a)
chore(category_theory/sites/*): Generalize universes ([#9675](https://github.com/leanprover-community/mathlib/pull/9675))
This generalizes the universe levels for sheaves to some extent.
This will allow us to now consider sheaves on `C : Type u` (satisfying `[category.{v} C]` and endowed with a Grothendieck topology) taking values in an arbitrary category with no additional universe restrictions.
The only part of the theory which has not been generalized is the equivalence of the sheaf condition with the condition involving Yoneda. To generalize this would require composing with `ulift_functors`'s, which we may or may not want to do.
#### Estimated changes
Modified src/category_theory/sites/closed.lean
- \+/\- *def* category_theory.functor.closed_sieves

Modified src/category_theory/sites/sheaf.lean
- \+/\- *def* category_theory.Sheaf_equiv_SheafOfTypes
- \+/\- *lemma* category_theory.is_sheaf_iff_is_sheaf_of_type
- \+/\- *def* category_theory.presheaf.is_sheaf_for_is_sheaf_for'
- \+/\- *lemma* category_theory.presheaf.is_sheaf_iff_is_sheaf_forget

Modified src/category_theory/sites/sheaf_of_types.lean
- \+/\- *def* category_theory.SheafOfTypes
- \+/\- *def* category_theory.SheafOfTypes_bot_equiv
- \+/\- *def* category_theory.SheafOfTypes_to_presheaf
- \+/\- *def* category_theory.equalizer.first_obj
- \+/\- *def* category_theory.equalizer.presieve.second_obj
- \+/\- *def* category_theory.equalizer.sieve.second_obj
- \+/\- *lemma* category_theory.presieve.extension_iff_amalgamation
- \+ *lemma* category_theory.presieve.family_of_elements.comp_prersheaf_map_comp
- \+ *lemma* category_theory.presieve.family_of_elements.comp_presheaf_map_id
- \+ *lemma* category_theory.presieve.family_of_elements.is_amalgamation.comp_presheaf_map
- \+/\- *def* category_theory.presieve.family_of_elements
- \+/\- *def* category_theory.presieve.is_separated
- \+/\- *def* category_theory.presieve.is_separated_for
- \+/\- *lemma* category_theory.presieve.is_separated_for_top
- \+/\- *lemma* category_theory.presieve.is_separated_of_is_sheaf
- \+/\- *lemma* category_theory.presieve.is_sheaf.is_sheaf_for
- \+/\- *def* category_theory.presieve.is_sheaf
- \+/\- *lemma* category_theory.presieve.is_sheaf_for.functor_inclusion_comp_extend
- \+/\- *lemma* category_theory.presieve.is_sheaf_for.hom_ext
- \+/\- *lemma* category_theory.presieve.is_sheaf_for.unique_extend
- \+/\- *def* category_theory.presieve.is_sheaf_for
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_iff_yoneda_sheaf_condition
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_iso
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_singleton_iso
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_subsieve
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_subsieve_aux
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_top_sieve
- \+/\- *lemma* category_theory.presieve.is_sheaf_iso
- \+/\- *lemma* category_theory.presieve.is_sheaf_of_le
- \+/\- *lemma* category_theory.presieve.is_sheaf_of_yoneda
- \+/\- *def* category_theory.presieve.nat_trans_equiv_compatible_family
- \+/\- *def* category_theory.presieve.yoneda_sheaf_condition

Modified src/topology/sheaves/sheaf_condition/sites.lean
- \+/\- *def* Top.presheaf.presieve_of_covering.pi_inters_to_second_obj
- \+/\- *def* Top.presheaf.presieve_of_covering.pi_opens_to_first_obj



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
Modified src/data/W/cardinal.lean


Modified src/logic/is_empty.lean
- \+ *lemma* is_empty_pi
- \+ *lemma* is_empty_pprod
- \+ *lemma* is_empty_prod
- \+ *lemma* is_empty_psum
- \+ *lemma* is_empty_sum

Modified src/set_theory/cardinal.lean
- \- *lemma* cardinal.eq_zero_iff_is_empty
- \- *lemma* cardinal.eq_zero_of_is_empty
- \+ *lemma* cardinal.mk_eq_zero
- \+ *lemma* cardinal.mk_eq_zero_iff
- \+ *lemma* cardinal.mk_ne_zero
- \+ *theorem* cardinal.mk_ne_zero_iff
- \- *theorem* cardinal.ne_zero_iff_nonempty
- \+/\- *theorem* cardinal.omega_ne_zero
- \+/\- *theorem* cardinal.prod_eq_zero

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean




## [2021-10-14 04:04:03](https://github.com/leanprover-community/mathlib/commit/3340617)
feat(algebra/bounds): `smul` of upper/lower bounds ([#9078](https://github.com/leanprover-community/mathlib/pull/9078))
This relates `lower_bounds (a • s)`/`upper_bounds (a • s)` and `a • lower_bounds s`/`a • upper_bounds s`.
#### Estimated changes
Modified src/algebra/module/ordered.lean
- \+ *lemma* bdd_above.smul_of_nonneg
- \+ *lemma* bdd_above.smul_of_nonpos
- \+ *lemma* bdd_above_smul_iff_of_neg
- \+ *lemma* bdd_above_smul_iff_of_pos
- \+ *lemma* bdd_below.smul_of_nonneg
- \+ *lemma* bdd_below.smul_of_nonpos
- \+ *lemma* bdd_below_smul_iff_of_neg
- \+ *lemma* bdd_below_smul_iff_of_pos
- \+ *lemma* lower_bounds_smul_of_neg
- \+ *lemma* lower_bounds_smul_of_pos
- \+ *lemma* smul_lower_bounds_subset_lower_bounds_smul
- \+ *lemma* smul_lower_bounds_subset_upper_bounds_smul
- \+ *lemma* smul_upper_bounds_subset_lower_bounds_smul
- \+ *lemma* smul_upper_bounds_subset_upper_bounds_smul
- \+ *lemma* upper_bounds_smul_of_neg
- \+ *lemma* upper_bounds_smul_of_pos



## [2021-10-13 21:29:32](https://github.com/leanprover-community/mathlib/commit/19da20b)
feat(combinatorics/hall): generalized Hall's Marriage Theorem ([#7825](https://github.com/leanprover-community/mathlib/pull/7825))
Used the generalized Kőnig's lemma to prove a version of Hall's Marriage Theorem with the `fintype` constraint on the index type removed.  The original `fintype` version is moved into `hall/finite.lean`, and the infinite version is put in `hall/basic.lean`.  They are in separate files because the infinite version pulls in `topology.category.Top.limits`, which is a rather large dependency.
#### Estimated changes
Modified docs/references.bib


Added src/combinatorics/hall/basic.lean
- \+ *theorem* finset.all_card_le_bUnion_card_iff_exists_injective
- \+ *theorem* fintype.all_card_le_filter_rel_iff_exists_injective
- \+ *theorem* fintype.all_card_le_rel_image_card_iff_exists_injective
- \+ *def* hall_finset_directed_order
- \+ *def* hall_matchings_functor
- \+ *lemma* hall_matchings_on.nonempty
- \+ *def* hall_matchings_on.restrict
- \+ *def* hall_matchings_on

Renamed src/combinatorics/hall.lean to src/combinatorics/hall/finite.lean
- \+ *theorem* finset.all_card_le_bUnion_card_iff_exists_injective'
- \- *theorem* finset.all_card_le_bUnion_card_iff_exists_injective
- \- *theorem* fintype.all_card_le_filter_rel_iff_exists_injective
- \- *theorem* fintype.all_card_le_rel_image_card_iff_exists_injective



## [2021-10-13 17:58:00](https://github.com/leanprover-community/mathlib/commit/5db83f9)
feat(set_theory/cardinal): add lemmas ([#9697](https://github.com/leanprover-community/mathlib/pull/9697))
We add three easy lemmas about cardinals living in different universes.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.add
- \+/\- *theorem* cardinal.lift_umax
- \+ *lemma* cardinal.mul

Modified src/set_theory/cofinality.lean




## [2021-10-13 17:57:59](https://github.com/leanprover-community/mathlib/commit/3faf0f5)
chore(data/real/irrational): add more lemmas ([#9684](https://github.com/leanprover-community/mathlib/pull/9684))
#### Estimated changes
Modified src/data/real/irrational.lean
- \+ *lemma* int.not_irrational
- \+ *theorem* irrational.add_int
- \+ *theorem* irrational.add_nat
- \+ *theorem* irrational.div_int
- \+ *theorem* irrational.div_nat
- \+ *theorem* irrational.div_rat
- \+ *theorem* irrational.int_add
- \+ *theorem* irrational.int_div
- \+ *theorem* irrational.int_mul
- \+ *theorem* irrational.int_sub
- \+ *theorem* irrational.mul_int
- \+ *theorem* irrational.mul_nat
- \+ *theorem* irrational.nat_add
- \+ *theorem* irrational.nat_div
- \+ *theorem* irrational.nat_mul
- \+ *theorem* irrational.nat_sub
- \+ *theorem* irrational.ne_int
- \+ *theorem* irrational.ne_nat
- \+ *theorem* irrational.ne_one
- \+ *theorem* irrational.ne_rat
- \+ *theorem* irrational.ne_zero
- \+ *theorem* irrational.of_add_int
- \+ *theorem* irrational.of_add_nat
- \+ *theorem* irrational.of_div_int
- \+ *theorem* irrational.of_div_nat
- \+ *theorem* irrational.of_div_rat
- \+ *theorem* irrational.of_int_add
- \+ *theorem* irrational.of_int_div
- \+ *theorem* irrational.of_int_mul
- \+ *theorem* irrational.of_int_sub
- \+ *theorem* irrational.of_mul_int
- \+ *theorem* irrational.of_mul_nat
- \+ *theorem* irrational.of_nat_add
- \+ *theorem* irrational.of_nat_div
- \+ *theorem* irrational.of_nat_mul
- \+ *theorem* irrational.of_nat_sub
- \+ *theorem* irrational.of_sub_int
- \+ *theorem* irrational.of_sub_nat
- \+ *theorem* irrational.rat_div
- \+ *theorem* irrational.sub_int
- \+ *theorem* irrational.sub_nat
- \+ *theorem* irrational_add_int_iff
- \+ *theorem* irrational_add_nat_iff
- \+ *theorem* irrational_div_int_iff
- \+ *theorem* irrational_div_nat_iff
- \+ *theorem* irrational_div_rat_iff
- \+ *theorem* irrational_int_add_iff
- \+ *theorem* irrational_int_div_iff
- \+ *theorem* irrational_int_mul_iff
- \+ *theorem* irrational_int_sub_iff
- \+ *theorem* irrational_mul_int_iff
- \+ *theorem* irrational_mul_nat_iff
- \+ *theorem* irrational_mul_rat_iff
- \+ *theorem* irrational_nat_add_iff
- \+ *theorem* irrational_nat_div_iff
- \+ *theorem* irrational_nat_mul_iff
- \+ *theorem* irrational_nat_sub_iff
- \+ *theorem* irrational_rat_div_iff
- \+ *theorem* irrational_rat_mul_iff
- \+ *theorem* irrational_sub_int_iff
- \+ *theorem* irrational_sub_nat_iff
- \+ *lemma* nat.not_irrational
- \+/\- *lemma* rat.not_irrational



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
Modified src/topology/connected.lean
- \+ *theorem* is_connected.subset_closure
- \+ *theorem* is_preconnected.subset_closure



## [2021-10-13 15:48:29](https://github.com/leanprover-community/mathlib/commit/32e1b6c)
chore(ring_theory/ideal): improve 1st isomorphism theorem docstrings ([#9699](https://github.com/leanprover-community/mathlib/pull/9699))
Fix a typo and add **bold** to the theorem names.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean




## [2021-10-13 15:48:28](https://github.com/leanprover-community/mathlib/commit/0ce4442)
refactor(algebra/group_power/order): relax linearity condition on `one_lt_pow` ([#9696](https://github.com/leanprover-community/mathlib/pull/9696))
`[linear_ordered_semiring R]` becomes `[ordered_semiring R] [nontrivial R]`. I also golf the proof and move ìt from `algebra.field_power` to `algebra.group_power.order`, where it belongs.
#### Estimated changes
Modified archive/imo/imo2013_q5.lean


Modified src/algebra/field_power.lean
- \+/\- *lemma* one_lt_fpow
- \- *lemma* one_lt_pow

Modified src/algebra/group_power/order.lean
- \+ *lemma* one_lt_pow

Modified src/number_theory/liouville/liouville_constant.lean




## [2021-10-13 15:48:27](https://github.com/leanprover-community/mathlib/commit/bc9e38f)
refactor(linear_algebra/dimension): remove some nontrivial assumptions ([#9693](https://github.com/leanprover-community/mathlib/pull/9693))
We remove some `nontrivial R` assumptions.
#### Estimated changes
Modified src/linear_algebra/dimension.lean




## [2021-10-13 15:48:25](https://github.com/leanprover-community/mathlib/commit/313db47)
feat(measure_theory/covering/besicovitch): remove measurability assumptions ([#9679](https://github.com/leanprover-community/mathlib/pull/9679))
For applications, it is important to allow non-measurable sets in the Besicovitch covering theorem. We tweak the proof to allow this.
Also give an improved statement that is easier to use in applications.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean
- \- *theorem* besicovitch.exists_disjoint_closed_ball_covering
- \+ *theorem* besicovitch.exists_disjoint_closed_ball_covering_ae
- \+ *theorem* besicovitch.exists_disjoint_closed_ball_covering_ae_aux
- \+ *theorem* besicovitch.exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux
- \- *theorem* besicovitch.exists_disjoint_closed_ball_covering_of_finite_measure



## [2021-10-13 15:48:24](https://github.com/leanprover-community/mathlib/commit/f29755b)
refactor(data/set/pairwise): generalize `pairwise_disjoint` to `semilattice_inf_bot` ([#9670](https://github.com/leanprover-community/mathlib/pull/9670))
`set.pairwise_disjoint` was only defined for `set (set α)`. Now, it's defined for `set α` where `semilattice_inf_bot α`. I also
* move it to `data.set.pairwise` because it's really not about `set` anymore.
* drop the `set` namespace.
* add more general elimination rules and rename the current one to `elim_set`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \- *lemma* set.pairwise_disjoint.elim
- \- *lemma* set.pairwise_disjoint.range
- \- *lemma* set.pairwise_disjoint.subset
- \- *def* set.pairwise_disjoint

Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise_disjoint.elim'
- \+ *lemma* set.pairwise_disjoint.elim
- \+ *lemma* set.pairwise_disjoint.elim_set
- \+ *lemma* set.pairwise_disjoint.range
- \+ *lemma* set.pairwise_disjoint.subset
- \+ *def* set.pairwise_disjoint

Modified src/data/setoid/partition.lean




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
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* has_scalar.comp.is_scalar_tower

Modified src/linear_algebra/basis.lean


Added test/has_scalar_comp_loop.lean
- \+ *def* foo



## [2021-10-13 15:48:21](https://github.com/leanprover-community/mathlib/commit/e8427b0)
feat(ring_theory/ideal/operation): add some extra definitions in the `double_quot` section ([#9649](https://github.com/leanprover-community/mathlib/pull/9649))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *def* double_quot.quot_quot_equiv_comm
- \+ *lemma* double_quot.quot_quot_equiv_comm_comp_quot_quot_mk
- \+ *lemma* double_quot.quot_quot_equiv_comm_quot_quot_mk
- \+ *lemma* double_quot.quot_quot_equiv_comm_symm
- \+ *lemma* double_quot.quot_quot_equiv_quot_sup_quot_quot_mk
- \+ *lemma* double_quot.quot_quot_equiv_quot_sup_symm_quot_quot_mk



## [2021-10-13 15:48:20](https://github.com/leanprover-community/mathlib/commit/a7ec633)
chore(algebra/*): add missing lemmas about `copy` on subobjects ([#9624](https://github.com/leanprover-community/mathlib/pull/9624))
This adds `coe_copy` and `copy_eq` to `sub{mul_action,group,ring,semiring,field,module,algebra,lie_module}`, to match the lemmas already present on `submonoid`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_copy
- \+ *lemma* subalgebra.copy_eq

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.coe_copy
- \+/\- *lemma* lie_submodule.coe_submodule_injective
- \+ *lemma* lie_submodule.copy_eq

Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.coe_copy
- \+ *lemma* submodule.copy_eq

Modified src/data/set_like/basic.lean


Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.coe_copy
- \+ *lemma* subfield.copy_eq

Modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* sub_mul_action.coe_copy
- \+ *lemma* sub_mul_action.copy_eq

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.coe_copy
- \+ *lemma* subgroup.copy_eq

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.coe_copy
- \+ *lemma* subring.copy_eq

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.coe_copy
- \+ *lemma* subsemiring.copy_eq



## [2021-10-13 15:48:18](https://github.com/leanprover-community/mathlib/commit/577cac1)
feat(algebra/order/nonneg): properties about the nonnegative cone ([#9598](https://github.com/leanprover-community/mathlib/pull/9598))
* Provide various classes on the type `{x : α // 0 ≤ x}` where `α` has some order (and algebraic) structure.
* Use this to automatically derive the classes on `nnreal`.
* We currently do not yet define `conditionally_complete_linear_order_bot nnreal` using nonneg, since that causes some errors (I think Lean then thinks that there are two orders that are not definitionally equal (unfolding only instances)).
* We leave a bunch of `example` lines in `nnreal` to show that `nnreal` has all the old classes. These could also be removed, if desired.
* We currently only give some instances and simp/norm_cast lemmas. This could be expanded in the future.
#### Estimated changes
Added src/algebra/order/nonneg.lean
- \+ *def* nonneg.coe_add_monoid_hom
- \+ *def* nonneg.coe_ring_hom
- \+ *lemma* nonneg.coe_to_nonneg
- \+ *lemma* nonneg.inv_mk
- \+ *lemma* nonneg.mk_add_mk
- \+ *lemma* nonneg.mk_div_mk
- \+ *lemma* nonneg.mk_eq_one
- \+ *lemma* nonneg.mk_eq_zero
- \+ *lemma* nonneg.mk_mul_mk
- \+ *lemma* nonneg.mk_sub_mk
- \+ *lemma* nonneg.nsmul_coe
- \+ *def* nonneg.to_nonneg
- \+ *lemma* nonneg.to_nonneg_coe
- \+ *lemma* nonneg.to_nonneg_le
- \+ *lemma* nonneg.to_nonneg_lt
- \+ *lemma* nonneg.to_nonneg_of_nonneg

Modified src/algebra/order/ring.lean
- \+ *lemma* le_iff_exists_nonneg_add

Modified src/analysis/normed_space/enorm.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.nsmul_coe

Modified src/measure_theory/decomposition/jordan.lean


Modified src/order/lattice_intervals.lean




## [2021-10-13 13:20:49](https://github.com/leanprover-community/mathlib/commit/aa67421)
lint(tactic/lint/misc): do not lint autogenerated proofs for bad universes ([#9676](https://github.com/leanprover-community/mathlib/pull/9676))
#### Estimated changes
Modified src/tactic/lint/misc.lean




## [2021-10-13 13:20:48](https://github.com/leanprover-community/mathlib/commit/ea360f2)
feat(group_theory/sylow): Frattini's Argument ([#9662](https://github.com/leanprover-community/mathlib/pull/9662))
Frattini's argument: If `N` is a normal subgroup of `G`, and `P` is a Sylow `p`-subgroup of `N`, then `PN=G`.
The proof is an application of Sylow's second theorem (all Sylow `p`-subgroups of `N` are conjugate).
#### Estimated changes
Modified src/group_theory/group_action/conj_act.lean
- \+ *lemma* mul_aut.conj_normal_coe

Modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* subgroup.pointwise_smul_def

Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.normalizer_sup_eq_top
- \+ *lemma* sylow.pointwise_smul_def
- \+ *lemma* sylow.smul_def



## [2021-10-13 13:20:46](https://github.com/leanprover-community/mathlib/commit/acc1d4b)
feat(analysis/normed_space/SemiNormedGroup/kernels) : add lemmas ([#9654](https://github.com/leanprover-community/mathlib/pull/9654))
From LTE.
#### Estimated changes
Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_comp_eq_desc
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_comp_eq_zero
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_norm_noninc
- \+ *lemma* SemiNormedGroup.explicit_cokernel_desc_zero
- \+ *lemma* SemiNormedGroup.explicit_cokernel_π_apply_dom_eq_zero
- \+ *lemma* SemiNormedGroup.explicit_cokernel_π_desc_apply
- \+ *lemma* SemiNormedGroup.explicit_cokernel_π_surjective



## [2021-10-13 13:20:45](https://github.com/leanprover-community/mathlib/commit/6ea59e3)
feat(category_theory/sites/sieves): Added functor pushforward ([#9647](https://github.com/leanprover-community/mathlib/pull/9647))
Defined `sieve.functor_pushforward`.
Proved that `sieve.functor_pushforward` and `sieve.functor_pullback` forms a Galois connection.
Provided some lemmas about `sieve.functor_pushforward`, `sieve.functor_pullback` regarding the lattice structure.
#### Estimated changes
Modified src/category_theory/sites/sieves.lean
- \+/\- *def* category_theory.presieve.functor_pullback
- \+/\- *lemma* category_theory.presieve.functor_pullback_id
- \+/\- *lemma* category_theory.presieve.functor_pullback_mem
- \+ *def* category_theory.presieve.functor_pushforward
- \+ *lemma* category_theory.presieve.functor_pushforward_comp
- \+ *lemma* category_theory.presieve.image_mem_functor_pushforward
- \+ *def* category_theory.sieve.ess_surj_full_functor_galois_insertion
- \+ *def* category_theory.sieve.fully_faithful_functor_galois_coinsertion
- \+ *lemma* category_theory.sieve.functor_galois_connection
- \+/\- *def* category_theory.sieve.functor_pullback
- \+ *lemma* category_theory.sieve.functor_pullback_arrows
- \+ *lemma* category_theory.sieve.functor_pullback_bot
- \+ *lemma* category_theory.sieve.functor_pullback_comp
- \+/\- *lemma* category_theory.sieve.functor_pullback_id
- \+ *lemma* category_theory.sieve.functor_pullback_inter
- \+ *lemma* category_theory.sieve.functor_pullback_monotone
- \+ *lemma* category_theory.sieve.functor_pullback_pushforward_le
- \+ *lemma* category_theory.sieve.functor_pullback_top
- \+ *lemma* category_theory.sieve.functor_pullback_union
- \+ *def* category_theory.sieve.functor_pushforward
- \+ *lemma* category_theory.sieve.functor_pushforward_bot
- \+ *lemma* category_theory.sieve.functor_pushforward_comp
- \+ *lemma* category_theory.sieve.functor_pushforward_extend_eq
- \+ *lemma* category_theory.sieve.functor_pushforward_id
- \+ *lemma* category_theory.sieve.functor_pushforward_monotone
- \+ *lemma* category_theory.sieve.functor_pushforward_union
- \+ *lemma* category_theory.sieve.image_mem_functor_pushforward
- \+ *lemma* category_theory.sieve.le_functor_pushforward_pullback



## [2021-10-13 13:20:44](https://github.com/leanprover-community/mathlib/commit/17d8928)
feat(algebra/graded_monoid,algebra/direct_sum/ring): provide lemmas about powers in graded monoids ([#9631](https://github.com/leanprover-community/mathlib/pull/9631))
The key results are `direct_sum.of_pow` and `graded_monoid.mk_pow`.
#### Estimated changes
Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* direct_sum.of_eq_of_graded_monoid_eq
- \+ *lemma* direct_sum.of_pow

Modified src/algebra/graded_monoid.lean
- \+ *def* graded_monoid.gmonoid.gnpow_rec
- \+ *lemma* graded_monoid.gmonoid.gnpow_rec_succ
- \+ *lemma* graded_monoid.gmonoid.gnpow_rec_zero
- \+ *lemma* graded_monoid.mk_pow



## [2021-10-13 13:20:43](https://github.com/leanprover-community/mathlib/commit/edf07cf)
feat(topology/sheaves/sheaf_condition/sites): Connect sheaves on sites to sheaves on spaces ([#9609](https://github.com/leanprover-community/mathlib/pull/9609))
Show that a sheaf on the site `opens X` is the same thing as a sheaf on the space `X`. This finally connects the theory of sheaves on sites to sheaves on spaces, which were previously independent of each other.
#### Estimated changes
Added src/topology/sheaves/sheaf_condition/sites.lean
- \+ *def* Top.presheaf.Sheaf_sites_to_sheaf_spaces
- \+ *def* Top.presheaf.Sheaf_spaces_equivelence_sheaf_sites
- \+ *def* Top.presheaf.Sheaf_spaces_to_sheaf_sites
- \+ *def* Top.presheaf.covering_of_presieve.diagram_nat_iso
- \+ *lemma* Top.presheaf.covering_of_presieve.first_obj_iso_comp_left_res_eq
- \+ *lemma* Top.presheaf.covering_of_presieve.first_obj_iso_comp_right_res_eq
- \+ *def* Top.presheaf.covering_of_presieve.first_obj_iso_pi_opens
- \+ *lemma* Top.presheaf.covering_of_presieve.first_obj_iso_pi_opens_π
- \+ *lemma* Top.presheaf.covering_of_presieve.fork_map_comp_first_obj_iso_pi_opens_eq
- \+ *def* Top.presheaf.covering_of_presieve.postcompose_diagram_fork_hom
- \+ *def* Top.presheaf.covering_of_presieve.postcompose_diagram_fork_iso
- \+ *def* Top.presheaf.covering_of_presieve.second_obj_iso_pi_inters
- \+ *lemma* Top.presheaf.covering_of_presieve.second_obj_iso_pi_inters_π
- \+ *lemma* Top.presheaf.covering_of_presieve.supr_eq_of_mem_grothendieck
- \+ *def* Top.presheaf.covering_of_presieve
- \+ *lemma* Top.presheaf.covering_of_presieve_apply
- \+ *lemma* Top.presheaf.is_sheaf_sites_iff_is_sheaf_spaces
- \+ *lemma* Top.presheaf.is_sheaf_sites_of_is_sheaf_spaces
- \+ *lemma* Top.presheaf.is_sheaf_spaces_of_is_sheaf_sites
- \+ *def* Top.presheaf.presieve_of_covering.first_obj_to_pi_opens
- \+ *lemma* Top.presheaf.presieve_of_covering.fork_map_comp_first_map_to_pi_opens_eq
- \+ *lemma* Top.presheaf.presieve_of_covering.fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq
- \+ *def* Top.presheaf.presieve_of_covering.hom_of_index
- \+ *def* Top.presheaf.presieve_of_covering.index_of_hom
- \+ *lemma* Top.presheaf.presieve_of_covering.index_of_hom_spec
- \+ *lemma* Top.presheaf.presieve_of_covering.mem_grothendieck_topology
- \+ *def* Top.presheaf.presieve_of_covering.pi_inters_to_second_obj
- \+ *def* Top.presheaf.presieve_of_covering.pi_opens_to_first_obj
- \+ *lemma* Top.presheaf.presieve_of_covering.pi_opens_to_first_obj_comp_fist_map_eq
- \+ *lemma* Top.presheaf.presieve_of_covering.pi_opens_to_first_obj_comp_second_map_eq
- \+ *lemma* Top.presheaf.presieve_of_covering.res_comp_pi_opens_to_first_obj_eq
- \+ *def* Top.presheaf.presieve_of_covering



## [2021-10-13 13:20:41](https://github.com/leanprover-community/mathlib/commit/f238733)
feat(algebra/order/smul): Monotonicity of scalar multiplication ([#9558](https://github.com/leanprover-community/mathlib/pull/9558))
Also prove `smul_nonneg`, `smul_pos` and variants.
#### Estimated changes
Modified src/algebra/module/ordered.lean
- \+ *lemma* antitone_smul_left
- \+ *def* order_iso.smul_left_dual
- \+ *lemma* smul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* smul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* strict_anti_smul_left

Modified src/algebra/order/smul.lean
- \+ *lemma* monotone_smul_left
- \+ *lemma* order_dual.of_dual_smul
- \+ *lemma* order_dual.to_dual_smul
- \+ *def* order_iso.smul_left
- \+ *lemma* smul_nonneg
- \+ *lemma* smul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* strict_mono_smul_left



## [2021-10-13 12:04:30](https://github.com/leanprover-community/mathlib/commit/04ed867)
chore(topology/uniform_space/cauchy): add a few simple lemmas ([#9685](https://github.com/leanprover-community/mathlib/pull/9685))
* rename `cauchy_prod` to `cauchy.prod`;
* add `cauchy_seq.tendsto_uniformity`, `cauchy_seq.nonempty`,
  `cauchy_seq.comp_tendsto`, `cauchy_seq.prod`, `cauchy_seq.prod_map`,
  `uniform_continuous.comp_cauchy_seq`, and
  `filter.tendsto.subseq_mem_entourage`;
* drop `[nonempty _]` assumption in `cauchy_seq.mem_entourage`.
#### Estimated changes
Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy.prod
- \- *lemma* cauchy_prod
- \+ *lemma* cauchy_seq.comp_tendsto
- \+/\- *lemma* cauchy_seq.mem_entourage
- \+ *lemma* cauchy_seq.nonempty
- \+ *lemma* cauchy_seq.prod
- \+ *lemma* cauchy_seq.prod_map
- \+ *lemma* cauchy_seq.tendsto_uniformity
- \+ *lemma* filter.tendsto.subseq_mem_entourage
- \+ *lemma* uniform_continuous.comp_cauchy_seq



## [2021-10-13 09:37:08](https://github.com/leanprover-community/mathlib/commit/46a7014)
feat(data/equiv/basic): psigma_congr_right ([#9687](https://github.com/leanprover-community/mathlib/pull/9687))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.psigma_congr_right
- \+ *lemma* equiv.psigma_congr_right_refl
- \+ *lemma* equiv.psigma_congr_right_symm
- \+ *lemma* equiv.psigma_congr_right_trans
- \+/\- *def* equiv.psigma_equiv_sigma
- \+/\- *def* equiv.sigma_congr_right
- \+/\- *lemma* equiv.sigma_congr_right_refl
- \+/\- *lemma* equiv.sigma_congr_right_symm
- \+/\- *lemma* equiv.sigma_congr_right_trans



## [2021-10-13 09:37:07](https://github.com/leanprover-community/mathlib/commit/4c1a9c4)
chore(order/filter): add 2 lemmas ([#9682](https://github.com/leanprover-community/mathlib/pull/9682))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.frequently_and_distrib_left
- \+ *lemma* filter.frequently_and_distrib_right



## [2021-10-13 09:37:00](https://github.com/leanprover-community/mathlib/commit/8886386)
feat(star/basic): add a `star_monoid (units R)` instance ([#9681](https://github.com/leanprover-community/mathlib/pull/9681))
This also moves all the `opposite R` instances to be adjacent, and add some missing `star_module` definitions.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \- *lemma* op_star
- \+ *lemma* opposite.op_star
- \+ *lemma* opposite.unop_star
- \+ *lemma* units.coe_star
- \+ *lemma* units.coe_star_inv
- \- *lemma* unop_star



## [2021-10-13 09:36:59](https://github.com/leanprover-community/mathlib/commit/52d5fd4)
feat(linear_algebra/{dimension,affine_space/finite_dimensional}): independent subsets of finite-dimensional spaces are finite. ([#9674](https://github.com/leanprover-community/mathlib/pull/9674))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* fintype_of_fintype_ne

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* finite_of_fin_dim_affine_independent

Modified src/linear_algebra/dimension.lean
- \+ *lemma* finite_of_is_noetherian_linear_independent



## [2021-10-13 07:56:13](https://github.com/leanprover-community/mathlib/commit/2c8abe5)
feat(algebra/star): `star_gpow` and `star_fpow` ([#9661](https://github.com/leanprover-community/mathlib/pull/9661))
One unrelated proof changes as the import additions pulls in a simp lemma that was previously missing, making the call to `ring` no longer necessary.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* star_fpow
- \+ *lemma* star_gpow

Modified src/ring_theory/polynomial/bernstein.lean




## [2021-10-13 02:43:35](https://github.com/leanprover-community/mathlib/commit/ea70e1c)
chore(scripts): update nolints.txt ([#9686](https://github.com/leanprover-community/mathlib/pull/9686))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-10-12 22:59:49](https://github.com/leanprover-community/mathlib/commit/c65de1e)
chore(data/sym/sym2): speed up some proofs ([#9677](https://github.com/leanprover-community/mathlib/pull/9677))
In one test, elaboration of sym2_ext went from 46.9s to 734ms, and of elems_iff_eq from 54.3s to 514ms.
#### Estimated changes
Modified src/data/sym/sym2.lean




## [2021-10-12 17:00:40](https://github.com/leanprover-community/mathlib/commit/66285c9)
feat(topology/instances/ennreal): if a tsum is finite, then the tsum over the complement of a finset tends to 0 at top ([#9665](https://github.com/leanprover-community/mathlib/pull/9665))
Together with minor tweaks of the library:
* rename `bounded.subset` to `bounded.mono`
* remove `bUnion_subset_bUnion_right`, which is exactly the same as `bUnion_mono`. Same for intersections.
* add `bUnion_congr` and `bInter_congr`
* introduce lemma `null_of_locally_null`: if a set has zero measure in a neighborhood of each of its points, then it has zero measure in a second-countable space.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.subset_set_bUnion_of_mem

Modified src/data/set/accumulate.lean


Modified src/data/set/function.lean
- \+ *lemma* set.inj_on.pairwise_on_image

Modified src/data/set/lattice.lean
- \+ *lemma* set.bInter_congr
- \- *theorem* set.bInter_subset_bInter_right
- \+ *lemma* set.bUnion_congr
- \- *theorem* set.bUnion_subset_bUnion_right
- \+ *lemma* set.pairwise_on_sUnion

Modified src/dynamics/omega_limit.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.null_of_locally_null

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable.sigma
- \+ *lemma* tendsto_tsum_compl_at_top_zero
- \+/\- *lemma* tsum_comm
- \+/\- *lemma* tsum_prod
- \+/\- *lemma* tsum_sigma

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_tsum_compl_at_top_zero

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.tendsto_tsum_compl_at_top_zero

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded.mono
- \- *lemma* metric.bounded.subset

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/subset_properties.lean




## [2021-10-12 17:00:39](https://github.com/leanprover-community/mathlib/commit/817c70d)
feat(category_theory/*): Functors about comma categories. ([#9627](https://github.com/leanprover-community/mathlib/pull/9627))
Added `pre` and `post` for `comma`, `structured_arrow`, `costructured_arrow`.
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *def* category_theory.comma.post
- \+ *def* category_theory.comma.pre_left
- \+ *def* category_theory.comma.pre_right

Modified src/category_theory/structured_arrow.lean
- \+ *def* category_theory.costructured_arrow.post
- \+ *def* category_theory.costructured_arrow.pre
- \+ *def* category_theory.structured_arrow.post
- \+ *def* category_theory.structured_arrow.pre



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
Modified src/algebra/star/basic.lean
- \+ *lemma* star_div'
- \+ *lemma* star_div
- \+ *lemma* star_gsmul
- \+ *lemma* star_inv'
- \+ *lemma* star_inv
- \+ *lemma* star_mul'
- \+/\- *lemma* star_neg
- \+ *lemma* star_nsmul
- \+ *lemma* star_pow
- \+ *lemma* star_prod
- \+/\- *lemma* star_sub
- \+/\- *lemma* star_sum



## [2021-10-12 11:41:14](https://github.com/leanprover-community/mathlib/commit/b486c88)
chore(analysis): fix file name ([#9673](https://github.com/leanprover-community/mathlib/pull/9673))
This file was moved since the docstring was written
#### Estimated changes
Modified src/analysis/calculus/parametric_integral.lean




## [2021-10-12 11:41:13](https://github.com/leanprover-community/mathlib/commit/bcb2943)
chore(set_theory/cardinal): move defs/lemmas about `lift` up ([#9669](https://github.com/leanprover-community/mathlib/pull/9669))
#### Estimated changes
Modified src/set_theory/cardinal.lean




## [2021-10-12 11:41:12](https://github.com/leanprover-community/mathlib/commit/a979d15)
feat(order/filter): `∃ᶠ m in at_top, m ≡ d [MOD n]` ([#9666](https://github.com/leanprover-community/mathlib/pull/9666))
#### Estimated changes
Added src/order/filter/modeq.lean
- \+ *lemma* nat.frequently_even
- \+ *lemma* nat.frequently_mod_eq
- \+ *lemma* nat.frequently_modeq
- \+ *lemma* nat.frequently_odd



## [2021-10-12 08:59:45](https://github.com/leanprover-community/mathlib/commit/fd7da4e)
refactor(combinatorics/partition): add `nat` namespace ([#9672](https://github.com/leanprover-community/mathlib/pull/9672))
`partition` is now `nat.partition`
#### Estimated changes
Modified src/combinatorics/partition.lean
- \+ *lemma* nat.partition.count_of_sums_of_ne_zero
- \+ *lemma* nat.partition.count_of_sums_zero
- \+ *def* nat.partition.distincts
- \+ *def* nat.partition.indiscrete_partition
- \+ *def* nat.partition.odd_distincts
- \+ *def* nat.partition.odds
- \+ *def* nat.partition.of_composition
- \+ *lemma* nat.partition.of_composition_surj
- \+ *def* nat.partition.of_multiset
- \+ *def* nat.partition.of_sums
- \+ *structure* nat.partition
- \- *lemma* partition.count_of_sums_of_ne_zero
- \- *lemma* partition.count_of_sums_zero
- \- *def* partition.distincts
- \- *def* partition.indiscrete_partition
- \- *def* partition.odd_distincts
- \- *def* partition.odds
- \- *def* partition.of_composition
- \- *lemma* partition.of_composition_surj
- \- *def* partition.of_multiset
- \- *def* partition.of_sums
- \- *structure* partition

Modified src/group_theory/perm/cycle_type.lean
- \+/\- *def* equiv.perm.partition



## [2021-10-12 08:59:43](https://github.com/leanprover-community/mathlib/commit/2e72f35)
refactor(data/opposite): Remove the `op_induction` tactic ([#9660](https://github.com/leanprover-community/mathlib/pull/9660))
The `induction` tactic is already powerful enough for this; we don't have `order_dual_induction` or `nat_induction` as tactics.
The bulk of this change is replacing `op_induction x` with `induction x using opposite.rec`.
This leaves behind the non-interactive `op_induction'` which is still needed as a `tidy` hook.
This also renames the def `opposite.op_induction` to `opposite.rec` to match `order_dual.rec` etc.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/opposites.lean


Modified src/algebra/quandle.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/limits/cones.lean


Modified src/data/opposite.lean
- \- *def* opposite.op_induction

Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified src/topology/sheaves/stalks.lean




## [2021-10-12 08:59:41](https://github.com/leanprover-community/mathlib/commit/ad4040d)
feat(algebra/opposites): provide npow and gpow explicitly, prove `op_gpow` and `unop_gpow` ([#9659](https://github.com/leanprover-community/mathlib/pull/9659))
By populating the `npow` and `gpow` fields in the obvious way, `op_pow` and `unop_pow` are true definitionally.
This adds the new lemmas `op_gpow` and `unop_gpow` which works for `group`s and `division_ring`s too.
Note that we do not provide an explicit `div` in `div_inv_monoid`, because there is no "reversed division" operator to define it via.
This also reorders the lemmas so that the definitional lemmas are available before any proof obligations might appear in stronger typeclasses.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* opposite.op_gpow
- \+/\- *lemma* opposite.op_pow
- \+ *lemma* opposite.unop_gpow
- \+/\- *lemma* opposite.unop_pow

Modified src/algebra/opposites.lean




## [2021-10-12 08:59:38](https://github.com/leanprover-community/mathlib/commit/34ffb15)
feat(linear_algebra/affine_space/finite_dimensional): upgrade `affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one` to an iff ([#9657](https://github.com/leanprover-community/mathlib/pull/9657))
Also including some related, but strictly speaking independent, lemmas such as `affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial`.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.subsingleton_iff

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nonempty
- \+ *lemma* affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial
- \+ *lemma* affine_subspace.card_pos_of_affine_span_eq_top
- \+ *lemma* affine_subspace.vector_span_eq_top_of_affine_span_eq_top

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one
- \- *lemma* affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one



## [2021-10-12 08:16:55](https://github.com/leanprover-community/mathlib/commit/1023d81)
chore(ring_theory/tensor_product): squeeze simps in a slow proof ([#9671](https://github.com/leanprover-community/mathlib/pull/9671))
This proof just timed out in bors. Goes from 21s to 1s on my computer just by squeezing the simps.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean




## [2021-10-12 06:20:54](https://github.com/leanprover-community/mathlib/commit/a132d0a)
chore(analysis): move some files to `analysis/normed/group` ([#9667](https://github.com/leanprover-community/mathlib/pull/9667))
#### Estimated changes
Renamed src/analysis/normed_space/SemiNormedGroup.lean to src/analysis/normed/group/SemiNormedGroup.lean


Renamed src/analysis/normed_space/SemiNormedGroup/kernels.lean to src/analysis/normed/group/SemiNormedGroup/kernels.lean


Renamed src/analysis/normed_space/normed_group_hom.lean to src/analysis/normed/group/hom.lean


Renamed src/analysis/normed_space/normed_group_hom_completion.lean to src/analysis/normed/group/hom_completion.lean


Renamed src/analysis/normed_space/normed_group_quotient.lean to src/analysis/normed/group/quotient.lean


Modified src/measure_theory/function/lp_space.lean




## [2021-10-12 01:53:33](https://github.com/leanprover-community/mathlib/commit/638dd0f)
feat(data/dfinsupp, algebra/direct_sum/module): direct sum on fintype ([#9664](https://github.com/leanprover-community/mathlib/pull/9664))
Analogues for `dfinsupp`/`direct_sum` of definitions/lemmas such as `finsupp.equiv_fun_on_fintype`:  a `dfinsupp`/`direct_sum` over a finite index set is canonically equivalent to `pi` over the same index set.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean
- \+ *def* direct_sum.linear_equiv_fun_on_fintype
- \+ *lemma* direct_sum.linear_equiv_fun_on_fintype_lof
- \+ *lemma* direct_sum.linear_equiv_fun_on_fintype_symm_coe
- \+ *lemma* direct_sum.linear_equiv_fun_on_fintype_symm_single

Modified src/data/dfinsupp.lean
- \+ *def* dfinsupp.equiv_fun_on_fintype
- \+ *lemma* dfinsupp.equiv_fun_on_fintype_single
- \+ *lemma* dfinsupp.equiv_fun_on_fintype_symm_coe
- \+ *lemma* dfinsupp.equiv_fun_on_fintype_symm_single
- \+ *lemma* dfinsupp.single_eq_pi_single



## [2021-10-11 22:34:26](https://github.com/leanprover-community/mathlib/commit/c2a30be)
feat(analysis/normed_space/normed_group_hom): add norm_noninc.neg ([#9658](https://github.com/leanprover-community/mathlib/pull/9658))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.norm_noninc.neg_iff



## [2021-10-11 21:39:10](https://github.com/leanprover-community/mathlib/commit/df132fe)
feat(topology/path_connected): add `path.reparam` for reparametrising a path. ([#9643](https://github.com/leanprover-community/mathlib/pull/9643))
I've also added `simps` to some of the definitions in this file.
#### Estimated changes
Modified src/topology/path_connected.lean
- \+ *lemma* path.coe_to_fun
- \+ *lemma* path.range_reparam
- \+/\- *def* path.refl
- \+ *lemma* path.refl_reparam
- \+ *def* path.reparam
- \+ *lemma* path.reparam_id
- \+ *def* path.simps.apply
- \+/\- *def* path.symm



## [2021-10-11 20:04:44](https://github.com/leanprover-community/mathlib/commit/136d0ce)
feat(topology/homotopy/path): Add homotopy between paths ([#9141](https://github.com/leanprover-community/mathlib/pull/9141))
There is also a lemma about `path.to_continuous_map` which I needed in a prior iteration of this PR that I missed in [#9133](https://github.com/leanprover-community/mathlib/pull/9133)
#### Estimated changes
Modified src/topology/homotopy/basic.lean


Added src/topology/homotopy/path.lean
- \+ *lemma* path.homotopic.equivalence
- \+ *lemma* path.homotopic.refl
- \+ *lemma* path.homotopic.symm
- \+ *lemma* path.homotopic.trans
- \+ *def* path.homotopic
- \+ *lemma* path.homotopy.coe_fn_injective
- \+ *def* path.homotopy.eval
- \+ *lemma* path.homotopy.eval_one
- \+ *lemma* path.homotopy.eval_zero
- \+ *def* path.homotopy.hcomp
- \+ *lemma* path.homotopy.hcomp_apply
- \+ *lemma* path.homotopy.hcomp_half
- \+ *def* path.homotopy.refl
- \+ *lemma* path.homotopy.source
- \+ *def* path.homotopy.symm
- \+ *lemma* path.homotopy.symm_symm
- \+ *lemma* path.homotopy.symm_trans
- \+ *lemma* path.homotopy.target
- \+ *def* path.homotopy.trans
- \+ *lemma* path.homotopy.trans_apply
- \+ *abbreviation* path.homotopy

Modified src/topology/path_connected.lean
- \+ *lemma* path.coe_to_continuous_map



## [2021-10-11 18:55:35](https://github.com/leanprover-community/mathlib/commit/6872dfb)
feat(analysis/normed/group/basic): add norm_le_add_norm_add ([#9655](https://github.com/leanprover-community/mathlib/pull/9655))
From LTE.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* norm_le_add_norm_add



## [2021-10-11 15:29:09](https://github.com/leanprover-community/mathlib/commit/fa5d9d6)
feat(tactic/lint/misc): unused haves and suffices linters ([#9310](https://github.com/leanprover-community/mathlib/pull/9310))
A linter for unused term mode have and suffices statements.
Based on initial work by @robertylewis https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/linter.20for.20helping.20grading/near/209243601 but hopefully with less false positives now.
#### Estimated changes
Modified src/control/traversable/instances.lean


Modified src/order/complete_lattice.lean


Modified src/tactic/lint/misc.lean


Added test/lint_unused_haves_suffices.lean
- \+ *lemma* test_a
- \+ *lemma* test_b
- \+ *lemma* test_c
- \+ *theorem* test_d
- \+ *theorem* test_map_reverse



## [2021-10-11 07:59:25](https://github.com/leanprover-community/mathlib/commit/c2fde70)
feat(number_theory/liouville): Liouville numbers form a dense Gδ set ([#9646](https://github.com/leanprover-community/mathlib/pull/9646))
#### Estimated changes
Added src/number_theory/liouville/residual.lean
- \+ *lemma* dense_irrational
- \+ *lemma* dense_liouville
- \+ *lemma* eventually_residual_irrational
- \+ *lemma* eventually_residual_liouville
- \+ *lemma* is_Gδ_irrational
- \+ *lemma* is_Gδ_set_of_liouville
- \+ *lemma* set_of_liouville_eq_Inter_Union
- \+ *lemma* set_of_liouville_eq_irrational_inter_Inter_Union

Modified src/topology/metric_space/baire.lean
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
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_cons
- \+/\- *lemma* finset.prod_multiset_map_count
- \- *lemma* finset.sum_multiset_map_count

Added src/algebra/big_operators/option.lean
- \+ *lemma* finset.prod_erase_none
- \+ *lemma* finset.prod_insert_none

Modified src/algebra/polynomial/big_operators.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.option_is_some_equiv

Modified src/data/finset/basic.lean
- \+ *theorem* finset.bUnion_congr
- \+ *theorem* finset.card_cons
- \+ *lemma* finset.coe_cons
- \+ *lemma* finset.cons_subset_cons
- \+/\- *def* finset.map_embedding
- \+/\- *theorem* finset.map_inj
- \+/\- *theorem* finset.map_subset_map
- \+/\- *theorem* finset.mem_cons
- \+ *lemma* finset.subtype_mono
- \- *theorem* option.mem_to_finset
- \- *def* option.to_finset
- \- *theorem* option.to_finset_none
- \- *theorem* option.to_finset_some

Modified src/data/finset/lattice.lean


Added src/data/finset/option.lean
- \+ *theorem* finset.card_insert_none
- \+ *lemma* finset.coe_erase_none
- \+ *def* finset.erase_none
- \+ *lemma* finset.erase_none_empty
- \+ *lemma* finset.erase_none_eq_bUnion
- \+ *lemma* finset.erase_none_image_some
- \+ *lemma* finset.erase_none_insert_none
- \+ *lemma* finset.erase_none_inter
- \+ *lemma* finset.erase_none_map_some
- \+ *lemma* finset.erase_none_none
- \+ *lemma* finset.erase_none_union
- \+ *lemma* finset.image_some_erase_none
- \+ *def* finset.insert_none
- \+ *lemma* finset.insert_none_erase_none
- \+ *lemma* finset.map_some_erase_none
- \+ *lemma* finset.mem_erase_none
- \+ *theorem* finset.mem_insert_none
- \+ *theorem* finset.some_mem_insert_none
- \+ *theorem* option.card_to_finset
- \+ *theorem* option.mem_to_finset
- \+ *def* option.to_finset
- \+ *theorem* option.to_finset_none
- \+ *theorem* option.to_finset_some

Modified src/data/finset/pimage.lean


Modified src/data/fintype/basic.lean
- \- *def* finset.insert_none
- \- *theorem* finset.mem_insert_none
- \- *theorem* finset.some_mem_insert_none

Modified src/data/fintype/card.lean


Modified src/data/set/basic.lean
- \+ *theorem* set.insert_subset_insert_iff

Modified src/logic/embedding.lean




## [2021-10-11 07:59:23](https://github.com/leanprover-community/mathlib/commit/1539ee1)
refactor(topology/sheaves/*): Make sheaf condition a Prop ([#9607](https://github.com/leanprover-community/mathlib/pull/9607))
Make `sheaf_condition` into a `Prop` and redefine the type of sheaves on a topological space `X` as a subtype of `(opens X)ᵒᵖ ⥤ C`.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.restrict
- \+ *def* algebraic_geometry.LocallyRingedSpace.restrict_top_iso

Modified src/algebraic_geometry/sheafed_space.lean
- \+/\- *def* algebraic_geometry.SheafedSpace.sheaf

Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *def* algebraic_geometry.structure_sheaf.basic_open_iso
- \+/\- *lemma* algebraic_geometry.structure_sheaf.exists_const
- \+/\- *def* algebraic_geometry.structure_sheaf.global_sections_iso
- \+/\- *def* algebraic_geometry.structure_sheaf.to_stalk

Modified src/topology/sheaves/forget.lean
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_comp
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_comp

Modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* Top.subpresheaf_to_Types.is_sheaf
- \- *def* Top.subpresheaf_to_Types.sheaf_condition

Modified src/topology/sheaves/sheaf.lean
- \+ *def* Top.presheaf.is_sheaf
- \+ *lemma* Top.presheaf.is_sheaf_iso_iff
- \+ *lemma* Top.presheaf.is_sheaf_of_iso
- \+ *lemma* Top.presheaf.is_sheaf_punit
- \- *def* Top.presheaf.sheaf_condition
- \- *def* Top.presheaf.sheaf_condition_equiv_of_iso
- \- *def* Top.presheaf.sheaf_condition_punit
- \+/\- *def* Top.sheaf.forget
- \+ *def* Top.sheaf
- \- *structure* Top.sheaf

Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_opens_le_cover
- \+ *def* Top.presheaf.is_sheaf_opens_le_cover
- \+ *lemma* Top.presheaf.is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_opens_le_cover
- \- *def* Top.presheaf.sheaf_condition_opens_le_cover
- \- *def* Top.presheaf.sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections

Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections
- \+ *def* Top.presheaf.is_sheaf_pairwise_intersections
- \+ *def* Top.presheaf.is_sheaf_preserves_limit_pairwise_intersections
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_pairwise_intersections
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections
- \- *def* Top.presheaf.sheaf_condition_pairwise_intersections
- \- *def* Top.presheaf.sheaf_condition_preserves_limit_pairwise_intersections

Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean
- \- *def* Top.presheaf.gluing
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing
- \+ *lemma* Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing_types
- \+ *lemma* Top.presheaf.is_sheaf_of_is_sheaf_unique_gluing_types
- \+ *def* Top.presheaf.is_sheaf_unique_gluing
- \+ *lemma* Top.presheaf.is_sheaf_unique_gluing_of_is_sheaf_types
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_unique_gluing
- \- *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_unique_gluing_types
- \- *def* Top.presheaf.sheaf_condition_of_exists_unique_gluing
- \- *def* Top.presheaf.sheaf_condition_of_sheaf_condition_unique_gluing_types
- \- *def* Top.presheaf.sheaf_condition_unique_gluing
- \- *def* Top.presheaf.sheaf_condition_unique_gluing_of_sheaf_condition_types
- \+/\- *lemma* Top.sheaf.eq_of_locally_eq
- \+/\- *lemma* Top.sheaf.exists_unique_gluing

Modified src/topology/sheaves/sheaf_of_functions.lean
- \- *def* Top.presheaf.to_Type
- \+ *lemma* Top.presheaf.to_Type_is_sheaf
- \- *def* Top.presheaf.to_Types
- \+ *lemma* Top.presheaf.to_Types_is_sheaf

Modified src/topology/sheaves/sheafify.lean
- \+/\- *def* Top.presheaf.sheafify_stalk_iso
- \+/\- *def* Top.presheaf.stalk_to_fiber
- \+/\- *def* Top.presheaf.to_sheafify

Modified src/topology/sheaves/stalks.lean
- \+/\- *lemma* Top.presheaf.section_ext



## [2021-10-11 07:59:22](https://github.com/leanprover-community/mathlib/commit/4a191ad)
feat(algebra.algebra.subalgebra): add `subalgebra.gc_map_comap` ([#9435](https://github.com/leanprover-community/mathlib/pull/9435))
Other changes:
* add `linear_map.coe_inl`/`linear_map.coe_inr` and move `@[simp]` from `inl_apply`/`inr_apply` to these lemmas;
* fix a typo in the name (`adjoint` → `adjoin`);
* drop `algebra.adjoin_inl_union_inr_le_prod `: we prove an equality anyway;
* add `alg_hom.map_adjoin` (same as `(adjoin_image _ _ _).symm`) to match `monoid_hom.map_closure` etc.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.gc_map_comap

Modified src/linear_algebra/prod.lean
- \+ *theorem* linear_map.coe_inl
- \+ *theorem* linear_map.coe_inr
- \+/\- *theorem* linear_map.inl_apply
- \+/\- *theorem* linear_map.inr_apply

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* alg_hom.map_adjoin
- \- *lemma* algebra.adjoin_inl_union_inr_le_prod
- \+ *lemma* algebra.adjoin_prod_le
- \- *lemma* algebra.adjoint_prod_le



## [2021-10-11 06:17:12](https://github.com/leanprover-community/mathlib/commit/30cf8b7)
feat(group_theory/subgroup/basic): apply_mem_map_injective ([#9637](https://github.com/leanprover-community/mathlib/pull/9637))
A translation of `function.injective.mem_set_image`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mem_map_iff_mem

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.mem_map_iff_mem



## [2021-10-11 06:17:11](https://github.com/leanprover-community/mathlib/commit/957f64e)
feat(algebra/floor): When the floor is strictly positive ([#9625](https://github.com/leanprover-community/mathlib/pull/9625))
`⌊a⌋₊` and `⌊a⌋` are strictly positive iff `1 ≤ a`. We use this to slightly golf IMO 2013 P5.
#### Estimated changes
Modified archive/imo/imo2013_q5.lean


Modified src/algebra/floor.lean
- \+ *lemma* floor_pos
- \+ *lemma* nat_floor_pos
- \+ *lemma* sub_one_lt_nat_floor



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
Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* abs_dist_sub_le_dist_add_add
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* add_mem_ball_iff_norm
- \+/\- *lemma* add_mem_closed_ball_iff_norm
- \+/\- *lemma* add_monoid_hom.continuous_of_bound
- \+/\- *lemma* add_monoid_hom.isometry_iff_norm
- \+/\- *lemma* add_monoid_hom.isometry_of_norm
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound
- \+/\- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+/\- *lemma* antilipschitz_with.add_lipschitz_with
- \+/\- *lemma* antilipschitz_with.add_sub_lipschitz_with
- \+/\- *lemma* ball_zero_eq
- \+/\- *lemma* bounded_iff_forall_norm_le
- \+/\- *lemma* cauchy_seq.add
- \+/\- *lemma* cauchy_seq_sum_of_eventually_eq
- \+/\- *lemma* coe_neg_sphere
- \+/\- *lemma* coe_nnnorm
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* continuous_norm
- \+/\- *lemma* controlled_sum_of_mem_closure
- \+/\- *lemma* controlled_sum_of_mem_closure_range
- \+/\- *lemma* dist_add_add_le
- \+/\- *lemma* dist_add_add_le_of_le
- \+/\- *lemma* dist_add_left
- \+/\- *lemma* dist_add_right
- \+/\- *lemma* dist_eq_norm'
- \+/\- *lemma* dist_eq_norm
- \+/\- *lemma* dist_le_norm_add_norm
- \+/\- *lemma* dist_neg_neg
- \+/\- *lemma* dist_norm_norm_le
- \+/\- *lemma* dist_sub_left
- \+/\- *lemma* dist_sub_right
- \+/\- *lemma* dist_sub_sub_le
- \+/\- *lemma* dist_sub_sub_le_of_le
- \+/\- *lemma* dist_sum_sum_le
- \+/\- *lemma* dist_sum_sum_le_of_le
- \+/\- *lemma* dist_zero_left
- \+/\- *lemma* dist_zero_right
- \+/\- *lemma* edist_add_add_le
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* eq_of_norm_sub_eq_zero
- \+/\- *lemma* eq_of_norm_sub_le_zero
- \+/\- *lemma* eventually_ne_of_tendsto_norm_at_top
- \+/\- *lemma* filter.tendsto.norm
- \+/\- *lemma* is_bounded_under_of_tendsto
- \+/\- *lemma* is_compact.exists_bound_of_continuous_on
- \+/\- *lemma* isometric.add_left_symm
- \+/\- *lemma* isometric.add_left_to_equiv
- \+/\- *lemma* isometric.add_right_apply
- \+/\- *lemma* isometric.add_right_symm
- \+/\- *lemma* isometric.add_right_to_equiv
- \+/\- *lemma* isometric.coe_add_left
- \+/\- *lemma* isometric.coe_add_right
- \+/\- *lemma* isometric.coe_neg
- \+/\- *lemma* isometric.neg_symm
- \+/\- *lemma* isometric.neg_to_equiv
- \+/\- *lemma* lipschitz_on_with.norm_sub_le
- \+/\- *lemma* lipschitz_on_with_iff_norm_sub_le
- \+/\- *lemma* lipschitz_with.add
- \+/\- *lemma* lipschitz_with.neg
- \+/\- *lemma* lipschitz_with.sub
- \+/\- *lemma* lipschitz_with_iff_norm_sub_le
- \+/\- *lemma* lipschitz_with_one_norm
- \+/\- *lemma* mem_ball_iff_norm'
- \+/\- *lemma* mem_ball_iff_norm
- \+/\- *lemma* mem_ball_zero_iff
- \+/\- *lemma* mem_closed_ball_iff_norm'
- \+/\- *lemma* mem_closed_ball_iff_norm
- \+/\- *lemma* mem_emetric_ball_zero_iff
- \+/\- *lemma* mem_sphere_iff_norm
- \+/\- *lemma* mem_sphere_zero_iff_norm
- \+/\- *lemma* nat.norm_cast_le
- \+/\- *lemma* ne_zero_of_norm_pos
- \+/\- *lemma* nndist_add_add_le
- \+/\- *lemma* nndist_eq_nnnorm
- \+/\- *lemma* nndist_nnnorm_nnnorm_le
- \+/\- *lemma* nnnorm_add_le
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* nnnorm_neg
- \+/\- *lemma* nnnorm_sum_le
- \+/\- *lemma* nnnorm_zero
- \+/\- *lemma* nonzero_of_mem_sphere
- \+/\- *lemma* nonzero_of_mem_unit_sphere
- \+/\- *lemma* norm_add_le
- \+/\- *lemma* norm_add_le_of_le
- \+/\- *lemma* norm_eq_of_mem_sphere
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_eq_zero_iff'
- \+/\- *lemma* norm_fst_le
- \+/\- *lemma* norm_le_insert'
- \+/\- *lemma* norm_le_insert
- \+/\- *lemma* norm_le_norm_add_const_of_dist_le
- \+/\- *lemma* norm_le_of_mem_closed_ball
- \+/\- *lemma* norm_le_zero_iff'
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_lt_norm_add_const_of_dist_lt
- \+/\- *lemma* norm_lt_of_mem_ball
- \+/\- *lemma* norm_neg
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* norm_of_subsingleton
- \+/\- *lemma* norm_pos_iff'
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_prod_le_iff
- \+/\- *lemma* norm_snd_le
- \+/\- *lemma* norm_sub_eq_zero_iff
- \+/\- *lemma* norm_sub_le
- \+/\- *lemma* norm_sub_le_of_le
- \+/\- *lemma* norm_sub_norm_le
- \+/\- *lemma* norm_sub_rev
- \+/\- *lemma* norm_sum_le
- \+/\- *lemma* norm_sum_le_of_le
- \+/\- *lemma* norm_zero
- \+/\- *lemma* normed_group.cauchy_seq_iff
- \+/\- *lemma* normed_group.core.to_semi_normed_group.core
- \+/\- *structure* normed_group.core
- \+/\- *def* normed_group.induced
- \+/\- *def* normed_group.of_add_dist
- \+/\- *lemma* normed_group.tendsto_nhds_nhds
- \+/\- *theorem* normed_group.tendsto_nhds_zero
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* pi_nnnorm_const
- \+/\- *lemma* pi_nnsemi_norm_const
- \+/\- *lemma* pi_norm_const
- \+/\- *lemma* pi_semi_norm_const
- \+/\- *lemma* preimage_add_ball
- \+/\- *lemma* preimage_add_closed_ball
- \+/\- *lemma* preimage_add_sphere
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* prod.nnsemi_norm_def
- \+/\- *lemma* prod.norm_def
- \+/\- *lemma* prod.semi_norm_def
- \+/\- *lemma* semi_norm_fst_le
- \+/\- *lemma* semi_norm_prod_le_iff
- \+/\- *lemma* semi_norm_snd_le
- \+/\- *structure* semi_normed_group.core
- \+/\- *def* semi_normed_group.induced
- \+/\- *lemma* semi_normed_group.mem_closure_iff
- \+/\- *def* semi_normed_group.of_add_dist'
- \+/\- *def* semi_normed_group.of_add_dist
- \+/\- *lemma* squeeze_zero_norm'
- \+/\- *lemma* squeeze_zero_norm
- \+/\- *lemma* tendsto_iff_norm_tendsto_zero
- \+/\- *lemma* tendsto_norm
- \+/\- *lemma* tendsto_norm_cocompact_at_top
- \+/\- *lemma* tendsto_norm_nhds_within_zero
- \+/\- *lemma* tendsto_norm_sub_self
- \+/\- *lemma* tendsto_norm_zero
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+/\- *lemma* uniform_continuous_nnnorm
- \+/\- *lemma* uniform_continuous_norm

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.edist_lt_top
- \+ *lemma* antilipschitz_with.edist_ne_top

Modified src/topology/metric_space/basic.lean
- \+/\- *def* pseudo_emetric_space.to_pseudo_metric_space



## [2021-10-11 04:03:51](https://github.com/leanprover-community/mathlib/commit/11117ec)
feat(topology/G_delta): a finite set is a Gδ-set ([#9644](https://github.com/leanprover-community/mathlib/pull/9644))
#### Estimated changes
Modified src/topology/G_delta.lean
- \+ *lemma* is_Gδ_empty
- \+ *lemma* is_Gδ_singleton
- \+ *lemma* set.finite.is_Gδ

Modified src/topology/separation.lean
- \+ *lemma* bInter_basis_nhds



## [2021-10-11 04:03:50](https://github.com/leanprover-community/mathlib/commit/c02a655)
feat(linear_algebra/affine_space/barycentric_coords): we can recover a point from its barycentric coordinates ([#9629](https://github.com/leanprover-community/mathlib/pull/9629))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* affine_combination_barycentric_coord_eq_self
- \+ *lemma* sum_barycentric_coord_apply_eq_one

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* eq_affine_combination_of_mem_affine_span_of_fintype



## [2021-10-11 04:03:49](https://github.com/leanprover-community/mathlib/commit/0bd14ba)
feat(category_theory/limits/lattice): Add explicit formulas for limits in lattices ([#9608](https://github.com/leanprover-community/mathlib/pull/9608))
Add explicit descriptions of finite limits and colimits in complete lattices. In particular, the product and the pullback is equal to the infimum, while coproduct and pushout is the supremum. Furthermore, `limit_iso_infi` can be strengthened to an equality, as preorder categories are skeletal.
#### Estimated changes
Modified src/category_theory/limits/lattice.lean
- \+/\- *def* category_theory.limits.complete_lattice.colimit_cocone
- \+ *lemma* category_theory.limits.complete_lattice.colimit_eq_supr
- \- *def* category_theory.limits.complete_lattice.colimit_iso_supr
- \- *lemma* category_theory.limits.complete_lattice.colimit_iso_supr_hom
- \- *lemma* category_theory.limits.complete_lattice.colimit_iso_supr_inv
- \+ *lemma* category_theory.limits.complete_lattice.coprod_eq_sup
- \+ *def* category_theory.limits.complete_lattice.finite_colimit_cocone
- \+ *lemma* category_theory.limits.complete_lattice.finite_colimit_eq_finset_univ_sup
- \+ *lemma* category_theory.limits.complete_lattice.finite_coproduct_eq_finset_sup
- \+ *def* category_theory.limits.complete_lattice.finite_limit_cone
- \+ *lemma* category_theory.limits.complete_lattice.finite_limit_eq_finset_univ_inf
- \+ *lemma* category_theory.limits.complete_lattice.finite_product_eq_finset_inf
- \+/\- *def* category_theory.limits.complete_lattice.limit_cone
- \+ *lemma* category_theory.limits.complete_lattice.limit_eq_infi
- \- *def* category_theory.limits.complete_lattice.limit_iso_infi
- \- *lemma* category_theory.limits.complete_lattice.limit_iso_infi_hom
- \- *lemma* category_theory.limits.complete_lattice.limit_iso_infi_inv
- \+ *lemma* category_theory.limits.complete_lattice.prod_eq_inf
- \+ *lemma* category_theory.limits.complete_lattice.pullback_eq_inf
- \+ *lemma* category_theory.limits.complete_lattice.pushout_eq_sup



## [2021-10-11 04:03:48](https://github.com/leanprover-community/mathlib/commit/c803c8d)
feat(algebra/gcd_monoid): trivial `gcd` on `comm_group_with_zero`s ([#9602](https://github.com/leanprover-community/mathlib/pull/9602))
This PR extends the `normalization_monoid` defined on `comm_group_with_zero`s (e.g. fields) to a `normalized_gcd_monoid`. This is useful if you need to take the gcd of two polynomials in a field.
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* comm_group_with_zero.coe_norm_unit
- \+ *lemma* comm_group_with_zero.normalize_eq_one

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* ufm_of_gcd_of_wf_dvd_monoid



## [2021-10-11 04:03:47](https://github.com/leanprover-community/mathlib/commit/ec5835d)
chore(order/*): use to_dual and of_dual in statements instead of implicit coercions between and `α` and  `order_dual α`  ([#9593](https://github.com/leanprover-community/mathlib/pull/9593))
Previously the meaning of the statement was hidden away in an invisible surprising typeclass argument.
Before this change, the docs suggested the nonsensical statement that `monotone f` implies `antitone f`!
![image](https://user-images.githubusercontent.com/425260/136348562-d3ecbb85-2a54-4c13-adda-806eb150b00a.png)
Most of the proof changes in this PR are a consequence of changing the interval lemmas, not the monotonicity or convexity ones.
#### Estimated changes
Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on.dual
- \+/\- *lemma* convex_on.dual
- \+/\- *lemma* strict_concave_on.dual
- \+/\- *lemma* strict_convex_on.dual

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.dual_Icc
- \+/\- *lemma* set.dual_Ici
- \+/\- *lemma* set.dual_Ico
- \+/\- *lemma* set.dual_Iic
- \+/\- *lemma* set.dual_Iio
- \+/\- *lemma* set.dual_Ioc
- \+/\- *lemma* set.dual_Ioi
- \+/\- *lemma* set.dual_Ioo

Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/ord_connected.lean
- \+/\- *lemma* set.ord_connected.dual
- \+/\- *lemma* set.ord_connected_dual

Modified src/data/set/intervals/surj_on.lean


Modified src/order/bounded_lattice.lean
- \+/\- *lemma* is_compl.to_order_dual

Modified src/order/bounds.lean


Modified src/order/filter/extr.lean
- \+/\- *lemma* is_extr_filter_dual_iff
- \+/\- *lemma* is_extr_on_dual_iff
- \+/\- *lemma* is_max_filter_dual_iff
- \+/\- *lemma* is_max_on_dual_iff
- \+/\- *lemma* is_min_filter_dual_iff
- \+/\- *lemma* is_min_on_dual_iff

Modified src/order/monotone.lean


Modified src/order/order_dual.lean


Modified src/set_theory/zfc.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/opens.lean
- \+/\- *def* topological_space.opens.gi

Modified src/topology/subset_properties.lean




## [2021-10-11 04:03:45](https://github.com/leanprover-community/mathlib/commit/ef46da8)
feat(category_theory/*): Curried yoneda lemma ([#9579](https://github.com/leanprover-community/mathlib/pull/9579))
Provided curried versions of the Yoneda lemma when the category is small.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* category_theory.cartesian_closed.curry_eq
- \+ *lemma* category_theory.cartesian_closed.curry_eq_iff
- \+ *lemma* category_theory.cartesian_closed.curry_id_eq_coev
- \+ *lemma* category_theory.cartesian_closed.curry_injective
- \+ *lemma* category_theory.cartesian_closed.curry_natural_left
- \+ *lemma* category_theory.cartesian_closed.curry_natural_right
- \+ *lemma* category_theory.cartesian_closed.curry_uncurry
- \+ *lemma* category_theory.cartesian_closed.eq_curry_iff
- \+ *lemma* category_theory.cartesian_closed.uncurry_curry
- \+ *lemma* category_theory.cartesian_closed.uncurry_eq
- \+ *lemma* category_theory.cartesian_closed.uncurry_id_eq_ev
- \+ *lemma* category_theory.cartesian_closed.uncurry_injective
- \+ *lemma* category_theory.cartesian_closed.uncurry_natural_left
- \+ *lemma* category_theory.cartesian_closed.uncurry_natural_right
- \- *lemma* category_theory.curry_eq
- \- *lemma* category_theory.curry_eq_iff
- \- *lemma* category_theory.curry_id_eq_coev
- \- *lemma* category_theory.curry_injective
- \- *lemma* category_theory.curry_natural_left
- \- *lemma* category_theory.curry_natural_right
- \- *lemma* category_theory.curry_uncurry
- \- *lemma* category_theory.eq_curry_iff
- \- *lemma* category_theory.uncurry_curry
- \- *lemma* category_theory.uncurry_eq
- \- *lemma* category_theory.uncurry_id_eq_ev
- \- *lemma* category_theory.uncurry_injective
- \- *lemma* category_theory.uncurry_natural_left
- \- *lemma* category_theory.uncurry_natural_right

Modified src/category_theory/closed/functor.lean


Modified src/category_theory/closed/ideal.lean


Modified src/category_theory/types.lean
- \+ *def* category_theory.ulift_functor_trivial

Modified src/category_theory/yoneda.lean
- \+ *def* category_theory.curried_yoneda_lemma'
- \+ *def* category_theory.curried_yoneda_lemma



## [2021-10-11 02:26:38](https://github.com/leanprover-community/mathlib/commit/e32154d)
feat(data/equiv/ring): add basic API lemmas for ring_equiv ([#9639](https://github.com/leanprover-community/mathlib/pull/9639))
This PR adds the lemmas `map_inv`, `map_div`, `map_pow` and `map_fpow` for `ring_equiv`. These lemmas were already available for `ring_hom`s. I'm very open to suggestions about where they should go; `map_fpow` in particular requires a new import in `algebra/field_power.lean`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* ring_equiv.map_fpow

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.map_div
- \+ *lemma* ring_equiv.map_inv
- \+ *lemma* ring_equiv.map_pow



## [2021-10-10 21:07:28](https://github.com/leanprover-community/mathlib/commit/64255e2)
chore(analysis): move some code to `analysis.normed.group.basic` ([#9642](https://github.com/leanprover-community/mathlib/pull/9642))
#### Estimated changes
Added src/analysis/normed/group/basic.lean
- \+ *lemma* abs_dist_sub_le_dist_add_add
- \+ *lemma* abs_norm_sub_norm_le
- \+ *lemma* add_mem_ball_iff_norm
- \+ *lemma* add_mem_closed_ball_iff_norm
- \+ *lemma* add_monoid_hom.continuous_of_bound
- \+ *lemma* add_monoid_hom.isometry_iff_norm
- \+ *lemma* add_monoid_hom.isometry_of_norm
- \+ *lemma* add_monoid_hom.lipschitz_of_bound
- \+ *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+ *lemma* antilipschitz_with.add_lipschitz_with
- \+ *lemma* antilipschitz_with.add_sub_lipschitz_with
- \+ *lemma* ball_zero_eq
- \+ *lemma* bounded_iff_forall_norm_le
- \+ *lemma* cauchy_seq.add
- \+ *lemma* cauchy_seq_sum_of_eventually_eq
- \+ *lemma* coe_neg_sphere
- \+ *lemma* coe_nnnorm
- \+ *lemma* coe_norm_subgroup
- \+ *lemma* continuous.nnnorm
- \+ *lemma* continuous.norm
- \+ *lemma* continuous_at.nnnorm
- \+ *lemma* continuous_at.norm
- \+ *lemma* continuous_nnnorm
- \+ *lemma* continuous_norm
- \+ *lemma* continuous_on.nnnorm
- \+ *lemma* continuous_on.norm
- \+ *lemma* continuous_within_at.nnnorm
- \+ *lemma* continuous_within_at.norm
- \+ *lemma* controlled_sum_of_mem_closure
- \+ *lemma* controlled_sum_of_mem_closure_range
- \+ *lemma* dist_add_add_le
- \+ *lemma* dist_add_add_le_of_le
- \+ *lemma* dist_add_left
- \+ *lemma* dist_add_right
- \+ *lemma* dist_eq_norm'
- \+ *lemma* dist_eq_norm
- \+ *lemma* dist_le_norm_add_norm
- \+ *lemma* dist_neg_neg
- \+ *lemma* dist_norm_norm_le
- \+ *lemma* dist_sub_left
- \+ *lemma* dist_sub_right
- \+ *lemma* dist_sub_sub_le
- \+ *lemma* dist_sub_sub_le_of_le
- \+ *lemma* dist_sum_sum_le
- \+ *lemma* dist_sum_sum_le_of_le
- \+ *lemma* dist_zero_left
- \+ *lemma* dist_zero_right
- \+ *lemma* edist_add_add_le
- \+ *lemma* edist_eq_coe_nnnorm
- \+ *lemma* edist_eq_coe_nnnorm_sub
- \+ *lemma* eq_of_norm_sub_eq_zero
- \+ *lemma* eq_of_norm_sub_le_zero
- \+ *lemma* eventually_ne_of_tendsto_norm_at_top
- \+ *lemma* filter.tendsto.nnnorm
- \+ *lemma* filter.tendsto.norm
- \+ *lemma* is_bounded_under_of_tendsto
- \+ *lemma* is_compact.exists_bound_of_continuous_on
- \+ *lemma* isometric.add_left_symm
- \+ *lemma* isometric.add_left_to_equiv
- \+ *lemma* isometric.add_right_apply
- \+ *lemma* isometric.add_right_symm
- \+ *lemma* isometric.add_right_to_equiv
- \+ *lemma* isometric.coe_add_left
- \+ *lemma* isometric.coe_add_right
- \+ *lemma* isometric.coe_neg
- \+ *lemma* isometric.neg_symm
- \+ *lemma* isometric.neg_to_equiv
- \+ *lemma* lipschitz_on_with.norm_sub_le
- \+ *lemma* lipschitz_on_with_iff_norm_sub_le
- \+ *lemma* lipschitz_with.add
- \+ *lemma* lipschitz_with.neg
- \+ *lemma* lipschitz_with.sub
- \+ *lemma* lipschitz_with_iff_norm_sub_le
- \+ *lemma* lipschitz_with_one_norm
- \+ *lemma* mem_ball_iff_norm'
- \+ *lemma* mem_ball_iff_norm
- \+ *lemma* mem_ball_zero_iff
- \+ *lemma* mem_closed_ball_iff_norm'
- \+ *lemma* mem_closed_ball_iff_norm
- \+ *lemma* mem_emetric_ball_zero_iff
- \+ *lemma* mem_sphere_iff_norm
- \+ *lemma* mem_sphere_zero_iff_norm
- \+ *lemma* nat.norm_cast_le
- \+ *lemma* ne_zero_of_norm_pos
- \+ *lemma* nndist_add_add_le
- \+ *lemma* nndist_eq_nnnorm
- \+ *lemma* nndist_nnnorm_nnnorm_le
- \+ *lemma* nnnorm_add_le
- \+ *lemma* nnnorm_eq_zero
- \+ *lemma* nnnorm_neg
- \+ *lemma* nnnorm_sum_le
- \+ *lemma* nnnorm_zero
- \+ *lemma* nonzero_of_mem_sphere
- \+ *lemma* nonzero_of_mem_unit_sphere
- \+ *lemma* norm_add_le
- \+ *lemma* norm_add_le_of_le
- \+ *lemma* norm_eq_of_mem_sphere
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_eq_zero_iff'
- \+ *lemma* norm_fst_le
- \+ *lemma* norm_le_insert'
- \+ *lemma* norm_le_insert
- \+ *lemma* norm_le_norm_add_const_of_dist_le
- \+ *lemma* norm_le_of_mem_closed_ball
- \+ *lemma* norm_le_pi_norm
- \+ *lemma* norm_le_zero_iff'
- \+ *lemma* norm_le_zero_iff
- \+ *lemma* norm_lt_norm_add_const_of_dist_lt
- \+ *lemma* norm_lt_of_mem_ball
- \+ *lemma* norm_neg
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_of_subsingleton
- \+ *lemma* norm_pos_iff'
- \+ *lemma* norm_pos_iff
- \+ *lemma* norm_prod_le_iff
- \+ *lemma* norm_snd_le
- \+ *lemma* norm_sub_eq_zero_iff
- \+ *lemma* norm_sub_le
- \+ *lemma* norm_sub_le_of_le
- \+ *lemma* norm_sub_norm_le
- \+ *lemma* norm_sub_rev
- \+ *lemma* norm_sum_le
- \+ *lemma* norm_sum_le_of_le
- \+ *lemma* norm_zero
- \+ *lemma* normed_group.cauchy_seq_iff
- \+ *lemma* normed_group.core.to_semi_normed_group.core
- \+ *structure* normed_group.core
- \+ *def* normed_group.induced
- \+ *def* normed_group.of_add_dist
- \+ *lemma* normed_group.tendsto_nhds_nhds
- \+ *theorem* normed_group.tendsto_nhds_zero
- \+ *lemma* of_real_norm_eq_coe_nnnorm
- \+ *lemma* pi_nnnorm_const
- \+ *lemma* pi_nnsemi_norm_const
- \+ *lemma* pi_norm_const
- \+ *lemma* pi_norm_le_iff
- \+ *lemma* pi_norm_lt_iff
- \+ *lemma* pi_semi_norm_const
- \+ *lemma* pi_semi_norm_le_iff
- \+ *lemma* pi_semi_norm_lt_iff
- \+ *lemma* preimage_add_ball
- \+ *lemma* preimage_add_closed_ball
- \+ *lemma* preimage_add_sphere
- \+ *lemma* prod.nnnorm_def
- \+ *lemma* prod.nnsemi_norm_def
- \+ *lemma* prod.norm_def
- \+ *lemma* prod.semi_norm_def
- \+ *lemma* punit.norm_eq_zero
- \+ *lemma* real.norm_eq_abs
- \+ *lemma* semi_norm_fst_le
- \+ *lemma* semi_norm_le_pi_norm
- \+ *lemma* semi_norm_prod_le_iff
- \+ *lemma* semi_norm_snd_le
- \+ *structure* semi_normed_group.core
- \+ *def* semi_normed_group.induced
- \+ *lemma* semi_normed_group.mem_closure_iff
- \+ *def* semi_normed_group.of_add_dist'
- \+ *def* semi_normed_group.of_add_dist
- \+ *lemma* squeeze_zero_norm'
- \+ *lemma* squeeze_zero_norm
- \+ *lemma* submodule.norm_coe
- \+ *lemma* submodule.norm_mk
- \+ *lemma* tendsto_iff_norm_tendsto_zero
- \+ *lemma* tendsto_norm
- \+ *lemma* tendsto_norm_cocompact_at_top
- \+ *lemma* tendsto_norm_nhds_within_zero
- \+ *lemma* tendsto_norm_sub_self
- \+ *lemma* tendsto_norm_zero
- \+ *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+ *lemma* uniform_continuous_nnnorm
- \+ *lemma* uniform_continuous_norm

Modified src/analysis/normed_space/basic.lean
- \- *lemma* abs_dist_sub_le_dist_add_add
- \- *lemma* abs_norm_sub_norm_le
- \- *lemma* add_mem_ball_iff_norm
- \- *lemma* add_mem_closed_ball_iff_norm
- \- *lemma* add_monoid_hom.continuous_of_bound
- \- *lemma* add_monoid_hom.isometry_iff_norm
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* add_monoid_hom.lipschitz_of_bound
- \- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \- *lemma* antilipschitz_with.add_lipschitz_with
- \- *lemma* antilipschitz_with.add_sub_lipschitz_with
- \- *lemma* ball_zero_eq
- \- *lemma* bounded_iff_forall_norm_le
- \- *lemma* cauchy_seq.add
- \- *lemma* cauchy_seq_sum_of_eventually_eq
- \- *lemma* coe_neg_sphere
- \- *lemma* coe_nnnorm
- \- *lemma* coe_norm_subgroup
- \- *lemma* continuous.nnnorm
- \- *lemma* continuous.norm
- \- *lemma* continuous_at.nnnorm
- \- *lemma* continuous_at.norm
- \- *lemma* continuous_nnnorm
- \- *lemma* continuous_norm
- \- *lemma* continuous_on.nnnorm
- \- *lemma* continuous_on.norm
- \- *lemma* continuous_within_at.nnnorm
- \- *lemma* continuous_within_at.norm
- \- *lemma* controlled_sum_of_mem_closure
- \- *lemma* controlled_sum_of_mem_closure_range
- \- *lemma* dist_add_add_le
- \- *lemma* dist_add_add_le_of_le
- \- *lemma* dist_add_left
- \- *lemma* dist_add_right
- \- *lemma* dist_eq_norm'
- \- *lemma* dist_eq_norm
- \- *lemma* dist_le_norm_add_norm
- \- *lemma* dist_neg_neg
- \- *lemma* dist_norm_norm_le
- \- *lemma* dist_sub_left
- \- *lemma* dist_sub_right
- \- *lemma* dist_sub_sub_le
- \- *lemma* dist_sub_sub_le_of_le
- \- *lemma* dist_sum_sum_le
- \- *lemma* dist_sum_sum_le_of_le
- \- *lemma* dist_zero_left
- \- *lemma* dist_zero_right
- \- *lemma* edist_add_add_le
- \- *lemma* edist_eq_coe_nnnorm
- \- *lemma* edist_eq_coe_nnnorm_sub
- \- *lemma* eq_of_norm_sub_eq_zero
- \- *lemma* eq_of_norm_sub_le_zero
- \- *lemma* eventually_ne_of_tendsto_norm_at_top
- \- *lemma* filter.tendsto.nnnorm
- \- *lemma* filter.tendsto.norm
- \- *lemma* is_bounded_under_of_tendsto
- \- *lemma* is_compact.exists_bound_of_continuous_on
- \- *lemma* isometric.add_left_symm
- \- *lemma* isometric.add_left_to_equiv
- \- *lemma* isometric.add_right_apply
- \- *lemma* isometric.add_right_symm
- \- *lemma* isometric.add_right_to_equiv
- \- *lemma* isometric.coe_add_left
- \- *lemma* isometric.coe_add_right
- \- *lemma* isometric.coe_neg
- \- *lemma* isometric.neg_symm
- \- *lemma* isometric.neg_to_equiv
- \- *lemma* lipschitz_on_with.norm_sub_le
- \- *lemma* lipschitz_on_with_iff_norm_sub_le
- \- *lemma* lipschitz_with.add
- \- *lemma* lipschitz_with.neg
- \- *lemma* lipschitz_with.sub
- \- *lemma* lipschitz_with_iff_norm_sub_le
- \- *lemma* lipschitz_with_one_norm
- \- *lemma* mem_ball_iff_norm'
- \- *lemma* mem_ball_iff_norm
- \- *lemma* mem_ball_zero_iff
- \- *lemma* mem_closed_ball_iff_norm'
- \- *lemma* mem_closed_ball_iff_norm
- \- *lemma* mem_emetric_ball_zero_iff
- \- *lemma* mem_sphere_iff_norm
- \- *lemma* mem_sphere_zero_iff_norm
- \- *lemma* nat.norm_cast_le
- \- *lemma* ne_zero_of_norm_pos
- \- *lemma* nndist_add_add_le
- \- *lemma* nndist_eq_nnnorm
- \- *lemma* nndist_nnnorm_nnnorm_le
- \- *lemma* nnnorm_add_le
- \- *lemma* nnnorm_eq_zero
- \- *lemma* nnnorm_neg
- \- *lemma* nnnorm_sum_le
- \- *lemma* nnnorm_zero
- \- *lemma* nonzero_of_mem_sphere
- \- *lemma* nonzero_of_mem_unit_sphere
- \- *lemma* norm_add_le
- \- *lemma* norm_add_le_of_le
- \- *lemma* norm_eq_of_mem_sphere
- \- *lemma* norm_eq_zero
- \- *lemma* norm_eq_zero_iff'
- \- *lemma* norm_fst_le
- \- *lemma* norm_le_insert'
- \- *lemma* norm_le_insert
- \- *lemma* norm_le_norm_add_const_of_dist_le
- \- *lemma* norm_le_of_mem_closed_ball
- \- *lemma* norm_le_pi_norm
- \- *lemma* norm_le_zero_iff'
- \- *lemma* norm_le_zero_iff
- \- *lemma* norm_lt_norm_add_const_of_dist_lt
- \- *lemma* norm_lt_of_mem_ball
- \- *lemma* norm_neg
- \- *lemma* norm_nonneg
- \- *lemma* norm_of_subsingleton
- \- *lemma* norm_pos_iff'
- \- *lemma* norm_pos_iff
- \- *lemma* norm_prod_le_iff
- \- *lemma* norm_snd_le
- \- *lemma* norm_sub_eq_zero_iff
- \- *lemma* norm_sub_le
- \- *lemma* norm_sub_le_of_le
- \- *lemma* norm_sub_norm_le
- \- *lemma* norm_sub_rev
- \- *lemma* norm_sum_le
- \- *lemma* norm_sum_le_of_le
- \- *lemma* norm_zero
- \- *lemma* normed_group.cauchy_seq_iff
- \- *lemma* normed_group.core.to_semi_normed_group.core
- \- *structure* normed_group.core
- \- *def* normed_group.induced
- \- *def* normed_group.of_add_dist
- \- *lemma* normed_group.tendsto_nhds_nhds
- \- *theorem* normed_group.tendsto_nhds_zero
- \- *lemma* of_real_norm_eq_coe_nnnorm
- \- *lemma* pi_nnnorm_const
- \- *lemma* pi_nnsemi_norm_const
- \- *lemma* pi_norm_const
- \- *lemma* pi_norm_le_iff
- \- *lemma* pi_norm_lt_iff
- \- *lemma* pi_semi_norm_const
- \- *lemma* pi_semi_norm_le_iff
- \- *lemma* pi_semi_norm_lt_iff
- \- *lemma* preimage_add_ball
- \- *lemma* preimage_add_closed_ball
- \- *lemma* preimage_add_sphere
- \- *lemma* prod.nnnorm_def
- \- *lemma* prod.nnsemi_norm_def
- \- *lemma* prod.norm_def
- \- *lemma* prod.semi_norm_def
- \- *lemma* punit.norm_eq_zero
- \- *lemma* real.norm_eq_abs
- \- *lemma* semi_norm_fst_le
- \- *lemma* semi_norm_le_pi_norm
- \- *lemma* semi_norm_prod_le_iff
- \- *lemma* semi_norm_snd_le
- \- *structure* semi_normed_group.core
- \- *def* semi_normed_group.induced
- \- *lemma* semi_normed_group.mem_closure_iff
- \- *def* semi_normed_group.of_add_dist'
- \- *def* semi_normed_group.of_add_dist
- \- *lemma* squeeze_zero_norm'
- \- *lemma* squeeze_zero_norm
- \- *lemma* submodule.norm_coe
- \- *lemma* submodule.norm_mk
- \- *lemma* tendsto_iff_norm_tendsto_zero
- \- *lemma* tendsto_norm
- \- *lemma* tendsto_norm_cocompact_at_top
- \- *lemma* tendsto_norm_nhds_within_zero
- \- *lemma* tendsto_norm_sub_self
- \- *lemma* tendsto_norm_zero
- \- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \- *lemma* uniform_continuous_nnnorm
- \- *lemma* uniform_continuous_norm



## [2021-10-10 21:07:27](https://github.com/leanprover-community/mathlib/commit/fa41436)
feat(algebra/*,group_theory/*): instances/lemmas about `is_scalar_tower` and `smul_comm_class` ([#9533](https://github.com/leanprover-community/mathlib/pull/9533))
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/group/prod.lean
- \+ *lemma* prod.mul_def

Modified src/algebra/module/basic.lean


Modified src/algebra/opposites.lean
- \+/\- *lemma* opposite.op_smul_eq_mul

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* is_scalar_tower.of_smul_one_mul
- \+ *lemma* mul_smul_one
- \+ *lemma* smul_comm_class.of_mul_smul_one
- \+ *lemma* smul_one_mul

Modified src/group_theory/group_action/prod.lean
- \+ *theorem* prod.smul_def



## [2021-10-10 18:58:39](https://github.com/leanprover-community/mathlib/commit/0bba837)
chore(data/nat/factorial): use `n + 1` instead of `n.succ` in `nat.factorial_succ` ([#9645](https://github.com/leanprover-community/mathlib/pull/9645))
#### Estimated changes
Modified src/data/nat/choose/basic.lean


Modified src/data/nat/factorial/basic.lean
- \+/\- *theorem* nat.factorial_succ

Modified src/number_theory/liouville/liouville_constant.lean




## [2021-10-10 09:54:18](https://github.com/leanprover-community/mathlib/commit/3d438ba)
feat(probability_theory/density): add continuous uniform distribution ([#9385](https://github.com/leanprover-community/mathlib/pull/9385))
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_eq_one_iff

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* set.mul_indicator_ae_eq_one

Modified src/probability_theory/density.lean
- \+ *lemma* measure_theory.has_pdf_of_pdf_ne_zero
- \+ *lemma* measure_theory.pdf.is_uniform.has_pdf
- \+ *lemma* measure_theory.pdf.is_uniform.integral_eq
- \+ *lemma* measure_theory.pdf.is_uniform.mul_pdf_integrable
- \+ *lemma* measure_theory.pdf.is_uniform.pdf_to_real_ae_eq
- \+ *def* measure_theory.pdf.is_uniform



## [2021-10-09 16:48:06](https://github.com/leanprover-community/mathlib/commit/54a4c17)
feat(group_theory/sylow): `set_like` instance for `sylow` ([#9641](https://github.com/leanprover-community/mathlib/pull/9641))
Adds a `set_like` instance for `sylow p G`.
Coauthored by @jcommelin
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.ext
- \+/\- *lemma* sylow.ext_iff
- \+/\- *lemma* sylow.to_subgroup_eq_coe



## [2021-10-09 14:56:51](https://github.com/leanprover-community/mathlib/commit/bb98444)
refactor(group_theory/congruence): remove old_structure_cmd ([#9622](https://github.com/leanprover-community/mathlib/pull/9622))
#### Estimated changes
Modified src/group_theory/congruence.lean
- \+/\- *lemma* con.Inf_def
- \+/\- *lemma* con.Sup_def
- \- *lemma* con.coe_eq
- \+/\- *theorem* con.con_gen_le
- \+/\- *lemma* con.rel_mk



## [2021-10-09 09:53:15](https://github.com/leanprover-community/mathlib/commit/7ed091d)
feat(group_theory/perm/concrete_cycle): computable cyclic perm notation ([#9470](https://github.com/leanprover-community/mathlib/pull/9470))
#### Estimated changes
Modified src/group_theory/perm/concrete_cycle.lean
- \+ *lemma* equiv.perm.is_cycle.exists_unique_cycle_nontrivial_subtype
- \+ *def* equiv.perm.iso_cycle'
- \+ *def* equiv.perm.iso_cycle
- \+ *lemma* equiv.perm.nodup_to_cycle
- \+ *lemma* equiv.perm.nontrivial_to_cycle
- \+ *def* equiv.perm.to_cycle
- \+ *lemma* equiv.perm.to_cycle_eq_to_list



## [2021-10-09 07:26:30](https://github.com/leanprover-community/mathlib/commit/ce50450)
chore(analysis/normed_space/linear_isometry): adjust `isometry` API ([#9635](https://github.com/leanprover-community/mathlib/pull/9635))
Now that we have the `linear_isometry` definition, it is better to pass through this definition rather then using a `linear_map` satisfying the `isometry` hypothesis.  To this end, convert old lemma `linear_map.norm_apply_of_isometry` to a new definition `linear_map.to_linear_isometry`, and delete old definition `continuous_linear_equiv.of_isometry`, whose use should be replaced by the pair of definitions`linear_map.to_linear_isometry`, `linear_isometry_equiv.of_surjective`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *def* continuous_linear_equiv.of_isometry
- \- *lemma* linear_map.norm_apply_of_isometry

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *def* linear_map.to_linear_isometry

Modified src/analysis/normed_space/operator_norm.lean




## [2021-10-09 07:26:28](https://github.com/leanprover-community/mathlib/commit/a9643aa)
feat(order/min_max): min_cases and max_cases lemmata ([#9632](https://github.com/leanprover-community/mathlib/pull/9632))
These lemmata make the following type of argument work seamlessly:
```lean
example (h1 : 0 ≤ x) (h2 : x ≤ 1) : min 1 x ≤ max x 0 := by cases min_cases 1 x; cases max_cases x 0; linarith
```
See similar PR [#8124](https://github.com/leanprover-community/mathlib/pull/8124)
#### Estimated changes
Modified src/order/min_max.lean
- \+ *lemma* max_cases
- \+ *lemma* min_cases



## [2021-10-09 07:26:25](https://github.com/leanprover-community/mathlib/commit/e0f80e7)
feat(analysis/convex/quasiconvex): Quasiconvexity of functions ([#9561](https://github.com/leanprover-community/mathlib/pull/9561))
A function is quasiconvex iff all its sublevels are convex. This generalizes unimodality to non-ordered spaces.
#### Estimated changes
Added src/analysis/convex/quasiconvex.lean
- \+ *lemma* antitone.quasiconcave_on
- \+ *lemma* antitone.quasiconvex_on
- \+ *lemma* antitone.quasilinear_on
- \+ *lemma* antitone_on.quasiconcave_on
- \+ *lemma* antitone_on.quasiconvex_on
- \+ *lemma* antitone_on.quasilinear_on
- \+ *lemma* concave_on.quasiconcave_on
- \+ *lemma* convex.quasiconcave_on_of_convex_ge
- \+ *lemma* convex.quasiconvex_on_of_convex_le
- \+ *lemma* convex_on.quasiconvex_on
- \+ *lemma* monotone.quasiconcave_on
- \+ *lemma* monotone.quasiconvex_on
- \+ *lemma* monotone.quasilinear_on
- \+ *lemma* monotone_on.quasiconcave_on
- \+ *lemma* monotone_on.quasiconvex_on
- \+ *lemma* monotone_on.quasilinear_on
- \+ *lemma* quasiconcave_on.convex
- \+ *lemma* quasiconcave_on.convex_gt
- \+ *lemma* quasiconcave_on.dual
- \+ *lemma* quasiconcave_on.inf
- \+ *def* quasiconcave_on
- \+ *lemma* quasiconcave_on_iff_min_le
- \+ *lemma* quasiconvex_on.convex
- \+ *lemma* quasiconvex_on.convex_lt
- \+ *lemma* quasiconvex_on.dual
- \+ *lemma* quasiconvex_on.sup
- \+ *def* quasiconvex_on
- \+ *lemma* quasiconvex_on_iff_le_max
- \+ *lemma* quasilinear_on.dual
- \+ *def* quasilinear_on
- \+ *lemma* quasilinear_on_iff_mem_interval

Modified src/data/set/basic.lean
- \+ *lemma* set.sep_inter_sep



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
Modified archive/oxford_invariants/2021summer/week3_p1.lean


Modified src/algebra/order/sub.lean
- \+ *lemma* sub_eq_of_eq_add_rev

Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean
- \- *lemma* nat.add_sub_sub_cancel
- \- *theorem* nat.sub_le_left_iff_le_add
- \- *theorem* nat.sub_le_right_iff_le_add

Modified src/data/nat/choose/basic.lean


Modified src/data/nat/sqrt.lean


Modified src/data/polynomial/hasse_deriv.lean


Modified src/data/polynomial/ring_division.lean


Modified src/order/jordan_holder.lean


Modified src/ring_theory/witt_vector/frobenius.lean




## [2021-10-09 02:44:04](https://github.com/leanprover-community/mathlib/commit/7aaa1b4)
chore(scripts): update nolints.txt ([#9636](https://github.com/leanprover-community/mathlib/pull/9636))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-10-08 21:56:11](https://github.com/leanprover-community/mathlib/commit/7e3fa4c)
chore(*): fix typos ([#9634](https://github.com/leanprover-community/mathlib/pull/9634))
#### Estimated changes
Modified archive/miu_language/basic.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/ring/prod.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/trigonometric/complex.lean
- \+/\- *lemma* complex.differentiable_at_tan

Modified src/category_theory/limits/fubini.lean


Modified src/combinatorics/pigeonhole.lean


Modified src/computability/epsilon_NFA.lean


Modified src/control/traversable/basic.lean


Modified src/control/traversable/equiv.lean


Modified src/data/buffer/parser/basic.lean


Modified src/data/equiv/set.lean


Modified src/data/finset/lattice.lean


Modified src/data/finset/noncomm_prod.lean


Modified src/data/list/zip.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/real/ennreal.lean


Modified src/data/set/lattice.lean


Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/measure/content.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/teichmuller.lean


Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/pgame.lean


Modified src/tactic/congr.lean


Modified src/tactic/core.lean


Modified src/tactic/lean_core_docs.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/valued_field.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/sheaves/sheaf_of_functions.lean


Modified src/topology/urysohns_lemma.lean




## [2021-10-08 21:06:41](https://github.com/leanprover-community/mathlib/commit/70a9540)
refactor(group_theory/monoid_localization) remove old_structure_cmd ([#9621](https://github.com/leanprover-community/mathlib/pull/9621))
#### Estimated changes
Modified src/group_theory/monoid_localization.lean




## [2021-10-08 20:24:14](https://github.com/leanprover-community/mathlib/commit/c37e3e7)
refactor(field_theory/intermediate_field): remove old_structure_cmd ([#9620](https://github.com/leanprover-community/mathlib/pull/9620))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *def* intermediate_field.to_subfield
- \+/\- *structure* intermediate_field



## [2021-10-08 20:24:12](https://github.com/leanprover-community/mathlib/commit/b39feab)
refactor(algebra/lie): reduce use of old_structure_cmd ([#9616](https://github.com/leanprover-community/mathlib/pull/9616))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* lie_equiv.to_linear_equiv
- \- *lemma* lie_hom.coe_linear_mk
- \+ *def* lie_hom.simps.apply

Modified src/algebra/lie/semisimple.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean




## [2021-10-08 17:52:23](https://github.com/leanprover-community/mathlib/commit/91ee8f1)
chore(data/equiv/ring): add big operator lemmas for ring equivs ([#9628](https://github.com/leanprover-community/mathlib/pull/9628))
This PR adds lemmas involving big operators (such as `map_sum`, `map_prod`, etc) for `ring_equiv`s.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.map_list_prod
- \+ *lemma* ring_equiv.map_list_sum
- \+ *lemma* ring_equiv.map_multiset_prod
- \+ *lemma* ring_equiv.map_multiset_sum
- \+ *lemma* ring_equiv.map_prod
- \+ *lemma* ring_equiv.map_sum



## [2021-10-08 16:13:52](https://github.com/leanprover-community/mathlib/commit/57cd1e9)
feat(analysis/normed_space/exponential): remove char_p assumption ([#9618](https://github.com/leanprover-community/mathlib/pull/9618))
Remove the `char_p` assumption from `exp_series_eq_exp_series_of_field_extension` as suggested by @urkud here : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Undergraduate.20math.20list/near/256679511
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean




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
Modified src/algebra/direct_sum/algebra.lean


Modified src/algebra/direct_sum/ring.lean
- \- *def* direct_sum.gcomm_monoid.of_add_subgroups
- \- *def* direct_sum.gcomm_monoid.of_add_submonoids
- \- *def* direct_sum.gcomm_monoid.of_submodules
- \+ *def* direct_sum.gcomm_semiring.of_add_subgroups
- \+ *def* direct_sum.gcomm_semiring.of_add_submonoids
- \+ *def* direct_sum.gcomm_semiring.of_submodules
- \- *def* direct_sum.ghas_mul.of_add_subgroups
- \- *lemma* direct_sum.ghas_mul.of_add_subgroups_mul
- \- *def* direct_sum.ghas_mul.of_add_submonoids
- \- *lemma* direct_sum.ghas_mul.of_add_submonoids_mul
- \- *def* direct_sum.ghas_mul.of_submodules
- \- *lemma* direct_sum.ghas_mul.of_submodules_mul
- \- *def* direct_sum.ghas_mul.to_sigma_has_mul
- \- *def* direct_sum.ghas_one.of_add_subgroups
- \- *def* direct_sum.ghas_one.of_add_submonoids
- \- *def* direct_sum.ghas_one.of_submodules
- \- *def* direct_sum.ghas_one.to_sigma_has_one
- \- *def* direct_sum.gmonoid.of_add_subgroups
- \- *def* direct_sum.gmonoid.of_add_submonoids
- \- *def* direct_sum.gmonoid.of_submodules
- \+ *def* direct_sum.gmul_hom
- \- *lemma* direct_sum.grade_zero.smul_eq_mul
- \+ *def* direct_sum.gsemiring.of_add_subgroups
- \+ *def* direct_sum.gsemiring.of_add_submonoids
- \+ *def* direct_sum.gsemiring.of_submodules
- \- *lemma* semiring.direct_sum_mul

Added src/algebra/graded_monoid.lean
- \+ *def* graded_monoid.gcomm_monoid.of_subobjects
- \+ *def* graded_monoid.ghas_mul.of_subobjects
- \+ *def* graded_monoid.ghas_one.of_subobjects
- \+ *def* graded_monoid.gmonoid.of_subobjects
- \+ *lemma* graded_monoid.grade_zero.smul_eq_mul
- \+ *def* graded_monoid.mk
- \+ *lemma* graded_monoid.mk_mul_mk
- \+ *def* graded_monoid.mk_zero_monoid_hom
- \+ *lemma* graded_monoid.mk_zero_smul
- \+ *def* graded_monoid

Modified src/algebra/monoid_algebra/grading.lean


Modified src/algebra/monoid_algebra/to_direct_sum.lean


Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-10-08 14:22:16](https://github.com/leanprover-community/mathlib/commit/745cbfc)
feat(data/polynomial): %ₘ as a linear map  ([#9532](https://github.com/leanprover-community/mathlib/pull/9532))
This PR bundles `(%ₘ) = polynomial.mod_by_monic` into a linear map. In a follow-up PR, I'll show this map descends to a linear map `adjoin_root q → polynomial R`, thereby (computably) assigning coefficients to each element in `adjoin_root q`.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.add_mod_by_monic
- \+ *lemma* polynomial.mod_by_monic_eq_of_dvd_sub
- \+ *def* polynomial.mod_by_monic_hom
- \+ *lemma* polynomial.smul_mod_by_monic

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial.ker_mod_by_monic_hom
- \+ *lemma* polynomial.mem_ker_mod_by_monic



## [2021-10-08 12:12:57](https://github.com/leanprover-community/mathlib/commit/99c3e22)
refactor(geometry/manifold): remove old_structure_cmd ([#9617](https://github.com/leanprover-community/mathlib/pull/9617))
#### Estimated changes
Modified src/geometry/manifold/algebra/lie_group.lean


Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/algebra/structures.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/topology/algebra/open_subgroup.lean




## [2021-10-08 12:12:56](https://github.com/leanprover-community/mathlib/commit/c107549)
refactor(ring_theory/valuation): remove unnecessary old_structure_cmd ([#9615](https://github.com/leanprover-community/mathlib/pull/9615))
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean


Modified src/topology/algebra/valued_field.lean




## [2021-10-08 12:12:55](https://github.com/leanprover-community/mathlib/commit/7bdd10e)
refactor(order/category): remove old_structure_cmd ([#9614](https://github.com/leanprover-community/mathlib/pull/9614))
#### Estimated changes
Modified src/order/category/NonemptyFinLinOrd.lean




## [2021-10-08 12:12:54](https://github.com/leanprover-community/mathlib/commit/af09d3f)
refactor(algebra/absolute_value): remove unnecessary old_structure_cmd ([#9613](https://github.com/leanprover-community/mathlib/pull/9613))
#### Estimated changes
Modified src/algebra/order/absolute_value.lean


Modified src/data/polynomial/degree/card_pow_degree.lean




## [2021-10-08 12:12:52](https://github.com/leanprover-community/mathlib/commit/25a45ab)
refactor(order/omega_complete_partial_order): remove old_structure_cmd ([#9612](https://github.com/leanprover-community/mathlib/pull/9612))
Removing a use of `old_structure_cmd`.
#### Estimated changes
Modified src/order/category/omega_complete_partial_order.lean


Modified src/order/omega_complete_partial_order.lean
- \+ *def* omega_complete_partial_order.continuous_hom.simps.apply



## [2021-10-08 12:12:51](https://github.com/leanprover-community/mathlib/commit/cea97d9)
feat(*): add not_mem_of_not_mem_closure for anything with subset_closure ([#9595](https://github.com/leanprover-community/mathlib/pull/9595))
This is a goal I would expect library search to finish if I have something not in a closure and I want it not in the base set.
#### Estimated changes
Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.not_mem_of_not_mem_closure

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.not_mem_of_not_mem_closure

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.not_mem_of_not_mem_closure

Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.substructure.not_mem_of_not_mem_closure

Modified src/order/closure.lean
- \+ *lemma* lower_adjoint.not_mem_of_not_mem_closure

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.not_mem_of_not_mem_closure

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.not_mem_of_not_mem_closure

Modified src/topology/basic.lean
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
Modified src/data/finsupp/antidiagonal.lean


Modified src/data/finsupp/basic.lean
- \- *lemma* finsupp.coe_nat_sub
- \+ *lemma* finsupp.coe_tsub
- \- *lemma* finsupp.nat_add_sub_assoc
- \- *lemma* finsupp.nat_add_sub_cancel
- \- *lemma* finsupp.nat_add_sub_cancel_left
- \- *lemma* finsupp.nat_add_sub_of_le
- \- *lemma* finsupp.nat_sub_add_cancel
- \- *lemma* finsupp.nat_sub_apply
- \- *lemma* finsupp.nat_sub_self
- \- *lemma* finsupp.nat_zero_sub
- \- *lemma* finsupp.single_nat_sub
- \+ *lemma* finsupp.single_tsub
- \+ *lemma* finsupp.tsub_apply

Modified src/data/mv_polynomial/basic.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-10-08 10:04:43](https://github.com/leanprover-community/mathlib/commit/34145b7)
feat(group_theory/subgroup/basic): a new to_additive lemma, and remove a by hand proof ([#9594](https://github.com/leanprover-community/mathlib/pull/9594))
I needed `add_subgroup.smul_mem` which didn't seem to exist, and noticed that the `add_subgroup.gsmul_mem` version is proved by hand while to_additive generates it fine (now?)
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \- *lemma* add_subgroup.gsmul_mem



## [2021-10-08 10:04:41](https://github.com/leanprover-community/mathlib/commit/d5146f4)
feat(ring_theory): `adjoin_root g ≃ S` if `S` has a power basis with the right minpoly ([#9529](https://github.com/leanprover-community/mathlib/pull/9529))
This is basically `power_basis.equiv'` with slightly different hypotheses, specialised to `adjoin_root`. It guarantees that even over non-fields, a monogenic extension of `R` can be given by the polynomials over `R` modulo the relevant minimal polynomial.
#### Estimated changes
Modified src/field_theory/adjoin.lean


Modified src/field_theory/normal.lean


Modified src/ring_theory/adjoin_root.lean
- \+ *def* adjoin_root.equiv'
- \+ *lemma* adjoin_root.equiv'_symm_to_alg_hom
- \+ *lemma* adjoin_root.equiv'_to_alg_hom
- \+ *lemma* adjoin_root.lift_hom_mk
- \+ *lemma* adjoin_root.lift_hom_of
- \+ *lemma* adjoin_root.lift_hom_root
- \+/\- *lemma* adjoin_root.lift_mk



## [2021-10-08 10:04:40](https://github.com/leanprover-community/mathlib/commit/82e2b98)
feat(ring_theory): generalize `power_basis.equiv` ([#9528](https://github.com/leanprover-community/mathlib/pull/9528))
`power_basis.equiv'` is an alternate formulation of `power_basis.equiv` that is somewhat more general when not over a field: instead of requiring the minimal polynomials are equal, we only require the generators are the roots of each other's minimal polynomials.
This is not quite enough to show `adjoin_root (minpoly R (pb : power_basis R S).gen)` is isomorphic to `S`, since `minpoly R (adjoin_root.root g)` is not guaranteed to have the same exact roots as `g` itself. So in a follow-up PR I will strengthen `power_basis.equiv'` to `adjoin_root.equiv'` that requires the correct hypothesis.
#### Estimated changes
Modified src/field_theory/adjoin.lean


Modified src/ring_theory/power_basis.lean
- \- *lemma* power_basis.equiv_aeval
- \- *lemma* power_basis.equiv_gen
- \- *lemma* power_basis.equiv_map
- \+ *lemma* power_basis.equiv_of_minpoly_aeval
- \+ *lemma* power_basis.equiv_of_minpoly_gen
- \+ *lemma* power_basis.equiv_of_minpoly_map
- \+ *lemma* power_basis.equiv_of_minpoly_symm
- \+ *lemma* power_basis.equiv_of_root_aeval
- \+ *lemma* power_basis.equiv_of_root_gen
- \+ *lemma* power_basis.equiv_of_root_map
- \+ *lemma* power_basis.equiv_of_root_symm
- \- *lemma* power_basis.equiv_symm



## [2021-10-08 10:04:39](https://github.com/leanprover-community/mathlib/commit/179a495)
feat(algebra/star/algebra): generalize to modules ([#9484](https://github.com/leanprover-community/mathlib/pull/9484))
This means there is now a `star_module ℂ (ι → ℂ)` instance available.
This adds `star_add_monoid`, and renames `star_algebra` to `star_module` with significantly relaxed typeclass arguments.
This also uses `export` to cut away some unnecessary definitions, and adds the missing `pi.star_def` to match `pi.add_def` etc.
#### Estimated changes
Modified src/algebra/ring_quot.lean


Deleted src/algebra/star/algebra.lean
- \- *lemma* star_smul

Modified src/algebra/star/basic.lean
- \- *def* star
- \- *lemma* star_add
- \+/\- *def* star_add_equiv
- \+/\- *lemma* star_id_of_comm
- \- *lemma* star_mul
- \+/\- *lemma* star_zero

Modified src/algebra/star/chsh.lean


Modified src/algebra/star/pi.lean
- \+ *lemma* pi.star_def



## [2021-10-08 07:33:10](https://github.com/leanprover-community/mathlib/commit/9ecdd38)
chore(algebra/order/sub): generalize 2 lemmas ([#9611](https://github.com/leanprover-community/mathlib/pull/9611))
* generalize `lt_sub_iff_left` and `lt_sub_iff_right`;
* use general lemmas in `data.real.ennreal`.
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+ *lemma* lt_sub_comm

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.lt_sub_comm
- \+/\- *lemma* ennreal.lt_sub_iff_add_lt



## [2021-10-08 07:33:09](https://github.com/leanprover-community/mathlib/commit/639a7ef)
feat(algebra/order/ring): variants of mul_sub' ([#9604](https://github.com/leanprover-community/mathlib/pull/9604))
Add some variants of `mul_sub'` and `sub_mul'` and use them in `ennreal`. (Also sneaking in a tiny stylistic change in `topology/ennreal`.)
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+/\- *lemma* mul_sub'
- \+ *lemma* mul_sub_ge
- \+/\- *lemma* sub_mul'
- \+ *lemma* sub_mul_ge

Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.sub_mul_ge

Modified src/topology/instances/ennreal.lean




## [2021-10-08 07:33:08](https://github.com/leanprover-community/mathlib/commit/83a07ce)
feat(data/nat/log): add antitonicity lemmas for first argument ([#9597](https://github.com/leanprover-community/mathlib/pull/9597))
`log` and `clog` are only antitone on bases >1, so we include this as an
assumption in `log_le_log_of_left_ge` (resp. `clog_le_...`) and as a
domain restriction in `log_left_gt_one_anti` (resp. `clog_left_...`).
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *lemma* nat.clog_antitone_left
- \+ *lemma* nat.clog_le_clog_of_left_ge
- \- *lemma* nat.clog_mono
- \+ *lemma* nat.clog_monotone
- \+ *lemma* nat.log_antitone_left
- \+ *lemma* nat.log_le_log_of_left_ge
- \- *lemma* nat.log_mono
- \+ *lemma* nat.log_monotone



## [2021-10-08 07:33:06](https://github.com/leanprover-community/mathlib/commit/41dd4da)
feat(data/multiset/interval): Intervals as `multiset`s ([#9588](https://github.com/leanprover-community/mathlib/pull/9588))
This provides API for `multiset.Ixx` (except `multiset.Ico`).
#### Estimated changes
Modified src/data/multiset/erase_dup.lean


Added src/data/multiset/interval.lean
- \+ *lemma* multiset.Icc_eq_zero_iff
- \+ *lemma* multiset.Icc_eq_zero_of_lt
- \+ *lemma* multiset.Icc_self
- \+ *lemma* multiset.Ioc_eq_zero_iff
- \+ *lemma* multiset.Ioc_eq_zero_of_le
- \+ *lemma* multiset.Ioc_self
- \+ *lemma* multiset.Ioo_eq_zero
- \+ *lemma* multiset.Ioo_eq_zero_iff
- \+ *lemma* multiset.Ioo_eq_zero_of_le
- \+ *lemma* multiset.Ioo_self
- \+ *lemma* multiset.map_add_const_Icc
- \+ *lemma* multiset.map_add_const_Ioc
- \+ *lemma* multiset.map_add_const_Ioo



## [2021-10-08 07:33:05](https://github.com/leanprover-community/mathlib/commit/c3768cc)
refactor(data/multiset/basic): remove sub lemmas ([#9578](https://github.com/leanprover-community/mathlib/pull/9578))
* Remove the multiset sub lemmas that are special cases of lemmas in `algebra/order/sub`
* [This](https://github.com/leanprover-community/mathlib/blob/14c3324143beef6e538f63da9c48d45f4a949604/src/data/multiset/basic.lean#L1513-L1538) gives the list of renamings.
* Use `derive` in `pnat.factors`.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/data/finset/basic.lean


Modified src/data/list/perm.lean


Modified src/data/multiset/antidiagonal.lean


Modified src/data/multiset/basic.lean
- \- *theorem* multiset.add_sub_cancel
- \- *theorem* multiset.add_sub_cancel_left
- \- *theorem* multiset.add_sub_of_le
- \+/\- *theorem* multiset.eq_union_left
- \- *theorem* multiset.le_sub_add
- \+/\- *theorem* multiset.le_union_left
- \- *theorem* multiset.sub_add'
- \- *theorem* multiset.sub_add_cancel
- \- *theorem* multiset.sub_le_self
- \- *theorem* multiset.sub_le_sub_left
- \- *theorem* multiset.sub_le_sub_right

Modified src/data/multiset/nodup.lean


Modified src/data/pnat/factors.lean
- \- *theorem* prime_multiset.add_sub_of_le

Modified src/group_theory/perm/cycle_type.lean




## [2021-10-08 07:33:03](https://github.com/leanprover-community/mathlib/commit/c400677)
feat(algebra/module/basic): `module rat E` is a subsingleton ([#9570](https://github.com/leanprover-community/mathlib/pull/9570))
* allow different (semi)rings in `add_monoid_hom.map_int_cast_smul` and `add_monoid_hom.map_nat_cast_smul`;
* add `add_monoid_hom.map_inv_int_cast_smul` and `add_monoid_hom.map_inv_nat_cast_smul`;
* allow different division rings in `add_monoid_hom.map_rat_cast_smul`, drop `char_zero` assumption;
* prove `subsingleton (module rat M)`;
* add a few convenience lemmas.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+/\- *lemma* add_monoid_hom.map_int_cast_smul
- \+ *lemma* add_monoid_hom.map_inv_int_cast_smul
- \+ *lemma* add_monoid_hom.map_inv_nat_cast_smul
- \+/\- *lemma* add_monoid_hom.map_nat_cast_smul
- \+/\- *lemma* add_monoid_hom.map_rat_cast_smul
- \+ *lemma* inv_int_cast_smul_eq
- \+ *lemma* inv_nat_cast_smul_eq
- \+ *lemma* rat_cast_smul_eq
- \+ *lemma* subsingleton_rat_module

Modified src/data/rat/cast.lean
- \+ *theorem* rat.cast_def
- \+ *theorem* rat.cast_inv_int
- \+ *theorem* rat.cast_inv_nat

Modified src/number_theory/padics/padic_numbers.lean


Modified src/topology/instances/real_vector_space.lean




## [2021-10-08 07:33:02](https://github.com/leanprover-community/mathlib/commit/eb3595e)
move(order/*): move from `algebra.order.` the files that aren't about algebra ([#9562](https://github.com/leanprover-community/mathlib/pull/9562))
`algebra.order.basic` and `algebra.order.functions` never mention `+`, `-` or `*`. Thus they belong under `order`.
#### Estimated changes
Modified archive/arithcc.lean


Modified src/algebra/covariant_and_contravariant.lean


Deleted src/algebra/order/basic.lean
- \- *theorem* cmp_compares
- \- *lemma* cmp_eq_cmp_symm
- \- *lemma* cmp_eq_eq_iff
- \- *lemma* cmp_eq_gt_iff
- \- *lemma* cmp_eq_lt_iff
- \- *def* cmp_le
- \- *theorem* cmp_le_eq_cmp
- \- *theorem* cmp_le_swap
- \- *lemma* cmp_self_eq_eq
- \- *theorem* cmp_swap
- \- *lemma* eq.not_gt
- \- *lemma* eq.not_lt
- \- *lemma* eq.trans_le
- \- *lemma* eq_iff_le_not_lt
- \- *lemma* eq_of_forall_ge_iff
- \- *lemma* eq_of_forall_le_iff
- \- *lemma* eq_or_lt_of_le
- \- *lemma* exists_ge_of_linear
- \- *lemma* forall_lt_iff_le'
- \- *lemma* forall_lt_iff_le
- \- *lemma* ge_iff_le
- \- *theorem* ge_of_eq
- \- *lemma* gt_iff_lt
- \- *lemma* has_le.le.le_iff_eq
- \- *lemma* has_le.le.le_or_le
- \- *lemma* has_le.le.le_or_lt
- \- *lemma* has_le.le.lt_iff_ne
- \- *lemma* has_le.le.lt_or_le
- \- *lemma* has_le.le.trans_eq
- \- *lemma* has_lt.lt.lt_or_lt
- \- *lemma* has_lt.lt.ne'
- \- *lemma* le_iff_eq_or_lt
- \- *lemma* le_iff_le_iff_lt_iff_lt
- \- *lemma* le_iff_le_of_cmp_eq_cmp
- \- *lemma* le_imp_le_iff_lt_imp_lt
- \- *lemma* le_implies_le_of_le_of_le
- \- *lemma* le_of_forall_le'
- \- *lemma* le_of_forall_le
- \- *lemma* le_of_forall_lt'
- \- *lemma* le_of_forall_lt
- \- *lemma* le_rfl
- \- *def* linear_order_of_compares
- \- *lemma* lt_iff_le_and_ne
- \- *lemma* lt_iff_lt_of_cmp_eq_cmp
- \- *lemma* lt_iff_lt_of_le_iff_le'
- \- *lemma* lt_iff_lt_of_le_iff_le
- \- *lemma* lt_iff_not_ge'
- \- *lemma* lt_imp_lt_of_le_imp_le
- \- *lemma* lt_of_not_ge'
- \- *lemma* ne.le_iff_lt
- \- *lemma* ne.lt_or_lt
- \- *lemma* ne_iff_lt_iff_le
- \- *lemma* not_le_of_lt
- \- *lemma* not_lt_iff_eq_or_lt
- \- *lemma* not_lt_of_le
- \- *theorem* ordering.compares.eq_eq
- \- *theorem* ordering.compares.eq_gt
- \- *theorem* ordering.compares.eq_lt
- \- *theorem* ordering.compares.inj
- \- *theorem* ordering.compares.le_antisymm
- \- *theorem* ordering.compares.le_total
- \- *theorem* ordering.compares.ne_gt
- \- *theorem* ordering.compares.ne_lt
- \- *def* ordering.compares
- \- *theorem* ordering.compares_iff_of_compares_impl
- \- *theorem* ordering.compares_swap
- \- *theorem* ordering.or_else_eq_lt
- \- *theorem* ordering.swap_eq_iff_eq_swap
- \- *theorem* ordering.swap_or_else

Modified src/algebra/order/monoid.lean


Modified src/computability/turing_machine.lean


Modified src/data/int/basic.lean


Modified src/order/basic.lean
- \+ *lemma* eq.not_gt
- \+ *lemma* eq.not_lt
- \+ *lemma* eq.trans_le
- \+ *lemma* eq_iff_le_not_lt
- \+ *lemma* eq_of_forall_ge_iff
- \+ *lemma* eq_of_forall_le_iff
- \+ *lemma* eq_or_lt_of_le
- \+ *lemma* exists_ge_of_linear
- \+ *lemma* forall_lt_iff_le'
- \+ *lemma* forall_lt_iff_le
- \+ *lemma* ge_iff_le
- \+ *theorem* ge_of_eq
- \+ *lemma* gt_iff_lt
- \+ *lemma* has_le.le.le_iff_eq
- \+ *lemma* has_le.le.le_or_le
- \+ *lemma* has_le.le.le_or_lt
- \+ *lemma* has_le.le.lt_iff_ne
- \+ *lemma* has_le.le.lt_or_le
- \+ *lemma* has_le.le.trans_eq
- \+ *lemma* has_lt.lt.lt_or_lt
- \+ *lemma* has_lt.lt.ne'
- \+ *lemma* le_iff_eq_or_lt
- \+ *lemma* le_iff_le_iff_lt_iff_lt
- \+ *lemma* le_imp_le_iff_lt_imp_lt
- \+ *lemma* le_implies_le_of_le_of_le
- \+ *lemma* le_of_forall_le'
- \+ *lemma* le_of_forall_le
- \+ *lemma* le_of_forall_lt'
- \+ *lemma* le_of_forall_lt
- \+ *lemma* le_rfl
- \+ *lemma* lt_iff_le_and_ne
- \+ *lemma* lt_iff_lt_of_le_iff_le'
- \+ *lemma* lt_iff_lt_of_le_iff_le
- \+ *lemma* lt_iff_not_ge'
- \+ *lemma* lt_imp_lt_of_le_imp_le
- \+ *lemma* lt_of_not_ge'
- \+/\- *lemma* lt_self_iff_false
- \+ *lemma* ne.le_iff_lt
- \+ *lemma* ne.lt_or_lt
- \+ *lemma* ne_iff_lt_iff_le
- \+ *lemma* not_le_of_lt
- \+ *lemma* not_lt_iff_eq_or_lt
- \+ *lemma* not_lt_of_le
- \- *theorem* order_dual.cmp_le_flip
- \- *lemma* order_dual.dual_compares

Added src/order/compare.lean
- \+ *lemma* cmp_compares
- \+ *lemma* cmp_eq_cmp_symm
- \+ *lemma* cmp_eq_eq_iff
- \+ *lemma* cmp_eq_gt_iff
- \+ *lemma* cmp_eq_lt_iff
- \+ *def* cmp_le
- \+ *lemma* cmp_le_eq_cmp
- \+ *lemma* cmp_le_swap
- \+ *lemma* cmp_self_eq_eq
- \+ *lemma* cmp_swap
- \+ *lemma* le_iff_le_of_cmp_eq_cmp
- \+ *def* linear_order_of_compares
- \+ *lemma* lt_iff_lt_of_cmp_eq_cmp
- \+ *lemma* order_dual.cmp_le_flip
- \+ *lemma* order_dual.dual_compares
- \+ *lemma* ordering.compares.eq_eq
- \+ *lemma* ordering.compares.eq_gt
- \+ *lemma* ordering.compares.eq_lt
- \+ *lemma* ordering.compares.inj
- \+ *lemma* ordering.compares.le_antisymm
- \+ *lemma* ordering.compares.le_total
- \+ *lemma* ordering.compares.ne_gt
- \+ *lemma* ordering.compares.ne_lt
- \+ *def* ordering.compares
- \+ *lemma* ordering.compares_iff_of_compares_impl
- \+ *lemma* ordering.compares_swap
- \+ *lemma* ordering.or_else_eq_lt
- \+ *lemma* ordering.swap_eq_iff_eq_swap
- \+ *lemma* ordering.swap_or_else

Renamed src/algebra/order/functions.lean to src/order/min_max.lean


Modified src/order/monotone.lean


Modified src/order/pilex.lean


Modified src/tactic/push_neg.lean




## [2021-10-08 07:33:00](https://github.com/leanprover-community/mathlib/commit/8aa1893)
feat(group_theory/subgroup/basic): Analog of `mul_aut.conj` for normal subgroups. ([#9552](https://github.com/leanprover-community/mathlib/pull/9552))
Analog of `mul_aut.conj` for normal subgroups (pretty much just copying the code from `data/equiv/mul_add_aut.lean`).
#### Estimated changes
Modified src/group_theory/group_action/conj_act.lean
- \+ *lemma* conj_act.subgroup.coe_conj_smul
- \+ *def* mul_aut.conj_normal
- \+ *lemma* mul_aut.conj_normal_apply
- \+ *lemma* mul_aut.conj_normal_inv_apply
- \+ *lemma* mul_aut.conj_normal_symm_apply



## [2021-10-08 07:32:59](https://github.com/leanprover-community/mathlib/commit/1390b44)
feat(analysis/convex/function): API for strict convex functions ([#9437](https://github.com/leanprover-community/mathlib/pull/9437))
This provides all the basic API for `strict_convex_on` and `strict_concave_on`.
#### Estimated changes
Modified src/analysis/convex/function.lean
- \- *lemma* concave_on_iff_forall_pos_ne
- \+ *lemma* concave_on_iff_pairwise_on_pos
- \- *lemma* convex_on_iff_forall_pos_ne
- \+ *lemma* convex_on_iff_pairwise_on_pos
- \+ *lemma* linear_order.strict_concave_on_of_lt
- \+ *lemma* linear_order.strict_convex_on_of_lt
- \+ *lemma* neg_strict_concave_on_iff
- \+ *lemma* neg_strict_convex_on_iff
- \+ *lemma* strict_concave_on.add
- \+ *lemma* strict_concave_on.concave_on
- \+ *lemma* strict_concave_on.convex_gt
- \+ *lemma* strict_concave_on.inf
- \+ *lemma* strict_concave_on.left_lt_of_lt_right'
- \+ *lemma* strict_concave_on.left_lt_of_lt_right
- \+ *lemma* strict_concave_on.lt_on_open_segment'
- \+ *lemma* strict_concave_on.lt_on_open_segment
- \+ *lemma* strict_concave_on.lt_right_of_left_lt'
- \+ *lemma* strict_concave_on.lt_right_of_left_lt
- \+ *lemma* strict_concave_on.subset
- \+ *lemma* strict_concave_on.translate_left
- \+ *lemma* strict_concave_on.translate_right
- \+ *lemma* strict_concave_on_iff_div
- \+ *lemma* strict_convex_on.add
- \+ *lemma* strict_convex_on.convex_lt
- \+ *lemma* strict_convex_on.convex_on
- \+ *lemma* strict_convex_on.lt_left_of_right_lt'
- \+ *lemma* strict_convex_on.lt_left_of_right_lt
- \+ *lemma* strict_convex_on.lt_on_open_segment'
- \+ *lemma* strict_convex_on.lt_on_open_segment
- \+ *lemma* strict_convex_on.lt_right_of_left_lt'
- \+ *lemma* strict_convex_on.lt_right_of_left_lt
- \+ *lemma* strict_convex_on.subset
- \+ *lemma* strict_convex_on.sup
- \+ *lemma* strict_convex_on.translate_left
- \+ *lemma* strict_convex_on.translate_right
- \+ *lemma* strict_convex_on_iff_div

Modified src/analysis/convex/slope.lean
- \+ *lemma* strict_concave_on.slope_anti_adjacent
- \+ *lemma* strict_concave_on_iff_slope_strict_anti_adjacent
- \+ *lemma* strict_concave_on_of_slope_strict_anti_adjacent
- \+ *lemma* strict_convex_on.slope_strict_mono_adjacent
- \+ *lemma* strict_convex_on_iff_slope_strict_mono_adjacent
- \+ *lemma* strict_convex_on_of_slope_strict_mono_adjacent



## [2021-10-08 07:32:58](https://github.com/leanprover-community/mathlib/commit/a0504eb)
refactor(data/*/interval): generalize `finset.Ico` to locally finite orders ([#7987](https://github.com/leanprover-community/mathlib/pull/7987))
`finset.Ico` currently goes `ℕ → ℕ → finset ℕ`. This generalizes it to `α → α → finset α` where `locally_finite_order α`.
This also ports all the existing `finset.Ico` lemmas to the new API, which involves renaming and moving them to `data.finset.interval` or `data.nat.interval` depending on whether I could generalize them away from `ℕ` or not.
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean


Modified src/algebra/geom_sum.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/analytic/inverse.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/data/fin/interval.lean
- \+ *lemma* fin.Ico_eq_finset_subtype
- \+ *lemma* fin.card_Ico
- \+ *lemma* fin.card_fintype_Ico
- \+ *lemma* fin.map_subtype_embedding_Ico

Modified src/data/finset/default.lean


Modified src/data/finset/interval.lean
- \+ *lemma* finset.Ico_diff_Ico_left
- \+ *lemma* finset.Ico_diff_Ico_right
- \+ *lemma* finset.Ico_disjoint_Ico_consecutive
- \+ *lemma* finset.Ico_eq_empty_iff
- \+ *lemma* finset.Ico_eq_empty_of_le
- \+ *lemma* finset.Ico_filter_le
- \+ *lemma* finset.Ico_filter_le_left
- \+ *lemma* finset.Ico_filter_le_of_le_left
- \+ *lemma* finset.Ico_filter_le_of_left_le
- \+ *lemma* finset.Ico_filter_le_of_right_le
- \+ *lemma* finset.Ico_filter_lt
- \+ *lemma* finset.Ico_filter_lt_of_le_left
- \+ *lemma* finset.Ico_filter_lt_of_le_right
- \+ *lemma* finset.Ico_filter_lt_of_right_le
- \+ *lemma* finset.Ico_insert_right
- \+ *lemma* finset.Ico_inter_Ico
- \+ *lemma* finset.Ico_inter_Ico_consecutive
- \+ *lemma* finset.Ico_self
- \+ *lemma* finset.Ico_subset_Ico_iff
- \+ *lemma* finset.Ico_union_Ico'
- \+ *lemma* finset.Ico_union_Ico
- \+ *lemma* finset.Ico_union_Ico_eq_Ico
- \+ *lemma* finset.Ioo_insert_left
- \+ *lemma* finset.image_add_const_Ico
- \+ *lemma* finset.nonempty_Ico
- \+ *lemma* finset.right_not_mem_Ico

Deleted src/data/finset/intervals.lean
- \- *theorem* finset.Ico.card
- \- *lemma* finset.Ico.coe_eq_Ico
- \- *lemma* finset.Ico.diff_left
- \- *lemma* finset.Ico.diff_right
- \- *lemma* finset.Ico.disjoint_consecutive
- \- *theorem* finset.Ico.eq_empty_iff
- \- *theorem* finset.Ico.eq_empty_of_le
- \- *lemma* finset.Ico.filter_Ico_bot
- \- *lemma* finset.Ico.filter_le
- \- *lemma* finset.Ico.filter_le_of_le
- \- *lemma* finset.Ico.filter_le_of_le_bot
- \- *lemma* finset.Ico.filter_le_of_top_le
- \- *lemma* finset.Ico.filter_lt
- \- *lemma* finset.Ico.filter_lt_of_ge
- \- *lemma* finset.Ico.filter_lt_of_le_bot
- \- *lemma* finset.Ico.filter_lt_of_top_le
- \- *theorem* finset.Ico.image_add
- \- *lemma* finset.Ico.image_const_sub
- \- *theorem* finset.Ico.image_sub
- \- *theorem* finset.Ico.insert_succ_bot
- \- *lemma* finset.Ico.inter
- \- *lemma* finset.Ico.inter_consecutive
- \- *theorem* finset.Ico.mem
- \- *theorem* finset.Ico.not_mem_top
- \- *theorem* finset.Ico.pred_singleton
- \- *theorem* finset.Ico.self_eq_empty
- \- *theorem* finset.Ico.subset_iff
- \- *theorem* finset.Ico.succ_singleton
- \- *theorem* finset.Ico.succ_top'
- \- *theorem* finset.Ico.succ_top
- \- *theorem* finset.Ico.to_finset
- \- *lemma* finset.Ico.union'
- \- *lemma* finset.Ico.union
- \- *lemma* finset.Ico.union_consecutive
- \- *theorem* finset.Ico.val
- \- *theorem* finset.Ico.zero_bot
- \- *def* finset.Ico
- \- *lemma* finset.Ico_ℤ.card
- \- *lemma* finset.Ico_ℤ.mem
- \- *def* finset.Ico_ℤ
- \- *lemma* finset.range_eq_Ico
- \- *lemma* finset.range_image_pred_top_sub

Deleted src/data/fintype/intervals.lean
- \- *lemma* set.Icc_ℕ_card
- \- *lemma* set.Icc_ℕ_finite
- \- *lemma* set.Icc_ℤ_card
- \- *lemma* set.Icc_ℤ_finite
- \- *lemma* set.Ico_pnat_card
- \- *lemma* set.Ico_ℕ_card
- \- *lemma* set.Ico_ℕ_finite
- \- *lemma* set.Ico_ℤ_card
- \- *lemma* set.Ico_ℤ_finite
- \- *lemma* set.Ioc_ℕ_card
- \- *lemma* set.Ioc_ℕ_finite
- \- *lemma* set.Ioc_ℤ_card
- \- *lemma* set.Ioc_ℤ_finite
- \- *lemma* set.Ioo_ℕ_card
- \- *lemma* set.Ioo_ℕ_finite
- \- *lemma* set.Ioo_ℤ_card
- \- *lemma* set.Ioo_ℤ_finite

Modified src/data/int/interval.lean
- \+ *lemma* int.Ico_eq_finset_map
- \+ *lemma* int.card_Ico
- \+ *lemma* int.card_Ico_of_le
- \+ *lemma* int.card_fintype_Ico
- \+ *lemma* int.card_fintype_Ico_of_le

Modified src/data/nat/interval.lean
- \+ *lemma* finset.range_eq_Ico
- \+ *lemma* nat.Icc_pred_right
- \+ *lemma* nat.Ico_eq_range'
- \+ *lemma* nat.Ico_image_const_sub_eq_Ico
- \+ *lemma* nat.Ico_insert_succ_left
- \+ *lemma* nat.Ico_pred_singleton
- \+ *lemma* nat.Ico_succ_left
- \+ *lemma* nat.Ico_succ_right
- \+ *lemma* nat.Ico_succ_right_eq_insert_Ico
- \+ *lemma* nat.Ico_succ_singleton
- \+ *lemma* nat.Ico_succ_succ
- \+ *lemma* nat.Ico_zero_eq_range
- \+ *lemma* nat.Iio_eq_range
- \+ *lemma* nat.card_Ico
- \+ *lemma* nat.card_fintype_Ico
- \+ *lemma* nat.image_sub_const_Ico
- \+ *lemma* nat.range_image_pred_top_sub

Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean


Modified src/data/pnat/interval.lean
- \+ *lemma* pnat.Ico_eq_finset_subtype
- \+ *lemma* pnat.card_Ico
- \+ *lemma* pnat.card_fintype_Ico
- \+ *lemma* pnat.map_subtype_embedding_Ico

Deleted src/data/pnat/intervals.lean
- \- *lemma* pnat.Ico.card
- \- *lemma* pnat.Ico.mem
- \- *def* pnat.Ico

Modified src/data/polynomial/inductions.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean


Modified src/number_theory/ADE_inequality.lean


Modified src/number_theory/divisors.lean


Modified src/number_theory/primorial.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/order/locally_finite.lean
- \+ *def* finset.Ico
- \+ *theorem* finset.Ico_subset_Ico
- \+ *def* finset.Iio
- \+ *lemma* finset.Iio_eq_Ico
- \+ *lemma* finset.coe_Ico
- \+ *lemma* finset.coe_Iio
- \+ *lemma* finset.map_subtype_embedding_Ico
- \+ *lemma* finset.mem_Ico
- \+ *lemma* finset.mem_Iio
- \+ *lemma* finset.subtype_Ico_eq
- \+ *def* multiset.Iio
- \+ *lemma* multiset.mem_Iio
- \+ *lemma* set.finite_Ico
- \+ *lemma* set.finite_Iio

Modified src/probability_theory/independence.lean


Modified src/ring_theory/henselian.lean


Modified src/tactic/interval_cases.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified test/fin_cases.lean




## [2021-10-08 06:08:46](https://github.com/leanprover-community/mathlib/commit/ba2454e)
feat(ring_theory/coprime): two lemmas prereq for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9456](https://github.com/leanprover-community/mathlib/pull/9456))
Two variants of the fact that `¬ is_coprime 0 0`.
#### Estimated changes
Modified src/ring_theory/coprime/basic.lean
- \+ *lemma* is_coprime.ne_zero
- \+ *lemma* is_coprime.sq_add_sq_ne_zero



## [2021-10-08 02:40:18](https://github.com/leanprover-community/mathlib/commit/235bfd7)
chore(scripts): update nolints.txt ([#9610](https://github.com/leanprover-community/mathlib/pull/9610))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-10-08 01:32:09](https://github.com/leanprover-community/mathlib/commit/9ea4568)
fix(topology/path_connected): add `continuity` to `path.continuous_extend` ([#9605](https://github.com/leanprover-community/mathlib/pull/9605))
#### Estimated changes
Modified src/topology/path_connected.lean




## [2021-10-08 00:30:16](https://github.com/leanprover-community/mathlib/commit/fa3b622)
refactor(analysis/normed_space/linear_isometry): semilinear isometries ([#9551](https://github.com/leanprover-community/mathlib/pull/9551))
Generalize the theory of linear isometries to the semilinear setting.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry.coe_comp
- \+/\- *lemma* linear_isometry.coe_fn_injective
- \+/\- *def* linear_isometry.comp
- \+/\- *lemma* linear_isometry.comp_assoc
- \+/\- *lemma* linear_isometry.ext
- \+/\- *lemma* linear_isometry.id_comp
- \+/\- *lemma* linear_isometry.map_eq_iff
- \+/\- *lemma* linear_isometry.map_ne
- \+/\- *lemma* linear_isometry.map_smul
- \+ *lemma* linear_isometry.map_smulₛₗ
- \+/\- *def* linear_isometry.to_continuous_linear_map
- \+/\- *lemma* linear_isometry.to_linear_map_injective
- \+/\- *structure* linear_isometry
- \+/\- *lemma* linear_isometry_equiv.apply_symm_apply
- \+/\- *lemma* linear_isometry_equiv.coe_coe''
- \+/\- *lemma* linear_isometry_equiv.coe_coe'
- \+/\- *lemma* linear_isometry_equiv.coe_coe
- \+/\- *lemma* linear_isometry_equiv.coe_mk
- \+/\- *lemma* linear_isometry_equiv.coe_symm_trans
- \+/\- *lemma* linear_isometry_equiv.coe_to_linear_equiv
- \+/\- *lemma* linear_isometry_equiv.coe_trans
- \+/\- *lemma* linear_isometry_equiv.ext
- \+/\- *lemma* linear_isometry_equiv.map_smul
- \+ *lemma* linear_isometry_equiv.map_smulₛₗ
- \+/\- *def* linear_isometry_equiv.of_bounds
- \+/\- *lemma* linear_isometry_equiv.range_eq_univ
- \+/\- *def* linear_isometry_equiv.symm
- \+/\- *lemma* linear_isometry_equiv.symm_trans
- \+/\- *def* linear_isometry_equiv.to_continuous_linear_equiv
- \+/\- *def* linear_isometry_equiv.to_homeomorph
- \+/\- *def* linear_isometry_equiv.to_isometric
- \+/\- *lemma* linear_isometry_equiv.to_linear_equiv_injective
- \+/\- *def* linear_isometry_equiv.to_linear_isometry
- \+/\- *def* linear_isometry_equiv.trans
- \+/\- *lemma* linear_isometry_equiv.trans_assoc
- \+/\- *lemma* linear_isometry_equiv.trans_refl
- \+/\- *structure* linear_isometry_equiv

Modified src/analysis/normed_space/multilinear.lean




## [2021-10-07 21:23:16](https://github.com/leanprover-community/mathlib/commit/9518ce1)
feat(topology/algebra): valued fields ([#9589](https://github.com/leanprover-community/mathlib/pull/9589))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* group_with_zero.eq_zero_or_unit

Modified src/ring_theory/valuation/basic.lean
- \+ *def* valuation.lt_add_subgroup

Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* topological_add_group.separated_iff_zero_closed
- \+ *lemma* topological_add_group.separated_of_zero_sep

Added src/topology/algebra/valuation.lean
- \+ *lemma* valued.cauchy_iff
- \+ *lemma* valued.loc_const
- \+ *lemma* valued.mem_nhds
- \+ *lemma* valued.mem_nhds_zero
- \+ *lemma* valued.subgroups_basis

Added src/topology/algebra/valued_field.lean
- \+ *lemma* valuation.inversion_estimate
- \+ *lemma* valued.continuous_extension
- \+ *lemma* valued.continuous_valuation
- \+ *lemma* valued.extension_extends

Modified src/topology/basic.lean
- \+ *lemma* dense_range.mem_nhds



## [2021-10-07 19:09:56](https://github.com/leanprover-community/mathlib/commit/ebccce9)
feat(measure_theory/covering/besicovitch): the measurable Besicovitch covering theorem ([#9576](https://github.com/leanprover-community/mathlib/pull/9576))
The measurable Besicovitch theorem ensures that, in nice metric spaces, if at every point one considers a class of balls of arbitrarily small radii, called admissible balls, then one can cover almost all the space by a family of disjoint admissible balls. It is deduced from the topological Besicovitch theorem.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean
- \+ *lemma* besicovitch.exist_finset_disjoint_balls_large_measure
- \+ *theorem* besicovitch.exists_disjoint_closed_ball_covering
- \+ *theorem* besicovitch.exists_disjoint_closed_ball_covering_of_finite_measure



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
Modified src/algebra/order/monoid.lean
- \+ *lemma* with_top.add_coe_eq_top_iff
- \+ *lemma* with_top.coe_add_eq_top_iff

Modified src/algebra/order/sub.lean
- \+ *lemma* with_top.coe_sub
- \+ *lemma* with_top.sub_top
- \+ *lemma* with_top.top_sub_coe

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.add_le_cancellable_iff_ne
- \- *lemma* ennreal.add_sub_cancel_of_le
- \+/\- *lemma* ennreal.add_sub_self'
- \+/\- *lemma* ennreal.add_sub_self
- \+ *lemma* ennreal.cancel_coe
- \+ *lemma* ennreal.cancel_of_lt'
- \+ *lemma* ennreal.cancel_of_lt
- \+ *lemma* ennreal.cancel_of_ne
- \+/\- *lemma* ennreal.coe_sub
- \- *lemma* ennreal.sub_add_cancel_of_le
- \+ *lemma* ennreal.sub_eq_Inf
- \+/\- *lemma* ennreal.sub_eq_of_add_eq
- \+ *lemma* ennreal.sub_eq_top_iff
- \+ *lemma* ennreal.sub_ne_top
- \+/\- *lemma* ennreal.sub_self
- \+/\- *lemma* ennreal.sub_top
- \+/\- *lemma* ennreal.sub_zero
- \+/\- *lemma* ennreal.top_sub_coe
- \+/\- *lemma* ennreal.zero_sub

Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/instances/ennreal.lean




## [2021-10-07 13:09:23](https://github.com/leanprover-community/mathlib/commit/bf76a1f)
feat(algebra/order/with_zero): add lt_of_mul_lt_mul_of_le₀ and mul_lt_mul_of_lt_of_le₀ ([#9596](https://github.com/leanprover-community/mathlib/pull/9596))
#### Estimated changes
Modified src/algebra/order/with_zero.lean
- \+ *lemma* lt_of_mul_lt_mul_of_le₀
- \+ *lemma* mul_lt_mul_of_lt_of_le₀



## [2021-10-07 11:57:08](https://github.com/leanprover-community/mathlib/commit/18a42f3)
feat(src/category_theory/*): Yoneda preserves limits. ([#9580](https://github.com/leanprover-community/mathlib/pull/9580))
Shows that `yoneda` and `coyoneda` preserves and reflects limits.
#### Estimated changes
Modified src/category_theory/limits/functor_category.lean
- \+ *def* category_theory.limits.preserves_colimit_of_evaluation
- \+ *def* category_theory.limits.preserves_colimits_of_evaluation
- \+ *def* category_theory.limits.preserves_colimits_of_shape_of_evaluation
- \+ *def* category_theory.limits.preserves_limit_of_evaluation
- \+ *def* category_theory.limits.preserves_limits_of_evaluation
- \+ *def* category_theory.limits.preserves_limits_of_shape_of_evaluation

Modified src/category_theory/limits/yoneda.lean




## [2021-10-07 06:55:11](https://github.com/leanprover-community/mathlib/commit/f874783)
feat(data/multiset/erase_dup): Alias for `multiset.erase_dup_eq_self` ([#9587](https://github.com/leanprover-community/mathlib/pull/9587))
The new `multiset.nodup.erase_dup` allows dot notation.
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/pi.lean


Modified src/data/multiset/erase_dup.lean


Modified src/number_theory/arithmetic_function.lean




## [2021-10-07 06:55:10](https://github.com/leanprover-community/mathlib/commit/cc46f31)
feat(analysis/normed_space/add_torsor_bases): the interior of the convex hull of a finite affine basis is the set of points with strictly positive barycentric coordinates ([#9583](https://github.com/leanprover-community/mathlib/pull/9583))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/convex/hull.lean
- \+ *lemma* convex_hull_univ

Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* interior_convex_hull_aff_basis

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.eq_univ_of_subsingleton_span_eq_top



## [2021-10-07 06:14:33](https://github.com/leanprover-community/mathlib/commit/a7784aa)
feat(category_theory/*): Yoneda extension is Kan ([#9574](https://github.com/leanprover-community/mathlib/pull/9574))
- Proved that `(F.elements)ᵒᵖ ≌ costructured_arrow yoneda F`.
- Verified that the yoneda extension is indeed the left Kan extension along the yoneda embedding.
#### Estimated changes
Modified src/category_theory/elements.lean
- \+ *def* category_theory.category_of_elements.costructured_arrow_yoneda_equivalence
- \+ *lemma* category_theory.category_of_elements.costructured_arrow_yoneda_equivalence_naturality
- \+ *def* category_theory.category_of_elements.from_costructured_arrow
- \+ *lemma* category_theory.category_of_elements.from_costructured_arrow_obj_mk
- \+ *lemma* category_theory.category_of_elements.from_to_costructured_arrow_eq
- \+ *def* category_theory.category_of_elements.to_costructured_arrow
- \+ *lemma* category_theory.category_of_elements.to_from_costructured_arrow_eq

Modified src/category_theory/limits/presheaf.lean
- \+ *def* category_theory.colimit_adj.extend_along_yoneda_iso_Kan
- \+ *def* category_theory.colimit_adj.extend_along_yoneda_iso_Kan_app
- \+ *lemma* category_theory.colimit_adj.extend_along_yoneda_map



## [2021-10-07 06:14:32](https://github.com/leanprover-community/mathlib/commit/b9097f1)
feat(analysis/asymptotics): Define superpolynomial decay of a function ([#9440](https://github.com/leanprover-community/mathlib/pull/9440))
Define superpolynomial decay of functions in terms of asymptotics.is_O.
#### Estimated changes
Added src/analysis/asymptotics/superpolynomial_decay.lean
- \+ *lemma* asymptotics.is_O.trans_superpolynomial_decay
- \+ *lemma* asymptotics.superpolynomial_decay.add
- \+ *lemma* asymptotics.superpolynomial_decay.algebra_map_mul
- \+ *lemma* asymptotics.superpolynomial_decay.algebra_map_pow_mul
- \+ *lemma* asymptotics.superpolynomial_decay.const_mul
- \+ *lemma* asymptotics.superpolynomial_decay.eventually_le
- \+ *lemma* asymptotics.superpolynomial_decay.eventually_mono
- \+ *lemma* asymptotics.superpolynomial_decay.mono
- \+ *lemma* asymptotics.superpolynomial_decay.mul
- \+ *lemma* asymptotics.superpolynomial_decay.mul_const
- \+ *lemma* asymptotics.superpolynomial_decay.mul_is_O
- \+ *lemma* asymptotics.superpolynomial_decay.mul_is_O_polynomial
- \+ *theorem* asymptotics.superpolynomial_decay.polynomial_mul
- \+ *lemma* asymptotics.superpolynomial_decay.tendsto_zero
- \+ *def* asymptotics.superpolynomial_decay
- \+ *lemma* asymptotics.superpolynomial_decay_const_iff
- \+ *lemma* asymptotics.superpolynomial_decay_const_mul_iff
- \+ *lemma* asymptotics.superpolynomial_decay_const_mul_iff_of_ne_zero
- \+ *theorem* asymptotics.superpolynomial_decay_iff_is_bounded_under
- \+ *theorem* asymptotics.superpolynomial_decay_iff_is_o
- \+ *theorem* asymptotics.superpolynomial_decay_iff_norm_tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay_iff_tendsto_zero
- \+ *lemma* asymptotics.superpolynomial_decay_mul_const_iff
- \+ *lemma* asymptotics.superpolynomial_decay_mul_const_iff_of_ne_zero
- \+ *lemma* asymptotics.superpolynomial_decay_of_eventually_is_O
- \+ *lemma* asymptotics.superpolynomial_decay_of_is_O_fpow_le
- \+ *lemma* asymptotics.superpolynomial_decay_of_is_O_fpow_lt
- \+ *lemma* asymptotics.superpolynomial_decay_zero'
- \+ *lemma* asymptotics.superpolynomial_decay_zero



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
Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified test/instance_diamonds.lean




## [2021-10-07 04:15:16](https://github.com/leanprover-community/mathlib/commit/cb3c844)
feat(category_theory/limits/*): Filtered colimits preserves finite limits ([#9522](https://github.com/leanprover-community/mathlib/pull/9522))
Restated `category_theory.limits.colimit_limit_to_limit_colimit_is_iso` in terms of limit preserving.
#### Estimated changes
Modified src/category_theory/limits/colimit_limit.lean
- \+/\- *lemma* category_theory.limits.ι_colimit_limit_to_limit_colimit_π

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/functor_category.lean
- \+ *def* category_theory.limits.colimit_iso_swap_comp_colim
- \+ *def* category_theory.limits.limit_iso_swap_comp_lim



## [2021-10-07 02:14:30](https://github.com/leanprover-community/mathlib/commit/7a2696d)
feat(category_theory/limits/preserves/*): Show that whiskering left preserves limits. ([#9581](https://github.com/leanprover-community/mathlib/pull/9581))
#### Estimated changes
Modified src/category_theory/limits/preserves/functor_category.lean




## [2021-10-07 02:14:29](https://github.com/leanprover-community/mathlib/commit/f37aeb0)
refactor(algebra/gcd_monoid): drop nontriviality assumptions  ([#9568](https://github.com/leanprover-community/mathlib/pull/9568))
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/gcd_monoid/multiset.lean


Modified src/algebra/group/units.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2021-10-06 21:14:59](https://github.com/leanprover-community/mathlib/commit/f63786b)
refactor(data/finsupp/basic): has_ordered_sub on finsupp ([#9577](https://github.com/leanprover-community/mathlib/pull/9577))
* Generalize `has_sub` and `canonically_ordered_add_monoid` instances for any finsupp with codomain a `canonically_ordered_add_monoid` & `has_ordered_sub`.
* Provide `has_ordered_sub` instance in the same situation
* Generalize lemmas about `nat` to this situation.
* Prove some lemmas as special cases of `has_ordered_sub` lemmas. These will be removed in a subsequent PR.
* Simplify some lemmas about `α →₀ ℕ` using `has_ordered_sub` lemmas.
* Prove `nat.one_le_iff_ne_zero` (it's the second time I want to use it this week)
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.coe_nat_sub
- \+/\- *lemma* finsupp.nat_add_sub_assoc
- \+/\- *lemma* finsupp.nat_add_sub_cancel
- \+/\- *lemma* finsupp.nat_add_sub_cancel_left
- \+/\- *lemma* finsupp.nat_add_sub_of_le
- \+/\- *lemma* finsupp.nat_sub_add_cancel
- \+/\- *lemma* finsupp.nat_sub_apply
- \+/\- *lemma* finsupp.nat_sub_self
- \+/\- *lemma* finsupp.nat_zero_sub
- \+/\- *lemma* finsupp.single_nat_sub

Modified src/data/nat/basic.lean
- \+ *lemma* nat.one_le_iff_ne_zero



## [2021-10-06 21:14:58](https://github.com/leanprover-community/mathlib/commit/b4a9767)
feat(data/multiset/basic): has_ordered_sub multiset ([#9566](https://github.com/leanprover-community/mathlib/pull/9566))
* Provide `instance : has_ordered_sub (multiset α)`
* Prove most multiset subtraction lemmas as special cases of `has_ordered_sub` lemmas
* In a subsequent PR I will remove the specialized multiset lemmas
#### Estimated changes
Modified src/data/multiset/basic.lean
- \- *theorem* multiset.sub_le_iff_le_add
- \- *theorem* multiset.sub_zero



## [2021-10-06 21:14:56](https://github.com/leanprover-community/mathlib/commit/845d064)
feat(algebra/big_operators/finprod): add finprod.mem_dvd ([#9549](https://github.com/leanprover-community/mathlib/pull/9549))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.dvd_prod_of_mem

Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_mem_dvd



## [2021-10-06 19:23:08](https://github.com/leanprover-community/mathlib/commit/b2ae195)
move(data/fin/*): group `fin` files under a `fin` folder ([#9524](https://github.com/leanprover-community/mathlib/pull/9524))
#### Estimated changes
Modified src/category_theory/Fintype.lean


Modified src/control/functor/multivariate.lean


Modified src/data/bitvec/basic.lean


Modified src/data/equiv/fin.lean


Renamed src/data/fin.lean to src/data/fin/basic.lean


Renamed src/data/fin2.lean to src/data/fin/fin2.lean


Modified src/data/fintype/fin.lean


Modified src/data/list/duplicate.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/list/of_fn.lean


Modified src/data/typevec.lean


Modified src/data/vector3.lean


Modified src/number_theory/dioph.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/jordan_holder.lean


Modified src/set_theory/pgame.lean


Modified src/system/random/basic.lean




## [2021-10-06 18:27:53](https://github.com/leanprover-community/mathlib/commit/5c3cdd2)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are open maps (in finite dimensions over a complete field) ([#9543](https://github.com/leanprover-community/mathlib/pull/9543))
Using the open mapping theorem with a one-dimensional codomain feels a bit ridiculous but I see no reason not to do so.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* is_open_map_barycentric_coord

Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* surjective_barycentric_coord



## [2021-10-06 17:48:50](https://github.com/leanprover-community/mathlib/commit/a7b4e78)
fix(computability/DFA): tighten regular pumping lemma to match standard textbooks ([#9585](https://github.com/leanprover-community/mathlib/pull/9585))
This PR slightly tightens the regular pumping lemma: the current version applies only to words that are of length at least the number of states in the DFA plus one. Here we remove the plus one.
#### Estimated changes
Modified src/computability/DFA.lean
- \+/\- *lemma* DFA.eval_from_split

Modified src/computability/NFA.lean


Modified src/computability/epsilon_NFA.lean




## [2021-10-06 15:46:06](https://github.com/leanprover-community/mathlib/commit/bcd13a7)
refactor(data/equiv): split out `./set` from `./basic` ([#9560](https://github.com/leanprover-community/mathlib/pull/9560))
This move all the equivalences between sets-coerced-to-types to a new file, which makes `equiv/basic` a slightly more manageable size.
The only non-move change in this PR is the rewriting of `equiv.of_bijective` to not go via `equiv.of_injective`, as we already have all the fields available directly and this allows the latter to move to a separate file.
This will allow us to import `order_dual.lean` earlier, as we no longer have to define boolean algebras before equivalences are available.
This relates to [#4758](https://github.com/leanprover-community/mathlib/pull/4758).
#### Estimated changes
Modified src/algebra/group/ulift.lean


Modified src/data/equiv/basic.lean
- \- *lemma* dite_comp_equiv_update
- \- *theorem* equiv.apply_of_injective_symm
- \- *lemma* equiv.eq_image_iff_symm_image_eq
- \- *lemma* equiv.eq_preimage_iff_image_eq
- \- *def* equiv.image
- \- *lemma* equiv.image_eq_iff_eq
- \- *lemma* equiv.image_preimage
- \- *lemma* equiv.image_subset
- \- *lemma* equiv.image_symm_image
- \- *theorem* equiv.of_injective_symm_apply
- \- *abbreviation* equiv.of_left_inverse'
- \- *lemma* equiv.of_left_inverse'_eq_of_injective
- \- *def* equiv.of_left_inverse
- \- *lemma* equiv.of_left_inverse_eq_of_injective
- \- *lemma* equiv.preimage_eq_iff_eq_image
- \- *lemma* equiv.preimage_image
- \- *lemma* equiv.preimage_subset
- \- *lemma* equiv.preimage_symm_preimage
- \- *lemma* equiv.prod_assoc_preimage
- \- *lemma* equiv.range_eq_univ
- \- *lemma* equiv.self_comp_of_injective_symm
- \- *lemma* equiv.set.image_symm_preimage
- \- *lemma* equiv.set.insert_apply_left
- \- *lemma* equiv.set.insert_apply_right
- \- *lemma* equiv.set.insert_symm_apply_inl
- \- *lemma* equiv.set.insert_symm_apply_inr
- \- *lemma* equiv.set.sum_compl_apply_inl
- \- *lemma* equiv.set.sum_compl_apply_inr
- \- *lemma* equiv.set.sum_compl_symm_apply
- \- *lemma* equiv.set.sum_compl_symm_apply_compl
- \- *lemma* equiv.set.sum_compl_symm_apply_of_mem
- \- *lemma* equiv.set.sum_compl_symm_apply_of_not_mem
- \- *lemma* equiv.set.sum_diff_subset_apply_inl
- \- *lemma* equiv.set.sum_diff_subset_apply_inr
- \- *lemma* equiv.set.sum_diff_subset_symm_apply_of_mem
- \- *lemma* equiv.set.sum_diff_subset_symm_apply_of_not_mem
- \- *lemma* equiv.set.union_apply_left
- \- *lemma* equiv.set.union_apply_right
- \- *lemma* equiv.set.union_symm_apply_left
- \- *lemma* equiv.set.union_symm_apply_right
- \- *def* equiv.set_congr
- \- *def* equiv.set_prod_equiv_sigma
- \- *lemma* equiv.symm_image_image
- \- *lemma* equiv.symm_preimage_preimage
- \- *lemma* set.image_equiv_eq_preimage_symm
- \- *lemma* set.mem_image_equiv
- \- *lemma* set.preimage_equiv_eq_image_symm

Modified src/data/equiv/local_equiv.lean


Modified src/data/equiv/mul_add.lean


Added src/data/equiv/set.lean
- \+ *lemma* dite_comp_equiv_update
- \+ *theorem* equiv.apply_of_injective_symm
- \+ *lemma* equiv.eq_image_iff_symm_image_eq
- \+ *lemma* equiv.eq_preimage_iff_image_eq
- \+ *def* equiv.image
- \+ *lemma* equiv.image_eq_iff_eq
- \+ *lemma* equiv.image_preimage
- \+ *lemma* equiv.image_subset
- \+ *lemma* equiv.image_symm_image
- \+ *theorem* equiv.of_injective_symm_apply
- \+ *abbreviation* equiv.of_left_inverse'
- \+ *lemma* equiv.of_left_inverse'_eq_of_injective
- \+ *def* equiv.of_left_inverse
- \+ *lemma* equiv.of_left_inverse_eq_of_injective
- \+ *lemma* equiv.preimage_eq_iff_eq_image
- \+ *lemma* equiv.preimage_image
- \+ *lemma* equiv.preimage_subset
- \+ *lemma* equiv.preimage_symm_preimage
- \+ *lemma* equiv.prod_assoc_preimage
- \+ *lemma* equiv.range_eq_univ
- \+ *lemma* equiv.self_comp_of_injective_symm
- \+ *lemma* equiv.set.image_symm_preimage
- \+ *lemma* equiv.set.insert_apply_left
- \+ *lemma* equiv.set.insert_apply_right
- \+ *lemma* equiv.set.insert_symm_apply_inl
- \+ *lemma* equiv.set.insert_symm_apply_inr
- \+ *lemma* equiv.set.sum_compl_apply_inl
- \+ *lemma* equiv.set.sum_compl_apply_inr
- \+ *lemma* equiv.set.sum_compl_symm_apply
- \+ *lemma* equiv.set.sum_compl_symm_apply_compl
- \+ *lemma* equiv.set.sum_compl_symm_apply_of_mem
- \+ *lemma* equiv.set.sum_compl_symm_apply_of_not_mem
- \+ *lemma* equiv.set.sum_diff_subset_apply_inl
- \+ *lemma* equiv.set.sum_diff_subset_apply_inr
- \+ *lemma* equiv.set.sum_diff_subset_symm_apply_of_mem
- \+ *lemma* equiv.set.sum_diff_subset_symm_apply_of_not_mem
- \+ *lemma* equiv.set.union_apply_left
- \+ *lemma* equiv.set.union_apply_right
- \+ *lemma* equiv.set.union_symm_apply_left
- \+ *lemma* equiv.set.union_symm_apply_right
- \+ *def* equiv.set_congr
- \+ *def* equiv.set_prod_equiv_sigma
- \+ *lemma* equiv.symm_image_image
- \+ *lemma* equiv.symm_preimage_preimage
- \+ *lemma* set.image_equiv_eq_preimage_symm
- \+ *lemma* set.mem_image_equiv
- \+ *lemma* set.preimage_equiv_eq_image_symm

Modified src/data/part.lean


Modified src/logic/embedding.lean


Modified src/logic/small.lean


Modified src/order/order_dual.lean


Modified src/order/rel_iso.lean




## [2021-10-06 15:46:04](https://github.com/leanprover-community/mathlib/commit/0b356b0)
feat(analysis/normed_space/banach): open mapping theorem for maps between affine spaces ([#9540](https://github.com/leanprover-community/mathlib/pull/9540))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* open_mapping_affine

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.surjective_iff_linear_surjective



## [2021-10-06 15:46:03](https://github.com/leanprover-community/mathlib/commit/5773bc6)
feat(group_theory/group_action/conj_act): conjugation action of groups ([#8627](https://github.com/leanprover-community/mathlib/pull/8627))
#### Estimated changes
Modified src/data/equiv/mul_add_aut.lean


Added src/group_theory/group_action/conj_act.lean
- \+ *lemma* conj_act.card
- \+ *lemma* conj_act.fixed_points_eq_center
- \+ *def* conj_act.of_conj_act
- \+ *lemma* conj_act.of_conj_act_inv
- \+ *lemma* conj_act.of_conj_act_mul
- \+ *lemma* conj_act.of_conj_act_one
- \+ *lemma* conj_act.of_conj_act_to_conj_act
- \+ *lemma* conj_act.of_conj_act_zero
- \+ *lemma* conj_act.of_mul_symm_eq
- \+ *lemma* conj_act.smul_def
- \+ *lemma* conj_act.smul_eq_mul_aut_conj
- \+ *def* conj_act.to_conj_act
- \+ *lemma* conj_act.to_conj_act_inv
- \+ *lemma* conj_act.to_conj_act_mul
- \+ *lemma* conj_act.to_conj_act_of_conj_act
- \+ *lemma* conj_act.to_conj_act_one
- \+ *lemma* conj_act.to_conj_act_zero
- \+ *lemma* conj_act.to_mul_symm_eq
- \+ *lemma* conj_act.«forall»
- \+ *def* conj_act



## [2021-10-06 14:53:28](https://github.com/leanprover-community/mathlib/commit/6abd6f2)
chore(ring_theory/witt_vector): fix a docstring ([#9575](https://github.com/leanprover-community/mathlib/pull/9575))
#### Estimated changes
Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-10-06 13:44:03](https://github.com/leanprover-community/mathlib/commit/850d5d2)
feat(analysis/convex/function): Dual lemmas ([#9571](https://github.com/leanprover-community/mathlib/pull/9571))
#### Estimated changes
Modified src/analysis/convex/function.lean
- \+ *lemma* concave_on.convex_gt
- \- *lemma* concave_on.convex_lt
- \+ *lemma* concave_on.dual
- \+ *lemma* concave_on.ge_on_segment'
- \+ *lemma* concave_on.ge_on_segment
- \- *lemma* concave_on.le_on_segment'
- \- *lemma* concave_on.le_on_segment
- \+/\- *lemma* concave_on.smul
- \+ *lemma* convex_on.dual
- \+/\- *lemma* convex_on.smul
- \+ *lemma* strict_concave_on.dual
- \+ *lemma* strict_convex_on.dual



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
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified archive/imo/imo1977_q6.lean


Modified archive/imo/imo1998_q2.lean


Modified archive/oxford_invariants/2021summer/week3_p1.lean


Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/intervals.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/pointwise.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/combinatorics/composition.lean


Modified src/combinatorics/derangements/exponential.lean


Modified src/combinatorics/derangements/finite.lean


Modified src/computability/DFA.lean


Modified src/computability/turing_machine.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/fin.lean


Modified src/data/fin.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/intervals.lean


Modified src/data/finset/sort.lean


Modified src/data/list/basic.lean


Modified src/data/list/cycle.lean


Modified src/data/list/intervals.lean


Modified src/data/list/perm.lean


Modified src/data/list/rotate.lean


Modified src/data/matrix/notation.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean
- \- *theorem* nat.sub_cancel
- \- *theorem* nat.sub_sub_assoc
- \- *lemma* nat.sub_sub_sub_cancel_right

Modified src/data/nat/choose/basic.lean


Modified src/data/nat/dist.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/nat/interval.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/nat/upto.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/polynomial/hasse_deriv.lean


Modified src/data/polynomial/mirror.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/list.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/admissible_card_pow_degree.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/iterate.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/set_theory/game/state.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.add_sub_cancel_of_le

Modified src/set_theory/ordinal_notation.lean


Modified src/system/random/basic.lean


Modified src/tactic/omega/coeffs.lean


Modified src/testing/slim_check/gen.lean


Modified src/testing/slim_check/sampleable.lean


Modified test/general_recursion.lean




## [2021-10-06 10:12:00](https://github.com/leanprover-community/mathlib/commit/facc1d2)
feat(topology/algebra): topology on a linear_ordered_comm_group_with_zero ([#9537](https://github.com/leanprover-community/mathlib/pull/9537))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
Modified src/algebra/order/with_zero.lean
- \+ *lemma* inv_mul_lt_of_lt_mul₀

Added src/topology/algebra/with_zero_topology.lean
- \+ *lemma* linear_ordered_comm_group_with_zero.directed_lt
- \+ *lemma* linear_ordered_comm_group_with_zero.has_basis_nhds_of_ne_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.has_basis_nhds_units
- \+ *lemma* linear_ordered_comm_group_with_zero.has_basis_nhds_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.nhds_coe_units
- \+ *def* linear_ordered_comm_group_with_zero.nhds_fun
- \+ *lemma* linear_ordered_comm_group_with_zero.nhds_fun_ok
- \+ *lemma* linear_ordered_comm_group_with_zero.nhds_of_ne_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.nhds_zero_of_ne_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.nhds_zero_of_units
- \+ *lemma* linear_ordered_comm_group_with_zero.pure_le_nhds_fun
- \+ *lemma* linear_ordered_comm_group_with_zero.singleton_nhds_of_ne_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.singleton_nhds_of_units
- \+ *lemma* linear_ordered_comm_group_with_zero.tendsto_of_ne_zero
- \+ *lemma* linear_ordered_comm_group_with_zero.tendsto_units
- \+ *lemma* linear_ordered_comm_group_with_zero.tendsto_zero

Modified src/topology/basic.lean
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
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/inner_product_space/dual.lean
- \- *def* inner_product_space.isometric.to_dual
- \- *lemma* inner_product_space.ker_to_dual_map
- \- *lemma* inner_product_space.norm_to_dual_apply
- \- *lemma* inner_product_space.norm_to_dual_map_apply
- \- *lemma* inner_product_space.norm_to_dual_symm_apply
- \- *lemma* inner_product_space.range_to_dual_map
- \+/\- *def* inner_product_space.to_dual
- \+/\- *lemma* inner_product_space.to_dual_apply
- \- *lemma* inner_product_space.to_dual_eq_iff_eq'
- \- *lemma* inner_product_space.to_dual_eq_iff_eq
- \+/\- *def* inner_product_space.to_dual_map
- \+/\- *lemma* inner_product_space.to_dual_map_apply
- \- *lemma* inner_product_space.to_dual_map_eq_iff_eq
- \- *lemma* inner_product_space.to_dual_map_injective
- \- *lemma* inner_product_space.to_dual_map_isometry

Modified src/analysis/normed_space/dual.lean
- \- *lemma* normed_space.inclusion_in_double_dual_isometry
- \+ *def* normed_space.inclusion_in_double_dual_li

Modified src/analysis/normed_space/linear_isometry.lean




## [2021-10-06 08:03:56](https://github.com/leanprover-community/mathlib/commit/e52e533)
feat(order/bounds): Antitone lemmas ([#9556](https://github.com/leanprover-community/mathlib/pull/9556))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* antitone.image_lower_bounds_subset_upper_bounds_image
- \+ *lemma* antitone.image_upper_bounds_subset_lower_bounds_image
- \+ *lemma* antitone.is_lub_image_le
- \+ *lemma* antitone.le_is_glb_image
- \+ *lemma* antitone.map_bdd_above
- \+ *lemma* antitone.map_bdd_below
- \+ *lemma* antitone.map_is_greatest
- \+ *lemma* antitone.map_is_least
- \+ *lemma* antitone.mem_lower_bounds_image
- \+ *lemma* antitone.mem_upper_bounds_image



## [2021-10-06 06:05:04](https://github.com/leanprover-community/mathlib/commit/f811910)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are 1 in zero dimensions ([#9564](https://github.com/leanprover-community/mathlib/pull/9564))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_of_univ_subsingleton
- \+ *lemma* set.subsingleton_univ_iff

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.subsingleton_of_subsingleton_span_eq_top

Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* coe_barycentric_coord_of_subsingleton_eq_one



## [2021-10-06 01:36:04](https://github.com/leanprover-community/mathlib/commit/db5ee76)
chore(linear_algebra/quadratic_form): squeeze simps ([#9572](https://github.com/leanprover-community/mathlib/pull/9572))
[#9567](https://github.com/leanprover-community/mathlib/pull/9567) speeds up the slowest declaration in the file, but many other declarations are also slow.
This PR squeezes all simps.
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean




## [2021-10-05 21:57:44](https://github.com/leanprover-community/mathlib/commit/fdf8a71)
feat(topology/bases): a family of nonempty disjoint open sets is countable in a separable space ([#9557](https://github.com/leanprover-community/mathlib/pull/9557))
Together with unrelated small lemmas on balls and on `pairwise_on`.
#### Estimated changes
Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/data/real/ennreal.lean
- \+ *theorem* ennreal.exists_le_of_sum_le
- \+ *theorem* ennreal.sum_lt_sum_of_nonempty

Modified src/data/set/basic.lean
- \+ *lemma* set.pairwise_on_disjoint_on_mono

Modified src/data/set/lattice.lean
- \+ *lemma* set.pairwise_on_Union

Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/bases.lean
- \+ *lemma* topological_space.countable_of_is_open_of_disjoint
- \+ *lemma* topological_space.countable_of_nonempty_interior_of_disjoint

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* emetric.disjoint_closed_ball_of_lt_inf_edist
- \+ *lemma* is_closed.Hausdorff_dist_zero_iff_eq
- \+ *lemma* is_closed.mem_iff_inf_dist_zero
- \+ *lemma* is_closed.not_mem_iff_inf_dist_pos
- \- *lemma* metric.Hausdorff_dist_zero_iff_eq_of_closed
- \+ *lemma* metric.disjoint_closed_ball_of_lt_inf_dist
- \- *lemma* metric.mem_iff_inf_dist_zero_of_closed



## [2021-10-05 21:57:43](https://github.com/leanprover-community/mathlib/commit/815eaca)
feat(analysis/normed_space/affine_isometry): affine maps are open iff their underlying linear maps are ([#9538](https://github.com/leanprover-community/mathlib/pull/9538))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/normed_space/affine_isometry.lean
- \+ *lemma* affine_map.is_open_map_linear_iff

Modified src/topology/algebra/affine.lean


Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.comp_is_open_map_iff'
- \+ *lemma* homeomorph.comp_is_open_map_iff



## [2021-10-05 19:53:22](https://github.com/leanprover-community/mathlib/commit/63903f2)
doc(linear_algebra/free_module/strong_rank_condition): correct a typo ([#9565](https://github.com/leanprover-community/mathlib/pull/9565))
#### Estimated changes
Modified src/linear_algebra/free_module/strong_rank_condition.lean




## [2021-10-05 19:53:21](https://github.com/leanprover-community/mathlib/commit/0b57520)
feat(order/bounds): Image under an `order_iso` and `upper_bounds` commute ([#9555](https://github.com/leanprover-community/mathlib/pull/9555))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* monotone.image_lower_bounds_subset_lower_bounds_image
- \+ *lemma* monotone.image_upper_bounds_subset_upper_bounds_image
- \+/\- *lemma* order_iso.is_glb_image'
- \+/\- *lemma* order_iso.is_glb_image
- \+/\- *lemma* order_iso.is_glb_preimage'
- \+/\- *lemma* order_iso.is_glb_preimage
- \+/\- *lemma* order_iso.is_lub_image'
- \+/\- *lemma* order_iso.is_lub_image
- \+/\- *lemma* order_iso.is_lub_preimage'
- \+/\- *lemma* order_iso.is_lub_preimage
- \+ *lemma* order_iso.lower_bounds_image
- \+ *lemma* order_iso.upper_bounds_image

Modified src/order/galois_connection.lean
- \- *lemma* order_iso.lower_bounds_image
- \- *lemma* order_iso.upper_bounds_image



## [2021-10-05 19:53:20](https://github.com/leanprover-community/mathlib/commit/111d73b)
feat(data/int/interval): Finite intervals in ℤ ([#9526](https://github.com/leanprover-community/mathlib/pull/9526))
This proves that `ℤ` is a locally finite order.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *def* nat.cast_embedding

Added src/data/int/interval.lean
- \+ *lemma* int.Icc_eq_finset_map
- \+ *lemma* int.Ioc_eq_finset_map
- \+ *lemma* int.Ioo_eq_finset_map
- \+ *lemma* int.card_Icc
- \+ *lemma* int.card_Icc_of_le
- \+ *lemma* int.card_Ioc
- \+ *lemma* int.card_Ioc_of_le
- \+ *lemma* int.card_Ioo
- \+ *lemma* int.card_Ioo_of_lt
- \+ *lemma* int.card_fintype_Icc
- \+ *lemma* int.card_fintype_Icc_of_le
- \+ *lemma* int.card_fintype_Ioc
- \+ *lemma* int.card_fintype_Ioc_of_le
- \+ *lemma* int.card_fintype_Ioo
- \+ *lemma* int.card_fintype_Ioo_of_lt



## [2021-10-05 17:44:36](https://github.com/leanprover-community/mathlib/commit/7455f47)
chore(linear_algebra/quadratic_form): speed up quadratic_form.lin_mul_lin ([#9567](https://github.com/leanprover-community/mathlib/pull/9567))
In my single profiler run, this reduced elaboration time from 20s to 1.5s.
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean




## [2021-10-05 11:41:22](https://github.com/leanprover-community/mathlib/commit/5926f10)
fix(data/equiv/basic): use `subtype p` not `coe_sort (set_of p)` ([#9559](https://github.com/leanprover-community/mathlib/pull/9559))
`↥{x | p x}` is just a clumsy way to write `{x // p x}`.
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2021-10-05 10:10:30](https://github.com/leanprover-community/mathlib/commit/da4d550)
chore(measure_theory/*): better names and notations, add easy lemmas ([#9554](https://github.com/leanprover-community/mathlib/pull/9554))
* Localize notation for absolutely continuous in the `measure_theory` namespace, and add separate notations for the case of measures and of vector measures.
* Standardize some names, using `measure` instead of `meas`.
* Add two lemmas on measures with density.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* meas_closure_of_null_bdry
- \- *lemma* meas_interior_of_null_bdry
- \+ *lemma* measure_closure_of_null_bdry
- \+ *lemma* measure_interior_of_null_bdry

Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/radon_nikodym.lean


Modified src/measure_theory/function/ess_sup.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.exists_absolutely_continuous_is_finite_measure
- \+ *lemma* measure_theory.with_density_mul
- \+ *lemma* measure_theory.with_density_one

Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.meas_eq_meas_larger_of_between_null_diff
- \- *lemma* measure_theory.meas_eq_meas_of_between_null_diff
- \- *lemma* measure_theory.meas_eq_meas_of_null_diff
- \- *lemma* measure_theory.meas_eq_meas_smaller_of_between_null_diff
- \+ *lemma* measure_theory.measure_diff_le_iff_le_add
- \+ *lemma* measure_theory.measure_eq_measure_larger_of_between_null_diff
- \+ *lemma* measure_theory.measure_eq_measure_of_between_null_diff
- \+ *lemma* measure_theory.measure_eq_measure_of_null_diff
- \+ *lemma* measure_theory.measure_eq_measure_smaller_of_between_null_diff

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.measure_Union_fintype_le

Modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.eq
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.map
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.mk
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.refl
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.trans
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.zero

Modified src/measure_theory/measure/with_density_vector_measure.lean




## [2021-10-05 10:10:29](https://github.com/leanprover-community/mathlib/commit/e7ea02f)
feat(analysis/convex/basic): Levels of a monotone/antitone function ([#9547](https://github.com/leanprover-community/mathlib/pull/9547))
The set of points whose image under a monotone function is less than a fixed value is convex, when the space is linear.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* antitone.convex_ge
- \+ *lemma* antitone.convex_gt
- \+ *lemma* antitone.convex_le
- \+ *lemma* antitone.convex_lt
- \+ *lemma* antitone_on.convex_ge
- \+ *lemma* antitone_on.convex_gt
- \+ *lemma* antitone_on.convex_le
- \+ *lemma* antitone_on.convex_lt
- \+ *lemma* convex.combo_le_max
- \+ *lemma* convex.min_le_combo
- \+ *lemma* monotone.convex_ge
- \+ *lemma* monotone.convex_gt
- \+ *lemma* monotone.convex_le
- \+ *lemma* monotone.convex_lt
- \+ *lemma* monotone_on.convex_ge
- \+ *lemma* monotone_on.convex_gt
- \+ *lemma* monotone_on.convex_le
- \+ *lemma* monotone_on.convex_lt
- \+ *lemma* segment_subset_interval



## [2021-10-05 10:10:28](https://github.com/leanprover-community/mathlib/commit/5b79319)
feat(ring_theory/polynomial/basic): add a lemma `polynomial_quotient_equiv_quotient_polynomial_map_mk` ([#9542](https://github.com/leanprover-community/mathlib/pull/9542))
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk
- \+ *lemma* ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk



## [2021-10-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/2666033)
refactor(algebra/gcd_monoid): don't require normalization ([#9443](https://github.com/leanprover-community/mathlib/pull/9443))
This will allow us to set up a gcd_monoid instance for all euclidean_domains and generalize the results in ring_theory/euclidean_domain.lean to PIDs.
#### Estimated changes
Modified docs/overview.yaml


Modified src/algebra/associated.lean
- \+ *lemma* associated_mul_unit_left
- \+ *lemma* associated_mul_unit_right
- \+ *lemma* associated_unit_mul_left
- \+ *lemma* associated_unit_mul_right
- \+ *lemma* units_eq_one

Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *theorem* associated.gcd_eq_left
- \+/\- *theorem* associated.gcd_eq_right
- \+/\- *theorem* dvd_gcd_iff
- \+/\- *lemma* dvd_gcd_mul_of_dvd_mul
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right
- \+/\- *lemma* dvd_mul_gcd_of_dvd_mul
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow
- \+/\- *lemma* exists_dvd_and_dvd_of_dvd_mul
- \+ *theorem* gcd_assoc'
- \+/\- *theorem* gcd_assoc
- \+ *theorem* gcd_comm'
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_dvd_gcd
- \+/\- *theorem* gcd_dvd_gcd_mul_left
- \+/\- *theorem* gcd_dvd_gcd_mul_left_right
- \+/\- *theorem* gcd_dvd_gcd_mul_right
- \+/\- *theorem* gcd_dvd_gcd_mul_right_right
- \+/\- *theorem* gcd_eq_left_iff
- \+/\- *theorem* gcd_eq_normalize
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* gcd_eq_zero_iff
- \+/\- *theorem* gcd_monoid.irreducible_iff_prime
- \+/\- *theorem* gcd_monoid.prime_of_irreducible
- \+/\- *theorem* gcd_mul_dvd_mul_gcd
- \+/\- *theorem* gcd_mul_lcm
- \+ *theorem* gcd_mul_left'
- \+/\- *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right'
- \+/\- *theorem* gcd_mul_right
- \+ *theorem* gcd_one_left'
- \+/\- *theorem* gcd_one_left
- \+ *theorem* gcd_one_right'
- \+/\- *theorem* gcd_one_right
- \+/\- *theorem* gcd_pow_left_dvd_pow_gcd
- \+/\- *theorem* gcd_pow_right_dvd_pow_gcd
- \+/\- *theorem* gcd_same
- \+ *theorem* gcd_zero_left'
- \+/\- *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_right'
- \+/\- *theorem* gcd_zero_right
- \+ *theorem* lcm_assoc'
- \+/\- *theorem* lcm_assoc
- \+ *theorem* lcm_comm'
- \+/\- *theorem* lcm_comm
- \+/\- *lemma* lcm_dvd
- \+/\- *lemma* lcm_dvd_iff
- \+/\- *theorem* lcm_dvd_lcm
- \+/\- *theorem* lcm_dvd_lcm_mul_left
- \+/\- *theorem* lcm_dvd_lcm_mul_left_right
- \+/\- *theorem* lcm_dvd_lcm_mul_right
- \+/\- *theorem* lcm_dvd_lcm_mul_right_right
- \+/\- *theorem* lcm_eq_left_iff
- \+/\- *lemma* lcm_eq_normalize
- \+/\- *theorem* lcm_eq_of_associated_left
- \+/\- *theorem* lcm_eq_of_associated_right
- \+/\- *theorem* lcm_eq_one_iff
- \+/\- *theorem* lcm_eq_right_iff
- \+/\- *theorem* lcm_eq_zero_iff
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* normalize_gcd
- \+/\- *lemma* normalize_lcm
- \+/\- *theorem* pow_dvd_of_mul_eq_pow
- \- *lemma* units_eq_one

Modified src/algebra/gcd_monoid/finset.lean


Modified src/algebra/gcd_monoid/multiset.lean


Modified src/field_theory/minpoly.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* associates.coprime_iff_inf_one
- \+/\- *theorem* associates.count_mul
- \+/\- *theorem* associates.count_mul_of_coprime'
- \+/\- *theorem* associates.count_mul_of_coprime
- \+/\- *theorem* associates.count_of_coprime
- \+/\- *lemma* associates.count_pow
- \+/\- *theorem* associates.dvd_count_of_dvd_count_mul
- \+/\- *theorem* associates.dvd_count_pow
- \+/\- *theorem* associates.eq_of_prod_eq_prod
- \+/\- *theorem* associates.eq_pow_of_mul_eq_pow
- \+/\- *theorem* associates.factors_le
- \+/\- *theorem* associates.factors_mono
- \+/\- *theorem* associates.factors_mul
- \+/\- *lemma* associates.factors_one
- \+/\- *theorem* associates.factors_prime_pow
- \+/\- *theorem* associates.is_pow_of_dvd_count
- \+/\- *theorem* associates.le_of_count_ne_zero
- \+/\- *theorem* associates.pow_factors
- \+/\- *theorem* associates.prime_pow_dvd_iff_le
- \+/\- *theorem* associates.prod_factors
- \+/\- *theorem* associates.prod_le
- \+/\- *theorem* associates.prod_le_prod_iff_le
- \+ *lemma* associates.quot_out
- \+/\- *lemma* associates.sup_mul_inf
- \+ *lemma* unique_factorization_monoid.exists_mem_factors_of_dvd
- \+ *theorem* unique_factorization_monoid.factors_prod
- \+ *theorem* unique_factorization_monoid.irreducible_of_factor
- \+/\- *lemma* unique_factorization_monoid.normalized_factors_zero
- \+ *theorem* unique_factorization_monoid.prime_of_factor



## [2021-10-05 08:58:55](https://github.com/leanprover-community/mathlib/commit/def4814)
refactor(topology/algebra/module): continuous semilinear maps ([#9539](https://github.com/leanprover-community/mathlib/pull/9539))
Generalize the theory of continuous linear maps to the semilinear setting.
We introduce a notation `∘L` for composition of continuous linear (i.e., not semilinear) maps, used sporadically to help with unification.  See [#8857](https://github.com/leanprover-community/mathlib/pull/8857) for a discussion of a related problem and fix.
#### Estimated changes
Modified src/analysis/complex/conformal.lean


Modified src/analysis/normed_space/complemented.lean


Modified src/topology/algebra/module.lean
- \+/\- *theorem* continuous_linear_equiv.apply_symm_apply
- \+/\- *theorem* continuous_linear_equiv.bijective
- \+/\- *theorem* continuous_linear_equiv.coe_apply
- \+/\- *lemma* continuous_linear_equiv.coe_coe
- \+/\- *theorem* continuous_linear_equiv.coe_comp_coe_symm
- \+/\- *theorem* continuous_linear_equiv.coe_def_rev
- \+/\- *lemma* continuous_linear_equiv.coe_inj
- \+/\- *lemma* continuous_linear_equiv.coe_injective
- \+/\- *lemma* continuous_linear_equiv.coe_prod
- \+/\- *theorem* continuous_linear_equiv.coe_symm_comp_coe
- \+/\- *lemma* continuous_linear_equiv.coe_to_homeomorph
- \+/\- *lemma* continuous_linear_equiv.coe_to_linear_equiv
- \+/\- *lemma* continuous_linear_equiv.comp_coe
- \+/\- *lemma* continuous_linear_equiv.eq_symm_apply
- \+/\- *def* continuous_linear_equiv.equiv_of_inverse
- \+/\- *lemma* continuous_linear_equiv.equiv_of_inverse_apply
- \+/\- *lemma* continuous_linear_equiv.ext
- \+/\- *lemma* continuous_linear_equiv.ext₁
- \+/\- *lemma* continuous_linear_equiv.image_closure
- \+/\- *theorem* continuous_linear_equiv.image_symm_image
- \+/\- *theorem* continuous_linear_equiv.injective
- \+/\- *lemma* continuous_linear_equiv.is_closed_image
- \+/\- *lemma* continuous_linear_equiv.map_add
- \+/\- *lemma* continuous_linear_equiv.map_eq_zero_iff
- \+/\- *lemma* continuous_linear_equiv.map_neg
- \+/\- *lemma* continuous_linear_equiv.map_nhds_eq
- \+/\- *lemma* continuous_linear_equiv.map_smul
- \+ *lemma* continuous_linear_equiv.map_smulₛₗ
- \+/\- *lemma* continuous_linear_equiv.map_sub
- \+/\- *lemma* continuous_linear_equiv.map_zero
- \+/\- *lemma* continuous_linear_equiv.preimage_closure
- \+/\- *def* continuous_linear_equiv.prod
- \+/\- *lemma* continuous_linear_equiv.prod_apply
- \+/\- *lemma* continuous_linear_equiv.self_comp_symm
- \+/\- *theorem* continuous_linear_equiv.surjective
- \+/\- *theorem* continuous_linear_equiv.symm_apply_apply
- \+/\- *lemma* continuous_linear_equiv.symm_apply_eq
- \+/\- *lemma* continuous_linear_equiv.symm_comp_self
- \+/\- *lemma* continuous_linear_equiv.symm_equiv_of_inverse
- \+/\- *theorem* continuous_linear_equiv.symm_image_image
- \+/\- *lemma* continuous_linear_equiv.symm_map_nhds_eq
- \+/\- *theorem* continuous_linear_equiv.symm_symm
- \+/\- *theorem* continuous_linear_equiv.symm_symm_apply
- \+/\- *lemma* continuous_linear_equiv.symm_to_homeomorph
- \+/\- *lemma* continuous_linear_equiv.symm_to_linear_equiv
- \+/\- *theorem* continuous_linear_equiv.symm_trans_apply
- \+/\- *def* continuous_linear_equiv.to_continuous_linear_map
- \+/\- *def* continuous_linear_equiv.to_homeomorph
- \+/\- *lemma* continuous_linear_equiv.to_linear_equiv_injective
- \+/\- *theorem* continuous_linear_equiv.trans_apply
- \+/\- *lemma* continuous_linear_equiv.trans_to_linear_equiv
- \+/\- *def* continuous_linear_map.cod_restrict
- \+/\- *lemma* continuous_linear_map.coe_add'
- \+/\- *lemma* continuous_linear_map.coe_add
- \+/\- *lemma* continuous_linear_map.coe_cod_restrict
- \+/\- *lemma* continuous_linear_map.coe_cod_restrict_apply
- \+/\- *lemma* continuous_linear_map.coe_coe
- \+/\- *lemma* continuous_linear_map.coe_comp'
- \+/\- *lemma* continuous_linear_map.coe_comp
- \+/\- *lemma* continuous_linear_map.coe_coprod
- \+/\- *lemma* continuous_linear_map.coe_eq_id
- \+/\- *theorem* continuous_linear_map.coe_fn_injective
- \+/\- *lemma* continuous_linear_map.coe_fst'
- \+/\- *lemma* continuous_linear_map.coe_fst
- \+/\- *lemma* continuous_linear_map.coe_id'
- \+/\- *lemma* continuous_linear_map.coe_id
- \+/\- *lemma* continuous_linear_map.coe_inj
- \+/\- *theorem* continuous_linear_map.coe_injective
- \+/\- *lemma* continuous_linear_map.coe_inl
- \+/\- *lemma* continuous_linear_map.coe_inr
- \+/\- *lemma* continuous_linear_map.coe_mk'
- \+/\- *lemma* continuous_linear_map.coe_mk
- \+/\- *lemma* continuous_linear_map.coe_mul
- \+/\- *lemma* continuous_linear_map.coe_neg'
- \+/\- *lemma* continuous_linear_map.coe_neg
- \+/\- *lemma* continuous_linear_map.coe_prod
- \+/\- *lemma* continuous_linear_map.coe_prod_map'
- \+/\- *lemma* continuous_linear_map.coe_prod_map
- \+/\- *lemma* continuous_linear_map.coe_snd'
- \+/\- *lemma* continuous_linear_map.coe_snd
- \+/\- *lemma* continuous_linear_map.coe_sub'
- \+/\- *lemma* continuous_linear_map.coe_sub
- \+/\- *lemma* continuous_linear_map.coe_subtype_val
- \+/\- *lemma* continuous_linear_map.coe_sum'
- \+/\- *lemma* continuous_linear_map.coe_sum
- \+/\- *lemma* continuous_linear_map.coe_zero'
- \+/\- *lemma* continuous_linear_map.coe_zero
- \+/\- *def* continuous_linear_map.comp
- \+/\- *lemma* continuous_linear_map.comp_apply
- \+/\- *theorem* continuous_linear_map.comp_assoc
- \+/\- *theorem* continuous_linear_map.comp_id
- \+/\- *theorem* continuous_linear_map.comp_zero
- \+/\- *def* continuous_linear_map.coprod
- \+/\- *lemma* continuous_linear_map.coprod_apply
- \+/\- *lemma* continuous_linear_map.default_def
- \+/\- *lemma* continuous_linear_map.eq_on_closure_span
- \+/\- *theorem* continuous_linear_map.ext
- \+/\- *theorem* continuous_linear_map.ext_iff
- \+/\- *lemma* continuous_linear_map.ext_on
- \+/\- *theorem* continuous_linear_map.ext_ring
- \+/\- *theorem* continuous_linear_map.ext_ring_iff
- \+/\- *def* continuous_linear_map.fst
- \+/\- *lemma* continuous_linear_map.fst_comp_prod
- \+/\- *lemma* continuous_linear_map.fst_prod_snd
- \+/\- *def* continuous_linear_map.id
- \+/\- *lemma* continuous_linear_map.id_apply
- \+/\- *theorem* continuous_linear_map.id_comp
- \+/\- *def* continuous_linear_map.inl
- \+/\- *lemma* continuous_linear_map.inl_apply
- \+/\- *def* continuous_linear_map.inr
- \+/\- *lemma* continuous_linear_map.inr_apply
- \+/\- *lemma* continuous_linear_map.is_closed_ker
- \+/\- *def* continuous_linear_map.ker
- \+/\- *lemma* continuous_linear_map.ker_cod_restrict
- \+/\- *lemma* continuous_linear_map.ker_coe
- \+/\- *lemma* continuous_linear_map.ker_prod
- \+/\- *lemma* continuous_linear_map.map_smul
- \+/\- *lemma* continuous_linear_map.map_smul_of_tower
- \+ *lemma* continuous_linear_map.map_smulₛₗ
- \+/\- *lemma* continuous_linear_map.map_sum
- \+/\- *lemma* continuous_linear_map.map_zero
- \+/\- *lemma* continuous_linear_map.mem_ker
- \+/\- *lemma* continuous_linear_map.mem_range
- \+/\- *lemma* continuous_linear_map.mem_range_self
- \+/\- *lemma* continuous_linear_map.mul_apply
- \+/\- *lemma* continuous_linear_map.mul_def
- \+/\- *lemma* continuous_linear_map.one_apply
- \+/\- *lemma* continuous_linear_map.one_def
- \+/\- *lemma* continuous_linear_map.prod_apply
- \+/\- *def* continuous_linear_map.prod_map
- \+/\- *def* continuous_linear_map.proj_ker_of_right_inverse
- \+/\- *def* continuous_linear_map.range
- \+/\- *lemma* continuous_linear_map.range_coe
- \+/\- *lemma* continuous_linear_map.range_coprod
- \+/\- *lemma* continuous_linear_map.range_prod_eq
- \+/\- *lemma* continuous_linear_map.range_prod_le
- \+/\- *def* continuous_linear_map.smul_right
- \+/\- *lemma* continuous_linear_map.smul_right_apply
- \+/\- *lemma* continuous_linear_map.smul_right_comp
- \+/\- *lemma* continuous_linear_map.smul_right_one_one
- \+/\- *def* continuous_linear_map.snd
- \+/\- *lemma* continuous_linear_map.snd_comp_prod
- \+/\- *lemma* continuous_linear_map.sub_apply'
- \+/\- *def* continuous_linear_map.subtype_val
- \+/\- *lemma* continuous_linear_map.subtype_val_apply
- \+/\- *lemma* continuous_linear_map.sum_apply
- \+/\- *lemma* continuous_linear_map.to_linear_map_eq_coe
- \+/\- *lemma* continuous_linear_map.zero_apply
- \+/\- *theorem* continuous_linear_map.zero_comp
- \+/\- *lemma* dense_range.topological_closure_map_submodule
- \+/\- *lemma* submodule.topological_closure_map



## [2021-10-05 08:05:44](https://github.com/leanprover-community/mathlib/commit/fefd8a3)
refactor(analysis/convex/*): prove `convex_independent_iff_finset` without full Carathéodory ([#9550](https://github.com/leanprover-community/mathlib/pull/9550))
Also relax one `add_comm_group` to `add_comm_monoid` and two `𝕜` to `β` + `module 𝕜 β`, and simplify imports.
#### Estimated changes
Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on_id
- \+/\- *lemma* convex_on_id

Modified src/analysis/convex/independent.lean




## [2021-10-05 08:05:43](https://github.com/leanprover-community/mathlib/commit/c42786f)
feat(topology/algebra): adic topology ([#9521](https://github.com/leanprover-community/mathlib/pull/9521))
This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
Added src/topology/algebra/nonarchimedean/adic_topology.lean
- \+ *lemma* ideal.adic_basis
- \+ *lemma* ideal.adic_module_basis
- \+ *def* ideal.adic_module_topology
- \+ *def* ideal.adic_topology
- \+ *lemma* ideal.has_basis_nhds_adic
- \+ *lemma* ideal.has_basis_nhds_zero_adic
- \+ *lemma* ideal.nonarchimedean
- \+ *def* ideal.open_add_subgroup
- \+ *def* ideal.ring_filter_basis
- \+ *def* is_adic
- \+ *lemma* is_adic_iff
- \+ *lemma* is_bot_adic_iff
- \+ *lemma* is_ideal_adic_pow
- \+ *def* with_ideal.topological_space_module



## [2021-10-05 08:05:41](https://github.com/leanprover-community/mathlib/commit/61cd266)
ci(.github/workflows): automatically remove awaiting-CI label ([#9491](https://github.com/leanprover-community/mathlib/pull/9491))
This PR adds a job to our CI which removes the label "awaiting-CI" when the build finishes successfully.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/awaiting-CI.2C.20.23bors.2C.20and.20the.20PR.20.23queue/near/255754196)
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2021-10-05 03:31:26](https://github.com/leanprover-community/mathlib/commit/1536412)
refactor(data/polynomial): use `monic.ne_zero` and `nontriviality` ([#9530](https://github.com/leanprover-community/mathlib/pull/9530))
There is a pattern in `data/polynomial` to have both `(hq : q.monic) (hq0 : q ≠ 0)` as assumptions. I found this less convenient to work with than `[nontrivial R] (hq : q.monic)` and using `monic.ne_zero` to replace `hq0`.
The `nontriviality` tactic automates all the cases where previously `nontrivial R` (or similar) was manually derived from the hypotheses.
#### Estimated changes
Modified src/data/polynomial/div.lean
- \+/\- *lemma* polynomial.degree_mod_by_monic_lt
- \+/\- *lemma* polynomial.div_by_monic_eq_zero_iff
- \+/\- *lemma* polynomial.mod_by_monic_eq_self_iff

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/minpoly.lean


Modified src/ring_theory/power_basis.lean




## [2021-10-05 02:21:57](https://github.com/leanprover-community/mathlib/commit/fd18953)
chore(scripts): update nolints.txt ([#9553](https://github.com/leanprover-community/mathlib/pull/9553))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-10-05 01:26:25](https://github.com/leanprover-community/mathlib/commit/0491621)
docs(ring_theory/adjoin_root): fix docstring ([#9546](https://github.com/leanprover-community/mathlib/pull/9546))
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean




## [2021-10-05 01:26:24](https://github.com/leanprover-community/mathlib/commit/7466424)
feat(number_theory/padics): add padic_norm lemmas ([#9527](https://github.com/leanprover-community/mathlib/pull/9527))
#### Estimated changes
Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_numbers.lean
- \+ *lemma* padic.norm_le_pow_iff_norm_lt_pow_add_one
- \+ *lemma* padic.norm_lt_pow_iff_norm_le_pow_sub_one



## [2021-10-04 23:18:15](https://github.com/leanprover-community/mathlib/commit/3aac8e5)
fix(order/sub): make arguments explicit ([#9541](https://github.com/leanprover-community/mathlib/pull/9541))
* This makes some arguments of lemmas explicit.
* These lemmas were not used in places where the implicitness/explicitness of the arguments matters
* Providing the arguments is sometimes useful, especially in `rw ← ...`
* This follows the explicitness of similar lemmas (like the instantiations for `nat`).
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+/\- *lemma* add_sub_add_right_eq_sub'
- \+/\- *lemma* add_sub_cancel_left
- \+/\- *lemma* add_sub_cancel_right
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
Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable/basic.lean


Modified src/data/quot.lean
- \+ *lemma* quotient.out_equiv_out
- \+ *lemma* quotient.out_inj

Modified src/data/rat/denumerable.lean
- \+/\- *lemma* cardinal.mk_rat

Modified src/logic/nontrivial.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.encodable_iff
- \+ *theorem* cardinal.lift_bit0
- \+ *theorem* cardinal.lift_bit1
- \+ *theorem* cardinal.lift_le_omega
- \+ *theorem* cardinal.lift_prod
- \+ *theorem* cardinal.lift_two
- \+/\- *theorem* cardinal.lift_two_power
- \+ *lemma* cardinal.mk_denumerable
- \+ *theorem* cardinal.mk_insert
- \+/\- *lemma* cardinal.mk_int
- \+ *lemma* cardinal.mk_le_omega
- \+/\- *lemma* cardinal.mk_nat
- \+/\- *lemma* cardinal.mk_pnat
- \+/\- *theorem* cardinal.mk_univ
- \+ *lemma* cardinal.omega_le_add_iff
- \+ *theorem* cardinal.omega_le_lift
- \+ *lemma* cardinal.omega_le_mk

Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* cardinal.nat_power_eq
- \+/\- *theorem* cardinal.pow_le
- \+ *lemma* cardinal.power_eq_two_power
- \+/\- *lemma* cardinal.power_nat_le
- \+/\- *lemma* cardinal.power_self_eq
- \+ *lemma* cardinal.prod_eq_two_power



## [2021-10-04 19:37:52](https://github.com/leanprover-community/mathlib/commit/50b51c5)
refactor(group_theory/is_p_group): Generalize `is_p_group.comap_injective` ([#9509](https://github.com/leanprover-community/mathlib/pull/9509))
`is_p_group.comap_injective` (comap along injective preserves p-groups) can be generalized to `is_p_group.comap_ker_is_p_group` (comap with p-group kernel preserves p-groups). This also simplifies the proof of `is_p_group.to_sup_of_normal_right`
#### Estimated changes
Modified src/group_theory/p_group.lean
- \- *lemma* is_p_group.comap_injective
- \+ *lemma* is_p_group.comap_of_injective
- \+ *lemma* is_p_group.comap_of_ker_is_p_group



## [2021-10-04 15:09:53](https://github.com/leanprover-community/mathlib/commit/7a5d15a)
feat(data/pnat/interval): Finite intervals in ℕ+ ([#9534](https://github.com/leanprover-community/mathlib/pull/9534))
This proves that `ℕ+` is a locally finite order.
#### Estimated changes
Added src/data/pnat/interval.lean
- \+ *lemma* pnat.Icc_eq_finset_subtype
- \+ *lemma* pnat.Ioc_eq_finset_subtype
- \+ *lemma* pnat.Ioo_eq_finset_subtype
- \+ *lemma* pnat.card_Icc
- \+ *lemma* pnat.card_Ioc
- \+ *lemma* pnat.card_Ioo
- \+ *lemma* pnat.card_fintype_Icc
- \+ *lemma* pnat.card_fintype_Ioc
- \+ *lemma* pnat.card_fintype_Ioo
- \+ *lemma* pnat.map_subtype_embedding_Icc
- \+ *lemma* pnat.map_subtype_embedding_Ioc
- \+ *lemma* pnat.map_subtype_embedding_Ioo



## [2021-10-04 15:09:52](https://github.com/leanprover-community/mathlib/commit/e998e4c)
feat(order/conditionally_complete_lattice): image and cSup commute ([#9510](https://github.com/leanprover-community/mathlib/pull/9510))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cinfi_set
- \+ *lemma* csupr_set
- \+ *lemma* galois_connection.l_cSup'
- \+ *lemma* galois_connection.u_cInf'
- \+ *lemma* order_iso.map_cInf'
- \+ *lemma* order_iso.map_cSup'



## [2021-10-04 15:09:51](https://github.com/leanprover-community/mathlib/commit/d8968ba)
feat(algebra/order/functions): recursors and images under monotone maps ([#9505](https://github.com/leanprover-community/mathlib/pull/9505))
#### Estimated changes
Modified src/algebra/order/functions.lean
- \+ *lemma* antitone_on.map_max
- \+ *lemma* antitone_on.map_min
- \+ *lemma* max_rec'
- \+ *lemma* max_rec
- \+ *lemma* min_rec'
- \+ *lemma* min_rec
- \+ *lemma* monotone_on.map_max
- \+ *lemma* monotone_on.map_min



## [2021-10-04 15:09:50](https://github.com/leanprover-community/mathlib/commit/fa52067)
refactor(order/fixed_points): rewrite using bundled `preorder_hom`s ([#9497](https://github.com/leanprover-community/mathlib/pull/9497))
This way `fixed_points.complete_lattice` can be an instance.
#### Estimated changes
Modified src/data/set/function.lean
- \+/\- *theorem* set.inj_on_empty
- \+ *theorem* set.inj_on_singleton
- \+ *theorem* set.inj_on_union
- \+ *lemma* set.injective_piecewise_iff
- \+ *theorem* set.subsingleton.inj_on

Modified src/logic/embedding.lean
- \- *theorem* function.embedding.injective

Modified src/order/fixed_points.lean
- \- *lemma* fixed_points.Sup_le_f_of_fixed_points
- \- *lemma* fixed_points.f_le_Inf_of_fixed_points
- \- *lemma* fixed_points.f_le_inf_of_fixed_points
- \- *lemma* fixed_points.le_next
- \- *def* fixed_points.next
- \- *lemma* fixed_points.next_eq
- \- *def* fixed_points.next_fixed
- \- *def* fixed_points.prev
- \- *lemma* fixed_points.prev_eq
- \- *def* fixed_points.prev_fixed
- \- *lemma* fixed_points.prev_le
- \- *lemma* fixed_points.sup_le_f_of_fixed_points
- \- *def* gfp
- \- *lemma* gfp_comp
- \- *lemma* gfp_fixed_point
- \- *lemma* gfp_gfp
- \- *lemma* gfp_induction
- \- *lemma* gfp_le
- \- *lemma* le_gfp
- \- *lemma* le_lfp
- \- *def* lfp
- \- *lemma* lfp_comp
- \- *lemma* lfp_fixed_point
- \- *lemma* lfp_induction
- \- *lemma* lfp_le
- \- *lemma* lfp_lfp
- \- *lemma* monotone_gfp
- \- *lemma* monotone_lfp
- \+ *def* preorder_hom.gfp
- \+ *lemma* preorder_hom.gfp_const_inf_le
- \+ *lemma* preorder_hom.gfp_gfp
- \+ *lemma* preorder_hom.gfp_induction
- \+ *lemma* preorder_hom.gfp_le
- \+ *lemma* preorder_hom.gfp_le_map
- \+ *lemma* preorder_hom.is_fixed_pt_gfp
- \+ *lemma* preorder_hom.is_fixed_pt_lfp
- \+ *lemma* preorder_hom.is_greatest_gfp
- \+ *lemma* preorder_hom.is_greatest_gfp_le
- \+ *lemma* preorder_hom.is_least_lfp
- \+ *lemma* preorder_hom.is_least_lfp_le
- \+ *lemma* preorder_hom.le_gfp
- \+ *lemma* preorder_hom.le_lfp
- \+ *lemma* preorder_hom.le_map_Sup_subset_fixed_points
- \+ *lemma* preorder_hom.le_map_sup_fixed_points
- \+ *lemma* preorder_hom.le_next_fixed
- \+ *lemma* preorder_hom.le_prev_fixed
- \+ *lemma* preorder_hom.le_prev_fixed_iff
- \+ *def* preorder_hom.lfp
- \+ *lemma* preorder_hom.lfp_induction
- \+ *lemma* preorder_hom.lfp_le
- \+ *lemma* preorder_hom.lfp_le_fixed
- \+ *lemma* preorder_hom.lfp_le_map
- \+ *lemma* preorder_hom.lfp_lfp
- \+ *lemma* preorder_hom.map_Inf_subset_fixed_points_le
- \+ *lemma* preorder_hom.map_gfp
- \+ *lemma* preorder_hom.map_gfp_comp
- \+ *lemma* preorder_hom.map_inf_fixed_points_le
- \+ *lemma* preorder_hom.map_le_gfp
- \+ *lemma* preorder_hom.map_le_lfp
- \+ *lemma* preorder_hom.map_lfp
- \+ *lemma* preorder_hom.map_lfp_comp
- \+ *def* preorder_hom.next_fixed
- \+ *lemma* preorder_hom.next_fixed_le
- \+ *lemma* preorder_hom.next_fixed_le_iff
- \+ *def* preorder_hom.prev_fixed
- \+ *lemma* preorder_hom.prev_fixed_le

Modified src/set_theory/schroeder_bernstein.lean




## [2021-10-04 15:09:49](https://github.com/leanprover-community/mathlib/commit/387ff6e)
feat(topology/homotopy): add `homotopy_with` ([#9252](https://github.com/leanprover-community/mathlib/pull/9252))
Added `homotopy_with` as in [`HOL-Analysis`](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html) extending `homotopy`. Furthermore, I've added `homotopy_rel`.
Also rename/moved the file. There is also some refactoring which is part of the suggestions from [#9141](https://github.com/leanprover-community/mathlib/pull/9141) .
#### Estimated changes
Deleted src/topology/homotopy.lean
- \- *lemma* continuous_map.homotopy.apply_one
- \- *lemma* continuous_map.homotopy.apply_zero
- \- *def* continuous_map.homotopy.curry
- \- *lemma* continuous_map.homotopy.ext
- \- *def* continuous_map.homotopy.extend
- \- *lemma* continuous_map.homotopy.extend_apply_one
- \- *lemma* continuous_map.homotopy.extend_apply_zero
- \- *def* continuous_map.homotopy.refl
- \- *def* continuous_map.homotopy.symm
- \- *lemma* continuous_map.homotopy.symm_apply
- \- *lemma* continuous_map.homotopy.symm_symm
- \- *lemma* continuous_map.homotopy.symm_trans
- \- *lemma* continuous_map.homotopy.to_continuous_map_apply
- \- *def* continuous_map.homotopy.trans
- \- *lemma* continuous_map.homotopy.trans_apply
- \- *structure* continuous_map.homotopy

Added src/topology/homotopy/basic.lean
- \+ *lemma* continuous_map.homotopy.apply_one
- \+ *lemma* continuous_map.homotopy.apply_zero
- \+ *lemma* continuous_map.homotopy.coe_fn_injective
- \+ *lemma* continuous_map.homotopy.coe_to_continuous_map
- \+ *lemma* continuous_map.homotopy.congr_arg
- \+ *lemma* continuous_map.homotopy.congr_fun
- \+ *def* continuous_map.homotopy.curry
- \+ *lemma* continuous_map.homotopy.curry_apply
- \+ *lemma* continuous_map.homotopy.ext
- \+ *def* continuous_map.homotopy.extend
- \+ *lemma* continuous_map.homotopy.extend_apply_coe
- \+ *lemma* continuous_map.homotopy.extend_apply_of_le_zero
- \+ *lemma* continuous_map.homotopy.extend_apply_of_mem_I
- \+ *lemma* continuous_map.homotopy.extend_apply_of_one_le
- \+ *def* continuous_map.homotopy.refl
- \+ *def* continuous_map.homotopy.simps.apply
- \+ *def* continuous_map.homotopy.symm
- \+ *lemma* continuous_map.homotopy.symm_symm
- \+ *lemma* continuous_map.homotopy.symm_trans
- \+ *def* continuous_map.homotopy.trans
- \+ *lemma* continuous_map.homotopy.trans_apply
- \+ *structure* continuous_map.homotopy
- \+ *lemma* continuous_map.homotopy_rel.eq_fst
- \+ *lemma* continuous_map.homotopy_rel.eq_snd
- \+ *lemma* continuous_map.homotopy_rel.fst_eq_snd
- \+ *def* continuous_map.homotopy_rel.refl
- \+ *def* continuous_map.homotopy_rel.symm
- \+ *lemma* continuous_map.homotopy_rel.symm_symm
- \+ *lemma* continuous_map.homotopy_rel.symm_trans
- \+ *def* continuous_map.homotopy_rel.trans
- \+ *lemma* continuous_map.homotopy_rel.trans_apply
- \+ *abbreviation* continuous_map.homotopy_rel
- \+ *lemma* continuous_map.homotopy_with.apply_one
- \+ *lemma* continuous_map.homotopy_with.apply_zero
- \+ *lemma* continuous_map.homotopy_with.coe_fn_injective
- \+ *lemma* continuous_map.homotopy_with.coe_to_continuous_map
- \+ *lemma* continuous_map.homotopy_with.coe_to_homotopy
- \+ *lemma* continuous_map.homotopy_with.ext
- \+ *lemma* continuous_map.homotopy_with.extend_prop
- \+ *lemma* continuous_map.homotopy_with.prop
- \+ *def* continuous_map.homotopy_with.refl
- \+ *def* continuous_map.homotopy_with.simps.apply
- \+ *def* continuous_map.homotopy_with.symm
- \+ *lemma* continuous_map.homotopy_with.symm_symm
- \+ *lemma* continuous_map.homotopy_with.symm_trans
- \+ *def* continuous_map.homotopy_with.trans
- \+ *lemma* continuous_map.homotopy_with.trans_apply
- \+ *structure* continuous_map.homotopy_with



## [2021-10-04 14:16:41](https://github.com/leanprover-community/mathlib/commit/f6c77be)
fix(ci): always use python3 executable ([#9531](https://github.com/leanprover-community/mathlib/pull/9531))
On many (particularly older) systems, the `python` command can refer to `python2` instead of `python3`.  Therefore we change all `python` calls to `python3` to prevent failures on some self-hosted runners.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2021-10-04 14:16:40](https://github.com/leanprover-community/mathlib/commit/a07d1de)
feat(data/fin/interval): Finite intervals in `fin n` ([#9523](https://github.com/leanprover-community/mathlib/pull/9523))
#### Estimated changes
Added src/data/fin/interval.lean
- \+ *lemma* fin.Icc_eq_finset_subtype
- \+ *lemma* fin.Ioc_eq_finset_subtype
- \+ *lemma* fin.Ioo_eq_finset_subtype
- \+ *lemma* fin.card_Icc
- \+ *lemma* fin.card_Ioc
- \+ *lemma* fin.card_Ioo
- \+ *lemma* fin.card_fintype_Icc
- \+ *lemma* fin.card_fintype_Ioc
- \+ *lemma* fin.card_fintype_Ioo
- \+ *lemma* fin.map_subtype_embedding_Icc
- \+ *lemma* fin.map_subtype_embedding_Ioc
- \+ *lemma* fin.map_subtype_embedding_Ioo



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
Added src/probability_theory/notation.lean




## [2021-10-04 09:48:18](https://github.com/leanprover-community/mathlib/commit/ab7d251)
feat(measure_theory/covering/besicovitch_vector_space): vector spaces satisfy the assumption of Besicovitch covering theorem ([#9461](https://github.com/leanprover-community/mathlib/pull/9461))
The Besicovitch covering theorem works in any metric space subject to a technical condition: there should be no satellite configuration of `N+1` points, for some `N`. We prove that this condition is satisfied in finite-dimensional real vector spaces. Moreover, we get the optimal bound for `N`: it coincides with the maximal number of `1`-separated points that fit in a ball of radius `2`, by [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994]
#### Estimated changes
Added src/measure_theory/covering/besicovitch_vector_space.lean
- \+ *lemma* besicovitch.card_le_multiplicity
- \+ *lemma* besicovitch.card_le_multiplicity_of_δ
- \+ *lemma* besicovitch.card_le_of_separated
- \+ *lemma* besicovitch.exists_good_δ
- \+ *def* besicovitch.good_δ
- \+ *lemma* besicovitch.good_δ_lt_one
- \+ *def* besicovitch.good_τ
- \+ *theorem* besicovitch.is_empty_satellite_config_multiplicity
- \+ *lemma* besicovitch.le_multiplicity_of_δ_of_fin
- \+ *def* besicovitch.multiplicity
- \+ *lemma* besicovitch.multiplicity_le
- \+ *lemma* besicovitch.one_lt_good_τ
- \+ *def* besicovitch.satellite_config.center_and_rescale
- \+ *lemma* besicovitch.satellite_config.center_and_rescale_center
- \+ *lemma* besicovitch.satellite_config.center_and_rescale_radius
- \+ *lemma* besicovitch.satellite_config.exists_normalized
- \+ *lemma* besicovitch.satellite_config.exists_normalized_aux1
- \+ *lemma* besicovitch.satellite_config.exists_normalized_aux2
- \+ *lemma* besicovitch.satellite_config.exists_normalized_aux3



## [2021-10-04 09:48:17](https://github.com/leanprover-community/mathlib/commit/b6f94a9)
feat(analysis/special_functions): real derivs of `complex.exp` and `complex.log` ([#9422](https://github.com/leanprover-community/mathlib/pull/9422))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.restrict_scalars_one_smul_right'
- \+ *lemma* complex.restrict_scalars_one_smul_right

Modified src/analysis/complex/real_deriv.lean
- \+ *lemma* has_deriv_at.complex_to_real_fderiv'
- \+ *lemma* has_deriv_at.complex_to_real_fderiv
- \+ *lemma* has_deriv_within_at.complex_to_real_fderiv'
- \+ *lemma* has_deriv_within_at.complex_to_real_fderiv
- \+ *lemma* has_strict_deriv_at.complex_to_real_fderiv'
- \+ *lemma* has_strict_deriv_at.complex_to_real_fderiv

Modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* complex.has_strict_fderiv_at_log_real
- \+ *lemma* has_deriv_at.clog_real
- \+ *lemma* has_deriv_within_at.clog_real
- \+ *lemma* has_strict_deriv_at.clog_real

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.has_strict_fderiv_at_exp_real
- \+ *lemma* has_deriv_at.cexp_real
- \+ *lemma* has_deriv_within_at.cexp_real
- \+ *lemma* has_strict_deriv_at.cexp_real



## [2021-10-04 09:48:16](https://github.com/leanprover-community/mathlib/commit/1faf964)
feat(ring_theory/algebraic_independent): Existence of transcendence bases and rings are algebraic over transcendence basis ([#9377](https://github.com/leanprover-community/mathlib/pull/9377))
#### Estimated changes
Modified src/ring_theory/algebraic_independent.lean
- \+ *lemma* algebraic_independent.aeval_comp_mv_polynomial_option_equiv_polynomial_adjoin
- \+ *lemma* algebraic_independent.algebra_map_aeval_equiv
- \+ *def* algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin
- \+ *theorem* algebraic_independent.option_iff
- \+ *lemma* exists_is_transcendence_basis
- \+ *lemma* is_transcendence_basis.is_algebraic



## [2021-10-04 09:48:14](https://github.com/leanprover-community/mathlib/commit/8a05dca)
feat(order/jordan_holder): Jordan Hölder theorem ([#8976](https://github.com/leanprover-community/mathlib/pull/8976))
The Jordan Hoelder theorem proved for a Jordan Hölder lattice, instances of which include submodules of a module and subgroups of a group.
#### Estimated changes
Added src/order/jordan_holder.lean
- \+ *def* composition_series.append
- \+ *lemma* composition_series.append_cast_add
- \+ *lemma* composition_series.append_cast_add_aux
- \+ *lemma* composition_series.append_nat_add
- \+ *lemma* composition_series.append_nat_add_aux
- \+ *lemma* composition_series.append_succ_cast_add
- \+ *lemma* composition_series.append_succ_cast_add_aux
- \+ *lemma* composition_series.append_succ_nat_add
- \+ *lemma* composition_series.append_succ_nat_add_aux
- \+ *def* composition_series.bot
- \+ *lemma* composition_series.bot_erase_top
- \+ *lemma* composition_series.bot_le
- \+ *lemma* composition_series.bot_le_of_mem
- \+ *lemma* composition_series.bot_mem
- \+ *lemma* composition_series.bot_snoc
- \+ *lemma* composition_series.chain'_to_list
- \+ *lemma* composition_series.coe_fn_mk
- \+ *lemma* composition_series.eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
- \+ *lemma* composition_series.eq_snoc_erase_top
- \+ *lemma* composition_series.equivalent.append
- \+ *lemma* composition_series.equivalent.length_eq
- \+ *lemma* composition_series.equivalent.refl
- \+ *lemma* composition_series.equivalent.snoc_snoc_swap
- \+ *lemma* composition_series.equivalent.symm
- \+ *lemma* composition_series.equivalent.trans
- \+ *def* composition_series.equivalent
- \+ *def* composition_series.erase_top
- \+ *lemma* composition_series.erase_top_top_le
- \+ *lemma* composition_series.exists_top_eq_snoc_equivalant
- \+ *lemma* composition_series.ext
- \+ *lemma* composition_series.ext_fun
- \+ *lemma* composition_series.forall_mem_eq_of_length_eq_zero
- \+ *lemma* composition_series.is_maximal_erase_top_top
- \+ *theorem* composition_series.jordan_holder
- \+ *lemma* composition_series.le_top
- \+ *lemma* composition_series.le_top_of_mem
- \+ *lemma* composition_series.length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
- \+ *lemma* composition_series.length_of_list
- \+ *lemma* composition_series.length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos
- \+ *lemma* composition_series.length_pos_of_mem_ne
- \+ *lemma* composition_series.length_to_list
- \+ *theorem* composition_series.lt_succ
- \+ *lemma* composition_series.lt_top_of_mem_erase_top
- \+ *lemma* composition_series.mem_def
- \+ *lemma* composition_series.mem_erase_top
- \+ *lemma* composition_series.mem_erase_top_of_ne_of_mem
- \+ *lemma* composition_series.mem_snoc
- \+ *lemma* composition_series.mem_to_list
- \+ *def* composition_series.of_list
- \+ *lemma* composition_series.of_list_to_list'
- \+ *lemma* composition_series.of_list_to_list
- \+ *def* composition_series.snoc
- \+ *lemma* composition_series.snoc_cast_succ
- \+ *lemma* composition_series.snoc_erase_top_top
- \+ *lemma* composition_series.snoc_last
- \+ *lemma* composition_series.step
- \+ *def* composition_series.to_list
- \+ *lemma* composition_series.to_list_injective
- \+ *lemma* composition_series.to_list_ne_nil
- \+ *lemma* composition_series.to_list_nodup
- \+ *lemma* composition_series.to_list_of_list
- \+ *lemma* composition_series.to_list_sorted
- \+ *def* composition_series.top
- \+ *lemma* composition_series.top_erase_top
- \+ *lemma* composition_series.top_mem
- \+ *lemma* composition_series.top_snoc
- \+ *lemma* composition_series.total
- \+ *structure* composition_series
- \+ *lemma* jordan_holder_lattice.is_maximal.iso_refl
- \+ *lemma* jordan_holder_lattice.is_maximal_inf_right_of_is_maximal_sup
- \+ *lemma* jordan_holder_lattice.is_maximal_of_eq_inf
- \+ *lemma* jordan_holder_lattice.second_iso_of_eq



## [2021-10-04 09:48:13](https://github.com/leanprover-community/mathlib/commit/abe81bc)
feat(linear_algebra/matrix/general_linear_group): GL(n, R) ([#8466](https://github.com/leanprover-community/mathlib/pull/8466))
added this file which contains definition of the general linear group as well as the subgroup of matrices with positive determinant.
#### Estimated changes
Added src/linear_algebra/general_linear_group.lean
- \+ *def* matrix.GL_pos
- \+ *lemma* matrix.GL_pos_coe_neg
- \+ *lemma* matrix.GL_pos_neg_elt
- \+ *lemma* matrix.general_linear_group.coe_fn_eq_coe
- \+ *lemma* matrix.general_linear_group.coe_inv
- \+ *lemma* matrix.general_linear_group.coe_mul
- \+ *lemma* matrix.general_linear_group.coe_one
- \+ *def* matrix.general_linear_group.det
- \+ *lemma* matrix.general_linear_group.ext
- \+ *lemma* matrix.general_linear_group.ext_iff
- \+ *def* matrix.general_linear_group.mk'
- \+ *def* matrix.general_linear_group.to_lin
- \+ *abbreviation* matrix.general_linear_group
- \+ *lemma* matrix.mem_GL_pos
- \+ *lemma* matrix.special_linear_group.coe_eq_to_GL_pos
- \+ *def* matrix.special_linear_group.to_GL_pos
- \+ *lemma* matrix.special_linear_group.to_GL_pos_injective

Modified src/ring_theory/subring.lean
- \+ *lemma* units.mem_pos_subgroup
- \+ *def* units.pos_subgroup

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* mem_pos_monoid
- \+ *def* pos_submonoid



## [2021-10-04 08:10:26](https://github.com/leanprover-community/mathlib/commit/edb22fe)
feat(topology/algebra): nonarchimedean filter bases ([#9511](https://github.com/leanprover-community/mathlib/pull/9511))
This is preparatory material for adic topology. It is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
Added src/topology/algebra/nonarchimedean/bases.lean
- \+ *def* ring_filter_basis.module_filter_basis
- \+ *structure* ring_filter_basis.submodules_basis
- \+ *lemma* ring_filter_basis.submodules_basis_is_basis
- \+ *lemma* ring_subgroups_basis.has_basis_nhds
- \+ *lemma* ring_subgroups_basis.has_basis_nhds_zero
- \+ *lemma* ring_subgroups_basis.mem_add_group_filter_basis
- \+ *lemma* ring_subgroups_basis.mem_add_group_filter_basis_iff
- \+ *lemma* ring_subgroups_basis.nonarchimedean
- \+ *lemma* ring_subgroups_basis.of_comm
- \+ *def* ring_subgroups_basis.open_add_subgroup
- \+ *def* ring_subgroups_basis.to_ring_filter_basis
- \+ *def* ring_subgroups_basis.topology
- \+ *structure* ring_subgroups_basis
- \+ *lemma* submodules_basis.nonarchimedean
- \+ *def* submodules_basis.open_add_subgroup
- \+ *def* submodules_basis.to_module_filter_basis
- \+ *def* submodules_basis.topology
- \+ *structure* submodules_basis
- \+ *lemma* submodules_ring_basis.to_ring_subgroups_basis
- \+ *lemma* submodules_ring_basis.to_submodules_basis
- \+ *def* submodules_ring_basis.topology
- \+ *structure* submodules_ring_basis



## [2021-10-04 08:10:24](https://github.com/leanprover-community/mathlib/commit/6bd6afa)
feat(data/nat/interval): finite intervals of naturals ([#9507](https://github.com/leanprover-community/mathlib/pull/9507))
This proves that `ℕ` is a `locally_finite_order`.
#### Estimated changes
Modified src/data/list/erase_dup.lean


Added src/data/nat/interval.lean
- \+ *lemma* nat.Icc_eq_range'
- \+ *lemma* nat.Icc_succ_left
- \+ *lemma* nat.Ioc_eq_range'
- \+ *lemma* nat.Ioo_eq_range'
- \+ *lemma* nat.card_Icc
- \+ *lemma* nat.card_Ioc
- \+ *lemma* nat.card_Ioo
- \+ *lemma* nat.card_fintype_Icc
- \+ *lemma* nat.card_fintype_Ioc
- \+ *lemma* nat.card_fintype_Ioo



## [2021-10-04 08:10:23](https://github.com/leanprover-community/mathlib/commit/dc1b045)
feat(linear_algebra/free_module/strong_rank_condition): add `comm_ring_strong_rank_condition` ([#9486](https://github.com/leanprover-community/mathlib/pull/9486))
We add `comm_ring_strong_rank_condition`: any commutative ring satisfies the strong rank condition.
Because of a circular import, this can't be in `linear_algebra.invariant_basis_number`.
#### Estimated changes
Modified src/linear_algebra/charpoly/basic.lean
- \- *lemma* linear_map.charpoly_coeff_zero_of_injective
- \+ *lemma* linear_map.minpoly_coeff_zero_of_injective

Added src/linear_algebra/free_module/strong_rank_condition.lean


Modified src/linear_algebra/invariant_basis_number.lean




## [2021-10-04 08:10:22](https://github.com/leanprover-community/mathlib/commit/6a6b4d0)
feat(category_theory/sites/*): Cover-lifting functors on sites ([#9431](https://github.com/leanprover-community/mathlib/pull/9431))
This PR defines cover-liftings functors between sites, and proves that `Ran F.op` maps sheaves to sheaves for cover-lifting functors `F`. 
This will probably be needed when we want to glue B-sheaves into sheaves.
#### Estimated changes
Added src/category_theory/sites/cover_lifting.lean
- \+ *def* category_theory.Ran_is_sheaf_of_cover_lifting.get_section
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.get_section_commute
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_amalgamation
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_unique
- \+ *def* category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone_π_app
- \+ *def* category_theory.Ran_is_sheaf_of_cover_lifting.glued_section
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_amalgamation
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_unique
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.helper
- \+ *def* category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family
- \+ *lemma* category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family_apply
- \+ *theorem* category_theory.Ran_is_sheaf_of_cover_lifting
- \+ *def* category_theory.comp_cover_lifting
- \+ *structure* category_theory.cover_lifting
- \+ *def* category_theory.id_cover_lifting

Modified src/category_theory/sites/sheaf_of_types.lean
- \+/\- *def* category_theory.SheafOfTypes
- \+ *def* category_theory.presieve.family_of_elements.comp_presheaf_map
- \+ *lemma* category_theory.presieve.family_of_elements.compatible.comp_presheaf_map
- \+ *lemma* category_theory.presieve.family_of_elements.compatible.functor_pullback
- \+ *lemma* category_theory.presieve.family_of_elements.compatible.pullback
- \+ *def* category_theory.presieve.family_of_elements.functor_pullback
- \+ *def* category_theory.presieve.family_of_elements.pullback

Modified src/category_theory/sites/sieves.lean
- \+ *def* category_theory.presieve.functor_pullback
- \+ *lemma* category_theory.presieve.functor_pullback_id
- \+ *lemma* category_theory.presieve.functor_pullback_mem
- \+/\- *def* category_theory.sieve.functor
- \+ *def* category_theory.sieve.functor_pullback
- \+ *lemma* category_theory.sieve.functor_pullback_id
- \+/\- *structure* category_theory.sieve

Modified src/category_theory/structured_arrow.lean
- \+ *def* category_theory.structured_arrow.hom_mk'



## [2021-10-04 05:54:42](https://github.com/leanprover-community/mathlib/commit/d677c29)
feat(field_theory/algebraic_closure): versions of exists_aeval_eq_zero for rings ([#9517](https://github.com/leanprover-community/mathlib/pull/9517))
#### Estimated changes
Modified src/field_theory/is_alg_closed/basic.lean
- \+ *theorem* is_alg_closed.exists_aeval_eq_zero_of_injective
- \+ *theorem* is_alg_closed.exists_eval₂_eq_zero_of_injective



## [2021-10-03 20:33:50](https://github.com/leanprover-community/mathlib/commit/52495a0)
chore(data/set/lattice): fix name ([#9520](https://github.com/leanprover-community/mathlib/pull/9520))
`comp` is for composition, `compl` for complement. Fix names using `comp` instead of `compl`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \- *theorem* set.Inter_eq_comp_Union_comp
- \+ *theorem* set.Inter_eq_compl_Union_compl
- \- *theorem* set.Union_eq_comp_Inter_comp
- \+ *theorem* set.Union_eq_compl_Inter_compl
- \- *theorem* set.sInter_eq_comp_sUnion_compl
- \+ *theorem* set.sInter_eq_compl_sUnion_compl



## [2021-10-03 20:33:49](https://github.com/leanprover-community/mathlib/commit/465508f)
split(order/monotone): split off `order.basic` ([#9518](https://github.com/leanprover-community/mathlib/pull/9518))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas.lean


Modified src/order/basic.lean
- \- *lemma* antitone.comp_monotone
- \- *lemma* antitone.comp_monotone_on
- \- *lemma* antitone.ne_of_lt_of_lt_int
- \- *lemma* antitone.ne_of_lt_of_lt_nat
- \- *lemma* antitone.reflect_lt
- \- *lemma* antitone.strict_anti_iff_injective
- \- *lemma* antitone.strict_anti_of_injective
- \- *def* antitone
- \- *theorem* antitone_app
- \- *theorem* antitone_const
- \- *theorem* antitone_lam
- \- *lemma* antitone_nat_of_succ_le
- \- *def* antitone_on
- \- *lemma* antitone_on_univ
- \- *lemma* forall_ge_le_of_forall_le_succ
- \- *lemma* function.monotone_eval
- \- *lemma* injective_of_le_imp_le
- \- *lemma* injective_of_lt_imp_ne
- \- *lemma* monotone.comp_antitone
- \- *lemma* monotone.comp_antitone_on
- \- *theorem* monotone.comp_le_comp_left
- \- *lemma* monotone.ne_of_lt_of_lt_int
- \- *lemma* monotone.ne_of_lt_of_lt_nat
- \- *lemma* monotone.reflect_lt
- \- *lemma* monotone.strict_mono_iff_injective
- \- *lemma* monotone.strict_mono_of_injective
- \- *def* monotone
- \- *theorem* monotone_app
- \- *theorem* monotone_const
- \- *lemma* monotone_fst
- \- *lemma* monotone_id
- \- *theorem* monotone_lam
- \- *lemma* monotone_nat_of_le_succ
- \- *def* monotone_on
- \- *lemma* monotone_on_univ
- \- *lemma* monotone_snd
- \- *lemma* strict_anti.comp_strict_mono
- \- *lemma* strict_anti.comp_strict_mono_on
- \- *lemma* strict_anti.injective
- \- *lemma* strict_anti.le_iff_le
- \- *lemma* strict_anti.lt_iff_lt
- \- *lemma* strict_anti.maximal_of_minimal_image
- \- *lemma* strict_anti.minimal_of_maximal_image
- \- *def* strict_anti
- \- *lemma* strict_anti_nat_of_succ_lt
- \- *lemma* strict_anti_on.le_iff_le
- \- *lemma* strict_anti_on.lt_iff_lt
- \- *def* strict_anti_on
- \- *lemma* strict_anti_on_univ
- \- *lemma* strict_mono.comp_strict_anti
- \- *lemma* strict_mono.comp_strict_anti_on
- \- *lemma* strict_mono.id_le
- \- *lemma* strict_mono.injective
- \- *lemma* strict_mono.le_iff_le
- \- *lemma* strict_mono.lt_iff_lt
- \- *lemma* strict_mono.maximal_of_maximal_image
- \- *lemma* strict_mono.minimal_of_minimal_image
- \- *def* strict_mono
- \- *lemma* strict_mono_id
- \- *lemma* strict_mono_nat_of_lt_succ
- \- *lemma* strict_mono_of_le_iff_le
- \- *lemma* strict_mono_on.le_iff_le
- \- *lemma* strict_mono_on.lt_iff_lt
- \- *def* strict_mono_on
- \- *lemma* strict_mono_on_univ
- \- *lemma* subtype.mono_coe
- \- *lemma* subtype.strict_mono_coe

Modified src/order/closure.lean


Modified src/order/iterate.lean


Modified src/order/lattice.lean


Added src/order/monotone.lean
- \+ *lemma* antitone.comp_monotone
- \+ *lemma* antitone.comp_monotone_on
- \+ *lemma* antitone.ne_of_lt_of_lt_int
- \+ *lemma* antitone.ne_of_lt_of_lt_nat
- \+ *lemma* antitone.reflect_lt
- \+ *lemma* antitone.strict_anti_iff_injective
- \+ *lemma* antitone.strict_anti_of_injective
- \+ *def* antitone
- \+ *theorem* antitone_app
- \+ *theorem* antitone_const
- \+ *theorem* antitone_lam
- \+ *lemma* antitone_nat_of_succ_le
- \+ *def* antitone_on
- \+ *lemma* antitone_on_univ
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+ *lemma* function.monotone_eval
- \+ *lemma* injective_of_le_imp_le
- \+ *lemma* injective_of_lt_imp_ne
- \+ *lemma* monotone.comp_antitone
- \+ *lemma* monotone.comp_antitone_on
- \+ *theorem* monotone.comp_le_comp_left
- \+ *lemma* monotone.ne_of_lt_of_lt_int
- \+ *lemma* monotone.ne_of_lt_of_lt_nat
- \+ *lemma* monotone.reflect_lt
- \+ *lemma* monotone.strict_mono_iff_injective
- \+ *lemma* monotone.strict_mono_of_injective
- \+ *def* monotone
- \+ *theorem* monotone_app
- \+ *theorem* monotone_const
- \+ *lemma* monotone_fst
- \+ *lemma* monotone_id
- \+ *theorem* monotone_lam
- \+ *lemma* monotone_nat_of_le_succ
- \+ *def* monotone_on
- \+ *lemma* monotone_on_univ
- \+ *lemma* monotone_snd
- \+ *lemma* strict_anti.comp_strict_mono
- \+ *lemma* strict_anti.comp_strict_mono_on
- \+ *lemma* strict_anti.injective
- \+ *lemma* strict_anti.le_iff_le
- \+ *lemma* strict_anti.lt_iff_lt
- \+ *lemma* strict_anti.maximal_of_minimal_image
- \+ *lemma* strict_anti.minimal_of_maximal_image
- \+ *def* strict_anti
- \+ *lemma* strict_anti_nat_of_succ_lt
- \+ *lemma* strict_anti_on.le_iff_le
- \+ *lemma* strict_anti_on.lt_iff_lt
- \+ *def* strict_anti_on
- \+ *lemma* strict_anti_on_univ
- \+ *lemma* strict_mono.comp_strict_anti
- \+ *lemma* strict_mono.comp_strict_anti_on
- \+ *lemma* strict_mono.id_le
- \+ *lemma* strict_mono.injective
- \+ *lemma* strict_mono.le_iff_le
- \+ *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_mono.maximal_of_maximal_image
- \+ *lemma* strict_mono.minimal_of_minimal_image
- \+ *def* strict_mono
- \+ *lemma* strict_mono_id
- \+ *lemma* strict_mono_nat_of_lt_succ
- \+ *lemma* strict_mono_of_le_iff_le
- \+ *lemma* strict_mono_on.le_iff_le
- \+ *lemma* strict_mono_on.lt_iff_lt
- \+ *def* strict_mono_on
- \+ *lemma* strict_mono_on_univ
- \+ *lemma* subtype.mono_coe
- \+ *lemma* subtype.strict_mono_coe

Modified src/order/prime_ideal.lean




## [2021-10-03 20:33:48](https://github.com/leanprover-community/mathlib/commit/c0f7c56)
feat(algebra/order): exists_square_le ([#9513](https://github.com/leanprover-community/mathlib/pull/9513))
This is a modernized version of code from the perfectoid project.
#### Estimated changes
Modified src/algebra/order/monoid_lemmas.lean
- \+ *lemma* exists_square_le



## [2021-10-03 20:33:47](https://github.com/leanprover-community/mathlib/commit/bc5a081)
feat(topology/algebra): Cauchy filters on groups ([#9512](https://github.com/leanprover-community/mathlib/pull/9512))
This adds a tiny file but putting this lemma in `topology/algebra/filter_basis.lean` would make that file import a lot of uniform spaces theory. This is a modernized version of code from the perfectoid spaces project.
#### Estimated changes
Added src/topology/algebra/uniform_filter_basis.lean
- \+ *lemma* add_group_filter_basis.cauchy_iff



## [2021-10-03 20:33:46](https://github.com/leanprover-community/mathlib/commit/44f4d70)
chore(*): use dot-notation for is_conj.symm and is_conj.trans ([#9498](https://github.com/leanprover-community/mathlib/pull/9498))
renames:
* is_conj_refl -> is_conj.refl
* is_conj_symm -> is_conj.symm
* is_conj_trans -> is_conj.trans
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+/\- *lemma* conj_classes.mem_carrier_mk
- \+ *lemma* is_conj.refl
- \+ *lemma* is_conj.symm
- \+ *lemma* is_conj.trans
- \- *lemma* is_conj_refl
- \- *lemma* is_conj_symm
- \- *lemma* is_conj_trans
- \+/\- *lemma* mem_conjugates_of_self

Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/subgroup/basic.lean




## [2021-10-03 20:33:45](https://github.com/leanprover-community/mathlib/commit/c1936c1)
feat(order/basic): define `is_top` and `is_bot` ([#9493](https://github.com/leanprover-community/mathlib/pull/9493))
These predicates allow us to formulate & prove some theorems
simultaneously for the cases `[order_top α]` and `[no_top_order α]`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.set_of_eq_eq_singleton'
- \+/\- *lemma* set.set_of_eq_eq_singleton
- \+ *lemma* set.subsingleton_is_bot
- \+ *lemma* set.subsingleton_is_top

Modified src/data/set/countable.lean
- \+ *lemma* set.countable_is_bot
- \+ *lemma* set.countable_is_top
- \+ *lemma* set.subsingleton.countable

Modified src/data/set/finite.lean
- \+ *lemma* set.finite_is_bot
- \+ *lemma* set.finite_is_top

Modified src/order/basic.lean
- \+ *lemma* is_bot.unique
- \+ *def* is_bot
- \+ *lemma* is_top.unique
- \+ *def* is_top
- \+ *lemma* not_is_bot
- \+ *lemma* not_is_top

Modified src/order/bounded_lattice.lean
- \+ *theorem* is_bot_iff_eq_bot
- \+ *theorem* is_top_iff_eq_top



## [2021-10-03 18:50:48](https://github.com/leanprover-community/mathlib/commit/e789ad3)
feat(group_theory/subgroup): mk lemmas ([#9514](https://github.com/leanprover-community/mathlib/pull/9514))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/set_like.20idiom
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.coe_set_mk
- \+ *lemma* submodule.mem_mk
- \- *lemma* submodule.mk_coe
- \+ *lemma* submodule.mk_le_mk

Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.coe_set_mk
- \+/\- *lemma* subfield.mem_mk
- \+ *lemma* subfield.mk_le_mk

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.coe_set_mk
- \+ *lemma* subgroup.mem_mk
- \+ *lemma* subgroup.mk_le_mk

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.coe_set_mk
- \+ *lemma* submonoid.mem_mk
- \+ *lemma* submonoid.mk_le_mk

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.coe_set_mk
- \+ *lemma* subring.mem_mk
- \+ *lemma* subring.mk_le_mk



## [2021-10-03 15:22:43](https://github.com/leanprover-community/mathlib/commit/d260894)
feat(analysis/convex/combination): lemmas connecting convex hull with affine combinations and barycentric coordinates ([#9499](https://github.com/leanprover-community/mathlib/pull/9499))
#### Estimated changes
Modified src/analysis/convex/combination.lean
- \+ *lemma* affine_combination_mem_convex_hull
- \+ *lemma* convex_hull_affine_basis_eq_nonneg_barycentric
- \+ *lemma* convex_hull_range_eq_exists_affine_combination

Modified src/linear_algebra/affine_space/barycentric_coords.lean
- \- *lemma* barycentric_coord_apply_combination
- \+ *lemma* barycentric_coord_apply_combination_of_mem
- \+ *lemma* barycentric_coord_apply_combination_of_not_mem



## [2021-10-03 11:42:58](https://github.com/leanprover-community/mathlib/commit/cff9927)
refactor(ring_theory/unique_factorization_domain): rename unique_factorization_monoid.factors ([#9503](https://github.com/leanprover-community/mathlib/pull/9503))
This frees up the name for the non-normalizing version.
#### Estimated changes
Modified src/algebra/squarefree.lean
- \- *lemma* unique_factorization_monoid.squarefree_iff_nodup_factors
- \+ *lemma* unique_factorization_monoid.squarefree_iff_nodup_normalized_factors

Modified src/field_theory/splitting_field.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/dedekind_domain.lean
- \- *lemma* factors_prod_factors_eq_factors
- \+ *lemma* normalized_factors_prod
- \- *lemma* prod_factors_eq_self
- \+ *lemma* prod_normalized_factors_eq_self
- \+/\- *lemma* sup_eq_prod_inf_factors

Modified src/ring_theory/int/basic.lean
- \+/\- *theorem* nat.factors_eq

Modified src/ring_theory/unique_factorization_domain.lean
- \- *lemma* unique_factorization_monoid.dvd_iff_factors_le_factors
- \+ *lemma* unique_factorization_monoid.dvd_iff_normalized_factors_le_normalized_factors
- \- *lemma* unique_factorization_monoid.dvd_of_mem_factors
- \+ *lemma* unique_factorization_monoid.dvd_of_mem_normalized_factors
- \- *lemma* unique_factorization_monoid.exists_mem_factors_of_dvd
- \+ *lemma* unique_factorization_monoid.exists_mem_normalized_factors_of_dvd
- \- *lemma* unique_factorization_monoid.factors_irreducible
- \- *lemma* unique_factorization_monoid.factors_mul
- \- *lemma* unique_factorization_monoid.factors_one
- \- *lemma* unique_factorization_monoid.factors_pow
- \- *theorem* unique_factorization_monoid.factors_prod
- \- *lemma* unique_factorization_monoid.factors_zero
- \- *theorem* unique_factorization_monoid.irreducible_of_factor
- \+ *theorem* unique_factorization_monoid.irreducible_of_normalized_factor
- \- *lemma* unique_factorization_monoid.le_multiplicity_iff_repeat_le_factors
- \+ *lemma* unique_factorization_monoid.le_multiplicity_iff_repeat_le_normalized_factors
- \- *lemma* unique_factorization_monoid.multiplicity_eq_count_factors
- \+ *lemma* unique_factorization_monoid.multiplicity_eq_count_normalized_factors
- \- *theorem* unique_factorization_monoid.normalize_factor
- \+ *theorem* unique_factorization_monoid.normalize_normalized_factor
- \+ *lemma* unique_factorization_monoid.normalized_factors_irreducible
- \+ *lemma* unique_factorization_monoid.normalized_factors_mul
- \+ *lemma* unique_factorization_monoid.normalized_factors_one
- \+ *lemma* unique_factorization_monoid.normalized_factors_pow
- \+ *theorem* unique_factorization_monoid.normalized_factors_prod
- \+ *lemma* unique_factorization_monoid.normalized_factors_zero
- \- *theorem* unique_factorization_monoid.prime_of_factor
- \+ *theorem* unique_factorization_monoid.prime_of_normalized_factor
- \- *lemma* unique_factorization_monoid.zero_not_mem_factors
- \+ *lemma* unique_factorization_monoid.zero_not_mem_normalized_factors



## [2021-10-03 11:42:57](https://github.com/leanprover-community/mathlib/commit/18e7f91)
feat(group_theory/quotient_group): if a quotient is trivial then the subgroup is the whole group ([#9092](https://github.com/leanprover-community/mathlib/pull/9092))
#### Estimated changes
Modified src/data/setoid/basic.lean
- \+ *lemma* quot.subsingleton_iff
- \+ *lemma* quotient.subsingleton_iff
- \+ *lemma* setoid.bot_def
- \+ *lemma* setoid.eq_top_iff
- \+ *lemma* setoid.top_def

Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.subgroup_eq_top_of_subsingleton
- \+ *lemma* quotient_group.subsingleton_quotient_top

Modified src/logic/relation.lean
- \+ *lemma* relation.eqv_gen_eq_of_equivalence



## [2021-10-03 10:10:01](https://github.com/leanprover-community/mathlib/commit/55c30c6)
feat(topology/basic): interior of finite intersection is intersection of interiors ([#9508](https://github.com/leanprover-community/mathlib/pull/9508))
And likewise for finite unions and closures.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* closure_Union_of_fintype
- \+ *lemma* finset.closure_Union
- \+ *lemma* finset.interior_Inter
- \+ *lemma* interior_Inter_of_fintype



## [2021-10-03 09:15:42](https://github.com/leanprover-community/mathlib/commit/2807d83)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are continuous ([#9515](https://github.com/leanprover-community/mathlib/pull/9515))
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* continuous_barycentric_coord



## [2021-10-03 06:55:59](https://github.com/leanprover-community/mathlib/commit/7d83ff1)
feat(analysis/special_functions/exp_log): prove continuity of exp without derivatives ([#9501](https://github.com/leanprover-community/mathlib/pull/9501))
This is a first step towards making the definition of log and rpow independent of derivatives. The final goal is to avoid importing all of calculus in measure_theory/function/lp_space.lean .
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.exp_bound_sq
- \+ *lemma* complex.locally_lipschitz_exp



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
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_iff_pairwise_on_pos

Modified src/analysis/convex/exposed.lean
- \+/\- *lemma* exposed_points_subset_extreme_points
- \- *lemma* is_exposed.antisymm
- \- *lemma* is_exposed.inter
- \- *lemma* is_exposed.is_closed
- \- *lemma* is_exposed.is_compact
- \- *lemma* is_exposed.refl

Modified src/analysis/convex/function.lean
- \+/\- *lemma* concave_on.add
- \- *lemma* concave_on.concave_ge
- \+ *lemma* concave_on.convex_ge
- \+ *lemma* concave_on.convex_strict_hypograph
- \+/\- *lemma* concave_on.subset
- \+/\- *lemma* concave_on.translate_left
- \+/\- *lemma* concave_on.translate_right
- \+ *lemma* concave_on_iff_forall_pos
- \+ *lemma* concave_on_iff_forall_pos_ne
- \+/\- *lemma* convex_on.add
- \+ *lemma* convex_on.convex_strict_epigraph
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+ *lemma* convex_on_iff_forall_pos
- \+ *lemma* convex_on_iff_forall_pos_ne
- \+/\- *lemma* neg_convex_on_iff



## [2021-10-02 23:49:54](https://github.com/leanprover-community/mathlib/commit/7b02277)
chore(topology/*): more lemmas about `dense`/`dense_range` ([#9492](https://github.com/leanprover-community/mathlib/pull/9492))
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* dense.exists_countable_dense_subset

Modified src/topology/basic.lean
- \+ *lemma* dense.dense_range_coe
- \+ *lemma* dense.exists_mem_open
- \+ *lemma* dense_range.exists_mem_open

Modified src/topology/dense_embedding.lean
- \+ *lemma* dense.dense_embedding_coe
- \+ *lemma* dense_embedding.dense_image
- \+/\- *def* dense_embedding.subtype_emb
- \+ *lemma* dense_inducing.dense_image
- \+/\- *structure* dense_inducing



## [2021-10-02 17:58:29](https://github.com/leanprover-community/mathlib/commit/c46a04a)
chore(measure_theory): move, deduplicate ([#9489](https://github.com/leanprover-community/mathlib/pull/9489))
* move lemmas like `is_compact.measure_lt_top` from `measure_theory.constructions.borel` to `measure_theory.measure.measure_space`;
* drop `is_compact.is_finite_measure` etc;
* add `measure_Ixx_lt_top`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* is_compact.exists_open_superset_measure_lt_top'
- \- *lemma* is_compact.exists_open_superset_measure_lt_top
- \- *lemma* is_compact.measure_lt_top
- \- *lemma* is_compact.measure_lt_top_of_nhds_within
- \- *def* measure_theory.measure.finite_spanning_sets_in_compact
- \- *def* measure_theory.measure.finite_spanning_sets_in_open

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* is_compact.exists_open_superset_measure_lt_top'
- \+ *lemma* is_compact.exists_open_superset_measure_lt_top
- \- *lemma* is_compact.is_finite_measure
- \- *lemma* is_compact.is_finite_measure_of_nhds_within
- \+ *lemma* is_compact.measure_lt_top
- \+ *lemma* is_compact.measure_lt_top_of_nhds_within
- \+ *lemma* measure_Icc_lt_top
- \+ *lemma* measure_Ico_lt_top
- \+ *lemma* measure_Ioc_lt_top
- \+ *lemma* measure_Ioo_lt_top
- \+ *def* measure_theory.measure.finite_spanning_sets_in_compact
- \+ *def* measure_theory.measure.finite_spanning_sets_in_open
- \- *lemma* metric.bounded.is_finite_measure
- \+ *lemma* metric.bounded.measure_lt_top



## [2021-10-02 17:58:27](https://github.com/leanprover-community/mathlib/commit/a97e86a)
chore(ring_theory/ideal): some simp attributes ([#9487](https://github.com/leanprover-community/mathlib/pull/9487))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+/\- *theorem* ideal.bot_mul
- \+/\- *theorem* ideal.mul_bot
- \+/\- *theorem* ideal.mul_top
- \+/\- *theorem* ideal.top_mul



## [2021-10-02 16:08:36](https://github.com/leanprover-community/mathlib/commit/e60dc2b)
docs(measure_theory/integral/lebesgue): Add "Markov's inequality" to the doc string of `mul_meas_ge_le_lintegral` ([#9506](https://github.com/leanprover-community/mathlib/pull/9506))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean




## [2021-10-02 16:08:34](https://github.com/leanprover-community/mathlib/commit/110c740)
refactor(linear_algebra/charpoly): split in two files ([#9485](https://github.com/leanprover-community/mathlib/pull/9485))
We split `linear_algebra/charpoly` in `linear_algebra/charpoly/basic` and `linear_algebra/charpoly/to_matrix`.
Currently in `linear_algebra/charpoly/to_matrix` we only prove `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. This needs to be in a separate file then the definition of `f.charpoly` since it needs the invariant basis number property for commutative rings and in a future PR I will prove this as a special case of the fact that any commutative ring satisfies the strong rank condition, but the proof of this uses the characteristic polynomial.
We plan to add ohter results regarding the characteristic polynomial in the future.
#### Estimated changes
Added src/linear_algebra/charpoly/basic.lean
- \+ *lemma* linear_map.aeval_self_charpoly
- \+ *def* linear_map.charpoly
- \+ *lemma* linear_map.charpoly_coeff_zero_of_injective
- \+ *lemma* linear_map.charpoly_def
- \+ *lemma* linear_map.charpoly_monic
- \+ *lemma* linear_map.is_integral
- \+ *lemma* linear_map.minpoly_dvd_charpoly

Renamed src/linear_algebra/charpoly.lean to src/linear_algebra/charpoly/to_matrix.lean
- \- *lemma* linear_map.aeval_self_charpoly
- \- *def* linear_map.charpoly
- \- *lemma* linear_map.charpoly_coeff_zero_of_injective
- \- *lemma* linear_map.charpoly_def
- \- *lemma* linear_map.charpoly_monic
- \- *lemma* linear_map.is_integral
- \- *lemma* linear_map.minpoly_dvd_charpoly

Modified src/linear_algebra/eigenspace.lean




## [2021-10-02 16:08:33](https://github.com/leanprover-community/mathlib/commit/1ceebca)
refactor(linear_algebra/free_module_pid): move linear_algebra/free_module_pid to linear_algebra/free_module/pid ([#9482](https://github.com/leanprover-community/mathlib/pull/9482))
We move `linear_algebra/free_module_pid` to `linear_algebra/free_module/pid`.
#### Estimated changes
Modified src/linear_algebra/determinant.lean


Renamed src/linear_algebra/free_module_pid.lean to src/linear_algebra/free_module/pid.lean


Modified src/number_theory/class_number/finite.lean




## [2021-10-02 16:08:31](https://github.com/leanprover-community/mathlib/commit/fa7fdca)
feat(measure_theory/function/ae_eq_of_integral): two ennreal-valued function are a.e. equal if their integrals agree ([#9372](https://github.com/leanprover-community/mathlib/pull/9372))
#### Estimated changes
Modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* measure_theory.ae_measurable.ae_eq_of_forall_set_lintegral_eq

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.lt_top_iff_ne_top
- \+ *lemma* filter.eventually.lt_top_of_ne
- \+ *lemma* filter.eventually.ne_of_lt
- \+ *lemma* filter.eventually.ne_top_of_lt

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.eventually_eq_of_to_real_eventually_eq



## [2021-10-02 13:51:01](https://github.com/leanprover-community/mathlib/commit/241aad7)
feat(data/finset/interval): API for `finset.Ixx` ([#9495](https://github.com/leanprover-community/mathlib/pull/9495))
This proves basic results about `finset.Ixx` & co. Lemma names (should) match their `set` counterparts.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.coe_eq_singleton

Added src/data/finset/interval.lean
- \+ *lemma* finset.Icc_eq_empty_iff
- \+ *lemma* finset.Icc_eq_empty_of_lt
- \+ *lemma* finset.Icc_self
- \+ *lemma* finset.Ioc_eq_empty_iff
- \+ *lemma* finset.Ioc_eq_empty_of_le
- \+ *lemma* finset.Ioc_self
- \+ *lemma* finset.Ioo_eq_empty
- \+ *lemma* finset.Ioo_eq_empty_iff
- \+ *lemma* finset.Ioo_eq_empty_of_le
- \+ *lemma* finset.Ioo_self
- \+ *lemma* finset.image_add_const_Icc
- \+ *lemma* finset.image_add_const_Ioc
- \+ *lemma* finset.image_add_const_Ioo
- \+ *lemma* finset.nonempty_Icc
- \+ *lemma* finset.nonempty_Ioc
- \+ *lemma* finset.nonempty_Ioo



## [2021-10-02 12:12:09](https://github.com/leanprover-community/mathlib/commit/f3746ea)
chore(src/analysis/special_functions/trigonometric/basic) : prove continuity of sin/cos/sinh/cosh without derivatives ([#9502](https://github.com/leanprover-community/mathlib/pull/9502))
In a future PR, I want to split all files in the special_functions folder to avoid importing calculus when not needed (the goal is to avoid importing it in the definition of lp_space in measure_theory). This PR changes the proofs of continuity of trigonometric functions.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* complex.continuous_cos
- \+/\- *lemma* complex.continuous_cosh
- \+/\- *lemma* complex.continuous_sin
- \+/\- *lemma* complex.continuous_sinh
- \+/\- *lemma* real.continuous_cos
- \+/\- *lemma* real.continuous_cosh
- \+/\- *lemma* real.continuous_sin
- \+/\- *lemma* real.continuous_sinh



## [2021-10-02 09:30:39](https://github.com/leanprover-community/mathlib/commit/e26a9e5)
feat(measure_theory/covering/besicovitch): the Besicovitch covering theorem ([#9462](https://github.com/leanprover-community/mathlib/pull/9462))
The Besicovitch covering theorem: in a nice metric space (e.g. real vector spaces), from any family of balls one can extract `N` subfamilies made of disjoint balls, covering all the centers of the balls in the family. The number `N` only depends on the metric space.
#### Estimated changes
Modified docs/references.bib


Added src/measure_theory/covering/besicovitch.lean
- \+ *structure* besicovitch.ball_package
- \+ *theorem* besicovitch.exist_disjoint_covering_families
- \+ *lemma* besicovitch.satellite_config.hlast'
- \+ *lemma* besicovitch.satellite_config.inter'
- \+ *structure* besicovitch.satellite_config
- \+ *def* besicovitch.tau_package.R
- \+ *def* besicovitch.tau_package.Union_up_to
- \+ *lemma* besicovitch.tau_package.color_lt
- \+ *def* besicovitch.tau_package.last_step
- \+ *lemma* besicovitch.tau_package.last_step_nonempty
- \+ *lemma* besicovitch.tau_package.mem_Union_up_to_last_step
- \+ *lemma* besicovitch.tau_package.monotone_Union_up_to
- \+ *structure* besicovitch.tau_package
- \+ *def* besicovitch.unit_ball_package



## [2021-10-02 09:30:37](https://github.com/leanprover-community/mathlib/commit/9e54ad0)
feat(ring_theory/algebraic_independent): algebraic independence ([#9229](https://github.com/leanprover-community/mathlib/pull/9229))
#### Estimated changes
Added src/ring_theory/algebraic_independent.lean
- \+ *lemma* alg_hom.algebraic_independent_iff
- \+ *lemma* algebraic_independent.aeval_comp_repr
- \+ *def* algebraic_independent.aeval_equiv
- \+ *lemma* algebraic_independent.aeval_repr
- \+ *lemma* algebraic_independent.algebra_map_injective
- \+ *lemma* algebraic_independent.coe_range
- \+ *lemma* algebraic_independent.comp
- \+ *theorem* algebraic_independent.eq_zero_of_aeval_eq_zero
- \+ *theorem* algebraic_independent.image
- \+ *theorem* algebraic_independent.image_of_comp
- \+ *lemma* algebraic_independent.is_transcendence_basis_iff
- \+ *lemma* algebraic_independent.linear_independent
- \+ *lemma* algebraic_independent.map'
- \+ *lemma* algebraic_independent.map
- \+ *lemma* algebraic_independent.mono
- \+ *lemma* algebraic_independent.ne_zero
- \+ *lemma* algebraic_independent.of_comp
- \+ *def* algebraic_independent.repr
- \+ *lemma* algebraic_independent.repr_ker
- \+ *lemma* algebraic_independent.restrict_of_comp_subtype
- \+ *lemma* algebraic_independent.restrict_scalars
- \+ *theorem* algebraic_independent.to_subtype_range'
- \+ *theorem* algebraic_independent.to_subtype_range
- \+ *def* algebraic_independent
- \+ *lemma* algebraic_independent_Union_of_directed
- \+ *lemma* algebraic_independent_adjoin
- \+ *lemma* algebraic_independent_bounded_of_finset_algebraic_independent_bounded
- \+ *theorem* algebraic_independent_comp_subtype
- \+ *lemma* algebraic_independent_empty
- \+ *lemma* algebraic_independent_empty_iff
- \+ *lemma* algebraic_independent_empty_type
- \+ *lemma* algebraic_independent_empty_type_iff
- \+ *theorem* algebraic_independent_equiv'
- \+ *theorem* algebraic_independent_equiv
- \+ *lemma* algebraic_independent_finset_map_embedding_subtype
- \+ *theorem* algebraic_independent_iff
- \+ *theorem* algebraic_independent_iff_injective_aeval
- \+ *theorem* algebraic_independent_iff_ker_eq_bot
- \+ *theorem* algebraic_independent_image
- \+ *lemma* algebraic_independent_of_finite
- \+ *lemma* algebraic_independent_of_subsingleton
- \+ *lemma* algebraic_independent_sUnion_of_directed
- \+ *theorem* algebraic_independent_subtype
- \+ *theorem* algebraic_independent_subtype_range
- \+ *lemma* exists_maximal_algebraic_independent
- \+ *def* is_transcendence_basis



## [2021-10-02 07:33:19](https://github.com/leanprover-community/mathlib/commit/709b449)
chore(algebra/star/basic): provide automorphisms in commutative rings ([#9483](https://github.com/leanprover-community/mathlib/pull/9483))
This adds `star_mul_aut` and `star_ring_aut`, which are the versions of `star_mul_equiv` and `star_ring_equiv` which avoid needing `opposite` due to commutativity.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *def* star_mul_aut
- \+ *def* star_ring_aut



## [2021-10-02 07:33:18](https://github.com/leanprover-community/mathlib/commit/fc7f9f3)
feat(algebra/algebra): the range of `algebra_map (S : subalgebra R A) A` ([#9450](https://github.com/leanprover-community/mathlib/pull/9450))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.id.map_eq_id
- \+/\- *lemma* algebra.id.map_eq_self

Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.algebra_map_eq
- \+ *lemma* subalgebra.range_algebra_map
- \+ *lemma* subalgebra.srange_algebra_map
- \+ *lemma* subalgebra.to_subring_subtype
- \+ *lemma* subalgebra.to_subsemiring_subtype



## [2021-10-02 07:33:17](https://github.com/leanprover-community/mathlib/commit/a59876f)
feat(ring_theory): quotients of a noetherian ring are noetherian ([#9449](https://github.com/leanprover-community/mathlib/pull/9449))
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \- *theorem* is_noetherian_of_quotient_of_noetherian



## [2021-10-02 04:58:50](https://github.com/leanprover-community/mathlib/commit/37f43bf)
feat(linear_algebra/affine_space/barycentric_coords): define barycentric coordinates ([#9472](https://github.com/leanprover-community/mathlib/pull/9472))
#### Estimated changes
Added src/linear_algebra/affine_space/barycentric_coords.lean
- \+ *lemma* barycentric_coord_apply
- \+ *lemma* barycentric_coord_apply_combination
- \+ *lemma* barycentric_coord_apply_eq
- \+ *lemma* barycentric_coord_apply_neq
- \+ *lemma* basis_of_aff_ind_span_eq_top_apply

Modified src/linear_algebra/affine_space/basic.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.coe_sum_coords
- \+ *lemma* basis.coe_sum_coords_eq_finsum
- \+ *lemma* basis.coe_sum_coords_of_fintype
- \+/\- *def* basis.coord
- \+ *lemma* basis.sum_coords_self_apply



## [2021-10-01 23:08:54](https://github.com/leanprover-community/mathlib/commit/06b184f)
refactor(analysis/convex/caratheodory): generalize ℝ to an arbitrary linearly ordered field ([#9479](https://github.com/leanprover-community/mathlib/pull/9479))
As a result; `convex_independent_iff_finset` also gets generalized.
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean
- \+/\- *theorem* eq_pos_convex_span_of_mem_convex_hull

Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/independent.lean
- \+/\- *lemma* convex_independent_iff_finset



## [2021-10-01 20:36:04](https://github.com/leanprover-community/mathlib/commit/118d45a)
doc(ring_theory/subring): fix docstring of `subring.center` ([#9494](https://github.com/leanprover-community/mathlib/pull/9494))
#### Estimated changes
Modified src/ring_theory/subring.lean




## [2021-10-01 20:36:02](https://github.com/leanprover-community/mathlib/commit/e6f8ad7)
refactor(analysis/convex/cone): generalize ℝ to an ordered semiring ([#9481](https://github.com/leanprover-community/mathlib/pull/9481))
Currently, `convex_cone` is only defined in ℝ-modules. This generalizes ℝ to an arbitray ordered semiring. `convex_cone E` is now spelt `convex_cone 𝕜 E`. Similarly, `positive_cone E` becomes `positive_cone 𝕜 E`.
#### Estimated changes
Modified src/analysis/convex/cone.lean
- \+/\- *lemma* convex.mem_to_cone'
- \+/\- *lemma* convex.mem_to_cone
- \+/\- *def* convex.to_cone
- \+/\- *lemma* convex.to_cone_eq_Inf
- \+/\- *lemma* convex.to_cone_is_least
- \+ *lemma* convex_cone.blunt.salient
- \+/\- *def* convex_cone.blunt
- \+ *lemma* convex_cone.blunt_iff_not_pointed
- \+/\- *lemma* convex_cone.coe_inf
- \+/\- *def* convex_cone.comap
- \+/\- *lemma* convex_cone.comap_comap
- \+/\- *lemma* convex_cone.comap_id
- \- *lemma* convex_cone.convex
- \+/\- *theorem* convex_cone.ext'
- \+/\- *theorem* convex_cone.ext
- \+ *lemma* convex_cone.flat.pointed
- \+/\- *def* convex_cone.flat
- \+/\- *def* convex_cone.map
- \+/\- *lemma* convex_cone.map_id
- \+/\- *lemma* convex_cone.map_map
- \+/\- *lemma* convex_cone.mem_Inf
- \+/\- *lemma* convex_cone.mem_bot
- \+/\- *lemma* convex_cone.mem_comap
- \+/\- *lemma* convex_cone.mem_mk
- \+/\- *lemma* convex_cone.mem_top
- \+/\- *def* convex_cone.pointed
- \+/\- *lemma* convex_cone.pointed_iff_not_blunt
- \- *lemma* convex_cone.pointed_of_positive_cone
- \+ *lemma* convex_cone.pointed_positive_cone
- \+/\- *def* convex_cone.positive_cone
- \+/\- *def* convex_cone.salient
- \+/\- *lemma* convex_cone.salient_iff_not_flat
- \- *lemma* convex_cone.salient_of_blunt
- \- *lemma* convex_cone.salient_of_positive_cone
- \+ *lemma* convex_cone.salient_positive_cone
- \+/\- *lemma* convex_cone.smul_mem
- \+/\- *lemma* convex_cone.smul_mem_iff
- \+/\- *def* convex_cone.to_ordered_add_comm_group
- \+/\- *lemma* convex_cone.to_ordered_smul
- \+/\- *def* convex_cone.to_partial_order
- \+/\- *def* convex_cone.to_preorder
- \+/\- *structure* convex_cone
- \+/\- *theorem* riesz_extension



## [2021-10-01 20:36:00](https://github.com/leanprover-community/mathlib/commit/05ee42c)
feat(order/circular): define circular orders ([#9413](https://github.com/leanprover-community/mathlib/pull/9413))
A circular order is the way to formalize positions on a circle. This is very foundational, as a good lot of the order-algebra-topology hierarchy has a circular analog.
#### Estimated changes
Added src/order/circular.lean
- \+ *lemma* btw_cyclic
- \+ *lemma* btw_cyclic_right
- \+ *lemma* btw_iff_not_sbtw
- \+ *lemma* btw_of_sbtw
- \+ *lemma* btw_refl_left
- \+ *lemma* btw_refl_left_right
- \+ *lemma* btw_refl_right
- \+ *lemma* btw_rfl
- \+ *lemma* btw_rfl_left
- \+ *lemma* btw_rfl_left_right
- \+ *lemma* btw_rfl_right
- \+ *lemma* has_btw.btw.antisymm
- \+ *lemma* has_btw.btw.cyclic_left
- \+ *def* has_le.to_has_btw
- \+ *def* has_lt.to_has_sbtw
- \+ *lemma* has_sbtw.sbtw.trans_left
- \+ *def* linear_order.to_circular_order
- \+ *lemma* not_btw_of_sbtw
- \+ *lemma* not_sbtw_of_btw
- \+ *def* partial_order.to_circular_partial_order
- \+ *def* preorder.to_circular_preorder
- \+ *lemma* sbtw_asymm
- \+ *lemma* sbtw_cyclic
- \+ *lemma* sbtw_cyclic_left
- \+ *lemma* sbtw_cyclic_right
- \+ *lemma* sbtw_iff_btw_not_btw
- \+ *lemma* sbtw_iff_not_btw
- \+ *lemma* sbtw_irrefl
- \+ *lemma* sbtw_irrefl_left
- \+ *lemma* sbtw_irrefl_left_right
- \+ *lemma* sbtw_irrefl_right
- \+ *lemma* sbtw_of_btw_not_btw
- \+ *lemma* sbtw_trans_right
- \+ *def* set.cIcc
- \+ *def* set.cIoo
- \+ *lemma* set.compl_cIcc
- \+ *lemma* set.compl_cIoo
- \+ *lemma* set.left_mem_cIcc
- \+ *lemma* set.mem_cIcc
- \+ *lemma* set.mem_cIoo
- \+ *lemma* set.right_mem_cIcc



## [2021-10-01 20:35:59](https://github.com/leanprover-community/mathlib/commit/5c92eb0)
feat(measure_theory/function/conditional_expectation): conditional expectation on real functions equal Radon-Nikodym derivative ([#9378](https://github.com/leanprover-community/mathlib/pull/9378))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.rn_deriv_ae_eq_condexp

Modified src/measure_theory/measure/with_density_vector_measure.lean
- \+ *lemma* measure_theory.integrable.with_densityᵥ_trim_absolutely_continuous
- \+ *lemma* measure_theory.integrable.with_densityᵥ_trim_eq_integral



## [2021-10-01 20:35:58](https://github.com/leanprover-community/mathlib/commit/75d022b)
feat(probability_theory/density): define probability density functions ([#9323](https://github.com/leanprover-community/mathlib/pull/9323))
This PR also proves some elementary properties about probability density function such as the law of the unconscious statistician.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.set_lintegral_lt_top_of_bdd_above
- \+ *lemma* measure_theory.set_lintegral_lt_top_of_is_compact
- \+ *lemma* measure_theory.set_lintegral_mono
- \+ *lemma* measure_theory.set_lintegral_mono_ae
- \+ *lemma* measure_theory.with_density_eq_zero

Added src/probability_theory/density.lean
- \+ *lemma* measure_theory.has_pdf.measurable
- \+ *lemma* measure_theory.map_eq_set_lintegral_pdf
- \+ *lemma* measure_theory.map_eq_with_density_pdf
- \+ *lemma* measure_theory.measurable_of_pdf_ne_zero
- \+ *lemma* measure_theory.measurable_pdf
- \+ *lemma* measure_theory.pdf.ae_lt_top
- \+ *lemma* measure_theory.pdf.has_finite_integral_mul
- \+ *lemma* measure_theory.pdf.has_pdf_iff
- \+ *lemma* measure_theory.pdf.has_pdf_iff_of_measurable
- \+ *lemma* measure_theory.pdf.have_lebesgue_decomposition_of_has_pdf
- \+ *lemma* measure_theory.pdf.integrable_iff_integrable_mul_pdf
- \+ *lemma* measure_theory.pdf.integral_fun_mul_eq_integral
- \+ *lemma* measure_theory.pdf.integral_mul_eq_integral
- \+ *lemma* measure_theory.pdf.lintegral_eq_measure_univ
- \+ *lemma* measure_theory.pdf.map_absolutely_continuous
- \+ *lemma* measure_theory.pdf.of_real_to_real_ae_eq
- \+ *lemma* measure_theory.pdf.quasi_measure_preserving_has_pdf'
- \+ *lemma* measure_theory.pdf.quasi_measure_preserving_has_pdf
- \+ *lemma* measure_theory.pdf.real.has_pdf_iff
- \+ *lemma* measure_theory.pdf.real.has_pdf_iff_of_measurable
- \+ *lemma* measure_theory.pdf.to_quasi_measure_preserving
- \+ *def* measure_theory.pdf
- \+ *lemma* measure_theory.pdf_eq_zero_of_not_measurable
- \+ *lemma* measure_theory.pdf_undef



## [2021-10-01 18:34:46](https://github.com/leanprover-community/mathlib/commit/6354fe9)
feat(topology/algebra): discrete group criterion ([#9488](https://github.com/leanprover-community/mathlib/pull/9488))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* discrete_topology_iff_open_singleton_one



## [2021-10-01 18:34:45](https://github.com/leanprover-community/mathlib/commit/a5fc0a3)
feat(topology/algebra): filters bases for algebra ([#9480](https://github.com/leanprover-community/mathlib/pull/9480))
This is modernized version of code from the perfectoid spaces project.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.mem_smul_of_mem

Modified src/order/filter/bases.lean


Added src/topology/algebra/filter_basis.lean
- \+ *def* group_filter_basis.N
- \+ *lemma* group_filter_basis.N_one
- \+ *lemma* group_filter_basis.conj
- \+ *lemma* group_filter_basis.inv
- \+ *lemma* group_filter_basis.mem_nhds_one
- \+ *lemma* group_filter_basis.mul
- \+ *lemma* group_filter_basis.nhds_eq
- \+ *lemma* group_filter_basis.nhds_has_basis
- \+ *lemma* group_filter_basis.nhds_one_eq
- \+ *lemma* group_filter_basis.nhds_one_has_basis
- \+ *lemma* group_filter_basis.one
- \+ *lemma* group_filter_basis.prod_subset_self
- \+ *def* group_filter_basis.topology
- \+ *def* group_filter_basis_of_comm
- \+ *def* module_filter_basis.of_bases
- \+ *lemma* module_filter_basis.smul
- \+ *lemma* module_filter_basis.smul_left
- \+ *lemma* module_filter_basis.smul_right
- \+ *def* module_filter_basis.topology'
- \+ *def* module_filter_basis.topology
- \+ *structure* module_filter_basis
- \+ *lemma* ring_filter_basis.mul
- \+ *lemma* ring_filter_basis.mul_left
- \+ *lemma* ring_filter_basis.mul_right
- \+ *def* ring_filter_basis.topology

Modified src/topology/algebra/ring.lean
- \+ *lemma* topological_ring.of_add_group_of_nhds_zero
- \+ *lemma* topological_ring.of_nhds_zero



## [2021-10-01 17:21:37](https://github.com/leanprover-community/mathlib/commit/db6d862)
split(analysis/convex/basic): split off `analysis.convex.hull` ([#9477](https://github.com/leanprover-community/mathlib/pull/9477))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \- *lemma* affine_map.image_convex_hull
- \- *lemma* convex.convex_hull_eq
- \- *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \- *lemma* convex_convex_hull
- \- *def* convex_hull
- \- *lemma* convex_hull_empty
- \- *lemma* convex_hull_empty_iff
- \- *lemma* convex_hull_min
- \- *lemma* convex_hull_mono
- \- *lemma* convex_hull_nonempty_iff
- \- *lemma* convex_hull_singleton
- \- *lemma* is_linear_map.convex_hull_image
- \- *lemma* is_linear_map.image_convex_hull
- \- *lemma* linear_map.convex_hull_image
- \- *lemma* linear_map.image_convex_hull
- \- *lemma* subset_convex_hull

Modified src/analysis/convex/combination.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/extreme.lean


Added src/analysis/convex/hull.lean
- \+ *lemma* affine_map.image_convex_hull
- \+ *lemma* convex.convex_hull_eq
- \+ *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \+ *lemma* convex_convex_hull
- \+ *def* convex_hull
- \+ *lemma* convex_hull_empty
- \+ *lemma* convex_hull_empty_iff
- \+ *lemma* convex_hull_min
- \+ *lemma* convex_hull_mono
- \+ *lemma* convex_hull_nonempty_iff
- \+ *lemma* convex_hull_singleton
- \+ *lemma* is_linear_map.convex_hull_image
- \+ *lemma* is_linear_map.image_convex_hull
- \+ *lemma* linear_map.convex_hull_image
- \+ *lemma* linear_map.image_convex_hull
- \+ *lemma* subset_convex_hull



## [2021-10-01 15:54:07](https://github.com/leanprover-community/mathlib/commit/249a015)
chore(ring_theory/coprime): split out imports into a new file so that `is_coprime` can be used earlier. ([#9403](https://github.com/leanprover-community/mathlib/pull/9403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Use.20of.20is_coprime.20in.20rat.2Ebasic/near/254942750)
#### Estimated changes
Modified src/data/polynomial/field_division.lean


Modified src/number_theory/fermat4.lean


Renamed src/ring_theory/coprime.lean to src/ring_theory/coprime/basic.lean
- \- *theorem* finset.prod_dvd_of_coprime
- \- *theorem* fintype.prod_dvd_of_coprime
- \- *theorem* is_coprime.of_prod_left
- \- *theorem* is_coprime.of_prod_right
- \- *theorem* is_coprime.pow
- \- *theorem* is_coprime.pow_iff
- \- *theorem* is_coprime.pow_left
- \- *theorem* is_coprime.pow_left_iff
- \- *theorem* is_coprime.pow_right
- \- *theorem* is_coprime.pow_right_iff
- \- *theorem* is_coprime.prod_left
- \- *theorem* is_coprime.prod_left_iff
- \- *theorem* is_coprime.prod_right
- \- *theorem* is_coprime.prod_right_iff
- \- *theorem* nat.is_coprime_iff_coprime

Added src/ring_theory/coprime/lemmas.lean
- \+ *theorem* finset.prod_dvd_of_coprime
- \+ *theorem* fintype.prod_dvd_of_coprime
- \+ *theorem* is_coprime.of_prod_left
- \+ *theorem* is_coprime.of_prod_right
- \+ *theorem* is_coprime.pow
- \+ *theorem* is_coprime.pow_iff
- \+ *theorem* is_coprime.pow_left
- \+ *theorem* is_coprime.pow_left_iff
- \+ *theorem* is_coprime.pow_right
- \+ *theorem* is_coprime.pow_right_iff
- \+ *theorem* is_coprime.prod_left
- \+ *theorem* is_coprime.prod_left_iff
- \+ *theorem* is_coprime.prod_right
- \+ *theorem* is_coprime.prod_right_iff
- \+ *theorem* nat.is_coprime_iff_coprime

Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/int/basic.lean




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
Added counterexamples/direct_sum_is_internal.lean
- \+ *lemma* mem_with_sign_neg_one
- \+ *lemma* mem_with_sign_one
- \+ *lemma* units_int.one_ne_neg_one
- \+ *def* with_sign.independent
- \+ *lemma* with_sign.is_compl
- \+ *lemma* with_sign.not_injective
- \+ *lemma* with_sign.not_internal
- \+ *lemma* with_sign.supr
- \+ *def* with_sign

Modified src/algebra/direct_sum/module.lean
- \+ *lemma* direct_sum.submodule_is_internal.independent
- \+ *lemma* direct_sum.submodule_is_internal_iff_independent_and_supr_eq_top
- \+ *lemma* direct_sum.submodule_is_internal_of_independent_of_supr_eq_top

Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* complete_lattice.independent.dfinsupp_lsum_injective
- \+ *lemma* complete_lattice.independent_iff_dfinsupp_lsum_injective
- \+ *lemma* complete_lattice.independent_iff_forall_dfinsupp
- \+ *lemma* complete_lattice.independent_of_dfinsupp_lsum_injective
- \+ *lemma* dfinsupp.lsum_single



## [2021-10-01 13:24:12](https://github.com/leanprover-community/mathlib/commit/9be12dd)
feat(order/locally_finite): introduce locally finite orders ([#9464](https://github.com/leanprover-community/mathlib/pull/9464))
The new typeclass `locally_finite_order` homogeneizes treatment of intervals as `finset`s and `multiset`s. `finset.Ico` is now available for all locally finite orders (instead of being ℕ-specialized), rendering `finset.Ico_ℤ` and `pnat.Ico` useless.
This PR also introduces the long-awaited `finset.Icc`, `finset.Ioc`, `finset.Ioo`, and `finset.Ici`, `finset.Ioi` (for `order_top`s) and `finset.Iic`, `finset.Iio` (for `order_bot`s), and the `multiset` variations thereof.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* and_and_and_comm

Added src/order/locally_finite.lean
- \+ *def* finset.Icc
- \+ *def* finset.Ici
- \+ *lemma* finset.Ici_eq_Icc
- \+ *def* finset.Iic
- \+ *lemma* finset.Iic_eq_Icc
- \+ *def* finset.Ioc
- \+ *def* finset.Ioi
- \+ *lemma* finset.Ioi_eq_Ioc
- \+ *def* finset.Ioo
- \+ *lemma* finset.coe_Icc
- \+ *lemma* finset.coe_Ici
- \+ *lemma* finset.coe_Iic
- \+ *lemma* finset.coe_Ioc
- \+ *lemma* finset.coe_Ioi
- \+ *lemma* finset.coe_Ioo
- \+ *lemma* finset.map_subtype_embedding_Icc
- \+ *lemma* finset.map_subtype_embedding_Ioc
- \+ *lemma* finset.map_subtype_embedding_Ioo
- \+ *lemma* finset.mem_Icc
- \+ *lemma* finset.mem_Ici
- \+ *lemma* finset.mem_Iic
- \+ *lemma* finset.mem_Ioc
- \+ *lemma* finset.mem_Ioi
- \+ *lemma* finset.mem_Ioo
- \+ *lemma* finset.subtype_Icc_eq
- \+ *lemma* finset.subtype_Ioc_eq
- \+ *lemma* finset.subtype_Ioo_eq
- \+ *def* locally_finite_order.of_Icc'
- \+ *def* locally_finite_order.of_Icc
- \+ *def* multiset.Icc
- \+ *def* multiset.Ici
- \+ *def* multiset.Iic
- \+ *def* multiset.Ioc
- \+ *def* multiset.Ioi
- \+ *def* multiset.Ioo
- \+ *lemma* multiset.mem_Icc
- \+ *lemma* multiset.mem_Ici
- \+ *lemma* multiset.mem_Iic
- \+ *lemma* multiset.mem_Ioc
- \+ *lemma* multiset.mem_Ioi
- \+ *lemma* multiset.mem_Ioo
- \+ *lemma* set.finite_Icc
- \+ *lemma* set.finite_Ici
- \+ *lemma* set.finite_Iic
- \+ *lemma* set.finite_Ioc
- \+ *lemma* set.finite_Ioi
- \+ *lemma* set.finite_Ioo



## [2021-10-01 13:24:10](https://github.com/leanprover-community/mathlib/commit/62b8c1f)
feat(order/basic): Antitone functions ([#9119](https://github.com/leanprover-community/mathlib/pull/9119))
Define `antitone` and `strict_anti`. Use them where they already were used in expanded form. Rename lemmas accordingly.
Provide a few more `order_dual` results, and rename `monotone.order_dual` to `monotone.dual`.
Restructure `order.basic`. Now, monotone stuff can easily be singled out to go in a new file `order.monotone` if wanted. It represents 587 out of the 965 lines.
#### Estimated changes
Modified src/algebra/order/functions.lean
- \+ *lemma* antitone.map_max
- \+ *lemma* antitone.map_min

Modified src/algebra/order/monoid_lemmas.lean
- \+/\- *lemma* monotone.mul_strict_mono'
- \+/\- *lemma* strict_mono.mul'

Modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* antitone_of_deriv_nonpos
- \- *theorem* concave_on_of_deriv_antitone
- \+ *theorem* concave_on_of_deriv_antitone_on
- \+ *theorem* convex.antitone_on_of_deriv_nonpos
- \- *theorem* convex.strict_anti_of_deriv_neg
- \+ *theorem* convex.strict_anti_on_of_deriv_neg
- \- *theorem* convex.strict_mono_of_deriv_pos
- \+ *theorem* convex.strict_mono_on_of_deriv_pos
- \- *theorem* convex_on_of_deriv_mono
- \+ *theorem* convex_on_of_deriv_monotone_on
- \- *theorem* convex_on_univ_of_deriv_mono
- \+ *theorem* convex_on_univ_of_deriv_monotone
- \+ *theorem* monotone_of_deriv_nonneg
- \- *theorem* monotone_on_of_deriv_nonneg

Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_sin_pow_antitone

Modified src/data/complex/exponential.lean
- \- *lemma* forall_ge_le_of_forall_le_succ

Modified src/data/set/function.lean
- \+ *lemma* strict_anti_on.comp
- \+ *lemma* strict_anti_on.comp_strict_mono_on
- \- *lemma* strict_mono.comp_strict_mono_on
- \+ *lemma* strict_mono_on.comp_strict_anti_on

Modified src/data/set/intervals/surj_on.lean


Modified src/data/setoid/basic.lean


Modified src/group_theory/nilpotent.lean
- \+/\- *lemma* lower_central_series_antitone

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* antitone.integrable_on_compact
- \+/\- *lemma* antitone_on.integrable_on_compact
- \+/\- *lemma* monotone_on.integrable_on_compact

Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* antitone.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* monotone_on.interval_integrable

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/number_theory/pell.lean
- \+ *theorem* pell.strict_mono_x
- \+ *theorem* pell.strict_mono_y
- \- *theorem* pell.x_increasing
- \- *theorem* pell.y_increasing

Modified src/order/basic.lean
- \+ *lemma* antitone.comp_monotone
- \+ *lemma* antitone.comp_monotone_on
- \+ *lemma* antitone.ne_of_lt_of_lt_int
- \+ *lemma* antitone.ne_of_lt_of_lt_nat
- \+ *lemma* antitone.reflect_lt
- \+ *lemma* antitone.strict_anti_iff_injective
- \+ *lemma* antitone.strict_anti_of_injective
- \+ *def* antitone
- \+ *theorem* antitone_app
- \+ *theorem* antitone_const
- \+ *theorem* antitone_lam
- \+ *lemma* antitone_nat_of_succ_le
- \+ *def* antitone_on
- \+ *lemma* antitone_on_univ
- \- *theorem* comp_le_comp_left_of_monotone
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+ *lemma* monotone.comp_antitone
- \+ *lemma* monotone.comp_antitone_on
- \+ *theorem* monotone.comp_le_comp_left
- \+/\- *lemma* monotone.ne_of_lt_of_lt_int
- \+/\- *lemma* monotone.ne_of_lt_of_lt_nat
- \+/\- *lemma* monotone.reflect_lt
- \+/\- *lemma* monotone.strict_mono_iff_injective
- \+/\- *lemma* monotone.strict_mono_of_injective
- \+/\- *theorem* monotone_app
- \+/\- *theorem* monotone_const
- \+ *lemma* monotone_id
- \- *theorem* monotone_id
- \+/\- *theorem* monotone_lam
- \+ *def* monotone_on
- \+ *lemma* monotone_on_univ
- \+ *lemma* strict_anti.comp_strict_mono
- \+ *lemma* strict_anti.comp_strict_mono_on
- \+ *lemma* strict_anti.injective
- \+ *lemma* strict_anti.le_iff_le
- \+ *lemma* strict_anti.lt_iff_lt
- \+ *lemma* strict_anti.maximal_of_minimal_image
- \+ *lemma* strict_anti.minimal_of_maximal_image
- \+ *def* strict_anti
- \+ *lemma* strict_anti_nat_of_succ_lt
- \+/\- *lemma* strict_anti_on.le_iff_le
- \+/\- *lemma* strict_anti_on.lt_iff_lt
- \+/\- *def* strict_anti_on
- \+ *lemma* strict_anti_on_univ
- \- *lemma* strict_mono.comp
- \+ *lemma* strict_mono.comp_strict_anti
- \+ *lemma* strict_mono.comp_strict_anti_on
- \+/\- *lemma* strict_mono.id_le
- \+/\- *lemma* strict_mono.injective
- \+/\- *lemma* strict_mono.le_iff_le
- \+/\- *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_mono.maximal_of_maximal_image
- \- *lemma* strict_mono.maximal_preimage_top
- \+ *lemma* strict_mono.minimal_of_minimal_image
- \- *lemma* strict_mono.minimal_preimage_bot
- \- *lemma* strict_mono.monotone
- \- *theorem* strict_mono.order_dual
- \+/\- *def* strict_mono
- \+/\- *lemma* strict_mono_id
- \+/\- *lemma* strict_mono_nat_of_lt_succ
- \+/\- *lemma* strict_mono_on.le_iff_le
- \+/\- *lemma* strict_mono_on.lt_iff_lt
- \+/\- *def* strict_mono_on
- \+ *lemma* strict_mono_on_univ

Modified src/order/bounded_lattice.lean
- \- *lemma* strict_mono.maximal_preimage_top'
- \+ *lemma* strict_mono.maximal_preimage_top
- \- *lemma* strict_mono.minimal_preimage_bot'
- \+ *lemma* strict_mono.minimal_preimage_bot

Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/ennreal.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/indicator_function.lean


Modified src/order/galois_connection.lean


Modified src/order/iterate.lean


Modified src/order/lattice.lean
- \+/\- *theorem* monotone.forall_le_of_antitone

Modified src/order/modular_lattice.lean


Modified src/order/ord_continuous.lean


Modified src/order/preorder_hom.lean


Modified src/testing/slim_check/functions.lean


Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* exists_seq_strict_anti_tendsto'
- \+ *lemma* exists_seq_strict_anti_tendsto
- \- *lemma* exists_seq_strict_antitone_tendsto'
- \- *lemma* exists_seq_strict_antitone_tendsto
- \+ *lemma* is_glb.exists_seq_antitone_tendsto'
- \+ *lemma* is_glb.exists_seq_antitone_tendsto
- \- *lemma* is_glb.exists_seq_monotone_tendsto'
- \- *lemma* is_glb.exists_seq_monotone_tendsto
- \+ *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem'
- \+ *lemma* is_glb.exists_seq_strict_anti_tendsto_of_not_mem
- \- *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem'
- \- *lemma* is_glb.exists_seq_strict_mono_tendsto_of_not_mem
- \+/\- *lemma* tendsto_at_bot_csupr
- \+/\- *lemma* tendsto_at_bot_is_lub
- \+/\- *lemma* tendsto_at_bot_supr
- \+/\- *lemma* tendsto_at_top_cinfi
- \+/\- *lemma* tendsto_at_top_infi
- \+/\- *lemma* tendsto_at_top_is_glb

Modified src/topology/local_extr.lean


Modified src/topology/semicontinuous.lean




## [2021-10-01 13:24:08](https://github.com/leanprover-community/mathlib/commit/d6bf2dd)
refactor(*): replace `abs` with vertical bar notation ([#8891](https://github.com/leanprover-community/mathlib/pull/8891))
The notion of an "absolute value" occurs both in algebra (e.g. lattice ordered groups) and analysis (e.g. GM and GL-spaces). I introduced a `has_abs` notation class in [#9172](https://github.com/leanprover-community/mathlib/pull/9172), along with the  conventional mathematical vertical bar notation `|.|` for `abs`.
The notation vertical bar notation was already in use in some files as a local notation. This PR replaces `abs` with the vertical bar notation throughout mathlib.
#### Estimated changes
Modified archive/imo/imo2006_q3.lean


Modified archive/imo/imo2008_q4.lean
- \+/\- *lemma* abs_eq_one_of_pow_eq_one

Modified archive/sensitivity.lean


Modified counterexamples/phillips.lean


Modified src/algebra/archimedean.lean
- \+/\- *lemma* abs_sub_round

Modified src/algebra/big_operators/order.lean


Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/field_power.lean


Modified src/algebra/floor.lean


Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* abs_pow

Modified src/algebra/group_power/order.lean
- \+/\- *theorem* abs_le_abs_of_sq_le_sq
- \+/\- *theorem* abs_le_of_sq_le_sq
- \+/\- *theorem* abs_lt_abs_of_sq_lt_sq
- \+/\- *theorem* abs_lt_of_sq_lt_sq
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *theorem* abs_sq
- \+/\- *lemma* pow_abs
- \+/\- *theorem* sq_abs
- \+/\- *theorem* sq_le_sq
- \+/\- *theorem* sq_lt_sq

Modified src/algebra/order/field.lean
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_inv
- \+/\- *lemma* abs_one_div

Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_add
- \+/\- *lemma* abs_add_three
- \+/\- *lemma* abs_by_cases
- \+/\- *lemma* abs_choice
- \+/\- *lemma* abs_eq
- \+/\- *lemma* abs_eq_abs
- \+/\- *lemma* abs_eq_zero
- \+/\- *lemma* abs_le'
- \+/\- *lemma* abs_le
- \+/\- *theorem* abs_le_abs
- \+/\- *lemma* abs_le_max_abs_abs
- \+/\- *lemma* abs_lt
- \+/\- *lemma* abs_max_sub_max_le_abs
- \+/\- *lemma* abs_neg
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_nonpos_iff
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_sub_comm
- \+/\- *lemma* abs_sub_le
- \+/\- *lemma* abs_sub_le_iff
- \+/\- *lemma* abs_sub_lt_iff
- \+/\- *lemma* abs_zero
- \+/\- *lemma* eq_of_abs_sub_eq_zero
- \+/\- *lemma* eq_of_abs_sub_nonpos
- \+/\- *lemma* eq_or_eq_neg_of_abs_eq
- \+/\- *lemma* le_abs
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* le_of_abs_le
- \+/\- *lemma* lt_abs
- \+/\- *lemma* lt_of_abs_lt
- \+/\- *lemma* max_sub_min_eq_abs'
- \+/\- *lemma* max_sub_min_eq_abs
- \+/\- *lemma* neg_abs_le_self
- \+/\- *lemma* neg_le_abs_self
- \+/\- *lemma* neg_le_of_abs_le
- \+/\- *lemma* neg_lt_of_abs_lt
- \+/\- *lemma* sub_le_of_abs_sub_le_left
- \+/\- *lemma* sub_le_of_abs_sub_le_right
- \+/\- *lemma* sub_lt_of_abs_sub_lt_left
- \+/\- *lemma* sub_lt_of_abs_sub_lt_right

Modified src/algebra/order/ring.lean
- \+/\- *lemma* abs_cases
- \+/\- *lemma* abs_dvd
- \+/\- *lemma* abs_dvd_abs
- \+/\- *lemma* abs_dvd_self
- \+/\- *lemma* abs_eq_iff_mul_self_eq
- \+/\- *lemma* abs_eq_neg_self
- \+/\- *lemma* abs_eq_self
- \+/\- *lemma* abs_le_iff_mul_self_le
- \+/\- *lemma* abs_le_one_iff_mul_self_le_one
- \+/\- *lemma* abs_lt_iff_mul_self_lt
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_sub_sq
- \+/\- *lemma* abs_two
- \+/\- *lemma* dvd_abs
- \+/\- *lemma* even_abs
- \+/\- *lemma* self_dvd_abs

Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/complex/basic.lean
- \+/\- *lemma* complex.norm_int

Modified src/analysis/convex/topology.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* abs_norm_eq_norm
- \+/\- *lemma* abs_norm_sub_norm_le
- \+/\- *lemma* int.norm_eq_abs
- \+/\- *lemma* real.norm_eq_abs

Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* real.abs_log_sub_add_sum_range_le
- \+/\- *lemma* real.exp_log_eq_abs
- \+/\- *theorem* real.has_sum_pow_div_log_of_abs_lt_1
- \+/\- *lemma* real.log_abs
- \+/\- *lemma* real.log_of_ne_zero

Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* real.abs_rpow_le_abs_rpow
- \+/\- *lemma* real.abs_rpow_le_exp_log_mul
- \+/\- *lemma* real.abs_rpow_of_nonneg

Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/analysis/specific_limits.lean
- \+/\- *lemma* has_sum_geometric_of_abs_lt_1
- \+/\- *lemma* is_o_pow_pow_of_abs_lt_left
- \+/\- *lemma* summable_geometric_of_abs_lt_1
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_abs_lt_1
- \+/\- *lemma* tendsto_pow_const_mul_const_pow_of_abs_lt_one
- \+/\- *lemma* tsum_geometric_of_abs_lt_1

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_abs
- \+/\- *lemma* complex.abs_abs_sub_le_abs_sub
- \+/\- *lemma* complex.abs_im_div_abs_le_one
- \+/\- *lemma* complex.abs_im_le_abs
- \+/\- *lemma* complex.abs_le_abs_re_add_abs_im
- \+/\- *lemma* complex.abs_of_real
- \+/\- *lemma* complex.abs_re_div_abs_le_one
- \+/\- *lemma* complex.abs_re_le_abs
- \+/\- *lemma* complex.int_cast_abs

Modified src/data/complex/exponential.lean
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* is_cau_of_decreasing_bounded
- \+/\- *lemma* is_cau_of_mono_bounded
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* real.abs_cos_le_one
- \+/\- *lemma* real.abs_exp
- \+/\- *lemma* real.abs_sin_le_one
- \+/\- *lemma* real.cos_bound
- \+/\- *lemma* real.cos_pos_of_le_one
- \+/\- *lemma* real.exp_bound
- \+/\- *lemma* real.sin_bound

Modified src/data/int/basic.lean
- \+/\- *theorem* int.abs_div_le_abs
- \+/\- *theorem* int.abs_eq_nat_abs
- \+/\- *theorem* int.coe_nat_abs
- \+/\- *theorem* int.div_eq_zero_of_lt_abs
- \+/\- *lemma* int.eq_zero_iff_abs_lt_one
- \+/\- *theorem* int.mod_abs
- \+/\- *theorem* int.mod_lt
- \+/\- *theorem* int.nat_abs_abs
- \+/\- *theorem* int.sign_mul_abs

Modified src/data/int/cast.lean
- \+/\- *lemma* int.cast_nat_abs

Modified src/data/int/modeq.lean


Modified src/data/nat/cast.lean


Modified src/data/polynomial/denoms_clearable.lean


Modified src/data/rat/cast.lean


Modified src/data/rat/order.lean
- \+/\- *theorem* rat.abs_def

Modified src/data/rat/sqrt.lean
- \+/\- *theorem* rat.sqrt_eq

Modified src/data/real/basic.lean
- \+/\- *theorem* real.is_cau_seq_iff_lift

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.coe_abs
- \+/\- *lemma* hyperreal.infinite_iff_abs_lt_abs
- \+/\- *lemma* hyperreal.infinite_iff_infinite_abs
- \+/\- *lemma* hyperreal.infinite_iff_infinite_pos_abs
- \+/\- *lemma* hyperreal.infinite_pos_abs_iff_infinite_abs

Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.abs_eq
- \+/\- *lemma* real.coe_nnabs
- \+/\- *lemma* real.coe_to_nnreal_le

Modified src/data/real/sqrt.lean
- \+/\- *theorem* real.abs_le_sqrt
- \+/\- *theorem* real.sqrt_mul_self_eq_abs
- \+/\- *theorem* real.sqrt_sq_eq_abs

Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/unordered_interval.lean
- \+/\- *lemma* set.abs_sub_le_of_subinterval
- \+/\- *lemma* set.abs_sub_left_of_mem_interval
- \+/\- *lemma* set.abs_sub_right_of_mem_interval

Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integral.norm_integral_le_abs_integral_norm

Modified src/measure_theory/measure/lebesgue.lean
- \+/\- *lemma* real.volume_interval

Modified src/number_theory/liouville/basic.lean
- \+/\- *def* liouville

Modified src/number_theory/liouville/liouville_constant.lean


Modified src/number_theory/primes_congruent_one.lean


Modified src/number_theory/zsqrtd/gaussian_int.lean
- \+/\- *lemma* gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le

Modified src/order/filter/filter_product.lean
- \+/\- *lemma* filter.germ.abs_def

Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* max_eq_half_add_add_abs_sub
- \+/\- *lemma* min_eq_half_add_sub_abs_sub

Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/weierstrass.lean


Modified src/topology/instances/real.lean
- \+/\- *theorem* int.dist_eq
- \+/\- *theorem* rat.dist_eq
- \+/\- *lemma* real.uniform_continuous_inv

Modified src/topology/metric_space/algebra.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* abs_dist
- \+/\- *theorem* abs_dist_sub_le
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *theorem* real.dist_0_eq_abs
- \+/\- *theorem* real.dist_eq

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/kuratowski.lean


Modified test/push_neg.lean




## [2021-10-01 12:27:23](https://github.com/leanprover-community/mathlib/commit/c33407a)
feat(algebraic_geometry/*): Proved Spec ⋙ Γ ≅ 𝟭 ([#9416](https://github.com/leanprover-community/mathlib/pull/9416))
- Specialied `algebraic_geometry.structure_sheaf.basic_open_iso` into global sections, proving that the map `structure_sheaf.to_open R ⊤` is an isomorphism in `algebraic_geometry.is_iso_to_global`.
- Proved that the map `R ⟶ Γ(Spec R)` is natural, and presents the fact above as an natural isomorphism `Spec.right_op ⋙ Γ ≅ 𝟭 _` in `algebraic_geometry.Spec_Γ_identity`.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean
- \+ *def* algebraic_geometry.Spec_Γ_identity
- \+ *lemma* algebraic_geometry.Spec_Γ_naturality
- \+ *def* algebraic_geometry.to_Spec_Γ

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *def* algebraic_geometry.structure_sheaf.global_sections_iso
- \+ *lemma* algebraic_geometry.structure_sheaf.global_sections_iso_hom
- \+ *lemma* algebraic_geometry.structure_sheaf.to_global_factors



## [2021-10-01 10:38:53](https://github.com/leanprover-community/mathlib/commit/38395ed)
chore(bors): bors should block on label awaiting-CI ([#9478](https://github.com/leanprover-community/mathlib/pull/9478))
#### Estimated changes
Modified bors.toml


Modified docs/contribute/bors.md




## [2021-10-01 10:38:52](https://github.com/leanprover-community/mathlib/commit/5936f53)
feat(topology/maps): for a continuous open map, preimage and interior commute ([#9471](https://github.com/leanprover-community/mathlib/pull/9471))
#### Estimated changes
Modified src/topology/basic.lean


Modified src/topology/maps.lean
- \+ *lemma* is_open_map.interior_preimage_subset_preimage_interior
- \+ *lemma* is_open_map.preimage_interior_eq_interior_preimage



## [2021-10-01 10:38:51](https://github.com/leanprover-community/mathlib/commit/265345c)
feat(linear_algebra/{bilinear,quadratic}_form): remove non-degeneracy requirement from `exists_orthogonal_basis` and Sylvester's law of inertia ([#9465](https://github.com/leanprover-community/mathlib/pull/9465))
This removes the `nondegenerate` hypothesis from `bilin_form.exists_orthogonal_basis`, and removes the `∀ i, B (v i) (v i) ≠ 0` statement from the goal. This property can be recovered in the case of a nondegenerate form with `is_Ortho.not_is_ortho_basis_self_of_nondegenerate`.
This also swaps the order of the binders in `is_Ortho` to make it expressible with `pairwise`.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.is_Ortho.nondegenerate_iff_not_is_ortho_basis_self
- \+ *lemma* bilin_form.is_Ortho.not_is_ortho_basis_self_of_nondegenerate

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* bilin_form.exists_bilin_form_self_ne_zero
- \- *lemma* bilin_form.exists_bilin_form_self_neq_zero
- \- *lemma* bilin_form.exists_orthogonal_basis'
- \+ *lemma* bilin_form.exists_orthogonal_basis
- \- *theorem* bilin_form.exists_orthogonal_basis
- \+ *lemma* bilin_form.to_quadratic_form_zero
- \+ *lemma* quadratic_form.basis_repr_eq_of_is_Ortho
- \+ *theorem* quadratic_form.equivalent_one_zero_neg_one_weighted_sum_squared
- \+ *lemma* quadratic_form.equivalent_weighted_sum_squares
- \- *lemma* quadratic_form.equivalent_weighted_sum_squares_of_nondegenerate'
- \+ *lemma* quadratic_form.equivalent_weighted_sum_squares_units_of_nondegenerate'
- \+ *lemma* quadratic_form.exists_quadratic_form_ne_zero
- \- *lemma* quadratic_form.exists_quadratic_form_neq_zero
- \+ *lemma* quadratic_form.isometry.coe_to_linear_equiv
- \+ *lemma* quadratic_form.isometry.to_linear_equiv_eq_coe
- \- *lemma* quadratic_form.isometry_of_is_Ortho_apply



## [2021-10-01 10:38:49](https://github.com/leanprover-community/mathlib/commit/74457cb)
feat(data/polynomial,field_theory): `(minpoly A x).map f ≠ 1` ([#9451](https://github.com/leanprover-community/mathlib/pull/9451))
We use this result to generalize `minpoly.not_is_unit` from integral domains to nontrivial `comm_ring`s.
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic.eq_one_of_map_eq_one

Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.map_ne_one
- \+ *lemma* minpoly.ne_one
- \+/\- *lemma* minpoly.not_is_unit



## [2021-10-01 08:55:56](https://github.com/leanprover-community/mathlib/commit/f7d7a91)
feat(algebraic_geometry/ringed_space): Define basic opens for ringed spaces. ([#9358](https://github.com/leanprover-community/mathlib/pull/9358))
Defines the category of ringed spaces, as an alias for `SheafedSpace CommRing`. We provide basic lemmas about sections being units in the stalk and define basic opens in this context.
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_RingedSpace

Added src/algebraic_geometry/ringed_space.lean
- \+ *def* algebraic_geometry.RingedSpace.basic_open
- \+ *lemma* algebraic_geometry.RingedSpace.is_unit_of_is_unit_germ
- \+ *lemma* algebraic_geometry.RingedSpace.is_unit_res_basic_open
- \+ *lemma* algebraic_geometry.RingedSpace.is_unit_res_of_is_unit_germ
- \+ *lemma* algebraic_geometry.RingedSpace.mem_basic_open
- \+ *abbreviation* algebraic_geometry.RingedSpace



## [2021-10-01 08:55:55](https://github.com/leanprover-community/mathlib/commit/9235c8a)
feat(data/polynomial/basic): polynomial.update ([#9020](https://github.com/leanprover-community/mathlib/pull/9020))
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.coeff_update
- \+ *lemma* polynomial.coeff_update_apply
- \+ *lemma* polynomial.coeff_update_ne
- \+ *lemma* polynomial.coeff_update_same
- \+ *lemma* polynomial.support_update
- \+ *lemma* polynomial.support_update_ne_zero
- \+ *lemma* polynomial.support_update_zero
- \+ *def* polynomial.update
- \+ *lemma* polynomial.update_zero_eq_erase

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.update_eq_add_sub_coeff

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_update_le



## [2021-10-01 06:05:13](https://github.com/leanprover-community/mathlib/commit/e0f7d0e)
feat(group_theory/complement): is_complement_iff_card_mul_and_disjoint ([#9476](https://github.com/leanprover-community/mathlib/pull/9476))
Adds the converse to an existing lemma `is_complement_of_disjoint` (renamed `is_complement_of_card_mul_and_disjoint`).
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement.card_mul
- \+ *lemma* subgroup.is_complement.disjoint
- \+ *lemma* subgroup.is_complement_iff_card_mul_and_disjoint
- \+ *lemma* subgroup.is_complement_of_card_mul_and_disjoint
- \- *lemma* subgroup.is_complement_of_disjoint



## [2021-10-01 06:05:12](https://github.com/leanprover-community/mathlib/commit/57fa903)
refactor(group_theory/complement): Split `complement.lean` ([#9474](https://github.com/leanprover-community/mathlib/pull/9474))
Splits off Schur-Zassenhaus from `complement.lean`. In the new file, we can replace `fintype.card (quotient_group.quotient H)` with `H.index`.
Advantages: We can avoid importing `cardinal.lean` in `complement.lean`. Later (once full SZ is proved), we can avoid importing `sylow.lean` in `complement.lean`.
#### Estimated changes
Modified src/group_theory/complement.lean
- \- *lemma* subgroup.diff_inv
- \- *lemma* subgroup.diff_mul_diff
- \- *lemma* subgroup.diff_self
- \- *theorem* subgroup.exists_left_complement_of_coprime
- \- *theorem* subgroup.exists_right_complement_of_coprime
- \- *lemma* subgroup.exists_smul_eq
- \- *lemma* subgroup.is_complement_stabilizer_of_coprime
- \- *def* subgroup.quotient_diff
- \- *lemma* subgroup.smul_diff
- \- *lemma* subgroup.smul_diff_smul
- \- *lemma* subgroup.smul_left_injective
- \- *lemma* subgroup.smul_symm_apply_eq_mul_symm_apply_inv_smul

Added src/group_theory/schur_zassenhaus.lean
- \+ *lemma* subgroup.diff_inv
- \+ *lemma* subgroup.diff_mul_diff
- \+ *lemma* subgroup.diff_self
- \+ *theorem* subgroup.exists_left_complement_of_coprime
- \+ *theorem* subgroup.exists_right_complement_of_coprime
- \+ *lemma* subgroup.exists_smul_eq
- \+ *lemma* subgroup.is_complement_stabilizer_of_coprime
- \+ *def* subgroup.quotient_diff
- \+ *lemma* subgroup.smul_diff
- \+ *lemma* subgroup.smul_diff_smul
- \+ *lemma* subgroup.smul_left_injective
- \+ *lemma* subgroup.smul_symm_apply_eq_mul_symm_apply_inv_smul



## [2021-10-01 06:05:11](https://github.com/leanprover-community/mathlib/commit/76ddb2b)
feat(analysis/normed_space/lattice_ordered_group): introduce normed lattice ordered groups ([#9274](https://github.com/leanprover-community/mathlib/pull/9274))
Motivated by Banach Lattices, this PR introduces normed lattice ordered groups and proves that they are topological lattices. To support this `has_continuous_inf` and `has_continuous_sup` mixin classes are also defined.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_eq_max_neg
- \+ *lemma* abs_eq_sup_neg

Added src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* dual_solid
- \+ *lemma* norm_abs_eq_norm
- \+ *lemma* solid

Added src/topology/order/lattice.lean
- \+ *lemma* continuous.inf
- \+ *lemma* continuous.sup
- \+ *lemma* continuous_inf
- \+ *lemma* continuous_sup



## [2021-10-01 03:25:37](https://github.com/leanprover-community/mathlib/commit/812d6bb)
chore(scripts): update nolints.txt ([#9475](https://github.com/leanprover-community/mathlib/pull/9475))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-10-01 03:25:36](https://github.com/leanprover-community/mathlib/commit/125dac8)
feat(group_theory/sylow): The number of Sylow subgroups equals the index of the normalizer ([#9455](https://github.com/leanprover-community/mathlib/pull/9455))
This PR adds further consequences of Sylow's theorems (still for infinite groups, more will be PRed later).
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* card_sylow_dvd_index
- \+ *lemma* card_sylow_eq_card_quotient_normalizer
- \+ *lemma* card_sylow_eq_index_normalizer
- \+ *lemma* sylow.orbit_eq_top
- \+ *lemma* sylow.stabilizer_eq_normalizer



## [2021-10-01 03:25:35](https://github.com/leanprover-community/mathlib/commit/b786443)
chore(algebra/category/*): Added `of_hom` to all of the algebraic categories. ([#9454](https://github.com/leanprover-community/mathlib/pull/9454))
As suggested in the comments of [#9416](https://github.com/leanprover-community/mathlib/pull/9416).
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+ *def* Algebra.of_hom

Modified src/algebra/category/CommRing/basic.lean
- \+ *def* CommRing.of_hom
- \+ *def* CommSemiRing.of_hom
- \+ *def* Ring.of_hom
- \+ *def* SemiRing.of_hom

Modified src/algebra/category/Group/basic.lean
- \+ *def* CommGroup.of_hom
- \+ *def* Group.of_hom

Modified src/algebra/category/Module/basic.lean
- \+ *def* Module.of_hom

Modified src/algebra/category/Mon/basic.lean
- \+ *def* Mon.of_hom

Modified src/algebra/category/Semigroup/basic.lean
- \+ *def* Magma.of_hom
- \+ *def* Semigroup.of_hom



## [2021-10-01 03:25:34](https://github.com/leanprover-community/mathlib/commit/babca8e)
refactor(algebra/group_with_zero): rename lemmas to use ₀ instead of ' ([#9424](https://github.com/leanprover-community/mathlib/pull/9424))
We currently have lots of lemmas for `group_with_zero` that already have a corresponding lemma for `group`. We've dealt with name collisions so far just by adding a prime.
This PR renames these lemmas to use a `₀` suffix instead of a `'`.
In part this is out of desire to reduce our overuse of primes in mathlib names (putting the burden on users to know names, rather than relying on naming conventions).
But it may also help with a problem Daniel Selsam ran into at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mathport.20depending.20on.20mathlib. (Briefly, mathport is also adding primes to names when it encounters name collisions, and these particular primes were causing problems. There are are other potential fixes in the works, but everything helps.)
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified src/algebra/algebra/bilinear.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/field.lean
- \+/\- *lemma* neg_div'
- \+/\- *lemma* ring_hom.map_inv

Modified src/algebra/gcd_monoid/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/conj.lean
- \- *lemma* is_conj_iff'
- \+ *lemma* is_conj_iff₀

Modified src/algebra/group_with_zero/basic.lean
- \- *theorem* commute.inv_inv'
- \+ *theorem* commute.inv_inv₀
- \- *theorem* commute.inv_left'
- \- *theorem* commute.inv_left_iff'
- \+ *theorem* commute.inv_left_iff₀
- \+ *theorem* commute.inv_left₀
- \- *theorem* commute.inv_right'
- \- *theorem* commute.inv_right_iff'
- \+ *theorem* commute.inv_right_iff₀
- \+ *theorem* commute.inv_right₀
- \- *lemma* eq_inv_mul_iff_mul_eq'
- \+ *lemma* eq_inv_mul_iff_mul_eq₀
- \- *lemma* eq_mul_inv_iff_mul_eq'
- \+ *lemma* eq_mul_inv_iff_mul_eq₀
- \- *lemma* inv_eq_one'
- \+ *lemma* inv_eq_one₀
- \- *lemma* inv_inj'
- \- *lemma* inv_injective'
- \+ *lemma* inv_injective₀
- \+ *lemma* inv_inj₀
- \- *lemma* inv_inv'
- \- *lemma* inv_involutive'
- \+ *lemma* inv_involutive₀
- \+ *lemma* inv_inv₀
- \- *lemma* inv_mul_cancel_left'
- \+ *lemma* inv_mul_cancel_left₀
- \- *lemma* inv_mul_cancel_right'
- \+ *lemma* inv_mul_cancel_right₀
- \- *lemma* inv_mul_eq_iff_eq_mul'
- \+ *lemma* inv_mul_eq_iff_eq_mul₀
- \- *lemma* inv_mul_eq_one'
- \+ *lemma* inv_mul_eq_one₀
- \- *lemma* monoid_with_zero_hom.map_inv'
- \+ *lemma* monoid_with_zero_hom.map_inv
- \- *lemma* mul_eq_one_iff_eq_inv'
- \+ *lemma* mul_eq_one_iff_eq_inv₀
- \- *lemma* mul_eq_one_iff_inv_eq'
- \+ *lemma* mul_eq_one_iff_inv_eq₀
- \- *lemma* mul_inv'
- \- *lemma* mul_inv_cancel_left'
- \+ *lemma* mul_inv_cancel_left₀
- \- *lemma* mul_inv_cancel_right'
- \+ *lemma* mul_inv_cancel_right₀
- \- *lemma* mul_inv_eq_iff_eq_mul'
- \+ *lemma* mul_inv_eq_iff_eq_mul₀
- \- *lemma* mul_inv_eq_one'
- \+ *lemma* mul_inv_eq_one₀
- \- *lemma* mul_inv_rev'
- \+ *lemma* mul_inv_rev₀
- \+ *lemma* mul_inv₀
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_right_inj'
- \- *lemma* semiconj_by.inv_right'
- \- *lemma* semiconj_by.inv_right_iff'
- \+ *lemma* semiconj_by.inv_right_iff₀
- \+ *lemma* semiconj_by.inv_right₀
- \- *lemma* semiconj_by.inv_symm_left'
- \- *lemma* semiconj_by.inv_symm_left_iff'
- \+ *lemma* semiconj_by.inv_symm_left_iff₀
- \+ *lemma* semiconj_by.inv_symm_left₀

Modified src/algebra/group_with_zero/defs.lean
- \- *lemma* mul_left_cancel'
- \+ *lemma* mul_left_cancel₀
- \- *lemma* mul_left_injective'
- \+ *lemma* mul_left_injective₀
- \- *lemma* mul_right_cancel'
- \+ *lemma* mul_right_cancel₀
- \- *lemma* mul_right_injective'
- \+ *lemma* mul_right_injective₀

Modified src/algebra/group_with_zero/power.lean
- \- *theorem* inv_pow'
- \+ *theorem* inv_pow₀
- \- *theorem* pow_inv_comm'
- \+ *theorem* pow_inv_comm₀
- \- *theorem* pow_sub'
- \+ *theorem* pow_sub₀
- \- *lemma* units.coe_gpow'
- \+ *lemma* units.coe_gpow₀

Modified src/algebra/module/pi.lean
- \- *lemma* pi.single_smul''
- \+/\- *lemma* pi.single_smul'
- \+ *lemma* pi.single_smul₀

Modified src/algebra/module/pointwise_pi.lean
- \- *lemma* smul_pi'
- \+ *lemma* smul_pi₀

Modified src/algebra/opposites.lean


Modified src/algebra/order/absolute_value.lean


Modified src/algebra/order/field.lean
- \- *def* order_iso.mul_left'
- \+ *def* order_iso.mul_left₀
- \- *def* order_iso.mul_right'
- \+ *def* order_iso.mul_right₀

Modified src/algebra/order/smul.lean


Modified src/algebra/order/with_zero.lean
- \- *lemma* div_le_div'
- \+ *lemma* div_le_div₀
- \- *lemma* inv_le_inv''
- \+ *lemma* inv_le_inv₀
- \- *lemma* inv_lt_inv''
- \+ *lemma* inv_lt_inv₀
- \- *lemma* mul_inv_lt_of_lt_mul'
- \+ *lemma* mul_inv_lt_of_lt_mul₀
- \- *lemma* mul_lt_mul''''
- \+ *lemma* mul_lt_mul₀
- \- *lemma* mul_lt_right'
- \+ *lemma* mul_lt_right₀
- \- *lemma* pow_lt_pow'
- \+ *lemma* pow_lt_pow₀
- \- *lemma* zero_lt_one''
- \+ *lemma* zero_lt_one₀

Modified src/algebra/periodic.lean
- \- *lemma* function.antiperiodic.const_inv_smul'
- \+ *lemma* function.antiperiodic.const_inv_smul₀
- \- *lemma* function.antiperiodic.const_smul'
- \+ *lemma* function.antiperiodic.const_smul₀
- \- *lemma* function.periodic.const_inv_smul'
- \+ *lemma* function.periodic.const_inv_smul₀
- \- *lemma* function.periodic.const_smul'
- \+ *lemma* function.periodic.const_smul₀

Modified src/algebra/pointwise.lean
- \- *lemma* mem_inv_smul_set_iff'
- \+ *lemma* mem_inv_smul_set_iff₀
- \- *lemma* mem_smul_set_iff_inv_smul_mem'
- \+ *lemma* mem_smul_set_iff_inv_smul_mem₀
- \- *lemma* preimage_smul'
- \- *lemma* preimage_smul_inv'
- \+ *lemma* preimage_smul_inv₀
- \+ *lemma* preimage_smul₀
- \- *lemma* set.smul_set_inter'
- \+ *lemma* set.smul_set_inter₀
- \- *lemma* set_smul_subset_iff'
- \+ *lemma* set_smul_subset_iff₀
- \- *lemma* set_smul_subset_set_smul_iff'
- \+ *lemma* set_smul_subset_set_smul_iff₀
- \- *lemma* smul_mem_smul_set_iff'
- \+ *lemma* smul_mem_smul_set_iff₀
- \- *lemma* subset_set_smul_iff'
- \+ *lemma* subset_set_smul_iff₀

Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/star/chsh.lean


Modified src/algebra/support.lean
- \- *lemma* function.mul_support_inv'
- \+ *lemma* function.mul_support_inv₀

Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/function.lean


Modified src/analysis/convex/jensen.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/exponential.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/p_series.lean


Modified src/analysis/seminorm.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/nat/choose/basic.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.inv_epsilon_eq_omega

Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean


Modified src/data/real/sqrt.lean
- \+/\- *lemma* nnreal.sqrt_inv

Modified src/data/set/intervals/image_preimage.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/field_theory/perfect_closure.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/group_theory/group_action/group.lean
- \- *lemma* eq_inv_smul_iff'
- \+ *lemma* eq_inv_smul_iff₀
- \- *lemma* inv_smul_eq_iff'
- \+ *lemma* inv_smul_eq_iff₀
- \- *lemma* inv_smul_smul'
- \+ *lemma* inv_smul_smul₀
- \- *lemma* smul_inv_smul'
- \+ *lemma* smul_inv_smul₀

Modified src/group_theory/specific_groups/cyclic.lean


Modified src/group_theory/subgroup/pointwise.lean
- \- *lemma* add_subgroup.le_pointwise_smul_iff'
- \+ *lemma* add_subgroup.le_pointwise_smul_iff₀
- \- *lemma* add_subgroup.mem_inv_pointwise_smul_iff'
- \+ *lemma* add_subgroup.mem_inv_pointwise_smul_iff₀
- \- *lemma* add_subgroup.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* add_subgroup.mem_pointwise_smul_iff_inv_smul_mem₀
- \- *lemma* add_subgroup.pointwise_smul_le_iff'
- \+ *lemma* add_subgroup.pointwise_smul_le_iff₀
- \- *lemma* add_subgroup.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* add_subgroup.pointwise_smul_le_pointwise_smul_iff₀
- \- *lemma* add_subgroup.smul_mem_pointwise_smul_iff'
- \+ *lemma* add_subgroup.smul_mem_pointwise_smul_iff₀
- \- *lemma* subgroup.le_pointwise_smul_iff'
- \+ *lemma* subgroup.le_pointwise_smul_iff₀
- \- *lemma* subgroup.mem_inv_pointwise_smul_iff'
- \+ *lemma* subgroup.mem_inv_pointwise_smul_iff₀
- \- *lemma* subgroup.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* subgroup.mem_pointwise_smul_iff_inv_smul_mem₀
- \- *lemma* subgroup.pointwise_smul_le_iff'
- \+ *lemma* subgroup.pointwise_smul_le_iff₀
- \- *lemma* subgroup.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* subgroup.pointwise_smul_le_pointwise_smul_iff₀
- \- *lemma* subgroup.smul_mem_pointwise_smul_iff'
- \+ *lemma* subgroup.smul_mem_pointwise_smul_iff₀

Modified src/group_theory/submonoid/center.lean
- \- *lemma* set.div_mem_center'
- \+ *lemma* set.div_mem_center₀
- \- *lemma* set.inv_mem_center'
- \+ *lemma* set.inv_mem_center₀

Modified src/group_theory/submonoid/pointwise.lean
- \- *lemma* add_submonoid.le_pointwise_smul_iff'
- \+ *lemma* add_submonoid.le_pointwise_smul_iff₀
- \- *lemma* add_submonoid.mem_inv_pointwise_smul_iff'
- \+ *lemma* add_submonoid.mem_inv_pointwise_smul_iff₀
- \- *lemma* add_submonoid.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* add_submonoid.mem_pointwise_smul_iff_inv_smul_mem₀
- \- *lemma* add_submonoid.pointwise_smul_le_iff'
- \+ *lemma* add_submonoid.pointwise_smul_le_iff₀
- \- *lemma* add_submonoid.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* add_submonoid.pointwise_smul_le_pointwise_smul_iff₀
- \- *lemma* add_submonoid.smul_mem_pointwise_smul_iff'
- \+ *lemma* add_submonoid.smul_mem_pointwise_smul_iff₀
- \- *lemma* submonoid.le_pointwise_smul_iff'
- \+ *lemma* submonoid.le_pointwise_smul_iff₀
- \- *lemma* submonoid.mem_inv_pointwise_smul_iff'
- \+ *lemma* submonoid.mem_inv_pointwise_smul_iff₀
- \- *lemma* submonoid.mem_pointwise_smul_iff_inv_smul_mem'
- \+ *lemma* submonoid.mem_pointwise_smul_iff_inv_smul_mem₀
- \- *lemma* submonoid.pointwise_smul_le_iff'
- \+ *lemma* submonoid.pointwise_smul_le_iff₀
- \- *lemma* submonoid.pointwise_smul_le_pointwise_smul_iff'
- \+ *lemma* submonoid.pointwise_smul_le_pointwise_smul_iff₀
- \- *lemma* submonoid.smul_mem_pointwise_smul_iff'
- \+ *lemma* submonoid.smul_mem_pointwise_smul_iff₀

Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/group/arithmetic.lean
- \- *lemma* ae_measurable_const_smul_iff'
- \+ *lemma* ae_measurable_const_smul_iff₀
- \- *lemma* ae_measurable_inv_iff'
- \+ *lemma* ae_measurable_inv_iff₀
- \- *lemma* measurable_const_smul_iff'
- \+ *lemma* measurable_const_smul_iff₀
- \- *lemma* measurable_inv_iff'
- \+ *lemma* measurable_inv_iff₀

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/l_series.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/order/filter/at_top_bot.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/ring_theory/valuation/integers.lean


Modified src/ring_theory/valuation/integral.lean


Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/norm_num.lean


Modified src/topology/algebra/group_with_zero.lean
- \- *lemma* continuous.inv'
- \+ *lemma* continuous.inv₀
- \- *lemma* continuous_at.inv'
- \+ *lemma* continuous_at.inv₀
- \- *lemma* continuous_on.inv'
- \+ *lemma* continuous_on.inv₀
- \- *lemma* continuous_on_inv'
- \+ *lemma* continuous_on_inv₀
- \- *lemma* continuous_within_at.inv'
- \+ *lemma* continuous_within_at.inv₀
- \- *lemma* filter.tendsto.inv'
- \+ *lemma* filter.tendsto.inv₀
- \- *lemma* homeomorph.coe_mul_left'
- \+ *lemma* homeomorph.coe_mul_left₀
- \- *lemma* homeomorph.coe_mul_right'
- \+ *lemma* homeomorph.coe_mul_right₀
- \- *lemma* homeomorph.mul_left'_symm_apply
- \+ *lemma* homeomorph.mul_left₀_symm_apply
- \- *lemma* homeomorph.mul_right'_symm_apply
- \+ *lemma* homeomorph.mul_right₀_symm_apply
- \- *lemma* tendsto_inv'
- \+ *lemma* tendsto_inv₀

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/mul_action.lean
- \- *lemma* continuous_at_const_smul_iff'
- \+ *lemma* continuous_at_const_smul_iff₀
- \- *lemma* continuous_const_smul_iff'
- \+ *lemma* continuous_const_smul_iff₀
- \- *lemma* continuous_on_const_smul_iff'
- \+ *lemma* continuous_on_const_smul_iff₀
- \- *lemma* continuous_within_at_const_smul_iff'
- \+ *lemma* continuous_within_at_const_smul_iff₀
- \- *lemma* is_closed_map_smul'
- \+ *lemma* is_closed_map_smul₀
- \- *lemma* is_open_map_smul'
- \+ *lemma* is_open_map_smul₀
- \- *lemma* tendsto_const_smul_iff'
- \+ *lemma* tendsto_const_smul_iff₀

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/instances/nnreal.lean




## [2021-10-01 01:14:03](https://github.com/leanprover-community/mathlib/commit/540fb94)
feat(data/fintype/basic): bijection preserves cardinality ([#9473](https://github.com/leanprover-community/mathlib/pull/9473))
We don't seem to have this lemma yet, so I've added it.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_of_bijective



## [2021-10-01 01:14:02](https://github.com/leanprover-community/mathlib/commit/456db24)
feat(topology/algebra/module): has_continuous_smul ([#9468](https://github.com/leanprover-community/mathlib/pull/9468))
in terms of nice neighborhoods of zero
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *lemma* has_continuous_smul.of_nhds_zero



## [2021-10-01 01:14:00](https://github.com/leanprover-community/mathlib/commit/2b23d2e)
chore(topology/algebra): remove dead code ([#9467](https://github.com/leanprover-community/mathlib/pull/9467))
This code wasn't used and its historically intended use will soon be redone much better. The second file is only a dead import and a misleading comment (referring to the dead code of the *other* file).
#### Estimated changes
Modified src/topology/algebra/group.lean
- \- *lemma* add_group_with_zero_nhd.add_Z
- \- *lemma* add_group_with_zero_nhd.exists_Z_half
- \- *lemma* add_group_with_zero_nhd.neg_Z
- \- *lemma* add_group_with_zero_nhd.nhds_eq
- \- *lemma* add_group_with_zero_nhd.nhds_zero_eq_Z

Modified src/topology/algebra/uniform_group.lean




## [2021-10-01 01:13:59](https://github.com/leanprover-community/mathlib/commit/5b02571)
chore(measure_theory/decomposition/lebesgue): make measurable_space implicit ([#9463](https://github.com/leanprover-community/mathlib/pull/9463))
Whenever the `measurable_space` can be inferred from a `measure` argument, it should be implicit. This PR applies that rule to the Lebesgue decomposition file.
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean
- \+/\- *theorem* measure_theory.measure.eq_rn_deriv
- \+/\- *theorem* measure_theory.measure.eq_singular_part
- \+/\- *lemma* measure_theory.measure.have_lebesgue_decomposition_add
- \+/\- *theorem* measure_theory.measure.have_lebesgue_decomposition_of_finite_measure
- \+/\- *lemma* measure_theory.measure.have_lebesgue_decomposition_spec
- \+/\- *theorem* measure_theory.signed_measure.eq_rn_deriv
- \+/\- *theorem* measure_theory.signed_measure.eq_singular_part
- \+/\- *lemma* measure_theory.signed_measure.have_lebesgue_decomposition_mk
- \+/\- *lemma* measure_theory.signed_measure.mutually_singular_singular_part
- \+/\- *lemma* measure_theory.signed_measure.not_have_lebesgue_decomposition_iff
- \+/\- *lemma* measure_theory.signed_measure.rn_deriv_add
- \+/\- *lemma* measure_theory.signed_measure.rn_deriv_neg
- \+/\- *lemma* measure_theory.signed_measure.rn_deriv_smul
- \+/\- *lemma* measure_theory.signed_measure.rn_deriv_sub
- \+ *def* measure_theory.signed_measure.singular_part(s
- \- *def* measure_theory.signed_measure.singular_part
- \+/\- *lemma* measure_theory.signed_measure.singular_part_mutually_singular
- \+/\- *lemma* measure_theory.signed_measure.singular_part_smul
- \+/\- *lemma* measure_theory.signed_measure.singular_part_total_variation

