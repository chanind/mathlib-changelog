## [2017-12-31 16:53:38-05:00](https://github.com/leanprover-community/mathlib/commit/1bc2ac7)
feat(data/ordinal): is_normal, omin, power/log, CNF, indecomposables,
addition and multiplication of infinite cardinals
#### Estimated changes
Modified algebra/linear_algebra/basic.lean


Modified algebra/module.lean


Modified algebra/order.lean
- \+ *lemma* lt_iff_lt_of_strict_mono

Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/cardinal.lean
- \+ *theorem* cardinal.add_le_add
- \+ *theorem* cardinal.add_le_add_left
- \+ *theorem* cardinal.add_le_add_right
- \+ *theorem* cardinal.add_lt_omega
- \- *theorem* cardinal.add_mono
- \+ *theorem* cardinal.le_add_left
- \+ *theorem* cardinal.le_add_right
- \+/\- *theorem* cardinal.le_iff_exists_add
- \+/\- *theorem* cardinal.le_zero
- \+ *theorem* cardinal.mul_le_mul
- \+ *theorem* cardinal.mul_le_mul_left
- \+ *theorem* cardinal.mul_le_mul_right
- \+ *theorem* cardinal.mul_lt_omega
- \- *theorem* cardinal.mul_mono
- \+ *theorem* cardinal.omega_le
- \+ *theorem* cardinal.one_lt_omega
- \+ *theorem* cardinal.power_le_power_left
- \+ *theorem* cardinal.power_le_power_right
- \- *theorem* cardinal.power_mono_left
- \- *theorem* cardinal.power_mono_right
- \+/\- *theorem* cardinal.zero_le

Modified data/equiv.lean


Modified data/ordinal.lean
- \+ *theorem* cardinal.add_eq_max
- \+ *theorem* cardinal.add_eq_self
- \+ *def* cardinal.aleph'.order_iso
- \+ *theorem* cardinal.aleph'.order_iso_coe
- \+ *def* cardinal.aleph'
- \+ *theorem* cardinal.aleph'_aleph_idx
- \+ *theorem* cardinal.aleph'_is_normal
- \+ *theorem* cardinal.aleph'_le
- \+ *theorem* cardinal.aleph'_le_of_limit
- \+ *theorem* cardinal.aleph'_lt
- \+ *theorem* cardinal.aleph'_nat
- \+ *theorem* cardinal.aleph'_omega
- \+ *theorem* cardinal.aleph'_succ
- \+ *theorem* cardinal.aleph'_zero
- \+ *def* cardinal.aleph
- \+ *theorem* cardinal.aleph_idx_aleph'
- \+ *theorem* cardinal.aleph_is_limit
- \+ *theorem* cardinal.aleph_is_normal
- \+ *theorem* cardinal.aleph_le
- \+ *theorem* cardinal.aleph_lt
- \+ *theorem* cardinal.aleph_succ
- \+ *theorem* cardinal.aleph_zero
- \+ *theorem* cardinal.exists_aleph
- \+ *theorem* cardinal.mul_eq_max
- \+ *theorem* cardinal.mul_eq_self
- \+ *theorem* cardinal.omega_le_aleph'
- \+ *theorem* cardinal.omega_le_aleph
- \+ *theorem* cardinal.ord_card_le
- \+ *def* cof
- \+ *def* ordinal.CNF
- \+ *theorem* ordinal.CNF_aux
- \+ *theorem* ordinal.CNF_foldr
- \+ *theorem* ordinal.CNF_fst_le
- \+ *theorem* ordinal.CNF_fst_le_log
- \+ *theorem* ordinal.CNF_ne_zero
- \+ *theorem* ordinal.CNF_pairwise
- \+ *theorem* ordinal.CNF_pairwise_aux
- \+ *theorem* ordinal.CNF_rec_ne_zero
- \+ *theorem* ordinal.CNF_rec_zero
- \+ *theorem* ordinal.CNF_snd_lt
- \+ *theorem* ordinal.CNF_sorted
- \+ *theorem* ordinal.CNF_zero
- \+ *theorem* ordinal.add_absorp
- \+ *theorem* ordinal.add_absorp_iff
- \+/\- *theorem* ordinal.add_is_limit
- \+ *theorem* ordinal.add_is_normal
- \+/\- *theorem* ordinal.add_le_add_iff_left
- \+/\- *theorem* ordinal.add_le_add_left
- \+ *theorem* ordinal.add_left_cancel
- \+ *theorem* ordinal.add_lt_omega
- \+ *theorem* ordinal.add_omega
- \+ *theorem* ordinal.add_omega_power
- \- *def* ordinal.aleph'.order_iso
- \- *theorem* ordinal.aleph'.order_iso_coe
- \- *def* ordinal.aleph'
- \- *theorem* ordinal.aleph'_aleph_idx
- \- *theorem* ordinal.aleph'_le
- \- *theorem* ordinal.aleph'_lt
- \- *theorem* ordinal.aleph'_succ
- \- *def* ordinal.aleph
- \- *theorem* ordinal.aleph_idx_aleph'
- \- *def* ordinal.cof
- \+ *theorem* ordinal.cof_sup_le
- \+ *theorem* ordinal.cof_sup_le_lift
- \+ *theorem* ordinal.is_limit.nat_lt
- \+ *theorem* ordinal.is_limit.one_lt
- \+ *theorem* ordinal.is_limit.pos
- \+ *theorem* ordinal.is_normal.inj
- \+ *theorem* ordinal.is_normal.is_limit
- \+ *theorem* ordinal.is_normal.le_iff
- \+ *theorem* ordinal.is_normal.le_self
- \+ *theorem* ordinal.is_normal.le_set'
- \+ *theorem* ordinal.is_normal.le_set
- \+ *theorem* ordinal.is_normal.limit_lt
- \+ *theorem* ordinal.is_normal.lt_iff
- \+ *theorem* ordinal.is_normal.refl
- \+ *theorem* ordinal.is_normal.trans
- \+ *def* ordinal.is_normal
- \+/\- *theorem* ordinal.le_add_right
- \+ *theorem* ordinal.le_log
- \+ *theorem* ordinal.le_omin
- \+ *theorem* ordinal.le_power_self
- \+/\- *theorem* ordinal.le_sup
- \+ *def* ordinal.log
- \+ *theorem* ordinal.log_def
- \+ *theorem* ordinal.log_le_log
- \+ *theorem* ordinal.log_le_self
- \+ *theorem* ordinal.log_lt
- \+ *theorem* ordinal.log_not_one_lt
- \+ *theorem* ordinal.log_zero
- \+ *theorem* ordinal.lt_mul_of_limit
- \+ *theorem* ordinal.lt_power_of_limit
- \+ *theorem* ordinal.lt_power_succ_log
- \+ *theorem* ordinal.mul_add_one
- \+ *theorem* ordinal.mul_is_normal
- \+ *theorem* ordinal.mul_le_mul
- \+ *theorem* ordinal.mul_lt_omega
- \+ *theorem* ordinal.mul_ne_zero
- \+ *theorem* ordinal.mul_omega
- \+ *theorem* ordinal.mul_omega_power
- \+ *theorem* ordinal.mul_omega_power_power
- \+/\- *theorem* ordinal.mul_succ
- \+ *theorem* ordinal.nat_cast_div
- \+ *theorem* ordinal.nat_cast_eq_zero
- \+ *theorem* ordinal.nat_cast_mod
- \+ *theorem* ordinal.nat_cast_mul
- \+ *theorem* ordinal.nat_cast_ne_zero
- \+ *theorem* ordinal.nat_cast_power
- \+ *theorem* ordinal.nat_cast_sub
- \+ *theorem* ordinal.omega_ne_zero
- \+ *theorem* ordinal.omega_pos
- \+ *def* ordinal.omin
- \+ *theorem* ordinal.omin_le
- \+ *theorem* ordinal.omin_mem
- \+ *theorem* ordinal.one_CNF
- \+ *theorem* ordinal.one_le_iff_ne_zero
- \+ *theorem* ordinal.one_le_iff_pos
- \+ *theorem* ordinal.one_lt_omega
- \+ *theorem* ordinal.one_power
- \- *theorem* ordinal.ord_card_le
- \- *theorem* ordinal.pos_of_is_limit
- \+ *theorem* ordinal.power_add
- \+ *theorem* ordinal.power_is_limit
- \+ *theorem* ordinal.power_is_limit_left
- \+ *theorem* ordinal.power_is_normal
- \+/\- *theorem* ordinal.power_le_of_limit
- \+ *theorem* ordinal.power_le_power_iff_right
- \+ *theorem* ordinal.power_le_power_left
- \+ *theorem* ordinal.power_le_power_right
- \+/\- *theorem* ordinal.power_limit
- \+ *theorem* ordinal.power_log_le
- \+ *theorem* ordinal.power_lt_power_iff_right
- \+ *theorem* ordinal.power_lt_power_left_of_succ
- \+ *theorem* ordinal.power_mul
- \+ *theorem* ordinal.power_ne_zero
- \+ *theorem* ordinal.power_one
- \+ *theorem* ordinal.power_pos
- \+ *theorem* ordinal.power_right_inj
- \+/\- *theorem* ordinal.power_succ
- \+/\- *theorem* ordinal.power_zero
- \+ *theorem* ordinal.sub_eq_zero_iff_le
- \+ *theorem* ordinal.succ_eq_add_one
- \+/\- *theorem* ordinal.succ_le
- \+ *theorem* ordinal.succ_log_def
- \+/\- *theorem* ordinal.succ_ne_zero
- \+ *theorem* ordinal.succ_pos
- \+ *theorem* ordinal.zero_CNF
- \+ *theorem* ordinal.zero_lt_one
- \+ *theorem* ordinal.zero_power'
- \+ *theorem* ordinal.zero_power

Modified data/prod.lean


Modified data/quot.lean


Modified data/set/basic.lean
- \+ *theorem* set.compl_image_set_of
- \- *lemma* set.compl_image_set_of
- \+ *theorem* set.compl_subset_of_compl_subset
- \- *lemma* set.compl_subset_of_compl_subset
- \+ *theorem* set.diff_diff
- \- *lemma* set.diff_diff
- \+ *theorem* set.diff_empty
- \- *lemma* set.diff_empty
- \+ *theorem* set.diff_neq_empty
- \- *lemma* set.diff_neq_empty
- \+ *theorem* set.diff_right_antimono
- \- *lemma* set.diff_right_antimono
- \+ *theorem* set.diff_subset_diff
- \- *lemma* set.diff_subset_diff
- \+ *theorem* set.empty_prod
- \- *lemma* set.empty_prod
- \+ *theorem* set.forall_range_iff
- \- *lemma* set.forall_range_iff
- \+ *theorem* set.image_inter
- \- *lemma* set.image_inter
- \+ *theorem* set.image_inter_on
- \- *lemma* set.image_inter_on
- \+ *theorem* set.image_preimage_eq_inter_rng
- \- *lemma* set.image_preimage_eq_inter_rng
- \+ *theorem* set.image_singleton
- \- *lemma* set.image_singleton
- \+ *theorem* set.image_swap_prod
- \- *lemma* set.image_swap_prod
- \+ *theorem* set.insert_prod
- \- *lemma* set.insert_prod
- \+ *theorem* set.insert_subset
- \- *lemma* set.insert_subset
- \+ *theorem* set.insert_subset_insert
- \- *lemma* set.insert_subset_insert
- \+ *theorem* set.insert_union
- \- *lemma* set.insert_union
- \+/\- *theorem* set.inter_assoc
- \+/\- *theorem* set.inter_comm
- \+/\- *theorem* set.inter_left_comm
- \+ *theorem* set.inter_singleton_eq_empty
- \+ *theorem* set.mem_image_of_injective
- \- *lemma* set.mem_image_of_injective
- \+ *theorem* set.mem_of_mem_of_subset
- \- *lemma* set.mem_of_mem_of_subset
- \+ *theorem* set.mem_prod
- \- *lemma* set.mem_prod
- \+ *theorem* set.mem_prod_eq
- \- *lemma* set.mem_prod_eq
- \+ *theorem* set.mem_range
- \- *lemma* set.mem_range
- \+ *theorem* set.mem_range_self
- \- *lemma* set.mem_range_self
- \+ *theorem* set.ne_empty_iff_exists_mem
- \- *lemma* set.ne_empty_iff_exists_mem
- \+ *theorem* set.not_eq_empty_iff_exists
- \- *lemma* set.not_eq_empty_iff_exists
- \+ *theorem* set.not_not_mem
- \- *lemma* set.not_not_mem
- \+ *theorem* set.not_subset
- \- *lemma* set.not_subset
- \+ *theorem* set.prod_empty
- \- *lemma* set.prod_empty
- \+ *theorem* set.prod_image_image_eq
- \- *lemma* set.prod_image_image_eq
- \+ *theorem* set.prod_insert
- \- *lemma* set.prod_insert
- \+ *theorem* set.prod_inter_prod
- \- *lemma* set.prod_inter_prod
- \+ *theorem* set.prod_mk_mem_set_prod_eq
- \- *lemma* set.prod_mk_mem_set_prod_eq
- \+ *theorem* set.prod_mono
- \- *lemma* set.prod_mono
- \+ *theorem* set.prod_neq_empty_iff
- \- *lemma* set.prod_neq_empty_iff
- \+ *theorem* set.prod_singleton_singleton
- \- *lemma* set.prod_singleton_singleton
- \+ *theorem* set.quot_mk_image_univ_eq
- \- *lemma* set.quot_mk_image_univ_eq
- \+ *theorem* set.range_compose
- \- *lemma* set.range_compose
- \+ *theorem* set.range_eq_image
- \- *lemma* set.range_eq_image
- \+ *theorem* set.range_id
- \- *lemma* set.range_id
- \+ *theorem* set.range_iff_surjective
- \- *lemma* set.range_iff_surjective
- \+ *theorem* set.set_compr_eq_eq_singleton
- \- *lemma* set.set_compr_eq_eq_singleton
- \+ *theorem* set.set_of_mem_eq
- \- *lemma* set.set_of_mem_eq
- \+ *theorem* set.singleton_inter_eq_empty
- \+/\- *theorem* set.union_assoc
- \+/\- *theorem* set.union_comm
- \+ *theorem* set.union_insert
- \- *lemma* set.union_insert
- \- *theorem* set.union_insert_eq
- \+/\- *theorem* set.union_left_comm
- \+ *theorem* set.union_singleton
- \+ *theorem* set.univ_eq_true_false
- \- *lemma* set.univ_eq_true_false
- \+ *theorem* set.univ_prod_univ
- \- *lemma* set.univ_prod_univ

Modified data/set/lattice.lean


Modified logic/embedding.lean
- \+ *def* set.embedding_of_subset

Modified order/basic.lean
- \+ *def* decidable_linear_order_of_STO'
- \+ *def* linear_order_of_STO'
- \+ *def* partial_order_of_SO



## [2017-12-23 10:06:18-05:00](https://github.com/leanprover-community/mathlib/commit/0abe086)
feat(data/ordinal): mul, div, mod, dvd, sub, power
#### Estimated changes
Modified algebra/linear_algebra/basic.lean


Modified data/cardinal.lean
- \+ *theorem* cardinal.le_zero
- \+ *theorem* cardinal.omega_ne_zero

Modified data/equiv.lean
- \+ *theorem* equiv.prod_assoc_apply
- \+ *theorem* equiv.prod_sum_distrib_apply_left
- \+ *theorem* equiv.prod_sum_distrib_apply_right
- \+ *theorem* equiv.prod_unit_apply
- \+ *theorem* equiv.sum_prod_distrib_apply_left
- \+ *theorem* equiv.sum_prod_distrib_apply_right
- \+ *theorem* equiv.unit_prod_apply

Modified data/ordinal.lean
- \+ *theorem* cardinal.add_one_of_omega_le
- \+ *theorem* cardinal.ord_is_limit
- \+ *theorem* ordinal.add_is_limit
- \+ *theorem* ordinal.add_le_of_limit
- \+ *theorem* ordinal.add_sub_cancel_of_le
- \+ *theorem* ordinal.card_mul
- \+ *theorem* ordinal.card_succ
- \+ *theorem* ordinal.div_add_mod
- \+ *def* ordinal.div_def
- \+ *theorem* ordinal.div_eq_zero_of_lt
- \+ *theorem* ordinal.div_le
- \+ *theorem* ordinal.div_le_of_le_mul
- \+ *theorem* ordinal.div_lt
- \+ *theorem* ordinal.div_mul_cancel
- \+ *theorem* ordinal.div_one
- \+ *theorem* ordinal.div_self
- \+ *theorem* ordinal.div_zero
- \+ *theorem* ordinal.dvd_def
- \+ *theorem* ordinal.dvd_mul
- \+ *theorem* ordinal.dvd_zero
- \+ *theorem* ordinal.le_div
- \+ *theorem* ordinal.le_of_mul_le_mul_left
- \+ *theorem* ordinal.le_succ_of_is_limit
- \+ *theorem* ordinal.le_zero
- \+ *theorem* ordinal.limit_le
- \+ *theorem* ordinal.limit_rec_on_limit
- \+ *theorem* ordinal.limit_rec_on_succ
- \+ *theorem* ordinal.limit_rec_on_zero
- \+ *theorem* ordinal.lt_div
- \+ *theorem* ordinal.lt_mul_div_add
- \+ *theorem* ordinal.lt_mul_succ_div
- \+ *theorem* ordinal.lt_succ
- \+ *theorem* ordinal.mod_def
- \+ *theorem* ordinal.mod_eq_of_lt
- \+ *theorem* ordinal.mod_lt
- \+ *theorem* ordinal.mod_one
- \+ *theorem* ordinal.mod_self
- \+ *theorem* ordinal.mod_zero
- \+ *theorem* ordinal.mul_add
- \+ *theorem* ordinal.mul_add_div
- \+ *theorem* ordinal.mul_assoc
- \+ *theorem* ordinal.mul_div_cancel
- \+ *theorem* ordinal.mul_div_le
- \+ *theorem* ordinal.mul_is_limit
- \+ *theorem* ordinal.mul_le_mul_iff_left
- \+ *theorem* ordinal.mul_le_mul_left
- \+ *theorem* ordinal.mul_le_mul_right
- \+ *theorem* ordinal.mul_le_of_limit
- \+ *theorem* ordinal.mul_left_inj
- \+ *theorem* ordinal.mul_lt_mul_iff_left
- \+ *theorem* ordinal.mul_lt_mul_of_pos_left
- \+ *theorem* ordinal.mul_lt_of_lt_div
- \+ *theorem* ordinal.mul_one
- \+ *theorem* ordinal.mul_pos
- \+ *theorem* ordinal.mul_succ
- \+ *theorem* ordinal.mul_zero
- \+ *theorem* ordinal.not_succ_is_limit
- \+ *theorem* ordinal.not_succ_of_is_limit
- \+ *theorem* ordinal.one_add_of_omega_le
- \+ *theorem* ordinal.one_add_omega
- \+ *theorem* ordinal.one_dvd
- \+ *theorem* ordinal.one_eq_lift_type_unit
- \+ *theorem* ordinal.one_eq_type_unit
- \+ *theorem* ordinal.one_mul
- \+ *theorem* ordinal.pos_iff_ne_zero
- \+ *def* ordinal.power
- \+ *theorem* ordinal.power_le_of_limit
- \+ *theorem* ordinal.power_limit
- \+ *theorem* ordinal.power_succ
- \+ *theorem* ordinal.power_zero
- \+ *theorem* ordinal.sub_le_self
- \+ *theorem* ordinal.sub_self
- \+ *theorem* ordinal.sub_zero
- \+ *theorem* ordinal.succ_lt_of_is_limit
- \+ *theorem* ordinal.type_add
- \+ *theorem* ordinal.type_eq_zero_iff_empty
- \+ *theorem* ordinal.type_mul
- \+ *theorem* ordinal.typein_apply
- \+ *theorem* ordinal.zero_div
- \+ *theorem* ordinal.zero_dvd
- \+ *theorem* ordinal.zero_eq_lift_type_empty
- \+ *theorem* ordinal.zero_eq_type_empty
- \+ *theorem* ordinal.zero_mod
- \+ *theorem* ordinal.zero_mul
- \+ *theorem* ordinal.zero_sub

Modified data/prod.lean
- \+ *theorem* prod.lex_def

Modified data/set/countable.lean


Modified data/set/lattice.lean


Modified data/sigma/basic.lean
- \+ *theorem* subtype.mk_eq_mk

Modified data/sum.lean
- \+ *theorem* sum.inl_ne_inr
- \+ *theorem* sum.inr_ne_inl

Modified order/basic.lean
- \- *def* empty_relation.is_well_order

Modified order/order_iso.lean
- \+ *theorem* order_embedding.nat_gt
- \+ *theorem* subrel.order_embedding_apply
- \+ *theorem* subrel_val



## [2017-12-21 06:51:34-05:00](https://github.com/leanprover-community/mathlib/commit/5f4d890)
feat(data/ordinal): omega is least limit ordinal
#### Estimated changes
Modified algebra/order.lean
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt

Modified data/cardinal.lean
- \+ *theorem* cardinal.le_lift_iff
- \+ *theorem* cardinal.lift_omega
- \+ *theorem* cardinal.lt_lift_iff
- \+ *theorem* cardinal.lt_omega_iff_finite
- \+ *theorem* cardinal.lt_omega_iff_fintype

Modified data/ordinal.lean
- \+/\- *theorem* cardinal.card_ord
- \+ *theorem* cardinal.lift_ord
- \+/\- *theorem* cardinal.ord_le_ord
- \+/\- *theorem* cardinal.ord_lt_ord
- \+/\- *theorem* cardinal.ord_nat
- \+ *theorem* cardinal.ord_omega
- \+ *theorem* ordinal.card_eq_nat
- \+ *theorem* ordinal.card_le_nat
- \+ *theorem* ordinal.card_lt_nat
- \+ *theorem* ordinal.fintype_card
- \+ *theorem* ordinal.le_lift_iff
- \+ *theorem* ordinal.lift_down'
- \+/\- *theorem* ordinal.lift_down
- \+ *theorem* ordinal.lift_nat_cast
- \+ *theorem* ordinal.lift_type_fin
- \+ *theorem* ordinal.lt_lift_iff
- \+ *theorem* ordinal.lt_omega
- \+ *theorem* ordinal.nat_cast_inj
- \+ *theorem* ordinal.nat_cast_le
- \+ *theorem* ordinal.nat_cast_lt
- \+ *theorem* ordinal.nat_le_card
- \+ *theorem* ordinal.nat_lt_card
- \+ *theorem* ordinal.nat_lt_limit
- \+ *theorem* ordinal.nat_lt_omega
- \+ *theorem* ordinal.omega_is_limit
- \+ *theorem* ordinal.omega_le
- \+ *theorem* ordinal.omega_le_of_is_limit
- \+ *theorem* ordinal.type_fin

Modified logic/basic.lean
- \+ *theorem* false_ne_true
- \- *theorem* false_neq_true
- \+/\- *theorem* iff_of_eq

Modified logic/schroeder_bernstein.lean
- \+/\- *theorem* function.embedding.injective_min

Modified order/order_iso.lean
- \+ *def* fin.val.order_embedding
- \+ *def* fin_fin.order_embedding
- \+ *def* order_iso.to_order_embedding



## [2017-12-20 23:25:17-05:00](https://github.com/leanprover-community/mathlib/commit/49a63b7)
refactor(data/ordinal): rearrange files, more cofinality
#### Estimated changes
Modified algebra/linear_algebra/basic.lean


Modified analysis/real.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/uniform_space.lean


Modified data/cardinal.lean
- \- *theorem* cardinal.embedding.antisymm
- \- *def* cardinal.embedding.arrow_congr_left
- \- *def* cardinal.embedding.arrow_congr_right
- \- *theorem* cardinal.embedding.coe_fn_mk
- \- *theorem* cardinal.embedding.inj'
- \- *theorem* cardinal.embedding.injective_min
- \- *def* cardinal.embedding.prod_congr
- \- *theorem* cardinal.embedding.refl_apply
- \- *theorem* cardinal.embedding.schroeder_bernstein
- \- *def* cardinal.embedding.sum_congr
- \- *theorem* cardinal.embedding.sum_congr_apply_inl
- \- *theorem* cardinal.embedding.sum_congr_apply_inr
- \- *theorem* cardinal.embedding.to_fun_eq_coe
- \- *theorem* cardinal.embedding.total
- \- *theorem* cardinal.embedding.trans_apply
- \- *structure* cardinal.embedding
- \+ *theorem* cardinal.lift_down
- \+ *theorem* cardinal.lt_omega
- \- *theorem* equiv.to_embedding_coe_fn

Modified data/ordinal.lean
- \- *def* empty_relation.is_well_order
- \- *def* is_irrefl.swap
- \- *def* is_irrefl_of_is_asymm
- \- *def* is_strict_order.swap
- \- *def* is_strict_total_order'.swap
- \- *def* is_strict_weak_order_of_is_order_connected
- \- *def* is_trans.swap
- \- *def* is_trichotomous.swap
- \- *def* order.preimage
- \- *def* order_embedding.cod_restrict
- \- *theorem* order_embedding.cod_restrict_apply
- \- *theorem* order_embedding.coe_fn_mk
- \- *theorem* order_embedding.coe_fn_to_embedding
- \- *theorem* order_embedding.eq_of_to_fun_eq
- \- *theorem* order_embedding.eq_preimage
- \- *theorem* order_embedding.nat_lt
- \- *def* order_embedding.of_monotone
- \- *theorem* order_embedding.of_monotone_coe
- \- *theorem* order_embedding.ord'
- \- *def* order_embedding.preimage
- \- *theorem* order_embedding.refl_apply
- \- *def* order_embedding.rsymm
- \- *theorem* order_embedding.trans_apply
- \- *theorem* order_embedding.well_founded_iff_no_descending_seq
- \- *structure* order_embedding
- \- *theorem* order_iso.apply_inverse_apply
- \- *theorem* order_iso.coe_coe_fn
- \- *theorem* order_iso.coe_fn_mk
- \- *theorem* order_iso.coe_fn_symm_mk
- \- *theorem* order_iso.coe_fn_to_equiv
- \- *theorem* order_iso.eq_of_to_fun_eq
- \- *theorem* order_iso.inverse_apply_apply
- \- *def* order_iso.of_surjective
- \- *theorem* order_iso.of_surjective_coe
- \- *theorem* order_iso.ord'
- \- *def* order_iso.preimage
- \- *theorem* order_iso.prod_lex_congr
- \- *theorem* order_iso.refl_apply
- \- *theorem* order_iso.sum_lex_congr
- \- *theorem* order_iso.trans_apply
- \- *structure* order_iso
- \+/\- *theorem* ordinal.card_omega
- \+ *theorem* ordinal.cof_add
- \+ *theorem* ordinal.cof_cof
- \+ *theorem* ordinal.cof_eq
- \+/\- *theorem* ordinal.cof_eq_one_iff_is_succ
- \- *theorem* ordinal.exists_of_cof
- \+ *theorem* ordinal.lift_card
- \+ *theorem* ordinal.lift_is_limit
- \+ *theorem* ordinal.lift_is_succ
- \+ *theorem* ordinal.lift_pred
- \+ *theorem* ordinal.lift_succ
- \+ *theorem* ordinal.ord_cof_eq
- \+ *theorem* ordinal.type_ne_zero_iff_nonempty
- \- *def* set_coe_embedding
- \- *def* subrel
- \- *theorem* well_founded.has_min
- \- *def* well_founded.min
- \- *theorem* well_founded.min_mem
- \- *theorem* well_founded.not_lt_min

Modified data/set/finite.lean
- \+/\- *theorem* set.finite_image

Modified data/sigma/basic.lean
- \+ *theorem* psigma.mk.inj_iff
- \- *lemma* psigma.mk.inj_iff
- \+ *theorem* subtype.coe_eta
- \+ *theorem* subtype.coe_mk

Modified logic/basic.lean
- \+ *theorem* Exists.fst
- \+ *theorem* Exists.snd

Added logic/embedding.lean
- \+ *theorem* equiv.to_embedding_coe_fn
- \+ *def* function.embedding.arrow_congr_left
- \+ *def* function.embedding.cod_restrict
- \+ *theorem* function.embedding.cod_restrict_apply
- \+ *theorem* function.embedding.coe_fn_mk
- \+ *theorem* function.embedding.inj'
- \+ *def* function.embedding.prod_congr
- \+ *theorem* function.embedding.refl_apply
- \+ *def* function.embedding.sum_congr
- \+ *theorem* function.embedding.sum_congr_apply_inl
- \+ *theorem* function.embedding.sum_congr_apply_inr
- \+ *theorem* function.embedding.to_fun_eq_coe
- \+ *theorem* function.embedding.trans_apply
- \+ *structure* function.embedding

Modified logic/function.lean
- \+/\- *def* function.injective.decidable_eq
- \+/\- *theorem* function.injective.eq_iff
- \+/\- *theorem* function.injective_of_partial_inv
- \+/\- *theorem* function.injective_of_partial_inv_right
- \+/\- *def* function.is_partial_inv
- \+/\- *theorem* function.partial_inv_of_injective
- \+/\- *lemma* function.surj_inv_eq

Added logic/schroeder_bernstein.lean
- \+ *theorem* function.embedding.antisymm
- \+ *theorem* function.embedding.injective_min
- \+ *theorem* function.embedding.schroeder_bernstein
- \+ *theorem* function.embedding.total

Modified order/basic.lean
- \+ *def* empty_relation.is_well_order
- \+ *def* is_irrefl.swap
- \+ *def* is_irrefl_of_is_asymm
- \+ *theorem* is_order_connected.neg_trans
- \+ *def* is_strict_order.swap
- \+ *def* is_strict_total_order'.swap
- \+ *def* is_strict_weak_order_of_is_order_connected
- \+ *def* is_trans.swap
- \+ *def* is_trichotomous.swap
- \+ *theorem* well_founded.has_min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min

Modified order/filter.lean


Added order/order_iso.lean
- \+ *def* order.preimage
- \+ *def* order_embedding.cod_restrict
- \+ *theorem* order_embedding.cod_restrict_apply
- \+ *theorem* order_embedding.coe_fn_mk
- \+ *theorem* order_embedding.coe_fn_to_embedding
- \+ *theorem* order_embedding.eq_of_to_fun_eq
- \+ *theorem* order_embedding.eq_preimage
- \+ *theorem* order_embedding.nat_lt
- \+ *def* order_embedding.of_monotone
- \+ *theorem* order_embedding.of_monotone_coe
- \+ *theorem* order_embedding.ord'
- \+ *def* order_embedding.preimage
- \+ *theorem* order_embedding.refl_apply
- \+ *def* order_embedding.rsymm
- \+ *theorem* order_embedding.trans_apply
- \+ *theorem* order_embedding.well_founded_iff_no_descending_seq
- \+ *structure* order_embedding
- \+ *theorem* order_iso.apply_inverse_apply
- \+ *theorem* order_iso.coe_coe_fn
- \+ *theorem* order_iso.coe_fn_mk
- \+ *theorem* order_iso.coe_fn_symm_mk
- \+ *theorem* order_iso.coe_fn_to_equiv
- \+ *theorem* order_iso.eq_of_to_fun_eq
- \+ *theorem* order_iso.inverse_apply_apply
- \+ *theorem* order_iso.of_surjective_coe
- \+ *theorem* order_iso.ord'
- \+ *def* order_iso.preimage
- \+ *theorem* order_iso.prod_lex_congr
- \+ *theorem* order_iso.refl_apply
- \+ *theorem* order_iso.sum_lex_congr
- \+ *theorem* order_iso.trans_apply
- \+ *structure* order_iso
- \+ *def* set_coe_embedding
- \+ *def* subrel



## [2017-12-19 04:59:43-05:00](https://github.com/leanprover-community/mathlib/commit/7726a92)
feat(data/ordinal): sup, cofinality, subtraction
#### Estimated changes
Modified algebra/order.lean
- \+ *lemma* le_of_forall_le
- \+ *lemma* le_of_forall_lt

Modified algebra/ordered_ring.lean
- \+ *lemma* zero_le_mul

Modified analysis/ennreal.lean
- \- *lemma* zero_le_mul

Modified analysis/metric_space.lean


Modified data/cardinal.lean
- \+/\- *theorem* cardinal.le_min
- \+ *theorem* cardinal.le_one_iff_subsingleton
- \+/\- *theorem* cardinal.lift_min
- \+/\- *def* cardinal.min
- \+/\- *theorem* cardinal.min_eq
- \+/\- *theorem* cardinal.min_le
- \+ *theorem* cardinal.nat_lt_omega
- \- *theorem* cardinal.nat_lt_ω
- \+/\- *theorem* cardinal.ne_zero_iff_nonempty
- \+ *def* cardinal.omega
- \+/\- *theorem* cardinal.prop_eq_two
- \+ *theorem* cardinal.succ_zero
- \+ *theorem* cardinal.zero_lt_one
- \- *def* cardinal.ω

Modified data/fintype.lean
- \+ *theorem* fintype.card_of_subtype
- \+ *theorem* fintype.subtype_card

Modified data/ordinal.lean
- \+ *def* cardinal.ord_eq_min
- \- *theorem* cardinal.ord_eq_min
- \+ *theorem* cardinal.ord_nat
- \+ *theorem* order_iso.cof.aux
- \+ *theorem* order_iso.cof
- \+ *theorem* ordinal.add_le_add_right
- \+ *theorem* ordinal.add_lt_add_iff_left
- \+ *theorem* ordinal.add_sub_cancel
- \+ *theorem* ordinal.aleph'_succ
- \+/\- *def* ordinal.aleph
- \+ *def* ordinal.bsup
- \+ *theorem* ordinal.bsup_le
- \+ *theorem* ordinal.card_eq_zero
- \+ *theorem* ordinal.card_omega
- \+ *def* ordinal.cof
- \+ *theorem* ordinal.cof_eq_one_iff_is_succ
- \+ *theorem* ordinal.cof_eq_zero
- \+ *theorem* ordinal.cof_le_card
- \+ *theorem* ordinal.cof_succ
- \+ *theorem* ordinal.cof_type_le
- \+ *theorem* ordinal.cof_zero
- \+ *theorem* ordinal.exists_of_cof
- \+ *def* ordinal.is_limit
- \+/\- *theorem* ordinal.le_add_left
- \+ *theorem* ordinal.le_add_sub
- \+ *theorem* ordinal.le_bsup
- \+ *theorem* ordinal.le_cof_type
- \+/\- *theorem* ordinal.le_min
- \+ *theorem* ordinal.le_sup
- \+/\- *theorem* ordinal.le_total
- \+/\- *theorem* ordinal.lift_min
- \+ *theorem* ordinal.lift_omega
- \- *theorem* ordinal.lift_ω
- \+ *def* ordinal.limit_rec_on
- \+ *theorem* ordinal.lt_cof_type
- \+ *theorem* ordinal.lt_of_add_lt_add_right
- \+ *theorem* ordinal.lt_pred
- \+ *theorem* ordinal.lt_sub
- \+/\- *def* ordinal.min
- \+/\- *theorem* ordinal.min_eq
- \+/\- *theorem* ordinal.min_le
- \+ *def* ordinal.omega
- \+ *theorem* ordinal.pos_of_is_limit
- \+ *def* ordinal.pred
- \+ *theorem* ordinal.pred_eq_iff_not_succ
- \+ *theorem* ordinal.pred_le
- \+ *theorem* ordinal.pred_le_self
- \+ *theorem* ordinal.pred_lt_iff_is_succ
- \+ *theorem* ordinal.pred_succ
- \+ *def* ordinal.sub
- \+ *theorem* ordinal.sub_le
- \+ *theorem* ordinal.succ_inj
- \+ *theorem* ordinal.succ_le
- \+ *theorem* ordinal.succ_le_succ
- \+ *theorem* ordinal.succ_lt_of_not_succ
- \+ *theorem* ordinal.succ_lt_succ
- \+ *theorem* ordinal.succ_nat_cast
- \+ *theorem* ordinal.succ_ne_zero
- \+ *theorem* ordinal.succ_pred_iff_is_succ
- \+ *theorem* ordinal.succ_zero
- \+ *def* ordinal.sup
- \+ *theorem* ordinal.sup_le
- \+ *theorem* ordinal.zero_or_succ_or_limit
- \- *def* ordinal.ω

Modified data/set/finite.lean
- \+ *theorem* set.card_fintype_insert'
- \+ *theorem* set.card_fintype_of_finset'
- \+ *theorem* set.card_fintype_of_finset
- \+ *theorem* set.card_insert
- \+ *theorem* set.card_singleton
- \+ *theorem* set.empty_card

Modified order/basic.lean
- \- *lemma* eq_of_le_of_forall_ge
- \+ *lemma* eq_of_le_of_forall_ge_of_dense
- \- *lemma* eq_of_le_of_forall_le
- \+ *lemma* eq_of_le_of_forall_le_of_dense
- \- *lemma* le_of_forall_ge
- \+ *lemma* le_of_forall_ge_of_dense
- \- *lemma* le_of_forall_le
- \+ *lemma* le_of_forall_le_of_dense



## [2017-12-18 08:38:41-05:00](https://github.com/leanprover-community/mathlib/commit/f6bbca7)
feat(data/ordinal): universe lifts, alephs
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *theorem* finset.card_sigma

Modified algebra/group_power.lean
- \+ *theorem* nat.smul_eq_mul

Modified algebra/module.lean


Modified data/cardinal.lean
- \+ *theorem* cardinal.add_one_le_succ
- \+ *theorem* cardinal.fintype_card
- \+ *theorem* cardinal.le_mk_iff_exists_set
- \+ *def* cardinal.lift
- \+ *theorem* cardinal.lift_add
- \+ *theorem* cardinal.lift_id
- \+ *theorem* cardinal.lift_inj
- \+ *theorem* cardinal.lift_le
- \+ *theorem* cardinal.lift_lift
- \+ *theorem* cardinal.lift_lt
- \+ *theorem* cardinal.lift_min
- \+ *theorem* cardinal.lift_mk
- \+ *theorem* cardinal.lift_mk_eq
- \+ *theorem* cardinal.lift_mk_fin
- \+ *theorem* cardinal.lift_mk_le
- \+ *theorem* cardinal.lift_mul
- \+ *theorem* cardinal.lift_nat_cast
- \+ *theorem* cardinal.lift_one
- \+ *theorem* cardinal.lift_power
- \+ *theorem* cardinal.lift_umax
- \+ *theorem* cardinal.lift_zero
- \+ *theorem* cardinal.lt_succ_self
- \+ *theorem* cardinal.mk_def
- \+ *theorem* cardinal.mk_fin
- \+ *theorem* cardinal.nat_cast_inj
- \+ *theorem* cardinal.nat_cast_le
- \+ *theorem* cardinal.nat_cast_lt
- \+ *theorem* cardinal.nat_lt_ω
- \+ *theorem* cardinal.nat_succ
- \+ *def* cardinal.succ
- \+ *theorem* cardinal.succ_le
- \+/\- *def* cardinal.ω

Modified data/finset.lean
- \+/\- *lemma* finset.bind_mono
- \+ *theorem* finset.card_image_of_inj_on
- \+ *theorem* finset.card_image_of_injective
- \+ *theorem* finset.card_product

Modified data/fintype.lean
- \+ *theorem* finset.eq_univ_iff_forall
- \+/\- *theorem* finset.mem_univ
- \+/\- *theorem* finset.mem_univ_val
- \+ *theorem* fintype.card_bool
- \+ *theorem* fintype.card_congr
- \+ *theorem* fintype.card_empty
- \+ *theorem* fintype.card_eq
- \+ *theorem* fintype.card_fin
- \+ *theorem* fintype.card_prod
- \+ *theorem* fintype.card_sigma
- \+ *theorem* fintype.card_sum
- \+ *theorem* fintype.card_ulift
- \+ *theorem* fintype.card_unit
- \+/\- *def* fintype.of_equiv
- \+ *theorem* fintype.of_equiv_card
- \+ *theorem* fintype.univ_bool
- \+ *theorem* fintype.univ_empty
- \+ *theorem* fintype.univ_unit

Modified data/list/basic.lean
- \+ *theorem* list.length_pmap
- \+ *theorem* list.nth_le_index_of

Modified data/multiset.lean
- \+ *theorem* multiset.card_bind
- \+ *theorem* multiset.card_join
- \+ *theorem* multiset.card_map
- \+ *theorem* multiset.card_pmap
- \+ *theorem* multiset.card_product
- \+ *theorem* multiset.card_sigma

Modified data/ordinal.lean
- \+ *theorem* cardinal.aleph_idx.init
- \+ *def* cardinal.aleph_idx.initial_seg
- \+ *theorem* cardinal.aleph_idx.initial_seg_coe
- \+ *def* cardinal.aleph_idx.order_iso
- \+ *theorem* cardinal.aleph_idx.order_iso_coe
- \+ *def* cardinal.aleph_idx
- \+ *theorem* cardinal.aleph_idx_le
- \+ *theorem* cardinal.aleph_idx_lt
- \+ *theorem* cardinal.card_ord
- \+ *theorem* cardinal.lt_ord
- \+ *def* cardinal.ord.order_embedding
- \+ *theorem* cardinal.ord.order_embedding_coe
- \+/\- *theorem* cardinal.ord_eq_min
- \+/\- *theorem* cardinal.ord_le
- \+/\- *theorem* cardinal.ord_le_ord
- \+ *theorem* cardinal.ord_le_type
- \+ *theorem* cardinal.ord_lt_ord
- \+ *theorem* cardinal.ord_zero
- \+ *def* order.cof
- \- *theorem* order_iso.of_surjective_apply
- \+ *theorem* order_iso.of_surjective_coe
- \+ *theorem* order_iso.prod_lex_congr
- \+ *theorem* order_iso.sum_lex_congr
- \+ *def* ordinal.aleph'.order_iso
- \+ *theorem* ordinal.aleph'.order_iso_coe
- \+ *def* ordinal.aleph'
- \+ *theorem* ordinal.aleph'_aleph_idx
- \+ *theorem* ordinal.aleph'_le
- \+ *theorem* ordinal.aleph'_lt
- \+ *def* ordinal.aleph
- \+ *theorem* ordinal.aleph_idx_aleph'
- \+ *theorem* ordinal.card_nat
- \+ *theorem* ordinal.card_type
- \+ *def* ordinal.lift.initial_seg
- \+ *theorem* ordinal.lift.initial_seg_coe
- \+ *def* ordinal.lift.principal_seg
- \+ *theorem* ordinal.lift.principal_seg_coe
- \+ *theorem* ordinal.lift.principal_seg_top'
- \+ *theorem* ordinal.lift.principal_seg_top
- \+ *def* ordinal.lift
- \+ *theorem* ordinal.lift_add
- \+ *theorem* ordinal.lift_down
- \+ *theorem* ordinal.lift_id
- \+ *theorem* ordinal.lift_inj
- \+ *theorem* ordinal.lift_le
- \+ *theorem* ordinal.lift_lift
- \+ *theorem* ordinal.lift_lt
- \+ *theorem* ordinal.lift_min
- \+ *theorem* ordinal.lift_mul
- \+ *theorem* ordinal.lift_one
- \+ *theorem* ordinal.lift_type_eq
- \+ *theorem* ordinal.lift_type_le
- \+ *theorem* ordinal.lift_type_lt
- \+ *theorem* ordinal.lift_umax
- \+ *theorem* ordinal.lift_zero
- \+ *theorem* ordinal.lift_ω
- \+ *theorem* ordinal.lt_succ_self
- \+ *theorem* ordinal.ord_card_le
- \+ *theorem* ordinal.type_le'
- \- *theorem* ordinal.type_le_of_order_embedding
- \+ *def* ordinal.typein.principal_seg
- \+ *theorem* ordinal.typein.principal_seg_coe
- \+ *def* ordinal.ω



## [2017-12-17 14:11:42-05:00](https://github.com/leanprover-community/mathlib/commit/52330fa)
fix(data/ordinal): update to lean
#### Estimated changes
Modified data/ordinal.lean




## [2017-12-17 04:47:45-05:00](https://github.com/leanprover-community/mathlib/commit/dba8d0e)
fix(data/ordinal): fix unsound proof
here's hoping lean will notice that the last proof is not correct
#### Estimated changes
Modified data/ordinal.lean




## [2017-12-17 02:45:25-05:00](https://github.com/leanprover-community/mathlib/commit/b19c222)
feat(data/ordinal): ordinal collapse, ordinals ordering,
#### Estimated changes
Modified algebra/group_power.lean


Modified data/cardinal.lean
- \+ *theorem* cardinal.embedding.sum_congr_apply_inl
- \+ *theorem* cardinal.embedding.sum_congr_apply_inr
- \+ *def* cardinal.mk

Modified data/equiv.lean
- \+ *def* equiv.empty_prod
- \+ *def* equiv.empty_sum
- \+ *theorem* equiv.prod_congr_apply
- \+ *def* equiv.prod_empty
- \- *def* equiv.prod_empty_left
- \- *def* equiv.prod_empty_right
- \+ *def* equiv.prod_unit
- \- *def* equiv.prod_unit_left
- \- *def* equiv.prod_unit_right
- \+ *theorem* equiv.sum_assoc_apply_in1
- \+ *theorem* equiv.sum_assoc_apply_in2
- \+ *theorem* equiv.sum_assoc_apply_in3
- \+ *theorem* equiv.sum_congr_apply_inl
- \+ *theorem* equiv.sum_congr_apply_inr
- \+ *def* equiv.sum_empty
- \- *def* equiv.sum_empty_left
- \- *def* equiv.sum_empty_right
- \+ *def* equiv.unit_prod

Modified data/ordinal.lean
- \+ *def* cardinal.ord
- \+ *theorem* cardinal.ord_eq
- \+ *theorem* cardinal.ord_eq_min
- \+ *theorem* cardinal.ord_le
- \+ *theorem* cardinal.ord_le_ord
- \+ *def* initial_seg.le_add
- \+ *theorem* initial_seg.le_add_apply
- \+ *def* order_embedding.collapse
- \+ *theorem* order_embedding.collapse_F.lt
- \+ *theorem* order_embedding.collapse_F.not_lt
- \+ *def* order_embedding.collapse_F
- \+ *theorem* order_embedding.collapse_apply
- \+ *def* order_embedding.of_monotone
- \- *theorem* order_embedding.of_monotone
- \+ *theorem* order_embedding.of_monotone_coe
- \+ *def* order_embedding.preimage
- \+ *theorem* ordinal.add_le_add_iff_left
- \+ *theorem* ordinal.add_le_add_left
- \+ *theorem* ordinal.add_succ
- \+ *theorem* ordinal.card_add
- \+ *theorem* ordinal.card_le_card
- \+ *theorem* ordinal.card_one
- \+ *theorem* ordinal.card_zero
- \+ *theorem* ordinal.le_add_left
- \+ *theorem* ordinal.le_add_right
- \+ *theorem* ordinal.le_min
- \+ *theorem* ordinal.le_total
- \+ *def* ordinal.min
- \+ *theorem* ordinal.min_eq
- \+ *theorem* ordinal.min_le
- \+ *def* ordinal.succ
- \+ *theorem* ordinal.type_le_of_order_embedding
- \+ *theorem* ordinal.zero_le
- \- *def* prod.lex.is_well_order
- \- *def* sum.lex.is_well_order
- \+ *theorem* well_founded.has_min
- \+ *def* well_founded.min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min

Modified data/set/basic.lean
- \+/\- *lemma* set.mem_range
- \+ *lemma* set.mem_range_self

Modified logic/basic.lean
- \+ *def* empty.elim
- \- *theorem* empty.elim

Modified order/complete_lattice.lean


Modified tactic/alias.lean


Modified tactic/interactive.lean




## [2017-12-15 22:45:11-05:00](https://github.com/leanprover-community/mathlib/commit/95507bf)
chore(algebra/module): update to lean
inout => out_param
#### Estimated changes
Modified algebra/module.lean




## [2017-12-15 13:40:09+01:00](https://github.com/leanprover-community/mathlib/commit/01f1d23)
refactor(style.md): copy naming conventions from the library_dev repository.
#### Estimated changes
Modified style.md




## [2017-12-14 21:29:14+01:00](https://github.com/leanprover-community/mathlib/commit/7948318)
feat(logic/basic): add rewrite rules for nonempty
#### Estimated changes
Modified logic/basic.lean
- \+ *lemma* classical.nonempty_pi
- \+ *lemma* nonempty.exists
- \+ *lemma* nonempty.forall
- \+ *lemma* nonempty_Prop
- \+ *lemma* nonempty_empty
- \+ *lemma* nonempty_plift
- \+ *lemma* nonempty_pprod
- \+ *lemma* nonempty_prod
- \+ *lemma* nonempty_psigma
- \+ *lemma* nonempty_psum
- \+ *lemma* nonempty_sigma
- \+ *lemma* nonempty_subtype
- \+ *lemma* nonempty_sum
- \+ *lemma* nonempty_ulift



## [2017-12-14 12:50:11+01:00](https://github.com/leanprover-community/mathlib/commit/d27f7ac)
chore(style.md): rename and some cleanup
#### Estimated changes
Renamed library_style.md to style.md




## [2017-12-14 12:42:51+01:00](https://github.com/leanprover-community/mathlib/commit/f8476fd)
feat(library_style): resurrecting Jeremy's library_style.org as md file
#### Estimated changes
Added library_style.md




## [2017-12-14 11:39:08+01:00](https://github.com/leanprover-community/mathlib/commit/0f50ba7)
feat(.travis.yml): export and run leanchecker
This should detect multiple definitions with the same name as in [#27](https://github.com/leanprover-community/mathlib/pull/27).
#### Estimated changes
Modified .travis.yml




## [2017-12-14 11:13:01+01:00](https://github.com/leanprover-community/mathlib/commit/86e494d)
fix(data/encodable): make decidable_eq_of_encodable priority 0
#### Estimated changes
Modified data/encodable.lean




## [2017-12-14 11:08:41+01:00](https://github.com/leanprover-community/mathlib/commit/2dbf07a)
chore(.): adapt to change `by_cases t with h` to  `by_cases h : t` 746134d11ceec378a53ffd3b7ab8626fb291f3bd
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/measure_theory/measurable_space.lean


Modified data/array/lemmas.lean


Modified data/equiv.lean
- \+/\- *theorem* equiv.set.image_apply
- \+/\- *theorem* equiv.set.range_apply

Modified data/finset.lean


Modified data/finsupp.lean


Modified data/hash_map.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/list/sort.lean


Modified data/multiset.lean


Modified data/nat/basic.lean


Modified data/nat/modeq.lean


Modified data/nat/pairing.lean


Modified data/nat/prime.lean


Modified data/ordinal.lean


Modified data/rat.lean




## [2017-12-13 17:34:22+01:00](https://github.com/leanprover-community/mathlib/commit/ea19776)
refactor(data/finsupp): generalize module construction for finsupp
#### Estimated changes
Modified algebra/linear_algebra/basic.lean
- \- *lemma* lc.smul_apply
- \- *lemma* lc.sum_smul_index

Modified algebra/linear_algebra/multivariate_polynomial.lean


Modified data/finsupp.lean
- \+/\- *lemma* finsupp.neg_apply
- \+/\- *def* finsupp.prod
- \+/\- *lemma* finsupp.prod_map_range_index
- \+/\- *lemma* finsupp.prod_neg_index
- \+/\- *lemma* finsupp.prod_single_index
- \+/\- *lemma* finsupp.prod_zero_index
- \+ *lemma* finsupp.smul_apply
- \+/\- *lemma* finsupp.sub_apply
- \+/\- *def* finsupp.sum
- \+ *lemma* finsupp.sum_smul_index
- \+ *def* finsupp.to_has_scalar
- \+ *def* finsupp.to_module



## [2017-12-13 16:52:33+01:00](https://github.com/leanprover-community/mathlib/commit/b29ab1b)
feat(data/finsupp): add support_neg
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* finsupp.support_neg



## [2017-12-13 13:09:54+01:00](https://github.com/leanprover-community/mathlib/commit/a2d6148)
feat(algebra/linear_algebra): add multivariate polynomials
#### Estimated changes
Added algebra/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* finset.bind_singleton2
- \+ *lemma* finset.le_sup
- \+ *def* finset.sup
- \+ *lemma* finset.sup_empty
- \+ *lemma* finset.sup_insert
- \+ *lemma* finset.sup_le
- \+ *lemma* finset.sup_mono
- \+ *lemma* finset.sup_mono_fun
- \+ *lemma* finset.sup_singleton
- \+ *lemma* finset.sup_union
- \+ *lemma* finsupp.single_induction_on
- \+ *def* mv_polynomial.C
- \+ *lemma* mv_polynomial.C_0
- \+ *lemma* mv_polynomial.C_1
- \+ *lemma* mv_polynomial.C_mul_monomial
- \+ *def* mv_polynomial.X
- \+ *lemma* mv_polynomial.X_pow_eq_single
- \+ *def* mv_polynomial.degree_of
- \+ *def* mv_polynomial.eval
- \+ *lemma* mv_polynomial.eval_C
- \+ *lemma* mv_polynomial.eval_X
- \+ *lemma* mv_polynomial.eval_add
- \+ *lemma* mv_polynomial.eval_monomial
- \+ *lemma* mv_polynomial.eval_mul
- \+ *lemma* mv_polynomial.eval_mul_monomial
- \+ *lemma* mv_polynomial.eval_zero
- \+ *lemma* mv_polynomial.induction_on
- \+ *def* mv_polynomial.monomial
- \+ *lemma* mv_polynomial.monomial_add_single
- \+ *lemma* mv_polynomial.monomial_eq
- \+ *lemma* mv_polynomial.monomial_single_add
- \+ *def* mv_polynomial.total_degree
- \+ *def* mv_polynomial.vars
- \+ *lemma* mv_polynomial.vars_0
- \+ *lemma* mv_polynomial.vars_C
- \+ *lemma* mv_polynomial.vars_X
- \+ *lemma* mv_polynomial.vars_monomial
- \+ *def* mv_polynomial



## [2017-12-13 13:09:17+01:00](https://github.com/leanprover-community/mathlib/commit/8369c7d)
feat(data/finsupp): big product over finsupp (big sum is now derived from it)
#### Estimated changes
Modified data/finsupp.lean
- \+ *def* finsupp.prod
- \+ *lemma* finsupp.prod_add_index
- \+ *lemma* finsupp.prod_comap_domain_index
- \+ *lemma* finsupp.prod_finset_sum_index
- \+ *lemma* finsupp.prod_map_domain_index
- \+ *lemma* finsupp.prod_map_range_index
- \+ *lemma* finsupp.prod_neg_index
- \+ *lemma* finsupp.prod_single_index
- \+ *lemma* finsupp.prod_subtype_domain_index
- \+ *lemma* finsupp.prod_sum_index
- \+ *lemma* finsupp.prod_zero_index
- \- *lemma* finsupp.sum_add_index
- \- *lemma* finsupp.sum_comap_domain_index
- \- *lemma* finsupp.sum_finset_sum_index
- \- *lemma* finsupp.sum_map_domain_index
- \- *lemma* finsupp.sum_map_range_index
- \- *lemma* finsupp.sum_neg_index
- \- *lemma* finsupp.sum_single_index
- \- *lemma* finsupp.sum_subtype_domain_index
- \- *lemma* finsupp.sum_sum_index
- \- *lemma* finsupp.sum_zero_index



## [2017-12-13 12:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/421c332)
fix(algebra/big_operators): congruence rules need to provide equations for all rewritable positions
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_congr

Modified algebra/linear_algebra/basic.lean


Modified analysis/topology/infinite_sum.lean


Modified data/finsupp.lean




## [2017-12-13 12:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/81908b0)
chore(algebra/linear_algebra): second isomorphism proof
#### Estimated changes
Modified algebra/linear_algebra/linear_map_module.lean




## [2017-12-13 04:31:56-05:00](https://github.com/leanprover-community/mathlib/commit/a243710)
feat(data/ordinal): well ordering theorem
Note to self: this proof seems more cumbersome than it should be. I will see if the proof is easier if we bypass Zorn's lemma.
#### Estimated changes
Modified algebra/big_operators.lean


Modified data/cardinal.lean
- \+ *theorem* cardinal.embedding.coe_fn_mk

Modified data/hash_map.lean


Modified data/list/basic.lean


Modified data/ordinal.lean
- \+ *theorem* chain_ub
- \+ *def* empty_relation.is_well_order
- \+ *def* prod.lex.is_well_order
- \+ *def* sum.lex.is_well_order
- \+ *theorem* well_ordering_thm

Modified data/set/basic.lean
- \+ *theorem* set.set_of_subset_set_of

Modified data/sigma/basic.lean
- \+ *lemma* psigma.mk.inj_iff
- \- *lemma* psigma.mk_eq_mk_iff
- \+ *theorem* sigma.exists
- \+ *theorem* sigma.forall
- \+ *theorem* sigma.mk.inj_iff
- \- *lemma* sigma.mk_eq_mk_iff
- \+ *theorem* subtype.exists
- \+ *theorem* subtype.forall

Added data/sum.lean
- \+ *theorem* sum.exists
- \+ *theorem* sum.forall
- \+ *theorem* sum.inl.inj_iff
- \+ *theorem* sum.inr.inj_iff
- \+ *inductive* sum.lex
- \+ *theorem* sum.lex_acc_inl
- \+ *theorem* sum.lex_acc_inr
- \+ *theorem* sum.lex_inl_inl
- \+ *theorem* sum.lex_inr_inl
- \+ *theorem* sum.lex_inr_inr
- \+ *theorem* sum.lex_wf
- \+ *def* sum.swap
- \+ *lemma* sum.swap_left_inverse
- \+ *lemma* sum.swap_right_inverse
- \+ *lemma* sum.swap_swap
- \+ *lemma* sum.swap_swap_eq

Modified logic/basic.lean
- \- *theorem* eq_iff_le_and_le
- \- *theorem* set_of_subset_set_of
- \- *theorem* sigma.exists
- \- *theorem* sigma.forall
- \- *theorem* sigma.mk.inj_iff
- \- *theorem* subtype.exists
- \- *theorem* subtype.forall

Modified order/filter.lean


Modified order/zorn.lean
- \+ *theorem* zorn.chain.directed
- \+/\- *theorem* zorn.chain.total
- \+ *theorem* zorn.chain.total_of_refl



## [2017-12-12 16:06:26-05:00](https://github.com/leanprover-community/mathlib/commit/bd99ad7)
feat(data/fin): fin.succ.inj
#### Estimated changes
Modified data/fin.lean




## [2017-12-11 23:34:49-05:00](https://github.com/leanprover-community/mathlib/commit/d3149ba)
fix(*): update to lean
#### Estimated changes
Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/topological_space.lean


Modified data/set/disjointed.lean


Modified data/set/enumerate.lean


Modified order/zorn.lean




## [2017-12-11 12:19:07-05:00](https://github.com/leanprover-community/mathlib/commit/6b10d8d)
chore(tests/finish3): rename definition with same name
#### Estimated changes
Modified tests/finish3.lean
- \+ *theorem* foo':
- \- *theorem* foo:



## [2017-12-11 12:19:07-05:00](https://github.com/leanprover-community/mathlib/commit/be79f9f)
chore(data/cardinal): put embedding into cardinal namespace
#### Estimated changes
Modified data/cardinal.lean
- \+ *theorem* cardinal.embedding.antisymm
- \+ *def* cardinal.embedding.arrow_congr_left
- \+ *def* cardinal.embedding.arrow_congr_right
- \+ *theorem* cardinal.embedding.inj'
- \+ *theorem* cardinal.embedding.injective_min
- \+ *def* cardinal.embedding.prod_congr
- \+ *theorem* cardinal.embedding.refl_apply
- \+ *theorem* cardinal.embedding.schroeder_bernstein
- \+ *def* cardinal.embedding.sum_congr
- \+ *theorem* cardinal.embedding.to_fun_eq_coe
- \+ *theorem* cardinal.embedding.total
- \+ *theorem* cardinal.embedding.trans_apply
- \+ *structure* cardinal.embedding
- \- *theorem* embedding.antisymm
- \- *def* embedding.arrow_congr_left
- \- *def* embedding.arrow_congr_right
- \- *theorem* embedding.inj'
- \- *theorem* embedding.injective_min
- \- *def* embedding.prod_congr
- \- *theorem* embedding.refl_apply
- \- *theorem* embedding.schroeder_bernstein
- \- *def* embedding.sum_congr
- \- *theorem* embedding.to_fun_eq_coe
- \- *theorem* embedding.total
- \- *theorem* embedding.trans_apply
- \- *structure* embedding

Modified data/ordinal.lean




## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/ee7ede9)
feat(algebra/linear_algebra): proof first and second isomorphism laws
#### Estimated changes
Modified algebra/linear_algebra/linear_map_module.lean
- \+ *lemma* classical.some_spec2
- \+ *lemma* linear_map.is_submodule.add_left_iff
- \+ *lemma* linear_map.is_submodule.neg_iff
- \+ *def* linear_map.quot_ker_equiv_im
- \+ *def* linear_map.union_quotient_equiv_quotient_inter

Modified algebra/linear_algebra/quotient_module.lean
- \+ *lemma* is_submodule.quotient.lift_mk
- \+ *lemma* is_submodule.quotient_rel_eq

Modified algebra/linear_algebra/subtype_module.lean
- \+/\- *lemma* is_linear_map_subtype_mk
- \+/\- *lemma* sub_val



## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/01c3b8f)
feature(algebra/linear_algebra): define linear equivalence
#### Estimated changes
Modified algebra/linear_algebra/basic.lean
- \+ *def* equiv_of_is_basis
- \+ *lemma* linear_equiv.linear_inv
- \+ *def* linear_equiv.refl
- \+ *def* linear_equiv.symm
- \+ *def* linear_equiv.trans
- \+ *structure* linear_equiv
- \+ *lemma* linear_independent_singleton
- \+ *lemma* mem_span_insert
- \+ *lemma* set.diff_self



## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/85a1667)
refactor(data/equiv): state refl, symm, and trans rules for equiv using projection. This gives more powerful rfl rules
#### Estimated changes
Modified data/equiv.lean
- \+ *theorem* function.left_inverse.comp
- \+ *theorem* function.right_inverse.comp



## [2017-12-11 05:07:46-05:00](https://github.com/leanprover-community/mathlib/commit/03074f1)
feat(data/ordinal): more ordinals
#### Estimated changes
Modified data/bool.lean


Modified data/ordinal.lean
- \+ *def* initial_seg.cod_restrict
- \+ *theorem* initial_seg.cod_restrict_apply
- \+ *theorem* initial_seg.coe_coe_fn
- \+ *def* initial_seg.le_lt
- \+ *theorem* initial_seg.le_lt_apply
- \+ *def* initial_seg.lt_or_eq
- \+ *theorem* initial_seg.lt_or_eq_apply_left
- \+ *theorem* initial_seg.lt_or_eq_apply_right
- \+ *def* order_embedding.cod_restrict
- \+ *theorem* order_embedding.cod_restrict_apply
- \+ *def* ordinal.enum
- \+ *theorem* ordinal.enum_lt
- \+ *theorem* ordinal.enum_type
- \+ *theorem* ordinal.enum_typein
- \+ *theorem* ordinal.induction_on
- \- *def* ordinal.le
- \+ *def* ordinal.type
- \+ *theorem* ordinal.type_def'
- \+ *theorem* ordinal.type_def
- \+ *theorem* ordinal.type_eq
- \+ *theorem* ordinal.type_le
- \+ *theorem* ordinal.type_lt
- \+ *def* ordinal.typein
- \+ *theorem* ordinal.typein_enum
- \+ *theorem* ordinal.typein_inj
- \+ *theorem* ordinal.typein_lt_type
- \+ *theorem* ordinal.typein_lt_typein
- \+ *theorem* ordinal.typein_surj
- \+ *theorem* ordinal.typein_top
- \+ *theorem* ordinal.wf
- \+ *def* principal_seg.cod_restrict
- \+ *theorem* principal_seg.cod_restrict_apply
- \+ *theorem* principal_seg.cod_restrict_top
- \+ *theorem* principal_seg.equiv_lt_top
- \- *def* principal_seg.le_lt
- \- *theorem* principal_seg.le_lt_apply
- \+ *theorem* principal_seg.lt_le_top
- \+ *theorem* principal_seg.lt_top
- \+ *def* principal_seg.of_element
- \+ *theorem* principal_seg.of_element_apply
- \+ *theorem* principal_seg.of_element_top
- \+ *theorem* principal_seg.top_eq
- \+ *theorem* principal_seg.trans_top
- \+/\- *def* set_coe_embedding
- \+ *def* subrel



## [2017-12-10 08:36:32-05:00](https://github.com/leanprover-community/mathlib/commit/a758ffb)
feat(data/ordinal): ordinal numbers
#### Estimated changes
Modified data/cardinal.lean
- \+ *theorem* cardinal.add_mono
- \- *lemma* cardinal.add_mono
- \+ *theorem* cardinal.le_iff_exists_add
- \- *lemma* cardinal.le_iff_exists_add
- \+ *theorem* cardinal.mul_mono
- \- *lemma* cardinal.mul_mono
- \+ *theorem* cardinal.mul_power
- \- *lemma* cardinal.mul_power
- \+ *theorem* cardinal.one_power
- \- *lemma* cardinal.one_power
- \+ *theorem* cardinal.power_mono_left
- \- *lemma* cardinal.power_mono_left
- \+ *theorem* cardinal.power_mono_right
- \- *lemma* cardinal.power_mono_right
- \+ *theorem* cardinal.power_mul
- \- *lemma* cardinal.power_mul
- \+ *theorem* cardinal.power_sum
- \- *lemma* cardinal.power_sum
- \+ *theorem* cardinal.power_zero
- \- *lemma* cardinal.power_zero
- \+ *theorem* cardinal.prop_eq_two
- \- *lemma* cardinal.prop_eq_two
- \+ *theorem* cardinal.zero_le
- \- *lemma* cardinal.zero_le
- \+ *theorem* cardinal.zero_power
- \- *lemma* cardinal.zero_power
- \+ *theorem* embedding.antisymm
- \- *lemma* embedding.antisymm
- \+ *theorem* embedding.inj'
- \+ *theorem* embedding.refl_apply
- \+ *theorem* embedding.schroeder_bernstein
- \- *lemma* embedding.schroeder_bernstein
- \+ *theorem* embedding.to_fun_eq_coe
- \+ *theorem* embedding.total
- \- *lemma* embedding.total
- \+ *theorem* embedding.trans_apply
- \- *lemma* equiv.of_bijective
- \+ *theorem* equiv.to_embedding_coe_fn

Modified data/equiv.lean
- \+ *theorem* equiv.cast_apply
- \- *theorem* equiv.comp_apply
- \- *def* equiv.id
- \- *theorem* equiv.id_apply
- \+ *theorem* equiv.of_bijective_to_fun
- \+ *theorem* equiv.refl_apply
- \+ *theorem* equiv.set.image_apply
- \+ *theorem* equiv.set.range_apply
- \+/\- *theorem* equiv.swap_self
- \+/\- *theorem* equiv.swap_swap
- \+ *theorem* equiv.trans_apply

Modified data/nat/basic.lean
- \+ *def* nat.foldl
- \+ *def* nat.foldr

Added data/ordinal.lean
- \+ *structure* Well_order
- \+ *theorem* initial_seg.antisymm.aux
- \+ *def* initial_seg.antisymm
- \+ *theorem* initial_seg.antisymm_symm
- \+ *theorem* initial_seg.antisymm_to_fun
- \+ *theorem* initial_seg.coe_fn_mk
- \+ *theorem* initial_seg.coe_fn_to_order_embedding
- \+ *theorem* initial_seg.eq_or_principal
- \+ *theorem* initial_seg.init'
- \+ *theorem* initial_seg.init_iff
- \+ *def* initial_seg.of_iso
- \+ *theorem* initial_seg.of_iso_apply
- \+ *theorem* initial_seg.refl_apply
- \+ *theorem* initial_seg.trans_apply
- \+ *def* initial_seg.unique_of_extensional
- \+ *structure* initial_seg
- \+ *def* is_irrefl.swap
- \+ *def* is_irrefl_of_is_asymm
- \+ *def* is_strict_order.swap
- \+ *def* is_strict_total_order'.swap
- \+ *def* is_strict_weak_order_of_is_order_connected
- \+ *def* is_trans.swap
- \+ *def* is_trichotomous.swap
- \+ *def* order.preimage
- \+ *theorem* order_embedding.coe_fn_mk
- \+ *theorem* order_embedding.coe_fn_to_embedding
- \+ *theorem* order_embedding.eq_of_to_fun_eq
- \+ *theorem* order_embedding.eq_preimage
- \+ *theorem* order_embedding.nat_lt
- \+ *theorem* order_embedding.of_monotone
- \+ *theorem* order_embedding.ord'
- \+ *theorem* order_embedding.refl_apply
- \+ *def* order_embedding.rsymm
- \+ *theorem* order_embedding.trans_apply
- \+ *theorem* order_embedding.well_founded_iff_no_descending_seq
- \+ *structure* order_embedding
- \+ *theorem* order_iso.apply_inverse_apply
- \+ *theorem* order_iso.coe_coe_fn
- \+ *theorem* order_iso.coe_fn_mk
- \+ *theorem* order_iso.coe_fn_symm_mk
- \+ *theorem* order_iso.coe_fn_to_equiv
- \+ *theorem* order_iso.eq_of_to_fun_eq
- \+ *theorem* order_iso.inverse_apply_apply
- \+ *def* order_iso.of_surjective
- \+ *theorem* order_iso.of_surjective_apply
- \+ *theorem* order_iso.ord'
- \+ *def* order_iso.preimage
- \+ *theorem* order_iso.refl_apply
- \+ *theorem* order_iso.trans_apply
- \+ *structure* order_iso
- \+ *def* ordinal.card
- \+ *def* ordinal.le
- \+ *def* ordinal.lt
- \+ *def* ordinal
- \+ *theorem* principal_seg.coe_coe_fn'
- \+ *theorem* principal_seg.coe_coe_fn
- \+ *theorem* principal_seg.coe_fn_mk
- \+ *theorem* principal_seg.coe_fn_to_order_embedding
- \+ *theorem* principal_seg.down'
- \+ *def* principal_seg.equiv_lt
- \+ *theorem* principal_seg.equiv_lt_apply
- \+ *theorem* principal_seg.init
- \+ *theorem* principal_seg.init_iff
- \+ *theorem* principal_seg.irrefl
- \+ *def* principal_seg.le_lt
- \+ *theorem* principal_seg.le_lt_apply
- \+ *def* principal_seg.lt_le
- \+ *theorem* principal_seg.lt_le_apply
- \+ *theorem* principal_seg.trans_apply
- \+ *structure* principal_seg
- \+ *def* set_coe_embedding

Modified data/set/basic.lean
- \+ *theorem* set.set_coe_cast



## [2017-12-09 22:14:32-05:00](https://github.com/leanprover-community/mathlib/commit/aef5c88)
feat(algebra/group_power): more gpow lemmas
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* add_monoid.neg_smul
- \+ *theorem* div_pow
- \+ *theorem* division_ring.inv_pow
- \+/\- *def* gpow
- \+ *theorem* gpow_bit0
- \+ *theorem* gpow_bit1
- \+ *theorem* gpow_coe_nat
- \+ *theorem* gpow_mul
- \+ *theorem* gpow_neg
- \+ *theorem* gpow_neg_one
- \+ *theorem* gpow_one
- \+ *theorem* gpow_zero
- \+ *theorem* gsmul_bit1
- \+ *theorem* gsmul_mul
- \+ *theorem* gsmul_neg
- \+ *theorem* gsmul_neg_one
- \+ *theorem* gsmul_one
- \+ *theorem* inv_gpow
- \+/\- *theorem* inv_pow
- \+ *theorem* one_div_pow
- \+ *theorem* one_gpow
- \- *theorem* pow_inv
- \+/\- *theorem* pow_ne_zero

Modified algebra/ring.lean


Modified analysis/limits.lean


Modified data/int/basic.lean
- \+ *theorem* int.coe_nat_mul_neg_succ
- \+ *theorem* int.neg_succ_mul_coe_nat
- \+ *theorem* int.neg_succ_mul_neg_succ



## [2017-12-08 17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8cfcef0)
feat(algebra/linear_algebra): add product construction for modules
#### Estimated changes
Added algebra/linear_algebra/prod_module.lean
- \+ *lemma* prod.fst_inl
- \+ *lemma* prod.fst_inr
- \+ *lemma* prod.fst_inv
- \+ *lemma* prod.fst_mul
- \+ *lemma* prod.fst_one
- \+ *lemma* prod.fst_prod
- \+ *lemma* prod.injective_inl
- \+ *lemma* prod.injective_inr
- \+ *def* prod.inl
- \+ *lemma* prod.inl_eq_inl
- \+ *lemma* prod.inl_eq_inr
- \+ *def* prod.inr
- \+ *lemma* prod.inr_eq_inl
- \+ *lemma* prod.inr_eq_inr
- \+ *lemma* prod.is_basis_inl_union_inr
- \+ *lemma* prod.is_linear_map_prod_fst
- \+ *lemma* prod.is_linear_map_prod_inl
- \+ *lemma* prod.is_linear_map_prod_inr
- \+ *lemma* prod.is_linear_map_prod_mk
- \+ *lemma* prod.is_linear_map_prod_snd
- \+ *lemma* prod.linear_independent_inl_union_inr
- \+ *lemma* prod.snd_inl
- \+ *lemma* prod.snd_inr
- \+ *lemma* prod.snd_inv
- \+ *lemma* prod.snd_mul
- \+ *lemma* prod.snd_one
- \+ *lemma* prod.snd_prod
- \+ *lemma* prod.span_inl_union_inr
- \+ *lemma* prod.span_prod



## [2017-12-08 17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8fab107)
refactor(algebra/module): split of type constructions and move quotient, subtype and linear_map to their own theories in algebra/linear_algebra
#### Estimated changes
Modified algebra/group.lean


Modified algebra/linear_algebra/basic.lean
- \+ *lemma* linear_independent_union

Added algebra/linear_algebra/linear_map_module.lean
- \+ *lemma* linear_map.add_app
- \+ *theorem* linear_map.ext
- \+ *def* linear_map.im
- \+ *theorem* linear_map.inj_of_trivial_ker
- \+ *lemma* linear_map.is_linear_map_coe
- \+ *def* linear_map.ker
- \+ *theorem* linear_map.ker_of_map_eq_map
- \+ *lemma* linear_map.map_add
- \+ *lemma* linear_map.map_neg
- \+ *lemma* linear_map.map_smul
- \+ *lemma* linear_map.map_sub
- \+ *lemma* linear_map.map_zero
- \+ *lemma* linear_map.mem_im
- \+ *lemma* linear_map.mem_ker
- \+ *lemma* linear_map.neg_app
- \+ *lemma* linear_map.smul_app
- \+ *theorem* linear_map.sub_ker
- \+ *lemma* linear_map.zero_app
- \+ *def* linear_map
- \+ *def* module.endomorphism_ring
- \+ *def* module.general_linear_group
- \+ *lemma* module.mul_app
- \+ *lemma* module.one_app

Added algebra/linear_algebra/quotient_module.lean
- \+ *lemma* is_submodule.is_linear_map_quotient_lift
- \+ *lemma* is_submodule.is_linear_map_quotient_mk
- \+ *lemma* is_submodule.quotient.injective_lift
- \+ *def* is_submodule.quotient.lift
- \+ *def* is_submodule.quotient
- \+ *def* is_submodule.quotient_rel

Added algebra/linear_algebra/subtype_module.lean
- \+ *lemma* add_val
- \+ *lemma* is_linear_map_subtype_mk
- \+ *lemma* is_linear_map_subtype_val
- \+ *lemma* neg_val
- \+ *lemma* smul_val
- \+ *lemma* sub_val
- \+ *lemma* zero_val

Modified algebra/module.lean
- \- *lemma* is_submodule.add_val
- \- *lemma* is_submodule.is_linear_map_quotient_lift
- \- *lemma* is_submodule.is_linear_map_quotient_mk
- \- *lemma* is_submodule.is_linear_map_subtype_mk
- \- *lemma* is_submodule.is_linear_map_subtype_val
- \- *lemma* is_submodule.neg_val
- \- *lemma* is_submodule.quotient.injective_lift
- \- *def* is_submodule.quotient.lift
- \- *def* is_submodule.quotient
- \- *def* is_submodule.quotient_rel
- \- *lemma* is_submodule.smul_val
- \- *lemma* is_submodule.sub_val
- \- *lemma* is_submodule.zero_val
- \- *lemma* linear_map.add_app
- \- *theorem* linear_map.ext
- \- *def* linear_map.im
- \- *theorem* linear_map.inj_of_trivial_ker
- \- *lemma* linear_map.is_linear_map_coe
- \- *def* linear_map.ker
- \- *theorem* linear_map.ker_of_map_eq_map
- \- *lemma* linear_map.map_add
- \- *lemma* linear_map.map_neg
- \- *lemma* linear_map.map_smul
- \- *lemma* linear_map.map_sub
- \- *lemma* linear_map.map_zero
- \- *lemma* linear_map.mem_im
- \- *lemma* linear_map.mem_ker
- \- *lemma* linear_map.neg_app
- \- *lemma* linear_map.smul_app
- \- *theorem* linear_map.sub_ker
- \- *lemma* linear_map.zero_app
- \- *def* linear_map
- \- *def* module.endomorphism_ring
- \- *def* module.general_linear_group
- \- *lemma* module.mul_app
- \- *lemma* module.one_app

Modified data/finsupp.lean
- \+ *def* finsupp.filter
- \+ *lemma* finsupp.filter_apply_neg
- \+ *lemma* finsupp.filter_apply_pos
- \+ *lemma* finsupp.filter_pos_add_filter_neg
- \+ *lemma* finsupp.support_filter
- \+ *lemma* finsupp.support_subset_iff

Modified data/set/basic.lean
- \+ *lemma* set.mem_image_of_injective



## [2017-12-08 17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/fccc5d3)
refactor(algebra/linear_algebra): move zero_not_mem_of_linear_independent from vector_space to module (zero_ne_one should be a typeclass in Prop not in Type)
#### Estimated changes
Modified algebra/linear_algebra/basic.lean
- \+ *lemma* zero_ne_one_or_forall_eq_0
- \+/\- *lemma* zero_not_mem_of_linear_independent



## [2017-12-08 08:32:13-05:00](https://github.com/leanprover-community/mathlib/commit/bd013e8)
feat(data/dardinal): wellordering of cardinals
#### Estimated changes
Modified algebra/linear_algebra/basic.lean
- \+/\- *lemma* exists_is_basis
- \+ *lemma* exists_subset_is_basis

Modified analysis/measure_theory/measurable_space.lean


Modified analysis/metric_space.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified data/bool.lean
- \+ *theorem* bool.to_bool_coe

Modified data/cardinal.lean
- \+ *theorem* cardinal.cantor
- \+ *lemma* cardinal.le_iff_exists_add
- \+ *theorem* cardinal.le_min
- \+ *theorem* cardinal.le_sum
- \+ *theorem* cardinal.le_sup
- \+ *def* cardinal.min
- \+ *theorem* cardinal.min_eq
- \+ *theorem* cardinal.min_le
- \+/\- *lemma* cardinal.mul_power
- \+ *theorem* cardinal.ne_zero_iff_nonempty
- \+/\- *lemma* cardinal.one_power
- \+/\- *lemma* cardinal.power_mono_left
- \+/\- *lemma* cardinal.power_mono_right
- \+/\- *lemma* cardinal.power_mul
- \+/\- *lemma* cardinal.power_sum
- \+/\- *lemma* cardinal.power_zero
- \+ *lemma* cardinal.prop_eq_two
- \+ *def* cardinal.sum
- \+ *def* cardinal.sup
- \+ *theorem* cardinal.sup_le
- \+ *lemma* cardinal.zero_le
- \+/\- *lemma* cardinal.zero_power
- \- *lemma* embedding.exists_injective_or_surjective
- \+ *theorem* embedding.injective_min
- \- *def* embedding.option.Sup
- \- *lemma* embedding.option.Sup_le
- \- *lemma* embedding.option.eq_of_le_some
- \- *inductive* embedding.option.le
- \- *lemma* embedding.option.le_Sup
- \- *lemma* embedding.option.mem_of_Sup_eq_some
- \- *def* embedding.option.strict_partial_order
- \- *def* embedding.pfun.partial_order
- \- *def* embedding.pfun
- \+/\- *lemma* embedding.total

Modified data/equiv.lean


Modified data/finset.lean
- \+/\- *lemma* finset.case_strong_induction_on
- \+ *theorem* finset.le_iff_subset
- \+ *theorem* finset.lt_iff_ssubset
- \+/\- *lemma* finset.strong_induction_on
- \+ *theorem* finset.val_lt_iff

Modified data/multiset.lean
- \+ *lemma* multiset.case_strong_induction_on
- \+ *lemma* multiset.strong_induction_on

Modified data/set/basic.lean
- \+ *lemma* set.empty_prod
- \+ *theorem* set.eq_empty_iff_forall_not_mem
- \- *theorem* set.eq_empty_of_forall_not_mem
- \+ *theorem* set.image_swap_eq_preimage_swap
- \+ *lemma* set.image_swap_prod
- \+ *lemma* set.insert_prod
- \+/\- *theorem* set.mem_insert_iff
- \+ *lemma* set.mem_prod
- \+ *lemma* set.mem_prod_eq
- \+ *lemma* set.prod_empty
- \+ *lemma* set.prod_image_image_eq
- \+ *lemma* set.prod_insert
- \+ *lemma* set.prod_inter_prod
- \+ *lemma* set.prod_mk_mem_set_prod_eq
- \+ *lemma* set.prod_mono
- \+ *lemma* set.prod_neq_empty_iff
- \+ *theorem* set.prod_preimage_eq
- \+ *lemma* set.prod_singleton_singleton
- \+ *lemma* set.univ_prod_univ

Modified data/set/default.lean


Modified data/set/disjointed.lean


Modified data/set/enumerate.lean


Modified data/set/finite.lean


Modified data/set/intervals.lean


Modified data/set/lattice.lean
- \- *lemma* bind_def
- \- *lemma* fmap_eq_image
- \- *lemma* image_Union
- \- *lemma* image_congr
- \- *lemma* mem_seq_iff
- \- *theorem* monotone_preimage
- \- *theorem* preimage_Union
- \- *theorem* preimage_sUnion
- \+ *lemma* set.bind_def
- \+ *lemma* set.fmap_eq_image
- \+ *lemma* set.image_Union
- \+ *lemma* set.image_congr
- \+ *lemma* set.mem_seq_iff
- \+ *theorem* set.monotone_preimage
- \+ *theorem* set.monotone_prod
- \+ *theorem* set.preimage_Union
- \+ *theorem* set.preimage_sUnion
- \+ *lemma* set.subtype_val_image
- \+ *lemma* set.univ_subtype
- \- *lemma* subtype_val_image
- \- *lemma* univ_subtype

Deleted data/set/prod.lean
- \- *lemma* set.empty_prod
- \- *theorem* set.image_swap_eq_preimage_swap
- \- *lemma* set.image_swap_prod
- \- *lemma* set.insert_prod
- \- *lemma* set.mem_prod
- \- *lemma* set.mem_prod_eq
- \- *theorem* set.monotone_prod
- \- *lemma* set.prod_empty
- \- *lemma* set.prod_image_image_eq
- \- *lemma* set.prod_insert
- \- *lemma* set.prod_inter_prod
- \- *lemma* set.prod_mk_mem_set_prod_eq
- \- *lemma* set.prod_mono
- \- *lemma* set.prod_neq_empty_iff
- \- *theorem* set.prod_preimage_eq
- \- *lemma* set.prod_singleton_singleton
- \- *lemma* set.univ_prod_univ

Modified logic/basic.lean
- \+ *theorem* empty.elim

Modified logic/function.lean
- \+ *theorem* function.cantor_injective
- \+ *theorem* function.cantor_surjective

Modified order/zorn.lean
- \+ *theorem* zorn.chain.total

Modified theories/number_theory/dioph.lean
- \- *def* arity
- \- *def* curry
- \- *def* uncurry
- \+ *theorem* vector3.append_add
- \- *def* vector3.append_add
- \+ *theorem* vector3.append_cons
- \- *def* vector3.append_cons
- \+ *theorem* vector3.append_left
- \- *def* vector3.append_left
- \+ *theorem* vector3.append_nil
- \- *def* vector3.append_nil
- \+ *theorem* vector3.cons_fs
- \- *def* vector3.cons_fs
- \+ *theorem* vector3.cons_fz
- \- *def* vector3.cons_fz
- \+ *theorem* vector3.insert_fs
- \- *def* vector3.insert_fs



## [2017-12-08 10:51:42+01:00](https://github.com/leanprover-community/mathlib/commit/b547de0)
chore(data/finsupp): replace { n with ... } syntax with { ..., .. n } (the former is deprecated)
#### Estimated changes
Modified data/finsupp.lean




## [2017-12-08 10:48:54+01:00](https://github.com/leanprover-community/mathlib/commit/e1e80b4)
chore(.): replace ginduction by induction; changed in lean revision 49e7a642c35e83ed16cbc573deef5bd3b6dfc627
#### Estimated changes
Modified data/hash_map.lean


Modified data/int/basic.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified theories/set_theory.lean




## [2017-12-07 17:25:25+01:00](https://github.com/leanprover-community/mathlib/commit/c32d01d)
feat(algebra/linear_algebra): add basic theory on linear algebra
#### Estimated changes
Added algebra/linear_algebra/basic.lean
- \+ *lemma* constr_add
- \+ *lemma* constr_basis
- \+ *lemma* constr_congr
- \+ *lemma* constr_eq
- \+ *lemma* constr_im_eq_span
- \+ *lemma* constr_mem_span
- \+ *lemma* constr_neg
- \+ *lemma* constr_smul
- \+ *lemma* constr_sub
- \+ *lemma* constr_zero
- \+ *lemma* eq_of_linear_independent_of_span
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *lemma* exists_is_basis
- \+ *lemma* exists_left_inverse_linear_map_of_injective
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *lemma* finset.smul_sum
- \+ *lemma* finsupp.smul_sum
- \+ *def* is_basis.constr
- \+ *lemma* is_basis.eq_linear_map
- \+ *lemma* is_basis.map_constr
- \+ *lemma* is_basis.map_repr
- \+ *def* is_basis
- \+ *lemma* is_linear_map.finsupp_sum
- \+ *lemma* is_submodule_range_smul
- \+ *lemma* is_submodule_span
- \+ *lemma* lc.is_linear_map_sum
- \+ *lemma* lc.smul_apply
- \+ *lemma* lc.sum_smul_index
- \+ *def* lc
- \+ *lemma* linear_eq_on
- \+ *lemma* linear_independent.eq_0_of_span
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_independent.inj_span_iff_inj
- \+ *lemma* linear_independent.insert
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent.of_image
- \+ *def* linear_independent.repr
- \+ *lemma* linear_independent.unique
- \+ *def* linear_independent
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent_empty
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_map.linear_independent_image_iff
- \+ *lemma* mem_span_insert_exchange
- \+ *def* module_equiv_lc
- \+ *lemma* repr_add
- \+ *lemma* repr_eq
- \+ *lemma* repr_eq_repr_of_subset
- \+ *lemma* repr_eq_single
- \+ *lemma* repr_eq_zero
- \+ *lemma* repr_finsupp_sum
- \+ *lemma* repr_neg
- \+ *lemma* repr_not_span
- \+ *lemma* repr_smul
- \+ *lemma* repr_spec
- \+ *lemma* repr_sub
- \+ *lemma* repr_sum
- \+ *lemma* repr_sum_eq
- \+ *lemma* repr_support
- \+ *lemma* repr_zero
- \+ *def* span
- \+ *lemma* span_empty
- \+ *lemma* span_eq
- \+ *lemma* span_eq_of_is_submodule
- \+ *lemma* span_image_of_linear_map
- \+ *lemma* span_insert
- \+ *lemma* span_insert_eq_span
- \+ *lemma* span_minimal
- \+ *lemma* span_mono
- \+ *lemma* span_singleton
- \+ *lemma* span_span
- \+ *lemma* span_union
- \+ *lemma* subset_span
- \+ *lemma* zero_not_mem_of_linear_independent

Added algebra/linear_algebra/default.lean




## [2017-12-07 17:24:30+01:00](https://github.com/leanprover-community/mathlib/commit/f09abb1)
feat(data/finsupp): add type of functions with finite support
#### Estimated changes
Added data/finsupp.lean
- \+ *lemma* finsupp.add_apply
- \+ *def* finsupp.comap_domain
- \+ *lemma* finsupp.comap_domain_add
- \+ *lemma* finsupp.comap_domain_apply
- \+ *lemma* finsupp.comap_domain_finsupp_sum
- \+ *lemma* finsupp.comap_domain_neg
- \+ *lemma* finsupp.comap_domain_sub
- \+ *lemma* finsupp.comap_domain_sum
- \+ *lemma* finsupp.comap_domain_zero
- \+ *lemma* finsupp.ext
- \+ *lemma* finsupp.finite_supp
- \+ *def* finsupp.map_domain
- \+ *lemma* finsupp.map_domain_add
- \+ *lemma* finsupp.map_domain_comp
- \+ *lemma* finsupp.map_domain_congr
- \+ *lemma* finsupp.map_domain_finset_sum
- \+ *lemma* finsupp.map_domain_id
- \+ *lemma* finsupp.map_domain_single
- \+ *lemma* finsupp.map_domain_sum
- \+ *lemma* finsupp.map_domain_support
- \+ *lemma* finsupp.map_domain_zero
- \+ *def* finsupp.map_range
- \+ *lemma* finsupp.map_range_apply
- \+ *lemma* finsupp.mem_support_iff
- \+ *lemma* finsupp.mul_def
- \+ *lemma* finsupp.neg_apply
- \+ *lemma* finsupp.one_def
- \+ *lemma* finsupp.prod_single
- \+ *def* finsupp.single
- \+ *lemma* finsupp.single_add
- \+ *lemma* finsupp.single_apply
- \+ *lemma* finsupp.single_eq_of_ne
- \+ *lemma* finsupp.single_eq_same
- \+ *lemma* finsupp.single_mul_single
- \+ *lemma* finsupp.single_zero
- \+ *lemma* finsupp.sub_apply
- \+ *def* finsupp.subtype_domain
- \+ *lemma* finsupp.subtype_domain_add
- \+ *lemma* finsupp.subtype_domain_apply
- \+ *lemma* finsupp.subtype_domain_finsupp_sum
- \+ *lemma* finsupp.subtype_domain_neg
- \+ *lemma* finsupp.subtype_domain_sub
- \+ *lemma* finsupp.subtype_domain_sum
- \+ *lemma* finsupp.subtype_domain_zero
- \+ *def* finsupp.sum
- \+ *lemma* finsupp.sum_add
- \+ *lemma* finsupp.sum_add_index
- \+ *lemma* finsupp.sum_apply
- \+ *lemma* finsupp.sum_comap_domain_index
- \+ *lemma* finsupp.sum_finset_sum_index
- \+ *lemma* finsupp.sum_map_domain_index
- \+ *lemma* finsupp.sum_map_range_index
- \+ *lemma* finsupp.sum_neg
- \+ *lemma* finsupp.sum_neg_index
- \+ *lemma* finsupp.sum_single
- \+ *lemma* finsupp.sum_single_index
- \+ *lemma* finsupp.sum_sub_index
- \+ *lemma* finsupp.sum_subtype_domain_index
- \+ *lemma* finsupp.sum_sum_index
- \+ *lemma* finsupp.sum_zero
- \+ *lemma* finsupp.sum_zero_index
- \+ *def* finsupp.support
- \+ *lemma* finsupp.support_add
- \+ *lemma* finsupp.support_map_range
- \+ *lemma* finsupp.support_single_ne_zero
- \+ *lemma* finsupp.support_single_subset
- \+ *lemma* finsupp.support_sum
- \+ *lemma* finsupp.support_zero
- \+ *lemma* finsupp.support_zip_with
- \+ *def* finsupp.to_comm_ring
- \+ *def* finsupp.to_comm_semiring
- \+ *def* finsupp.to_ring
- \+ *def* finsupp.to_semiring
- \+ *lemma* finsupp.zero_apply
- \+ *def* finsupp.zip_with
- \+ *lemma* finsupp.zip_with_apply
- \+ *def* finsupp



## [2017-12-07 17:22:37+01:00](https://github.com/leanprover-community/mathlib/commit/fcf0bfa)
feat(data/set/finite): add finite_to_set, finset.coe_to_finset
#### Estimated changes
Modified data/set/finite.lean
- \+/\- *lemma* finset.coe_filter
- \+ *lemma* finset.coe_to_finset
- \+ *lemma* finset.finite_to_set



## [2017-12-07 17:18:54+01:00](https://github.com/leanprover-community/mathlib/commit/5e42425)
fix(algebra/module): fix type universes in is_linear_map.sum
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* is_linear_map.sum



## [2017-12-07 14:42:09+01:00](https://github.com/leanprover-community/mathlib/commit/0995ac1)
feat(algebra/module): the inverse of a linear map is linear
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* is_linear_map.inverse
- \+ *lemma* is_submodule.smul_ne_0



## [2017-12-07 14:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/645bf60)
core(algebra/module): generalize map_smul_left; add is_submodule.range
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* is_linear_map.map_smul_left



## [2017-12-07 00:39:32-05:00](https://github.com/leanprover-community/mathlib/commit/5f642d8)
refactor(*): remove local simp AC lemmas
Using local simp lemmas everywhere for mul_assoc and friends defeats the purpose of the change in core. Now theorems are proven with only the AC lemmas actually used in the proof.
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* div_eq_inv_mul

Modified algebra/functions.lean
- \+ *theorem* le_max_left_iff_true
- \+ *theorem* le_max_right_iff_true
- \+ *theorem* max.left_comm
- \+ *theorem* max.right_comm
- \+ *theorem* min_right_comm

Modified algebra/group_power.lean


Modified algebra/order.lean
- \+/\- *lemma* le_of_not_lt
- \+ *lemma* le_or_lt
- \+ *lemma* lt_or_le
- \+/\- *lemma* not_le
- \+/\- *lemma* not_lt

Modified analysis/ennreal.lean
- \+ *theorem* ennreal.le_def
- \+/\- *lemma* ennreal.of_real_lt_of_real_iff_cases

Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/real.lean
- \- *lemma* eq_0_of_nonneg_of_neg_nonneg
- \+ *lemma* nonneg_antisymm
- \+/\- *lemma* uniform_embedding_mul_rat

Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_closed_iff_nhds
- \+ *lemma* is_open_iff_forall_mem_open
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *lemma* is_open_iff_nhds
- \+ *lemma* mem_interior
- \+ *lemma* subset_interior_iff_open

Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/analysis/filter.lean


Modified data/analysis/topology.lean


Modified data/cardinal.lean


Modified data/finset.lean
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_subset
- \+/\- *theorem* finset.insert_union
- \+/\- *theorem* finset.inter_assoc
- \+/\- *theorem* finset.inter_comm
- \+/\- *theorem* finset.inter_left_comm
- \+/\- *theorem* finset.inter_right_comm
- \+/\- *theorem* finset.union_assoc
- \+/\- *theorem* finset.union_comm
- \+/\- *theorem* finset.union_insert
- \+/\- *theorem* finset.union_left_comm

Modified data/multiset.lean


Modified data/nat/sqrt.lean


Modified data/num/lemmas.lean


Modified data/rat.lean


Modified data/set/countable.lean


Modified data/set/disjointed.lean


Modified data/set/intervals.lean


Modified logic/function.lean


Modified order/basic.lean
- \- *theorem* le_max_left_iff_true
- \- *theorem* le_max_right_iff_true
- \- *theorem* max.left_comm
- \- *theorem* max.right_comm
- \- *theorem* min_right_comm
- \- *lemma* not_le_iff
- \- *lemma* not_lt_iff

Modified order/filter.lean


Modified order/zorn.lean


Modified tactic/converter/interactive.lean


Modified theories/number_theory/dioph.lean


Modified theories/number_theory/pell.lean




## [2017-12-06 17:16:14+01:00](https://github.com/leanprover-community/mathlib/commit/a3a2faa)
feat(algebra/big_operators): add renameing rules under bijection
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_attach
- \+ *lemma* finset.prod_bij
- \+ *lemma* finset.prod_bij_ne_one

Modified data/finset.lean
- \+ *lemma* finset.attach_image_val



## [2017-12-06 16:48:38+01:00](https://github.com/leanprover-community/mathlib/commit/e5c4eb1)
feat(data/set): add lift converting finset to set
#### Estimated changes
Modified data/set/default.lean


Modified data/set/finite.lean
- \+ *lemma* finset.coe_bind
- \+ *lemma* finset.coe_empty
- \+ *lemma* finset.coe_eq_coe
- \+ *lemma* finset.coe_erase
- \+ *lemma* finset.coe_filter
- \+ *lemma* finset.coe_image
- \+ *lemma* finset.coe_insert
- \+ *lemma* finset.coe_inter
- \+ *lemma* finset.coe_sdiff
- \+ *lemma* finset.coe_singleton
- \+ *lemma* finset.coe_subseteq_coe
- \+ *lemma* finset.coe_union
- \+ *lemma* finset.mem_coe
- \+ *def* finset.to_set



## [2017-12-06 16:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/7f9dd51)
feat(data/finset): add strong induction rules for finset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.card_eq_succ
- \+ *theorem* finset.card_le_of_subset
- \+ *lemma* finset.card_lt_card
- \+ *lemma* finset.case_strong_induction_on
- \+ *theorem* finset.eq_of_subset_of_card_le
- \+ *lemma* finset.strong_induction_on



## [2017-12-06 16:21:41+01:00](https://github.com/leanprover-community/mathlib/commit/81e53e8)
feat(data/finset): add ssubset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.erase_ssubset
- \+ *lemma* finset.ssubset_iff
- \+ *lemma* finset.ssubset_insert



## [2017-12-06 13:30:50+01:00](https://github.com/leanprover-community/mathlib/commit/f9b39eb)
feature(.): add various theorems
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.bind_mono
- \+ *lemma* finset.bind_singleton

Modified data/prod.lean
- \+ *lemma* prod.eq_iff_fst_eq_snd_eq
- \+ *theorem* prod.exists
- \+ *theorem* prod.forall
- \+/\- *lemma* prod.fst_swap
- \+/\- *lemma* prod.mk.eta
- \+ *theorem* prod.mk.inj_iff
- \+/\- *lemma* prod.snd_swap
- \+/\- *def* prod.swap
- \+/\- *lemma* prod.swap_left_inverse
- \+/\- *lemma* prod.swap_prod_mk
- \+/\- *lemma* prod.swap_right_inverse
- \+/\- *lemma* prod.swap_swap
- \+/\- *lemma* prod.swap_swap_eq

Modified data/set/basic.lean
- \+ *lemma* set.diff_diff
- \+ *theorem* set.insert_sdiff
- \+ *lemma* set.insert_subset
- \+ *lemma* set.insert_subset_insert
- \+ *lemma* set.insert_union
- \+/\- *theorem* set.nonempty_of_inter_nonempty_left
- \+/\- *theorem* set.nonempty_of_inter_nonempty_right
- \+/\- *lemma* set.not_not_mem
- \+ *lemma* set.not_subset
- \+/\- *theorem* set.ssubset_def
- \+ *lemma* set.union_insert

Modified data/set/finite.lean
- \+ *theorem* set.finite.dinduction_on
- \+ *lemma* set.to_finset_insert

Modified logic/basic.lean
- \- *theorem* prod.exists
- \- *theorem* prod.forall
- \- *theorem* prod.mk.inj_iff



## [2017-12-06 06:02:26-05:00](https://github.com/leanprover-community/mathlib/commit/fd803b6)
chore(.): adapt to change bc89ebc19c93392419b7bab8b68271db12855dc5 (improve how induction hypotheses are named)
#### Estimated changes
Modified data/analysis/filter.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/multiset.lean


Modified data/num/lemmas.lean


Modified tests/finish3.lean




## [2017-12-05 15:23:53-05:00](https://github.com/leanprover-community/mathlib/commit/c43e013)
fix(theories/number_theory/pell,*): fix broken proofs, less simp AC
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* is_submodule.add_val
- \+/\- *lemma* is_submodule.neg_val

Modified algebra/ring.lean


Modified data/bool.lean
- \+ *theorem* bool.coe_to_bool
- \- *theorem* bool.to_bool_bool

Modified data/hash_map.lean


Modified data/list/basic.lean


Modified data/nat/basic.lean


Modified data/nat/gcd.lean


Modified data/nat/sqrt.lean


Modified data/num/lemmas.lean


Modified data/seq/parallel.lean


Modified data/seq/wseq.lean


Modified data/set/basic.lean


Modified data/set/lattice.lean


Modified data/set/prod.lean


Modified theories/number_theory/dioph.lean


Modified theories/number_theory/pell.lean


Modified theories/set_theory.lean




## [2017-12-05 18:39:28+01:00](https://github.com/leanprover-community/mathlib/commit/e9e51db)
fix(data/sigma): use Sort for psigma
#### Estimated changes
Modified data/sigma/basic.lean




## [2017-12-05 18:13:32+01:00](https://github.com/leanprover-community/mathlib/commit/0e3b156)
fix(algebra/module): remove instance endomorphism_ring, it breaks real.lean
#### Estimated changes
Modified algebra/module.lean
- \+ *def* module.endomorphism_ring
- \+/\- *def* module.general_linear_group



## [2017-12-05 18:03:32+01:00](https://github.com/leanprover-community/mathlib/commit/394d721)
feat(algebra/module): add quotient module
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* is_submodule.is_linear_map_quotient_lift
- \+ *lemma* is_submodule.is_linear_map_quotient_mk
- \+ *lemma* is_submodule.quotient.injective_lift
- \+ *def* is_submodule.quotient.lift
- \+ *def* is_submodule.quotient
- \+ *def* is_submodule.quotient_rel



## [2017-12-05 17:24:36+01:00](https://github.com/leanprover-community/mathlib/commit/dcfb9a0)
refactor(algebra/module): add is_linear_map as predicate
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* is_linear_map.comp
- \+ *lemma* is_linear_map.id
- \+ *lemma* is_linear_map.map_add
- \+ *lemma* is_linear_map.map_neg
- \+ *lemma* is_linear_map.map_smul_left
- \+ *lemma* is_linear_map.map_smul_right
- \+ *lemma* is_linear_map.map_sub
- \+ *lemma* is_linear_map.map_sum
- \+ *lemma* is_linear_map.map_zero
- \+ *lemma* is_linear_map.neg
- \+ *lemma* is_linear_map.sub
- \+ *lemma* is_linear_map.sum
- \+ *lemma* is_linear_map.zero
- \+ *structure* is_linear_map
- \+ *lemma* is_submodule.Inter_submodule
- \+ *lemma* is_submodule.is_linear_map_subtype_mk
- \+ *lemma* is_submodule.is_linear_map_subtype_val
- \+/\- *lemma* is_submodule.sub_val
- \+/\- *lemma* linear_map.add_app
- \+/\- *theorem* linear_map.ext
- \+/\- *def* linear_map.im
- \+ *lemma* linear_map.is_linear_map_coe
- \+/\- *def* linear_map.ker
- \+ *lemma* linear_map.map_add
- \- *lemma* linear_map.map_add_app
- \+/\- *lemma* linear_map.map_neg
- \+ *lemma* linear_map.map_smul
- \- *lemma* linear_map.map_smul_app
- \+/\- *lemma* linear_map.map_sub
- \+/\- *lemma* linear_map.map_zero
- \+/\- *lemma* linear_map.mem_im
- \+/\- *lemma* linear_map.neg_app
- \+/\- *lemma* linear_map.smul_app
- \+/\- *lemma* linear_map.zero_app
- \+ *def* linear_map
- \- *structure* linear_map
- \- *def* module.endomorphism_ring
- \+/\- *def* module.general_linear_group
- \+/\- *lemma* module.mul_app
- \+/\- *lemma* module.one_app
- \+ *lemma* set.sInter_eq_Inter
- \+ *lemma* smul_eq_mul



## [2017-12-05 14:35:49+01:00](https://github.com/leanprover-community/mathlib/commit/88202b6)
refactor(algebra/module): clean up is_submodule projections
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* is_submodule.add
- \+/\- *lemma* is_submodule.add_val
- \+/\- *lemma* is_submodule.neg
- \+/\- *lemma* is_submodule.neg_val
- \+/\- *lemma* is_submodule.sub
- \+ *lemma* is_submodule.sub_val
- \+ *lemma* is_submodule.sum
- \+ *lemma* is_submodule.zero



## [2017-12-05 14:15:07+01:00](https://github.com/leanprover-community/mathlib/commit/90ed0ab)
refactor(algebra/module): rename submodule -> is_submodule, smul_left_distrib -> smul_add, smul_right_distrib -> add_smul, smul_sub_left_distrib -> smul_sub, sub_smul_right_distrib -> sub_smul
#### Estimated changes
Modified algebra/module.lean
- \+ *theorem* add_smul
- \+ *lemma* is_submodule.add_val
- \+ *lemma* is_submodule.neg
- \+ *lemma* is_submodule.neg_val
- \+ *lemma* is_submodule.smul_val
- \+ *lemma* is_submodule.sub
- \+ *lemma* is_submodule.zero_val
- \+ *theorem* smul_add
- \- *theorem* smul_left_distrib
- \- *theorem* smul_right_distrib
- \+ *theorem* smul_sub
- \- *theorem* smul_sub_left_distrib
- \+ *theorem* sub_smul
- \- *theorem* sub_smul_right_distrib
- \- *lemma* submodule.add_val
- \- *lemma* submodule.neg
- \- *lemma* submodule.neg_val
- \- *lemma* submodule.smul_val
- \- *lemma* submodule.sub
- \- *lemma* submodule.zero_val



## [2017-12-05 12:33:55+01:00](https://github.com/leanprover-community/mathlib/commit/6ebe286)
refactor(.): use new funext tactic
#### Estimated changes
Modified analysis/measure_theory/measure_space.lean


Modified analysis/metric_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/analysis/topology.lean


Modified data/equiv.lean


Modified data/int/basic.lean
- \+/\- *theorem* int.mod_add_cancel_right
- \+/\- *theorem* int.mod_sub_cancel_right

Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/pfun.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified order/complete_lattice.lean


Modified order/filter.lean




## [2017-12-05 12:04:46+01:00](https://github.com/leanprover-community/mathlib/commit/8273536)
chore(.): adapt to change 6d96741010f5f36f2f4f046e4b2b8276eb2b04d4 (provide names for constructor arguments)
#### Estimated changes
Modified data/nat/basic.lean


Modified data/option.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified data/set/basic.lean


Modified tactic/finish.lean


Modified tests/finish3.lean




## [2017-12-05 11:24:13+01:00](https://github.com/leanprover-community/mathlib/commit/f6474f0)
chore(.): adapt to change b7322e28c12d274ccec992b7fc49d35b2e56a2a4 (remove AC simp rules)
#### Estimated changes
Modified algebra/field.lean


Modified algebra/group_power.lean


Modified algebra/module.lean


Modified algebra/ring.lean


Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/analysis/filter.lean


Modified data/analysis/topology.lean


Modified data/array/lemmas.lean


Modified data/finset.lean
- \+/\- *def* finset.fold

Modified data/hash_map.lean


Modified data/list/basic.lean
- \+/\- *theorem* list.diff_nil
- \+/\- *theorem* list.pw_filter_nil

Modified data/list/perm.lean


Modified data/list/sort.lean


Modified data/multiset.lean
- \+ *theorem* multiset.quot_mk_to_coe''

Modified data/nat/basic.lean


Modified data/nat/gcd.lean


Modified data/nat/modeq.lean


Modified data/nat/sqrt.lean


Modified data/num/lemmas.lean


Modified data/rat.lean


Modified data/seq/wseq.lean


Modified data/set/basic.lean


Modified data/set/countable.lean


Modified data/set/finite.lean


Modified data/set/lattice.lean


Modified data/set/prod.lean


Modified logic/basic.lean


Modified order/complete_lattice.lean


Modified order/filter.lean


Modified order/zorn.lean


Modified pending/default.lean
- \+ *lemma* of_to_bool_iff

Modified tactic/finish.lean


Modified tests/finish3.lean


Modified theories/number_theory/dioph.lean
- \+/\- *theorem* dioph.dioph_comp
- \+/\- *theorem* dioph.dioph_fn_comp

Modified theories/number_theory/pell.lean


Modified theories/set_theory.lean




## [2017-12-04 23:24:01-05:00](https://github.com/leanprover-community/mathlib/commit/2dadfdb)
feat(tactic/norm_num): add {nat,int}.mod
#### Estimated changes
Modified tactic/norm_num.lean
- \+ *lemma* norm_num.int_mod_helper
- \+ *lemma* norm_num.nat_mod_helper



## [2017-12-04 23:05:57-05:00](https://github.com/leanprover-community/mathlib/commit/8d27f70)
feat(tactic/norm_num): add support for {nat,int}.div
#### Estimated changes
Modified data/rat.lean


Modified tactic/norm_num.lean
- \+ *lemma* norm_num.int_div_helper
- \+ *lemma* norm_num.nat_div_helper

Modified tests/norm_num.lean




## [2017-12-04 21:23:11-05:00](https://github.com/leanprover-community/mathlib/commit/b1981c9)
chore(theories/number_theory/dioph): cleanup
#### Estimated changes
Modified data/int/basic.lean


Modified theories/number_theory/dioph.lean
- \+/\- *theorem* dioph.abs_poly_dioph
- \+/\- *theorem* dioph.of_no_dummies
- \+/\- *theorem* poly.add_eval
- \- *theorem* poly.add_val
- \+/\- *theorem* poly.const_eval
- \- *def* poly.eval
- \+/\- *def* poly.ext
- \+/\- *def* poly.isp
- \+/\- *theorem* poly.mul_eval
- \- *theorem* poly.mul_val
- \+/\- *theorem* poly.neg_eval
- \- *theorem* poly.neg_val
- \+/\- *theorem* poly.one_eval
- \- *theorem* poly.one_val
- \+/\- *theorem* poly.proj_eval
- \+/\- *theorem* poly.remap_eval
- \+/\- *theorem* poly.sub_eval
- \- *theorem* poly.sub_val
- \+/\- *def* poly.subst
- \+/\- *theorem* poly.subst_eval
- \+/\- *theorem* poly.sumsq_eq_zero
- \+/\- *theorem* poly.sumsq_nonneg
- \+/\- *theorem* poly.zero_eval
- \- *theorem* poly.zero_val
- \- *inductive* vector2



## [2017-12-01 08:02:15-05:00](https://github.com/leanprover-community/mathlib/commit/7191e39)
feat(theories/number_theory/dioph): Pell equation, diophantine equations
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* bit0_zero
- \+ *lemma* bit1_zero

Modified data/int/basic.lean
- \+ *theorem* int.coe_nat_mod
- \+ *theorem* int.mod_add_cancel_left
- \+ *theorem* int.mod_add_cancel_right
- \+ *theorem* int.mod_eq_mod_iff_mod_sub_eq_zero
- \- *theorem* int.mod_eq_mod_of_add_mod_eq_add_mod_left
- \- *theorem* int.mod_eq_mod_of_add_mod_eq_add_mod_right
- \+ *theorem* int.mod_sub_cancel_right
- \+ *theorem* int.to_nat_coe_nat
- \+ *theorem* int.to_nat_of_nonneg

Modified data/nat/gcd.lean
- \+/\- *theorem* nat.coprime.gcd_eq_one
- \+/\- *theorem* nat.coprime.symm
- \+ *def* nat.gcd_a
- \+ *def* nat.gcd_b
- \+ *theorem* nat.gcd_eq_gcd_ab
- \+ *def* nat.xgcd
- \+ *def* nat.xgcd_aux
- \+ *theorem* nat.xgcd_aux_P
- \+ *theorem* nat.xgcd_aux_fst
- \+ *theorem* nat.xgcd_aux_rec
- \+ *theorem* nat.xgcd_aux_val
- \+ *theorem* nat.xgcd_val
- \+ *theorem* nat.xgcd_zero_left

Added data/nat/modeq.lean
- \+ *theorem* nat.modeq.chinese_remainder
- \+ *theorem* nat.modeq.dvd_of_modeq
- \+ *theorem* nat.modeq.modeq_add
- \+ *theorem* nat.modeq.modeq_add_cancel_left
- \+ *theorem* nat.modeq.modeq_add_cancel_right
- \+ *theorem* nat.modeq.modeq_iff_dvd
- \+ *theorem* nat.modeq.modeq_mul
- \+ *theorem* nat.modeq.modeq_mul_left'
- \+ *theorem* nat.modeq.modeq_mul_left
- \+ *theorem* nat.modeq.modeq_mul_right'
- \+ *theorem* nat.modeq.modeq_mul_right
- \+ *theorem* nat.modeq.modeq_of_dvd
- \+ *theorem* nat.modeq.modeq_of_dvd_of_modeq
- \+ *theorem* nat.modeq.modeq_zero_iff
- \+ *def* nat.modeq

Modified data/pfun.lean
- \+/\- *def* pfun.graph
- \+ *theorem* pfun.lift_graph

Added theories/number_theory/dioph.lean
- \+ *def* arity
- \+ *def* curry
- \+ *theorem* dioph.abs_poly_dioph
- \+ *theorem* dioph.add_dioph
- \+ *theorem* dioph.and_dioph
- \+ *theorem* dioph.const_dioph
- \+ *theorem* dioph.dioph_comp2
- \+ *theorem* dioph.dioph_comp
- \+ *def* dioph.dioph_fn
- \+ *theorem* dioph.dioph_fn_comp1
- \+ *theorem* dioph.dioph_fn_comp2
- \+ *theorem* dioph.dioph_fn_comp
- \+ *theorem* dioph.dioph_fn_compn
- \+ *theorem* dioph.dioph_fn_iff_pfun
- \+ *theorem* dioph.dioph_fn_vec
- \+ *theorem* dioph.dioph_fn_vec_comp1
- \+ *theorem* dioph.dioph_list_all
- \+ *def* dioph.dioph_pfun
- \+ *theorem* dioph.dioph_pfun_comp1
- \+ *theorem* dioph.dioph_pfun_vec
- \+ *theorem* dioph.div_dioph
- \+ *theorem* dioph.dom_dioph
- \+ *theorem* dioph.dvd_dioph
- \+ *theorem* dioph.eq_dioph
- \+ *theorem* dioph.ex1_dioph
- \+ *theorem* dioph.ex_dioph
- \+ *theorem* dioph.ext
- \+ *theorem* dioph.inject_dummies
- \+ *lemma* dioph.inject_dummies_lem
- \+ *theorem* dioph.le_dioph
- \+ *theorem* dioph.lt_dioph
- \+ *theorem* dioph.mod_dioph
- \+ *theorem* dioph.modeq_dioph
- \+ *theorem* dioph.mul_dioph
- \+ *theorem* dioph.ne_dioph
- \+ *theorem* dioph.of_no_dummies
- \+ *theorem* dioph.or_dioph
- \+ *theorem* dioph.pell_dioph
- \+ *theorem* dioph.pow_dioph
- \+ *theorem* dioph.proj_dioph
- \+ *def* dioph.proj_dioph_of_nat
- \+ *theorem* dioph.reindex_dioph
- \+ *theorem* dioph.reindex_dioph_fn
- \+ *theorem* dioph.sub_dioph
- \+ *theorem* dioph.vec_ex1_dioph
- \+ *theorem* dioph.xn_dioph
- \+ *def* dioph
- \+ *theorem* exists_vector_succ
- \+ *theorem* exists_vector_zero
- \+ *def* fin2.add
- \+ *def* fin2.elim0
- \+ *def* fin2.insert_perm
- \+ *def* fin2.left
- \+ *def* fin2.of_nat'
- \+ *def* fin2.opt_of_nat
- \+ *def* fin2.remap_left
- \+ *inductive* fin2
- \+ *lemma* int.eq_nat_abs_iff_mul
- \+ *inductive* is_poly
- \+ *theorem* list_all.imp
- \+ *def* list_all
- \+ *theorem* list_all_congr
- \+ *theorem* list_all_cons
- \+ *theorem* list_all_iff_forall
- \+ *theorem* list_all_map
- \+ *def* option.cons
- \+ *def* option.cons_head_tail
- \+ *def* poly.add
- \+ *theorem* poly.add_eval
- \+ *theorem* poly.add_val
- \+ *def* poly.const
- \+ *theorem* poly.const_eval
- \+ *def* poly.eval
- \+ *def* poly.ext
- \+ *def* poly.induction
- \+ *def* poly.isp
- \+ *def* poly.mul
- \+ *theorem* poly.mul_eval
- \+ *theorem* poly.mul_val
- \+ *def* poly.neg
- \+ *theorem* poly.neg_eval
- \+ *theorem* poly.neg_val
- \+ *def* poly.one
- \+ *theorem* poly.one_eval
- \+ *theorem* poly.one_val
- \+ *def* poly.pow
- \+ *def* poly.proj
- \+ *theorem* poly.proj_eval
- \+ *def* poly.remap
- \+ *theorem* poly.remap_eval
- \+ *def* poly.sub
- \+ *theorem* poly.sub_eval
- \+ *theorem* poly.sub_val
- \+ *def* poly.subst
- \+ *theorem* poly.subst_eval
- \+ *def* poly.sumsq
- \+ *theorem* poly.sumsq_eq_zero
- \+ *theorem* poly.sumsq_nonneg
- \+ *def* poly.zero
- \+ *theorem* poly.zero_eval
- \+ *theorem* poly.zero_val
- \+ *def* poly
- \+ *def* sum.join
- \+ *def* uncurry
- \+ *inductive* vector2
- \+ *def* vector3.append
- \+ *def* vector3.append_add
- \+ *def* vector3.append_cons
- \+ *theorem* vector3.append_insert
- \+ *def* vector3.append_left
- \+ *def* vector3.append_nil
- \+ *def* vector3.cons
- \+ *def* vector3.cons_elim
- \+ *theorem* vector3.cons_elim_cons
- \+ *def* vector3.cons_fs
- \+ *def* vector3.cons_fz
- \+ *theorem* vector3.cons_head_tail
- \+ *theorem* vector3.eq_nil
- \+ *def* vector3.head
- \+ *def* vector3.insert
- \+ *def* vector3.insert_fs
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

Added theories/number_theory/pell.lean
- \+ *theorem* pell.asq_pos
- \+ *def* pell.az
- \+ *theorem* pell.d_pos
- \+ *theorem* pell.dvd_of_ysq_dvd
- \+ *theorem* pell.dz_val
- \+ *theorem* pell.eq_of_xn_modeq'
- \+ *theorem* pell.eq_of_xn_modeq
- \+ *theorem* pell.eq_of_xn_modeq_le
- \+ *theorem* pell.eq_of_xn_modeq_lem1
- \+ *theorem* pell.eq_of_xn_modeq_lem2
- \+ *theorem* pell.eq_of_xn_modeq_lem3
- \+ *theorem* pell.eq_pell
- \+ *lemma* pell.eq_pell_lem
- \+ *theorem* pell.eq_pell_zd
- \+ *theorem* pell.eq_pow_of_pell
- \+ *lemma* pell.eq_pow_of_pell_lem
- \+ *def* pell.is_pell
- \+ *def* pell.is_pell_conj
- \+ *def* pell.is_pell_mul
- \+ *def* pell.is_pell_nat
- \+ *def* pell.is_pell_norm
- \+ *def* pell.is_pell_one
- \+ *def* pell.is_pell_pell_zd
- \+ *theorem* pell.matiyasevic
- \+ *theorem* pell.modeq_of_xn_modeq
- \+ *def* pell.n_lt_a_pow
- \+ *theorem* pell.n_lt_xn
- \+ *def* pell.pell
- \+ *theorem* pell.pell_eq
- \+ *theorem* pell.pell_eqz
- \+ *theorem* pell.pell_val
- \+ *def* pell.pell_zd
- \+ *theorem* pell.pell_zd_add
- \+ *theorem* pell.pell_zd_im
- \+ *theorem* pell.pell_zd_re
- \+ *theorem* pell.pell_zd_sub
- \+ *theorem* pell.pell_zd_succ
- \+ *theorem* pell.pell_zd_succ_succ
- \+ *theorem* pell.x_increasing
- \+ *theorem* pell.x_pos
- \+ *theorem* pell.x_sub_y_dvd_pow
- \+ *lemma* pell.x_sub_y_dvd_pow_lem
- \+ *def* pell.xn
- \+ *theorem* pell.xn_add
- \+ *def* pell.xn_ge_a_pow
- \+ *theorem* pell.xn_modeq_x2n_add
- \+ *theorem* pell.xn_modeq_x2n_add_lem
- \+ *theorem* pell.xn_modeq_x2n_sub
- \+ *lemma* pell.xn_modeq_x2n_sub_lem
- \+ *theorem* pell.xn_modeq_x4n_add
- \+ *theorem* pell.xn_modeq_x4n_sub
- \+ *theorem* pell.xn_one
- \+ *theorem* pell.xn_succ
- \+ *theorem* pell.xn_succ_succ
- \+ *theorem* pell.xn_zero
- \+ *theorem* pell.xy_coprime
- \+ *theorem* pell.xy_modeq_of_modeq
- \+ *theorem* pell.xy_modeq_yn
- \+ *theorem* pell.xy_succ_succ
- \+ *def* pell.xz
- \+ *theorem* pell.xz_sub
- \+ *theorem* pell.xz_succ
- \+ *theorem* pell.xz_succ_succ
- \+ *theorem* pell.y_dvd_iff
- \+ *theorem* pell.y_increasing
- \+ *theorem* pell.y_mul_dvd
- \+ *def* pell.yn
- \+ *theorem* pell.yn_add
- \+ *theorem* pell.yn_ge_n
- \+ *theorem* pell.yn_modeq_a_sub_one
- \+ *theorem* pell.yn_modeq_two
- \+ *theorem* pell.yn_one
- \+ *theorem* pell.yn_succ
- \+ *theorem* pell.yn_succ_succ
- \+ *theorem* pell.yn_zero
- \+ *theorem* pell.ysq_dvd_yy
- \+ *def* pell.yz
- \+ *theorem* pell.yz_sub
- \+ *theorem* pell.yz_succ
- \+ *theorem* pell.yz_succ_succ
- \+ *def* zsqrtd.add
- \+ *theorem* zsqrtd.add_def
- \+ *theorem* zsqrtd.add_im
- \+ *theorem* zsqrtd.add_re
- \+ *theorem* zsqrtd.bit0_im
- \+ *theorem* zsqrtd.bit0_re
- \+ *theorem* zsqrtd.bit1_im
- \+ *theorem* zsqrtd.bit1_re
- \+ *theorem* zsqrtd.coe_int_im
- \+ *theorem* zsqrtd.coe_int_re
- \+ *theorem* zsqrtd.coe_int_val
- \+ *theorem* zsqrtd.coe_nat_im
- \+ *theorem* zsqrtd.coe_nat_re
- \+ *theorem* zsqrtd.coe_nat_val
- \+ *def* zsqrtd.conj
- \+ *theorem* zsqrtd.conj_im
- \+ *theorem* zsqrtd.conj_mul
- \+ *theorem* zsqrtd.conj_re
- \+ *theorem* zsqrtd.d_pos
- \+ *theorem* zsqrtd.decompose
- \+ *theorem* zsqrtd.divides_sq_eq_zero
- \+ *theorem* zsqrtd.divides_sq_eq_zero_z
- \+ *theorem* zsqrtd.ext
- \+ *theorem* zsqrtd.le_antisymm
- \+ *theorem* zsqrtd.le_arch
- \+ *theorem* zsqrtd.le_of_le_le
- \+ *theorem* zsqrtd.le_refl
- \+ *def* zsqrtd.mul
- \+ *theorem* zsqrtd.mul_conj
- \+ *theorem* zsqrtd.mul_im
- \+ *theorem* zsqrtd.mul_re
- \+ *theorem* zsqrtd.muld_val
- \+ *def* zsqrtd.neg
- \+ *theorem* zsqrtd.neg_im
- \+ *theorem* zsqrtd.neg_re
- \+ *def* zsqrtd.nonneg
- \+ *theorem* zsqrtd.nonneg_add
- \+ *lemma* zsqrtd.nonneg_add_lem
- \+ *theorem* zsqrtd.nonneg_antisymm
- \+ *theorem* zsqrtd.nonneg_cases
- \+ *theorem* zsqrtd.nonneg_iff_zero_le
- \+ *theorem* zsqrtd.nonneg_mul
- \+ *theorem* zsqrtd.nonneg_mul_lem
- \+ *theorem* zsqrtd.nonneg_muld
- \+ *theorem* zsqrtd.nonneg_smul
- \+ *def* zsqrtd.nonnegg
- \+ *def* zsqrtd.nonnegg_cases_left
- \+ *def* zsqrtd.nonnegg_cases_right
- \+ *def* zsqrtd.nonnegg_comm
- \+ *def* zsqrtd.nonnegg_neg_pos
- \+ *def* zsqrtd.nonnegg_pos_neg
- \+ *theorem* zsqrtd.not_divides_square
- \+ *theorem* zsqrtd.not_sq_le_succ
- \+ *def* zsqrtd.of_int
- \+ *theorem* zsqrtd.of_int_eq_coe
- \+ *theorem* zsqrtd.of_int_im
- \+ *theorem* zsqrtd.of_int_re
- \+ *def* zsqrtd.one
- \+ *theorem* zsqrtd.one_im
- \+ *theorem* zsqrtd.one_re
- \+ *theorem* zsqrtd.smul_val
- \+ *theorem* zsqrtd.smuld_val
- \+ *def* zsqrtd.sq_le
- \+ *theorem* zsqrtd.sq_le_add
- \+ *theorem* zsqrtd.sq_le_add_mixed
- \+ *theorem* zsqrtd.sq_le_cancel
- \+ *theorem* zsqrtd.sq_le_mul
- \+ *theorem* zsqrtd.sq_le_of_le
- \+ *theorem* zsqrtd.sq_le_smul
- \+ *def* zsqrtd.sqrtd
- \+ *theorem* zsqrtd.sqrtd_im
- \+ *theorem* zsqrtd.sqrtd_re
- \+ *def* zsqrtd.zero
- \+ *theorem* zsqrtd.zero_im
- \+ *theorem* zsqrtd.zero_re
- \+ *structure* zsqrtd

