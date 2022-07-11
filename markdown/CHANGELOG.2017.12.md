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
- \+/\- *theorem* zero_le
- \+/\- *theorem* le_zero
- \+ *theorem* add_le_add
- \+ *theorem* add_le_add_left
- \+ *theorem* add_le_add_right
- \+ *theorem* le_add_right
- \+ *theorem* le_add_left
- \+ *theorem* mul_le_mul
- \+ *theorem* mul_le_mul_left
- \+ *theorem* mul_le_mul_right
- \+ *theorem* power_le_power_left
- \+ *theorem* power_le_power_right
- \+/\- *theorem* le_iff_exists_add
- \+ *theorem* one_lt_omega
- \+ *theorem* omega_le
- \+ *theorem* add_lt_omega
- \+ *theorem* mul_lt_omega
- \- *theorem* add_mono
- \- *theorem* mul_mono
- \- *theorem* power_mono_left
- \- *theorem* power_mono_right

Modified data/equiv.lean


Modified data/ordinal.lean
- \+ *theorem* succ_eq_add_one
- \+ *theorem* succ_pos
- \+/\- *theorem* succ_ne_zero
- \+/\- *theorem* succ_le
- \+ *theorem* one_le_iff_pos
- \+ *theorem* one_le_iff_ne_zero
- \+/\- *theorem* add_le_add_left
- \+/\- *theorem* le_add_right
- \+/\- *theorem* add_le_add_iff_left
- \+ *theorem* add_left_cancel
- \+ *theorem* zero_lt_one
- \+ *theorem* is_limit.pos
- \+ *theorem* is_limit.one_lt
- \+ *theorem* is_limit.nat_lt
- \+ *theorem* is_normal.limit_lt
- \+ *theorem* is_normal.lt_iff
- \+ *theorem* is_normal.le_iff
- \+ *theorem* is_normal.inj
- \+ *theorem* is_normal.le_self
- \+ *theorem* is_normal.le_set
- \+ *theorem* is_normal.le_set'
- \+ *theorem* is_normal.refl
- \+ *theorem* is_normal.trans
- \+ *theorem* is_normal.is_limit
- \+/\- *theorem* add_le_of_limit
- \+ *theorem* add_is_normal
- \+/\- *theorem* add_is_limit
- \+ *theorem* omin_mem
- \+ *theorem* le_omin
- \+ *theorem* omin_le
- \+ *theorem* sub_eq_zero_iff_le
- \+/\- *theorem* one_add_omega
- \+/\- *theorem* one_add_of_omega_le
- \+ *theorem* mul_add_one
- \+/\- *theorem* mul_succ
- \+ *theorem* mul_le_mul
- \+ *theorem* mul_is_normal
- \+ *theorem* lt_mul_of_limit
- \+/\- *theorem* mul_lt_mul_iff_left
- \+/\- *theorem* mul_le_mul_iff_left
- \+/\- *theorem* mul_lt_mul_of_pos_left
- \+/\- *theorem* mul_pos
- \+ *theorem* mul_ne_zero
- \+/\- *theorem* le_of_mul_le_mul_left
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* ord_card_le
- \+/\- *theorem* le_sup
- \+ *theorem* zero_power'
- \+ *theorem* zero_power
- \+/\- *theorem* power_zero
- \+/\- *theorem* power_succ
- \+/\- *theorem* power_limit
- \+/\- *theorem* power_le_of_limit
- \+ *theorem* lt_power_of_limit
- \+ *theorem* power_one
- \+ *theorem* one_power
- \+ *theorem* power_pos
- \+ *theorem* power_ne_zero
- \+ *theorem* power_is_normal
- \+ *theorem* power_lt_power_iff_right
- \+ *theorem* power_le_power_iff_right
- \+ *theorem* power_right_inj
- \+ *theorem* power_is_limit
- \+ *theorem* power_is_limit_left
- \+ *theorem* power_le_power_right
- \+ *theorem* power_le_power_left
- \+ *theorem* le_power_self
- \+ *theorem* power_lt_power_left_of_succ
- \+ *theorem* power_add
- \+ *theorem* power_mul
- \+ *theorem* log_not_one_lt
- \+ *theorem* log_def
- \+ *theorem* log_zero
- \+ *theorem* succ_log_def
- \+ *theorem* lt_power_succ_log
- \+ *theorem* power_log_le
- \+ *theorem* le_log
- \+ *theorem* log_lt
- \+ *theorem* log_le_log
- \+ *theorem* log_le_self
- \+ *theorem* nat_cast_mul
- \+ *theorem* nat_cast_power
- \+ *theorem* nat_cast_eq_zero
- \+ *theorem* nat_cast_ne_zero
- \+ *theorem* nat_cast_sub
- \+ *theorem* nat_cast_div
- \+ *theorem* nat_cast_mod
- \+/\- *theorem* ord_omega
- \+/\- *theorem* add_one_of_omega_le
- \+/\- *theorem* lt_omega
- \+/\- *theorem* nat_lt_omega
- \+ *theorem* omega_pos
- \+ *theorem* omega_ne_zero
- \+ *theorem* one_lt_omega
- \+/\- *theorem* omega_is_limit
- \+/\- *theorem* omega_le
- \+/\- *theorem* nat_lt_limit
- \+/\- *theorem* omega_le_of_is_limit
- \+ *theorem* add_omega
- \+ *theorem* add_lt_omega
- \+ *theorem* mul_lt_omega
- \+ *theorem* add_omega_power
- \+ *theorem* add_absorp
- \+ *theorem* add_absorp_iff
- \+ *theorem* mul_omega
- \+ *theorem* mul_omega_power
- \+ *theorem* mul_omega_power_power
- \+ *theorem* CNF_aux
- \+ *theorem* CNF_rec_zero
- \+ *theorem* CNF_rec_ne_zero
- \+ *theorem* zero_CNF
- \+ *theorem* CNF_zero
- \+ *theorem* CNF_ne_zero
- \+ *theorem* one_CNF
- \+ *theorem* CNF_foldr
- \+ *theorem* CNF_pairwise_aux
- \+ *theorem* CNF_pairwise
- \+ *theorem* CNF_fst_le_log
- \+ *theorem* CNF_fst_le
- \+ *theorem* CNF_snd_lt
- \+ *theorem* CNF_sorted
- \+/\- *theorem* ord_is_limit
- \+/\- *theorem* aleph_idx.initial_seg_coe
- \+/\- *theorem* aleph_idx_lt
- \+/\- *theorem* aleph_idx_le
- \+/\- *theorem* aleph_idx.init
- \+/\- *theorem* aleph_idx.order_iso_coe
- \+/\- *theorem* aleph'.order_iso_coe
- \+/\- *theorem* aleph'_lt
- \+/\- *theorem* aleph'_le
- \+/\- *theorem* aleph'_aleph_idx
- \+/\- *theorem* aleph_idx_aleph'
- \+ *theorem* aleph'_zero
- \+/\- *theorem* aleph'_succ
- \+ *theorem* aleph'_nat
- \+ *theorem* aleph'_le_of_limit
- \+ *theorem* aleph'_omega
- \+ *theorem* aleph_lt
- \+ *theorem* aleph_le
- \+ *theorem* aleph_succ
- \+ *theorem* aleph_zero
- \+ *theorem* omega_le_aleph'
- \+ *theorem* omega_le_aleph
- \+ *theorem* aleph_is_limit
- \+ *theorem* exists_aleph
- \+ *theorem* aleph'_is_normal
- \+ *theorem* aleph_is_normal
- \+ *theorem* mul_eq_self
- \+ *theorem* mul_eq_max
- \+ *theorem* add_eq_self
- \+ *theorem* add_eq_max
- \+/\- *theorem* order_iso.cof.aux
- \+/\- *theorem* order_iso.cof
- \+/\- *theorem* le_cof_type
- \+/\- *theorem* cof_type_le
- \+/\- *theorem* lt_cof_type
- \+ *theorem* cof_sup_le_lift
- \+ *theorem* cof_sup_le
- \+ *theorem* cof_bsup_le_lift
- \- *theorem* pos_of_is_limit
- \+ *def* is_normal
- \+ *def* omin
- \+ *def* log
- \+ *def* CNF
- \+/\- *def* aleph_idx.initial_seg
- \+/\- *def* aleph_idx
- \+/\- *def* aleph_idx.order_iso
- \+/\- *def* aleph'.order_iso
- \+/\- *def* aleph'
- \+/\- *def* aleph
- \+/\- *def* order.cof
- \+/\- *def* cof

Modified data/prod.lean


Modified data/quot.lean


Modified data/set/basic.lean
- \- *lemma* mem_of_mem_of_subset
- \- *lemma* set_of_mem_eq
- \- *lemma* not_subset
- \- *lemma* not_not_mem
- \- *lemma* ne_empty_iff_exists_mem
- \- *lemma* not_eq_empty_iff_exists
- \- *lemma* insert_subset
- \- *lemma* insert_subset_insert
- \- *lemma* insert_union
- \- *lemma* union_insert
- \- *lemma* set_compr_eq_eq_singleton
- \- *lemma* compl_subset_of_compl_subset
- \- *lemma* diff_subset_diff
- \- *lemma* diff_right_antimono
- \- *lemma* diff_neq_empty
- \- *lemma* diff_empty
- \- *lemma* diff_diff
- \- *lemma* mem_image_of_injective
- \- *lemma* image_inter_on
- \- *lemma* image_inter
- \- *lemma* image_singleton
- \- *lemma* image_preimage_eq_inter_rng
- \- *lemma* compl_image_set_of
- \- *lemma* quot_mk_image_univ_eq
- \- *lemma* univ_eq_true_false
- \- *lemma* mem_range
- \- *lemma* mem_range_self
- \- *lemma* forall_range_iff
- \- *lemma* range_iff_surjective
- \- *lemma* range_id
- \- *lemma* range_eq_image
- \- *lemma* range_compose
- \- *lemma* mem_prod_eq
- \- *lemma* mem_prod
- \- *lemma* prod_empty
- \- *lemma* empty_prod
- \- *lemma* insert_prod
- \- *lemma* prod_insert
- \- *lemma* prod_mono
- \- *lemma* prod_inter_prod
- \- *lemma* image_swap_prod
- \- *lemma* prod_image_image_eq
- \- *lemma* prod_singleton_singleton
- \- *lemma* prod_neq_empty_iff
- \- *lemma* prod_mk_mem_set_prod_eq
- \- *lemma* univ_prod_univ
- \+ *theorem* mem_of_mem_of_subset
- \+ *theorem* set_of_mem_eq
- \+ *theorem* not_subset
- \+ *theorem* not_not_mem
- \+ *theorem* ne_empty_iff_exists_mem
- \+ *theorem* not_eq_empty_iff_exists
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_assoc
- \+/\- *theorem* union_left_comm
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_left_comm
- \+ *theorem* insert_subset
- \+ *theorem* insert_subset_insert
- \+ *theorem* insert_union
- \+ *theorem* union_insert
- \+ *theorem* set_compr_eq_eq_singleton
- \+ *theorem* union_singleton
- \+ *theorem* singleton_inter_eq_empty
- \+ *theorem* inter_singleton_eq_empty
- \+ *theorem* compl_subset_of_compl_subset
- \+ *theorem* diff_subset_diff
- \+ *theorem* diff_right_antimono
- \+ *theorem* diff_neq_empty
- \+ *theorem* diff_empty
- \+ *theorem* diff_diff
- \+ *theorem* mem_image_of_injective
- \+ *theorem* image_inter_on
- \+ *theorem* image_inter
- \+ *theorem* image_singleton
- \+ *theorem* image_preimage_eq_inter_rng
- \+ *theorem* compl_image_set_of
- \+ *theorem* quot_mk_image_univ_eq
- \+ *theorem* univ_eq_true_false
- \+ *theorem* mem_range
- \+ *theorem* mem_range_self
- \+ *theorem* forall_range_iff
- \+ *theorem* range_iff_surjective
- \+ *theorem* range_id
- \+ *theorem* range_eq_image
- \+ *theorem* range_compose
- \+ *theorem* mem_prod_eq
- \+ *theorem* mem_prod
- \+ *theorem* prod_empty
- \+ *theorem* empty_prod
- \+ *theorem* insert_prod
- \+ *theorem* prod_insert
- \+ *theorem* prod_mono
- \+ *theorem* prod_inter_prod
- \+ *theorem* image_swap_prod
- \+ *theorem* prod_image_image_eq
- \+ *theorem* prod_singleton_singleton
- \+ *theorem* prod_neq_empty_iff
- \+ *theorem* prod_mk_mem_set_prod_eq
- \+ *theorem* univ_prod_univ
- \- *theorem* union_insert_eq

Modified data/set/lattice.lean


Modified logic/embedding.lean
- \+ *def* embedding_of_subset

Modified order/basic.lean
- \+ *def* partial_order_of_SO
- \+ *def* linear_order_of_STO'
- \+ *def* decidable_linear_order_of_STO'



## [2017-12-23 10:06:18-05:00](https://github.com/leanprover-community/mathlib/commit/0abe086)
feat(data/ordinal): mul, div, mod, dvd, sub, power
#### Estimated changes
Modified algebra/linear_algebra/basic.lean


Modified data/cardinal.lean
- \+ *theorem* le_zero
- \+ *theorem* omega_ne_zero

Modified data/equiv.lean
- \+ *theorem* prod_assoc_apply
- \+ *theorem* prod_unit_apply
- \+ *theorem* unit_prod_apply
- \+ *theorem* sum_prod_distrib_apply_left
- \+ *theorem* sum_prod_distrib_apply_right
- \+ *theorem* prod_sum_distrib_apply_left
- \+ *theorem* prod_sum_distrib_apply_right

Modified data/ordinal.lean
- \+ *theorem* typein_apply
- \+ *theorem* zero_eq_type_empty
- \+ *theorem* le_zero
- \+ *theorem* pos_iff_ne_zero
- \+ *theorem* one_eq_type_unit
- \+ *theorem* type_add
- \+ *theorem* card_succ
- \+ *theorem* zero_eq_lift_type_empty
- \+ *theorem* one_eq_lift_type_unit
- \+ *theorem* lt_succ
- \+ *theorem* type_eq_zero_iff_empty
- \+ *theorem* not_succ_is_limit
- \+ *theorem* not_succ_of_is_limit
- \+ *theorem* succ_lt_of_is_limit
- \+ *theorem* le_succ_of_is_limit
- \+ *theorem* limit_le
- \+ *theorem* add_le_of_limit
- \+/\- *theorem* add_is_limit
- \+ *theorem* limit_rec_on_zero
- \+ *theorem* limit_rec_on_succ
- \+ *theorem* limit_rec_on_limit
- \+ *theorem* sub_le_self
- \+ *theorem* add_sub_cancel_of_le
- \+ *theorem* sub_zero
- \+ *theorem* zero_sub
- \+ *theorem* sub_self
- \+ *theorem* type_mul
- \+/\- *theorem* lift_mul
- \+ *theorem* card_mul
- \+ *theorem* mul_zero
- \+ *theorem* zero_mul
- \+ *theorem* mul_one
- \+ *theorem* one_mul
- \+ *theorem* mul_assoc
- \+ *theorem* mul_add
- \+ *theorem* mul_succ
- \+ *theorem* mul_le_mul_left
- \+ *theorem* mul_le_mul_right
- \+ *theorem* mul_lt_mul_of_pos_left
- \+ *theorem* mul_pos
- \+ *theorem* le_of_mul_le_mul_left
- \+ *theorem* mul_le_mul_iff_left
- \+ *theorem* mul_lt_mul_iff_left
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_le_of_limit
- \+ *theorem* mul_is_limit
- \+ *theorem* div_zero
- \+ *theorem* lt_mul_succ_div
- \+ *theorem* lt_mul_div_add
- \+ *theorem* div_le
- \+ *theorem* lt_div
- \+ *theorem* le_div
- \+ *theorem* div_lt
- \+ *theorem* div_le_of_le_mul
- \+ *theorem* mul_lt_of_lt_div
- \+ *theorem* zero_div
- \+ *theorem* mul_div_le
- \+ *theorem* mul_add_div
- \+ *theorem* div_eq_zero_of_lt
- \+ *theorem* mul_div_cancel
- \+ *theorem* div_one
- \+ *theorem* div_self
- \+ *theorem* dvd_def
- \+ *theorem* dvd_mul
- \+ *theorem* dvd_zero
- \+ *theorem* zero_dvd
- \+ *theorem* one_dvd
- \+ *theorem* div_mul_cancel
- \+ *theorem* mod_def
- \+ *theorem* mod_zero
- \+ *theorem* mod_eq_of_lt
- \+ *theorem* zero_mod
- \+ *theorem* div_add_mod
- \+ *theorem* mod_lt
- \+ *theorem* mod_self
- \+ *theorem* mod_one
- \+ *theorem* power_zero
- \+ *theorem* power_succ
- \+ *theorem* power_limit
- \+ *theorem* power_le_of_limit
- \+ *theorem* one_add_omega
- \+ *theorem* one_add_of_omega_le
- \+ *theorem* add_one_of_omega_le
- \+ *theorem* ord_is_limit
- \- *theorem* add_limit
- \- *theorem* sub_add_cancel_of_le
- \+ *def* div_def
- \+ *def* power

Modified data/prod.lean
- \+ *theorem* lex_def

Modified data/set/countable.lean


Modified data/set/lattice.lean


Modified data/sigma/basic.lean
- \+ *theorem* subtype.mk_eq_mk

Modified data/sum.lean
- \+ *theorem* inl_ne_inr
- \+ *theorem* inr_ne_inl

Modified order/basic.lean
- \- *def* empty_relation.is_well_order

Modified order/order_iso.lean
- \+ *theorem* nat_gt
- \+ *theorem* subrel_val
- \+ *theorem* order_embedding_apply



## [2017-12-21 06:51:34-05:00](https://github.com/leanprover-community/mathlib/commit/5f4d890)
feat(data/ordinal): omega is least limit ordinal
#### Estimated changes
Modified algebra/order.lean
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt

Modified data/cardinal.lean
- \+ *theorem* le_lift_iff
- \+ *theorem* lt_lift_iff
- \+ *theorem* lift_omega
- \+ *theorem* lt_omega_iff_fintype
- \+ *theorem* lt_omega_iff_finite

Modified data/ordinal.lean
- \+ *theorem* lift_down'
- \+/\- *theorem* lift_down
- \+ *theorem* le_lift_iff
- \+ *theorem* lt_lift_iff
- \+/\- *theorem* card_ord
- \+/\- *theorem* ord_le_ord
- \+/\- *theorem* ord_lt_ord
- \+/\- *theorem* ord_nat
- \+ *theorem* lift_ord
- \+ *theorem* nat_cast_le
- \+ *theorem* nat_cast_lt
- \+ *theorem* nat_cast_inj
- \+ *theorem* nat_le_card
- \+ *theorem* nat_lt_card
- \+ *theorem* card_lt_nat
- \+ *theorem* card_le_nat
- \+ *theorem* card_eq_nat
- \+ *theorem* type_fin
- \+ *theorem* lift_nat_cast
- \+ *theorem* lift_type_fin
- \+ *theorem* fintype_card
- \+/\- *theorem* ord_omega
- \+ *theorem* lt_omega
- \+/\- *theorem* nat_lt_omega
- \+/\- *theorem* omega_is_limit
- \+ *theorem* omega_le
- \+ *theorem* nat_lt_limit
- \+ *theorem* omega_le_of_is_limit

Modified logic/basic.lean
- \+ *theorem* false_ne_true
- \+/\- *theorem* iff_of_eq
- \- *theorem* false_neq_true

Modified logic/schroeder_bernstein.lean
- \+/\- *theorem* injective_min

Modified order/order_iso.lean
- \+ *def* fin.val.order_embedding
- \+ *def* fin_fin.order_embedding
- \+ *def* to_order_embedding



## [2017-12-20 23:25:17-05:00](https://github.com/leanprover-community/mathlib/commit/49a63b7)
refactor(data/ordinal): rearrange files, more cofinality
#### Estimated changes
Modified algebra/linear_algebra/basic.lean


Modified analysis/real.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/uniform_space.lean


Modified data/cardinal.lean
- \+ *theorem* lift_down
- \+/\- *theorem* lt_omega
- \- *theorem* to_fun_eq_coe
- \- *theorem* coe_fn_mk
- \- *theorem* inj'
- \- *theorem* refl_apply
- \- *theorem* trans_apply
- \- *theorem* schroeder_bernstein
- \- *theorem* antisymm
- \- *theorem* injective_min
- \- *theorem* total
- \- *theorem* sum_congr_apply_inl
- \- *theorem* sum_congr_apply_inr
- \- *theorem* equiv.to_embedding_coe_fn
- \- *def* prod_congr
- \- *def* sum_congr
- \- *def* arrow_congr_left
- \- *def* arrow_congr_right

Modified data/ordinal.lean
- \+ *theorem* lift_succ
- \+ *theorem* lift_card
- \+/\- *theorem* lift_down
- \+/\- *theorem* card_omega
- \+ *theorem* type_ne_zero_iff_nonempty
- \+ *theorem* lift_is_succ
- \+ *theorem* lift_pred
- \+ *theorem* lift_is_limit
- \+ *theorem* cof_eq
- \+ *theorem* ord_cof_eq
- \+/\- *theorem* cof_eq_one_iff_is_succ
- \+ *theorem* cof_add
- \+ *theorem* cof_cof
- \+ *theorem* omega_is_limit
- \+/\- *theorem* nat_lt_omega
- \+/\- *theorem* sub_add_cancel_of_le
- \+/\- *theorem* add_is_limit
- \- *theorem* well_founded.has_min
- \- *theorem* well_founded.min_mem
- \- *theorem* well_founded.not_lt_min
- \- *theorem* ord'
- \- *theorem* coe_fn_mk
- \- *theorem* coe_fn_to_embedding
- \- *theorem* eq_of_to_fun_eq
- \- *theorem* refl_apply
- \- *theorem* trans_apply
- \- *theorem* eq_preimage
- \- *theorem* of_monotone_coe
- \- *theorem* nat_lt
- \- *theorem* well_founded_iff_no_descending_seq
- \- *theorem* coe_coe_fn
- \- *theorem* coe_fn_to_equiv
- \- *theorem* coe_fn_symm_mk
- \- *theorem* apply_inverse_apply
- \- *theorem* inverse_apply_apply
- \- *theorem* of_surjective_coe
- \- *theorem* sum_lex_congr
- \- *theorem* prod_lex_congr
- \- *theorem* order_embedding.cod_restrict_apply
- \- *theorem* exists_of_cof
- \+/\- *def* omega
- \- *def* is_irrefl_of_is_asymm
- \- *def* is_irrefl.swap
- \- *def* is_trans.swap
- \- *def* is_strict_order.swap
- \- *def* is_trichotomous.swap
- \- *def* is_strict_total_order'.swap
- \- *def* is_strict_weak_order_of_is_order_connected
- \- *def* empty_relation.is_well_order
- \- *def* well_founded.min
- \- *def* order.preimage
- \- *def* rsymm
- \- *def* preimage
- \- *def* of_monotone
- \- *def* of_surjective
- \- *def* set_coe_embedding
- \- *def* subrel
- \- *def* order_embedding.cod_restrict

Modified data/set/finite.lean
- \+/\- *theorem* finite_image

Modified data/sigma/basic.lean
- \- *lemma* psigma.mk.inj_iff
- \+ *theorem* psigma.mk.inj_iff
- \+ *theorem* subtype.coe_eta
- \+ *theorem* subtype.coe_mk

Modified logic/basic.lean
- \+ *theorem* Exists.fst
- \+ *theorem* Exists.snd

Created logic/embedding.lean
- \+ *theorem* equiv.to_embedding_coe_fn
- \+ *theorem* to_fun_eq_coe
- \+ *theorem* coe_fn_mk
- \+ *theorem* inj'
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* cod_restrict_apply
- \+ *theorem* sum_congr_apply_inl
- \+ *theorem* sum_congr_apply_inr
- \+ *def* cod_restrict
- \+ *def* prod_congr
- \+ *def* sum_congr
- \+ *def* arrow_congr_left

Modified logic/function.lean
- \+/\- *lemma* surj_inv_eq
- \+/\- *theorem* injective.eq_iff
- \+/\- *theorem* injective_of_partial_inv
- \+/\- *theorem* injective_of_partial_inv_right
- \+/\- *theorem* partial_inv_of_injective
- \+/\- *def* injective.decidable_eq
- \+/\- *def* is_partial_inv

Created logic/schroeder_bernstein.lean
- \+ *theorem* schroeder_bernstein
- \+ *theorem* antisymm
- \+ *theorem* injective_min
- \+ *theorem* total

Modified order/basic.lean
- \+ *theorem* is_order_connected.neg_trans
- \+ *theorem* well_founded.has_min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min
- \+ *def* is_irrefl_of_is_asymm
- \+ *def* is_irrefl.swap
- \+ *def* is_trans.swap
- \+ *def* is_strict_order.swap
- \+ *def* is_trichotomous.swap
- \+ *def* is_strict_total_order'.swap
- \+ *def* is_strict_weak_order_of_is_order_connected
- \+ *def* empty_relation.is_well_order

Modified order/filter.lean


Created order/order_iso.lean
- \+ *theorem* ord'
- \+ *theorem* coe_fn_mk
- \+ *theorem* coe_fn_to_embedding
- \+ *theorem* eq_of_to_fun_eq
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* eq_preimage
- \+ *theorem* of_monotone_coe
- \+ *theorem* nat_lt
- \+ *theorem* well_founded_iff_no_descending_seq
- \+ *theorem* coe_coe_fn
- \+ *theorem* coe_fn_to_equiv
- \+ *theorem* coe_fn_symm_mk
- \+ *theorem* apply_inverse_apply
- \+ *theorem* inverse_apply_apply
- \+ *theorem* of_surjective_coe
- \+ *theorem* sum_lex_congr
- \+ *theorem* prod_lex_congr
- \+ *theorem* order_embedding.cod_restrict_apply
- \+ *def* order.preimage
- \+ *def* rsymm
- \+ *def* preimage
- \+ *def* of_monotone
- \+ *def* set_coe_embedding
- \+ *def* subrel
- \+ *def* order_embedding.cod_restrict



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
- \+/\- *theorem* ne_zero_iff_nonempty
- \+ *theorem* le_one_iff_subsingleton
- \+/\- *theorem* prop_eq_two
- \+ *theorem* zero_lt_one
- \+/\- *theorem* min_eq
- \+/\- *theorem* min_le
- \+/\- *theorem* le_min
- \+/\- *theorem* lift_min
- \+ *theorem* succ_zero
- \+ *theorem* nat_lt_omega
- \+ *theorem* lt_omega
- \- *theorem* nat_lt_ω
- \- *theorem* lt_ω
- \+/\- *def* min
- \+ *def* omega
- \- *def* ω

Modified data/fintype.lean
- \+ *theorem* subtype_card
- \+ *theorem* card_of_subtype

Modified data/ordinal.lean
- \+ *theorem* succ_ne_zero
- \+/\- *theorem* succ_le
- \+ *theorem* succ_nat_cast
- \+ *theorem* succ_zero
- \+ *theorem* card_omega
- \+ *theorem* nat_lt_omega
- \+ *theorem* lift_omega
- \+ *theorem* add_le_add_right
- \+/\- *theorem* le_add_left
- \+/\- *theorem* le_total
- \+ *theorem* add_lt_add_iff_left
- \+ *theorem* lt_of_add_lt_add_right
- \+ *theorem* succ_lt_succ
- \+ *theorem* succ_le_succ
- \+ *theorem* succ_inj
- \+ *theorem* card_eq_zero
- \+ *theorem* pred_succ
- \+ *theorem* pred_le_self
- \+ *theorem* pred_eq_iff_not_succ
- \+ *theorem* pred_lt_iff_is_succ
- \+ *theorem* succ_pred_iff_is_succ
- \+ *theorem* succ_lt_of_not_succ
- \+ *theorem* lt_pred
- \+ *theorem* pred_le
- \+ *theorem* pos_of_is_limit
- \+ *theorem* zero_or_succ_or_limit
- \+/\- *theorem* min_eq
- \+/\- *theorem* min_le
- \+/\- *theorem* le_min
- \+/\- *theorem* lift_min
- \+ *theorem* le_add_sub
- \+ *theorem* sub_le
- \+ *theorem* lt_sub
- \+ *theorem* add_sub_cancel
- \+ *theorem* sub_add_cancel_of_le
- \+ *theorem* add_is_limit
- \+ *theorem* ord_omega
- \+/\- *theorem* order_iso.cof.aux
- \+/\- *theorem* order_iso.cof
- \+ *theorem* le_sup
- \+ *theorem* sup_le
- \+ *theorem* bsup_le
- \+ *theorem* le_bsup
- \+ *theorem* add_limit
- \+ *theorem* le_cof_type
- \+ *theorem* cof_type_le
- \+ *theorem* lt_cof_type
- \+ *theorem* exists_of_cof
- \+ *theorem* cof_le_card
- \+ *theorem* cof_zero
- \+ *theorem* cof_eq_zero
- \+ *theorem* cof_succ
- \+ *theorem* cof_eq_one_iff_is_succ
- \- *theorem* lift_ω
- \- *theorem* ord_eq_min
- \+ *def* omega
- \+ *def* pred
- \+ *def* is_limit
- \+ *def* limit_rec_on
- \+/\- *def* min
- \+ *def* sub
- \+ *def* ord_eq_min
- \+/\- *def* order.cof
- \+ *def* sup
- \+ *def* bsup
- \+/\- *def* aleph
- \+/\- *def* cof
- \- *def* ω

Modified data/set/finite.lean
- \+ *theorem* card_fintype_of_finset
- \+ *theorem* card_fintype_of_finset'
- \+ *theorem* empty_card
- \+ *theorem* card_fintype_insert'
- \+ *theorem* card_insert
- \+ *theorem* card_singleton

Modified order/basic.lean
- \+ *lemma* le_of_forall_le_of_dense
- \+ *lemma* eq_of_le_of_forall_le_of_dense
- \+ *lemma* le_of_forall_ge_of_dense
- \+ *lemma* eq_of_le_of_forall_ge_of_dense
- \- *lemma* le_of_forall_le
- \- *lemma* eq_of_le_of_forall_le
- \- *lemma* le_of_forall_ge
- \- *lemma* eq_of_le_of_forall_ge



## [2017-12-18 08:38:41-05:00](https://github.com/leanprover-community/mathlib/commit/f6bbca7)
feat(data/ordinal): universe lifts, alephs
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *theorem* card_sigma

Modified algebra/group_power.lean
- \+ *theorem* nat.smul_eq_mul

Modified algebra/module.lean


Modified data/cardinal.lean
- \+ *theorem* mk_def
- \+ *theorem* le_mk_iff_exists_set
- \+ *theorem* lt_succ_self
- \+ *theorem* succ_le
- \+ *theorem* add_one_le_succ
- \+ *theorem* lift_mk
- \+ *theorem* lift_umax
- \+ *theorem* lift_id
- \+ *theorem* lift_lift
- \+ *theorem* lift_mk_le
- \+ *theorem* lift_mk_eq
- \+ *theorem* lift_le
- \+ *theorem* lift_inj
- \+ *theorem* lift_lt
- \+ *theorem* lift_zero
- \+ *theorem* lift_one
- \+ *theorem* lift_add
- \+ *theorem* lift_mul
- \+ *theorem* lift_power
- \+ *theorem* lift_min
- \+ *theorem* mk_fin
- \+ *theorem* lift_nat_cast
- \+ *theorem* lift_mk_fin
- \+ *theorem* fintype_card
- \+ *theorem* nat_cast_le
- \+ *theorem* nat_cast_lt
- \+ *theorem* nat_cast_inj
- \+ *theorem* nat_succ
- \+ *theorem* nat_lt_ω
- \+ *theorem* lt_ω
- \+ *def* succ
- \+ *def* lift
- \+/\- *def* ω

Modified data/finset.lean
- \+/\- *lemma* bind_mono
- \+ *theorem* card_image_of_inj_on
- \+ *theorem* card_image_of_injective
- \+ *theorem* card_product

Modified data/fintype.lean
- \+/\- *theorem* mem_univ
- \+/\- *theorem* mem_univ_val
- \+ *theorem* eq_univ_iff_forall
- \+ *theorem* of_equiv_card
- \+ *theorem* card_congr
- \+ *theorem* card_eq
- \+ *theorem* fintype.card_fin
- \+ *theorem* fintype.univ_empty
- \+ *theorem* fintype.card_empty
- \+ *theorem* fintype.univ_unit
- \+ *theorem* fintype.card_unit
- \+ *theorem* fintype.univ_bool
- \+ *theorem* fintype.card_bool
- \+ *theorem* fintype.card_sigma
- \+ *theorem* fintype.card_prod
- \+ *theorem* fintype.card_ulift
- \+ *theorem* fintype.card_sum
- \+/\- *def* of_equiv

Modified data/list/basic.lean
- \+ *theorem* length_pmap
- \+ *theorem* nth_le_index_of

Modified data/multiset.lean
- \+ *theorem* card_map
- \+ *theorem* card_join
- \+ *theorem* card_bind
- \+ *theorem* card_product
- \+ *theorem* card_sigma
- \+ *theorem* card_pmap

Modified data/ordinal.lean
- \+ *theorem* of_surjective_coe
- \+ *theorem* sum_lex_congr
- \+ *theorem* prod_lex_congr
- \+ *theorem* card_type
- \+ *theorem* lt_succ_self
- \+ *theorem* succ_le
- \+ *theorem* card_nat
- \+ *theorem* lift_umax
- \+ *theorem* lift_id
- \+ *theorem* lift_lift
- \+ *theorem* lift_type_le
- \+ *theorem* lift_type_eq
- \+ *theorem* lift_type_lt
- \+ *theorem* lift_le
- \+ *theorem* lift_inj
- \+ *theorem* lift_lt
- \+ *theorem* lift_zero
- \+ *theorem* lift_one
- \+ *theorem* lift_add
- \+ *theorem* lift_mul
- \+ *theorem* lift_ω
- \+ *theorem* type_le'
- \+ *theorem* typein.principal_seg_coe
- \+ *theorem* lift_min
- \+ *theorem* lift_down
- \+ *theorem* lift.initial_seg_coe
- \+ *theorem* lift.principal_seg_coe
- \+ *theorem* lift.principal_seg_top
- \+ *theorem* lift.principal_seg_top'
- \+ *theorem* order_iso.cof.aux
- \+ *theorem* order_iso.cof
- \+/\- *theorem* ord_eq_min
- \+ *theorem* ord_le_type
- \+/\- *theorem* ord_le
- \+ *theorem* lt_ord
- \+ *theorem* card_ord
- \+/\- *theorem* ord_le_ord
- \+ *theorem* ord_lt_ord
- \+ *theorem* ord_zero
- \+ *theorem* ord_nat
- \+ *theorem* ord.order_embedding_coe
- \+ *theorem* aleph_idx.initial_seg_coe
- \+ *theorem* aleph_idx_lt
- \+ *theorem* aleph_idx_le
- \+ *theorem* aleph_idx.init
- \+ *theorem* aleph_idx.order_iso_coe
- \+ *theorem* ord_card_le
- \+ *theorem* aleph'.order_iso_coe
- \+ *theorem* aleph'_lt
- \+ *theorem* aleph'_le
- \+ *theorem* aleph'_aleph_idx
- \+ *theorem* aleph_idx_aleph'
- \+ *theorem* aleph'_succ
- \- *theorem* of_surjective_apply
- \- *theorem* type_le_of_order_embedding
- \+ *def* lift
- \+ *def* ω
- \+ *def* typein.principal_seg
- \+ *def* lift.initial_seg
- \+ *def* lift.principal_seg
- \+ *def* order.cof
- \+ *def* ord.order_embedding
- \+ *def* aleph_idx.initial_seg
- \+ *def* aleph_idx
- \+ *def* aleph_idx.order_iso
- \+ *def* aleph'.order_iso
- \+ *def* aleph'
- \+ *def* aleph



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
- \+ *theorem* sum_congr_apply_inl
- \+ *theorem* sum_congr_apply_inr
- \+ *def* mk

Modified data/equiv.lean
- \+ *theorem* prod_congr_apply
- \+ *theorem* sum_congr_apply_inl
- \+ *theorem* sum_congr_apply_inr
- \+ *theorem* sum_assoc_apply_in1
- \+ *theorem* sum_assoc_apply_in2
- \+ *theorem* sum_assoc_apply_in3
- \+ *def* prod_unit
- \+ *def* unit_prod
- \+ *def* prod_empty
- \+ *def* empty_prod
- \+ *def* sum_empty
- \+ *def* empty_sum
- \- *def* prod_unit_right
- \- *def* prod_unit_left
- \- *def* prod_empty_right
- \- *def* prod_empty_left
- \- *def* sum_empty_right
- \- *def* sum_empty_left

Modified data/ordinal.lean
- \+ *theorem* well_founded.has_min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min
- \+ *theorem* of_monotone_coe
- \+ *theorem* le_add_apply
- \+ *theorem* collapse_F.lt
- \+ *theorem* collapse_F.not_lt
- \+ *theorem* collapse_apply
- \+ *theorem* card_le_card
- \+ *theorem* card_zero
- \+ *theorem* zero_le
- \+ *theorem* card_one
- \+ *theorem* card_add
- \+ *theorem* add_succ
- \+ *theorem* add_le_add_left
- \+ *theorem* le_add_right
- \+ *theorem* add_le_add_iff_left
- \+ *theorem* type_le_of_order_embedding
- \+ *theorem* le_add_left
- \+ *theorem* le_total
- \+ *theorem* min_eq
- \+ *theorem* min_le
- \+ *theorem* le_min
- \+ *theorem* ord_eq_min
- \+ *theorem* ord_eq
- \+ *theorem* ord_le
- \+ *theorem* ord_le_ord
- \- *theorem* of_monotone
- \+ *def* well_founded.min
- \+ *def* preimage
- \+ *def* of_monotone
- \+ *def* le_add
- \+ *def* collapse_F
- \+ *def* collapse
- \+ *def* succ
- \+ *def* min
- \+ *def* cof
- \+ *def* ord
- \- *def* sum.lex.is_well_order
- \- *def* prod.lex.is_well_order

Modified data/set/basic.lean
- \+/\- *lemma* mem_range
- \+ *lemma* mem_range_self

Modified logic/basic.lean
- \- *theorem* empty.elim
- \+ *def* empty.elim

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
- \+ *lemma* nonempty_Prop
- \+ *lemma* nonempty_sigma
- \+ *lemma* nonempty_subtype
- \+ *lemma* nonempty_prod
- \+ *lemma* nonempty_pprod
- \+ *lemma* nonempty_sum
- \+ *lemma* nonempty_psum
- \+ *lemma* nonempty_psigma
- \+ *lemma* nonempty_empty
- \+ *lemma* nonempty_ulift
- \+ *lemma* nonempty_plift
- \+ *lemma* nonempty.forall
- \+ *lemma* nonempty.exists
- \+ *lemma* classical.nonempty_pi



## [2017-12-14 12:50:11+01:00](https://github.com/leanprover-community/mathlib/commit/d27f7ac)
chore(style.md): rename and some cleanup
#### Estimated changes
Renamed library_style.md to style.md




## [2017-12-14 12:42:51+01:00](https://github.com/leanprover-community/mathlib/commit/f8476fd)
feat(library_style): resurrecting Jeremy's library_style.org as md file
#### Estimated changes
Created library_style.md
- \+ *theorem* two_step_induction_on
- \+ *theorem* nat_case
- \+ *theorem* nat_discriminate
- \+ *theorem* mem_split
- \+ *theorem* add_right_inj
- \+ *theorem* reverse_reverse



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
- \+/\- *theorem* image_apply
- \+/\- *theorem* range_apply

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
- \- *lemma* smul_apply
- \- *lemma* sum_smul_index

Modified algebra/linear_algebra/multivariate_polynomial.lean


Modified data/finsupp.lean
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* prod_zero_index
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+ *lemma* smul_apply
- \+ *lemma* sum_smul_index
- \+/\- *def* sum
- \+/\- *def* prod
- \+ *def* to_has_scalar
- \+ *def* to_module



## [2017-12-13 16:52:33+01:00](https://github.com/leanprover-community/mathlib/commit/b29ab1b)
feat(data/finsupp): add support_neg
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* support_neg



## [2017-12-13 13:09:54+01:00](https://github.com/leanprover-community/mathlib/commit/a2d6148)
feat(algebra/linear_algebra): add multivariate polynomials
#### Estimated changes
Created algebra/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* sup_empty
- \+ *lemma* sup_insert
- \+ *lemma* sup_singleton
- \+ *lemma* sup_union
- \+ *lemma* sup_mono_fun
- \+ *lemma* le_sup
- \+ *lemma* sup_le
- \+ *lemma* sup_mono
- \+ *lemma* finset.bind_singleton2
- \+ *lemma* finsupp.single_induction_on
- \+ *lemma* C_0
- \+ *lemma* C_1
- \+ *lemma* C_mul_monomial
- \+ *lemma* X_pow_eq_single
- \+ *lemma* monomial_add_single
- \+ *lemma* monomial_single_add
- \+ *lemma* monomial_eq
- \+ *lemma* induction_on
- \+ *lemma* eval_zero
- \+ *lemma* eval_add
- \+ *lemma* eval_monomial
- \+ *lemma* eval_C
- \+ *lemma* eval_X
- \+ *lemma* eval_mul_monomial
- \+ *lemma* eval_mul
- \+ *lemma* vars_0
- \+ *lemma* vars_monomial
- \+ *lemma* vars_C
- \+ *lemma* vars_X
- \+ *def* sup
- \+ *def* mv_polynomial
- \+ *def* monomial
- \+ *def* C
- \+ *def* X
- \+ *def* eval
- \+ *def* vars
- \+ *def* degree_of
- \+ *def* total_degree



## [2017-12-13 13:09:17+01:00](https://github.com/leanprover-community/mathlib/commit/8369c7d)
feat(data/finsupp): big product over finsupp (big sum is now derived from it)
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* prod_map_range_index
- \+ *lemma* prod_zero_index
- \+ *lemma* prod_single_index
- \+ *lemma* prod_neg_index
- \+ *lemma* prod_add_index
- \+ *lemma* prod_finset_sum_index
- \+ *lemma* prod_sum_index
- \+ *lemma* prod_map_domain_index
- \+ *lemma* prod_comap_domain_index
- \+ *lemma* prod_subtype_domain_index
- \- *lemma* sum_map_range_index
- \- *lemma* sum_zero_index
- \- *lemma* sum_single_index
- \- *lemma* sum_neg_index
- \- *lemma* sum_add_index
- \- *lemma* sum_finset_sum_index
- \- *lemma* sum_sum_index
- \- *lemma* sum_map_domain_index
- \- *lemma* sum_comap_domain_index
- \- *lemma* sum_subtype_domain_index
- \+ *def* prod



## [2017-12-13 12:21:45+01:00](https://github.com/leanprover-community/mathlib/commit/421c332)
fix(algebra/big_operators): congruence rules need to provide equations for all rewritable positions
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_congr

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
- \+ *theorem* coe_fn_mk

Modified data/hash_map.lean


Modified data/list/basic.lean


Modified data/ordinal.lean
- \+ *theorem* chain_ub
- \+ *theorem* well_ordering_thm
- \+ *def* empty_relation.is_well_order
- \+ *def* sum.lex.is_well_order
- \+ *def* prod.lex.is_well_order

Modified data/set/basic.lean
- \+ *theorem* set_of_subset_set_of

Modified data/sigma/basic.lean
- \+ *lemma* psigma.mk.inj_iff
- \- *lemma* sigma.mk_eq_mk_iff
- \- *lemma* psigma.mk_eq_mk_iff
- \+ *theorem* sigma.mk.inj_iff
- \+ *theorem* sigma.forall
- \+ *theorem* sigma.exists
- \+ *theorem* subtype.forall
- \+ *theorem* subtype.exists

Created data/sum.lean
- \+ *lemma* swap_swap
- \+ *lemma* swap_swap_eq
- \+ *lemma* swap_left_inverse
- \+ *lemma* swap_right_inverse
- \+ *theorem* sum.forall
- \+ *theorem* sum.exists
- \+ *theorem* inl.inj_iff
- \+ *theorem* inr.inj_iff
- \+ *def* swap

Modified logic/basic.lean
- \- *theorem* eq_iff_le_and_le
- \- *theorem* set_of_subset_set_of
- \- *theorem* sigma.mk.inj_iff
- \- *theorem* sigma.forall
- \- *theorem* sigma.exists
- \- *theorem* subtype.forall
- \- *theorem* subtype.exists

Modified order/filter.lean


Modified order/zorn.lean
- \+ *theorem* chain.total_of_refl
- \+ *theorem* chain.directed
- \+/\- *theorem* chain.total



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


Modified data/ordinal.lean




## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/ee7ede9)
feat(algebra/linear_algebra): proof first and second isomorphism laws
#### Estimated changes
Modified algebra/linear_algebra/linear_map_module.lean
- \+ *lemma* some_spec2
- \+ *lemma* is_submodule.add_left_iff
- \+ *lemma* is_submodule.neg_iff
- \+ *def* quot_ker_equiv_im
- \+ *def* union_quotient_equiv_quotient_inter

Modified algebra/linear_algebra/quotient_module.lean
- \+ *lemma* quotient_rel_eq
- \+ *lemma* quotient.lift_mk

Modified algebra/linear_algebra/subtype_module.lean
- \+/\- *lemma* sub_val
- \+/\- *lemma* is_linear_map_subtype_mk



## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/01c3b8f)
feature(algebra/linear_algebra): define linear equivalence
#### Estimated changes
Modified algebra/linear_algebra/basic.lean
- \+ *lemma* set.diff_self
- \+ *lemma* linear_inv
- \+ *lemma* mem_span_insert
- \+ *lemma* linear_independent_singleton
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* equiv_of_is_basis



## [2017-12-11 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/85a1667)
refactor(data/equiv): state refl, symm, and trans rules for equiv using projection. This gives more powerful rfl rules
#### Estimated changes
Modified data/equiv.lean
- \+ *theorem* left_inverse.comp
- \+ *theorem* right_inverse.comp



## [2017-12-11 05:07:46-05:00](https://github.com/leanprover-community/mathlib/commit/03074f1)
feat(data/ordinal): more ordinals
#### Estimated changes
Modified data/bool.lean


Modified data/ordinal.lean
- \+ *theorem* order_embedding.cod_restrict_apply
- \+ *theorem* coe_coe_fn
- \+ *theorem* cod_restrict_apply
- \+ *theorem* lt_top
- \+ *theorem* lt_le_top
- \+ *theorem* trans_top
- \+ *theorem* equiv_lt_top
- \+ *theorem* top_eq
- \+ *theorem* of_element_apply
- \+ *theorem* of_element_top
- \+ *theorem* cod_restrict_top
- \+ *theorem* initial_seg.lt_or_eq_apply_left
- \+ *theorem* initial_seg.lt_or_eq_apply_right
- \+ *theorem* initial_seg.le_lt_apply
- \+ *theorem* type_def
- \+ *theorem* type_def'
- \+ *theorem* type_eq
- \+ *theorem* induction_on
- \+ *theorem* type_le
- \+ *theorem* type_lt
- \+ *theorem* typein_lt_type
- \+ *theorem* typein_top
- \+ *theorem* typein_lt_typein
- \+ *theorem* typein_surj
- \+ *theorem* typein_inj
- \+ *theorem* enum_type
- \+ *theorem* enum_typein
- \+ *theorem* typein_enum
- \+ *theorem* enum_lt
- \+ *theorem* wf
- \- *theorem* le_lt_apply
- \+/\- *def* set_coe_embedding
- \+ *def* subrel
- \+ *def* order_embedding.cod_restrict
- \+ *def* cod_restrict
- \+ *def* of_element
- \+ *def* initial_seg.lt_or_eq
- \+ *def* initial_seg.le_lt
- \+ *def* type
- \+ *def* typein
- \+ *def* enum
- \- *def* le_lt
- \- *def* le



## [2017-12-10 08:36:32-05:00](https://github.com/leanprover-community/mathlib/commit/a758ffb)
feat(data/ordinal): ordinal numbers
#### Estimated changes
Modified data/cardinal.lean
- \- *lemma* equiv.of_bijective
- \- *lemma* schroeder_bernstein
- \- *lemma* antisymm
- \- *lemma* total
- \- *lemma* power_zero
- \- *lemma* one_power
- \- *lemma* prop_eq_two
- \- *lemma* zero_power
- \- *lemma* mul_power
- \- *lemma* power_sum
- \- *lemma* power_mul
- \- *lemma* zero_le
- \- *lemma* add_mono
- \- *lemma* mul_mono
- \- *lemma* power_mono_left
- \- *lemma* power_mono_right
- \- *lemma* le_iff_exists_add
- \+ *theorem* to_fun_eq_coe
- \+ *theorem* inj'
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* schroeder_bernstein
- \+ *theorem* antisymm
- \+ *theorem* total
- \+ *theorem* equiv.to_embedding_coe_fn
- \+ *theorem* power_zero
- \+ *theorem* one_power
- \+ *theorem* prop_eq_two
- \+ *theorem* zero_power
- \+ *theorem* mul_power
- \+ *theorem* power_sum
- \+ *theorem* power_mul
- \+ *theorem* zero_le
- \+ *theorem* add_mono
- \+ *theorem* mul_mono
- \+ *theorem* power_mono_left
- \+ *theorem* power_mono_right
- \+ *theorem* le_iff_exists_add

Modified data/equiv.lean
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* cast_apply
- \+ *theorem* image_apply
- \+ *theorem* range_apply
- \+ *theorem* of_bijective_to_fun
- \+/\- *theorem* swap_self
- \+/\- *theorem* swap_swap
- \- *theorem* id_apply
- \- *theorem* comp_apply
- \- *def* id

Modified data/nat/basic.lean
- \+ *def* foldl
- \+ *def* foldr

Created data/ordinal.lean
- \+ *theorem* ord'
- \+ *theorem* coe_fn_mk
- \+ *theorem* coe_fn_to_embedding
- \+ *theorem* eq_of_to_fun_eq
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* eq_preimage
- \+ *theorem* of_monotone
- \+ *theorem* nat_lt
- \+ *theorem* well_founded_iff_no_descending_seq
- \+ *theorem* coe_coe_fn
- \+ *theorem* coe_fn_to_equiv
- \+ *theorem* coe_fn_symm_mk
- \+ *theorem* apply_inverse_apply
- \+ *theorem* inverse_apply_apply
- \+ *theorem* of_surjective_apply
- \+ *theorem* coe_fn_to_order_embedding
- \+ *theorem* init'
- \+ *theorem* init_iff
- \+ *theorem* of_iso_apply
- \+ *theorem* antisymm.aux
- \+ *theorem* antisymm_to_fun
- \+ *theorem* antisymm_symm
- \+ *theorem* eq_or_principal
- \+ *theorem* down'
- \+ *theorem* init
- \+ *theorem* coe_coe_fn'
- \+ *theorem* irrefl
- \+ *theorem* lt_le_apply
- \+ *theorem* equiv_lt_apply
- \+ *theorem* le_lt_apply
- \+ *def* is_irrefl_of_is_asymm
- \+ *def* is_irrefl.swap
- \+ *def* is_trans.swap
- \+ *def* is_strict_order.swap
- \+ *def* is_trichotomous.swap
- \+ *def* is_strict_total_order'.swap
- \+ *def* is_strict_weak_order_of_is_order_connected
- \+ *def* order.preimage
- \+ *def* rsymm
- \+ *def* preimage
- \+ *def* of_surjective
- \+ *def* set_coe_embedding
- \+ *def* of_iso
- \+ *def* unique_of_extensional
- \+ *def* antisymm
- \+ *def* lt_le
- \+ *def* equiv_lt
- \+ *def* le_lt
- \+ *def* ordinal
- \+ *def* le
- \+ *def* lt
- \+ *def* card

Modified data/set/basic.lean
- \+ *theorem* set_coe_cast



## [2017-12-09 22:14:32-05:00](https://github.com/leanprover-community/mathlib/commit/aef5c88)
feat(algebra/group_power): more gpow lemmas
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* inv_pow
- \+/\- *theorem* add_monoid.neg_smul
- \+ *theorem* gpow_coe_nat
- \+ *theorem* gpow_zero
- \+ *theorem* gpow_one
- \+ *theorem* gsmul_one
- \+ *theorem* one_gpow
- \+ *theorem* gpow_neg
- \+ *theorem* gsmul_neg
- \+ *theorem* gpow_neg_one
- \+ *theorem* gsmul_neg_one
- \+ *theorem* inv_gpow
- \+ *theorem* gpow_mul
- \+ *theorem* gsmul_mul
- \+ *theorem* gpow_bit0
- \+ *theorem* gpow_bit1
- \+ *theorem* gsmul_bit1
- \+/\- *theorem* pow_ne_zero
- \+ *theorem* one_div_pow
- \+ *theorem* division_ring.inv_pow
- \+ *theorem* div_pow
- \- *theorem* pow_inv
- \+/\- *def* gpow

Modified algebra/ring.lean


Modified analysis/limits.lean


Modified data/int/basic.lean
- \+ *theorem* coe_nat_mul_neg_succ
- \+ *theorem* neg_succ_mul_coe_nat
- \+ *theorem* neg_succ_mul_neg_succ



## [2017-12-08 17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8cfcef0)
feat(algebra/linear_algebra): add product construction for modules
#### Estimated changes
Created algebra/linear_algebra/prod_module.lean
- \+ *lemma* fst_mul
- \+ *lemma* snd_mul
- \+ *lemma* fst_one
- \+ *lemma* snd_one
- \+ *lemma* fst_inv
- \+ *lemma* snd_inv
- \+ *lemma* fst_prod
- \+ *lemma* snd_prod
- \+ *lemma* injective_inl
- \+ *lemma* injective_inr
- \+ *lemma* inl_eq_inl
- \+ *lemma* inr_eq_inr
- \+ *lemma* inl_eq_inr
- \+ *lemma* inr_eq_inl
- \+ *lemma* fst_inl
- \+ *lemma* snd_inl
- \+ *lemma* fst_inr
- \+ *lemma* snd_inr
- \+ *lemma* is_linear_map_prod_fst
- \+ *lemma* is_linear_map_prod_snd
- \+ *lemma* is_linear_map_prod_mk
- \+ *lemma* is_linear_map_prod_inl
- \+ *lemma* is_linear_map_prod_inr
- \+ *lemma* span_prod
- \+ *lemma* span_inl_union_inr
- \+ *lemma* linear_independent_inl_union_inr
- \+ *lemma* is_basis_inl_union_inr
- \+ *def* inl
- \+ *def* inr



## [2017-12-08 17:29:17+01:00](https://github.com/leanprover-community/mathlib/commit/8fab107)
refactor(algebra/module): split of type constructions and move quotient, subtype and linear_map to their own theories in algebra/linear_algebra
#### Estimated changes
Modified algebra/group.lean


Modified algebra/linear_algebra/basic.lean
- \+ *lemma* linear_independent_union

Created algebra/linear_algebra/linear_map_module.lean
- \+ *lemma* is_linear_map_coe
- \+ *lemma* map_add
- \+ *lemma* map_smul
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* mem_ker
- \+ *lemma* mem_im
- \+ *lemma* add_app
- \+ *lemma* zero_app
- \+ *lemma* neg_app
- \+ *lemma* smul_app
- \+ *lemma* one_app
- \+ *lemma* mul_app
- \+ *theorem* ext
- \+ *theorem* ker_of_map_eq_map
- \+ *theorem* inj_of_trivial_ker
- \+ *theorem* sub_ker
- \+ *def* linear_map
- \+ *def* ker
- \+ *def* im
- \+ *def* endomorphism_ring
- \+ *def* general_linear_group

Created algebra/linear_algebra/quotient_module.lean
- \+ *lemma* is_linear_map_quotient_mk
- \+ *lemma* is_linear_map_quotient_lift
- \+ *lemma* quotient.injective_lift
- \+ *def* quotient_rel
- \+ *def* quotient
- \+ *def* quotient.lift

Created algebra/linear_algebra/subtype_module.lean
- \+ *lemma* add_val
- \+ *lemma* zero_val
- \+ *lemma* neg_val
- \+ *lemma* smul_val
- \+ *lemma* sub_val
- \+ *lemma* is_linear_map_subtype_val
- \+ *lemma* is_linear_map_subtype_mk

Modified algebra/module.lean
- \- *lemma* add_val
- \- *lemma* zero_val
- \- *lemma* neg_val
- \- *lemma* smul_val
- \- *lemma* sub_val
- \- *lemma* is_linear_map_subtype_val
- \- *lemma* is_linear_map_subtype_mk
- \- *lemma* is_linear_map_quotient_mk
- \- *lemma* is_linear_map_quotient_lift
- \- *lemma* quotient.injective_lift
- \- *lemma* is_linear_map_coe
- \- *lemma* map_add
- \- *lemma* map_smul
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* mem_ker
- \- *lemma* mem_im
- \- *lemma* add_app
- \- *lemma* zero_app
- \- *lemma* neg_app
- \- *lemma* smul_app
- \- *lemma* one_app
- \- *lemma* mul_app
- \- *theorem* ext
- \- *theorem* ker_of_map_eq_map
- \- *theorem* inj_of_trivial_ker
- \- *theorem* sub_ker
- \- *def* quotient_rel
- \- *def* quotient
- \- *def* quotient.lift
- \- *def* linear_map
- \- *def* ker
- \- *def* im
- \- *def* endomorphism_ring
- \- *def* general_linear_group

Modified data/finsupp.lean
- \+ *lemma* support_subset_iff
- \+ *lemma* filter_apply_pos
- \+ *lemma* filter_apply_neg
- \+ *lemma* support_filter
- \+ *lemma* filter_pos_add_filter_neg
- \+ *def* filter

Modified data/set/basic.lean
- \+ *lemma* mem_image_of_injective



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
- \+ *lemma* exists_subset_is_basis
- \+/\- *lemma* exists_is_basis

Modified analysis/measure_theory/measurable_space.lean


Modified analysis/metric_space.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified data/bool.lean
- \+ *theorem* to_bool_coe

Modified data/cardinal.lean
- \+/\- *lemma* total
- \+/\- *lemma* power_zero
- \+/\- *lemma* one_power
- \+ *lemma* prop_eq_two
- \+/\- *lemma* zero_power
- \+/\- *lemma* mul_power
- \+/\- *lemma* power_sum
- \+/\- *lemma* power_mul
- \+ *lemma* zero_le
- \+/\- *lemma* power_mono_left
- \+/\- *lemma* power_mono_right
- \+ *lemma* le_iff_exists_add
- \- *lemma* option.eq_of_le_some
- \- *lemma* option.le_Sup
- \- *lemma* option.Sup_le
- \- *lemma* option.mem_of_Sup_eq_some
- \- *lemma* exists_injective_or_surjective
- \+ *theorem* injective_min
- \+ *theorem* ne_zero_iff_nonempty
- \+ *theorem* cantor
- \+ *theorem* min_eq
- \+ *theorem* min_le
- \+ *theorem* le_min
- \+ *theorem* le_sum
- \+ *theorem* le_sup
- \+ *theorem* sup_le
- \+ *def* min
- \+ *def* sum
- \+ *def* sup
- \- *def* option.strict_partial_order
- \- *def* option.Sup
- \- *def* pfun
- \- *def* pfun.partial_order

Modified data/equiv.lean


Modified data/finset.lean
- \+/\- *lemma* strong_induction_on
- \+/\- *lemma* case_strong_induction_on
- \+ *theorem* le_iff_subset
- \+ *theorem* lt_iff_ssubset
- \+ *theorem* val_lt_iff

Modified data/multiset.lean
- \+ *lemma* strong_induction_on
- \+ *lemma* case_strong_induction_on

Modified data/set/basic.lean
- \+ *lemma* mem_prod_eq
- \+ *lemma* mem_prod
- \+ *lemma* prod_empty
- \+ *lemma* empty_prod
- \+ *lemma* insert_prod
- \+ *lemma* prod_insert
- \+ *lemma* prod_mono
- \+ *lemma* prod_inter_prod
- \+ *lemma* image_swap_prod
- \+ *lemma* prod_image_image_eq
- \+ *lemma* prod_singleton_singleton
- \+ *lemma* prod_neq_empty_iff
- \+ *lemma* prod_mk_mem_set_prod_eq
- \+ *lemma* univ_prod_univ
- \+ *theorem* eq_empty_iff_forall_not_mem
- \+/\- *theorem* mem_insert_iff
- \+ *theorem* prod_preimage_eq
- \+ *theorem* image_swap_eq_preimage_swap
- \- *theorem* eq_empty_of_forall_not_mem

Modified data/set/default.lean


Modified data/set/disjointed.lean


Modified data/set/enumerate.lean


Modified data/set/finite.lean


Modified data/set/intervals.lean


Modified data/set/lattice.lean
- \+ *theorem* monotone_prod

Deleted data/set/prod.lean
- \- *lemma* mem_prod_eq
- \- *lemma* mem_prod
- \- *lemma* prod_empty
- \- *lemma* empty_prod
- \- *lemma* insert_prod
- \- *lemma* prod_insert
- \- *lemma* prod_mono
- \- *lemma* prod_inter_prod
- \- *lemma* image_swap_prod
- \- *lemma* prod_image_image_eq
- \- *lemma* prod_singleton_singleton
- \- *lemma* prod_neq_empty_iff
- \- *lemma* prod_mk_mem_set_prod_eq
- \- *lemma* univ_prod_univ
- \- *theorem* prod_preimage_eq
- \- *theorem* monotone_prod
- \- *theorem* image_swap_eq_preimage_swap

Modified logic/basic.lean
- \+ *theorem* empty.elim

Modified logic/function.lean
- \+ *theorem* cantor_surjective
- \+ *theorem* cantor_injective

Modified order/zorn.lean
- \+ *theorem* chain.total

Modified theories/number_theory/dioph.lean
- \- *def* arity
- \- *def* curry
- \- *def* uncurry



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
Created algebra/linear_algebra/basic.lean
- \+ *lemma* smul_sum
- \+ *lemma* smul_apply
- \+ *lemma* sum_smul_index
- \+ *lemma* is_linear_map_sum
- \+ *lemma* finsupp_sum
- \+ *lemma* is_submodule_span
- \+ *lemma* subset_span
- \+ *lemma* span_eq_of_is_submodule
- \+ *lemma* span_mono
- \+ *lemma* span_minimal
- \+ *lemma* span_eq
- \+ *lemma* span_empty
- \+ *lemma* is_submodule_range_smul
- \+ *lemma* span_singleton
- \+ *lemma* span_union
- \+ *lemma* span_insert_eq_span
- \+ *lemma* span_insert
- \+ *lemma* span_span
- \+ *lemma* span_image_of_linear_map
- \+ *lemma* linear_eq_on
- \+ *lemma* linear_independent_empty
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent.unique
- \+ *lemma* repr_not_span
- \+ *lemma* repr_spec
- \+ *lemma* repr_eq_zero
- \+ *lemma* repr_sum_eq
- \+ *lemma* repr_eq
- \+ *lemma* repr_eq_single
- \+ *lemma* repr_zero
- \+ *lemma* repr_support
- \+ *lemma* repr_add
- \+ *lemma* repr_smul
- \+ *lemma* repr_neg
- \+ *lemma* repr_sub
- \+ *lemma* repr_sum
- \+ *lemma* repr_finsupp_sum
- \+ *lemma* repr_eq_repr_of_subset
- \+ *lemma* linear_independent.of_image
- \+ *lemma* linear_independent.eq_0_of_span
- \+ *lemma* is_basis.map_repr
- \+ *lemma* is_basis.map_constr
- \+ *lemma* is_basis.eq_linear_map
- \+ *lemma* constr_congr
- \+ *lemma* constr_basis
- \+ *lemma* constr_eq
- \+ *lemma* constr_zero
- \+ *lemma* constr_add
- \+ *lemma* constr_sub
- \+ *lemma* constr_neg
- \+ *lemma* constr_smul
- \+ *lemma* constr_mem_span
- \+ *lemma* constr_im_eq_span
- \+ *lemma* linear_independent.inj_span_iff_inj
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_map.linear_independent_image_iff
- \+ *lemma* zero_not_mem_of_linear_independent
- \+ *lemma* mem_span_insert_exchange
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent.insert
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_is_basis
- \+ *lemma* eq_of_linear_independent_of_span
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *lemma* exists_left_inverse_linear_map_of_injective
- \+ *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *def* lc
- \+ *def* span
- \+ *def* linear_independent
- \+ *def* linear_independent.repr
- \+ *def* is_basis
- \+ *def* is_basis.constr
- \+ *def* module_equiv_lc

Created algebra/linear_algebra/default.lean




## [2017-12-07 17:24:30+01:00](https://github.com/leanprover-community/mathlib/commit/f09abb1)
feat(data/finsupp): add type of functions with finite support
#### Estimated changes
Created data/finsupp.lean
- \+ *lemma* zero_apply
- \+ *lemma* ext
- \+ *lemma* finite_supp
- \+ *lemma* mem_support_iff
- \+ *lemma* support_zero
- \+ *lemma* single_apply
- \+ *lemma* single_eq_same
- \+ *lemma* single_eq_of_ne
- \+ *lemma* single_zero
- \+ *lemma* support_single_subset
- \+ *lemma* support_single_ne_zero
- \+ *lemma* map_range_apply
- \+ *lemma* support_map_range
- \+ *lemma* zip_with_apply
- \+ *lemma* support_zip_with
- \+ *lemma* sum_map_range_index
- \+ *lemma* sum_zero_index
- \+ *lemma* sum_single_index
- \+ *lemma* add_apply
- \+ *lemma* support_add
- \+ *lemma* single_add
- \+ *lemma* sum_neg_index
- \+ *lemma* neg_apply
- \+ *lemma* sub_apply
- \+ *lemma* sum_apply
- \+ *lemma* support_sum
- \+ *lemma* sum_zero
- \+ *lemma* sum_add
- \+ *lemma* sum_neg
- \+ *lemma* sum_single
- \+ *lemma* sum_add_index
- \+ *lemma* sum_sub_index
- \+ *lemma* sum_finset_sum_index
- \+ *lemma* sum_sum_index
- \+ *lemma* map_domain_id
- \+ *lemma* map_domain_comp
- \+ *lemma* map_domain_single
- \+ *lemma* map_domain_zero
- \+ *lemma* map_domain_congr
- \+ *lemma* map_domain_add
- \+ *lemma* map_domain_finset_sum
- \+ *lemma* map_domain_sum
- \+ *lemma* map_domain_support
- \+ *lemma* sum_map_domain_index
- \+ *lemma* mul_def
- \+ *lemma* one_def
- \+ *lemma* comap_domain_apply
- \+ *lemma* comap_domain_zero
- \+ *lemma* sum_comap_domain_index
- \+ *lemma* sum_subtype_domain_index
- \+ *lemma* subtype_domain_apply
- \+ *lemma* subtype_domain_zero
- \+ *lemma* comap_domain_add
- \+ *lemma* subtype_domain_add
- \+ *lemma* comap_domain_sum
- \+ *lemma* comap_domain_finsupp_sum
- \+ *lemma* subtype_domain_sum
- \+ *lemma* subtype_domain_finsupp_sum
- \+ *lemma* comap_domain_neg
- \+ *lemma* comap_domain_sub
- \+ *lemma* subtype_domain_neg
- \+ *lemma* subtype_domain_sub
- \+ *lemma* single_mul_single
- \+ *lemma* prod_single
- \+ *def* finsupp
- \+ *def* support
- \+ *def* single
- \+ *def* map_range
- \+ *def* zip_with
- \+ *def* sum
- \+ *def* map_domain
- \+ *def* comap_domain
- \+ *def* subtype_domain
- \+ *def* to_semiring
- \+ *def* to_comm_semiring
- \+ *def* to_ring
- \+ *def* to_comm_ring



## [2017-12-07 17:22:37+01:00](https://github.com/leanprover-community/mathlib/commit/fcf0bfa)
feat(data/set/finite): add finite_to_set, finset.coe_to_finset
#### Estimated changes
Modified data/set/finite.lean
- \+ *lemma* finite_to_set
- \+/\- *lemma* coe_filter
- \+ *lemma* coe_to_finset



## [2017-12-07 17:18:54+01:00](https://github.com/leanprover-community/mathlib/commit/5e42425)
fix(algebra/module): fix type universes in is_linear_map.sum
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* sum



## [2017-12-07 14:42:09+01:00](https://github.com/leanprover-community/mathlib/commit/0995ac1)
feat(algebra/module): the inverse of a linear map is linear
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* inverse
- \+ *lemma* smul_ne_0



## [2017-12-07 14:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/645bf60)
core(algebra/module): generalize map_smul_left; add is_submodule.range
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* map_smul_left



## [2017-12-07 00:39:32-05:00](https://github.com/leanprover-community/mathlib/commit/5f642d8)
refactor(*): remove local simp AC lemmas
Using local simp lemmas everywhere for mul_assoc and friends defeats the purpose of the change in core. Now theorems are proven with only the AC lemmas actually used in the proof.
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* div_eq_inv_mul

Modified algebra/functions.lean
- \+ *theorem* le_max_left_iff_true
- \+ *theorem* le_max_right_iff_true
- \+ *theorem* min_right_comm
- \+ *theorem* max.left_comm
- \+ *theorem* max.right_comm

Modified algebra/group_power.lean


Modified algebra/order.lean
- \+/\- *lemma* not_lt
- \+/\- *lemma* le_of_not_lt
- \+/\- *lemma* not_le
- \+ *lemma* lt_or_le
- \+ *lemma* le_or_lt

Modified analysis/ennreal.lean
- \+/\- *lemma* of_real_lt_of_real_iff_cases
- \+ *theorem* le_def

Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/real.lean
- \+/\- *lemma* uniform_embedding_mul_rat
- \+ *lemma* nonneg_antisymm
- \- *lemma* eq_0_of_nonneg_of_neg_nonneg

Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* mem_interior
- \+ *lemma* subset_interior_iff_open
- \+ *lemma* is_open_iff_forall_mem_open
- \+/\- *lemma* is_open_iff_nhds
- \+/\- *lemma* is_open_iff_mem_nhds
- \+/\- *lemma* is_closed_iff_nhds

Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/analysis/filter.lean


Modified data/analysis/topology.lean


Modified data/cardinal.lean


Modified data/finset.lean
- \+/\- *theorem* insert_subset
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_assoc
- \+/\- *theorem* union_left_comm
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+/\- *theorem* union_insert
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm

Modified data/multiset.lean


Modified data/nat/sqrt.lean


Modified data/num/lemmas.lean


Modified data/rat.lean


Modified data/set/countable.lean


Modified data/set/disjointed.lean


Modified data/set/intervals.lean


Modified logic/function.lean


Modified order/basic.lean
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
- \+ *lemma* prod_attach
- \+ *lemma* prod_bij
- \+ *lemma* prod_bij_ne_one

Modified data/finset.lean
- \+ *lemma* attach_image_val



## [2017-12-06 16:48:38+01:00](https://github.com/leanprover-community/mathlib/commit/e5c4eb1)
feat(data/set): add lift converting finset to set
#### Estimated changes
Modified data/set/default.lean


Modified data/set/finite.lean
- \+ *lemma* mem_coe
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_subseteq_coe
- \+ *lemma* coe_empty
- \+ *lemma* coe_insert
- \+ *lemma* coe_erase
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_singleton
- \+ *lemma* coe_union
- \+ *lemma* coe_inter
- \+ *lemma* coe_image
- \+ *lemma* coe_bind
- \+ *lemma* coe_filter
- \+ *def* to_set



## [2017-12-06 16:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/7f9dd51)
feat(data/finset): add strong induction rules for finset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* card_eq_succ
- \+ *lemma* card_lt_card
- \+ *lemma* strong_induction_on
- \+ *lemma* case_strong_induction_on
- \+ *theorem* card_le_of_subset
- \+ *theorem* eq_of_subset_of_card_le



## [2017-12-06 16:21:41+01:00](https://github.com/leanprover-community/mathlib/commit/81e53e8)
feat(data/finset): add ssubset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* ssubset_iff
- \+ *lemma* ssubset_insert
- \+ *lemma* erase_ssubset



## [2017-12-06 13:30:50+01:00](https://github.com/leanprover-community/mathlib/commit/f9b39eb)
feature(.): add various theorems
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* bind_mono
- \+ *lemma* bind_singleton

Modified data/prod.lean
- \+ *lemma* mk.eta
- \+ *lemma* swap_swap
- \+ *lemma* fst_swap
- \+ *lemma* snd_swap
- \+ *lemma* swap_prod_mk
- \+ *lemma* swap_swap_eq
- \+ *lemma* swap_left_inverse
- \+ *lemma* swap_right_inverse
- \+ *lemma* eq_iff_fst_eq_snd_eq
- \- *lemma* prod.mk.eta
- \- *lemma* prod.swap_swap
- \- *lemma* prod.fst_swap
- \- *lemma* prod.snd_swap
- \- *lemma* prod.swap_prod_mk
- \- *lemma* prod.swap_swap_eq
- \- *lemma* prod.swap_left_inverse
- \- *lemma* prod.swap_right_inverse
- \+ *theorem* prod.forall
- \+ *theorem* prod.exists
- \+ *theorem* mk.inj_iff
- \+ *def* swap
- \- *def* prod.swap

Modified data/set/basic.lean
- \+ *lemma* not_subset
- \+/\- *lemma* not_not_mem
- \+ *lemma* insert_subset
- \+ *lemma* insert_subset_insert
- \+ *lemma* insert_union
- \+ *lemma* union_insert
- \+ *lemma* diff_diff
- \+/\- *theorem* ssubset_def
- \+/\- *theorem* nonempty_of_inter_nonempty_right
- \+/\- *theorem* nonempty_of_inter_nonempty_left
- \+ *theorem* insert_sdiff

Modified data/set/finite.lean
- \+ *lemma* to_finset_insert
- \+ *theorem* finite.dinduction_on

Modified logic/basic.lean
- \- *theorem* prod.mk.inj_iff
- \- *theorem* prod.forall
- \- *theorem* prod.exists



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
- \+/\- *lemma* add_val
- \+/\- *lemma* neg_val

Modified algebra/ring.lean


Modified data/bool.lean
- \+ *theorem* coe_to_bool
- \- *theorem* to_bool_bool

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
- \+/\- *lemma* sigma.mk_eq_mk_iff
- \+/\- *def* sigma.map



## [2017-12-05 18:13:32+01:00](https://github.com/leanprover-community/mathlib/commit/0e3b156)
fix(algebra/module): remove instance endomorphism_ring, it breaks real.lean
#### Estimated changes
Modified algebra/module.lean
- \+ *def* endomorphism_ring
- \+/\- *def* general_linear_group



## [2017-12-05 18:03:32+01:00](https://github.com/leanprover-community/mathlib/commit/394d721)
feat(algebra/module): add quotient module
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* is_linear_map_quotient_mk
- \+ *lemma* is_linear_map_quotient_lift
- \+ *lemma* quotient.injective_lift
- \+ *def* quotient_rel
- \+ *def* quotient
- \+ *def* quotient.lift



## [2017-12-05 17:24:36+01:00](https://github.com/leanprover-community/mathlib/commit/dcfb9a0)
refactor(algebra/module): add is_linear_map as predicate
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* set.sInter_eq_Inter
- \+ *lemma* smul_eq_mul
- \+ *lemma* zero
- \+ *lemma* neg
- \+ *lemma* sub
- \+ *lemma* sum
- \+ *lemma* comp
- \+ *lemma* id
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg
- \+ *lemma* map_add
- \+ *lemma* map_sum
- \+/\- *lemma* map_sub
- \+ *lemma* map_smul_right
- \+ *lemma* map_smul_left
- \+ *lemma* Inter_submodule
- \+/\- *lemma* sub_val
- \+ *lemma* is_linear_map_subtype_val
- \+ *lemma* is_linear_map_subtype_mk
- \+ *lemma* is_linear_map_coe
- \+ *lemma* map_smul
- \+/\- *lemma* mem_im
- \+/\- *lemma* add_app
- \+/\- *lemma* zero_app
- \+/\- *lemma* neg_app
- \+/\- *lemma* smul_app
- \+/\- *lemma* one_app
- \+/\- *lemma* mul_app
- \- *lemma* map_add_app
- \- *lemma* map_smul_app
- \+/\- *theorem* ext
- \+ *def* linear_map
- \+/\- *def* ker
- \+/\- *def* im
- \+/\- *def* general_linear_group
- \- *def* endomorphism_ring



## [2017-12-05 14:35:49+01:00](https://github.com/leanprover-community/mathlib/commit/88202b6)
refactor(algebra/module): clean up is_submodule projections
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* zero
- \+ *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* sub
- \+ *lemma* sum
- \+/\- *lemma* add_val
- \+/\- *lemma* neg_val
- \+ *lemma* sub_val



## [2017-12-05 14:15:07+01:00](https://github.com/leanprover-community/mathlib/commit/90ed0ab)
refactor(algebra/module): rename submodule -> is_submodule, smul_left_distrib -> smul_add, smul_right_distrib -> add_smul, smul_sub_left_distrib -> smul_sub, sub_smul_right_distrib -> sub_smul
#### Estimated changes
Modified algebra/module.lean
- \+ *theorem* smul_add
- \+ *theorem* add_smul
- \+ *theorem* smul_sub
- \+ *theorem* sub_smul
- \- *theorem* smul_left_distrib
- \- *theorem* smul_right_distrib
- \- *theorem* smul_sub_left_distrib
- \- *theorem* sub_smul_right_distrib



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
- \+/\- *theorem* mod_add_cancel_right
- \+/\- *theorem* mod_sub_cancel_right

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
- \+/\- *theorem* ball_image_of_ball
- \+/\- *theorem* ball_image_iff

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
- \+/\- *def* fold

Modified data/hash_map.lean


Modified data/list/basic.lean
- \+/\- *theorem* diff_nil
- \+/\- *theorem* pw_filter_nil

Modified data/list/perm.lean


Modified data/list/sort.lean


Modified data/multiset.lean
- \+ *theorem* quot_mk_to_coe''

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


Modified theories/number_theory/pell.lean


Modified theories/set_theory.lean




## [2017-12-04 23:24:01-05:00](https://github.com/leanprover-community/mathlib/commit/2dadfdb)
feat(tactic/norm_num): add {nat,int}.mod
#### Estimated changes
Modified tactic/norm_num.lean
- \+ *lemma* nat_mod_helper
- \+ *lemma* int_mod_helper



## [2017-12-04 23:05:57-05:00](https://github.com/leanprover-community/mathlib/commit/8d27f70)
feat(tactic/norm_num): add support for {nat,int}.div
#### Estimated changes
Modified data/rat.lean


Modified tactic/norm_num.lean
- \+ *lemma* nat_div_helper
- \+ *lemma* int_div_helper

Modified tests/norm_num.lean




## [2017-12-04 21:23:11-05:00](https://github.com/leanprover-community/mathlib/commit/b1981c9)
chore(theories/number_theory/dioph): cleanup
#### Estimated changes
Modified data/int/basic.lean


Modified theories/number_theory/dioph.lean
- \+/\- *theorem* subst_eval
- \+/\- *theorem* proj_eval
- \+/\- *theorem* const_eval
- \+/\- *theorem* zero_eval
- \+/\- *theorem* one_eval
- \+/\- *theorem* sub_eval
- \+/\- *theorem* neg_eval
- \+/\- *theorem* add_eval
- \+/\- *theorem* mul_eval
- \+/\- *theorem* sumsq_nonneg
- \+/\- *theorem* sumsq_eq_zero
- \+/\- *theorem* remap_eval
- \- *theorem* nth_of_fn
- \- *theorem* of_fn_nth
- \- *theorem* left_extends.le
- \- *theorem* append_left_extends
- \- *theorem* left_extends_iff_append
- \- *theorem* exists_left_extends_iff_append
- \- *theorem* insert_fz
- \- *theorem* insert_perm_nth
- \- *theorem* insert_nth
- \- *theorem* append_insert
- \- *theorem* vector.nth'_eq_nth_le
- \- *theorem* vector.nth'_eq_nth_le'
- \- *theorem* vector.nth'_zero
- \- *theorem* vector.nth'_succ
- \- *theorem* vector.nth'_of_fn
- \- *theorem* vector.of_fn_nth'
- \- *theorem* zero_val
- \- *theorem* one_val
- \- *theorem* sub_val
- \- *theorem* neg_val
- \- *theorem* add_val
- \- *theorem* mul_val
- \+/\- *def* isp
- \+/\- *def* ext
- \+/\- *def* subst
- \- *def* cons_elim
- \- *def* nth
- \- *def* of_fn
- \- *def* append
- \- *def* insert
- \- *def* vector.nth'
- \- *def* vector.append_nth'_left
- \- *def* vector.append_nth'_right
- \- *def* vector.nth'_map
- \- *def* eval
- \- *def* insert_poly
- \- *def* remap
- \- *def* ndrop



## [2017-12-01 08:02:15-05:00](https://github.com/leanprover-community/mathlib/commit/7191e39)
feat(theories/number_theory/dioph): Pell equation, diophantine equations
#### Estimated changes
Modified algebra/group.lean


Modified data/int/basic.lean
- \+ *theorem* coe_nat_mod
- \+ *theorem* mod_add_cancel_right
- \+ *theorem* mod_add_cancel_left
- \+ *theorem* mod_sub_cancel_right
- \+ *theorem* mod_eq_mod_iff_mod_sub_eq_zero
- \+ *theorem* to_nat_of_nonneg
- \+ *theorem* to_nat_coe_nat
- \- *theorem* mod_eq_mod_of_add_mod_eq_add_mod_right
- \- *theorem* mod_eq_mod_of_add_mod_eq_add_mod_left

Modified data/nat/gcd.lean
- \+ *theorem* xgcd_zero_left
- \+ *theorem* xgcd_aux_rec
- \+ *theorem* xgcd_aux_fst
- \+ *theorem* xgcd_aux_val
- \+ *theorem* xgcd_val
- \+ *theorem* xgcd_aux_P
- \+ *theorem* gcd_eq_gcd_ab
- \+/\- *theorem* coprime.gcd_eq_one
- \+/\- *theorem* coprime.symm
- \+ *def* xgcd_aux
- \+ *def* xgcd
- \+ *def* gcd_a
- \+ *def* gcd_b

Created data/nat/modeq.lean
- \+ *theorem* modeq_zero_iff
- \+ *theorem* modeq_iff_dvd
- \+ *theorem* modeq_of_dvd
- \+ *theorem* dvd_of_modeq
- \+ *theorem* modeq_of_dvd_of_modeq
- \+ *theorem* modeq_mul_left'
- \+ *theorem* modeq_mul_left
- \+ *theorem* modeq_mul_right'
- \+ *theorem* modeq_mul_right
- \+ *theorem* modeq_mul
- \+ *theorem* modeq_add
- \+ *theorem* modeq_add_cancel_left
- \+ *theorem* modeq_add_cancel_right
- \+ *theorem* chinese_remainder
- \+ *def* modeq

Modified data/pfun.lean
- \+ *theorem* lift_graph
- \+/\- *def* graph

Created theories/number_theory/dioph.lean
- \+ *theorem* nth_of_fn
- \+ *theorem* of_fn_nth
- \+ *theorem* left_extends.le
- \+ *theorem* append_left_extends
- \+ *theorem* left_extends_iff_append
- \+ *theorem* exists_left_extends_iff_append
- \+ *theorem* insert_fz
- \+ *theorem* insert_perm_nth
- \+ *theorem* insert_nth
- \+ *theorem* append_insert
- \+ *theorem* vector.nth'_eq_nth_le
- \+ *theorem* vector.nth'_eq_nth_le'
- \+ *theorem* vector.nth'_zero
- \+ *theorem* vector.nth'_succ
- \+ *theorem* vector.nth'_of_fn
- \+ *theorem* vector.of_fn_nth'
- \+ *theorem* exists_vector_zero
- \+ *theorem* exists_vector_succ
- \+ *theorem* vector_ex_iff_exists
- \+ *theorem* vector_all_iff_forall
- \+ *theorem* vector_allp_nil
- \+ *theorem* vector_allp_singleton
- \+ *theorem* vector_allp_cons
- \+ *theorem* vector_allp_iff_forall
- \+ *theorem* vector_allp.imp
- \+ *theorem* list_all_cons
- \+ *theorem* list_all_iff_forall
- \+ *theorem* list_all.imp
- \+ *theorem* list_all_map
- \+ *theorem* list_all_congr
- \+ *theorem* subst_eval
- \+ *theorem* proj_eval
- \+ *theorem* const_eval
- \+ *theorem* zero_eval
- \+ *theorem* zero_val
- \+ *theorem* one_eval
- \+ *theorem* one_val
- \+ *theorem* sub_eval
- \+ *theorem* sub_val
- \+ *theorem* neg_eval
- \+ *theorem* neg_val
- \+ *theorem* add_eval
- \+ *theorem* add_val
- \+ *theorem* mul_eval
- \+ *theorem* mul_val
- \+ *theorem* sumsq_nonneg
- \+ *theorem* sumsq_eq_zero
- \+ *theorem* remap_eval
- \+ *def* vector3
- \+ *def* cons_elim
- \+ *def* nth
- \+ *def* of_fn
- \+ *def* append
- \+ *def* insert
- \+ *def* vector.append_nth'_left
- \+ *def* vector.append_nth'_right
- \+ *def* vector.nth'_map
- \+ *def* arity
- \+ *def* curry
- \+ *def* uncurry
- \+ *def* vector_ex
- \+ *def* vector_all
- \+ *def* vector_allp
- \+ *def* list_all
- \+ *def* poly
- \+ *def* eval
- \+ *def* isp
- \+ *def* ext
- \+ *def* subst
- \+ *def* proj
- \+ *def* const
- \+ *def* zero
- \+ *def* one
- \+ *def* sub
- \+ *def* neg
- \+ *def* add
- \+ *def* mul
- \+ *def* induction
- \+ *def* pow
- \+ *def* sumsq
- \+ *def* remap
- \+ *def* insert_poly
- \+ *def* ndrop
- \+ *def* dioph
- \- *def* vector.nth'

Created theories/number_theory/pell.lean
- \+ *lemma* eq_pow_of_pell_lem
- \+ *theorem* xy_modeq_of_modeq
- \+ *theorem* matiyasevic
- \+ *theorem* eq_pow_of_pell

