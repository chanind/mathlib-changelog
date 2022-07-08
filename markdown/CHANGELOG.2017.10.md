## [2017-10-25 22:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/ff43691)
fix(analysis/real): remove import for old file
note: exists_subtype is now subtype.exists in logic/basic
#### Estimated changes
modified analysis/real.lean



## [2017-10-25 21:55:10-04:00](https://github.com/leanprover-community/mathlib/commit/3cd6229)
refactor(analysis/real): use more coe instead of of_rat
#### Estimated changes
modified analysis/ennreal.lean

modified analysis/measure_theory/borel_space.lean
- \+ *lemma* is_topological_basis_Ioo_rat
- \+ *lemma* borel_eq_generate_from_Ioo_rat
- \+ *lemma* borel_eq_generate_from_Iio_rat
- \- *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \- *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \- *lemma* borel_eq_generate_from_Iio_of_rat

modified analysis/measure_theory/lebesgue_measure.lean

modified analysis/real.lean
- \+ *lemma* exists_rat_btwn
- \+ *lemma* exists_lt_rat
- \+ *lemma* exists_rat_lt
- \- *lemma* exists_lt_of_rat_of_rat_gt

modified data/int/basic.lean
- \+ *theorem* cast_min
- \+ *theorem* cast_max
- \+ *theorem* cast_abs

modified data/nat/cast.lean
- \+ *theorem* cast_min
- \+ *theorem* cast_max

modified data/rat.lean
- \+ *theorem* cast_min
- \+ *theorem* cast_max
- \+ *theorem* cast_abs

deleted data/subtype.lean
- \- *lemma* forall_subtype
- \- *theorem* exists_subtype



## [2017-10-24 22:57:22-04:00](https://github.com/leanprover-community/mathlib/commit/2dd035a)
Merge remote-tracking branch 'cipher1024/master'
#### Estimated changes
created meta/expr.lean

created tactic/norm_num.lean
- \+ *lemma* pow_bit0
- \+ *lemma* pow_bit0_helper
- \+ *lemma* pow_bit1
- \+ *lemma* pow_bit1_helper
- \+ *lemma* pow_one
- \+ *lemma* pow_zero
- \+ *lemma* pow_eq_pow_nat
- \+ *lemma* pow_eq_pow_nat_helper
- \+ *lemma* zero_le_bit0
- \+ *lemma* zero_le_bit1
- \+ *lemma* zero_le_zero
- \+ *lemma* zero_le_one
- \+ *lemma* one_le_bit0
- \+ *lemma* one_le_bit1
- \+ *lemma* one_le_one
- \+ *lemma* bit0_le_zero
- \+ *lemma* bit0_le_one
- \+ *lemma* bit1_le_bit0
- \+ *lemma* bit1_le_zero
- \+ *lemma* bit1_le_one
- \+ *lemma* one_le_denote
- \+ *lemma* denote_add1
- \+ *lemma* bit0_le_bit0
- \+ *lemma* denote_le_denote_of_pos_num_le
- \+ *lemma* zero_le_denote
- \+ *lemma* denote_le_denote_of_num_le
- \+ *lemma* denote_le_denote_of_znum_le
- \+ *def* add1
- \+ *def* add_n
- \+ *def* pos_le
- \+ *def* num_le
- \+ *def* znum_le
- \+ *def* znum.to_pos
- \+ *def* znum.to_neg

created tests/norm_num.lean



## [2017-10-24 22:31:12-04:00](https://github.com/leanprover-community/mathlib/commit/dd9f766)
feat(data/num,data/nat/cast,...): nat,num,int,rat.cast, list stuff
#### Estimated changes
modified algebra/field.lean
- \+ *lemma* inv_comm_of_comm

modified algebra/group.lean

modified algebra/group_power.lean
- \+ *theorem* nat.pow_eq_pow_nat

modified algebra/ordered_ring.lean
- \+ *theorem* mul_nonneg_iff_right_nonneg_of_pos

modified analysis/limits.lean
- \+/\- *lemma* mul_add_one_le_pow
- \+/\- *lemma* mul_add_one_le_pow

modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* tendsto_of_nat_at_top_at_top
- \+/\- *lemma* tendsto_of_nat_at_top_at_top

modified analysis/metric_space.lean

deleted analysis/of_nat.lean
- \- *lemma* of_nat_add
- \- *lemma* of_nat_one
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_sub
- \- *lemma* int_of_nat_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* zero_le_of_nat
- \- *lemma* of_nat_pos
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* exists_lt_of_nat
- \- *def* of_nat

modified analysis/real.lean
- \+ *lemma* exists_lt_nat
- \+ *theorem* coe_rat_eq_of_rat
- \+/\- *def* lift_rat_fun
- \+/\- *def* lift_rat_op
- \+/\- *def* lift_rat_fun
- \+/\- *def* lift_rat_op

modified data/encodable.lean
- \+/\- *def* encodable_of_left_injection
- \+/\- *def* encodable_of_equiv
- \+/\- *def* encodable_of_left_injection
- \+/\- *def* encodable_of_equiv

modified data/equiv.lean
- \+ *lemma* apply_inverse_apply
- \+ *def* psum_equiv_sum
- \+ *def* psigma_equiv_sigma
- \+ *def* sigma_congr_right
- \+ *def* sigma_congr_left
- \+ *def* sigma_equiv_prod
- \+ *def* sigma_equiv_prod_of_equiv
- \+ *def* int_equiv_nat_sum_nat
- \+ *def* int_equiv_nat

modified data/finset/basic.lean

modified data/int/basic.lean
- \+ *theorem* coe_nat_le
- \+ *theorem* coe_nat_lt
- \+ *theorem* coe_nat_inj'
- \+ *theorem* coe_nat_pos
- \+ *theorem* coe_nat_eq_zero
- \+ *theorem* coe_nat_ne_zero
- \+ *theorem* coe_nat_dvd
- \+ *theorem* nat_abs_dvd
- \+ *theorem* dvd_nat_abs
- \+ *theorem* nat_cast_eq_coe_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_of_nat
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_neg_succ_of_nat
- \+ *theorem* cast_one
- \+ *theorem* cast_sub_nat_nat
- \+ *theorem* cast_neg_of_nat
- \+ *theorem* cast_add
- \+ *theorem* cast_neg
- \+ *theorem* cast_sub
- \+ *theorem* cast_mul
- \+ *theorem* mul_cast_comm
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_nonneg
- \+ *theorem* cast_le
- \+ *theorem* cast_lt
- \+ *theorem* cast_nonpos
- \+ *theorem* cast_pos
- \+ *theorem* cast_lt_zero
- \+ *theorem* cast_inj
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero
- \+ *theorem* cast_id
- \- *theorem* coe_nat_dvd_coe_nat_of_dvd
- \- *theorem* dvd_of_coe_nat_dvd_coe_nat
- \- *theorem* coe_nat_dvd_coe_nat_iff
- \- *theorem* coe_nat_dvd_left
- \- *theorem* coe_nat_dvd_right

modified data/list/basic.lean
- \+ *theorem* erase_comm
- \+ *theorem* diff_nil
- \+ *theorem* diff_cons
- \+ *theorem* diff_eq_foldl

modified data/list/perm.lean
- \+ *theorem* perm_subset
- \+/\- *theorem* mem_of_perm
- \+ *theorem* perm.subperm_left
- \+ *theorem* perm.subperm_right
- \+ *theorem* subperm_of_sublist
- \+ *theorem* subperm_of_perm
- \+ *theorem* subperm.refl
- \+ *theorem* subperm.trans
- \+ *theorem* length_le_of_subperm
- \+ *theorem* subperm.perm_of_length_le
- \+ *theorem* subperm.antisymm
- \+ *theorem* subset_of_subperm
- \+ *theorem* exists_perm_append_of_sublist
- \+ *theorem* countp_le_of_subperm
- \+ *theorem* count_le_of_subperm
- \+ *theorem* perm_app_right_iff
- \+ *theorem* subperm_cons
- \+ *theorem* subperm_app_left
- \+ *theorem* subperm_app_right
- \+ *theorem* subperm.exists_of_length_lt
- \+ *theorem* subperm_of_subset_nodup
- \+ *theorem* perm_diff_left
- \+ *theorem* perm_diff_right
- \+/\- *theorem* mem_of_perm
- \- *theorem* mem_iff_mem_of_perm
- \- *theorem* perm_app_inv_right
- \- *theorem* exists_sublist_perm_of_subset_nodup
- \+ *def* subperm

modified data/list/sort.lean

created data/nat/cast.lean
- \+ *theorem* cast_zero
- \+ *theorem* cast_add_one
- \+ *theorem* cast_succ
- \+ *theorem* cast_one
- \+ *theorem* cast_add
- \+ *theorem* cast_pred
- \+ *theorem* cast_sub
- \+ *theorem* cast_mul
- \+ *theorem* mul_cast_comm
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_nonneg
- \+ *theorem* cast_le
- \+ *theorem* cast_lt
- \+ *theorem* cast_pos
- \+ *theorem* cast_inj
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero
- \+ *theorem* cast_id

modified data/num/basic.lean

modified data/num/bitwise.lean

modified data/num/lemmas.lean

deleted data/num/norm_num.lean
- \- *lemma* pow_bit0
- \- *lemma* pow_bit0_helper
- \- *lemma* pow_bit1
- \- *lemma* pow_bit1_helper
- \- *lemma* pow_one
- \- *lemma* pow_zero
- \- *lemma* pow_eq_pow_nat
- \- *lemma* pow_eq_pow_nat_helper
- \- *lemma* zero_le_bit0
- \- *lemma* zero_le_bit1
- \- *lemma* zero_le_zero
- \- *lemma* zero_le_one
- \- *lemma* one_le_bit0
- \- *lemma* one_le_bit1
- \- *lemma* one_le_one
- \- *lemma* bit0_le_zero
- \- *lemma* bit0_le_one
- \- *lemma* bit1_le_bit0
- \- *lemma* bit1_le_zero
- \- *lemma* bit1_le_one
- \- *lemma* one_le_denote
- \- *lemma* denote_add1
- \- *lemma* bit0_le_bit0
- \- *lemma* denote_le_denote_of_pos_num_le
- \- *lemma* zero_le_denote
- \- *lemma* denote_le_denote_of_num_le
- \- *lemma* denote_le_denote_of_znum_le
- \- *def* add1
- \- *def* add_n
- \- *def* pos_le
- \- *def* num_le
- \- *def* znum_le
- \- *def* znum.to_pos
- \- *def* znum.to_neg

modified data/option.lean
- \+/\- *lemma* mem_def
- \+/\- *lemma* some_inj
- \+ *lemma* none_ne_some
- \+ *lemma* bind_none
- \+/\- *lemma* bind_some
- \+ *lemma* bind_eq_some
- \+ *lemma* map_none
- \+ *lemma* map_some
- \+ *lemma* map_eq_some
- \+ *lemma* is_some_iff_exists
- \+/\- *lemma* guard_eq_some
- \+/\- *lemma* mem_def
- \+/\- *lemma* some_inj
- \+/\- *lemma* bind_some
- \+/\- *lemma* guard_eq_some
- \+/\- *def* iget
- \+/\- *def* guard
- \+/\- *def* filter
- \+/\- *def* iget
- \+/\- *def* guard
- \+/\- *def* filter

modified data/rat.lean
- \+ *theorem* num_dvd
- \+ *theorem* denom_dvd
- \+ *theorem* of_int_eq_mk
- \+/\- *theorem* coe_int_eq_mk
- \+ *theorem* coe_int_eq_of_int
- \+ *theorem* mk_eq_div
- \+ *theorem* cast_of_int
- \+ *theorem* cast_coe_int
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_one
- \+ *theorem* mul_cast_comm
- \+ *theorem* cast_mk_of_ne_zero
- \+ *theorem* cast_add_of_ne_zero
- \+ *theorem* cast_neg
- \+ *theorem* cast_sub_of_ne_zero
- \+ *theorem* cast_mul_of_ne_zero
- \+ *theorem* cast_mk
- \+ *theorem* cast_add
- \+ *theorem* cast_sub
- \+ *theorem* cast_mul
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_nonneg
- \+ *theorem* cast_le
- \+ *theorem* cast_lt
- \+ *theorem* cast_inj
- \+ *theorem* cast_nonpos
- \+ *theorem* cast_pos
- \+ *theorem* cast_lt_zero
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero
- \+ *theorem* cast_id
- \- *theorem* linear_order_cases_on_eq
- \- *theorem* linear_order_cases_on_lt
- \- *theorem* linear_order_cases_on_gt
- \- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+/\- *theorem* coe_int_eq_mk
- \- *theorem* coe_nat_rat_eq_mk
- \- *theorem* coe_int_inj
- \- *theorem* coe_int_add
- \- *theorem* coe_int_neg
- \- *theorem* coe_int_sub
- \- *theorem* coe_int_mul
- \- *theorem* coe_int_one
- \- *theorem* coe_int_le
- \- *theorem* coe_int_lt
- \- *def* linear_order_cases_on

modified data/set/enumerate.lean

deleted meta/expr.lean



## [2017-10-17 00:02:03-04:00](https://github.com/leanprover-community/mathlib/commit/2e7651a)
feat(data/num): add tactics for evaluating arithmetic expressions made of literals, including `x \le y` and `x ^ y`
#### Estimated changes
modified data/num/basic.lean

modified data/num/lemmas.lean

created data/num/norm_num.lean
- \+ *lemma* pow_bit0
- \+ *lemma* pow_bit0_helper
- \+ *lemma* pow_bit1
- \+ *lemma* pow_bit1_helper
- \+ *lemma* pow_one
- \+ *lemma* pow_zero
- \+ *lemma* pow_eq_pow_nat
- \+ *lemma* pow_eq_pow_nat_helper
- \+ *lemma* zero_le_bit0
- \+ *lemma* zero_le_bit1
- \+ *lemma* zero_le_zero
- \+ *lemma* zero_le_one
- \+ *lemma* one_le_bit0
- \+ *lemma* one_le_bit1
- \+ *lemma* one_le_one
- \+ *lemma* bit0_le_zero
- \+ *lemma* bit0_le_one
- \+ *lemma* bit1_le_bit0
- \+ *lemma* bit1_le_zero
- \+ *lemma* bit1_le_one
- \+ *lemma* one_le_denote
- \+ *lemma* denote_add1
- \+ *lemma* bit0_le_bit0
- \+ *lemma* denote_le_denote_of_pos_num_le
- \+ *lemma* zero_le_denote
- \+ *lemma* denote_le_denote_of_num_le
- \+ *lemma* denote_le_denote_of_znum_le
- \+ *def* add1
- \+ *def* add_n
- \+ *def* pos_le
- \+ *def* num_le
- \+ *def* znum_le
- \+ *def* znum.to_pos
- \+ *def* znum.to_neg

created meta/expr.lean



## [2017-10-15 02:26:24-04:00](https://github.com/leanprover-community/mathlib/commit/5ad8020)
Merge remote-tracking branch 'minchaowu/master'
#### Estimated changes
modified analysis/real.lean

modified analysis/topology/continuity.lean

modified analysis/topology/infinite_sum.lean

modified analysis/topology/uniform_space.lean

modified data/set/basic.lean
- \+ *theorem* preimage_diff
- \+ *theorem* image_subset_iff
- \+ *theorem* inter_preimage_subset
- \+ *theorem* union_preimage_subset
- \+ *theorem* subset_image_union
- \- *theorem* image_subset_iff_subset_preimage

created data/set/function.lean
- \+ *lemma* injective_iff_inj_on_univ
- \+ *lemma* surjective_iff_surj_on_univ
- \+ *lemma* image_eq_of_maps_to_of_surj_on
- \+ *lemma* maps_to_of_bij_on
- \+ *lemma* inj_on_of_bij_on
- \+ *lemma* surj_on_of_bij_on
- \+ *lemma* bij_on.mk
- \+ *lemma* image_eq_of_bij_on
- \+ *lemma* bijective_iff_bij_on_univ
- \+ *theorem* maps_to_of_eq_on
- \+ *theorem* maps_to_comp
- \+ *theorem* maps_to_univ_univ
- \+ *theorem* image_subset_of_maps_to_of_subset
- \+ *theorem* image_subset_of_maps_to
- \+ *theorem* inj_on_empty
- \+ *theorem* inj_on_of_eq_on
- \+ *theorem* inj_on_comp
- \+ *theorem* inj_on_of_inj_on_of_subset
- \+ *theorem* surj_on_of_eq_on
- \+ *theorem* surj_on_comp
- \+ *theorem* bij_on_of_eq_on
- \+ *theorem* bij_on_comp
- \+ *theorem* left_inv_on_of_eq_on_left
- \+ *theorem* left_inv_on_of_eq_on_right
- \+ *theorem* inj_on_of_left_inv_on
- \+ *theorem* left_inv_on_comp
- \+ *theorem* right_inv_on_of_eq_on_left
- \+ *theorem* right_inv_on_of_eq_on_right
- \+ *theorem* surj_on_of_right_inv_on
- \+ *theorem* right_inv_on_comp
- \+ *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \+ *theorem* eq_on_of_left_inv_of_right_inv
- \+ *theorem* left_inv_on_of_surj_on_right_inv_on
- \+ *theorem* bij_on_of_inv_on
- \+ *def* maps_to
- \+ *def* inj_on
- \+ *def* surj_on
- \+ *def* bij_on
- \+ *def* left_inv_on
- \+ *def* right_inv_on
- \+ *def* inv_on

modified order/filter.lean

modified order/galois_connection.lean



## [2017-10-15 01:58:58-04:00](https://github.com/leanprover-community/mathlib/commit/8f4327a)
feat(*): working on list/basic, robusting simp proofs
#### Estimated changes
modified algebra/big_operators.lean
- \+ *theorem* prod_repeat
- \- *theorem* prod_replicate

modified algebra/field.lean
- \+ *lemma* division_ring.neg_inv

modified algebra/functions.lean
- \+ *lemma* lt_max_iff

modified analysis/ennreal.lean

modified analysis/limits.lean

modified analysis/measure_theory/borel_space.lean

modified analysis/measure_theory/measure_space.lean

modified analysis/measure_theory/outer_measure.lean

modified analysis/metric_space.lean

modified analysis/of_nat.lean

modified analysis/real.lean
- \+ *lemma* of_rat_injective
- \+ *lemma* of_rat_inj
- \+/\- *lemma* uniform_embedding_of_rat
- \+ *lemma* of_rat_lt
- \+/\- *lemma* uniform_embedding_of_rat
- \- *lemma* of_rat_lt_of_rat

modified analysis/topology/continuity.lean

modified analysis/topology/infinite_sum.lean

modified analysis/topology/topological_space.lean

modified analysis/topology/topological_structures.lean

modified analysis/topology/uniform_space.lean

modified data/bool.lean
- \+ *theorem* coe_sort_tt
- \+ *theorem* coe_sort_ff
- \+ *theorem* to_bool_true
- \+ *theorem* to_bool_false
- \+ *theorem* to_bool_bool
- \+/\- *theorem* bor_inl
- \+/\- *theorem* bor_inr
- \- *theorem* coe_tt
- \- *theorem* band_tt
- \- *theorem* tt_band
- \- *theorem* band_ff
- \- *theorem* ff_band
- \- *theorem* bor_tt
- \- *theorem* tt_bor
- \- *theorem* bor_ff
- \- *theorem* ff_bor
- \- *theorem* band_eq_tt
- \- *theorem* band_eq_ff
- \- *theorem* bor_eq_tt
- \- *theorem* bor_eq_ff
- \- *theorem* or_of_bor_eq
- \+/\- *theorem* bor_inl
- \+/\- *theorem* bor_inr
- \- *theorem* band_self
- \- *theorem* bnot_bnot
- \- *theorem* ff_bxor_ff
- \- *theorem* ff_bxor_tt
- \- *theorem* tt_bxor_ff
- \- *theorem* tt_bxor_tt
- \- *theorem* bxor_self
- \- *theorem* bxor_ff
- \- *theorem* bxor_tt
- \- *theorem* ff_bxor
- \- *theorem* tt_bxor
- \- *def* bxor

modified data/encodable.lean
- \+ *theorem* encode_injective

modified data/equiv.lean
- \+ *def* list_equiv_of_equiv
- \+ *def* list_nat_equiv_nat
- \+ *def* list_equiv_self_of_equiv_nat

modified data/finset/basic.lean
- \- *lemma* lt_max_iff
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+ *theorem* mem_to_finset_of_mem
- \+/\- *theorem* mem_to_finset
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* mem_insert
- \+ *theorem* mem_insert_self
- \+/\- *theorem* mem_singleton_self
- \+ *theorem* mem_union
- \+/\- *theorem* mem_inter
- \+ *theorem* mem_inter_of_mem
- \+ *theorem* mem_erase
- \+ *theorem* mem_filter
- \+/\- *theorem* mem_sdiff_iff
- \+ *theorem* mem_range
- \+ *theorem* range_zero
- \+ *theorem* range_succ
- \+ *theorem* not_mem_range_self
- \+ *theorem* range_subset
- \+ *theorem* exists_nat_subset_range
- \+ *theorem* exists_mem_insert
- \+ *theorem* forall_mem_insert
- \+ *theorem* card_range
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* mem_to_finset
- \- *theorem* mem_to_finset_iff
- \+/\- *theorem* not_mem_empty
- \- *theorem* mem_empty_iff
- \- *theorem* mem_insert_iff
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_singleton_self
- \- *theorem* mem_union_iff
- \- *theorem* mem_inter_iff
- \+/\- *theorem* mem_inter
- \- *theorem* mem_erase_iff
- \- *theorem* mem_filter_iff
- \+/\- *theorem* mem_sdiff_iff
- \- *theorem* lt_of_mem_upto
- \- *theorem* mem_upto_succ_of_mem_upto
- \- *theorem* mem_upto_of_lt
- \- *theorem* mem_upto_iff
- \- *theorem* upto_zero
- \- *theorem* upto_succ
- \- *theorem* not_mem_upto
- \- *theorem* upto_subset_upto_iff
- \- *theorem* exists_nat_subset_upto
- \- *theorem* exists_mem_insert_iff
- \- *theorem* forall_mem_insert_iff
- \- *theorem* card_upto
- \+ *def* range
- \- *def* upto

modified data/finset/fold.lean
- \- *lemma* heq_iff_eq

modified data/hash_map.lean
- \+/\- *theorem* mem_as_list
- \+/\- *theorem* find_aux_iff
- \+/\- *theorem* contains_aux_iff
- \+/\- *theorem* mem_as_list
- \+/\- *theorem* find_aux_iff
- \+/\- *theorem* contains_aux_iff

modified data/list/basic.lean
- \- *lemma* concat_eq_append
- \- *lemma* length_concat
- \- *lemma* map_concat
- \- *lemma* mem_bind_iff
- \- *lemma* exists_of_mem_bind
- \- *lemma* mem_bind
- \- *lemma* foldr_eta
- \- *lemma* scanr_nil
- \- *lemma* scanr_aux_cons
- \- *lemma* scanr_cons
- \- *lemma* span_eq_take_drop
- \- *lemma* take_while_append_drop
- \- *lemma* prefix_append
- \- *lemma* suffix_append
- \- *lemma* infix_append
- \- *lemma* prefix_refl
- \- *lemma* suffix_refl
- \- *lemma* infix_of_prefix
- \- *lemma* infix_of_suffix
- \- *lemma* infix_refl
- \- *lemma* sublist_of_infix
- \- *lemma* length_le_of_infix
- \- *lemma* eq_nil_of_infix_nil
- \- *lemma* eq_nil_of_prefix_nil
- \- *lemma* eq_nil_of_suffix_nil
- \- *lemma* infix_iff_prefix_suffix
- \- *lemma* mem_inits
- \- *lemma* mem_tails
- \- *lemma* sublists_aux_eq_foldl
- \- *lemma* sublists_aux_cons_cons
- \- *lemma* mem_sublists
- \+/\- *theorem* head_eq_of_cons_eq
- \+/\- *theorem* tail_eq_of_cons_eq
- \+/\- *theorem* cons_inj
- \+ *theorem* cons_inj'
- \+/\- *theorem* eq_nil_of_forall_not_mem
- \+ *theorem* mem_singleton_self
- \+ *theorem* eq_of_mem_singleton
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_of_mem_cons_of_mem
- \+/\- *theorem* not_mem_append
- \+/\- *theorem* length_pos_of_mem
- \+ *theorem* exists_mem_of_length_pos
- \+/\- *theorem* mem_split
- \+/\- *theorem* mem_of_ne_of_mem
- \+/\- *theorem* ne_of_not_mem_cons
- \+/\- *theorem* not_mem_of_not_mem_cons
- \+/\- *theorem* not_mem_cons_of_ne_of_not_mem
- \+/\- *theorem* ne_and_not_mem_of_not_mem_cons
- \+ *theorem* mem_map_of_mem
- \+/\- *theorem* exists_of_mem_map
- \+/\- *theorem* mem_map
- \+ *theorem* mem_map_of_inj
- \+/\- *theorem* mem_join
- \+/\- *theorem* exists_of_mem_join
- \+ *theorem* mem_join_of_mem
- \+ *theorem* mem_bind
- \+ *theorem* exists_of_mem_bind
- \+ *theorem* mem_bind_of_mem
- \+/\- *theorem* subset_app_of_subset_left
- \+/\- *theorem* subset_app_of_subset_right
- \+/\- *theorem* cons_subset_of_subset_of_mem
- \+/\- *theorem* app_subset_of_subset_of_subset
- \+/\- *theorem* eq_nil_of_subset_nil
- \+ *theorem* eq_nil_iff_forall_not_mem
- \+ *theorem* append_inj'
- \+ *theorem* append_inj_left'
- \+ *theorem* append_inj_right'
- \+ *theorem* append_left_cancel
- \+ *theorem* append_right_cancel
- \+ *theorem* eq_of_mem_repeat
- \+ *theorem* eq_repeat_of_mem
- \+ *theorem* eq_repeat'
- \+ *theorem* eq_repeat
- \+ *theorem* repeat_subset_singleton
- \+ *theorem* map_const
- \+ *theorem* eq_of_mem_map_const
- \+ *theorem* concat_eq_append
- \+ *theorem* length_concat
- \+ *theorem* reverse_cons'
- \+/\- *theorem* mem_reverse
- \+ *theorem* map_concat
- \+/\- *theorem* eq_nil_of_map_eq_nil
- \+ *theorem* nil_map₂
- \+ *theorem* map₂_nil
- \+/\- *theorem* sublist_app_of_sublist_left
- \+/\- *theorem* sublist_app_of_sublist_right
- \+ *theorem* cons_sublist_cons_iff
- \+ *theorem* append_sublist_append_left
- \+ *theorem* append_sublist_append_of_sublist_right
- \+ *theorem* reverse_sublist
- \+ *theorem* reverse_sublist_iff
- \+ *theorem* append_sublist_append_right
- \+ *theorem* singleton_sublist
- \+ *theorem* repeat_sublist_repeat
- \+ *theorem* eq_of_sublist_of_length_eq
- \+ *theorem* sublist_antisymm
- \+ *theorem* foldl_nil
- \+ *theorem* foldl_cons
- \+ *theorem* foldr_nil
- \+ *theorem* foldr_cons
- \+ *theorem* foldl_append
- \+ *theorem* foldr_append
- \+ *theorem* foldl_reverse
- \+ *theorem* foldr_reverse
- \+ *theorem* foldr_eta
- \+ *theorem* scanr_nil
- \+ *theorem* scanr_aux_cons
- \+ *theorem* scanr_cons
- \+ *theorem* forall_mem_nil
- \+ *theorem* forall_mem_cons'
- \+ *theorem* forall_mem_cons
- \+ *theorem* forall_mem_of_forall_mem_cons
- \+ *theorem* not_exists_mem_nil
- \+ *theorem* exists_mem_cons_of
- \+ *theorem* exists_mem_cons_of_exists
- \+ *theorem* or_exists_of_exists_mem_cons
- \+ *theorem* exists_mem_cons_iff
- \+ *theorem* all_nil
- \+ *theorem* all_cons
- \+ *theorem* all_iff_forall
- \+ *theorem* all_iff_forall_prop
- \+ *theorem* any_nil
- \+ *theorem* any_cons
- \+ *theorem* any_iff_exists
- \+ *theorem* any_iff_exists_prop
- \+ *theorem* any_of_mem
- \+ *theorem* find_nil
- \+ *theorem* find_cons_of_pos
- \+ *theorem* find_cons_of_neg
- \+ *theorem* find_eq_none
- \+ *theorem* find_some
- \+ *theorem* find_mem
- \+ *theorem* filter_map_nil
- \+ *theorem* filter_map_cons_none
- \+ *theorem* filter_map_cons_some
- \+ *theorem* filter_map_eq_map
- \+ *theorem* filter_map_eq_filter
- \+ *theorem* filter_map_filter_map
- \+ *theorem* map_filter_map
- \+ *theorem* filter_map_map
- \+ *theorem* filter_filter_map
- \+ *theorem* filter_map_filter
- \+ *theorem* filter_map_some
- \+ *theorem* mem_filter_map
- \+ *theorem* map_filter_map_of_inv
- \+ *theorem* filter_map_sublist_filter_map
- \+/\- *theorem* filter_subset
- \+/\- *theorem* of_mem_filter
- \+/\- *theorem* mem_of_mem_filter
- \+/\- *theorem* mem_filter_of_mem
- \+ *theorem* mem_filter
- \+ *theorem* filter_eq_self
- \+ *theorem* filter_eq_nil
- \+ *theorem* filter_sublist_filter
- \+ *theorem* span_eq_take_drop
- \+ *theorem* take_while_append_drop
- \+ *theorem* countp_nil
- \+ *theorem* countp_cons_of_pos
- \+ *theorem* countp_cons_of_neg
- \+ *theorem* countp_eq_length_filter
- \+ *theorem* countp_append
- \+ *theorem* exists_mem_of_countp_pos
- \+ *theorem* countp_pos_of_mem
- \+ *theorem* countp_le_of_sublist
- \+ *theorem* count_le_of_sublist
- \+/\- *theorem* count_cons_ge_count
- \+/\- *theorem* count_append
- \+/\- *theorem* mem_of_count_pos
- \+/\- *theorem* count_pos_of_mem
- \+ *theorem* count_pos
- \+ *theorem* count_repeat
- \+ *theorem* le_count_iff_repeat_sublist
- \+ *theorem* prefix_append
- \+ *theorem* suffix_append
- \+ *theorem* infix_append
- \+ *theorem* prefix_refl
- \+ *theorem* suffix_refl
- \+ *theorem* suffix_cons
- \+ *theorem* prefix_concat
- \+ *theorem* infix_of_prefix
- \+ *theorem* infix_of_suffix
- \+ *theorem* infix_refl
- \+ *theorem* is_prefix.trans
- \+ *theorem* is_suffix.trans
- \+ *theorem* is_infix.trans
- \+ *theorem* sublist_of_infix
- \+ *theorem* sublist_of_prefix
- \+ *theorem* sublist_of_suffix
- \+ *theorem* length_le_of_infix
- \+ *theorem* eq_nil_of_infix_nil
- \+ *theorem* eq_nil_of_prefix_nil
- \+ *theorem* eq_nil_of_suffix_nil
- \+ *theorem* infix_iff_prefix_suffix
- \+ *theorem* eq_of_infix_of_length_eq
- \+ *theorem* eq_of_prefix_of_length_eq
- \+ *theorem* eq_of_suffix_of_length_eq
- \+ *theorem* mem_inits
- \+ *theorem* mem_tails
- \+ *theorem* sublists_aux_eq_foldl
- \+ *theorem* sublists_aux_cons_cons
- \+ *theorem* mem_sublists
- \+ *theorem* insert_nil
- \+ *theorem* insert.def
- \+ *theorem* insert_of_mem
- \+ *theorem* insert_of_not_mem
- \+ *theorem* mem_insert_iff
- \+ *theorem* suffix_insert
- \+ *theorem* mem_insert_self
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* length_insert_of_mem
- \+ *theorem* length_insert_of_not_mem
- \+ *theorem* erase_nil
- \+ *theorem* erase_cons
- \+ *theorem* erase_cons_head
- \+ *theorem* erase_cons_tail
- \+ *theorem* erase_of_not_mem
- \+ *theorem* exists_erase_eq
- \+ *theorem* length_erase_of_mem
- \+ *theorem* erase_append_left
- \+ *theorem* erase_append_right
- \+ *theorem* erase_sublist
- \+ *theorem* erase_subset
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* zip_cons_cons
- \+ *theorem* zip_nil_left
- \+ *theorem* zip_nil_right
- \+ *theorem* unzip_nil
- \+ *theorem* unzip_cons
- \+ *theorem* zip_unzip
- \+ *theorem* nil_product
- \+ *theorem* product_cons
- \+ *theorem* product_nil
- \+ *theorem* mem_product
- \+ *theorem* length_product
- \+ *theorem* disjoint.symm
- \+ *theorem* disjoint_comm
- \+ *theorem* disjoint_left
- \+ *theorem* disjoint_right
- \+ *theorem* disjoint_iff_ne
- \+ *theorem* disjoint_of_subset_left
- \+ *theorem* disjoint_of_subset_right
- \+ *theorem* disjoint_of_disjoint_cons_left
- \+ *theorem* disjoint_of_disjoint_cons_right
- \+ *theorem* disjoint_nil_left
- \+ *theorem* singleton_disjoint
- \+ *theorem* disjoint_singleton
- \+ *theorem* disjoint_append_left
- \+ *theorem* disjoint_append_right
- \+ *theorem* disjoint_cons_left
- \+ *theorem* disjoint_cons_right
- \+ *theorem* disjoint_append_of_disjoint_left
- \+ *theorem* disjoint_of_disjoint_append_left_left
- \+ *theorem* disjoint_of_disjoint_append_left_right
- \+ *theorem* disjoint_of_disjoint_append_right_left
- \+ *theorem* disjoint_of_disjoint_append_right_right
- \+ *theorem* nil_union
- \+ *theorem* cons_union
- \+ *theorem* mem_union
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* sublist_suffix_of_union
- \+ *theorem* suffix_union_right
- \+ *theorem* union_sublist_append
- \+ *theorem* forall_mem_union
- \+ *theorem* forall_mem_of_forall_mem_union_left
- \+ *theorem* forall_mem_of_forall_mem_union_right
- \+ *theorem* inter_nil
- \+ *theorem* inter_cons_of_mem
- \+ *theorem* inter_cons_of_not_mem
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter_of_mem_of_mem
- \+ *theorem* mem_inter
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* inter_eq_nil_iff_disjoint
- \+ *theorem* forall_mem_inter_of_forall_left
- \+ *theorem* forall_mem_inter_of_forall_right
- \+ *theorem* pairwise_cons
- \+ *theorem* rel_of_pairwise_cons
- \+ *theorem* pairwise_of_pairwise_cons
- \+ *theorem* pairwise.imp
- \+ *theorem* pairwise.iff
- \+ *theorem* pairwise_of_forall
- \+ *theorem* pairwise.iff_mem
- \+ *theorem* pairwise_of_sublist
- \+ *theorem* pairwise_singleton
- \+ *theorem* pairwise_pair
- \+ *theorem* pairwise_append
- \+ *theorem* pairwise_app_comm
- \+ *theorem* pairwise_middle
- \+ *theorem* pairwise_map
- \+ *theorem* pairwise_of_pairwise_map
- \+ *theorem* pairwise_map_of_pairwise
- \+ *theorem* pairwise_filter_map
- \+ *theorem* pairwise_filter_map_of_pairwise
- \+ *theorem* pairwise_filter
- \+ *theorem* pairwise_filter_of_pairwise
- \+ *theorem* pairwise_join
- \+ *theorem* pairwise_reverse
- \+ *theorem* pw_filter_nil
- \+ *theorem* pw_filter_cons_of_pos
- \+ *theorem* pw_filter_cons_of_neg
- \+ *theorem* pw_filter_sublist
- \+ *theorem* pw_filter_subset
- \+ *theorem* pairwise_pw_filter
- \+ *theorem* pw_filter_eq_self
- \+ *theorem* forall_mem_pw_filter
- \+ *theorem* chain_cons
- \+ *theorem* rel_of_chain_cons
- \+ *theorem* chain_of_chain_cons
- \+ *theorem* chain.imp
- \+ *theorem* chain.iff
- \+ *theorem* chain.iff_mem
- \+ *theorem* chain_singleton
- \+ *theorem* chain_split
- \+ *theorem* chain_map
- \+ *theorem* chain_of_chain_map
- \+ *theorem* chain_map_of_chain
- \+ *theorem* chain_of_pairwise
- \+ *theorem* chain_iff_pairwise
- \+ *theorem* forall_mem_ne
- \+ *theorem* nodup_nil
- \+ *theorem* nodup_cons
- \+ *theorem* nodup_cons_of_nodup
- \+ *theorem* nodup_singleton
- \+ *theorem* nodup_of_nodup_cons
- \+ *theorem* not_mem_of_nodup_cons
- \+ *theorem* not_nodup_cons_of_mem
- \+ *theorem* nodup_of_sublist
- \+ *theorem* not_nodup_pair
- \+ *theorem* nodup_iff_sublist
- \+ *theorem* nodup_iff_count_le_one
- \+ *theorem* count_eq_one_of_mem
- \+ *theorem* nodup_of_nodup_append_left
- \+ *theorem* nodup_of_nodup_append_right
- \+ *theorem* nodup_append
- \+ *theorem* disjoint_of_nodup_append
- \+ *theorem* nodup_append_of_nodup
- \+ *theorem* nodup_app_comm
- \+ *theorem* nodup_middle
- \+ *theorem* nodup_of_nodup_map
- \+ *theorem* nodup_map_on
- \+ *theorem* nodup_map
- \+ *theorem* nodup_filter
- \+ *theorem* nodup_reverse
- \+ *theorem* nodup_erase_eq_filter
- \+ *theorem* nodup_erase_of_nodup
- \+ *theorem* mem_erase_iff_of_nodup
- \+ *theorem* mem_erase_of_nodup
- \+ *theorem* nodup_join
- \+ *theorem* nodup_bind
- \+ *theorem* nodup_product
- \+ *theorem* nodup_filter_map
- \+ *theorem* nodup_concat
- \+ *theorem* nodup_insert
- \+ *theorem* nodup_union
- \+ *theorem* nodup_inter_of_nodup
- \+ *theorem* erase_dup_nil
- \+ *theorem* erase_dup_cons_of_mem'
- \+ *theorem* erase_dup_cons_of_not_mem'
- \+ *theorem* mem_erase_dup
- \+ *theorem* erase_dup_cons_of_mem
- \+ *theorem* erase_dup_cons_of_not_mem
- \+ *theorem* erase_dup_sublist
- \+ *theorem* erase_dup_subset
- \+ *theorem* subset_erase_dup
- \+ *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_eq_self
- \+ *theorem* erase_dup_append
- \+ *theorem* length_range'
- \+ *theorem* mem_range'
- \+ *theorem* chain_succ_range'
- \+ *theorem* chain_lt_range'
- \+ *theorem* pairwise_lt_range'
- \+ *theorem* nodup_range'
- \+ *theorem* range'_append
- \+ *theorem* range'_sublist_right
- \+ *theorem* range'_subset_right
- \+ *theorem* range'_concat
- \+ *theorem* range_core_range'
- \+ *theorem* range_eq_range'
- \+ *theorem* length_range
- \+ *theorem* pairwise_lt_range
- \+ *theorem* nodup_range
- \+ *theorem* range_sublist
- \+ *theorem* range_subset
- \+ *theorem* mem_range
- \+ *theorem* not_mem_range_self
- \+ *theorem* iota_eq_reverse_range'
- \+ *theorem* length_iota
- \+ *theorem* pairwise_gt_iota
- \+ *theorem* nodup_iota
- \+ *theorem* mem_iota
- \+/\- *theorem* head_eq_of_cons_eq
- \+/\- *theorem* tail_eq_of_cons_eq
- \+/\- *theorem* cons_inj
- \- *theorem* append_right_inj
- \+/\- *theorem* eq_nil_of_forall_not_mem
- \+/\- *theorem* mem_singleton
- \- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_of_mem_cons_of_mem
- \+/\- *theorem* not_mem_append
- \+/\- *theorem* length_pos_of_mem
- \+/\- *theorem* mem_split
- \+/\- *theorem* mem_of_ne_of_mem
- \+/\- *theorem* ne_of_not_mem_cons
- \+/\- *theorem* not_mem_of_not_mem_cons
- \+/\- *theorem* not_mem_cons_of_ne_of_not_mem
- \+/\- *theorem* ne_and_not_mem_of_not_mem_cons
- \+/\- *theorem* mem_reverse
- \+/\- *theorem* mem_map
- \+/\- *theorem* exists_of_mem_map
- \- *theorem* mem_map_iff
- \- *theorem* mem_join_iff
- \+/\- *theorem* exists_of_mem_join
- \+/\- *theorem* mem_join
- \+/\- *theorem* subset_app_of_subset_left
- \+/\- *theorem* subset_app_of_subset_right
- \+/\- *theorem* cons_subset_of_subset_of_mem
- \+/\- *theorem* app_subset_of_subset_of_subset
- \+/\- *theorem* eq_nil_of_subset_nil
- \+/\- *theorem* sublist_app_of_sublist_left
- \+/\- *theorem* sublist_app_of_sublist_right
- \+/\- *theorem* eq_nil_of_map_eq_nil
- \- *theorem* eq_of_map_const
- \+/\- *theorem* filter_subset
- \+/\- *theorem* of_mem_filter
- \+/\- *theorem* mem_of_mem_filter
- \+/\- *theorem* mem_filter_of_mem
- \- *theorem* mem_filter_iff
- \+/\- *theorem* count_cons_ge_count
- \+/\- *theorem* count_append
- \+/\- *theorem* mem_of_count_pos
- \+/\- *theorem* count_pos_of_mem
- \- *theorem* mem_iff_count_pos
- \+/\- *def* concat
- \+/\- *def* inth
- \+ *def* prod
- \+/\- *def* sum
- \+/\- *def* find
- \+/\- *def* find_indexes_aux
- \+/\- *def* find_indexes
- \+/\- *def* indexes_of
- \+ *def* countp
- \+/\- *def* count
- \+/\- *def* inits
- \+/\- *def* tails
- \+ *def* product
- \+ *def* disjoint
- \+ *def* pw_filter
- \+ *def* nodup
- \+ *def* erase_dup
- \+ *def* range'
- \+/\- *def* concat
- \+/\- *def* inth
- \+/\- *def* find
- \+/\- *def* find_indexes_aux
- \+/\- *def* find_indexes
- \+/\- *def* indexes_of
- \+/\- *def* sum
- \+/\- *def* count
- \+/\- *def* inits
- \+/\- *def* tails

deleted data/list/comb.lean
- \- *theorem* foldl_nil
- \- *theorem* foldl_cons
- \- *theorem* foldr_nil
- \- *theorem* foldr_cons
- \- *theorem* foldl_append
- \- *theorem* foldr_append
- \- *theorem* foldl_reverse
- \- *theorem* foldr_reverse
- \- *theorem* length_replicate
- \- *theorem* map₂_nil1
- \- *theorem* map₂_nil2
- \- *theorem* length_map₂
- \- *theorem* all_nil
- \- *theorem* all_cons
- \- *theorem* all_eq_tt_of_forall
- \- *theorem* forall_mem_eq_tt_of_all_eq_tt
- \- *theorem* all_eq_tt_iff
- \- *theorem* any_nil
- \- *theorem* any_cons
- \- *theorem* any_of_mem
- \- *theorem* exists_of_any_eq_tt
- \- *theorem* any_eq_tt_iff
- \- *theorem* forall_mem_nil
- \- *theorem* forall_mem_cons
- \- *theorem* of_forall_mem_cons
- \- *theorem* forall_mem_of_forall_mem_cons
- \- *theorem* forall_mem_cons_iff
- \- *theorem* not_exists_mem_nil
- \- *theorem* exists_mem_cons_of
- \- *theorem* exists_mem_cons_of_exists
- \- *theorem* or_exists_of_exists_mem_cons
- \- *theorem* exists_mem_cons_iff
- \- *theorem* zip_cons_cons
- \- *theorem* zip_nil_left
- \- *theorem* zip_nil_right
- \- *theorem* unzip_nil
- \- *theorem* unzip_cons'
- \- *theorem* unzip_cons
- \- *theorem* zip_unzip
- \- *theorem* length_mapAccumR
- \- *theorem* length_mapAccumR₂
- \- *theorem* nil_product
- \- *theorem* product_cons
- \- *theorem* product_nil
- \- *theorem* eq_of_mem_map_pair₁
- \- *theorem* mem_of_mem_map_pair₁
- \- *theorem* mem_product
- \- *theorem* mem_of_mem_product_left
- \- *theorem* mem_of_mem_product_right
- \- *theorem* length_product
- \- *theorem* dmap_nil
- \- *theorem* dmap_cons_of_pos
- \- *theorem* dmap_cons_of_neg
- \- *theorem* mem_dmap
- \- *theorem* exists_of_mem_dmap
- \- *theorem* map_dmap_of_inv_of_pos
- \- *theorem* mem_of_dinj_of_mem_dmap
- \- *theorem* not_mem_dmap_of_dinj_of_not_mem
- \- *def* replicate
- \- *def* map₂
- \- *def* mapAccumR
- \- *def* mapAccumR₂
- \- *def* flat
- \- *def* product
- \- *def* dinj₁
- \- *def* dinj
- \- *def* dmap
- \- *def* list_equiv_of_equiv
- \- *def* list_nat_equiv_nat
- \- *def* list_equiv_self_of_equiv_nat

modified data/list/default.lean

modified data/list/perm.lean
- \+ *theorem* perm.eqv
- \+/\- *theorem* perm_app_left
- \+/\- *theorem* perm_app_right
- \+/\- *theorem* perm_app
- \+/\- *theorem* perm_app_cons
- \+/\- *theorem* perm_middle
- \+/\- *theorem* perm_cons_app
- \+ *theorem* concat_perm
- \+ *theorem* perm_length
- \+/\- *theorem* eq_nil_of_perm_nil
- \+/\- *theorem* not_perm_nil_cons
- \+ *theorem* reverse_perm
- \+ *theorem* perm_repeat
- \+/\- *theorem* perm_erase
- \+/\- *theorem* xswap
- \+ *theorem* perm_filter_map
- \+/\- *theorem* perm_filter
- \+ *theorem* exists_perm_sublist
- \+ *theorem* perm_countp
- \+ *theorem* perm_count
- \+/\- *theorem* perm_inv_core
- \+/\- *theorem* perm_cons_inv
- \+ *theorem* perm_cons
- \+ *theorem* perm_app_left_iff
- \+/\- *theorem* perm_app_inv_right
- \+ *theorem* exists_sublist_perm_of_subset_nodup
- \+/\- *theorem* perm_ext
- \+ *theorem* erase_perm_erase
- \+ *theorem* cons_perm_iff_perm_erase
- \+ *theorem* perm_iff_count
- \+/\- *theorem* perm_erase_dup_of_perm
- \+/\- *theorem* perm_insert
- \+ *theorem* perm_insert_swap
- \+/\- *theorem* perm_union_left
- \+/\- *theorem* perm_union_right
- \+/\- *theorem* perm_union
- \+/\- *theorem* perm_inter_left
- \+/\- *theorem* perm_inter_right
- \+/\- *theorem* perm_inter
- \+ *theorem* perm_pairwise
- \+ *theorem* perm_nodup
- \+ *theorem* perm_bind_left
- \+ *theorem* perm_bind_right
- \+/\- *theorem* perm_product_left
- \+/\- *theorem* perm_product_right
- \+/\- *theorem* perm_product
- \- *theorem* eqv
- \- *theorem* not_mem_of_perm
- \+/\- *theorem* perm_app_left
- \+/\- *theorem* perm_app_right
- \+/\- *theorem* perm_app
- \+/\- *theorem* perm_app_cons
- \+/\- *theorem* perm_cons_app
- \- *theorem* perm_cons_app_simp
- \- *theorem* length_eq_length_of_perm
- \+/\- *theorem* eq_nil_of_perm_nil
- \+/\- *theorem* not_perm_nil_cons
- \- *theorem* perm_rev
- \- *theorem* perm_rev_simp
- \+/\- *theorem* perm_middle
- \- *theorem* perm_middle_simp
- \+/\- *theorem* perm_erase
- \+/\- *theorem* xswap
- \- *theorem* count_eq_count_of_perm
- \- *theorem* perm_of_forall_count_eq
- \- *theorem* perm_iff_forall_count_eq_count
- \- *theorem* perm_iff_forall_mem_count_eq_count
- \- *theorem* perm_of_qeq
- \- *theorem* qeq_app
- \- *theorem* mem_head_of_qeq
- \- *theorem* mem_tail_of_qeq
- \- *theorem* mem_cons_of_qeq
- \- *theorem* length_eq_of_qeq
- \- *theorem* qeq_of_mem
- \- *theorem* qeq_split
- \- *theorem* subset_of_mem_of_subset_of_qeq
- \+/\- *theorem* perm_inv_core
- \+/\- *theorem* perm_cons_inv
- \- *theorem* perm_app_inv_left
- \+/\- *theorem* perm_app_inv_right
- \- *theorem* perm_app_inv
- \- *theorem* erase_perm_erase_of_perm
- \+/\- *theorem* perm_erase_dup_of_perm
- \+/\- *theorem* perm_insert
- \- *theorem* perm_insert_insert
- \+/\- *theorem* perm_union_left
- \+/\- *theorem* perm_union_right
- \+/\- *theorem* perm_union
- \+/\- *theorem* perm_inter_left
- \+/\- *theorem* perm_inter_right
- \+/\- *theorem* perm_inter
- \+/\- *theorem* perm_ext
- \- *theorem* nodup_of_perm_of_nodup
- \+/\- *theorem* perm_product_left
- \+/\- *theorem* perm_product_right
- \+/\- *theorem* perm_product
- \+/\- *theorem* perm_filter
- \- *def* decidable_perm_aux
- \- *def* decidable_perm

deleted data/list/set.lean
- \- *theorem* insert_nil
- \- *theorem* insert.def
- \- *theorem* insert_of_mem
- \- *theorem* insert_of_not_mem
- \- *theorem* mem_insert_iff
- \- *theorem* mem_insert_self
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* length_insert_of_mem
- \- *theorem* length_insert_of_not_mem
- \- *theorem* forall_mem_insert_of_forall_mem
- \- *theorem* erase_nil
- \- *theorem* erase_cons_head
- \- *theorem* erase_cons_tail
- \- *theorem* length_erase_of_mem
- \- *theorem* erase_of_not_mem
- \- *theorem* length_erase_of_not_mem
- \- *theorem* erase_append_left
- \- *theorem* erase_append_right
- \- *theorem* erase_sublist
- \- *theorem* erase_subset
- \- *theorem* mem_erase_of_ne_of_mem
- \- *theorem* mem_of_mem_erase
- \- *theorem* disjoint_left
- \- *theorem* disjoint_right
- \- *theorem* disjoint.symm
- \- *theorem* disjoint_comm
- \- *theorem* disjoint_of_subset_left
- \- *theorem* disjoint_of_subset_right
- \- *theorem* disjoint_of_disjoint_cons_left
- \- *theorem* disjoint_of_disjoint_cons_right
- \- *theorem* disjoint_nil_left
- \- *theorem* disjoint_singleton
- \- *theorem* singleton_disjoint
- \- *theorem* disjoint_cons_of_not_mem_of_disjoint
- \- *theorem* disjoint_append_of_disjoint_left
- \- *theorem* disjoint_of_disjoint_append_left_left
- \- *theorem* disjoint_of_disjoint_append_left_right
- \- *theorem* disjoint_of_disjoint_append_right_left
- \- *theorem* disjoint_of_disjoint_append_right_right
- \- *theorem* upto_nil
- \- *theorem* upto_succ
- \- *theorem* length_upto
- \- *theorem* upto_ne_nil_of_ne_zero
- \- *theorem* lt_of_mem_upto
- \- *theorem* mem_upto_succ_of_mem_upto
- \- *theorem* mem_upto_of_lt
- \- *theorem* upto_step
- \- *theorem* nil_union
- \- *theorem* cons_union
- \- *theorem* mem_union_iff
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* forall_mem_union
- \- *theorem* forall_mem_of_forall_mem_union_left
- \- *theorem* forall_mem_of_forall_mem_union_right
- \- *theorem* inter_nil
- \- *theorem* inter_cons_of_mem
- \- *theorem* inter_cons_of_not_mem
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* mem_inter_of_mem_of_mem
- \- *theorem* mem_inter_iff
- \- *theorem* inter_eq_nil_of_disjoint
- \- *theorem* forall_mem_inter_of_forall_left
- \- *theorem* forall_mem_inter_of_forall_right
- \- *theorem* nodup_nil
- \- *theorem* nodup_cons
- \- *theorem* nodup_singleton
- \- *theorem* nodup_of_nodup_cons
- \- *theorem* not_mem_of_nodup_cons
- \- *theorem* not_nodup_cons_of_mem
- \- *theorem* nodup_of_sublist
- \- *theorem* not_nodup_cons_of_not_nodup
- \- *theorem* nodup_of_nodup_append_left
- \- *theorem* nodup_of_nodup_append_right
- \- *theorem* disjoint_of_nodup_append
- \- *theorem* nodup_append
- \- *theorem* nodup_app_comm
- \- *theorem* nodup_head
- \- *theorem* nodup_middle
- \- *theorem* nodup_of_nodup_map
- \- *theorem* nodup_map_on
- \- *theorem* nodup_map
- \- *theorem* nodup_erase_of_nodup
- \- *theorem* mem_erase_iff_of_nodup
- \- *theorem* mem_erase_of_nodup
- \- *theorem* erase_dup_nil
- \- *theorem* erase_dup_cons_of_mem
- \- *theorem* erase_dup_cons_of_not_mem
- \- *theorem* mem_erase_dup
- \- *theorem* erase_dup_sublist
- \- *theorem* erase_dup_subset
- \- *theorem* subset_erase_dup
- \- *theorem* nodup_erase_dup
- \- *theorem* erase_dup_eq_of_nodup
- \- *theorem* nodup_product
- \- *theorem* nodup_filter
- \- *theorem* dmap_nodup_of_dinj
- \- *theorem* nodup_concat
- \- *theorem* nodup_insert
- \- *theorem* nodup_upto
- \- *theorem* nodup_union
- \- *theorem* nodup_inter_of_nodup
- \- *def* disjoint
- \- *def* upto
- \- *def* erase_dup

modified data/list/sort.lean
- \- *lemma* eq_of_sorted_of_perm
- \+/\- *theorem* sorted_nil
- \+/\- *theorem* sorted_singleton
- \+/\- *theorem* sorted_of_sorted_cons
- \+ *theorem* rel_of_sorted_cons
- \+/\- *theorem* sorted_cons
- \+ *theorem* eq_of_sorted_of_perm
- \+/\- *theorem* sorted_nil
- \+/\- *theorem* sorted_singleton
- \+/\- *theorem* sorted_of_sorted_cons
- \- *theorem* forall_mem_rel_of_sorted_cons
- \+/\- *theorem* sorted_cons
- \- *theorem* ordered_insert_nil
- \- *theorem* ordered_insert_cons
- \+/\- *def* sorted
- \+/\- *def* ordered_insert
- \+/\- *def* insertion_sort
- \+/\- *def* sorted
- \+/\- *def* ordered_insert
- \+/\- *def* insertion_sort

modified data/nat/pairing.lean
- \+ *theorem* mkpair_unpair'

modified data/option.lean
- \+ *lemma* mem_def
- \+ *lemma* some_inj
- \+ *lemma* guard_eq_some
- \+/\- *def* iget
- \+ *def* guard
- \+/\- *def* filter
- \+/\- *def* iget
- \+/\- *def* filter

modified data/prod.lean
- \+ *lemma* prod.swap_left_inverse
- \+ *lemma* prod.swap_right_inverse

modified data/rat.lean

modified data/seq/wseq.lean

modified data/set/basic.lean
- \+/\- *lemma* compl_image_set_of
- \+/\- *lemma* univ_eq_true_false
- \+/\- *lemma* forall_range_iff
- \+/\- *lemma* range_of_surjective
- \- *lemma* mem_of_eq_of_mem
- \+/\- *lemma* compl_image_set_of
- \+/\- *lemma* univ_eq_true_false
- \- *lemma* mem_image_iff_of_inverse
- \- *lemma* image_subset_eq
- \+/\- *lemma* forall_range_iff
- \+/\- *lemma* range_of_surjective
- \+/\- *theorem* subset.trans
- \+ *theorem* mem_of_eq_of_mem
- \+/\- *theorem* preimage_empty
- \+/\- *theorem* mem_preimage_eq
- \+/\- *theorem* preimage_mono
- \+/\- *theorem* preimage_univ
- \+/\- *theorem* preimage_inter
- \+/\- *theorem* preimage_union
- \+/\- *theorem* preimage_compl
- \+/\- *theorem* preimage_set_of_eq
- \+/\- *theorem* preimage_id
- \+/\- *theorem* preimage_comp
- \+/\- *theorem* eq_preimage_subtype_val_iff
- \+ *theorem* mem_image_iff_bex
- \+/\- *theorem* mem_image
- \+/\- *theorem* ball_image_iff
- \+ *theorem* image_subset_preimage_of_inverse
- \+ *theorem* preimage_subset_image_of_inverse
- \+/\- *theorem* image_eq_preimage_of_inverse
- \+ *theorem* mem_image_iff_of_inverse
- \+/\- *theorem* image_subset_iff_subset_preimage
- \+/\- *theorem* image_preimage_subset
- \+/\- *theorem* subset_preimage_image
- \+/\- *theorem* preimage_image_eq
- \+ *theorem* image_preimage_eq
- \+ *theorem* compl_image
- \+/\- *theorem* subset.trans
- \+/\- *theorem* mem_image
- \+/\- *theorem* image_subset_iff_subset_preimage
- \+/\- *theorem* ball_image_iff
- \+/\- *theorem* preimage_empty
- \+/\- *theorem* mem_preimage_eq
- \+/\- *theorem* preimage_mono
- \+/\- *theorem* preimage_image_eq
- \+/\- *theorem* preimage_univ
- \+/\- *theorem* preimage_inter
- \+/\- *theorem* preimage_union
- \+/\- *theorem* preimage_compl
- \- *theorem* preimage_diff
- \+/\- *theorem* preimage_set_of_eq
- \+/\- *theorem* preimage_id
- \+/\- *theorem* preimage_comp
- \+/\- *theorem* image_eq_preimage_of_inverse
- \+/\- *theorem* eq_preimage_subtype_val_iff
- \+/\- *theorem* image_preimage_subset
- \+/\- *theorem* subset_preimage_image
- \- *theorem* inter_preimage_subset
- \- *theorem* union_preimage_subset
- \- *theorem* image_union_supset
- \+/\- *def* preimage
- \+/\- *def* pairwise_on
- \+/\- *def* preimage
- \+/\- *def* pairwise_on

modified data/set/countable.lean
- \+/\- *def* countable
- \- *def* encodable_of_inj
- \+/\- *def* countable

modified data/set/enumerate.lean

deleted data/set/function.lean
- \- *lemma* injective_iff_inj_on_univ
- \- *lemma* surjective_iff_surj_on_univ
- \- *lemma* image_eq_of_maps_to_of_surj_on
- \- *lemma* maps_to_of_bij_on
- \- *lemma* inj_on_of_bij_on
- \- *lemma* surj_on_of_bij_on
- \- *lemma* bij_on.mk
- \- *lemma* image_eq_of_bij_on
- \- *lemma* bijective_iff_bij_on_univ
- \- *theorem* maps_to_of_eq_on
- \- *theorem* maps_to_comp
- \- *theorem* maps_to_univ_univ
- \- *theorem* image_subset_of_maps_to_of_subset
- \- *theorem* image_subset_of_maps_to
- \- *theorem* inj_on_empty
- \- *theorem* inj_on_of_eq_on
- \- *theorem* inj_on_comp
- \- *theorem* inj_on_of_inj_on_of_subset
- \- *theorem* surj_on_of_eq_on
- \- *theorem* surj_on_comp
- \- *theorem* bij_on_of_eq_on
- \- *theorem* bij_on_comp
- \- *theorem* left_inv_on_of_eq_on_left
- \- *theorem* left_inv_on_of_eq_on_right
- \- *theorem* inj_on_of_left_inv_on
- \- *theorem* left_inv_on_comp
- \- *theorem* right_inv_on_of_eq_on_left
- \- *theorem* right_inv_on_of_eq_on_right
- \- *theorem* surj_on_of_right_inv_on
- \- *theorem* right_inv_on_comp
- \- *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \- *theorem* eq_on_of_left_inv_of_right_inv
- \- *theorem* left_inv_on_of_surj_on_right_inv_on
- \- *theorem* bij_on_of_inv_on
- \- *def* maps_to
- \- *def* inj_on
- \- *def* surj_on
- \- *def* bij_on
- \- *def* left_inv_on
- \- *def* right_inv_on
- \- *def* inv_on

modified data/set/prod.lean
- \+/\- *lemma* mem_prod_eq
- \+ *lemma* mem_prod
- \+/\- *lemma* mem_prod_eq

modified logic/basic.lean
- \+ *lemma* and_iff_left_of_imp
- \+ *lemma* and_iff_right_of_imp
- \+ *lemma* heq_iff_eq
- \+ *theorem* sigma.mk.inj_iff
- \+ *theorem* sigma.forall
- \+ *theorem* sigma.exists
- \+ *theorem* subtype.forall
- \+ *theorem* subtype.exists
- \+ *theorem* exists_and_distrib_right

renamed logic/function_inverse.lean to logic/function.lean
- \+ *lemma* injective.has_left_inverse
- \+/\- *lemma* surj_inv_eq
- \+ *lemma* surjective.has_right_inverse
- \- *lemma* has_left_inverse
- \+/\- *lemma* surj_inv_eq
- \- *lemma* has_right_inverse
- \+ *theorem* injective.eq_iff
- \+ *theorem* partial_inv_eq
- \+ *theorem* partial_inv_eq_of_eq
- \- *def* inv_fun_on
- \- *def* inv_fun
- \- *def* surj_inv

modified order/filter.lean

modified tactic/interactive.lean

modified tactic/rcases.lean



## [2017-10-02 00:06:27-05:00](https://github.com/leanprover-community/mathlib/commit/e951a75)
Merge branch 'master' into master
#### Estimated changes
modified data/set/basic.lean
- \+ *lemma* image_subset_eq
- \+ *theorem* preimage_diff
- \+ *theorem* image_preimage_subset
- \+ *theorem* subset_preimage_image
- \+ *theorem* inter_preimage_subset
- \+ *theorem* union_preimage_subset
- \+ *theorem* image_union_supset

created data/set/function.lean
- \+ *lemma* injective_iff_inj_on_univ
- \+ *lemma* surjective_iff_surj_on_univ
- \+ *lemma* image_eq_of_maps_to_of_surj_on
- \+ *lemma* maps_to_of_bij_on
- \+ *lemma* inj_on_of_bij_on
- \+ *lemma* surj_on_of_bij_on
- \+ *lemma* bij_on.mk
- \+ *lemma* image_eq_of_bij_on
- \+ *lemma* bijective_iff_bij_on_univ
- \+ *theorem* maps_to_of_eq_on
- \+ *theorem* maps_to_comp
- \+ *theorem* maps_to_univ_univ
- \+ *theorem* image_subset_of_maps_to_of_subset
- \+ *theorem* image_subset_of_maps_to
- \+ *theorem* inj_on_empty
- \+ *theorem* inj_on_of_eq_on
- \+ *theorem* inj_on_comp
- \+ *theorem* inj_on_of_inj_on_of_subset
- \+ *theorem* surj_on_of_eq_on
- \+ *theorem* surj_on_comp
- \+ *theorem* bij_on_of_eq_on
- \+ *theorem* bij_on_comp
- \+ *theorem* left_inv_on_of_eq_on_left
- \+ *theorem* left_inv_on_of_eq_on_right
- \+ *theorem* inj_on_of_left_inv_on
- \+ *theorem* left_inv_on_comp
- \+ *theorem* right_inv_on_of_eq_on_left
- \+ *theorem* right_inv_on_of_eq_on_right
- \+ *theorem* surj_on_of_right_inv_on
- \+ *theorem* right_inv_on_comp
- \+ *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \+ *theorem* eq_on_of_left_inv_of_right_inv
- \+ *theorem* left_inv_on_of_surj_on_right_inv_on
- \+ *theorem* bij_on_of_inv_on
- \+ *def* maps_to
- \+ *def* inj_on
- \+ *def* surj_on
- \+ *def* bij_on
- \+ *def* left_inv_on
- \+ *def* right_inv_on
- \+ *def* inv_on

