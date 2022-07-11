## [2017-07-30 00:50:04+01:00](https://github.com/leanprover-community/mathlib/commit/8f65496)
feat(data/fp): first pass at a floating point model
Hopefully this will be eventually moved to init so it can get a native representation.
#### Estimated changes
Created data/fp/basic.lean
- \+ *theorem* float.zero.valid
- \+ *def* prec
- \+ *def* emax
- \+ *def* emin
- \+ *def* valid_finite
- \+ *def* float.is_finite
- \+ *def* shift2
- \+ *def* to_rat
- \+ *def* float.zero
- \+ *def* div_nat_lt_two_pow
- \+ *def* default_nan



## [2017-07-30 00:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/bce43b3)
feat(data/rat): new rat representation using canonical elements
This yields better performance in long rational computations provided the numbers can be simplified.
#### Estimated changes
Modified algebra/group.lean


Modified data/int/basic.lean
- \+ *theorem* coe_nat_dvd_left
- \+ *theorem* coe_nat_dvd_right
- \+ *theorem* div_sign
- \+ *theorem* sign_mul
- \+/\- *theorem* nat_abs_add_le
- \+/\- *theorem* nat_abs_mul
- \+ *theorem* nat_succ_eq_int_succ
- \+/\- *theorem* pred_succ
- \+/\- *theorem* succ_pred
- \+/\- *theorem* neg_succ
- \+/\- *theorem* neg_nat_succ
- \+/\- *theorem* succ_neg_nat_succ
- \- *theorem* of_nat_sub
- \- *theorem* rec_nat_on_neg
- \+/\- *def* succ
- \+/\- *def* pred
- \- *def* nat_succ_eq_int_succ
- \- *def* rec_nat_on

Modified data/nat/basic.lean


Modified data/nat/gcd.lean
- \+ *theorem* coprime_one_left
- \+ *theorem* coprime_one_right
- \- *theorem* comprime_one_left
- \- *theorem* comprime_one_right

Modified data/num/lemmas.lean


Modified data/rat.lean
- \+/\- *theorem* linear_order_cases_on_eq
- \+/\- *theorem* linear_order_cases_on_lt
- \+/\- *theorem* linear_order_cases_on_gt
- \+ *theorem* mk_pnat_eq
- \+ *theorem* mk_nat_eq
- \+ *theorem* mk_zero
- \+ *theorem* zero_mk_pnat
- \+ *theorem* zero_mk_nat
- \+ *theorem* zero_mk
- \+ *theorem* mk_eq_zero
- \+ *theorem* mk_eq
- \+ *theorem* div_mk_div_cancel_left
- \+ *theorem* num_denom
- \+ *theorem* num_denom'
- \+ *theorem* {u}
- \+ *theorem* lift_binop_eq
- \+ *theorem* add_def
- \+ *theorem* neg_def
- \+ *theorem* mul_def
- \+ *theorem* inv_def
- \+ *theorem* mk_nonneg
- \+ *theorem* nonneg_iff_zero_le
- \- *theorem* not_antimono
- \+ *def* of_int
- \+ *def* mk_pnat
- \+ *def* mk_nat
- \+ *def* mk
- \+ *def* floor
- \+ *def* ceil
- \- *def* rat

Modified data/seq/computation.lean


Modified data/seq/seq.lean


Modified pending/default.lean


Modified tactic/converter/binders.lean
- \+/\- *theorem* mem_image



## [2017-07-28 16:56:17+01:00](https://github.com/leanprover-community/mathlib/commit/bfe2db7)
fix(*): adapt to lean
#### Estimated changes
Modified algebra/group.lean


Modified data/list/basic.lean
- \- *def* filter_map

Modified data/rat.lean


Modified pending/default.lean


Modified tactic/converter/binders.lean




## [2017-07-27 14:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/b37966e)
chore(.travis.yml): add Travis CI support
#### Estimated changes
Created .travis.yml


Modified README.md




## [2017-07-26 14:25:09+01:00](https://github.com/leanprover-community/mathlib/commit/b8ea20f)
fix(data): bitvec and vector are in the main repo
#### Estimated changes
Deleted data/bitvec.lean
- \- *def* bitvec
- \- *def* append

Modified data/list/basic.lean
- \- *theorem* eq_nil_of_length_eq_zero
- \- *theorem* ne_nil_of_length_eq_succ
- \- *theorem* length_take
- \- *theorem* length_map₂
- \- *theorem* length_remove_nth
- \- *theorem* length_take_le
- \- *def* map₂
- \- *def* nth_le
- \- *def* update_nth
- \- *def* remove_nth

Modified data/list/comb.lean
- \- *theorem* length_map_accumr
- \- *theorem* length_map_accumr₂
- \- *def* map_accumr
- \- *def* map_accumr₂

Modified data/nat/basic.lean
- \- *lemma* bodd_bit
- \- *lemma* div2_bit
- \- *lemma* shiftl'_add
- \- *lemma* shiftl_add
- \- *lemma* shiftr_add
- \- *lemma* shiftl'_sub
- \- *lemma* shiftl_sub
- \- *lemma* shiftl_eq_mul_pow
- \- *lemma* shiftl'_tt_eq_mul_pow
- \- *lemma* one_shiftl
- \- *lemma* zero_shiftl
- \- *lemma* shiftr_eq_div_pow
- \- *lemma* zero_shiftr
- \- *lemma* test_bit_zero
- \- *lemma* test_bit_succ
- \- *lemma* binary_rec_eq
- \- *lemma* bitwise_bit_aux
- \- *lemma* bitwise_zero_left
- \- *lemma* bitwise_zero_right
- \- *lemma* bitwise_zero
- \- *lemma* bitwise_bit
- \- *lemma* lor_bit
- \- *lemma* land_bit
- \- *lemma* ldiff_bit
- \- *lemma* lxor_bit
- \- *lemma* test_bit_bitwise
- \- *lemma* test_bit_lor
- \- *lemma* test_bit_land
- \- *lemma* test_bit_ldiff
- \- *lemma* test_bit_lxor
- \- *theorem* add_one_ne_zero
- \- *theorem* eq_zero_or_eq_succ_pred
- \- *theorem* exists_eq_succ_of_ne_zero
- \- *theorem* succ_inj
- \- *theorem* discriminate
- \- *theorem* one_succ_zero
- \- *theorem* two_step_induction
- \- *theorem* sub_induction
- \- *theorem* succ_add_eq_succ_add
- \- *theorem* one_add
- \- *theorem* eq_zero_of_add_eq_zero
- \- *theorem* eq_zero_of_mul_eq_zero
- \- *theorem* le_succ_of_pred_le
- \- *theorem* le_lt_antisymm
- \- *theorem* lt_le_antisymm
- \- *theorem* lt_succ_of_lt
- \- *theorem* mul_self_le_mul_self
- \- *theorem* mul_self_lt_mul_self
- \- *theorem* mul_self_le_mul_self_iff
- \- *theorem* mul_self_lt_mul_self_iff
- \- *theorem* le_mul_self
- \- *theorem* succ_sub_sub_succ
- \- *theorem* mul_pred_left
- \- *theorem* mul_pred_right
- \- *theorem* succ_mul_succ_eq
- \- *theorem* succ_sub
- \- *theorem* sub_one_sub_lt
- \- *theorem* min_succ_succ
- \- *theorem* sub_eq_sub_min
- \- *theorem* sub_add_min_cancel
- \- *theorem* pred_inj
- \- *theorem* mod_le
- \- *theorem* add_mod_right
- \- *theorem* add_mod_left
- \- *theorem* add_mul_mod_self_left
- \- *theorem* add_mul_mod_self_right
- \- *theorem* mul_mod_right
- \- *theorem* mul_mod_left
- \- *theorem* mul_mod_mul_left
- \- *theorem* mul_mod_mul_right
- \- *theorem* cond_to_bool_mod_two
- \- *theorem* sub_mul_mod
- \- *theorem* sub_mul_div
- \- *theorem* div_mul_le_self
- \- *theorem* add_div_right
- \- *theorem* add_div_left
- \- *theorem* mul_div_right
- \- *theorem* mul_div_left
- \- *theorem* add_mul_div_left
- \- *theorem* add_mul_div_right
- \- *theorem* mul_sub_div
- \- *theorem* dvd_sub
- \- *theorem* dvd_mod_iff
- \- *theorem* le_of_dvd
- \- *theorem* dvd_antisymm
- \- *theorem* pos_of_dvd_of_pos
- \- *theorem* eq_one_of_dvd_one
- \- *theorem* dvd_of_mod_eq_zero
- \- *theorem* mod_eq_zero_of_dvd
- \- *theorem* dvd_iff_mod_eq_zero
- \- *theorem* dvd_of_mul_dvd_mul_left
- \- *theorem* dvd_of_mul_dvd_mul_right
- \- *theorem* pow_one
- \- *theorem* pow_le_pow_of_le_left
- \- *theorem* pow_le_pow_of_le_right
- \- *theorem* pos_pow_of_pos
- \- *theorem* zero_pow
- \- *theorem* pow_lt_pow_of_lt_left
- \- *theorem* pow_lt_pow_of_lt_right
- \- *theorem* mod_pow_succ
- \- *theorem* bitwise_swap
- \- *def* iterate
- \- *def* one_pos

Modified data/num/basic.lean


Deleted data/vector.lean
- \- *theorem* head_cons
- \- *theorem* tail_cons
- \- *theorem* cons_head_tail
- \- *theorem* map_nil
- \- *theorem* map_cons
- \- *theorem* to_list_mk
- \- *theorem* to_list_nil
- \- *theorem* to_list_length
- \- *theorem* to_list_cons
- \- *theorem* to_list_append
- \- *theorem* to_list_drop
- \- *theorem* to_list_take
- \- *def* vector
- \- *def* nil
- \- *def* cons
- \- *def* length
- \- *def* head
- \- *def* tail
- \- *def* to_list
- \- *def* nth
- \- *def* append
- \- *def* elim
- \- *def* map
- \- *def* map₂
- \- *def* repeat
- \- *def* drop
- \- *def* take
- \- *def* remove_nth
- \- *def* of_fn



## [2017-07-25 13:51:39+01:00](https://github.com/leanprover-community/mathlib/commit/9451087)
refactor(*): move in list lemmas, adapt to change in list.union
#### Estimated changes
Modified data/hash_map.lean
- \+ *theorem* insert_lemma
- \- *theorem* insert_theorem

Modified data/list/basic.lean
- \+ *lemma* concat_eq_append
- \+ *lemma* length_concat
- \+ *lemma* map_concat
- \+/\- *theorem* not_mem_append
- \+/\- *theorem* mem_split
- \+/\- *theorem* sublist.refl
- \+/\- *theorem* sublist.trans
- \+ *theorem* index_of_cons_eq
- \+ *theorem* index_of_cons_self
- \+ *theorem* index_of_cons_ne
- \+ *theorem* index_of_eq_length
- \+/\- *theorem* index_of_of_not_mem
- \+/\- *theorem* index_of_lt_length
- \+ *theorem* index_of_nth_le
- \+/\- *theorem* index_of_nth
- \+/\- *theorem* length_remove_nth
- \+/\- *theorem* nth_le_reverse_aux1
- \+/\- *theorem* nth_le_reverse_aux2
- \+/\- *theorem* nth_le_reverse
- \- *theorem* mem_or_mem_of_mem_append
- \- *theorem* mem_append_of_mem_or_mem
- \- *theorem* not_mem_of_not_mem_append_left
- \- *theorem* not_mem_of_not_mem_append_right
- \- *theorem* index_of_cons_of_eq
- \- *theorem* index_of_cons_of_ne
- \- *theorem* not_mem_of_index_of_eq_length
- \+ *def* split_at
- \+ *def* concat
- \+ *def* map₂
- \+ *def* filter_map
- \+ *def* nth_le
- \+ *def* update_nth
- \+ *def* remove_nth
- \+ *def* to_array
- \+ *def* take_while
- \+ *def* find
- \+ *def* find_indexes_aux
- \+ *def* find_indexes
- \+ *def* indexes_of
- \+ *def* scanl
- \+ *def* scanr_aux
- \+ *def* scanr
- \+ *def* sum
- \+ *def* is_prefix
- \+ *def* is_suffix
- \+ *def* is_infix
- \+ *def* inits
- \+ *def* tails
- \+ *def* sublists_aux
- \+ *def* sublists
- \+ *def* transpose_aux
- \+ *def* transpose

Modified data/list/comb.lean


Modified data/list/perm.lean
- \+/\- *theorem* perm_insert
- \+/\- *theorem* perm_insert_insert

Modified data/list/set.lean
- \+/\- *theorem* insert.def
- \+/\- *theorem* insert_of_not_mem
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* erase_nil
- \+ *theorem* disjoint.symm
- \+ *theorem* disjoint_comm
- \+ *theorem* disjoint_singleton
- \+ *theorem* singleton_disjoint
- \+ *theorem* nil_union
- \+ *theorem* cons_union
- \+/\- *theorem* mem_union_iff
- \+/\- *theorem* mem_or_mem_of_mem_union
- \+ *theorem* nodup_append
- \+/\- *theorem* erase_dup_nil
- \+/\- *theorem* erase_dup_cons_of_mem
- \+/\- *theorem* erase_dup_cons_of_not_mem
- \+/\- *theorem* mem_erase_dup
- \+/\- *theorem* erase_dup_eq_of_nodup
- \+ *theorem* nodup_union
- \- *theorem* erase_cons
- \- *theorem* disjoint.comm
- \- *theorem* disjoint_nil_right
- \- *theorem* union_nil
- \- *theorem* union_cons
- \- *theorem* nodup_append_of_nodup_of_nodup_of_disjoint
- \- *theorem* mem_of_mem_erase_dup
- \- *theorem* mem_erase_dup_iff
- \- *theorem* nodup_union_of_nodup_of_nodup

Modified data/set/basic.lean
- \+/\- *theorem* mem_empty_eq
- \+/\- *theorem* mem_sep_eq
- \+/\- *theorem* mem_image_eq

Modified logic/basic.lean
- \+/\- *theorem* set_of_subset_set_of

Modified tactic/finish.lean




## [2017-07-24 00:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/aa78466)
refactor(*): move in some nat lemmas
and other lemmas from init
#### Estimated changes
Created data/array/lemmas.lean
- \+ *lemma* read_write
- \+ *lemma* read_write_eq
- \+ *lemma* read_write_ne
- \+ *lemma* push_back_rev_list_core
- \+ *theorem* rev_list_reverse_core
- \+ *theorem* rev_list_reverse
- \+ *theorem* to_list_reverse
- \+ *theorem* rev_list_length_aux
- \+ *theorem* rev_list_length
- \+ *theorem* to_list_length
- \+ *theorem* to_list_nth_core
- \+ *theorem* to_list_nth
- \+ *theorem* mem_iff_rev_list_mem_core
- \+ *theorem* mem_iff_rev_list_mem
- \+ *theorem* mem_iff_list_mem
- \+ *theorem* to_list_to_array
- \+ *theorem* to_array_to_list
- \+ *theorem* push_back_rev_list
- \+ *theorem* push_back_to_list
- \+ *def* read_foreach_aux
- \+ *def* read_foreach
- \+ *def* read_map
- \+ *def* read_map₂

Modified data/bitvec.lean


Modified data/fin.lean
- \- *theorem* lt_succ_of_lt

Modified data/hash_map.lean


Modified data/int/basic.lean
- \+ *lemma* bodd_zero
- \+ *lemma* bodd_one
- \+ *lemma* bodd_two
- \+ *lemma* bodd_sub_nat_nat
- \+ *lemma* bodd_neg_of_nat
- \+ *lemma* bodd_neg
- \+ *lemma* bodd_add
- \+ *lemma* bodd_mul
- \+ *lemma* bit0_val
- \+ *lemma* bit1_val
- \+ *lemma* bit_val
- \+ *lemma* bit_decomp
- \+ *lemma* bit_zero
- \+ *lemma* bit_coe_nat
- \+ *lemma* bit_neg_succ
- \+ *lemma* bodd_bit
- \+ *lemma* div2_bit
- \+ *lemma* test_bit_zero
- \+ *lemma* test_bit_succ
- \+ *lemma* bitwise_bit
- \+ *lemma* lor_bit
- \+ *lemma* land_bit
- \+ *lemma* ldiff_bit
- \+ *lemma* lxor_bit
- \+ *lemma* lnot_bit
- \+ *lemma* test_bit_bitwise
- \+ *lemma* test_bit_lor
- \+ *lemma* test_bit_land
- \+ *lemma* test_bit_ldiff
- \+ *lemma* test_bit_lxor
- \+ *lemma* test_bit_lnot
- \+ *lemma* shiftl_add
- \+ *lemma* shiftl_sub
- \+ *lemma* shiftl_neg
- \+ *lemma* shiftr_neg
- \+ *lemma* shiftl_coe_nat
- \+ *lemma* shiftr_coe_nat
- \+ *lemma* shiftl_neg_succ
- \+ *lemma* shiftr_neg_succ
- \+ *lemma* shiftr_add
- \+ *lemma* shiftl_eq_mul_pow
- \+ *lemma* shiftr_eq_div_pow
- \+ *lemma* one_shiftl
- \+ *lemma* zero_shiftl
- \+ *lemma* zero_shiftr
- \+ *theorem* of_nat_div
- \+ *theorem* neg_succ_of_nat_div
- \+ *theorem* div_of_neg_of_pos
- \+ *theorem* div_neg'
- \+ *theorem* div_eq_zero_of_lt
- \+ *theorem* div_eq_zero_of_lt_abs
- \+ *theorem* of_nat_mod
- \+ *theorem* neg_succ_of_nat_mod
- \+ *theorem* mod_neg
- \+ *theorem* mod_abs
- \+ *theorem* zero_mod
- \+ *theorem* mod_zero
- \+ *theorem* mod_one
- \+ *theorem* mod_eq_of_lt
- \+ *theorem* mod_nonneg
- \+ *theorem* mod_lt_of_pos
- \+ *theorem* mod_lt
- \+ *theorem* mod_add_div_aux
- \+ *theorem* mod_add_div
- \+ *theorem* mod_def
- \+ *theorem* add_mul_mod_self
- \+ *theorem* add_mul_mod_self_left
- \+ *theorem* add_mod_self
- \+ *theorem* add_mod_self_left
- \+ *theorem* mod_add_mod
- \+ *theorem* add_mod_mod
- \+ *theorem* add_mod_eq_add_mod_right
- \+ *theorem* add_mod_eq_add_mod_left
- \+ *theorem* mod_eq_mod_of_add_mod_eq_add_mod_right
- \+ *theorem* mod_eq_mod_of_add_mod_eq_add_mod_left
- \+ *theorem* mul_mod_left
- \+ *theorem* mul_mod_right
- \+ *theorem* mod_self
- \+ *theorem* mul_div_mul_of_pos
- \+ *theorem* mul_div_mul_of_pos_left
- \+ *theorem* mul_mod_mul_of_pos
- \+ *theorem* lt_div_add_one_mul_self
- \+ *theorem* abs_div_le_abs
- \+ *theorem* div_le_self
- \+ *theorem* mul_div_cancel_of_mod_eq_zero
- \+ *theorem* div_mul_cancel_of_mod_eq_zero
- \+ *theorem* coe_nat_dvd_coe_nat_of_dvd
- \+ *theorem* dvd_of_coe_nat_dvd_coe_nat
- \+ *theorem* coe_nat_dvd_coe_nat_iff
- \+ *theorem* dvd_antisymm
- \+ *theorem* dvd_of_mod_eq_zero
- \+ *theorem* mod_eq_zero_of_dvd
- \+ *theorem* dvd_iff_mod_eq_zero
- \+ *theorem* div_dvd_div
- \+ *theorem* neg_div_of_dvd
- \+ *theorem* le_of_dvd
- \+ *theorem* eq_one_of_dvd_one
- \+ *theorem* eq_one_of_mul_eq_one_right
- \+ *theorem* eq_one_of_mul_eq_one_left
- \+ *theorem* div_pos_of_pos_of_dvd
- \+ *theorem* div_eq_div_of_mul_eq_mul
- \+ *theorem* bodd_add_div2
- \+ *theorem* div2_val
- \+ *theorem* bitwise_or
- \+ *theorem* bitwise_and
- \+ *theorem* bitwise_diff
- \+ *theorem* bitwise_xor
- \+ *def* {u}

Modified data/int/order.lean
- \+ *theorem* exists_least_of_bdd
- \+ *theorem* exists_greatest_of_bdd

Modified data/list/basic.lean
- \+ *lemma* mem_bind_iff
- \+ *lemma* exists_of_mem_bind
- \+ *lemma* mem_bind
- \+ *lemma* foldr_eta
- \+ *lemma* scanr_nil
- \+ *lemma* scanr_aux_cons
- \+ *lemma* scanr_cons
- \+ *lemma* span_eq_take_drop
- \+ *lemma* take_while_append_drop
- \+ *lemma* prefix_append
- \+ *lemma* suffix_append
- \+ *lemma* infix_append
- \+ *lemma* prefix_refl
- \+ *lemma* suffix_refl
- \+ *lemma* infix_of_prefix
- \+ *lemma* infix_of_suffix
- \+ *lemma* infix_refl
- \+ *lemma* sublist_of_infix
- \+ *lemma* length_le_of_infix
- \+ *lemma* eq_nil_of_infix_nil
- \+ *lemma* eq_nil_of_prefix_nil
- \+ *lemma* eq_nil_of_suffix_nil
- \+ *lemma* infix_iff_prefix_suffix
- \+ *lemma* mem_inits
- \+ *lemma* mem_tails
- \+ *lemma* sublists_aux_eq_foldl
- \+ *lemma* sublists_aux_cons_cons
- \+ *lemma* mem_sublists
- \+/\- *theorem* cons_ne_nil
- \+ *theorem* append_ne_nil_of_ne_nil_left
- \+ *theorem* append_ne_nil_of_ne_nil_right
- \+ *theorem* append_foldl
- \+ *theorem* append_foldr
- \+ *theorem* split_at_eq_take_drop
- \+ *theorem* take_append_drop
- \+ *theorem* eq_nil_of_length_eq_zero
- \+ *theorem* ne_nil_of_length_eq_succ
- \+ *theorem* length_take
- \+ *theorem* length_remove_nth
- \+ *theorem* append_inj
- \+ *theorem* append_inj_left
- \+ *theorem* append_inj_right
- \+ *theorem* append_right_inj
- \+ *theorem* reverse_nil
- \+ *theorem* reverse_cons
- \+ *theorem* reverse_singleton
- \+ *theorem* reverse_append
- \+ *theorem* reverse_reverse
- \+ *theorem* concat_eq_reverse_cons
- \+ *theorem* length_reverse
- \+ *theorem* map_reverse
- \+ *theorem* nth_le_reverse_aux1
- \+ *theorem* nth_le_reverse_aux2
- \+ *theorem* nth_le_reverse
- \+ *theorem* last_cons
- \+ *theorem* last_append
- \+ *theorem* last_concat
- \+ *theorem* head_append
- \+ *theorem* cons_head_tail
- \+ *theorem* map_id'
- \+ *theorem* foldl_map
- \+ *theorem* foldr_map
- \+ *theorem* foldl_hom
- \+ *theorem* foldr_hom
- \+ *theorem* length_map₂
- \+ *theorem* eq_nil_of_forall_not_mem
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_of_mem_cons_of_mem
- \+ *theorem* mem_or_mem_of_mem_append
- \+ *theorem* mem_append_of_mem_or_mem
- \+ *theorem* not_mem_of_not_mem_append_left
- \+ *theorem* not_mem_of_not_mem_append_right
- \+ *theorem* not_mem_append
- \+ *theorem* length_pos_of_mem
- \+ *theorem* mem_split
- \+ *theorem* mem_of_ne_of_mem
- \+ *theorem* ne_of_not_mem_cons
- \+ *theorem* not_mem_of_not_mem_cons
- \+ *theorem* not_mem_cons_of_ne_of_not_mem
- \+ *theorem* ne_and_not_mem_of_not_mem_cons
- \+ *theorem* mem_reverse
- \+ *theorem* mem_map
- \+ *theorem* exists_of_mem_map
- \+ *theorem* mem_map_iff
- \+ *theorem* mem_join_iff
- \+ *theorem* exists_of_mem_join
- \+ *theorem* mem_join
- \+ *theorem* subset_app_of_subset_left
- \+ *theorem* subset_app_of_subset_right
- \+ *theorem* cons_subset_of_subset_of_mem
- \+ *theorem* app_subset_of_subset_of_subset
- \+ *theorem* eq_nil_of_subset_nil
- \+ *theorem* nil_sublist
- \+ *theorem* sublist.refl
- \+ *theorem* sublist.trans
- \+ *theorem* sublist_cons
- \+ *theorem* sublist_of_cons_sublist
- \+ *theorem* cons_sublist_cons
- \+ *theorem* sublist_append_left
- \+ *theorem* sublist_append_right
- \+ *theorem* sublist_cons_of_sublist
- \+ *theorem* sublist_app_of_sublist_left
- \+ *theorem* sublist_app_of_sublist_right
- \+ *theorem* sublist_of_cons_sublist_cons
- \+ *theorem* subset_of_sublist
- \+ *theorem* eq_nil_of_sublist_nil
- \+ *theorem* eq_nil_of_map_eq_nil
- \+ *theorem* eq_of_map_const
- \+ *theorem* nth_le_nth
- \+ *theorem* nth_ge_len
- \+ *theorem* ext
- \+ *theorem* ext_le
- \+ *theorem* take_zero
- \+ *theorem* take_nil
- \+ *theorem* take_cons
- \+ *theorem* take_all
- \+ *theorem* take_all_of_ge
- \+ *theorem* take_take
- \+ *theorem* length_take_le
- \+ *theorem* filter_subset
- \+ *theorem* of_mem_filter
- \+ *theorem* mem_of_mem_filter
- \+ *theorem* mem_filter_of_mem
- \- *theorem* append.assoc
- \- *theorem* nth_eq_some
- \- *theorem* inth_zero
- \- *theorem* inth_succ
- \- *theorem* ith_zero
- \- *theorem* ith_succ
- \- *theorem* taken_zero
- \- *theorem* taken_nil
- \- *theorem* taken_cons
- \- *theorem* taken_all
- \- *theorem* taken_all_of_ge
- \- *theorem* taken_taken
- \- *theorem* length_taken_le
- \- *theorem* length_taken_eq
- \- *theorem* length_dropn
- \+/\- *def* inth
- \- *def* ith

Modified data/list/perm.lean


Modified data/nat/basic.lean
- \+ *lemma* bodd_bit
- \+ *lemma* div2_bit
- \+ *lemma* shiftl'_add
- \+ *lemma* shiftl_add
- \+ *lemma* shiftr_add
- \+ *lemma* shiftl'_sub
- \+ *lemma* shiftl_sub
- \+ *lemma* shiftl_eq_mul_pow
- \+ *lemma* shiftl'_tt_eq_mul_pow
- \+ *lemma* one_shiftl
- \+ *lemma* zero_shiftl
- \+ *lemma* shiftr_eq_div_pow
- \+ *lemma* zero_shiftr
- \+ *lemma* test_bit_zero
- \+ *lemma* test_bit_succ
- \+ *lemma* binary_rec_eq
- \+ *lemma* bitwise_bit_aux
- \+ *lemma* bitwise_zero_left
- \+ *lemma* bitwise_zero_right
- \+ *lemma* bitwise_zero
- \+ *lemma* bitwise_bit
- \+ *lemma* lor_bit
- \+ *lemma* land_bit
- \+ *lemma* ldiff_bit
- \+ *lemma* lxor_bit
- \+ *lemma* test_bit_bitwise
- \+ *lemma* test_bit_lor
- \+ *lemma* test_bit_land
- \+ *lemma* test_bit_ldiff
- \+ *lemma* test_bit_lxor
- \+/\- *theorem* discriminate
- \+/\- *theorem* one_add
- \+ *theorem* eq_zero_of_mul_eq_zero
- \+ *theorem* le_succ_of_pred_le
- \+ *theorem* le_lt_antisymm
- \+ *theorem* lt_le_antisymm
- \+ *theorem* lt_succ_of_lt
- \+ *theorem* mul_self_le_mul_self
- \+ *theorem* mul_self_lt_mul_self
- \+ *theorem* mul_self_le_mul_self_iff
- \+ *theorem* mul_self_lt_mul_self_iff
- \+ *theorem* le_mul_self
- \+ *theorem* succ_sub_sub_succ
- \+ *theorem* mul_pred_left
- \+ *theorem* mul_pred_right
- \+ *theorem* succ_mul_succ_eq
- \+ *theorem* succ_sub
- \+ *theorem* sub_one_sub_lt
- \+ *theorem* min_succ_succ
- \+ *theorem* sub_eq_sub_min
- \+ *theorem* sub_add_min_cancel
- \+ *theorem* pred_inj
- \+ *theorem* mod_le
- \+ *theorem* add_mod_right
- \+ *theorem* add_mod_left
- \+ *theorem* add_mul_mod_self_left
- \+ *theorem* add_mul_mod_self_right
- \+ *theorem* mul_mod_right
- \+ *theorem* mul_mod_left
- \+ *theorem* mul_mod_mul_left
- \+ *theorem* mul_mod_mul_right
- \+ *theorem* cond_to_bool_mod_two
- \+ *theorem* sub_mul_mod
- \+ *theorem* sub_mul_div
- \+ *theorem* div_mul_le_self
- \+ *theorem* add_div_right
- \+ *theorem* add_div_left
- \+ *theorem* mul_div_right
- \+ *theorem* mul_div_left
- \+ *theorem* add_mul_div_left
- \+ *theorem* add_mul_div_right
- \+ *theorem* mul_sub_div
- \+ *theorem* dvd_sub
- \+ *theorem* dvd_mod_iff
- \+ *theorem* le_of_dvd
- \+ *theorem* dvd_antisymm
- \+ *theorem* pos_of_dvd_of_pos
- \+ *theorem* eq_one_of_dvd_one
- \+ *theorem* dvd_of_mod_eq_zero
- \+ *theorem* mod_eq_zero_of_dvd
- \+ *theorem* dvd_iff_mod_eq_zero
- \+ *theorem* dvd_of_mul_dvd_mul_left
- \+ *theorem* dvd_of_mul_dvd_mul_right
- \+ *theorem* pow_one
- \+ *theorem* pow_le_pow_of_le_left
- \+ *theorem* pow_le_pow_of_le_right
- \+ *theorem* pos_pow_of_pos
- \+ *theorem* zero_pow
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_lt_pow_of_lt_right
- \+ *theorem* mod_pow_succ
- \+ *theorem* bitwise_swap
- \- *theorem* add_one
- \+/\- *def* iterate
- \+ *def* one_pos

Modified data/nat/gcd.lean


Modified data/nat/sub.lean


Created data/option.lean
- \+ *def* iget

Modified data/seq/computation.lean


Modified data/seq/wseq.lean


Modified data/stream.lean




## [2017-07-23 19:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/1b6322f)
chore(*): rfl-lemmas on same line
#### Estimated changes
Modified algebra/group.lean
- \+/\- *theorem* bit0_add_one
- \+/\- *theorem* bit1_add_one
- \+/\- *theorem* add1_bit0
- \+/\- *theorem* add1_one
- \+/\- *theorem* one_add_one

Modified algebra/lattice/filter.lean
- \+/\- *theorem* fmap_eq_image
- \+/\- *theorem* set_of_mem_eq
- \+/\- *theorem* mem_join_sets
- \+/\- *theorem* mem_principal_sets
- \+/\- *theorem* join_principal_eq_Sup
- \+/\- *theorem* principal_univ
- \+/\- *theorem* principal_empty

Modified algebra/order.lean


Modified data/bool.lean
- \+/\- *theorem* cond_ff
- \+/\- *theorem* cond_tt
- \+/\- *theorem* bnot_false
- \+/\- *theorem* bnot_true

Modified data/list/basic.lean
- \+/\- *theorem* last_singleton
- \+/\- *theorem* head_cons
- \+/\- *theorem* tail_nil
- \+/\- *theorem* tail_cons
- \+/\- *theorem* index_of_nil
- \+/\- *theorem* index_of_cons
- \+/\- *theorem* inth_zero
- \+/\- *theorem* inth_succ
- \+/\- *theorem* ith_zero
- \+/\- *theorem* count_nil

Modified data/stream.lean
- \+/\- *theorem* nth_zero_cons
- \+/\- *theorem* head_cons
- \+/\- *theorem* tail_cons
- \+/\- *theorem* nth_drop
- \+/\- *theorem* tail_eq_drop
- \+/\- *theorem* nth_succ
- \+/\- *theorem* drop_succ
- \+/\- *theorem* all_def
- \+/\- *theorem* any_def
- \+/\- *theorem* nth_map
- \+/\- *theorem* head_map
- \+/\- *theorem* map_id
- \+/\- *theorem* map_map
- \+/\- *theorem* map_tail
- \+/\- *theorem* nth_zip
- \+/\- *theorem* head_zip
- \+/\- *theorem* tail_zip
- \+/\- *theorem* map_const
- \+/\- *theorem* nth_const
- \+/\- *theorem* head_iterate
- \+/\- *theorem* nth_zero_iterate
- \+/\- *theorem* corec_def
- \+/\- *theorem* corec_id_f_eq_iterate
- \+/\- *theorem* odd_eq
- \+/\- *theorem* head_even
- \+/\- *theorem* even_tail
- \+/\- *theorem* nil_append_stream
- \+/\- *theorem* cons_append_stream
- \+/\- *theorem* approx_zero
- \+/\- *theorem* approx_succ
- \+/\- *theorem* tails_eq_iterate
- \+/\- *theorem* inits_tail
- \+/\- *theorem* identity
- \+/\- *theorem* composition
- \+/\- *theorem* homomorphism
- \+/\- *theorem* interchange
- \+/\- *theorem* map_eq_apply
- \+/\- *theorem* nth_nats

Modified topology/continuity.lean




## [2017-07-23 18:59:39+01:00](https://github.com/leanprover-community/mathlib/commit/4a28535)
refactor(*): attributes on same line
#### Estimated changes
Modified algebra/lattice/boolean_algebra.lean
- \+/\- *theorem* inf_neg_eq_bot
- \+/\- *theorem* neg_inf_eq_bot
- \+/\- *theorem* sup_neg_eq_top
- \+/\- *theorem* neg_sup_eq_top
- \+/\- *theorem* neg_top
- \+/\- *theorem* neg_bot
- \+/\- *theorem* neg_neg
- \+/\- *theorem* neg_eq_neg_iff
- \+/\- *theorem* neg_inf
- \+/\- *theorem* neg_sup

Modified algebra/lattice/complete_lattice.lean
- \+/\- *theorem* le_Sup
- \+/\- *theorem* Inf_le
- \+/\- *theorem* le_Sup_iff
- \+/\- *theorem* Inf_le_iff
- \+/\- *theorem* Sup_empty
- \+/\- *theorem* Inf_empty
- \+/\- *theorem* Sup_univ
- \+/\- *theorem* Inf_univ
- \+/\- *theorem* Sup_insert
- \+/\- *theorem* Inf_insert
- \+/\- *theorem* Sup_singleton
- \+/\- *theorem* Inf_singleton
- \+/\- *theorem* le_supr'
- \+/\- *theorem* supr_le_iff
- \+/\- *theorem* supr_congr_Prop
- \+/\- *theorem* infi_le'
- \+/\- *theorem* infi_le₂'
- \+/\- *theorem* le_infi_iff
- \+/\- *theorem* infi_congr_Prop
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* infi_infi_eq_left
- \+/\- *theorem* infi_infi_eq_right
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right
- \+/\- *theorem* foo
- \+/\- *theorem* foo'
- \+/\- *theorem* infi_false
- \+/\- *theorem* supr_false
- \+/\- *theorem* infi_true
- \+/\- *theorem* supr_true
- \+/\- *theorem* infi_exists
- \+/\- *theorem* supr_exists
- \+/\- *theorem* infi_emptyset
- \+/\- *theorem* supr_emptyset
- \+/\- *theorem* infi_univ
- \+/\- *theorem* supr_univ
- \+/\- *theorem* infi_union
- \+/\- *theorem* supr_union
- \+/\- *theorem* infi_insert
- \+/\- *theorem* supr_insert
- \+/\- *theorem* infi_singleton
- \+/\- *theorem* supr_singleton
- \+/\- *theorem* infi_empty
- \+/\- *theorem* supr_empty
- \+/\- *theorem* infi_unit
- \+/\- *theorem* supr_unit
- \+/\- *theorem* Inf_eq_top
- \+/\- *theorem* infi_eq_top
- \+/\- *theorem* Sup_eq_bot
- \+/\- *theorem* supr_eq_top

Modified algebra/lattice/filter.lean
- \+/\- *theorem* prod.swap_swap
- \+/\- *theorem* prod.fst_swap
- \+/\- *theorem* prod.snd_swap
- \+/\- *theorem* prod.swap_prod_mk
- \+/\- *theorem* prod.swap_swap_eq
- \+/\- *theorem* prod_singleton_singleton
- \+/\- *theorem* prod_mk_mem_set_prod_eq
- \+/\- *theorem* vimage_set_of_eq
- \+/\- *theorem* set_of_mem_eq
- \+/\- *theorem* diff_empty
- \+/\- *theorem* not_not_mem_iff
- \+/\- *theorem* singleton_neq_emptyset
- \+/\- *theorem* mem_join_sets
- \+/\- *theorem* mem_principal_sets
- \+/\- *theorem* le_principal_iff
- \+/\- *theorem* principal_eq_iff_eq
- \+/\- *theorem* map_principal
- \+/\- *theorem* join_principal_eq_Sup
- \+/\- *theorem* mem_bot_sets
- \+/\- *theorem* mem_sup_sets
- \+/\- *theorem* mem_inf_sets
- \+/\- *theorem* sup_join
- \+/\- *theorem* supr_join
- \+/\- *theorem* inf_principal
- \+/\- *theorem* sup_principal
- \+/\- *theorem* supr_principal
- \+/\- *theorem* principal_eq_bot_iff
- \+/\- *theorem* mem_pure
- \+/\- *theorem* mem_map
- \+/\- *theorem* map_id
- \+/\- *theorem* map_compose
- \+/\- *theorem* map_sup
- \+/\- *theorem* supr_map
- \+/\- *theorem* map_bot
- \+/\- *theorem* map_eq_bot_iff
- \+/\- *theorem* fmap_principal
- \+/\- *theorem* vmap_principal
- \+/\- *theorem* lift'_id
- \+/\- *theorem* mem_top_sets_iff
- \+/\- *theorem* infi_sets_induct

Modified data/bool.lean
- \+ *theorem* coe_tt
- \+ *theorem* band_tt
- \+ *theorem* tt_band
- \+ *theorem* band_ff
- \+ *theorem* ff_band
- \+ *theorem* bor_tt
- \+ *theorem* tt_bor
- \+ *theorem* bor_ff
- \+ *theorem* ff_bor
- \+ *theorem* band_eq_tt
- \+ *theorem* band_eq_ff
- \+ *theorem* bor_eq_tt
- \+ *theorem* bor_eq_ff
- \+ *theorem* dichotomy
- \+ *theorem* cond_ff
- \+ *theorem* cond_tt
- \+ *theorem* eq_tt_of_ne_ff
- \+ *theorem* eq_ff_of_ne_tt
- \+ *theorem* absurd_of_eq_ff_of_eq_tt
- \+ *theorem* bor_comm
- \+ *theorem* bor_assoc
- \+ *theorem* bor_left_comm
- \+ *theorem* or_of_bor_eq
- \+ *theorem* bor_inl
- \+ *theorem* bor_inr
- \+ *theorem* band_self
- \+ *theorem* band_comm
- \+ *theorem* band_assoc
- \+ *theorem* band_left_comm
- \+ *theorem* band_elim_left
- \+ *theorem* band_intro
- \+ *theorem* band_elim_right
- \+ *theorem* bnot_false
- \+ *theorem* bnot_true
- \+ *theorem* bnot_bnot
- \+ *theorem* eq_tt_of_bnot_eq_ff
- \+ *theorem* eq_ff_of_bnot_eq_tt
- \+ *theorem* ff_bxor_ff
- \+ *theorem* ff_bxor_tt
- \+ *theorem* tt_bxor_ff
- \+ *theorem* tt_bxor_tt
- \+ *theorem* bxor_self
- \+ *theorem* bxor_ff
- \+ *theorem* bxor_tt
- \+ *theorem* ff_bxor
- \+ *theorem* tt_bxor
- \+ *theorem* bxor_comm
- \+ *theorem* bxor_assoc
- \+ *theorem* bxor_left_comm
- \+ *def* bxor

Modified data/list/basic.lean
- \+/\- *theorem* cons_ne_nil
- \+/\- *theorem* append.assoc
- \+/\- *theorem* concat_ne_nil
- \+/\- *theorem* concat_append
- \+/\- *theorem* last_singleton
- \+/\- *theorem* last_cons_cons
- \+/\- *theorem* head_cons
- \+/\- *theorem* tail_nil
- \+/\- *theorem* tail_cons
- \+/\- *theorem* index_of_nil
- \+/\- *theorem* index_of_cons_of_eq
- \+/\- *theorem* index_of_cons_of_ne
- \+/\- *theorem* index_of_of_not_mem
- \+/\- *theorem* ith_zero
- \+/\- *theorem* ith_succ
- \+/\- *theorem* taken_zero
- \+/\- *theorem* taken_nil
- \+/\- *theorem* count_nil
- \+/\- *theorem* count_cons_self
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_append
- \+/\- *theorem* count_concat
- \+/\- *theorem* count_eq_zero_of_not_mem

Modified data/list/comb.lean
- \+/\- *theorem* length_map_accumr
- \+/\- *theorem* length_map_accumr₂
- \+/\- *theorem* foldl_nil
- \+/\- *theorem* foldl_cons
- \+/\- *theorem* foldr_nil
- \+/\- *theorem* foldr_cons
- \+/\- *theorem* foldl_append
- \+/\- *theorem* foldr_append
- \+/\- *theorem* length_replicate
- \+/\- *theorem* all_nil
- \+/\- *theorem* all_cons
- \+/\- *theorem* any_nil
- \+/\- *theorem* any_cons
- \+/\- *theorem* forall_mem_cons_iff
- \+/\- *theorem* exists_mem_cons_iff
- \+/\- *theorem* zip_cons_cons
- \+/\- *theorem* zip_nil_left
- \+/\- *theorem* zip_nil_right
- \+/\- *theorem* unzip_nil
- \+/\- *theorem* unzip_cons
- \- *def* decidable_forall_mem
- \- *def* decidable_exists_mem

Modified data/list/perm.lean
- \+/\- *theorem* perm_cons_app_simp
- \+/\- *theorem* perm_app_comm
- \+/\- *theorem* perm_rev_simp
- \+/\- *theorem* perm_induction_on
- \+/\- *theorem* perm_map

Modified data/list/set.lean
- \+/\- *theorem* insert_nil
- \+/\- *theorem* insert_of_mem
- \+/\- *theorem* insert_of_not_mem
- \+/\- *theorem* mem_insert_self
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* length_insert_of_mem
- \+/\- *theorem* length_insert_of_not_mem
- \+/\- *theorem* erase_nil
- \+/\- *theorem* erase_cons_head
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* length_erase_of_mem
- \+/\- *theorem* erase_of_not_mem
- \+/\- *theorem* upto_nil
- \+/\- *theorem* upto_succ
- \+/\- *theorem* length_upto
- \+/\- *theorem* union_nil
- \+/\- *theorem* union_cons
- \+/\- *theorem* mem_union_iff
- \+/\- *theorem* inter_nil
- \+/\- *theorem* inter_cons_of_mem
- \+/\- *theorem* inter_cons_of_not_mem
- \+/\- *theorem* mem_inter_iff
- \+/\- *theorem* mem_erase_dup_iff

Modified data/list/sort.lean
- \- *theorem* ordered_insert_nil
- \- *theorem* ordered_insert_cons

Modified data/nat/basic.lean
- \+/\- *theorem* succ_add_eq_succ_add

Modified data/nat/sub.lean
- \+/\- *theorem* dist_comm
- \+/\- *theorem* dist_self

Modified data/rat.lean
- \- *def* decidable_nonneg

Modified data/set/basic.lean
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* mem_sep_eq

Modified data/set/finite.lean
- \+/\- *theorem* finite_insert
- \+/\- *theorem* finite_singleton

Modified data/set/lattice.lean
- \+/\- *theorem* mem_Union_eq
- \+/\- *theorem* mem_Inter_eq
- \+/\- *theorem* bInter_empty
- \+/\- *theorem* bInter_univ
- \+/\- *theorem* bInter_singleton
- \+/\- *theorem* bInter_insert
- \+/\- *theorem* bUnion_empty
- \+/\- *theorem* bUnion_univ
- \+/\- *theorem* bUnion_singleton
- \+/\- *theorem* bUnion_insert
- \+/\- *theorem* mem_sUnion_eq
- \+/\- *theorem* mem_sInter_eq
- \+/\- *theorem* sUnion_empty
- \+/\- *theorem* sInter_empty
- \+/\- *theorem* sUnion_singleton
- \+/\- *theorem* sInter_singleton
- \+/\- *theorem* sUnion_insert
- \+/\- *theorem* sInter_insert
- \+/\- *theorem* sUnion_image
- \+/\- *theorem* sInter_image
- \+/\- *theorem* union_same_compl
- \+/\- *theorem* sdiff_singleton_eq_same
- \+/\- *theorem* insert_sdiff_singleton
- \+/\- *def* Union
- \+/\- *def* Inter
- \+/\- *def* sInter

Modified logic/basic.lean
- \+/\- *theorem* prod.mk.inj_iff
- \+/\- *theorem* prod.forall
- \+/\- *theorem* prod.exists
- \+/\- *theorem* set_of_subset_set_of

Modified tactic/converter/binders.lean
- \+/\- *theorem* mem_image

Modified tests/examples.lean
- \+/\- *theorem* mem_set_of

Modified topology/continuity.lean
- \+/\- *theorem* false_neq_true
- \+/\- *theorem* open_singleton_true

Modified topology/topological_space.lean
- \+/\- *theorem* open_univ
- \+/\- *theorem* open_empty
- \+/\- *theorem* closed_empty
- \+/\- *theorem* closed_univ
- \+/\- *theorem* closed_compl_iff_open
- \+/\- *theorem* open_compl_iff_closed
- \+/\- *theorem* open_interior
- \+/\- *theorem* interior_empty
- \+/\- *theorem* interior_univ
- \+/\- *theorem* interior_interior
- \+/\- *theorem* interior_inter
- \+/\- *theorem* closed_closure
- \+/\- *theorem* closure_empty
- \+/\- *theorem* closure_univ
- \+/\- *theorem* closure_closure
- \+/\- *theorem* closure_union
- \+/\- *theorem* interior_compl_eq
- \+/\- *theorem* closure_compl_eq
- \+/\- *theorem* nhds_neq_bot



## [2017-07-23 18:39:51+01:00](https://github.com/leanprover-community/mathlib/commit/a4b157b)
chore(data/nat): remove addl
#### Estimated changes
Modified data/nat/basic.lean
- \- *theorem* addl_zero_left
- \- *theorem* addl_succ_left
- \- *theorem* zero_has_zero
- \- *theorem* addl_zero_right
- \- *theorem* addl_succ_right
- \- *theorem* add_eq_addl
- \- *def* addl



## [2017-07-23 18:29:16+01:00](https://github.com/leanprover-community/mathlib/commit/5816424)
refactor(*): use 'lemma' iff statement is private
#### Estimated changes
Modified algebra/lattice/basic.lean
- \- *lemma* le_top
- \- *lemma* top_unique
- \- *lemma* eq_top_iff
- \- *lemma* top_le_iff
- \- *lemma* bot_le
- \- *lemma* bot_unique
- \- *lemma* eq_bot_iff
- \- *lemma* le_bot_iff
- \- *lemma* neq_bot_of_le_neq_bot
- \- *lemma* le_sup_left
- \- *lemma* le_sup_left'
- \- *lemma* le_sup_right
- \- *lemma* le_sup_right'
- \- *lemma* le_sup_left_of_le
- \- *lemma* le_sup_right_of_le
- \- *lemma* sup_le
- \- *lemma* sup_le_iff
- \- *lemma* sup_of_le_left
- \- *lemma* sup_of_le_right
- \- *lemma* sup_le_sup
- \- *lemma* le_of_sup_eq
- \- *lemma* sup_idem
- \- *lemma* sup_comm
- \- *lemma* sup_assoc
- \- *lemma* inf_le_left
- \- *lemma* inf_le_left'
- \- *lemma* inf_le_right
- \- *lemma* inf_le_right'
- \- *lemma* le_inf
- \- *lemma* inf_le_left_of_le
- \- *lemma* inf_le_right_of_le
- \- *lemma* le_inf_iff
- \- *lemma* inf_of_le_left
- \- *lemma* inf_of_le_right
- \- *lemma* inf_le_inf
- \- *lemma* le_of_inf_eq
- \- *lemma* inf_idem
- \- *lemma* inf_comm
- \- *lemma* inf_assoc
- \- *lemma* top_sup_eq
- \- *lemma* sup_top_eq
- \- *lemma* bot_sup_eq
- \- *lemma* sup_bot_eq
- \- *lemma* sup_eq_bot_iff
- \- *lemma* top_inf_eq
- \- *lemma* inf_top_eq
- \- *lemma* inf_eq_top_iff
- \- *lemma* bot_inf_eq
- \- *lemma* inf_bot_eq
- \- *lemma* sup_inf_le
- \- *lemma* le_inf_sup
- \- *lemma* inf_sup_self
- \- *lemma* sup_inf_self
- \+ *theorem* le_top
- \+ *theorem* top_unique
- \+ *theorem* eq_top_iff
- \+ *theorem* top_le_iff
- \+ *theorem* bot_le
- \+ *theorem* bot_unique
- \+ *theorem* eq_bot_iff
- \+ *theorem* le_bot_iff
- \+ *theorem* neq_bot_of_le_neq_bot
- \+ *theorem* le_sup_left
- \+ *theorem* le_sup_left'
- \+ *theorem* le_sup_right
- \+ *theorem* le_sup_right'
- \+ *theorem* le_sup_left_of_le
- \+ *theorem* le_sup_right_of_le
- \+ *theorem* sup_le
- \+ *theorem* sup_le_iff
- \+ *theorem* sup_of_le_left
- \+ *theorem* sup_of_le_right
- \+ *theorem* sup_le_sup
- \+ *theorem* le_of_sup_eq
- \+ *theorem* sup_idem
- \+ *theorem* sup_comm
- \+ *theorem* sup_assoc
- \+ *theorem* inf_le_left
- \+ *theorem* inf_le_left'
- \+ *theorem* inf_le_right
- \+ *theorem* inf_le_right'
- \+ *theorem* le_inf
- \+ *theorem* inf_le_left_of_le
- \+ *theorem* inf_le_right_of_le
- \+ *theorem* le_inf_iff
- \+ *theorem* inf_of_le_left
- \+ *theorem* inf_of_le_right
- \+ *theorem* inf_le_inf
- \+ *theorem* le_of_inf_eq
- \+ *theorem* inf_idem
- \+ *theorem* inf_comm
- \+ *theorem* inf_assoc
- \+ *theorem* top_sup_eq
- \+ *theorem* sup_top_eq
- \+ *theorem* bot_sup_eq
- \+ *theorem* sup_bot_eq
- \+ *theorem* sup_eq_bot_iff
- \+ *theorem* top_inf_eq
- \+ *theorem* inf_top_eq
- \+ *theorem* inf_eq_top_iff
- \+ *theorem* bot_inf_eq
- \+ *theorem* inf_bot_eq
- \+ *theorem* sup_inf_le
- \+ *theorem* le_inf_sup
- \+ *theorem* inf_sup_self
- \+ *theorem* sup_inf_self

Modified algebra/lattice/boolean_algebra.lean
- \- *lemma* le_sup_inf
- \- *lemma* sup_inf_left
- \- *lemma* sup_inf_right
- \- *lemma* inf_sup_left
- \- *lemma* inf_sup_right
- \- *lemma* inf_neg_eq_bot
- \- *lemma* neg_inf_eq_bot
- \- *lemma* sup_neg_eq_top
- \- *lemma* neg_sup_eq_top
- \- *lemma* sub_eq
- \- *lemma* neg_unique
- \- *lemma* neg_top
- \- *lemma* neg_bot
- \- *lemma* neg_neg
- \- *lemma* neg_eq_neg_of_eq
- \- *lemma* neg_eq_neg_iff
- \- *lemma* neg_inf
- \- *lemma* neg_sup
- \- *lemma* neg_le_neg
- \- *lemma* neg_le_neg_iff_le
- \- *lemma* le_neg_of_le_neg
- \- *lemma* neg_le_of_neg_le
- \- *lemma* neg_le_iff_neg_le
- \- *lemma* sup_sub_same
- \- *lemma* sub_eq_left
- \+ *theorem* le_sup_inf
- \+ *theorem* sup_inf_left
- \+ *theorem* sup_inf_right
- \+ *theorem* inf_sup_left
- \+ *theorem* inf_sup_right
- \+ *theorem* inf_neg_eq_bot
- \+ *theorem* neg_inf_eq_bot
- \+ *theorem* sup_neg_eq_top
- \+ *theorem* neg_sup_eq_top
- \+ *theorem* sub_eq
- \+ *theorem* neg_unique
- \+ *theorem* neg_top
- \+ *theorem* neg_bot
- \+ *theorem* neg_neg
- \+ *theorem* neg_eq_neg_of_eq
- \+ *theorem* neg_eq_neg_iff
- \+ *theorem* neg_inf
- \+ *theorem* neg_sup
- \+ *theorem* neg_le_neg
- \+ *theorem* neg_le_neg_iff_le
- \+ *theorem* le_neg_of_le_neg
- \+ *theorem* neg_le_of_neg_le
- \+ *theorem* neg_le_iff_neg_le
- \+ *theorem* sup_sub_same
- \+ *theorem* sub_eq_left

Modified algebra/lattice/bounded_lattice.lean
- \- *lemma* monotone_and
- \- *lemma* monotone_or
- \+ *theorem* monotone_and
- \+ *theorem* monotone_or

Modified algebra/lattice/complete_boolean_algebra.lean
- \- *lemma* sup_Inf_eq
- \- *lemma* inf_Sup_eq
- \- *lemma* neg_infi
- \- *lemma* neg_supr
- \- *lemma* neg_Inf
- \- *lemma* neg_Sup
- \+ *theorem* sup_Inf_eq
- \+ *theorem* inf_Sup_eq
- \+ *theorem* neg_infi
- \+ *theorem* neg_supr
- \+ *theorem* neg_Inf
- \+ *theorem* neg_Sup

Modified algebra/lattice/complete_lattice.lean
- \- *lemma* le_Sup
- \- *lemma* Sup_le
- \- *lemma* Inf_le
- \- *lemma* le_Inf
- \- *lemma* le_Sup_of_le
- \- *lemma* Inf_le_of_le
- \- *lemma* Sup_le_Sup
- \- *lemma* Inf_le_Inf
- \- *lemma* le_Sup_iff
- \- *lemma* Inf_le_iff
- \- *lemma* Inf_le_Sup
- \- *lemma* Sup_union
- \- *lemma* Sup_inter_le
- \- *lemma* Inf_union
- \- *lemma* le_Inf_inter
- \- *lemma* Sup_empty
- \- *lemma* Inf_empty
- \- *lemma* Sup_univ
- \- *lemma* Inf_univ
- \- *lemma* Sup_insert
- \- *lemma* Inf_insert
- \- *lemma* Sup_singleton
- \- *lemma* Inf_singleton
- \- *lemma* le_supr
- \- *lemma* le_supr'
- \- *lemma* le_supr_of_le
- \- *lemma* supr_le
- \- *lemma* supr_le_supr
- \- *lemma* supr_le_supr2
- \- *lemma* supr_le_supr_const
- \- *lemma* supr_le_iff
- \- *lemma* supr_congr_Prop
- \- *lemma* infi_le
- \- *lemma* infi_le'
- \- *lemma* infi_le₂'
- \- *lemma* infi_le_of_le
- \- *lemma* le_infi
- \- *lemma* infi_le_infi
- \- *lemma* infi_le_infi2
- \- *lemma* infi_le_infi_const
- \- *lemma* le_infi_iff
- \- *lemma* infi_congr_Prop
- \- *lemma* infi_const
- \- *lemma* supr_const
- \- *lemma* infi_comm
- \- *lemma* supr_comm
- \- *lemma* infi_infi_eq_left
- \- *lemma* infi_infi_eq_right
- \- *lemma* supr_supr_eq_left
- \- *lemma* supr_supr_eq_right
- \- *lemma* foo
- \- *lemma* foo'
- \- *lemma* infi_inf_eq
- \- *lemma* supr_sup_eq
- \- *lemma* infi_false
- \- *lemma* supr_false
- \- *lemma* infi_true
- \- *lemma* supr_true
- \- *lemma* infi_exists
- \- *lemma* supr_exists
- \- *lemma* infi_and
- \- *lemma* supr_and
- \- *lemma* infi_or
- \- *lemma* supr_or
- \- *lemma* Inf_eq_infi
- \- *lemma* Sup_eq_supr
- \- *lemma* Inf_image
- \- *lemma* Sup_image
- \- *lemma* infi_emptyset
- \- *lemma* supr_emptyset
- \- *lemma* infi_univ
- \- *lemma* supr_univ
- \- *lemma* infi_union
- \- *lemma* supr_union
- \- *lemma* infi_insert
- \- *lemma* supr_insert
- \- *lemma* infi_singleton
- \- *lemma* supr_singleton
- \- *lemma* infi_empty
- \- *lemma* supr_empty
- \- *lemma* infi_unit
- \- *lemma* supr_unit
- \- *lemma* infi_subtype
- \- *lemma* supr_subtype
- \- *lemma* infi_sigma
- \- *lemma* supr_sigma
- \- *lemma* infi_prod
- \- *lemma* supr_prod
- \- *lemma* infi_sum
- \- *lemma* supr_sum
- \- *lemma* monotone_Sup_of_monotone
- \- *lemma* monotone_Inf_of_monotone
- \- *lemma* Inf_eq_top
- \- *lemma* infi_eq_top
- \- *lemma* Sup_eq_bot
- \- *lemma* supr_eq_top
- \+ *theorem* le_Sup
- \+ *theorem* Sup_le
- \+ *theorem* Inf_le
- \+ *theorem* le_Inf
- \+ *theorem* le_Sup_of_le
- \+ *theorem* Inf_le_of_le
- \+ *theorem* Sup_le_Sup
- \+ *theorem* Inf_le_Inf
- \+ *theorem* le_Sup_iff
- \+ *theorem* Inf_le_iff
- \+ *theorem* Inf_le_Sup
- \+ *theorem* Sup_union
- \+ *theorem* Sup_inter_le
- \+ *theorem* Inf_union
- \+ *theorem* le_Inf_inter
- \+ *theorem* Sup_empty
- \+ *theorem* Inf_empty
- \+ *theorem* Sup_univ
- \+ *theorem* Inf_univ
- \+ *theorem* Sup_insert
- \+ *theorem* Inf_insert
- \+ *theorem* Sup_singleton
- \+ *theorem* Inf_singleton
- \+ *theorem* le_supr
- \+ *theorem* le_supr'
- \+ *theorem* le_supr_of_le
- \+ *theorem* supr_le
- \+ *theorem* supr_le_supr
- \+ *theorem* supr_le_supr2
- \+ *theorem* supr_le_supr_const
- \+ *theorem* supr_le_iff
- \+ *theorem* supr_congr_Prop
- \+ *theorem* infi_le
- \+ *theorem* infi_le'
- \+ *theorem* infi_le₂'
- \+ *theorem* infi_le_of_le
- \+ *theorem* le_infi
- \+ *theorem* infi_le_infi
- \+ *theorem* infi_le_infi2
- \+ *theorem* infi_le_infi_const
- \+ *theorem* le_infi_iff
- \+ *theorem* infi_congr_Prop
- \+ *theorem* infi_const
- \+ *theorem* supr_const
- \+ *theorem* infi_comm
- \+ *theorem* supr_comm
- \+ *theorem* infi_infi_eq_left
- \+ *theorem* infi_infi_eq_right
- \+ *theorem* supr_supr_eq_left
- \+ *theorem* supr_supr_eq_right
- \+ *theorem* foo
- \+ *theorem* foo'
- \+ *theorem* infi_inf_eq
- \+ *theorem* supr_sup_eq
- \+ *theorem* infi_false
- \+ *theorem* supr_false
- \+ *theorem* infi_true
- \+ *theorem* supr_true
- \+ *theorem* infi_exists
- \+ *theorem* supr_exists
- \+ *theorem* infi_and
- \+ *theorem* supr_and
- \+ *theorem* infi_or
- \+ *theorem* supr_or
- \+ *theorem* Inf_eq_infi
- \+ *theorem* Sup_eq_supr
- \+ *theorem* Inf_image
- \+ *theorem* Sup_image
- \+ *theorem* infi_emptyset
- \+ *theorem* supr_emptyset
- \+ *theorem* infi_univ
- \+ *theorem* supr_univ
- \+ *theorem* infi_union
- \+ *theorem* supr_union
- \+ *theorem* infi_insert
- \+ *theorem* supr_insert
- \+ *theorem* infi_singleton
- \+ *theorem* supr_singleton
- \+ *theorem* infi_empty
- \+ *theorem* supr_empty
- \+ *theorem* infi_unit
- \+ *theorem* supr_unit
- \+ *theorem* infi_subtype
- \+ *theorem* supr_subtype
- \+ *theorem* infi_sigma
- \+ *theorem* supr_sigma
- \+ *theorem* infi_prod
- \+ *theorem* supr_prod
- \+ *theorem* infi_sum
- \+ *theorem* supr_sum
- \+ *theorem* monotone_Sup_of_monotone
- \+ *theorem* monotone_Inf_of_monotone
- \+ *theorem* Inf_eq_top
- \+ *theorem* infi_eq_top
- \+ *theorem* Sup_eq_bot
- \+ *theorem* supr_eq_top

Modified algebra/lattice/filter.lean
- \- *lemma* pure_seq_eq_map
- \- *lemma* prod.mk.eta
- \- *lemma* prod.swap_swap
- \- *lemma* prod.fst_swap
- \- *lemma* prod.snd_swap
- \- *lemma* prod.swap_prod_mk
- \- *lemma* prod.swap_swap_eq
- \- *lemma* Inf_eq_finite_sets
- \- *lemma* Sup_le_iff
- \- *lemma* fmap_eq_image
- \- *lemma* mem_seq_iff
- \- *lemma* mem_prod_eq
- \- *lemma* prod_vimage_eq
- \- *lemma* prod_mono
- \- *lemma* prod_inter_prod
- \- *lemma* monotone_prod
- \- *lemma* image_swap_prod
- \- *lemma* prod_image_image_eq
- \- *lemma* prod_singleton_singleton
- \- *lemma* prod_neq_empty_iff
- \- *lemma* prod_mk_mem_set_prod_eq
- \- *lemma* monotone_inter
- \- *lemma* vimage_set_of_eq
- \- *lemma* set_of_mem_eq
- \- *lemma* mem_image_iff_of_inverse
- \- *lemma* image_eq_vimage_of_inverse
- \- *lemma* image_swap_eq_vimage_swap
- \- *lemma* monotone_set_of
- \- *lemma* diff_right_antimono
- \- *lemma* sUnion_mono
- \- *lemma* Union_subset_Union
- \- *lemma* Union_subset_Union2
- \- *lemma* Union_subset_Union_const
- \- *lemma* diff_neq_empty
- \- *lemma* diff_empty
- \- *lemma* implies_implies_true_iff
- \- *lemma* not_not_mem_iff
- \- *lemma* singleton_neq_emptyset
- \- *lemma* eq_of_sup_eq_inf_eq
- \- *lemma* inf_eq_bot_iff_le_compl
- \- *lemma* compl_image_set_of
- \- *lemma* neg_subset_neg_iff_subset
- \- *lemma* sUnion_eq_Union
- \- *lemma* directed_on_Union
- \- *lemma* directed_of_chain
- \- *lemma* filter_eq
- \- *lemma* univ_mem_sets'
- \- *lemma* univ_mem_sets
- \- *lemma* inter_mem_sets
- \- *lemma* Inter_mem_sets
- \- *lemma* exists_sets_subset_iff
- \- *lemma* monotone_mem_sets
- \- *lemma* mem_join_sets
- \- *lemma* mem_principal_sets
- \- *lemma* le_principal_iff
- \- *lemma* principal_mono
- \- *lemma* monotone_principal
- \- *lemma* principal_eq_iff_eq
- \- *lemma* map_principal
- \- *lemma* join_principal_eq_Sup
- \- *lemma* mem_inf_sets_of_left
- \- *lemma* mem_inf_sets_of_right
- \- *lemma* mem_bot_sets
- \- *lemma* empty_in_sets_eq_bot
- \- *lemma* inhabited_of_mem_sets
- \- *lemma* filter_eq_bot_of_not_nonempty
- \- *lemma* forall_sets_neq_empty_iff_neq_bot
- \- *lemma* mem_sets_of_neq_bot
- \- *lemma* mem_sup_sets
- \- *lemma* mem_inf_sets
- \- *lemma* infi_sets_eq
- \- *lemma* infi_sets_eq'
- \- *lemma* Inf_sets_eq_finite
- \- *lemma* supr_sets_eq
- \- *lemma* sup_join
- \- *lemma* supr_join
- \- *lemma* binfi_sup_eq
- \- *lemma* infi_sup_eq
- \- *lemma* inf_principal
- \- *lemma* sup_principal
- \- *lemma* supr_principal
- \- *lemma* principal_univ
- \- *lemma* principal_empty
- \- *lemma* principal_eq_bot_iff
- \- *lemma* mem_pure
- \- *lemma* mem_map
- \- *lemma* image_mem_map
- \- *lemma* map_id
- \- *lemma* map_compose
- \- *lemma* map_sup
- \- *lemma* supr_map
- \- *lemma* map_bot
- \- *lemma* map_eq_bot_iff
- \- *lemma* map_mono
- \- *lemma* monotone_map
- \- *lemma* map_infi_le
- \- *lemma* map_infi_eq
- \- *lemma* map_binfi_eq
- \- *lemma* mem_bind_sets
- \- *lemma* bind_mono
- \- *lemma* bind_sup
- \- *lemma* bind_mono2
- \- *lemma* principal_bind
- \- *lemma* seq_mono
- \- *lemma* fmap_principal
- \- *lemma* mem_return_sets
- \- *lemma* infi_neq_bot_of_directed
- \- *lemma* infi_neq_bot_iff_of_directed
- \- *lemma* return_neq_bot
- \- *lemma* mem_vmap_of_mem
- \- *lemma* vmap_mono
- \- *lemma* monotone_vmap
- \- *lemma* vmap_principal
- \- *lemma* vimage_mem_vmap
- \- *lemma* le_map_vmap
- \- *lemma* vmap_map
- \- *lemma* vmap_neq_bot
- \- *lemma* vmap_neq_bot_of_surj
- \- *lemma* map_vmap_le
- \- *lemma* le_vmap_map
- \- *lemma* vmap_vmap_comp
- \- *lemma* le_vmap_iff_map_le
- \- *lemma* lift_sets_eq
- \- *lemma* mem_lift
- \- *lemma* mem_lift_iff
- \- *lemma* lift_mono
- \- *lemma* lift_mono'
- \- *lemma* map_lift_eq
- \- *lemma* vmap_lift_eq
- \- *lemma* vmap_lift_eq2
- \- *lemma* map_lift_eq2
- \- *lemma* lift_comm
- \- *lemma* lift_assoc
- \- *lemma* lift_lift_same_le_lift
- \- *lemma* lift_lift_same_eq_lift
- \- *lemma* lift_principal
- \- *lemma* monotone_lift
- \- *lemma* lift_neq_bot_iff
- \- *lemma* mem_lift'
- \- *lemma* mem_lift'_iff
- \- *lemma* lift'_mono
- \- *lemma* lift'_mono'
- \- *lemma* lift'_cong
- \- *lemma* map_lift'_eq
- \- *lemma* map_lift'_eq2
- \- *lemma* vmap_lift'_eq
- \- *lemma* vmap_lift'_eq2
- \- *lemma* lift'_principal
- \- *lemma* principal_le_lift'
- \- *lemma* monotone_lift'
- \- *lemma* lift_lift'_assoc
- \- *lemma* lift'_lift'_assoc
- \- *lemma* lift'_lift_assoc
- \- *lemma* lift_lift'_same_le_lift'
- \- *lemma* lift_lift'_same_eq_lift'
- \- *lemma* lift'_inf_principal_eq
- \- *lemma* lift'_neq_bot_iff
- \- *lemma* lift'_id
- \- *lemma* le_lift'
- \- *lemma* vmap_eq_lift'
- \- *lemma* prod_mem_prod
- \- *lemma* prod_same_eq
- \- *lemma* mem_prod_iff
- \- *lemma* mem_prod_same_iff
- \- *lemma* prod_comm
- \- *lemma* prod_lift_lift
- \- *lemma* prod_lift'_lift'
- \- *lemma* prod_map_map_eq
- \- *lemma* prod_vmap_vmap_eq
- \- *lemma* prod_inf_prod
- \- *lemma* prod_neq_bot
- \- *lemma* prod_principal_principal
- \- *lemma* mem_infi_sets
- \- *lemma* mem_top_sets_iff
- \- *lemma* infi_sets_induct
- \- *lemma* lift_infi
- \- *lemma* lift_infi'
- \- *lemma* lift'_infi
- \- *lemma* map_eq_vmap_of_inverse
- \- *lemma* map_swap_vmap_swap_eq
- \- *lemma* ultrafilter_pure
- \- *lemma* ultrafilter_unique
- \- *lemma* exists_ultrafilter
- \- *lemma* le_of_ultrafilter
- \- *lemma* mem_or_compl_mem_of_ultrafilter
- \- *lemma* mem_or_mem_of_ultrafilter
- \- *lemma* mem_of_finite_sUnion_ultrafilter
- \- *lemma* mem_of_finite_Union_ultrafilter
- \- *lemma* ultrafilter_of_split
- \- *lemma* ultrafilter_map
- \- *lemma* ultrafilter_of_spec
- \- *lemma* ultrafilter_of_le
- \- *lemma* ultrafilter_ultrafilter_of
- \- *lemma* ultrafilter_of_ultrafilter
- \+ *theorem* pure_seq_eq_map
- \+ *theorem* prod.mk.eta
- \+ *theorem* prod.swap_swap
- \+ *theorem* prod.fst_swap
- \+ *theorem* prod.snd_swap
- \+ *theorem* prod.swap_prod_mk
- \+ *theorem* prod.swap_swap_eq
- \+ *theorem* Inf_eq_finite_sets
- \+ *theorem* Sup_le_iff
- \+ *theorem* fmap_eq_image
- \+ *theorem* mem_seq_iff
- \+ *theorem* mem_prod_eq
- \+ *theorem* prod_vimage_eq
- \+ *theorem* prod_mono
- \+ *theorem* prod_inter_prod
- \+ *theorem* monotone_prod
- \+ *theorem* image_swap_prod
- \+ *theorem* prod_image_image_eq
- \+ *theorem* prod_singleton_singleton
- \+ *theorem* prod_neq_empty_iff
- \+ *theorem* prod_mk_mem_set_prod_eq
- \+ *theorem* monotone_inter
- \+ *theorem* vimage_set_of_eq
- \+ *theorem* set_of_mem_eq
- \+ *theorem* mem_image_iff_of_inverse
- \+ *theorem* image_eq_vimage_of_inverse
- \+ *theorem* image_swap_eq_vimage_swap
- \+ *theorem* monotone_set_of
- \+ *theorem* diff_right_antimono
- \+ *theorem* sUnion_mono
- \+ *theorem* Union_subset_Union
- \+ *theorem* Union_subset_Union2
- \+ *theorem* Union_subset_Union_const
- \+ *theorem* diff_neq_empty
- \+ *theorem* diff_empty
- \+ *theorem* implies_implies_true_iff
- \+ *theorem* not_not_mem_iff
- \+ *theorem* singleton_neq_emptyset
- \+ *theorem* eq_of_sup_eq_inf_eq
- \+ *theorem* inf_eq_bot_iff_le_compl
- \+ *theorem* compl_image_set_of
- \+ *theorem* neg_subset_neg_iff_subset
- \+ *theorem* sUnion_eq_Union
- \+ *theorem* directed_on_Union
- \+ *theorem* directed_of_chain
- \+ *theorem* filter_eq
- \+ *theorem* univ_mem_sets'
- \+ *theorem* univ_mem_sets
- \+ *theorem* inter_mem_sets
- \+ *theorem* Inter_mem_sets
- \+ *theorem* exists_sets_subset_iff
- \+ *theorem* monotone_mem_sets
- \+ *theorem* mem_join_sets
- \+ *theorem* mem_principal_sets
- \+ *theorem* le_principal_iff
- \+ *theorem* principal_mono
- \+ *theorem* monotone_principal
- \+ *theorem* principal_eq_iff_eq
- \+ *theorem* map_principal
- \+ *theorem* join_principal_eq_Sup
- \+ *theorem* mem_inf_sets_of_left
- \+ *theorem* mem_inf_sets_of_right
- \+ *theorem* mem_bot_sets
- \+ *theorem* empty_in_sets_eq_bot
- \+ *theorem* inhabited_of_mem_sets
- \+ *theorem* filter_eq_bot_of_not_nonempty
- \+ *theorem* forall_sets_neq_empty_iff_neq_bot
- \+ *theorem* mem_sets_of_neq_bot
- \+ *theorem* mem_sup_sets
- \+ *theorem* mem_inf_sets
- \+ *theorem* infi_sets_eq
- \+ *theorem* infi_sets_eq'
- \+ *theorem* Inf_sets_eq_finite
- \+ *theorem* supr_sets_eq
- \+ *theorem* sup_join
- \+ *theorem* supr_join
- \+ *theorem* binfi_sup_eq
- \+ *theorem* infi_sup_eq
- \+ *theorem* inf_principal
- \+ *theorem* sup_principal
- \+ *theorem* supr_principal
- \+ *theorem* principal_univ
- \+ *theorem* principal_empty
- \+ *theorem* principal_eq_bot_iff
- \+ *theorem* mem_pure
- \+ *theorem* mem_map
- \+ *theorem* image_mem_map
- \+ *theorem* map_id
- \+ *theorem* map_compose
- \+ *theorem* map_sup
- \+ *theorem* supr_map
- \+ *theorem* map_bot
- \+ *theorem* map_eq_bot_iff
- \+ *theorem* map_mono
- \+ *theorem* monotone_map
- \+ *theorem* map_infi_le
- \+ *theorem* map_infi_eq
- \+ *theorem* map_binfi_eq
- \+ *theorem* mem_bind_sets
- \+ *theorem* bind_mono
- \+ *theorem* bind_sup
- \+ *theorem* bind_mono2
- \+ *theorem* principal_bind
- \+ *theorem* seq_mono
- \+ *theorem* fmap_principal
- \+ *theorem* mem_return_sets
- \+ *theorem* infi_neq_bot_of_directed
- \+ *theorem* infi_neq_bot_iff_of_directed
- \+ *theorem* return_neq_bot
- \+ *theorem* mem_vmap_of_mem
- \+ *theorem* vmap_mono
- \+ *theorem* monotone_vmap
- \+ *theorem* vmap_principal
- \+ *theorem* vimage_mem_vmap
- \+ *theorem* le_map_vmap
- \+ *theorem* vmap_map
- \+ *theorem* vmap_neq_bot
- \+ *theorem* vmap_neq_bot_of_surj
- \+ *theorem* map_vmap_le
- \+ *theorem* le_vmap_map
- \+ *theorem* vmap_vmap_comp
- \+ *theorem* le_vmap_iff_map_le
- \+ *theorem* lift_sets_eq
- \+ *theorem* mem_lift
- \+ *theorem* mem_lift_iff
- \+ *theorem* lift_mono
- \+ *theorem* lift_mono'
- \+ *theorem* map_lift_eq
- \+ *theorem* vmap_lift_eq
- \+ *theorem* vmap_lift_eq2
- \+ *theorem* map_lift_eq2
- \+ *theorem* lift_comm
- \+ *theorem* lift_assoc
- \+ *theorem* lift_lift_same_le_lift
- \+ *theorem* lift_lift_same_eq_lift
- \+ *theorem* lift_principal
- \+ *theorem* monotone_lift
- \+ *theorem* lift_neq_bot_iff
- \+ *theorem* mem_lift'
- \+ *theorem* mem_lift'_iff
- \+ *theorem* lift'_mono
- \+ *theorem* lift'_mono'
- \+ *theorem* lift'_cong
- \+ *theorem* map_lift'_eq
- \+ *theorem* map_lift'_eq2
- \+ *theorem* vmap_lift'_eq
- \+ *theorem* vmap_lift'_eq2
- \+ *theorem* lift'_principal
- \+ *theorem* principal_le_lift'
- \+ *theorem* monotone_lift'
- \+ *theorem* lift_lift'_assoc
- \+ *theorem* lift'_lift'_assoc
- \+ *theorem* lift'_lift_assoc
- \+ *theorem* lift_lift'_same_le_lift'
- \+ *theorem* lift_lift'_same_eq_lift'
- \+ *theorem* lift'_inf_principal_eq
- \+ *theorem* lift'_neq_bot_iff
- \+ *theorem* lift'_id
- \+ *theorem* le_lift'
- \+ *theorem* vmap_eq_lift'
- \+ *theorem* prod_mem_prod
- \+ *theorem* prod_same_eq
- \+ *theorem* mem_prod_iff
- \+ *theorem* mem_prod_same_iff
- \+ *theorem* prod_comm
- \+ *theorem* prod_lift_lift
- \+ *theorem* prod_lift'_lift'
- \+ *theorem* prod_map_map_eq
- \+ *theorem* prod_vmap_vmap_eq
- \+ *theorem* prod_inf_prod
- \+ *theorem* prod_neq_bot
- \+ *theorem* prod_principal_principal
- \+ *theorem* mem_infi_sets
- \+ *theorem* mem_top_sets_iff
- \+ *theorem* infi_sets_induct
- \+ *theorem* lift_infi
- \+ *theorem* lift_infi'
- \+ *theorem* lift'_infi
- \+ *theorem* map_eq_vmap_of_inverse
- \+ *theorem* map_swap_vmap_swap_eq
- \+ *theorem* ultrafilter_pure
- \+ *theorem* ultrafilter_unique
- \+ *theorem* exists_ultrafilter
- \+ *theorem* le_of_ultrafilter
- \+ *theorem* mem_or_compl_mem_of_ultrafilter
- \+ *theorem* mem_or_mem_of_ultrafilter
- \+ *theorem* mem_of_finite_sUnion_ultrafilter
- \+ *theorem* mem_of_finite_Union_ultrafilter
- \+ *theorem* ultrafilter_of_split
- \+ *theorem* ultrafilter_map
- \+ *theorem* ultrafilter_of_spec
- \+ *theorem* ultrafilter_of_le
- \+ *theorem* ultrafilter_ultrafilter_of
- \+ *theorem* ultrafilter_of_ultrafilter

Modified algebra/lattice/fixed_points.lean
- \- *lemma* ge_of_eq
- \- *lemma* lfp_le
- \- *lemma* le_lfp
- \- *lemma* lfp_eq
- \- *lemma* lfp_induct
- \- *lemma* monotone_lfp
- \- *lemma* le_gfp
- \- *lemma* gfp_le
- \- *lemma* gfp_eq
- \- *lemma* gfp_induct
- \- *lemma* monotone_gfp
- \- *lemma* lfp_comp
- \- *lemma* gfp_comp
- \- *lemma* lfp_lfp
- \- *lemma* gfp_gfp
- \+ *theorem* ge_of_eq
- \+ *theorem* lfp_le
- \+ *theorem* le_lfp
- \+ *theorem* lfp_eq
- \+ *theorem* lfp_induct
- \+ *theorem* monotone_lfp
- \+ *theorem* le_gfp
- \+ *theorem* gfp_le
- \+ *theorem* gfp_eq
- \+ *theorem* gfp_induct
- \+ *theorem* monotone_gfp
- \+ *theorem* lfp_comp
- \+ *theorem* gfp_comp
- \+ *theorem* lfp_lfp
- \+ *theorem* gfp_gfp

Modified algebra/lattice/zorn.lean
- \- *lemma* chain_insert
- \- *lemma* succ_spec
- \- *lemma* chain_succ
- \- *lemma* super_of_not_max
- \- *lemma* succ_increasing
- \- *lemma* chain_closure_empty
- \- *lemma* chain_closure_closure
- \- *lemma* chain_closure_total
- \- *lemma* chain_closure_succ_fixpoint
- \- *lemma* chain_closure_succ_fixpoint_iff
- \- *lemma* chain_chain_closure
- \- *lemma* max_chain_spec
- \- *lemma* zorn
- \- *lemma* zorn_weak_order
- \+ *theorem* chain_insert
- \+ *theorem* succ_spec
- \+ *theorem* chain_succ
- \+ *theorem* super_of_not_max
- \+ *theorem* succ_increasing
- \+ *theorem* chain_closure_empty
- \+ *theorem* chain_closure_closure
- \+ *theorem* chain_closure_total
- \+ *theorem* chain_closure_succ_fixpoint
- \+ *theorem* chain_closure_succ_fixpoint_iff
- \+ *theorem* chain_chain_closure
- \+ *theorem* max_chain_spec
- \+ *theorem* zorn
- \+ *theorem* zorn_weak_order

Modified algebra/order.lean
- \- *lemma* monotone_id
- \- *lemma* monotone_const
- \- *lemma* monotone_comp
- \- *lemma* le_dual_eq_le
- \- *lemma* comp_le_comp_left_of_monotone
- \- *lemma* monotone_lam
- \- *lemma* monotone_app
- \+ *theorem* monotone_id
- \+ *theorem* monotone_const
- \+ *theorem* monotone_comp
- \+ *theorem* le_dual_eq_le
- \+ *theorem* comp_le_comp_left_of_monotone
- \+ *theorem* monotone_lam
- \+ *theorem* monotone_app

Modified data/bitvec.lean


Modified data/bool.lean


Modified data/fin.lean
- \- *lemma* lt_succ_of_lt
- \- *lemma* eq_of_lt_succ_of_not_lt
- \+ *theorem* lt_succ_of_lt
- \+ *theorem* eq_of_lt_succ_of_not_lt

Modified data/hash_map.lean
- \- *lemma* foldl_eq_lem
- \- *lemma* insert_lemma
- \+ *theorem* foldl_eq_lem
- \+ *theorem* insert_theorem
- \- *theorem* valid_aux.insert_lemma1

Modified data/int/basic.lean
- \- *lemma* neg_add_neg
- \+ *theorem* neg_add_neg

Modified data/list/basic.lean
- \- *lemma* cons_ne_nil
- \- *lemma* head_eq_of_cons_eq
- \- *lemma* tail_eq_of_cons_eq
- \- *lemma* cons_inj
- \- *lemma* last_singleton
- \- *lemma* last_cons_cons
- \- *lemma* index_of_le_length
- \- *lemma* not_mem_of_index_of_eq_length
- \- *lemma* index_of_lt_length
- \- *lemma* ith_zero
- \- *lemma* ith_succ
- \- *lemma* taken_zero
- \- *lemma* taken_nil
- \- *lemma* taken_cons
- \- *lemma* taken_all
- \- *lemma* taken_all_of_ge
- \- *lemma* taken_taken
- \- *lemma* length_taken_le
- \- *lemma* length_taken_eq
- \- *lemma* count_nil
- \- *lemma* count_cons
- \- *lemma* count_cons'
- \- *lemma* count_cons_self
- \- *lemma* count_cons_of_ne
- \- *lemma* count_cons_ge_count
- \- *lemma* count_singleton
- \- *lemma* count_append
- \- *lemma* count_concat
- \- *lemma* mem_of_count_pos
- \- *lemma* count_pos_of_mem
- \- *lemma* mem_iff_count_pos
- \- *lemma* count_eq_zero_of_not_mem
- \- *lemma* not_mem_of_count_eq_zero
- \+ *theorem* cons_ne_nil
- \+ *theorem* head_eq_of_cons_eq
- \+ *theorem* tail_eq_of_cons_eq
- \+ *theorem* cons_inj
- \+ *theorem* last_singleton
- \+ *theorem* last_cons_cons
- \+ *theorem* index_of_le_length
- \+ *theorem* not_mem_of_index_of_eq_length
- \+ *theorem* index_of_lt_length
- \+ *theorem* ith_zero
- \+ *theorem* ith_succ
- \+ *theorem* taken_zero
- \+ *theorem* taken_nil
- \+ *theorem* taken_cons
- \+ *theorem* taken_all
- \+ *theorem* taken_all_of_ge
- \+ *theorem* taken_taken
- \+ *theorem* length_taken_le
- \+ *theorem* length_taken_eq
- \+ *theorem* count_nil
- \+ *theorem* count_cons
- \+ *theorem* count_cons'
- \+ *theorem* count_cons_self
- \+ *theorem* count_cons_of_ne
- \+ *theorem* count_cons_ge_count
- \+ *theorem* count_singleton
- \+ *theorem* count_append
- \+ *theorem* count_concat
- \+ *theorem* mem_of_count_pos
- \+ *theorem* count_pos_of_mem
- \+ *theorem* mem_iff_count_pos
- \+ *theorem* count_eq_zero_of_not_mem
- \+ *theorem* not_mem_of_count_eq_zero

Modified data/list/comb.lean
- \- *lemma* dmap_nil
- \- *lemma* dmap_cons_of_pos
- \- *lemma* dmap_cons_of_neg
- \- *lemma* mem_dmap
- \- *lemma* exists_of_mem_dmap
- \- *lemma* map_dmap_of_inv_of_pos
- \- *lemma* mem_of_dinj_of_mem_dmap
- \- *lemma* not_mem_dmap_of_dinj_of_not_mem
- \+ *theorem* dmap_nil
- \+ *theorem* dmap_cons_of_pos
- \+ *theorem* dmap_cons_of_neg
- \+ *theorem* mem_dmap
- \+ *theorem* exists_of_mem_dmap
- \+ *theorem* map_dmap_of_inv_of_pos
- \+ *theorem* mem_of_dinj_of_mem_dmap
- \+ *theorem* not_mem_dmap_of_dinj_of_not_mem

Modified data/list/perm.lean
- \- *lemma* perm_of_qeq
- \- *lemma* perm_insert_insert
- \+ *theorem* perm_of_qeq
- \+ *theorem* perm_insert_insert

Modified data/list/set.lean
- \- *lemma* erase_nil
- \- *lemma* erase_cons
- \- *lemma* erase_cons_head
- \- *lemma* erase_cons_tail
- \- *lemma* length_erase_of_mem
- \- *lemma* erase_of_not_mem
- \- *lemma* erase_append_left
- \- *lemma* erase_append_right
- \- *lemma* erase_sublist
- \- *lemma* erase_subset
- \- *lemma* disjoint_left
- \- *lemma* disjoint_right
- \- *lemma* disjoint.comm
- \- *lemma* disjoint_of_subset_left
- \- *lemma* disjoint_of_subset_right
- \- *lemma* disjoint_of_disjoint_cons_left
- \- *lemma* disjoint_of_disjoint_cons_right
- \- *lemma* disjoint_nil_left
- \- *lemma* disjoint_nil_right
- \- *lemma* disjoint_cons_of_not_mem_of_disjoint
- \- *lemma* disjoint_append_of_disjoint_left
- \- *lemma* disjoint_of_disjoint_append_left_left
- \- *lemma* disjoint_of_disjoint_append_left_right
- \- *lemma* disjoint_of_disjoint_append_right_left
- \- *lemma* disjoint_of_disjoint_append_right_right
- \- *lemma* upto_step
- \- *lemma* dmap_nodup_of_dinj
- \+ *theorem* erase_nil
- \+ *theorem* erase_cons
- \+ *theorem* erase_cons_head
- \+ *theorem* erase_cons_tail
- \+ *theorem* length_erase_of_mem
- \+ *theorem* erase_of_not_mem
- \+ *theorem* erase_append_left
- \+ *theorem* erase_append_right
- \+ *theorem* erase_sublist
- \+ *theorem* erase_subset
- \+ *theorem* disjoint_left
- \+ *theorem* disjoint_right
- \+ *theorem* disjoint.comm
- \+ *theorem* disjoint_of_subset_left
- \+ *theorem* disjoint_of_subset_right
- \+ *theorem* disjoint_of_disjoint_cons_left
- \+ *theorem* disjoint_of_disjoint_cons_right
- \+ *theorem* disjoint_nil_left
- \+ *theorem* disjoint_nil_right
- \+ *theorem* disjoint_cons_of_not_mem_of_disjoint
- \+ *theorem* disjoint_append_of_disjoint_left
- \+ *theorem* disjoint_of_disjoint_append_left_left
- \+ *theorem* disjoint_of_disjoint_append_left_right
- \+ *theorem* disjoint_of_disjoint_append_right_left
- \+ *theorem* disjoint_of_disjoint_append_right_right
- \+ *theorem* upto_step
- \+ *theorem* dmap_nodup_of_dinj

Modified data/list/sort.lean
- \- *lemma* succ_le_succ_iff
- \- *lemma* lt_succ_iff_le
- \+ *theorem* succ_le_succ_iff
- \+ *theorem* lt_succ_iff_le

Modified data/nat/basic.lean
- \- *lemma* addl_zero_left
- \- *lemma* addl_succ_left
- \- *lemma* zero_has_zero
- \- *lemma* one_succ_zero
- \+ *theorem* addl_zero_left
- \+ *theorem* addl_succ_left
- \+ *theorem* zero_has_zero
- \+ *theorem* one_succ_zero

Modified data/nat/gcd.lean
- \- *lemma* gcd_eq_one_of_coprime
- \+ *theorem* gcd_eq_one_of_coprime

Modified data/nat/sub.lean
- \- *lemma* dist_eq_max_sub_min
- \- *lemma* dist_succ_succ
- \- *lemma* dist_pos_of_ne
- \+ *theorem* dist_succ_succ
- \+ *theorem* dist_pos_of_ne
- \- *theorem* dist_eq_max_sub_min

Modified data/num/lemmas.lean


Modified data/rat.lean
- \- *lemma* linear_order_cases_on_eq
- \- *lemma* linear_order_cases_on_lt
- \- *lemma* linear_order_cases_on_gt
- \- *lemma* mul_nonneg_iff_right_nonneg_of_pos
- \- *lemma* not_antimono
- \+ *theorem* linear_order_cases_on_eq
- \+ *theorem* linear_order_cases_on_lt
- \+ *theorem* linear_order_cases_on_gt
- \+ *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+ *theorem* not_antimono

Modified data/seq/computation.lean
- \- *lemma* map_ret
- \- *lemma* map_think
- \- *lemma* destruct_map
- \- *lemma* map_comp
- \- *lemma* ret_bind
- \- *lemma* think_bind
- \- *lemma* return_def
- \- *lemma* map_ret'
- \- *lemma* map_think'
- \- *lemma* lift_rel_rec.lem
- \+ *theorem* map_ret
- \+ *theorem* map_think
- \+ *theorem* destruct_map
- \+ *theorem* map_comp
- \+ *theorem* ret_bind
- \+ *theorem* think_bind
- \+ *theorem* return_def
- \+ *theorem* map_ret'
- \+ *theorem* map_think'
- \+ *theorem* lift_rel_rec.lem

Modified data/seq/parallel.lean
- \- *lemma* terminates_parallel.aux
- \- *lemma* map_parallel
- \- *lemma* parallel_congr_lem
- \+ *theorem* terminates_parallel.aux
- \+ *theorem* map_parallel
- \+ *theorem* parallel_congr_lem

Modified data/seq/seq.lean
- \- *lemma* mem_cons
- \- *lemma* mem_cons_of_mem
- \- *lemma* eq_or_mem_of_mem_cons
- \- *lemma* mem_cons_iff
- \- *lemma* coinduction
- \- *lemma* coinduction2
- \- *lemma* nil_append
- \- *lemma* cons_append
- \- *lemma* append_nil
- \- *lemma* append_assoc
- \- *lemma* map_nil
- \- *lemma* map_cons
- \- *lemma* map_id
- \- *lemma* map_tail
- \- *lemma* map_comp
- \- *lemma* map_nth
- \- *lemma* join_nil
- \- *lemma* join_cons_nil
- \- *lemma* join_cons_cons
- \- *lemma* join_cons
- \- *lemma* join_append
- \- *lemma* exists_of_mem_map
- \+ *theorem* mem_cons
- \+ *theorem* mem_cons_of_mem
- \+ *theorem* eq_or_mem_of_mem_cons
- \+ *theorem* mem_cons_iff
- \+ *theorem* coinduction
- \+ *theorem* coinduction2
- \+ *theorem* nil_append
- \+ *theorem* cons_append
- \+ *theorem* append_nil
- \+ *theorem* append_assoc
- \+ *theorem* map_nil
- \+ *theorem* map_cons
- \+ *theorem* map_id
- \+ *theorem* map_tail
- \+ *theorem* map_comp
- \+ *theorem* map_nth
- \+ *theorem* join_nil
- \+ *theorem* join_cons_nil
- \+ *theorem* join_cons_cons
- \+ *theorem* join_cons
- \+ *theorem* join_append
- \+ *theorem* exists_of_mem_map

Modified data/seq/wseq.lean
- \- *lemma* nil_append
- \- *lemma* cons_append
- \- *lemma* think_append
- \- *lemma* append_nil
- \- *lemma* append_assoc
- \- *lemma* exists_of_mem_map
- \- *lemma* map_nil
- \- *lemma* map_cons
- \- *lemma* map_think
- \- *lemma* map_comp
- \- *lemma* destruct_map
- \- *lemma* destruct_append
- \- *lemma* destruct_join
- \- *lemma* join_append
- \+ *theorem* nil_append
- \+ *theorem* cons_append
- \+ *theorem* think_append
- \+ *theorem* append_nil
- \+ *theorem* append_assoc
- \+ *theorem* exists_of_mem_map
- \+ *theorem* map_nil
- \+ *theorem* map_cons
- \+ *theorem* map_think
- \+ *theorem* map_comp
- \+ *theorem* destruct_map
- \+ *theorem* destruct_append
- \+ *theorem* destruct_join
- \+ *theorem* join_append

Modified data/set/basic.lean
- \- *lemma* set_of_false
- \+ *theorem* set_of_false

Modified data/set/finite.lean
- \- *lemma* finite_insert
- \- *lemma* finite_singleton
- \- *lemma* finite_union
- \- *lemma* finite_subset
- \- *lemma* finite_image
- \- *lemma* finite_sUnion
- \+ *theorem* finite_insert
- \+ *theorem* finite_singleton
- \+ *theorem* finite_union
- \+ *theorem* finite_subset
- \+ *theorem* finite_image
- \+ *theorem* finite_sUnion

Modified data/stream.lean
- \- *lemma* nth_zero_cons
- \- *lemma* head_cons
- \- *lemma* tail_cons
- \- *lemma* tail_drop
- \- *lemma* nth_drop
- \- *lemma* tail_eq_drop
- \- *lemma* drop_drop
- \- *lemma* nth_succ
- \- *lemma* drop_succ
- \- *lemma* all_def
- \- *lemma* any_def
- \- *lemma* mem_cons
- \- *lemma* mem_cons_of_mem
- \- *lemma* eq_or_mem_of_mem_cons
- \- *lemma* mem_of_nth_eq
- \- *lemma* drop_map
- \- *lemma* nth_map
- \- *lemma* tail_map
- \- *lemma* head_map
- \- *lemma* map_eq
- \- *lemma* map_cons
- \- *lemma* map_id
- \- *lemma* map_map
- \- *lemma* map_tail
- \- *lemma* mem_map
- \- *lemma* exists_of_mem_map
- \- *lemma* drop_zip
- \- *lemma* nth_zip
- \- *lemma* head_zip
- \- *lemma* tail_zip
- \- *lemma* zip_eq
- \- *lemma* mem_const
- \- *lemma* const_eq
- \- *lemma* tail_const
- \- *lemma* map_const
- \- *lemma* nth_const
- \- *lemma* drop_const
- \- *lemma* head_iterate
- \- *lemma* tail_iterate
- \- *lemma* iterate_eq
- \- *lemma* nth_zero_iterate
- \- *lemma* nth_succ_iterate
- \- *lemma* bisim_simple
- \- *lemma* coinduction
- \- *lemma* iterate_id
- \- *lemma* map_iterate
- \- *lemma* corec_def
- \- *lemma* corec_eq
- \- *lemma* corec_id_id_eq_const
- \- *lemma* corec_id_f_eq_iterate
- \- *lemma* corec'_eq
- \- *lemma* unfolds_eq
- \- *lemma* nth_unfolds_head_tail
- \- *lemma* unfolds_head_eq
- \- *lemma* interleave_eq
- \- *lemma* tail_interleave
- \- *lemma* interleave_tail_tail
- \- *lemma* nth_interleave_left
- \- *lemma* nth_interleave_right
- \- *lemma* mem_interleave_left
- \- *lemma* mem_interleave_right
- \- *lemma* odd_eq
- \- *lemma* head_even
- \- *lemma* tail_even
- \- *lemma* even_cons_cons
- \- *lemma* even_tail
- \- *lemma* even_interleave
- \- *lemma* interleave_even_odd
- \- *lemma* nth_even
- \- *lemma* nth_odd
- \- *lemma* mem_of_mem_even
- \- *lemma* mem_of_mem_odd
- \- *lemma* nil_append_stream
- \- *lemma* cons_append_stream
- \- *lemma* append_append_stream
- \- *lemma* map_append_stream
- \- *lemma* drop_append_stream
- \- *lemma* append_stream_head_tail
- \- *lemma* mem_append_stream_right
- \- *lemma* mem_append_stream_left
- \- *lemma* approx_zero
- \- *lemma* approx_succ
- \- *lemma* nth_approx
- \- *lemma* append_approx_drop
- \- *lemma* take_lemma
- \- *lemma* cycle_eq
- \- *lemma* mem_cycle
- \- *lemma* cycle_singleton
- \- *lemma* tails_eq
- \- *lemma* nth_tails
- \- *lemma* tails_eq_iterate
- \- *lemma* inits_core_eq
- \- *lemma* tail_inits
- \- *lemma* inits_tail
- \- *lemma* cons_nth_inits_core
- \- *lemma* nth_inits
- \- *lemma* inits_eq
- \- *lemma* zip_inits_tails
- \- *lemma* identity
- \- *lemma* composition
- \- *lemma* homomorphism
- \- *lemma* interchange
- \- *lemma* map_eq_apply
- \- *lemma* nth_nats
- \- *lemma* nats_eq
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

Modified data/vector.lean
- \- *lemma* map_nil
- \- *lemma* map_cons
- \- *lemma* to_list_mk
- \- *lemma* to_list_nil
- \- *lemma* to_list_length
- \- *lemma* to_list_cons
- \- *lemma* to_list_append
- \- *lemma* to_list_drop
- \- *lemma* to_list_take
- \+ *theorem* map_nil
- \+ *theorem* map_cons
- \+ *theorem* to_list_mk
- \+ *theorem* to_list_nil
- \+ *theorem* to_list_length
- \+ *theorem* to_list_cons
- \+ *theorem* to_list_append
- \+ *theorem* to_list_drop
- \+ *theorem* to_list_take

Modified logic/basic.lean
- \- *lemma* eq_iff_le_and_le
- \- *lemma* prod.mk.inj_iff
- \- *lemma* prod.forall
- \- *lemma* prod.exists
- \- *lemma* set_of_subset_set_of
- \- *lemma* or_of_not_implies
- \- *lemma* or_of_not_implies'
- \- *lemma* not_imp_iff_not_imp
- \- *lemma* or_imp_iff_and_imp
- \- *lemma* forall_eq
- \+ *theorem* eq_iff_le_and_le
- \+ *theorem* prod.mk.inj_iff
- \+ *theorem* prod.forall
- \+ *theorem* prod.exists
- \+ *theorem* set_of_subset_set_of
- \+ *theorem* or_of_not_implies
- \+ *theorem* or_of_not_implies'
- \+ *theorem* not_imp_iff_not_imp
- \+ *theorem* or_imp_iff_and_imp
- \+ *theorem* forall_eq

Modified tactic/converter/binders.lean
- \- *lemma* {u
- \- *lemma* mem_image
- \- *lemma* Inf_image
- \- *lemma* Sup_image
- \+ *theorem* {u
- \+ *theorem* mem_image
- \+ *theorem* Inf_image
- \+ *theorem* Sup_image

Modified tests/examples.lean
- \- *lemma* mem_set_of
- \+ *theorem* mem_set_of

Modified tests/finish2.lean
- \- *lemma* NoMember
- \+ *theorem* NoMember

Modified topology/continuity.lean
- \- *lemma* univ_eq_true_false
- \- *lemma* false_neq_true
- \- *lemma* subtype.val_image
- \- *lemma* continuous_id
- \- *lemma* continuous_compose
- \- *lemma* continuous_iff_towards
- \- *lemma* continuous_iff_induced_le
- \- *lemma* continuous_eq_le_coinduced
- \- *lemma* continuous_generated_from
- \- *lemma* continuous_induced_dom
- \- *lemma* continuous_induced_rng
- \- *lemma* continuous_coinduced_rng
- \- *lemma* continuous_coinduced_dom
- \- *lemma* continuous_inf_dom
- \- *lemma* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_right
- \- *lemma* continuous_Inf_dom
- \- *lemma* continuous_Inf_rng
- \- *lemma* continuous_infi_dom
- \- *lemma* continuous_infi_rng
- \- *lemma* continuous_top
- \- *lemma* continuous_bot
- \- *lemma* continuous_sup_rng
- \- *lemma* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_right
- \- *lemma* open_singleton_true
- \- *lemma* continuous_Prop
- \- *lemma* open_induced
- \- *lemma* nhds_induced_eq_vmap
- \- *lemma* map_nhds_induced_eq
- \- *lemma* continuous_fst
- \- *lemma* continuous_snd
- \- *lemma* continuous_prod_mk
- \- *lemma* open_set_prod
- \- *lemma* prod_eq_generate_from
- \- *lemma* nhds_prod_eq
- \- *lemma* closure_prod_eq
- \- *lemma* continuous_inl
- \- *lemma* continuous_inr
- \- *lemma* continuous_sum_rec
- \- *lemma* continuous_subtype_val
- \- *lemma* continuous_subtype_mk
- \- *lemma* map_nhds_subtype_val_eq
- \- *lemma* continuous_subtype_nhds_cover
- \- *lemma* nhds_pi
- \- *lemma* compact_pi_infinite
- \+ *theorem* univ_eq_true_false
- \+ *theorem* false_neq_true
- \+ *theorem* subtype.val_image
- \+ *theorem* continuous_id
- \+ *theorem* continuous_compose
- \+ *theorem* continuous_iff_towards
- \+ *theorem* continuous_iff_induced_le
- \+ *theorem* continuous_eq_le_coinduced
- \+ *theorem* continuous_generated_from
- \+ *theorem* continuous_induced_dom
- \+ *theorem* continuous_induced_rng
- \+ *theorem* continuous_coinduced_rng
- \+ *theorem* continuous_coinduced_dom
- \+ *theorem* continuous_inf_dom
- \+ *theorem* continuous_inf_rng_left
- \+ *theorem* continuous_inf_rng_right
- \+ *theorem* continuous_Inf_dom
- \+ *theorem* continuous_Inf_rng
- \+ *theorem* continuous_infi_dom
- \+ *theorem* continuous_infi_rng
- \+ *theorem* continuous_top
- \+ *theorem* continuous_bot
- \+ *theorem* continuous_sup_rng
- \+ *theorem* continuous_sup_dom_left
- \+ *theorem* continuous_sup_dom_right
- \+ *theorem* open_singleton_true
- \+ *theorem* continuous_Prop
- \+ *theorem* open_induced
- \+ *theorem* nhds_induced_eq_vmap
- \+ *theorem* map_nhds_induced_eq
- \+ *theorem* continuous_fst
- \+ *theorem* continuous_snd
- \+ *theorem* continuous_prod_mk
- \+ *theorem* open_set_prod
- \+ *theorem* prod_eq_generate_from
- \+ *theorem* nhds_prod_eq
- \+ *theorem* closure_prod_eq
- \+ *theorem* continuous_inl
- \+ *theorem* continuous_inr
- \+ *theorem* continuous_sum_rec
- \+ *theorem* continuous_subtype_val
- \+ *theorem* continuous_subtype_mk
- \+ *theorem* map_nhds_subtype_val_eq
- \+ *theorem* continuous_subtype_nhds_cover
- \+ *theorem* nhds_pi
- \+ *theorem* compact_pi_infinite

Modified topology/topological_space.lean
- \- *lemma* topological_space_eq
- \- *lemma* open_univ
- \- *lemma* open_inter
- \- *lemma* open_sUnion
- \- *lemma* open_Union
- \- *lemma* open_empty
- \- *lemma* closed_empty
- \- *lemma* closed_univ
- \- *lemma* closed_union
- \- *lemma* closed_sInter
- \- *lemma* closed_Inter
- \- *lemma* closed_compl_iff_open
- \- *lemma* open_compl_iff_closed
- \- *lemma* open_diff
- \- *lemma* open_interior
- \- *lemma* interior_subset
- \- *lemma* interior_maximal
- \- *lemma* interior_eq_of_open
- \- *lemma* interior_eq_iff_open
- \- *lemma* subset_interior_iff_subset_of_open
- \- *lemma* interior_mono
- \- *lemma* interior_empty
- \- *lemma* interior_univ
- \- *lemma* interior_interior
- \- *lemma* interior_inter
- \- *lemma* interior_union_closed_of_interior_empty
- \- *lemma* closed_closure
- \- *lemma* subset_closure
- \- *lemma* closure_minimal
- \- *lemma* closure_eq_of_closed
- \- *lemma* closure_eq_iff_closed
- \- *lemma* closure_subset_iff_subset_of_closed
- \- *lemma* closure_mono
- \- *lemma* closure_empty
- \- *lemma* closure_univ
- \- *lemma* closure_closure
- \- *lemma* closure_union
- \- *lemma* interior_subset_closure
- \- *lemma* closure_eq_compl_interior_compl
- \- *lemma* interior_compl_eq
- \- *lemma* closure_compl_eq
- \- *lemma* nhds_sets
- \- *lemma* map_nhds
- \- *lemma* mem_nhds_sets_iff
- \- *lemma* mem_nhds_sets
- \- *lemma* return_le_nhds
- \- *lemma* nhds_neq_bot
- \- *lemma* interior_eq_nhds
- \- *lemma* open_iff_nhds
- \- *lemma* closure_eq_nhds
- \- *lemma* closed_iff_nhds
- \- *lemma* closed_Union_of_locally_finite
- \- *lemma* compact_adherence_nhdset
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \- *lemma* finite_subcover_of_compact
- \- *lemma* eq_of_nhds_neq_bot
- \- *lemma* nhds_generate_from
- \- *lemma* t2_space_top
- \- *lemma* le_of_nhds_le_nhds
- \- *lemma* eq_of_nhds_eq_nhds
- \- *lemma* generate_from_le
- \- *lemma* supr_eq_generate_from
- \- *lemma* sup_eq_generate_from
- \- *lemma* nhds_mono
- \- *lemma* nhds_supr
- \+ *theorem* topological_space_eq
- \+ *theorem* open_univ
- \+ *theorem* open_inter
- \+ *theorem* open_sUnion
- \+ *theorem* open_Union
- \+ *theorem* open_empty
- \+ *theorem* closed_empty
- \+ *theorem* closed_univ
- \+ *theorem* closed_union
- \+ *theorem* closed_sInter
- \+ *theorem* closed_Inter
- \+ *theorem* closed_compl_iff_open
- \+ *theorem* open_compl_iff_closed
- \+ *theorem* open_diff
- \+ *theorem* open_interior
- \+ *theorem* interior_subset
- \+ *theorem* interior_maximal
- \+ *theorem* interior_eq_of_open
- \+ *theorem* interior_eq_iff_open
- \+ *theorem* subset_interior_iff_subset_of_open
- \+ *theorem* interior_mono
- \+ *theorem* interior_empty
- \+ *theorem* interior_univ
- \+ *theorem* interior_interior
- \+ *theorem* interior_inter
- \+ *theorem* interior_union_closed_of_interior_empty
- \+ *theorem* closed_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_minimal
- \+ *theorem* closure_eq_of_closed
- \+ *theorem* closure_eq_iff_closed
- \+ *theorem* closure_subset_iff_subset_of_closed
- \+ *theorem* closure_mono
- \+ *theorem* closure_empty
- \+ *theorem* closure_univ
- \+ *theorem* closure_closure
- \+ *theorem* closure_union
- \+ *theorem* interior_subset_closure
- \+ *theorem* closure_eq_compl_interior_compl
- \+ *theorem* interior_compl_eq
- \+ *theorem* closure_compl_eq
- \+ *theorem* nhds_sets
- \+ *theorem* map_nhds
- \+ *theorem* mem_nhds_sets_iff
- \+ *theorem* mem_nhds_sets
- \+ *theorem* return_le_nhds
- \+ *theorem* nhds_neq_bot
- \+ *theorem* interior_eq_nhds
- \+ *theorem* open_iff_nhds
- \+ *theorem* closure_eq_nhds
- \+ *theorem* closed_iff_nhds
- \+ *theorem* closed_Union_of_locally_finite
- \+ *theorem* compact_adherence_nhdset
- \+ *theorem* compact_iff_ultrafilter_le_nhds
- \+ *theorem* finite_subcover_of_compact
- \+ *theorem* eq_of_nhds_neq_bot
- \+ *theorem* nhds_generate_from
- \+ *theorem* t2_space_top
- \+ *theorem* le_of_nhds_le_nhds
- \+ *theorem* eq_of_nhds_eq_nhds
- \+ *theorem* generate_from_le
- \+ *theorem* supr_eq_generate_from
- \+ *theorem* sup_eq_generate_from
- \+ *theorem* nhds_mono
- \+ *theorem* nhds_supr

Modified topology/uniform_space.lean
- \- *lemma* swap_id_rel
- \- *lemma* monotone_comp_rel
- \- *lemma* prod_mk_mem_comp_rel
- \- *lemma* id_comp_rel
- \- *lemma* uniform_space_eq
- \- *lemma* refl_le_uniformity
- \- *lemma* refl_mem_uniformity
- \- *lemma* symm_le_uniformity
- \- *lemma* comp_le_uniformity
- \- *lemma* comp_mem_uniformity_sets
- \- *lemma* symm_of_uniformity
- \- *lemma* comp_symm_of_uniformity
- \- *lemma* uniformity_le_symm
- \- *lemma* uniformity_eq_symm
- \- *lemma* uniformity_lift_le_swap
- \- *lemma* uniformity_lift_le_comp
- \- *lemma* comp_le_uniformity3
- \- *lemma* mem_nhds_uniformity_iff
- \- *lemma* nhds_eq_uniformity
- \- *lemma* mem_nhds_left
- \- *lemma* mem_nhds_right
- \- *lemma* lift_nhds_left
- \- *lemma* lift_nhds_right
- \- *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \- *lemma* nhds_eq_uniformity_prod
- \- *lemma* nhdset_of_mem_uniformity
- \- *lemma* closure_eq_inter_uniformity
- \- *lemma* uniformity_eq_uniformity_closure
- \- *lemma* uniformity_eq_uniformity_interior
- \- *lemma* interior_mem_uniformity
- \- *lemma* uniform_continuous_of_embedding
- \- *lemma* continuous_of_uniform
- \- *lemma* cauchy_downwards
- \- *lemma* cauchy_nhds
- \- *lemma* cauchy_pure
- \- *lemma* le_nhds_of_cauchy_adhp
- \- *lemma* le_nhds_iff_adhp_of_cauchy
- \- *lemma* cauchy_map
- \- *lemma* cauchy_vmap
- \- *lemma* separated_equiv
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \- *lemma* totally_bounded_iff_filter
- \- *lemma* totally_bounded_iff_ultrafilter
- \- *lemma* compact_of_totally_bounded_complete
- \- *lemma* complete_of_closed
- \- *lemma* compact_of_totally_bounded_closed
- \- *lemma* complete_space_extension
- \- *lemma* uniform_continuous_quotient_mk
- \- *lemma* vmap_quotient_le_uniformity
- \- *lemma* complete_space_separation
- \- *lemma* uniformly_extend_spec
- \- *lemma* uniformly_extend_unique
- \- *lemma* uniformly_extend_of_emb
- \- *lemma* uniform_continuous_uniformly_extend
- \- *lemma* monotone_gen
- \- *lemma* uniform_embedding_pure_cauchy
- \- *lemma* pure_cauchy_dense
- \- *lemma* uniform_continuous_vmap
- \- *lemma* to_topological_space_vmap
- \- *lemma* to_topological_space_mono
- \- *lemma* supr_uniformity
- \- *lemma* to_topological_space_top
- \- *lemma* to_topological_space_bot
- \- *lemma* to_topological_space_supr
- \+ *theorem* swap_id_rel
- \+ *theorem* monotone_comp_rel
- \+ *theorem* prod_mk_mem_comp_rel
- \+ *theorem* id_comp_rel
- \+ *theorem* uniform_space_eq
- \+ *theorem* refl_le_uniformity
- \+ *theorem* refl_mem_uniformity
- \+ *theorem* symm_le_uniformity
- \+ *theorem* comp_le_uniformity
- \+ *theorem* comp_mem_uniformity_sets
- \+ *theorem* symm_of_uniformity
- \+ *theorem* comp_symm_of_uniformity
- \+ *theorem* uniformity_le_symm
- \+ *theorem* uniformity_eq_symm
- \+ *theorem* uniformity_lift_le_swap
- \+ *theorem* uniformity_lift_le_comp
- \+ *theorem* comp_le_uniformity3
- \+ *theorem* mem_nhds_uniformity_iff
- \+ *theorem* nhds_eq_uniformity
- \+ *theorem* mem_nhds_left
- \+ *theorem* mem_nhds_right
- \+ *theorem* lift_nhds_left
- \+ *theorem* lift_nhds_right
- \+ *theorem* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *theorem* nhds_eq_uniformity_prod
- \+ *theorem* nhdset_of_mem_uniformity
- \+ *theorem* closure_eq_inter_uniformity
- \+ *theorem* uniformity_eq_uniformity_closure
- \+ *theorem* uniformity_eq_uniformity_interior
- \+ *theorem* interior_mem_uniformity
- \+ *theorem* uniform_continuous_of_embedding
- \+ *theorem* continuous_of_uniform
- \+ *theorem* cauchy_downwards
- \+ *theorem* cauchy_nhds
- \+ *theorem* cauchy_pure
- \+ *theorem* le_nhds_of_cauchy_adhp
- \+ *theorem* le_nhds_iff_adhp_of_cauchy
- \+ *theorem* cauchy_map
- \+ *theorem* cauchy_vmap
- \+ *theorem* separated_equiv
- \+ *theorem* cauchy_of_totally_bounded_of_ultrafilter
- \+ *theorem* totally_bounded_iff_filter
- \+ *theorem* totally_bounded_iff_ultrafilter
- \+ *theorem* compact_of_totally_bounded_complete
- \+ *theorem* complete_of_closed
- \+ *theorem* compact_of_totally_bounded_closed
- \+ *theorem* complete_space_extension
- \+ *theorem* uniform_continuous_quotient_mk
- \+ *theorem* vmap_quotient_le_uniformity
- \+ *theorem* complete_space_separation
- \+ *theorem* uniformly_extend_spec
- \+ *theorem* uniformly_extend_unique
- \+ *theorem* uniformly_extend_of_emb
- \+ *theorem* uniform_continuous_uniformly_extend
- \+ *theorem* monotone_gen
- \+ *theorem* uniform_embedding_pure_cauchy
- \+ *theorem* pure_cauchy_dense
- \+ *theorem* uniform_continuous_vmap
- \+ *theorem* to_topological_space_vmap
- \+ *theorem* to_topological_space_mono
- \+ *theorem* supr_uniformity
- \+ *theorem* to_topological_space_top
- \+ *theorem* to_topological_space_bot
- \+ *theorem* to_topological_space_supr



## [2017-07-23 18:13:37+01:00](https://github.com/leanprover-community/mathlib/commit/b9f1d64)
refactor(*): use . instead of ^.
#### Estimated changes
Modified algebra/group.lean


Modified algebra/lattice/basic.lean


Modified algebra/lattice/boolean_algebra.lean


Modified algebra/lattice/complete_boolean_algebra.lean


Modified algebra/lattice/complete_lattice.lean


Modified algebra/lattice/filter.lean
- \+/\- *lemma* filter_eq
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* univ_mem_sets
- \+/\- *lemma* inter_mem_sets
- \+/\- *lemma* monotone_mem_sets
- \+/\- *lemma* mem_join_sets
- \+/\- *lemma* mem_principal_sets
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* mem_bot_sets
- \+/\- *lemma* empty_in_sets_eq_bot
- \+/\- *lemma* inhabited_of_mem_sets
- \+/\- *lemma* supr_sets_eq
- \+/\- *lemma* bind_mono
- \+/\- *lemma* mem_return_sets
- \+/\- *lemma* lift_sets_eq
- \+/\- *lemma* mem_lift
- \+/\- *lemma* lift_mono
- \+/\- *lemma* lift_mono'
- \+/\- *lemma* lift_neq_bot_iff
- \+/\- *lemma* mem_lift'
- \+/\- *lemma* mem_lift'_iff
- \+/\- *lemma* lift'_mono
- \+/\- *lemma* lift'_mono'
- \+/\- *lemma* lift'_cong
- \+/\- *lemma* map_lift'_eq
- \+/\- *lemma* principal_le_lift'
- \+/\- *lemma* lift'_neq_bot_iff
- \+/\- *lemma* prod_same_eq

Modified algebra/lattice/fixed_points.lean


Modified algebra/ring.lean


Modified data/list/basic.lean


Modified data/list/comb.lean


Modified data/list/set.lean


Modified data/list/sort.lean


Modified data/rat.lean


Modified data/set/basic.lean


Modified data/set/finite.lean


Modified data/set/lattice.lean


Modified logic/basic.lean


Modified tactic/finish.lean


Modified topology/continuity.lean
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* map_nhds_subtype_val_eq

Modified topology/topological_space.lean
- \+/\- *lemma* topological_space_eq
- \+/\- *lemma* nhds_sets

Modified topology/uniform_space.lean




## [2017-07-23 18:07:49+01:00](https://github.com/leanprover-community/mathlib/commit/9d01cb8)
refactor(algebra/lattice): use *experiment files, move set.lattice to .basic
#### Estimated changes
Modified algebra/lattice/basic.lean
- \+/\- *lemma* le_top
- \+ *lemma* top_le_iff
- \+/\- *lemma* bot_le
- \+ *lemma* le_bot_iff
- \+ *lemma* le_sup_left'
- \+ *lemma* le_sup_right'
- \+/\- *lemma* sup_le
- \+/\- *lemma* sup_le_iff
- \+/\- *lemma* sup_idem
- \+ *lemma* inf_le_left'
- \+ *lemma* inf_le_right'
- \+/\- *lemma* le_inf_iff
- \+/\- *lemma* inf_idem
- \+/\- *lemma* top_sup_eq
- \+/\- *lemma* sup_top_eq
- \+/\- *lemma* bot_sup_eq
- \+/\- *lemma* sup_bot_eq
- \+/\- *lemma* sup_eq_bot_iff
- \+/\- *lemma* top_inf_eq
- \+/\- *lemma* inf_top_eq
- \+/\- *lemma* inf_eq_top_iff
- \+/\- *lemma* bot_inf_eq
- \+/\- *lemma* inf_bot_eq

Deleted algebra/lattice/basic_experiment.lean
- \- *lemma* le_top
- \- *lemma* top_unique
- \- *lemma* eq_top_iff
- \- *lemma* top_le_iff
- \- *lemma* bot_le
- \- *lemma* bot_unique
- \- *lemma* eq_bot_iff
- \- *lemma* le_bot_iff
- \- *lemma* neq_bot_of_le_neq_bot
- \- *lemma* le_sup_left
- \- *lemma* le_sup_left'
- \- *lemma* le_sup_right
- \- *lemma* le_sup_right'
- \- *lemma* le_sup_left_of_le
- \- *lemma* le_sup_right_of_le
- \- *lemma* sup_le
- \- *lemma* sup_le_iff
- \- *lemma* sup_of_le_left
- \- *lemma* sup_of_le_right
- \- *lemma* sup_le_sup
- \- *lemma* le_of_sup_eq
- \- *lemma* sup_idem
- \- *lemma* sup_comm
- \- *lemma* sup_assoc
- \- *lemma* inf_le_left
- \- *lemma* inf_le_left'
- \- *lemma* inf_le_right
- \- *lemma* inf_le_right'
- \- *lemma* le_inf
- \- *lemma* inf_le_left_of_le
- \- *lemma* inf_le_right_of_le
- \- *lemma* le_inf_iff
- \- *lemma* inf_of_le_left
- \- *lemma* inf_of_le_right
- \- *lemma* inf_le_inf
- \- *lemma* le_of_inf_eq
- \- *lemma* inf_idem
- \- *lemma* inf_comm
- \- *lemma* inf_assoc
- \- *lemma* top_sup_eq
- \- *lemma* sup_top_eq
- \- *lemma* bot_sup_eq
- \- *lemma* sup_bot_eq
- \- *lemma* sup_eq_bot_iff
- \- *lemma* top_inf_eq
- \- *lemma* inf_top_eq
- \- *lemma* inf_eq_top_iff
- \- *lemma* bot_inf_eq
- \- *lemma* inf_bot_eq
- \- *lemma* sup_inf_le
- \- *lemma* le_inf_sup
- \- *lemma* inf_sup_self
- \- *lemma* sup_inf_self
- \- *def* imp

Modified algebra/lattice/bounded_lattice.lean


Deleted algebra/lattice/bounded_lattice_experiment.lean
- \- *lemma* monotone_and
- \- *lemma* monotone_or

Modified algebra/lattice/complete_boolean_algebra.lean


Modified algebra/lattice/complete_lattice.lean
- \+ *lemma* le_supr'
- \+ *lemma* infi_le'
- \+ *lemma* infi_le₂'
- \+ *lemma* foo
- \+ *lemma* foo'
- \- *theorem* subset_union_left
- \- *theorem* subset_union_right

Deleted algebra/lattice/complete_lattice_experiment.lean
- \- *lemma* mem_set_of
- \- *lemma* mem_set_of_eq
- \- *lemma* nmem_set_of_eq
- \- *lemma* set_of_false
- \- *lemma* le_Sup
- \- *lemma* Sup_le
- \- *lemma* Inf_le
- \- *lemma* le_Inf
- \- *lemma* le_Sup_of_le
- \- *lemma* Inf_le_of_le
- \- *lemma* Sup_le_Sup
- \- *lemma* Inf_le_Inf
- \- *lemma* le_Sup_iff
- \- *lemma* Inf_le_iff
- \- *lemma* Inf_le_Sup
- \- *lemma* Sup_union
- \- *lemma* Sup_inter_le
- \- *lemma* Inf_union
- \- *lemma* le_Inf_inter
- \- *lemma* Sup_empty
- \- *lemma* Inf_empty
- \- *lemma* Sup_univ
- \- *lemma* Inf_univ
- \- *lemma* Sup_insert
- \- *lemma* Inf_insert
- \- *lemma* Sup_singleton
- \- *lemma* Inf_singleton
- \- *lemma* le_supr
- \- *lemma* le_supr'
- \- *lemma* le_supr_of_le
- \- *lemma* supr_le
- \- *lemma* supr_le_supr
- \- *lemma* supr_le_supr2
- \- *lemma* supr_le_supr_const
- \- *lemma* supr_le_iff
- \- *lemma* supr_congr_Prop
- \- *lemma* infi_le
- \- *lemma* infi_le'
- \- *lemma* infi_le₂'
- \- *lemma* infi_le_of_le
- \- *lemma* le_infi
- \- *lemma* infi_le_infi
- \- *lemma* infi_le_infi2
- \- *lemma* infi_le_infi_const
- \- *lemma* le_infi_iff
- \- *lemma* infi_congr_Prop
- \- *lemma* infi_const
- \- *lemma* supr_const
- \- *lemma* infi_comm
- \- *lemma* supr_comm
- \- *lemma* infi_infi_eq_left
- \- *lemma* infi_infi_eq_right
- \- *lemma* supr_supr_eq_left
- \- *lemma* supr_supr_eq_right
- \- *lemma* foo
- \- *lemma* foo'
- \- *lemma* infi_inf_eq
- \- *lemma* supr_sup_eq
- \- *lemma* infi_false
- \- *lemma* supr_false
- \- *lemma* infi_true
- \- *lemma* supr_true
- \- *lemma* infi_exists
- \- *lemma* supr_exists
- \- *lemma* infi_and
- \- *lemma* supr_and
- \- *lemma* infi_or
- \- *lemma* supr_or
- \- *lemma* Inf_eq_infi
- \- *lemma* Sup_eq_supr
- \- *lemma* Inf_image
- \- *lemma* Sup_image
- \- *lemma* infi_emptyset
- \- *lemma* supr_emptyset
- \- *lemma* infi_univ
- \- *lemma* supr_univ
- \- *lemma* infi_union
- \- *lemma* supr_union
- \- *lemma* infi_insert
- \- *lemma* supr_insert
- \- *lemma* infi_singleton
- \- *lemma* supr_singleton
- \- *lemma* infi_empty
- \- *lemma* supr_empty
- \- *lemma* infi_unit
- \- *lemma* supr_unit
- \- *lemma* infi_subtype
- \- *lemma* supr_subtype
- \- *lemma* infi_sigma
- \- *lemma* supr_sigma
- \- *lemma* infi_prod
- \- *lemma* supr_prod
- \- *lemma* infi_sum
- \- *lemma* supr_sum
- \- *lemma* monotone_Sup_of_monotone
- \- *lemma* monotone_Inf_of_monotone
- \- *lemma* Inf_eq_top
- \- *lemma* infi_eq_top
- \- *lemma* Sup_eq_bot
- \- *lemma* supr_eq_top
- \- *theorem* set_eq_def
- \- *theorem* subset_def
- \- *theorem* union_def
- \- *theorem* inter_def
- \- *theorem* mem_univ_eq
- \- *theorem* subset_univ
- \- *theorem* mem_union_eq
- \- *theorem* union_left_comm
- \- *theorem* mem_inter_eq
- \- *theorem* inter_left_comm
- \- *theorem* insert_def
- \- *theorem* insert_of_has_insert
- \- *theorem* subset_insert
- \- *theorem* mem_insert_iff
- \- *theorem* insert_eq_of_mem
- \- *theorem* singleton_def
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_singleton
- \- *theorem* singleton_eq_singleton_iff
- \- *def* Sup
- \- *def* Inf
- \- *def* supr
- \- *def* infi

Modified data/seq/wseq.lean


Modified data/set/basic.lean
- \+ *lemma* set_of_false
- \- *lemma* ext
- \- *lemma* subset.refl
- \- *lemma* subset.trans
- \- *lemma* subset.antisymm
- \- *lemma* eq_of_subset_of_subset
- \- *lemma* mem_of_subset_of_mem
- \- *lemma* not_mem_empty
- \- *lemma* mem_empty_eq
- \- *lemma* eq_empty_of_forall_not_mem
- \- *lemma* ne_empty_of_mem
- \- *lemma* empty_subset
- \- *lemma* eq_empty_of_subset_empty
- \- *lemma* union_comm
- \- *lemma* union_assoc
- \- *lemma* union_self
- \- *lemma* union_empty
- \- *lemma* empty_union
- \- *lemma* inter_comm
- \- *lemma* inter_assoc
- \- *lemma* inter_self
- \- *lemma* inter_empty
- \- *lemma* empty_inter
- \+ *theorem* ext
- \+ *theorem* set_eq_def
- \+ *theorem* mem_set_of_eq
- \+ *theorem* nmem_set_of_eq
- \+ *theorem* subset_def
- \+ *theorem* subset.refl
- \+ *theorem* subset.trans
- \+ *theorem* subset.antisymm
- \+ *theorem* eq_of_subset_of_subset
- \+ *theorem* mem_of_subset_of_mem
- \+ *theorem* ssubset_def
- \+ *theorem* not_mem_empty
- \+ *theorem* empty_def
- \+ *theorem* mem_empty_eq
- \+ *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* ne_empty_of_mem
- \+ *theorem* empty_subset
- \+ *theorem* eq_empty_of_subset_empty
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* bounded_forall_empty_iff
- \+ *theorem* univ_def
- \+ *theorem* mem_univ
- \+ *theorem* mem_univ_iff
- \+ *theorem* mem_univ_eq
- \+ *theorem* empty_ne_univ
- \+ *theorem* subset_univ
- \+ *theorem* eq_univ_of_univ_subset
- \+ *theorem* eq_univ_of_forall
- \+ *theorem* union_def
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union.elim
- \+ *theorem* mem_union_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* union_self
- \+ *theorem* union_empty
- \+ *theorem* empty_union
- \+ *theorem* union_comm
- \+ *theorem* union_assoc
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_eq_self_of_subset_left
- \+ *theorem* union_eq_self_of_subset_right
- \+ *theorem* subset_union_left
- \+ *theorem* subset_union_right
- \+ *theorem* union_subset
- \+ *theorem* union_subset_iff
- \+ *theorem* union_subset_union
- \+ *theorem* inter_def
- \+ *theorem* mem_inter_iff
- \+ *theorem* mem_inter_eq
- \+ *theorem* mem_inter
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* inter_self
- \+ *theorem* inter_empty
- \+ *theorem* empty_inter
- \+ *theorem* inter_comm
- \+ *theorem* inter_assoc
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* inter_univ
- \+ *theorem* univ_inter
- \+ *theorem* inter_subset_inter_right
- \+ *theorem* inter_subset_inter_left
- \+ *theorem* inter_subset_inter
- \+ *theorem* inter_eq_self_of_subset_left
- \+ *theorem* inter_eq_self_of_subset_right
- \+ *theorem* nonempty_of_inter_nonempty_right
- \+ *theorem* nonempty_of_inter_nonempty_left
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* insert_def
- \+ *theorem* insert_of_has_insert
- \+ *theorem* subset_insert
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* ssubset_insert
- \+ *theorem* insert_comm
- \+ *theorem* insert_ne_empty
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* forall_insert_of_forall
- \+ *theorem* bounded_forall_insert_iff
- \+ *theorem* singleton_def
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* singleton_eq_singleton_iff
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* insert_eq
- \+ *theorem* union_insert_eq
- \+ *theorem* pair_eq_singleton
- \+ *theorem* singleton_ne_empty
- \+ *theorem* singleton_subset_iff
- \+ *theorem* mem_sep
- \+ *theorem* mem_sep_eq
- \+ *theorem* mem_sep_iff
- \+ *theorem* eq_sep_of_subset
- \+ *theorem* sep_subset
- \+ *theorem* forall_not_of_sep_empty
- \+ *theorem* mem_compl
- \+ *theorem* not_mem_of_mem_compl
- \+ *theorem* mem_compl_eq
- \+ *theorem* mem_compl_iff
- \+ *theorem* inter_compl_self
- \+ *theorem* compl_inter_self
- \+ *theorem* compl_empty
- \+ *theorem* compl_union
- \+ *theorem* compl_compl
- \+ *theorem* compl_inter
- \+ *theorem* compl_univ
- \+ *theorem* union_eq_compl_compl_inter_compl
- \+ *theorem* inter_eq_compl_compl_union_compl
- \+ *theorem* union_compl_self
- \+ *theorem* compl_union_self
- \+ *theorem* compl_comp_compl
- \+ *theorem* diff_eq
- \+ *theorem* mem_diff
- \+ *theorem* mem_of_mem_diff
- \+ *theorem* not_mem_of_mem_diff
- \+ *theorem* mem_diff_iff
- \+ *theorem* mem_diff_eq
- \+ *theorem* union_diff_cancel
- \+ *theorem* diff_subset
- \+ *theorem* compl_eq_univ_diff
- \+ *theorem* mem_powerset
- \+ *theorem* subset_of_mem_powerset
- \+ *theorem* mem_powerset_iff
- \+ *theorem* mem_image_eq
- \+ *theorem* mem_image
- \+ *theorem* mem_image_of_mem
- \+ *theorem* mono_image
- \+ *theorem* image_subset_iff_subset_vimage
- \+ *theorem* image_eq_image_of_eq_on
- \+ *theorem* image_comp
- \+ *theorem* image_subset
- \+ *theorem* image_union
- \+ *theorem* image_empty
- \+ *theorem* fix_set_compl
- \+ *theorem* mem_image_compl
- \+ *theorem* image_id
- \+ *theorem* compl_compl_image
- \+ *theorem* bounded_forall_image_of_bounded_forall
- \+ *theorem* bounded_forall_image_iff
- \+ *theorem* image_insert_eq
- \+ *theorem* vimage_empty
- \+ *theorem* mem_vimage_eq
- \+ *theorem* vimage_mono
- \+ *theorem* vimage_image_eq
- \+ *theorem* vimage_univ
- \+ *theorem* vimage_inter
- \+ *theorem* vimage_union
- \+ *theorem* vimage_compl
- \+ *theorem* vimage_id
- \+ *theorem* vimage_comp
- \+ *theorem* eq_vimage_subtype_val_iff
- \+ *def* strict_subset
- \+ *def* eq_on
- \+ *def* mem_image_elim
- \+ *def* mem_image_elim_on
- \+ *def* vimage
- \+ *def* pairwise_on

Modified data/set/lattice.lean
- \- *lemma* mem_set_of
- \- *lemma* mem_set_of_eq
- \- *lemma* nmem_set_of_eq
- \- *lemma* set_of_false
- \- *lemma* bounded_forall_empty_iff
- \- *lemma* union_subset_iff
- \- *lemma* ssubset_insert
- \- *lemma* bounded_forall_insert_iff
- \- *lemma* union_insert_eq
- \- *lemma* singleton_subset_iff
- \- *lemma* image_comp
- \- *lemma* image_subset
- \- *lemma* bounded_forall_image_of_bounded_forall
- \- *lemma* bounded_forall_image_iff
- \- *lemma* image_insert_eq
- \- *lemma* union_sdiff_same
- \- *lemma* union_same_compl
- \- *lemma* sdiff_singleton_eq_same
- \- *lemma* insert_sdiff_singleton
- \- *lemma* vimage_empty
- \- *lemma* mem_vimage_eq
- \- *lemma* vimage_mono
- \- *lemma* monotone_vimage
- \- *lemma* vimage_image_eq
- \- *lemma* vimage_univ
- \- *lemma* vimage_inter
- \- *lemma* vimage_union
- \- *lemma* vimage_compl
- \- *lemma* vimage_Union
- \- *lemma* vimage_sUnion
- \- *lemma* vimage_id
- \- *lemma* vimage_comp
- \- *lemma* eq_vimage_subtype_val_iff
- \- *lemma* disjoint_symm
- \- *lemma* disjoint_bot_left
- \- *lemma* disjoint_bot_right
- \+ *theorem* union_sdiff_same
- \+ *theorem* union_same_compl
- \+ *theorem* sdiff_singleton_eq_same
- \+ *theorem* insert_sdiff_singleton
- \+ *theorem* monotone_vimage
- \+ *theorem* vimage_Union
- \+ *theorem* vimage_sUnion
- \+ *theorem* disjoint_symm
- \+ *theorem* disjoint_bot_left
- \+ *theorem* disjoint_bot_right
- \- *theorem* set_eq_def
- \- *theorem* subset_def
- \- *theorem* union_def
- \- *theorem* inter_def
- \- *theorem* union_subset
- \- *theorem* inter_subset_left
- \- *theorem* inter_subset_right
- \- *theorem* subset_inter
- \- *theorem* ssubset_def
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* subset_empty_iff
- \- *theorem* mem_univ
- \- *theorem* mem_univ_iff
- \- *theorem* mem_univ_eq
- \- *theorem* empty_ne_univ
- \- *theorem* univ_def
- \- *theorem* subset_univ
- \- *theorem* eq_univ_of_univ_subset
- \- *theorem* eq_univ_of_forall
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* mem_unionl
- \- *theorem* mem_unionr
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* mem_union.elim
- \- *theorem* mem_union_iff
- \- *theorem* mem_union_eq
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* union_eq_self_of_subset_left
- \- *theorem* union_eq_self_of_subset_right
- \- *theorem* union_subset_union
- \- *theorem* mem_inter_iff
- \- *theorem* mem_inter_eq
- \- *theorem* mem_inter
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* nonempty_of_inter_nonempty_right
- \- *theorem* nonempty_of_inter_nonempty_left
- \- *theorem* inter_left_comm
- \- *theorem* inter_right_comm
- \- *theorem* inter_univ
- \- *theorem* univ_inter
- \- *theorem* inter_subset_inter_right
- \- *theorem* inter_subset_inter
- \- *theorem* inter_subset_inter_left
- \- *theorem* inter_eq_self_of_subset_left
- \- *theorem* inter_eq_self_of_subset_right
- \- *theorem* inter_distrib_left
- \- *theorem* inter_distrib_right
- \- *theorem* union_distrib_left
- \- *theorem* union_distrib_right
- \- *theorem* insert_def
- \- *theorem* insert_of_has_insert
- \- *theorem* subset_insert
- \- *theorem* mem_insert
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* mem_of_mem_insert_of_ne
- \- *theorem* mem_insert_iff
- \- *theorem* insert_eq_of_mem
- \- *theorem* insert_comm
- \- *theorem* insert_ne_empty
- \- *theorem* forall_of_forall_insert
- \- *theorem* forall_insert_of_forall
- \- *theorem* singleton_def
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_singleton
- \- *theorem* eq_of_mem_singleton
- \- *theorem* singleton_eq_singleton_iff
- \- *theorem* mem_singleton_of_eq
- \- *theorem* insert_eq
- \- *theorem* pair_eq_singleton
- \- *theorem* singleton_ne_empty
- \- *theorem* mem_sep
- \- *theorem* mem_sep_eq
- \- *theorem* mem_sep_iff
- \- *theorem* eq_sep_of_subset
- \- *theorem* sep_subset
- \- *theorem* forall_not_of_sep_empty
- \- *theorem* mem_compl
- \- *theorem* not_mem_of_mem_compl
- \- *theorem* mem_compl_eq
- \- *theorem* mem_compl_iff
- \- *theorem* inter_compl_self
- \- *theorem* compl_inter_self
- \- *theorem* compl_empty
- \- *theorem* compl_union
- \- *theorem* compl_compl
- \- *theorem* compl_inter
- \- *theorem* compl_univ
- \- *theorem* union_eq_compl_compl_inter_compl
- \- *theorem* inter_eq_compl_compl_union_compl
- \- *theorem* union_compl_self
- \- *theorem* compl_union_self
- \- *theorem* compl_comp_compl
- \- *theorem* diff_eq
- \- *theorem* mem_diff
- \- *theorem* mem_of_mem_diff
- \- *theorem* not_mem_of_mem_diff
- \- *theorem* mem_diff_iff
- \- *theorem* mem_diff_eq
- \- *theorem* union_diff_cancel
- \- *theorem* diff_subset
- \- *theorem* compl_eq_univ_diff
- \- *theorem* mem_powerset
- \- *theorem* subset_of_mem_powerset
- \- *theorem* mem_powerset_iff
- \- *theorem* mem_image_eq
- \- *theorem* mem_image
- \- *theorem* mem_image_of_mem
- \- *theorem* mono_image
- \- *theorem* image_subset_iff_subset_vimage
- \- *theorem* image_eq_image_of_eq_on
- \- *theorem* image_union
- \- *theorem* image_empty
- \- *theorem* fix_set_compl
- \- *theorem* mem_image_compl
- \- *theorem* image_id
- \- *theorem* compl_compl_image
- \- *def* strict_subset
- \- *def* eq_on
- \- *def* mem_image_elim
- \- *def* mem_image_elim_on
- \- *def* vimage
- \- *def* pairwise_on

Deleted tests/finish_set_basic.lean
- \- *lemma* mem_set_of
- \- *lemma* bounded_forall_empty_iff
- \- *lemma* bounded_forall_insert_iff
- \- *lemma* image_comp
- \- *lemma* image_subset
- \- *lemma* bounded_forall_image_of_bounded_forall
- \- *lemma* bounded_forall_image_iff
- \- *lemma* image_insert_eq
- \- *theorem* subset_def
- \- *theorem* union_def
- \- *theorem* inter_def
- \- *theorem* union_subset
- \- *theorem* inter_subset_left
- \- *theorem* inter_subset_right
- \- *theorem* subset_inter
- \- *theorem* set_eq_def
- \- *theorem* empty_def
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* subset_empty_iff
- \- *theorem* mem_univ
- \- *theorem* mem_univ_iff
- \- *theorem* mem_univ_eq
- \- *theorem* empty_ne_univ
- \- *theorem* univ_def
- \- *theorem* subset_univ
- \- *theorem* eq_univ_of_univ_subset
- \- *theorem* eq_univ_of_forall
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* mem_unionl
- \- *theorem* mem_unionr
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* mem_union.elim
- \- *theorem* mem_union_iff
- \- *theorem* mem_union_eq
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* union_eq_self_of_subset_left
- \- *theorem* union_eq_self_of_subset_right
- \- *theorem* mem_inter_iff
- \- *theorem* mem_inter_eq
- \- *theorem* mem_inter
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* nonempty_of_inter_nonempty_right
- \- *theorem* nonempty_of_inter_nonempty_left
- \- *theorem* inter_left_comm
- \- *theorem* inter_left_comm'
- \- *theorem* inter_right_comm
- \- *theorem* inter_univ
- \- *theorem* univ_inter
- \- *theorem* inter_subset_inter_right
- \- *theorem* inter_subset_inter_left
- \- *theorem* inter_eq_self_of_subset_left
- \- *theorem* inter_eq_self_of_subset_right
- \- *theorem* inter_distrib_left
- \- *theorem* inter_distrib_right
- \- *theorem* union_distrib_left
- \- *theorem* union_distrib_right
- \- *theorem* insert_def
- \- *theorem* subset_insert
- \- *theorem* mem_insert
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* mem_of_mem_insert_of_ne
- \- *theorem* mem_insert_iff
- \- *theorem* insert_eq_of_mem
- \- *theorem* insert_comm
- \- *theorem* insert_ne_empty
- \- *theorem* forall_of_forall_insert
- \- *theorem* forall_insert_of_forall
- \- *theorem* singleton_def
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_singleton
- \- *theorem* eq_of_mem_singleton
- \- *theorem* mem_singleton_of_eq
- \- *theorem* insert_eq
- \- *theorem* insert_of_has_insert
- \- *theorem* pair_eq_singleton
- \- *theorem* singleton_ne_empty
- \- *theorem* mem_sep
- \- *theorem* mem_sep_eq
- \- *theorem* mem_sep_iff
- \- *theorem* eq_sep_of_subset
- \- *theorem* sep_subset
- \- *theorem* forall_not_of_sep_empty
- \- *theorem* mem_compl
- \- *theorem* not_mem_of_mem_compl
- \- *theorem* mem_compl_eq
- \- *theorem* mem_compl_iff
- \- *theorem* inter_compl_self
- \- *theorem* compl_inter_self
- \- *theorem* compl_empty
- \- *theorem* compl_union
- \- *theorem* compl_compl
- \- *theorem* compl_inter
- \- *theorem* compl_univ
- \- *theorem* union_eq_compl_compl_inter_compl
- \- *theorem* inter_eq_compl_compl_union_compl
- \- *theorem* union_compl_self
- \- *theorem* compl_union_self
- \- *theorem* compl_comp_compl
- \- *theorem* diff_eq
- \- *theorem* mem_diff
- \- *theorem* mem_of_mem_diff
- \- *theorem* not_mem_of_mem_diff
- \- *theorem* mem_diff_iff
- \- *theorem* mem_diff_eq
- \- *theorem* union_diff_cancel
- \- *theorem* diff_subset
- \- *theorem* compl_eq_univ_diff
- \- *theorem* mem_powerset
- \- *theorem* subset_of_mem_powerset
- \- *theorem* mem_powerset_iff
- \- *theorem* mem_image_eq
- \- *theorem* mem_image
- \- *theorem* mem_image_of_mem
- \- *theorem* image_eq_image_of_eq_on
- \- *theorem* image_union
- \- *theorem* image_empty
- \- *theorem* fix_set_compl
- \- *theorem* mem_image_compl
- \- *theorem* image_id
- \- *theorem* compl_compl_image
- \- *def* strict_subset
- \- *def* eq_on
- \- *def* mem_image_elim
- \- *def* mem_image_elim_on

Modified theories/set_theory.lean


Modified topology/continuity.lean


Modified topology/topological_space.lean




## [2017-07-23 15:39:35+01:00](https://github.com/leanprover-community/mathlib/commit/32beb92)
refactor(*): tools -> tactic, remove experimental stuff
#### Estimated changes
Modified algebra/group_power.lean


Modified algebra/lattice/basic_experiment.lean


Modified data/int/basic.lean


Modified data/set/lattice.lean


Renamed tools/converter/binders.lean to tactic/converter/binders.lean


Renamed tools/converter/interactive.lean to tactic/converter/interactive.lean


Renamed tools/converter/old_conv.lean to tactic/converter/old_conv.lean


Renamed tools/auto/finish.lean to tactic/finish.lean


Modified tests/finish1.lean


Modified tests/finish2.lean


Modified tests/finish3.lean


Modified tests/finish_set_basic.lean


Deleted tools/auto/mk_inhabitant.lean


Deleted tools/parser/modal.lean
- \- *def* varname
- \- *def* size
- \- *def* num_atoms
- \- *def* atom
- \- *def* unary_op
- \- *def* binary_op
- \- *def* strong_form_aux
- \- *def* strong_form
- \- *def* form_aux
- \- *def* form
- \- *def* form_of_string

Deleted tools/parser/parser.lean
- \- *lemma* {u
- \- *lemma* {u}
- \- *def* parser
- \- *def* parser_fmap
- \- *def* parser_pure
- \- *def* parser_bind
- \- *def* list.deterministic_or
- \- *def* parser_bignum
- \- *def* parse
- \- *def* item
- \- *def* sat
- \- *def* take_char
- \- *def* take_string_aux
- \- *def* take_string
- \- *def* many_aux
- \- *def* many
- \- *def* many1
- \- *def* sepby1
- \- *def* sepby
- \- *def* chainl1_rest
- \- *def* chainl1
- \- *def* chainl
- \- *def* chainr1_rest
- \- *def* chainr1
- \- *def* chainr
- \- *def* space
- \- *def* token
- \- *def* symb
- \- *def* apply

Deleted tools/tactic/tactic.lean




## [2017-07-23 15:31:56+01:00](https://github.com/leanprover-community/mathlib/commit/bb8b8f8)
refactor(tests): consolidate tests
#### Estimated changes
Renamed tools/tactic/examples.lean to tests/examples.lean


Renamed tools/auto/experiments/test1.lean to tests/finish1.lean


Renamed tools/auto/experiments/test2.lean to tests/finish2.lean


Renamed tools/auto/experiments/test3.lean to tests/finish3.lean


Renamed tools/auto/experiments/set_basic.lean to tests/finish_set_basic.lean


Modified tools/parser/modal.lean




## [2017-07-23 15:24:21+01:00](https://github.com/leanprover-community/mathlib/commit/ae65643)
refactor(*): use absolute paths
#### Estimated changes
Modified algebra/group_power.lean


Modified algebra/lattice/basic.lean


Modified algebra/lattice/basic_experiment.lean


Modified algebra/lattice/boolean_algebra.lean


Modified algebra/lattice/bounded_lattice.lean


Modified algebra/lattice/bounded_lattice_experiment.lean


Modified algebra/lattice/complete_boolean_algebra.lean


Modified algebra/lattice/complete_lattice.lean


Modified algebra/lattice/complete_lattice_experiment.lean


Modified algebra/lattice/default.lean


Modified algebra/lattice/filter.lean


Modified algebra/lattice/fixed_points.lean


Modified data/int/basic.lean


Modified data/int/order.lean


Modified data/list/default.lean


Modified data/list/perm.lean


Modified data/list/set.lean


Modified data/list/sort.lean


Modified data/nat/bquant.lean


Modified data/num/bitwise.lean


Modified data/num/lemmas.lean


Modified data/pfun.lean


Modified data/set/default.lean


Modified data/set/finite.lean


Modified tools/parser/modal.lean


Modified topology/continuity.lean


Modified topology/uniform_space.lean




## [2017-07-23 15:16:51+01:00](https://github.com/leanprover-community/mathlib/commit/deb1681)
refactor(*): import content from lean/library/data and library_dev
#### Estimated changes
Created .gitignore


Created algebra/group.lean
- \+ *theorem* add_comm_four
- \+ *theorem* add_comm_middle
- \+ *theorem* bit0_add_bit0
- \+ *theorem* bit0_add_bit0_helper
- \+ *theorem* bit1_add_bit0
- \+ *theorem* bit1_add_bit0_helper
- \+ *theorem* bit0_add_bit1
- \+ *theorem* bit0_add_bit1_helper
- \+ *theorem* bit1_add_bit1
- \+ *theorem* bit1_add_bit1_helper
- \+ *theorem* bin_add_zero
- \+ *theorem* bin_zero_add
- \+ *theorem* one_add_bit0
- \+ *theorem* bit0_add_one
- \+ *theorem* bit1_add_one
- \+ *theorem* bit1_add_one_helper
- \+ *theorem* one_add_bit1
- \+ *theorem* one_add_bit1_helper
- \+ *theorem* add1_bit0
- \+ *theorem* add1_bit1
- \+ *theorem* add1_bit1_helper
- \+ *theorem* add1_one
- \+ *theorem* add1_zero
- \+ *theorem* one_add_one
- \+ *theorem* subst_into_sum
- \+ *theorem* neg_zero_helper
- \+ *def* add1

Created algebra/group_power.lean
- \+ *theorem* pow_zero
- \+ *theorem* pow_succ
- \+ *theorem* pow_one
- \+ *theorem* pow_succ'
- \+ *theorem* one_pow
- \+ *theorem* pow_add
- \+ *theorem* pow_mul
- \+ *theorem* pow_comm
- \+ *theorem* mul_pow
- \+ *theorem* inv_pow
- \+ *theorem* pow_sub
- \+ *theorem* pow_inv_comm
- \+ *theorem* gpow_add
- \+ *theorem* gpow_comm
- \+ *theorem* pow_pos
- \+ *theorem* pow_ge_one_of_ge_one
- \+ *def* pow_nat
- \+ *def* pow_int
- \+ *def* monoid.pow
- \+ *def* gpow

Created algebra/lattice/README.md


Created algebra/lattice/basic.lean
- \+ *lemma* le_top
- \+ *lemma* top_unique
- \+ *lemma* eq_top_iff
- \+ *lemma* bot_le
- \+ *lemma* bot_unique
- \+ *lemma* eq_bot_iff
- \+ *lemma* neq_bot_of_le_neq_bot
- \+ *lemma* le_sup_left
- \+ *lemma* le_sup_right
- \+ *lemma* sup_le
- \+ *lemma* le_sup_left_of_le
- \+ *lemma* le_sup_right_of_le
- \+ *lemma* sup_le_iff
- \+ *lemma* sup_of_le_left
- \+ *lemma* sup_of_le_right
- \+ *lemma* sup_le_sup
- \+ *lemma* le_of_sup_eq
- \+ *lemma* sup_idem
- \+ *lemma* sup_comm
- \+ *lemma* sup_assoc
- \+ *lemma* inf_le_left
- \+ *lemma* inf_le_right
- \+ *lemma* le_inf
- \+ *lemma* inf_le_left_of_le
- \+ *lemma* inf_le_right_of_le
- \+ *lemma* le_inf_iff
- \+ *lemma* inf_of_le_left
- \+ *lemma* inf_of_le_right
- \+ *lemma* inf_le_inf
- \+ *lemma* le_of_inf_eq
- \+ *lemma* inf_idem
- \+ *lemma* inf_comm
- \+ *lemma* inf_assoc
- \+ *lemma* top_sup_eq
- \+ *lemma* sup_top_eq
- \+ *lemma* bot_sup_eq
- \+ *lemma* sup_bot_eq
- \+ *lemma* sup_eq_bot_iff
- \+ *lemma* top_inf_eq
- \+ *lemma* inf_top_eq
- \+ *lemma* inf_eq_top_iff
- \+ *lemma* bot_inf_eq
- \+ *lemma* inf_bot_eq
- \+ *lemma* sup_inf_le
- \+ *lemma* le_inf_sup
- \+ *lemma* inf_sup_self
- \+ *lemma* sup_inf_self

Created algebra/lattice/basic_experiment.lean
- \+ *lemma* le_top
- \+ *lemma* top_unique
- \+ *lemma* eq_top_iff
- \+ *lemma* top_le_iff
- \+ *lemma* bot_le
- \+ *lemma* bot_unique
- \+ *lemma* eq_bot_iff
- \+ *lemma* le_bot_iff
- \+ *lemma* neq_bot_of_le_neq_bot
- \+ *lemma* le_sup_left
- \+ *lemma* le_sup_left'
- \+ *lemma* le_sup_right
- \+ *lemma* le_sup_right'
- \+ *lemma* le_sup_left_of_le
- \+ *lemma* le_sup_right_of_le
- \+ *lemma* sup_le
- \+ *lemma* sup_le_iff
- \+ *lemma* sup_of_le_left
- \+ *lemma* sup_of_le_right
- \+ *lemma* sup_le_sup
- \+ *lemma* le_of_sup_eq
- \+ *lemma* sup_idem
- \+ *lemma* sup_comm
- \+ *lemma* sup_assoc
- \+ *lemma* inf_le_left
- \+ *lemma* inf_le_left'
- \+ *lemma* inf_le_right
- \+ *lemma* inf_le_right'
- \+ *lemma* le_inf
- \+ *lemma* inf_le_left_of_le
- \+ *lemma* inf_le_right_of_le
- \+ *lemma* le_inf_iff
- \+ *lemma* inf_of_le_left
- \+ *lemma* inf_of_le_right
- \+ *lemma* inf_le_inf
- \+ *lemma* le_of_inf_eq
- \+ *lemma* inf_idem
- \+ *lemma* inf_comm
- \+ *lemma* inf_assoc
- \+ *lemma* top_sup_eq
- \+ *lemma* sup_top_eq
- \+ *lemma* bot_sup_eq
- \+ *lemma* sup_bot_eq
- \+ *lemma* sup_eq_bot_iff
- \+ *lemma* top_inf_eq
- \+ *lemma* inf_top_eq
- \+ *lemma* inf_eq_top_iff
- \+ *lemma* bot_inf_eq
- \+ *lemma* inf_bot_eq
- \+ *lemma* sup_inf_le
- \+ *lemma* le_inf_sup
- \+ *lemma* inf_sup_self
- \+ *lemma* sup_inf_self
- \+ *def* imp

Created algebra/lattice/boolean_algebra.lean
- \+ *lemma* le_sup_inf
- \+ *lemma* sup_inf_left
- \+ *lemma* sup_inf_right
- \+ *lemma* inf_sup_left
- \+ *lemma* inf_sup_right
- \+ *lemma* inf_neg_eq_bot
- \+ *lemma* neg_inf_eq_bot
- \+ *lemma* sup_neg_eq_top
- \+ *lemma* neg_sup_eq_top
- \+ *lemma* sub_eq
- \+ *lemma* neg_unique
- \+ *lemma* neg_top
- \+ *lemma* neg_bot
- \+ *lemma* neg_neg
- \+ *lemma* neg_eq_neg_of_eq
- \+ *lemma* neg_eq_neg_iff
- \+ *lemma* neg_inf
- \+ *lemma* neg_sup
- \+ *lemma* neg_le_neg
- \+ *lemma* neg_le_neg_iff_le
- \+ *lemma* le_neg_of_le_neg
- \+ *lemma* neg_le_of_neg_le
- \+ *lemma* neg_le_iff_neg_le
- \+ *lemma* sup_sub_same
- \+ *lemma* sub_eq_left

Created algebra/lattice/bounded_lattice.lean
- \+ *lemma* monotone_and
- \+ *lemma* monotone_or

Created algebra/lattice/bounded_lattice_experiment.lean
- \+ *lemma* monotone_and
- \+ *lemma* monotone_or

Created algebra/lattice/complete_boolean_algebra.lean
- \+ *lemma* sup_Inf_eq
- \+ *lemma* inf_Sup_eq
- \+ *lemma* neg_infi
- \+ *lemma* neg_supr
- \+ *lemma* neg_Inf
- \+ *lemma* neg_Sup

Created algebra/lattice/complete_lattice.lean
- \+ *lemma* le_Sup
- \+ *lemma* Sup_le
- \+ *lemma* Inf_le
- \+ *lemma* le_Inf
- \+ *lemma* le_Sup_of_le
- \+ *lemma* Inf_le_of_le
- \+ *lemma* Sup_le_Sup
- \+ *lemma* Inf_le_Inf
- \+ *lemma* le_Sup_iff
- \+ *lemma* Inf_le_iff
- \+ *lemma* Inf_le_Sup
- \+ *lemma* Sup_union
- \+ *lemma* Sup_inter_le
- \+ *lemma* Inf_union
- \+ *lemma* le_Inf_inter
- \+ *lemma* Sup_empty
- \+ *lemma* Inf_empty
- \+ *lemma* Sup_univ
- \+ *lemma* Inf_univ
- \+ *lemma* Sup_insert
- \+ *lemma* Inf_insert
- \+ *lemma* Sup_singleton
- \+ *lemma* Inf_singleton
- \+ *lemma* le_supr
- \+ *lemma* le_supr_of_le
- \+ *lemma* supr_le
- \+ *lemma* supr_le_supr
- \+ *lemma* supr_le_supr2
- \+ *lemma* supr_le_supr_const
- \+ *lemma* supr_le_iff
- \+ *lemma* supr_congr_Prop
- \+ *lemma* infi_le
- \+ *lemma* infi_le_of_le
- \+ *lemma* le_infi
- \+ *lemma* infi_le_infi
- \+ *lemma* infi_le_infi2
- \+ *lemma* infi_le_infi_const
- \+ *lemma* le_infi_iff
- \+ *lemma* infi_congr_Prop
- \+ *lemma* infi_const
- \+ *lemma* supr_const
- \+ *lemma* infi_comm
- \+ *lemma* supr_comm
- \+ *lemma* infi_infi_eq_left
- \+ *lemma* infi_infi_eq_right
- \+ *lemma* supr_supr_eq_left
- \+ *lemma* supr_supr_eq_right
- \+ *lemma* infi_inf_eq
- \+ *lemma* supr_sup_eq
- \+ *lemma* infi_false
- \+ *lemma* supr_false
- \+ *lemma* infi_true
- \+ *lemma* supr_true
- \+ *lemma* infi_exists
- \+ *lemma* supr_exists
- \+ *lemma* infi_and
- \+ *lemma* supr_and
- \+ *lemma* infi_or
- \+ *lemma* supr_or
- \+ *lemma* Inf_eq_infi
- \+ *lemma* Sup_eq_supr
- \+ *lemma* Inf_image
- \+ *lemma* Sup_image
- \+ *lemma* infi_emptyset
- \+ *lemma* supr_emptyset
- \+ *lemma* infi_univ
- \+ *lemma* supr_univ
- \+ *lemma* infi_union
- \+ *lemma* supr_union
- \+ *lemma* infi_insert
- \+ *lemma* supr_insert
- \+ *lemma* infi_singleton
- \+ *lemma* supr_singleton
- \+ *lemma* infi_empty
- \+ *lemma* supr_empty
- \+ *lemma* infi_unit
- \+ *lemma* supr_unit
- \+ *lemma* infi_subtype
- \+ *lemma* supr_subtype
- \+ *lemma* infi_sigma
- \+ *lemma* supr_sigma
- \+ *lemma* infi_prod
- \+ *lemma* supr_prod
- \+ *lemma* infi_sum
- \+ *lemma* supr_sum
- \+ *lemma* monotone_Sup_of_monotone
- \+ *lemma* monotone_Inf_of_monotone
- \+ *lemma* Inf_eq_top
- \+ *lemma* infi_eq_top
- \+ *lemma* Sup_eq_bot
- \+ *lemma* supr_eq_top
- \+ *theorem* subset_union_left
- \+ *theorem* subset_union_right
- \+ *theorem* insert_of_has_insert
- \+ *def* Sup
- \+ *def* Inf
- \+ *def* supr
- \+ *def* infi

Created algebra/lattice/complete_lattice_experiment.lean
- \+ *lemma* mem_set_of
- \+ *lemma* mem_set_of_eq
- \+ *lemma* nmem_set_of_eq
- \+ *lemma* set_of_false
- \+ *lemma* le_Sup
- \+ *lemma* Sup_le
- \+ *lemma* Inf_le
- \+ *lemma* le_Inf
- \+ *lemma* le_Sup_of_le
- \+ *lemma* Inf_le_of_le
- \+ *lemma* Sup_le_Sup
- \+ *lemma* Inf_le_Inf
- \+ *lemma* le_Sup_iff
- \+ *lemma* Inf_le_iff
- \+ *lemma* Inf_le_Sup
- \+ *lemma* Sup_union
- \+ *lemma* Sup_inter_le
- \+ *lemma* Inf_union
- \+ *lemma* le_Inf_inter
- \+ *lemma* Sup_empty
- \+ *lemma* Inf_empty
- \+ *lemma* Sup_univ
- \+ *lemma* Inf_univ
- \+ *lemma* Sup_insert
- \+ *lemma* Inf_insert
- \+ *lemma* Sup_singleton
- \+ *lemma* Inf_singleton
- \+ *lemma* le_supr
- \+ *lemma* le_supr'
- \+ *lemma* le_supr_of_le
- \+ *lemma* supr_le
- \+ *lemma* supr_le_supr
- \+ *lemma* supr_le_supr2
- \+ *lemma* supr_le_supr_const
- \+ *lemma* supr_le_iff
- \+ *lemma* supr_congr_Prop
- \+ *lemma* infi_le
- \+ *lemma* infi_le'
- \+ *lemma* infi_le₂'
- \+ *lemma* infi_le_of_le
- \+ *lemma* le_infi
- \+ *lemma* infi_le_infi
- \+ *lemma* infi_le_infi2
- \+ *lemma* infi_le_infi_const
- \+ *lemma* le_infi_iff
- \+ *lemma* infi_congr_Prop
- \+ *lemma* infi_const
- \+ *lemma* supr_const
- \+ *lemma* infi_comm
- \+ *lemma* supr_comm
- \+ *lemma* infi_infi_eq_left
- \+ *lemma* infi_infi_eq_right
- \+ *lemma* supr_supr_eq_left
- \+ *lemma* supr_supr_eq_right
- \+ *lemma* foo
- \+ *lemma* foo'
- \+ *lemma* infi_inf_eq
- \+ *lemma* supr_sup_eq
- \+ *lemma* infi_false
- \+ *lemma* supr_false
- \+ *lemma* infi_true
- \+ *lemma* supr_true
- \+ *lemma* infi_exists
- \+ *lemma* supr_exists
- \+ *lemma* infi_and
- \+ *lemma* supr_and
- \+ *lemma* infi_or
- \+ *lemma* supr_or
- \+ *lemma* Inf_eq_infi
- \+ *lemma* Sup_eq_supr
- \+ *lemma* Inf_image
- \+ *lemma* Sup_image
- \+ *lemma* infi_emptyset
- \+ *lemma* supr_emptyset
- \+ *lemma* infi_univ
- \+ *lemma* supr_univ
- \+ *lemma* infi_union
- \+ *lemma* supr_union
- \+ *lemma* infi_insert
- \+ *lemma* supr_insert
- \+ *lemma* infi_singleton
- \+ *lemma* supr_singleton
- \+ *lemma* infi_empty
- \+ *lemma* supr_empty
- \+ *lemma* infi_unit
- \+ *lemma* supr_unit
- \+ *lemma* infi_subtype
- \+ *lemma* supr_subtype
- \+ *lemma* infi_sigma
- \+ *lemma* supr_sigma
- \+ *lemma* infi_prod
- \+ *lemma* supr_prod
- \+ *lemma* infi_sum
- \+ *lemma* supr_sum
- \+ *lemma* monotone_Sup_of_monotone
- \+ *lemma* monotone_Inf_of_monotone
- \+ *lemma* Inf_eq_top
- \+ *lemma* infi_eq_top
- \+ *lemma* Sup_eq_bot
- \+ *lemma* supr_eq_top
- \+ *theorem* set_eq_def
- \+ *theorem* subset_def
- \+ *theorem* union_def
- \+ *theorem* inter_def
- \+ *theorem* mem_univ_eq
- \+ *theorem* subset_univ
- \+ *theorem* mem_union_eq
- \+ *theorem* union_left_comm
- \+ *theorem* mem_inter_eq
- \+ *theorem* inter_left_comm
- \+ *theorem* insert_def
- \+ *theorem* insert_of_has_insert
- \+ *theorem* subset_insert
- \+ *theorem* mem_insert_iff
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* singleton_def
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* singleton_eq_singleton_iff
- \+ *def* Sup
- \+ *def* Inf
- \+ *def* supr
- \+ *def* infi

Created algebra/lattice/default.lean


Created algebra/lattice/filter.lean
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* prod.mk.eta
- \+ *lemma* prod.swap_swap
- \+ *lemma* prod.fst_swap
- \+ *lemma* prod.snd_swap
- \+ *lemma* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap_eq
- \+ *lemma* Inf_eq_finite_sets
- \+ *lemma* Sup_le_iff
- \+ *lemma* fmap_eq_image
- \+ *lemma* mem_seq_iff
- \+ *lemma* mem_prod_eq
- \+ *lemma* prod_vimage_eq
- \+ *lemma* prod_mono
- \+ *lemma* prod_inter_prod
- \+ *lemma* monotone_prod
- \+ *lemma* image_swap_prod
- \+ *lemma* prod_image_image_eq
- \+ *lemma* prod_singleton_singleton
- \+ *lemma* prod_neq_empty_iff
- \+ *lemma* prod_mk_mem_set_prod_eq
- \+ *lemma* monotone_inter
- \+ *lemma* vimage_set_of_eq
- \+ *lemma* set_of_mem_eq
- \+ *lemma* mem_image_iff_of_inverse
- \+ *lemma* image_eq_vimage_of_inverse
- \+ *lemma* image_swap_eq_vimage_swap
- \+ *lemma* monotone_set_of
- \+ *lemma* diff_right_antimono
- \+ *lemma* sUnion_mono
- \+ *lemma* Union_subset_Union
- \+ *lemma* Union_subset_Union2
- \+ *lemma* Union_subset_Union_const
- \+ *lemma* diff_neq_empty
- \+ *lemma* diff_empty
- \+ *lemma* implies_implies_true_iff
- \+ *lemma* not_not_mem_iff
- \+ *lemma* singleton_neq_emptyset
- \+ *lemma* eq_of_sup_eq_inf_eq
- \+ *lemma* inf_eq_bot_iff_le_compl
- \+ *lemma* compl_image_set_of
- \+ *lemma* neg_subset_neg_iff_subset
- \+ *lemma* sUnion_eq_Union
- \+ *lemma* directed_on_Union
- \+ *lemma* directed_of_chain
- \+ *lemma* filter_eq
- \+ *lemma* univ_mem_sets'
- \+ *lemma* univ_mem_sets
- \+ *lemma* inter_mem_sets
- \+ *lemma* Inter_mem_sets
- \+ *lemma* exists_sets_subset_iff
- \+ *lemma* monotone_mem_sets
- \+ *lemma* mem_join_sets
- \+ *lemma* mem_principal_sets
- \+ *lemma* le_principal_iff
- \+ *lemma* principal_mono
- \+ *lemma* monotone_principal
- \+ *lemma* principal_eq_iff_eq
- \+ *lemma* map_principal
- \+ *lemma* join_principal_eq_Sup
- \+ *lemma* mem_inf_sets_of_left
- \+ *lemma* mem_inf_sets_of_right
- \+ *lemma* mem_bot_sets
- \+ *lemma* empty_in_sets_eq_bot
- \+ *lemma* inhabited_of_mem_sets
- \+ *lemma* filter_eq_bot_of_not_nonempty
- \+ *lemma* forall_sets_neq_empty_iff_neq_bot
- \+ *lemma* mem_sets_of_neq_bot
- \+ *lemma* mem_sup_sets
- \+ *lemma* mem_inf_sets
- \+ *lemma* infi_sets_eq
- \+ *lemma* infi_sets_eq'
- \+ *lemma* Inf_sets_eq_finite
- \+ *lemma* supr_sets_eq
- \+ *lemma* sup_join
- \+ *lemma* supr_join
- \+ *lemma* binfi_sup_eq
- \+ *lemma* infi_sup_eq
- \+ *lemma* inf_principal
- \+ *lemma* sup_principal
- \+ *lemma* supr_principal
- \+ *lemma* principal_univ
- \+ *lemma* principal_empty
- \+ *lemma* principal_eq_bot_iff
- \+ *lemma* mem_pure
- \+ *lemma* mem_map
- \+ *lemma* image_mem_map
- \+ *lemma* map_id
- \+ *lemma* map_compose
- \+ *lemma* map_sup
- \+ *lemma* supr_map
- \+ *lemma* map_bot
- \+ *lemma* map_eq_bot_iff
- \+ *lemma* map_mono
- \+ *lemma* monotone_map
- \+ *lemma* map_infi_le
- \+ *lemma* map_infi_eq
- \+ *lemma* map_binfi_eq
- \+ *lemma* mem_bind_sets
- \+ *lemma* bind_mono
- \+ *lemma* bind_sup
- \+ *lemma* bind_mono2
- \+ *lemma* principal_bind
- \+ *lemma* seq_mono
- \+ *lemma* fmap_principal
- \+ *lemma* mem_return_sets
- \+ *lemma* infi_neq_bot_of_directed
- \+ *lemma* infi_neq_bot_iff_of_directed
- \+ *lemma* return_neq_bot
- \+ *lemma* mem_vmap_of_mem
- \+ *lemma* vmap_mono
- \+ *lemma* monotone_vmap
- \+ *lemma* vmap_principal
- \+ *lemma* vimage_mem_vmap
- \+ *lemma* le_map_vmap
- \+ *lemma* vmap_map
- \+ *lemma* vmap_neq_bot
- \+ *lemma* vmap_neq_bot_of_surj
- \+ *lemma* map_vmap_le
- \+ *lemma* le_vmap_map
- \+ *lemma* vmap_vmap_comp
- \+ *lemma* le_vmap_iff_map_le
- \+ *lemma* lift_sets_eq
- \+ *lemma* mem_lift
- \+ *lemma* mem_lift_iff
- \+ *lemma* lift_mono
- \+ *lemma* lift_mono'
- \+ *lemma* map_lift_eq
- \+ *lemma* vmap_lift_eq
- \+ *lemma* vmap_lift_eq2
- \+ *lemma* map_lift_eq2
- \+ *lemma* lift_comm
- \+ *lemma* lift_assoc
- \+ *lemma* lift_lift_same_le_lift
- \+ *lemma* lift_lift_same_eq_lift
- \+ *lemma* lift_principal
- \+ *lemma* monotone_lift
- \+ *lemma* lift_neq_bot_iff
- \+ *lemma* mem_lift'
- \+ *lemma* mem_lift'_iff
- \+ *lemma* lift'_mono
- \+ *lemma* lift'_mono'
- \+ *lemma* lift'_cong
- \+ *lemma* map_lift'_eq
- \+ *lemma* map_lift'_eq2
- \+ *lemma* vmap_lift'_eq
- \+ *lemma* vmap_lift'_eq2
- \+ *lemma* lift'_principal
- \+ *lemma* principal_le_lift'
- \+ *lemma* monotone_lift'
- \+ *lemma* lift_lift'_assoc
- \+ *lemma* lift'_lift'_assoc
- \+ *lemma* lift'_lift_assoc
- \+ *lemma* lift_lift'_same_le_lift'
- \+ *lemma* lift_lift'_same_eq_lift'
- \+ *lemma* lift'_inf_principal_eq
- \+ *lemma* lift'_neq_bot_iff
- \+ *lemma* lift'_id
- \+ *lemma* le_lift'
- \+ *lemma* vmap_eq_lift'
- \+ *lemma* prod_mem_prod
- \+ *lemma* prod_same_eq
- \+ *lemma* mem_prod_iff
- \+ *lemma* mem_prod_same_iff
- \+ *lemma* prod_comm
- \+ *lemma* prod_lift_lift
- \+ *lemma* prod_lift'_lift'
- \+ *lemma* prod_map_map_eq
- \+ *lemma* prod_vmap_vmap_eq
- \+ *lemma* prod_inf_prod
- \+ *lemma* prod_neq_bot
- \+ *lemma* prod_principal_principal
- \+ *lemma* mem_infi_sets
- \+ *lemma* mem_top_sets_iff
- \+ *lemma* infi_sets_induct
- \+ *lemma* lift_infi
- \+ *lemma* lift_infi'
- \+ *lemma* lift'_infi
- \+ *lemma* map_eq_vmap_of_inverse
- \+ *lemma* map_swap_vmap_swap_eq
- \+ *lemma* ultrafilter_pure
- \+ *lemma* ultrafilter_unique
- \+ *lemma* exists_ultrafilter
- \+ *lemma* le_of_ultrafilter
- \+ *lemma* mem_or_compl_mem_of_ultrafilter
- \+ *lemma* mem_or_mem_of_ultrafilter
- \+ *lemma* mem_of_finite_sUnion_ultrafilter
- \+ *lemma* mem_of_finite_Union_ultrafilter
- \+ *lemma* ultrafilter_of_split
- \+ *lemma* ultrafilter_map
- \+ *lemma* ultrafilter_of_spec
- \+ *lemma* ultrafilter_of_le
- \+ *lemma* ultrafilter_ultrafilter_of
- \+ *lemma* ultrafilter_of_ultrafilter
- \+ *theorem* map_bind
- \+ *theorem* seq_bind_eq
- \+ *theorem* seq_eq_bind_map
- \+ *theorem* bind_assoc
- \+ *theorem* bind_def
- \+ *theorem* ne_empty_iff_exists_mem
- \+ *theorem* pure_def
- \+ *def* prod.swap
- \+ *def* directed
- \+ *def* directed_on
- \+ *def* upwards
- \+ *def* principal
- \+ *def* join
- \+ *def* map
- \+ *def* vmap
- \+ *def* cofinite
- \+ *def* at_top
- \+ *def* at_bot
- \+ *def* towards
- \+ *def* ultrafilter

Created algebra/lattice/fixed_points.lean
- \+ *lemma* ge_of_eq
- \+ *lemma* lfp_le
- \+ *lemma* le_lfp
- \+ *lemma* lfp_eq
- \+ *lemma* lfp_induct
- \+ *lemma* monotone_lfp
- \+ *lemma* le_gfp
- \+ *lemma* gfp_le
- \+ *lemma* gfp_eq
- \+ *lemma* gfp_induct
- \+ *lemma* monotone_gfp
- \+ *lemma* lfp_comp
- \+ *lemma* gfp_comp
- \+ *lemma* lfp_lfp
- \+ *lemma* gfp_gfp
- \+ *def* lfp
- \+ *def* gfp

Created algebra/lattice/zorn.lean
- \+ *lemma* chain_insert
- \+ *lemma* succ_spec
- \+ *lemma* chain_succ
- \+ *lemma* super_of_not_max
- \+ *lemma* succ_increasing
- \+ *lemma* chain_closure_empty
- \+ *lemma* chain_closure_closure
- \+ *lemma* chain_closure_total
- \+ *lemma* chain_closure_succ_fixpoint
- \+ *lemma* chain_closure_succ_fixpoint_iff
- \+ *lemma* chain_chain_closure
- \+ *lemma* max_chain_spec
- \+ *lemma* zorn
- \+ *lemma* zorn_weak_order
- \+ *def* chain
- \+ *def* super_chain
- \+ *def* is_max_chain
- \+ *def* succ_chain
- \+ *def* max_chain

Created algebra/order.lean
- \+ *lemma* monotone_id
- \+ *lemma* monotone_const
- \+ *lemma* monotone_comp
- \+ *lemma* le_dual_eq_le
- \+ *lemma* comp_le_comp_left_of_monotone
- \+ *lemma* monotone_lam
- \+ *lemma* monotone_app
- \+ *def* monotone
- \+ *def* weak_order_dual

Created algebra/ring.lean
- \+ *theorem* mul_zero
- \+ *theorem* zero_mul
- \+ *theorem* mul_one
- \+ *theorem* mul_bit0
- \+ *theorem* mul_bit0_helper
- \+ *theorem* mul_bit1
- \+ *theorem* mul_bit1_helper
- \+ *theorem* subst_into_prod
- \+ *theorem* mk_cong
- \+ *theorem* neg_add_neg_eq_of_add_add_eq_zero
- \+ *theorem* neg_add_neg_helper
- \+ *theorem* neg_add_pos_eq_of_eq_add
- \+ *theorem* neg_add_pos_helper1
- \+ *theorem* neg_add_pos_helper2
- \+ *theorem* pos_add_neg_helper
- \+ *theorem* sub_eq_add_neg_helper
- \+ *theorem* pos_add_pos_helper
- \+ *theorem* subst_into_subtr
- \+ *theorem* neg_neg_helper
- \+ *theorem* neg_mul_neg_helper
- \+ *theorem* neg_mul_pos_helper
- \+ *theorem* pos_mul_neg_helper

Created data/bitvec.lean
- \+ *def* bitvec
- \+ *def* append

Created data/bool.lean


Created data/fin.lean
- \+ *lemma* lt_succ_of_lt
- \+ *lemma* eq_of_lt_succ_of_not_lt
- \+ *def* raise_fin

Created data/hash_map.lean
- \+ *lemma* foldl_eq_lem
- \+ *lemma* insert_lemma
- \+ *theorem* mem_as_list
- \+ *theorem* foldl_eq
- \+ *theorem* find_aux_iff
- \+ *theorem* contains_aux_iff
- \+ *theorem* valid_aux.unfold_cons
- \+ *theorem* valid_aux.nodup
- \+ *theorem* valid_aux.eq
- \+ *theorem* valid_aux.insert_lemma1
- \+ *theorem* valid.nodup
- \+ *theorem* valid.eq
- \+ *theorem* valid.eq'
- \+ *theorem* valid.as_list_nodup
- \+ *theorem* valid.as_list_length
- \+ *theorem* valid.mk
- \+ *theorem* valid.find_aux_iff
- \+ *theorem* valid.contains_aux_iff
- \+ *theorem* mk_as_list
- \+ *theorem* valid.replace_aux
- \+ *theorem* valid.replace
- \+ *theorem* valid.insert
- \+ *theorem* valid.erase_aux
- \+ *theorem* valid.erase
- \+ *theorem* find_iff
- \+ *theorem* contains_iff
- \+ *theorem* entries_empty
- \+ *theorem* keys_empty
- \+ *theorem* find_empty
- \+ *theorem* not_contains_empty
- \+ *theorem* mem_insert
- \+ *theorem* find_insert_eq
- \+ *theorem* find_insert_ne
- \+ *theorem* find_insert
- \+ *theorem* mem_erase
- \+ *theorem* find_erase_eq
- \+ *theorem* find_erase_ne
- \+ *theorem* find_erase
- \+ *def* bucket_array
- \+ *def* hash_map.mk_idx
- \+ *def* read
- \+ *def* write
- \+ *def* modify
- \+ *def* as_list
- \+ *def* foldl
- \+ *def* reinsert_aux
- \+ *def* find_aux
- \+ *def* contains_aux
- \+ *def* replace_aux
- \+ *def* erase_aux
- \+ *def* valid
- \+ *def* mk_hash_map
- \+ *def* find
- \+ *def* contains
- \+ *def* fold
- \+ *def* entries
- \+ *def* keys
- \+ *def* insert
- \+ *def* insert_all
- \+ *def* of_list
- \+ *def* erase

Created data/int/basic.lean
- \+ *lemma* neg_add_neg
- \+ *theorem* of_nat_add_neg_succ_of_nat_of_lt
- \+ *theorem* of_nat_add_neg_succ_of_nat_of_ge
- \+ *theorem* nat_abs_add_le
- \+ *theorem* nat_abs_neg_of_nat
- \+ *theorem* nat_abs_mul
- \+ *theorem* of_nat_sub
- \+ *theorem* neg_succ_of_nat_eq'
- \+ *theorem* pred_succ
- \+ *theorem* succ_pred
- \+ *theorem* neg_succ
- \+ *theorem* succ_neg_succ
- \+ *theorem* neg_pred
- \+ *theorem* pred_neg_pred
- \+ *theorem* pred_nat_succ
- \+ *theorem* neg_nat_succ
- \+ *theorem* succ_neg_nat_succ
- \+ *theorem* rec_nat_on_neg
- \+ *def* succ
- \+ *def* pred
- \+ *def* nat_succ_eq_int_succ
- \+ *def* rec_nat_on

Created data/int/order.lean
- \+ *theorem* coe_nat_nonneg
- \+ *theorem* coe_nat_pos
- \+ *theorem* coe_nat_succ_pos
- \+ *theorem* exists_eq_coe_nat
- \+ *theorem* exists_eq_neg_coe_nat
- \+ *theorem* coe_nat_nat_abs_of_nonneg
- \+ *theorem* coe_nat_nat_abs_of_nonpos
- \+ *theorem* coe_nat_nat_abs
- \+ *theorem* nat_abs_abs
- \+ *theorem* lt_of_add_one_le
- \+ *theorem* add_one_le_of_lt
- \+ *theorem* lt_add_one_of_le
- \+ *theorem* le_of_lt_add_one
- \+ *theorem* sub_one_le_of_lt
- \+ *theorem* lt_of_sub_one_le
- \+ *theorem* le_sub_one_of_lt
- \+ *theorem* lt_of_le_sub_one
- \+ *theorem* sign_of_succ
- \+ *theorem* exists_eq_neg_succ_coe_nat
- \+ *theorem* eq_one_of_mul_eq_one_right
- \+ *theorem* eq_one_of_mul_eq_one_left
- \+ *theorem* eq_one_of_mul_eq_self_left
- \+ *theorem* eq_one_of_mul_eq_self_right
- \+ *theorem* eq_one_of_dvd_one
- \+ *theorem* exists_least_of_bdd
- \+ *theorem* exists_greatest_of_bdd

Created data/lazy_list.lean
- \+ *def* singleton
- \+ *def* of_list
- \+ *def* to_list
- \+ *def* head
- \+ *def* tail
- \+ *def* append
- \+ *def* map
- \+ *def* map₂
- \+ *def* zip
- \+ *def* join
- \+ *def* for
- \+ *def* approx
- \+ *def* filter
- \+ *def* nth

Created data/list/basic.lean
- \+ *lemma* cons_ne_nil
- \+ *lemma* head_eq_of_cons_eq
- \+ *lemma* tail_eq_of_cons_eq
- \+ *lemma* cons_inj
- \+ *lemma* last_singleton
- \+ *lemma* last_cons_cons
- \+ *lemma* index_of_le_length
- \+ *lemma* not_mem_of_index_of_eq_length
- \+ *lemma* index_of_lt_length
- \+ *lemma* ith_zero
- \+ *lemma* ith_succ
- \+ *lemma* taken_zero
- \+ *lemma* taken_nil
- \+ *lemma* taken_cons
- \+ *lemma* taken_all
- \+ *lemma* taken_all_of_ge
- \+ *lemma* taken_taken
- \+ *lemma* length_taken_le
- \+ *lemma* length_taken_eq
- \+ *lemma* count_nil
- \+ *lemma* count_cons
- \+ *lemma* count_cons'
- \+ *lemma* count_cons_self
- \+ *lemma* count_cons_of_ne
- \+ *lemma* count_cons_ge_count
- \+ *lemma* count_singleton
- \+ *lemma* count_append
- \+ *lemma* count_concat
- \+ *lemma* mem_of_count_pos
- \+ *lemma* count_pos_of_mem
- \+ *lemma* mem_iff_count_pos
- \+ *lemma* count_eq_zero_of_not_mem
- \+ *lemma* not_mem_of_count_eq_zero
- \+ *theorem* append.assoc
- \+ *theorem* concat_nil
- \+ *theorem* concat_cons
- \+ *theorem* concat_ne_nil
- \+ *theorem* concat_append
- \+ *theorem* append_concat
- \+ *theorem* last_congr
- \+ *theorem* head_cons
- \+ *theorem* tail_nil
- \+ *theorem* tail_cons
- \+ *theorem* index_of_nil
- \+ *theorem* index_of_cons
- \+ *theorem* index_of_cons_of_eq
- \+ *theorem* index_of_cons_of_ne
- \+ *theorem* index_of_of_not_mem
- \+ *theorem* nth_eq_some
- \+ *theorem* index_of_nth
- \+ *theorem* inth_zero
- \+ *theorem* inth_succ
- \+ *theorem* length_dropn
- \+ *def* inth
- \+ *def* ith
- \+ *def* count
- \+ *def* permutations_aux2
- \+ *def* permutations_aux.F
- \+ *def* permutations_aux
- \+ *def* permutations
- \+ *def* permutations_aux.eqn_1
- \+ *def* permutations_aux.eqn_2

Created data/list/comb.lean
- \+ *lemma* dmap_nil
- \+ *lemma* dmap_cons_of_pos
- \+ *lemma* dmap_cons_of_neg
- \+ *lemma* mem_dmap
- \+ *lemma* exists_of_mem_dmap
- \+ *lemma* map_dmap_of_inv_of_pos
- \+ *lemma* mem_of_dinj_of_mem_dmap
- \+ *lemma* not_mem_dmap_of_dinj_of_not_mem
- \+ *theorem* length_map_accumr
- \+ *theorem* length_map_accumr₂
- \+ *theorem* foldl_nil
- \+ *theorem* foldl_cons
- \+ *theorem* foldr_nil
- \+ *theorem* foldr_cons
- \+ *theorem* foldl_append
- \+ *theorem* foldr_append
- \+ *theorem* foldl_reverse
- \+ *theorem* foldr_reverse
- \+ *theorem* length_replicate
- \+ *theorem* map₂_nil1
- \+ *theorem* map₂_nil2
- \+ *theorem* all_nil
- \+ *theorem* all_cons
- \+ *theorem* all_eq_tt_of_forall
- \+ *theorem* forall_mem_eq_tt_of_all_eq_tt
- \+ *theorem* all_eq_tt_iff
- \+ *theorem* any_nil
- \+ *theorem* any_cons
- \+ *theorem* any_of_mem
- \+ *theorem* exists_of_any_eq_tt
- \+ *theorem* any_eq_tt_iff
- \+ *theorem* forall_mem_nil
- \+ *theorem* forall_mem_cons
- \+ *theorem* of_forall_mem_cons
- \+ *theorem* forall_mem_of_forall_mem_cons
- \+ *theorem* forall_mem_cons_iff
- \+ *theorem* not_exists_mem_nil
- \+ *theorem* exists_mem_cons_of
- \+ *theorem* exists_mem_cons_of_exists
- \+ *theorem* or_exists_of_exists_mem_cons
- \+ *theorem* exists_mem_cons_iff
- \+ *theorem* zip_cons_cons
- \+ *theorem* zip_nil_left
- \+ *theorem* zip_nil_right
- \+ *theorem* unzip_nil
- \+ *theorem* unzip_cons'
- \+ *theorem* unzip_cons
- \+ *theorem* zip_unzip
- \+ *theorem* length_mapAccumR
- \+ *theorem* length_mapAccumR₂
- \+ *theorem* nil_product
- \+ *theorem* product_cons
- \+ *theorem* product_nil
- \+ *theorem* eq_of_mem_map_pair₁
- \+ *theorem* mem_of_mem_map_pair₁
- \+ *theorem* mem_product
- \+ *theorem* mem_of_mem_product_left
- \+ *theorem* mem_of_mem_product_right
- \+ *theorem* length_product
- \- *theorem* length_map₂
- \+ *def* map_accumr
- \+ *def* map_accumr₂
- \+ *def* replicate
- \+ *def* decidable_forall_mem
- \+ *def* decidable_exists_mem
- \+ *def* mapAccumR
- \+ *def* mapAccumR₂
- \+ *def* flat
- \+ *def* product
- \+ *def* dinj₁
- \+ *def* dinj
- \+ *def* dmap
- \+ *def* list_equiv_of_equiv
- \+ *def* list_nat_equiv_nat
- \+ *def* list_equiv_self_of_equiv_nat
- \- *def* map₂

Created data/list/default.lean


Created data/list/perm.lean
- \+ *lemma* perm_of_qeq
- \+ *lemma* perm_insert_insert
- \+ *theorem* eqv
- \+ *theorem* mem_of_perm
- \+ *theorem* not_mem_of_perm
- \+ *theorem* mem_iff_mem_of_perm
- \+ *theorem* perm_app_left
- \+ *theorem* perm_app_right
- \+ *theorem* perm_app
- \+ *theorem* perm_cons_app
- \+ *theorem* perm_cons_app_simp
- \+ *theorem* perm_app_comm
- \+ *theorem* length_eq_length_of_perm
- \+ *theorem* eq_nil_of_perm_nil
- \+ *theorem* not_perm_nil_cons
- \+ *theorem* eq_singleton_of_perm
- \+ *theorem* eq_singleton_of_perm_inv
- \+ *theorem* perm_rev
- \+ *theorem* perm_rev_simp
- \+ *theorem* perm_middle
- \+ *theorem* perm_middle_simp
- \+ *theorem* perm_cons_app_cons
- \+ *theorem* perm_erase
- \+ *theorem* perm_induction_on
- \+ *theorem* xswap
- \+ *theorem* perm_map
- \+ *theorem* count_eq_count_of_perm
- \+ *theorem* perm_of_forall_count_eq
- \+ *theorem* perm_iff_forall_count_eq_count
- \+ *theorem* perm_iff_forall_mem_count_eq_count
- \+ *theorem* qeq_app
- \+ *theorem* mem_head_of_qeq
- \+ *theorem* mem_tail_of_qeq
- \+ *theorem* mem_cons_of_qeq
- \+ *theorem* length_eq_of_qeq
- \+ *theorem* qeq_of_mem
- \+ *theorem* qeq_split
- \+ *theorem* perm_inv_core
- \+ *theorem* perm_cons_inv
- \+ *theorem* perm_app_inv_left
- \+ *theorem* perm_app_inv_right
- \+ *theorem* perm_app_inv
- \+ *theorem* foldl_eq_of_perm
- \+ *theorem* foldr_eq_of_perm
- \+ *theorem* erase_perm_erase_of_perm
- \+ *theorem* perm_erase_dup_of_perm
- \+ *theorem* perm_union_left
- \+ *theorem* perm_union_right
- \+ *theorem* perm_union
- \+ *theorem* perm_insert
- \+ *theorem* perm_inter_left
- \+ *theorem* perm_inter_right
- \+ *theorem* perm_inter
- \+ *theorem* perm_ext
- \+ *theorem* nodup_of_perm_of_nodup
- \+ *theorem* perm_product_left
- \+ *theorem* perm_product_right
- \+ *theorem* perm_product
- \+ *theorem* perm_filter
- \- *theorem* perm_app_cons
- \- *theorem* subset_of_mem_of_subset_of_qeq
- \+ *def* decidable_perm_aux
- \+ *def* decidable_perm

Created data/list/set.lean
- \+ *lemma* erase_nil
- \+ *lemma* erase_cons
- \+ *lemma* erase_cons_head
- \+ *lemma* erase_cons_tail
- \+ *lemma* length_erase_of_mem
- \+ *lemma* erase_of_not_mem
- \+ *lemma* erase_append_left
- \+ *lemma* erase_append_right
- \+ *lemma* erase_sublist
- \+ *lemma* erase_subset
- \+ *lemma* disjoint_left
- \+ *lemma* disjoint_right
- \+ *lemma* disjoint.comm
- \+ *lemma* disjoint_of_subset_left
- \+ *lemma* disjoint_of_subset_right
- \+ *lemma* disjoint_of_disjoint_cons_left
- \+ *lemma* disjoint_of_disjoint_cons_right
- \+ *lemma* disjoint_nil_left
- \+ *lemma* disjoint_nil_right
- \+ *lemma* disjoint_cons_of_not_mem_of_disjoint
- \+ *lemma* disjoint_append_of_disjoint_left
- \+ *lemma* disjoint_of_disjoint_append_left_left
- \+ *lemma* disjoint_of_disjoint_append_left_right
- \+ *lemma* disjoint_of_disjoint_append_right_left
- \+ *lemma* disjoint_of_disjoint_append_right_right
- \+ *lemma* upto_step
- \+ *lemma* dmap_nodup_of_dinj
- \+ *theorem* insert_nil
- \+ *theorem* insert.def
- \+ *theorem* insert_of_mem
- \+ *theorem* insert_of_not_mem
- \+ *theorem* mem_insert_self
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_insert_iff
- \+ *theorem* length_insert_of_mem
- \+ *theorem* length_insert_of_not_mem
- \+ *theorem* forall_mem_insert_of_forall_mem
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* upto_nil
- \+ *theorem* upto_succ
- \+ *theorem* length_upto
- \+ *theorem* upto_ne_nil_of_ne_zero
- \+ *theorem* lt_of_mem_upto
- \+ *theorem* mem_upto_succ_of_mem_upto
- \+ *theorem* mem_upto_of_lt
- \+ *theorem* union_nil
- \+ *theorem* union_cons
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* mem_union_iff
- \+ *theorem* forall_mem_union
- \+ *theorem* forall_mem_of_forall_mem_union_left
- \+ *theorem* forall_mem_of_forall_mem_union_right
- \+ *theorem* inter_nil
- \+ *theorem* inter_cons_of_mem
- \+ *theorem* inter_cons_of_not_mem
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter_of_mem_of_mem
- \+ *theorem* mem_inter_iff
- \+ *theorem* inter_eq_nil_of_disjoint
- \+ *theorem* forall_mem_inter_of_forall_left
- \+ *theorem* forall_mem_inter_of_forall_right
- \+ *theorem* nodup_nil
- \+ *theorem* nodup_cons
- \+ *theorem* nodup_singleton
- \+ *theorem* nodup_of_nodup_cons
- \+ *theorem* not_mem_of_nodup_cons
- \+ *theorem* not_nodup_cons_of_mem
- \+ *theorem* nodup_of_sublist
- \+ *theorem* not_nodup_cons_of_not_nodup
- \+ *theorem* nodup_of_nodup_append_left
- \+ *theorem* nodup_of_nodup_append_right
- \+ *theorem* disjoint_of_nodup_append
- \+ *theorem* nodup_append_of_nodup_of_nodup_of_disjoint
- \+ *theorem* nodup_app_comm
- \+ *theorem* nodup_head
- \+ *theorem* nodup_middle
- \+ *theorem* nodup_of_nodup_map
- \+ *theorem* nodup_map
- \+ *theorem* nodup_erase_of_nodup
- \+ *theorem* mem_erase_of_nodup
- \+ *theorem* erase_dup_nil
- \+ *theorem* erase_dup_cons_of_mem
- \+ *theorem* erase_dup_cons_of_not_mem
- \+ *theorem* mem_erase_dup
- \+ *theorem* erase_dup_sublist
- \+ *theorem* mem_of_mem_erase_dup
- \+ *theorem* mem_erase_dup_iff
- \+ *theorem* erase_dup_subset
- \+ *theorem* subset_erase_dup
- \+ *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_eq_of_nodup
- \+ *theorem* nodup_product
- \+ *theorem* nodup_filter
- \+ *theorem* nodup_concat
- \+ *theorem* nodup_insert
- \+ *theorem* nodup_upto
- \+ *theorem* nodup_union_of_nodup_of_nodup
- \+ *theorem* nodup_inter_of_nodup
- \+ *def* disjoint
- \+ *def* upto
- \+ *def* erase_dup

Created data/list/sort.lean
- \+ *lemma* succ_le_succ_iff
- \+ *lemma* lt_succ_iff_le
- \+ *theorem* add_pos_left
- \+ *theorem* add_pos_right
- \+ *theorem* add_pos_iff_pos_or_pos
- \+ *theorem* sorted_nil
- \+ *theorem* sorted_singleton
- \+ *theorem* sorted_of_sorted_cons
- \+ *theorem* forall_mem_rel_of_sorted_cons
- \+ *theorem* sorted_cons
- \+ *theorem* perm_ordered_insert
- \+ *theorem* perm_insertion_sort
- \+ *theorem* sorted_ordered_insert
- \+ *theorem* sorted_insert_sort
- \+ *theorem* split_cons_of_eq
- \+ *theorem* length_split_le
- \+ *theorem* length_split_lt
- \+ *theorem* perm_split
- \+ *theorem* merge_sort_cons_cons
- \+ *theorem* perm_merge
- \+ *theorem* perm_merge_sort
- \+ *theorem* sorted_merge
- \+ *theorem* sorted_merge_sort
- \- *theorem* ordered_insert_nil
- \- *theorem* ordered_insert_cons
- \+ *def* sorted
- \+ *def* ordered_insert
- \+ *def* insertion_sort
- \+ *def* split
- \+ *def* merge
- \+ *def* merge_sort

Created data/nat/basic.lean
- \+ *lemma* addl_zero_left
- \+ *lemma* addl_succ_left
- \+ *lemma* zero_has_zero
- \+ *lemma* one_succ_zero
- \+ *theorem* addl_zero_right
- \+ *theorem* addl_succ_right
- \+ *theorem* add_eq_addl
- \+ *theorem* add_one_ne_zero
- \+ *theorem* eq_zero_or_eq_succ_pred
- \+ *theorem* exists_eq_succ_of_ne_zero
- \+ *theorem* succ_inj
- \+ *theorem* discriminate
- \+ *theorem* two_step_induction
- \+ *theorem* sub_induction
- \+ *theorem* succ_add_eq_succ_add
- \+ *theorem* eq_zero_of_add_eq_zero
- \+ *theorem* add_one
- \+ *theorem* one_add
- \+ *def* addl
- \+ *def* iterate

Created data/nat/bquant.lean
- \+ *def* ball

Created data/nat/gcd.lean
- \+ *lemma* gcd_eq_one_of_coprime
- \+ *theorem* gcd_dvd
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* dvd_gcd
- \+ *theorem* gcd_comm
- \+ *theorem* gcd_assoc
- \+ *theorem* gcd_one_right
- \+ *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right
- \+ *theorem* gcd_pos_of_pos_left
- \+ *theorem* gcd_pos_of_pos_right
- \+ *theorem* eq_zero_of_gcd_eq_zero_left
- \+ *theorem* eq_zero_of_gcd_eq_zero_right
- \+ *theorem* gcd_div
- \+ *theorem* gcd_dvd_gcd_of_dvd_left
- \+ *theorem* gcd_dvd_gcd_of_dvd_right
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* lcm_comm
- \+ *theorem* lcm_zero_left
- \+ *theorem* lcm_zero_right
- \+ *theorem* lcm_one_left
- \+ *theorem* lcm_one_right
- \+ *theorem* lcm_self
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* gcd_mul_lcm
- \+ *theorem* lcm_dvd
- \+ *theorem* lcm_assoc
- \+ *theorem* coprime_swap
- \+ *theorem* coprime_of_dvd
- \+ *theorem* coprime_of_dvd'
- \+ *theorem* dvd_of_coprime_of_dvd_mul_right
- \+ *theorem* dvd_of_coprime_of_dvd_mul_left
- \+ *theorem* gcd_mul_left_cancel_of_coprime
- \+ *theorem* gcd_mul_right_cancel_of_coprime
- \+ *theorem* gcd_mul_left_cancel_of_coprime_right
- \+ *theorem* gcd_mul_right_cancel_of_coprime_right
- \+ *theorem* coprime_div_gcd_div_gcd
- \+ *theorem* not_coprime_of_dvd_of_dvd
- \+ *theorem* exists_coprime
- \+ *theorem* coprime_mul
- \+ *theorem* coprime_mul_right
- \+ *theorem* coprime_of_coprime_dvd_left
- \+ *theorem* coprime_of_coprime_dvd_right
- \+ *theorem* coprime_of_coprime_mul_left
- \+ *theorem* coprime_of_coprime_mul_right
- \+ *theorem* coprime_of_coprime_mul_left_right
- \+ *theorem* coprime_of_coprime_mul_right_right
- \+ *theorem* comprime_one_left
- \+ *theorem* comprime_one_right
- \+ *theorem* coprime_pow_left
- \+ *theorem* coprime_pow_right
- \+ *theorem* coprime_pow
- \+ *theorem* exists_eq_prod_and_dvd_and_dvd

Created data/nat/sub.lean
- \+ *lemma* dist_succ_succ
- \+ *lemma* dist_pos_of_ne
- \- *lemma* dist_eq_max_sub_min
- \+ *theorem* dist.def
- \+ *theorem* dist_comm
- \+ *theorem* dist_self
- \+ *theorem* eq_of_dist_eq_zero
- \+ *theorem* dist_eq_zero
- \+ *theorem* dist_eq_sub_of_le
- \+ *theorem* dist_eq_sub_of_ge
- \+ *theorem* dist_zero_right
- \+ *theorem* dist_zero_left
- \+ *theorem* dist_add_add_right
- \+ *theorem* dist_add_add_left
- \+ *theorem* dist_eq_intro
- \+ *theorem* dist.triangle_inequality
- \+ *theorem* dist_mul_right
- \+ *theorem* dist_mul_left
- \+ *def* dist

Created data/num/basic.lean


Created data/num/bitwise.lean


Created data/num/lemmas.lean


Created data/pfun.lean
- \+ *theorem* to_of_option
- \+ *theorem* of_to_option
- \+ *theorem* dom_iff_mem
- \+ *theorem* bind_some_eq_map
- \+ *theorem* some_bind
- \+ *theorem* bind_assoc
- \+ *theorem* mem_unique
- \+ *theorem* mem_some
- \+ *theorem* mem_ret
- \+ *theorem* mem_ret_iff
- \+ *theorem* eq_ret_of_mem
- \+ *theorem* mem_bind
- \+ *theorem* exists_of_mem_bind
- \+ *theorem* assert_defined
- \+ *theorem* bind_defined
- \+ *theorem* dom_iff_graph
- \+ *theorem* pure_defined
- \+ *def* to_option
- \+ *def* of_option
- \+ *def* assert
- \+ *def* restrict
- \+ *def* pfun
- \+ *def* dom
- \+ *def* fn
- \+ *def* eval_opt
- \+ *def* as_subtype
- \+ *def* graph
- \+ *def* ran

Created data/pnat.lean
- \+ *def* pnat

Created data/rat.lean
- \+ *lemma* linear_order_cases_on_eq
- \+ *lemma* linear_order_cases_on_lt
- \+ *lemma* linear_order_cases_on_gt
- \+ *lemma* mul_nonneg_iff_right_nonneg_of_pos
- \+ *lemma* not_antimono
- \+ *def* linear_order_cases_on
- \+ *def* rat
- \+ *def* decidable_nonneg

Created data/seq/computation.lean
- \+ *lemma* map_ret
- \+ *lemma* map_think
- \+ *lemma* destruct_map
- \+ *lemma* map_comp
- \+ *lemma* ret_bind
- \+ *lemma* think_bind
- \+ *lemma* return_def
- \+ *lemma* map_ret'
- \+ *lemma* map_think'
- \+ *lemma* lift_rel_rec.lem
- \+ *theorem* destruct_eq_ret
- \+ *theorem* destruct_eq_think
- \+ *theorem* destruct_ret
- \+ *theorem* destruct_think
- \+ *theorem* destruct_empty
- \+ *theorem* head_ret
- \+ *theorem* head_think
- \+ *theorem* head_empty
- \+ *theorem* tail_ret
- \+ *theorem* tail_think
- \+ *theorem* tail_empty
- \+ *theorem* think_empty
- \+ *theorem* le_stable
- \+ *theorem* mem_unique
- \+ *theorem* terminates_of_mem
- \+ *theorem* terminates_def
- \+ *theorem* ret_mem
- \+ *theorem* eq_of_ret_mem
- \+ *theorem* think_mem
- \+ *theorem* of_think_mem
- \+ *theorem* of_think_terminates
- \+ *theorem* not_mem_empty
- \+ *theorem* not_terminates_empty
- \+ *theorem* eq_empty_of_not_terminates
- \+ *theorem* thinkN_mem
- \+ *theorem* of_thinkN_terminates
- \+ *theorem* mem_promises
- \+ *theorem* empty_promises
- \+ *theorem* get_think
- \+ *theorem* get_thinkN
- \+ *theorem* get_ret
- \+ *theorem* length_ret
- \+ *theorem* results_ret
- \+ *theorem* length_think
- \+ *theorem* results_think
- \+ *theorem* of_results_think
- \+ *theorem* results_think_iff
- \+ *theorem* results_thinkN
- \+ *theorem* results_thinkN_ret
- \+ *theorem* length_thinkN
- \+ *theorem* has_bind_eq_bind
- \+ *theorem* map_id
- \+ *theorem* bind_ret
- \+ *theorem* bind_ret'
- \+ *theorem* bind_assoc
- \+ *theorem* results_bind
- \+ *theorem* mem_bind
- \+ *theorem* get_bind
- \+ *theorem* length_bind
- \+ *theorem* of_results_bind
- \+ *theorem* exists_of_mem_bind
- \+ *theorem* bind_promises
- \+ *theorem* has_map_eq_map
- \+ *theorem* mem_map
- \+ *theorem* exists_of_mem_map
- \+ *theorem* terminates_map_iff
- \+ *theorem* ret_orelse
- \+ *theorem* orelse_ret
- \+ *theorem* orelse_think
- \+ *theorem* empty_orelse
- \+ *theorem* orelse_empty
- \+ *theorem* equiv.refl
- \+ *theorem* equiv.symm
- \+ *theorem* equiv.trans
- \+ *theorem* equiv.equivalence
- \+ *theorem* equiv_of_mem
- \+ *theorem* terminates_congr
- \+ *theorem* promises_congr
- \+ *theorem* get_equiv
- \+ *theorem* think_equiv
- \+ *theorem* thinkN_equiv
- \+ *theorem* bind_congr
- \+ *theorem* equiv_ret_of_mem
- \+ *theorem* lift_rel.swap
- \+ *theorem* lift_eq_iff_equiv
- \+ *theorem* lift_rel_of_mem
- \+ *theorem* exists_of_lift_rel_left
- \+ *theorem* exists_of_lift_rel_right
- \+ *theorem* lift_rel_def
- \+ *theorem* lift_rel_bind
- \+ *theorem* lift_rel_return_left
- \+ *theorem* lift_rel_return_right
- \+ *theorem* lift_rel_return
- \+ *theorem* lift_rel_think_left
- \+ *theorem* lift_rel_think_right
- \+ *theorem* lift_rel_mem_cases
- \+ *theorem* lift_rel_congr
- \+ *theorem* lift_rel_map
- \+ *theorem* map_congr
- \+ *theorem* lift_rel_aux.swap
- \+ *theorem* lift_rel_rec
- \+ *def* computation
- \+ *def* return
- \+ *def* think
- \+ *def* thinkN
- \+ *def* head
- \+ *def* tail
- \+ *def* empty
- \+ *def* run_for
- \+ *def* destruct
- \+ *def* cases_on
- \+ *def* corec.F
- \+ *def* corec
- \+ *def* lmap
- \+ *def* rmap
- \+ *def* corec_eq
- \+ *def* terminates
- \+ *def* promises
- \+ *def* length
- \+ *def* get
- \+ *def* get_mem
- \+ *def* get_eq_of_mem
- \+ *def* mem_of_get_eq
- \+ *def* get_promises
- \+ *def* mem_of_promises
- \+ *def* get_eq_of_promises
- \+ *def* results
- \+ *def* results_of_terminates
- \+ *def* results_of_terminates'
- \+ *def* results.mem
- \+ *def* results.terminates
- \+ *def* results.length
- \+ *def* results.val_unique
- \+ *def* results.len_unique
- \+ *def* exists_results_of_mem
- \+ *def* eq_thinkN
- \+ *def* eq_thinkN'
- \+ *def* mem_rec_on
- \+ *def* terminates_rec_on
- \+ *def* map
- \+ *def* bind.G
- \+ *def* bind.F
- \+ *def* bind
- \+ *def* join
- \+ *def* orelse
- \+ *def* equiv
- \+ *def* lift_rel
- \+ *def* lift_rel.refl
- \+ *def* lift_rel.symm
- \+ *def* lift_rel.trans
- \+ *def* lift_rel.equiv
- \+ *def* lift_rel.imp
- \+ *def* terminates_of_lift_rel
- \+ *def* rel_of_lift_rel
- \+ *def* lift_rel_aux
- \+ *def* lift_rel_aux.ret_left
- \+ *def* lift_rel_aux.ret_right

Created data/seq/parallel.lean
- \+ *lemma* terminates_parallel.aux
- \+ *lemma* map_parallel
- \+ *lemma* parallel_congr_lem
- \+ *theorem* terminates_parallel
- \+ *theorem* exists_of_mem_parallel
- \+ *theorem* parallel_empty
- \+ *theorem* parallel_promises
- \+ *theorem* mem_parallel
- \+ *theorem* parallel_congr_left
- \+ *theorem* parallel_congr_right
- \+ *def* parallel.aux2
- \+ *def* parallel.aux1
- \+ *def* parallel
- \+ *def* parallel_rec

Created data/seq/seq.lean
- \+ *lemma* mem_cons
- \+ *lemma* mem_cons_of_mem
- \+ *lemma* eq_or_mem_of_mem_cons
- \+ *lemma* mem_cons_iff
- \+ *lemma* coinduction
- \+ *lemma* coinduction2
- \+ *lemma* nil_append
- \+ *lemma* cons_append
- \+ *lemma* append_nil
- \+ *lemma* append_assoc
- \+ *lemma* map_nil
- \+ *lemma* map_cons
- \+ *lemma* map_id
- \+ *lemma* map_tail
- \+ *lemma* map_comp
- \+ *lemma* map_nth
- \+ *lemma* join_nil
- \+ *lemma* join_cons_nil
- \+ *lemma* join_cons_cons
- \+ *lemma* join_cons
- \+ *lemma* join_append
- \+ *lemma* exists_of_mem_map
- \+ *theorem* le_stable
- \+ *theorem* not_mem_nil
- \+ *theorem* destruct_eq_nil
- \+ *theorem* destruct_eq_cons
- \+ *theorem* destruct_nil
- \+ *theorem* destruct_cons
- \+ *theorem* head_eq_destruct
- \+ *theorem* head_nil
- \+ *theorem* head_cons
- \+ *theorem* tail_nil
- \+ *theorem* tail_cons
- \+ *theorem* mem_rec_on
- \+ *theorem* map_append
- \+ *theorem* dropn_add
- \+ *theorem* dropn_tail
- \+ *theorem* nth_tail
- \+ *theorem* head_dropn
- \+ *theorem* mem_map
- \+ *theorem* map_id
- \+ *theorem* join_map_ret
- \+ *theorem* bind_ret
- \+ *theorem* ret_bind
- \+ *theorem* map_join'
- \+ *theorem* map_join
- \+ *theorem* join_join
- \+ *theorem* bind_assoc
- \+ *def* seq
- \+ *def* seq1
- \+ *def* nil
- \+ *def* cons
- \+ *def* nth
- \+ *def* omap
- \+ *def* head
- \+ *def* tail
- \+ *def* destruct
- \+ *def* cases_on
- \+ *def* corec.F
- \+ *def* corec
- \+ *def* corec_eq
- \+ *def* of_list
- \+ *def* of_stream
- \+ *def* of_lazy_list
- \+ *def* append
- \+ *def* map
- \+ *def* join
- \+ *def* drop
- \+ *def* take
- \+ *def* split_at
- \+ *def* zip_with
- \+ *def* zip
- \+ *def* unzip
- \+ *def* to_list
- \+ *def* to_stream
- \+ *def* to_list_or_stream
- \+ *def* of_list_nil
- \+ *def* of_list_cons
- \+ *def* of_stream_cons
- \+ *def* of_list_append
- \+ *def* of_stream_append
- \+ *def* to_list'
- \+ *def* of_mem_append
- \+ *def* mem_append_left
- \+ *def* to_seq
- \+ *def* ret
- \+ *def* bind

Created data/seq/wseq.lean
- \+ *lemma* nil_append
- \+ *lemma* cons_append
- \+ *lemma* think_append
- \+ *lemma* append_nil
- \+ *lemma* append_assoc
- \+ *lemma* exists_of_mem_map
- \+ *lemma* map_nil
- \+ *lemma* map_cons
- \+ *lemma* map_think
- \+ *lemma* map_comp
- \+ *lemma* destruct_map
- \+ *lemma* destruct_append
- \+ *lemma* destruct_join
- \+ *lemma* join_append
- \+ *theorem* not_mem_nil
- \+ *theorem* lift_rel_o.imp
- \+ *theorem* lift_rel_o.imp_right
- \+ *theorem* bisim_o.imp
- \+ *theorem* lift_rel_destruct
- \+ *theorem* lift_rel_destruct_iff
- \+ *theorem* destruct_congr
- \+ *theorem* destruct_congr_iff
- \+ *theorem* equiv.refl
- \+ *theorem* equiv.symm
- \+ *theorem* equiv.trans
- \+ *theorem* equiv.equivalence
- \+ *theorem* destruct_nil
- \+ *theorem* destruct_cons
- \+ *theorem* destruct_think
- \+ *theorem* seq_destruct_nil
- \+ *theorem* seq_destruct_cons
- \+ *theorem* seq_destruct_think
- \+ *theorem* head_nil
- \+ *theorem* head_cons
- \+ *theorem* head_think
- \+ *theorem* flatten_ret
- \+ *theorem* flatten_think
- \+ *theorem* destruct_flatten
- \+ *theorem* head_terminates_iff
- \+ *theorem* tail_nil
- \+ *theorem* tail_cons
- \+ *theorem* tail_think
- \+ *theorem* dropn_nil
- \+ *theorem* dropn_cons
- \+ *theorem* dropn_think
- \+ *theorem* dropn_add
- \+ *theorem* dropn_tail
- \+ *theorem* nth_add
- \+ *theorem* nth_tail
- \+ *theorem* destruct_tail
- \+ *theorem* destruct_dropn
- \+ *theorem* head_terminates_of_head_tail_terminates
- \+ *theorem* destruct_some_of_destruct_tail_some
- \+ *theorem* head_some_of_head_tail_some
- \+ *theorem* head_some_of_nth_some
- \+ *theorem* nth_terminates_le
- \+ *theorem* head_terminates_of_nth_terminates
- \+ *theorem* destruct_terminates_of_nth_terminates
- \+ *theorem* mem_rec_on
- \+ *theorem* mem_think
- \+ *theorem* eq_or_mem_iff_mem
- \+ *theorem* mem_cons_iff
- \+ *theorem* mem_cons_of_mem
- \+ *theorem* mem_cons
- \+ *theorem* mem_of_mem_tail
- \+ *theorem* mem_of_mem_dropn
- \+ *theorem* nth_mem
- \+ *theorem* exists_nth_of_mem
- \+ *theorem* exists_dropn_of_mem
- \+ *theorem* lift_rel_dropn_destruct
- \+ *theorem* exists_of_lift_rel_left
- \+ *theorem* exists_of_lift_rel_right
- \+ *theorem* head_terminates_of_mem
- \+ *theorem* cons_congr
- \+ *theorem* think_equiv
- \+ *theorem* think_congr
- \+ *theorem* head_congr
- \+ *theorem* flatten_equiv
- \+ *theorem* lift_rel_flatten
- \+ *theorem* flatten_congr
- \+ *theorem* tail_congr
- \+ *theorem* dropn_congr
- \+ *theorem* nth_congr
- \+ *theorem* mem_congr
- \+ *theorem* productive_congr
- \+ *theorem* equiv.ext
- \+ *theorem* length_eq_map
- \+ *theorem* to_list_of_list
- \+ *theorem* destruct_of_seq
- \+ *theorem* head_of_seq
- \+ *theorem* tail_of_seq
- \+ *theorem* dropn_of_seq
- \+ *theorem* nth_of_seq
- \+ *theorem* to_seq_of_seq
- \+ *theorem* map_id
- \+ *theorem* map_ret
- \+ *theorem* map_append
- \+ *theorem* mem_map
- \+ *theorem* exists_of_mem_join
- \+ *theorem* exists_of_mem_bind
- \+ *theorem* lift_rel_map
- \+ *theorem* map_congr
- \+ *theorem* lift_rel_append
- \+ *theorem* lift_rel_join.lem
- \+ *theorem* lift_rel_join
- \+ *theorem* join_congr
- \+ *theorem* lift_rel_bind
- \+ *theorem* bind_congr
- \+ *theorem* join_ret
- \+ *theorem* join_map_ret
- \+ *theorem* bind_ret
- \+ *theorem* ret_bind
- \+ *theorem* map_join
- \+ *theorem* join_join
- \+ *theorem* bind_assoc
- \+ *def* wseq
- \+ *def* of_seq
- \+ *def* of_list
- \+ *def* of_stream
- \+ *def* nil
- \+ *def* cons
- \+ *def* think
- \+ *def* destruct
- \+ *def* cases_on
- \+ *def* head
- \+ *def* flatten
- \+ *def* tail
- \+ *def* drop
- \+ *def* nth
- \+ *def* to_list
- \+ *def* length
- \+ *def* is_finite
- \+ *def* get
- \+ *def* productive
- \+ *def* update_nth
- \+ *def* remove_nth
- \+ *def* filter_map
- \+ *def* filter
- \+ *def* find
- \+ *def* zip_with
- \+ *def* zip
- \+ *def* find_indexes
- \+ *def* find_index
- \+ *def* index_of
- \+ *def* indexes_of
- \+ *def* union
- \+ *def* is_empty
- \+ *def* compute
- \+ *def* take
- \+ *def* split_at
- \+ *def* any
- \+ *def* all
- \+ *def* scanl
- \+ *def* inits
- \+ *def* collect
- \+ *def* append
- \+ *def* map
- \+ *def* join
- \+ *def* bind
- \+ *def* lift_rel_o
- \+ *def* bisim_o
- \+ *def* lift_rel
- \+ *def* equiv
- \+ *def* lift_rel.refl
- \+ *def* lift_rel_o.swap
- \+ *def* lift_rel.swap_lem
- \+ *def* lift_rel.swap
- \+ *def* lift_rel.symm
- \+ *def* lift_rel.trans
- \+ *def* lift_rel.equiv
- \+ *def* join_nil
- \+ *def* join_think
- \+ *def* join_cons
- \+ *def* tail.aux
- \+ *def* drop.aux
- \+ *def* drop.aux_none
- \+ *def* to_seq
- \+ *def* of_mem_append
- \+ *def* mem_append_left
- \+ *def* lift_rel_nil
- \+ *def* lift_rel_cons
- \+ *def* lift_rel_think_left
- \+ *def* lift_rel_think_right
- \+ *def* of_list_nil
- \+ *def* of_list_cons
- \+ *def* to_list'_nil
- \+ *def* to_list'_cons
- \+ *def* to_list'_think
- \+ *def* to_list'_map
- \+ *def* to_list_cons
- \+ *def* to_list_nil
- \+ *def* ret
- \+ *def* destruct_append.aux
- \+ *def* destruct_join.aux

Created data/set/basic.lean
- \+ *lemma* ext
- \+ *lemma* subset.refl
- \+ *lemma* subset.trans
- \+ *lemma* subset.antisymm
- \+ *lemma* eq_of_subset_of_subset
- \+ *lemma* mem_of_subset_of_mem
- \+ *lemma* not_mem_empty
- \+ *lemma* mem_empty_eq
- \+ *lemma* eq_empty_of_forall_not_mem
- \+ *lemma* ne_empty_of_mem
- \+ *lemma* empty_subset
- \+ *lemma* eq_empty_of_subset_empty
- \+ *lemma* union_comm
- \+ *lemma* union_assoc
- \+ *lemma* union_self
- \+ *lemma* union_empty
- \+ *lemma* empty_union
- \+ *lemma* inter_comm
- \+ *lemma* inter_assoc
- \+ *lemma* inter_self
- \+ *lemma* inter_empty
- \+ *lemma* empty_inter

Created data/set/default.lean


Created data/set/finite.lean
- \+ *lemma* finite_insert
- \+ *lemma* finite_singleton
- \+ *lemma* finite_union
- \+ *lemma* finite_subset
- \+ *lemma* finite_image
- \+ *lemma* finite_sUnion

Created data/set/lattice.lean
- \+ *lemma* mem_set_of
- \+ *lemma* mem_set_of_eq
- \+ *lemma* nmem_set_of_eq
- \+ *lemma* set_of_false
- \+ *lemma* bounded_forall_empty_iff
- \+ *lemma* union_subset_iff
- \+ *lemma* ssubset_insert
- \+ *lemma* bounded_forall_insert_iff
- \+ *lemma* union_insert_eq
- \+ *lemma* singleton_subset_iff
- \+ *lemma* image_comp
- \+ *lemma* image_subset
- \+ *lemma* bounded_forall_image_of_bounded_forall
- \+ *lemma* bounded_forall_image_iff
- \+ *lemma* image_insert_eq
- \+ *lemma* union_sdiff_same
- \+ *lemma* union_same_compl
- \+ *lemma* sdiff_singleton_eq_same
- \+ *lemma* insert_sdiff_singleton
- \+ *lemma* vimage_empty
- \+ *lemma* mem_vimage_eq
- \+ *lemma* vimage_mono
- \+ *lemma* monotone_vimage
- \+ *lemma* vimage_image_eq
- \+ *lemma* vimage_univ
- \+ *lemma* vimage_inter
- \+ *lemma* vimage_union
- \+ *lemma* vimage_compl
- \+ *lemma* vimage_Union
- \+ *lemma* vimage_sUnion
- \+ *lemma* vimage_id
- \+ *lemma* vimage_comp
- \+ *lemma* eq_vimage_subtype_val_iff
- \+ *lemma* disjoint_symm
- \+ *lemma* disjoint_bot_left
- \+ *lemma* disjoint_bot_right
- \+ *theorem* set_eq_def
- \+ *theorem* subset_def
- \+ *theorem* union_def
- \+ *theorem* inter_def
- \+ *theorem* union_subset
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* ssubset_def
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* mem_univ
- \+ *theorem* mem_univ_iff
- \+ *theorem* mem_univ_eq
- \+ *theorem* empty_ne_univ
- \+ *theorem* univ_def
- \+ *theorem* subset_univ
- \+ *theorem* eq_univ_of_univ_subset
- \+ *theorem* eq_univ_of_forall
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* mem_unionl
- \+ *theorem* mem_unionr
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union.elim
- \+ *theorem* mem_union_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_eq_self_of_subset_left
- \+ *theorem* union_eq_self_of_subset_right
- \+ *theorem* union_subset_union
- \+ *theorem* mem_inter_iff
- \+ *theorem* mem_inter_eq
- \+ *theorem* mem_inter
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* nonempty_of_inter_nonempty_right
- \+ *theorem* nonempty_of_inter_nonempty_left
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_univ
- \+ *theorem* univ_inter
- \+ *theorem* inter_subset_inter_right
- \+ *theorem* inter_subset_inter
- \+ *theorem* inter_subset_inter_left
- \+ *theorem* inter_eq_self_of_subset_left
- \+ *theorem* inter_eq_self_of_subset_right
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* insert_def
- \+ *theorem* insert_of_has_insert
- \+ *theorem* subset_insert
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* insert_comm
- \+ *theorem* insert_ne_empty
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* forall_insert_of_forall
- \+ *theorem* singleton_def
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* singleton_eq_singleton_iff
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* insert_eq
- \+ *theorem* pair_eq_singleton
- \+ *theorem* singleton_ne_empty
- \+ *theorem* mem_sep
- \+ *theorem* mem_sep_eq
- \+ *theorem* mem_sep_iff
- \+ *theorem* eq_sep_of_subset
- \+ *theorem* sep_subset
- \+ *theorem* forall_not_of_sep_empty
- \+ *theorem* mem_compl
- \+ *theorem* not_mem_of_mem_compl
- \+ *theorem* mem_compl_eq
- \+ *theorem* mem_compl_iff
- \+ *theorem* inter_compl_self
- \+ *theorem* compl_inter_self
- \+ *theorem* compl_empty
- \+ *theorem* compl_union
- \+ *theorem* compl_compl
- \+ *theorem* compl_inter
- \+ *theorem* compl_univ
- \+ *theorem* union_eq_compl_compl_inter_compl
- \+ *theorem* inter_eq_compl_compl_union_compl
- \+ *theorem* union_compl_self
- \+ *theorem* compl_union_self
- \+ *theorem* compl_comp_compl
- \+ *theorem* diff_eq
- \+ *theorem* mem_diff
- \+ *theorem* mem_of_mem_diff
- \+ *theorem* not_mem_of_mem_diff
- \+ *theorem* mem_diff_iff
- \+ *theorem* mem_diff_eq
- \+ *theorem* union_diff_cancel
- \+ *theorem* diff_subset
- \+ *theorem* compl_eq_univ_diff
- \+ *theorem* mem_powerset
- \+ *theorem* subset_of_mem_powerset
- \+ *theorem* mem_powerset_iff
- \+ *theorem* mem_image_eq
- \+ *theorem* mem_image
- \+ *theorem* mem_image_of_mem
- \+ *theorem* mono_image
- \+ *theorem* image_subset_iff_subset_vimage
- \+ *theorem* image_eq_image_of_eq_on
- \+ *theorem* image_union
- \+ *theorem* image_empty
- \+ *theorem* fix_set_compl
- \+ *theorem* mem_image_compl
- \+ *theorem* image_id
- \+ *theorem* compl_compl_image
- \+ *theorem* mem_Union_eq
- \+ *theorem* mem_Inter_eq
- \+ *theorem* Union_subset
- \+ *theorem* Union_subset_iff
- \+ *theorem* mem_Inter
- \+ *theorem* subset_Inter
- \+ *theorem* compl_Union
- \+ *theorem* compl_Inter
- \+ *theorem* Union_eq_comp_Inter_comp
- \+ *theorem* Inter_eq_comp_Union_comp
- \+ *theorem* inter_distrib_Union_left
- \+ *theorem* union_distrib_Inter_left
- \+ *theorem* mem_bUnion
- \+ *theorem* mem_bInter
- \+ *theorem* bUnion_subset
- \+ *theorem* subset_bInter
- \+ *theorem* subset_bUnion_of_mem
- \+ *theorem* bInter_subset_of_mem
- \+ *theorem* bInter_empty
- \+ *theorem* bInter_univ
- \+ *theorem* bInter_singleton
- \+ *theorem* bInter_union
- \+ *theorem* bInter_insert
- \+ *theorem* bInter_pair
- \+ *theorem* bUnion_empty
- \+ *theorem* bUnion_univ
- \+ *theorem* bUnion_singleton
- \+ *theorem* bUnion_union
- \+ *theorem* bUnion_insert
- \+ *theorem* bUnion_pair
- \+ *theorem* mem_sUnion
- \+ *theorem* mem_sUnion_eq
- \+ *theorem* not_mem_of_not_mem_sUnion
- \+ *theorem* mem_sInter
- \+ *theorem* mem_sInter_eq
- \+ *theorem* sInter_subset_of_mem
- \+ *theorem* subset_sUnion_of_mem
- \+ *theorem* sUnion_subset
- \+ *theorem* sUnion_subset_iff
- \+ *theorem* subset_sInter
- \+ *theorem* sUnion_empty
- \+ *theorem* sInter_empty
- \+ *theorem* sUnion_singleton
- \+ *theorem* sInter_singleton
- \+ *theorem* sUnion_union
- \+ *theorem* sInter_union
- \+ *theorem* sUnion_insert
- \+ *theorem* sInter_insert
- \+ *theorem* sUnion_image
- \+ *theorem* sInter_image
- \+ *theorem* compl_sUnion
- \+ *theorem* sUnion_eq_compl_sInter_compl
- \+ *theorem* compl_sInter
- \+ *theorem* sInter_eq_comp_sUnion_compl
- \+ *theorem* inter_empty_of_inter_sUnion_empty
- \+ *theorem* Union_eq_sUnion_image
- \+ *theorem* Inter_eq_sInter_image
- \+ *def* strict_subset
- \+ *def* eq_on
- \+ *def* mem_image_elim
- \+ *def* mem_image_elim_on
- \+ *def* Union
- \+ *def* Inter
- \+ *def* sInter
- \+ *def* vimage
- \+ *def* pairwise_on
- \+ *def* disjoint

Created data/stream.lean
- \+ *lemma* nth_zero_cons
- \+ *lemma* head_cons
- \+ *lemma* tail_cons
- \+ *lemma* tail_drop
- \+ *lemma* nth_drop
- \+ *lemma* tail_eq_drop
- \+ *lemma* drop_drop
- \+ *lemma* nth_succ
- \+ *lemma* drop_succ
- \+ *lemma* all_def
- \+ *lemma* any_def
- \+ *lemma* mem_cons
- \+ *lemma* mem_cons_of_mem
- \+ *lemma* eq_or_mem_of_mem_cons
- \+ *lemma* mem_of_nth_eq
- \+ *lemma* drop_map
- \+ *lemma* nth_map
- \+ *lemma* tail_map
- \+ *lemma* head_map
- \+ *lemma* map_eq
- \+ *lemma* map_cons
- \+ *lemma* map_id
- \+ *lemma* map_map
- \+ *lemma* map_tail
- \+ *lemma* mem_map
- \+ *lemma* exists_of_mem_map
- \+ *lemma* drop_zip
- \+ *lemma* nth_zip
- \+ *lemma* head_zip
- \+ *lemma* tail_zip
- \+ *lemma* zip_eq
- \+ *lemma* mem_const
- \+ *lemma* const_eq
- \+ *lemma* tail_const
- \+ *lemma* map_const
- \+ *lemma* nth_const
- \+ *lemma* drop_const
- \+ *lemma* head_iterate
- \+ *lemma* tail_iterate
- \+ *lemma* iterate_eq
- \+ *lemma* nth_zero_iterate
- \+ *lemma* nth_succ_iterate
- \+ *lemma* bisim_simple
- \+ *lemma* coinduction
- \+ *lemma* iterate_id
- \+ *lemma* map_iterate
- \+ *lemma* corec_def
- \+ *lemma* corec_eq
- \+ *lemma* corec_id_id_eq_const
- \+ *lemma* corec_id_f_eq_iterate
- \+ *lemma* corec'_eq
- \+ *lemma* unfolds_eq
- \+ *lemma* nth_unfolds_head_tail
- \+ *lemma* unfolds_head_eq
- \+ *lemma* interleave_eq
- \+ *lemma* tail_interleave
- \+ *lemma* interleave_tail_tail
- \+ *lemma* nth_interleave_left
- \+ *lemma* nth_interleave_right
- \+ *lemma* mem_interleave_left
- \+ *lemma* mem_interleave_right
- \+ *lemma* odd_eq
- \+ *lemma* head_even
- \+ *lemma* tail_even
- \+ *lemma* even_cons_cons
- \+ *lemma* even_tail
- \+ *lemma* even_interleave
- \+ *lemma* interleave_even_odd
- \+ *lemma* nth_even
- \+ *lemma* nth_odd
- \+ *lemma* mem_of_mem_even
- \+ *lemma* mem_of_mem_odd
- \+ *lemma* nil_append_stream
- \+ *lemma* cons_append_stream
- \+ *lemma* append_append_stream
- \+ *lemma* map_append_stream
- \+ *lemma* drop_append_stream
- \+ *lemma* append_stream_head_tail
- \+ *lemma* mem_append_stream_right
- \+ *lemma* mem_append_stream_left
- \+ *lemma* approx_zero
- \+ *lemma* approx_succ
- \+ *lemma* nth_approx
- \+ *lemma* append_approx_drop
- \+ *lemma* take_lemma
- \+ *lemma* cycle_eq
- \+ *lemma* mem_cycle
- \+ *lemma* cycle_singleton
- \+ *lemma* tails_eq
- \+ *lemma* nth_tails
- \+ *lemma* tails_eq_iterate
- \+ *lemma* inits_core_eq
- \+ *lemma* tail_inits
- \+ *lemma* inits_tail
- \+ *lemma* cons_nth_inits_core
- \+ *lemma* nth_inits
- \+ *lemma* inits_eq
- \+ *lemma* zip_inits_tails
- \+ *lemma* identity
- \+ *lemma* composition
- \+ *lemma* homomorphism
- \+ *lemma* interchange
- \+ *lemma* map_eq_apply
- \+ *lemma* nth_nats
- \+ *lemma* nats_eq
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

Created data/vector.lean
- \+ *lemma* map_nil
- \+ *lemma* map_cons
- \+ *lemma* to_list_mk
- \+ *lemma* to_list_nil
- \+ *lemma* to_list_length
- \+ *lemma* to_list_cons
- \+ *lemma* to_list_append
- \+ *lemma* to_list_drop
- \+ *lemma* to_list_take
- \+ *theorem* head_cons
- \+ *theorem* tail_cons
- \+ *theorem* cons_head_tail
- \+ *def* vector
- \+ *def* nil
- \+ *def* cons
- \+ *def* length
- \+ *def* head
- \+ *def* tail
- \+ *def* to_list
- \+ *def* nth
- \+ *def* append
- \+ *def* elim
- \+ *def* map
- \+ *def* map₂
- \+ *def* repeat
- \+ *def* drop
- \+ *def* take
- \+ *def* remove_nth
- \+ *def* of_fn

Created leanpkg.toml


Created logic/basic.lean
- \+ *lemma* eq_iff_le_and_le
- \+ *lemma* prod.mk.inj_iff
- \+ *lemma* prod.forall
- \+ *lemma* prod.exists
- \+ *lemma* set_of_subset_set_of
- \+ *lemma* or_of_not_implies
- \+ *lemma* or_of_not_implies'
- \+ *lemma* not_imp_iff_not_imp
- \+ *lemma* or_imp_iff_and_imp
- \+ *lemma* forall_eq
- \+ *theorem* implies_self
- \+ *theorem* implies_intro
- \+ *theorem* implies_false_iff
- \+ *theorem* {u}
- \+ *theorem* not_not_of_not_implies
- \+ *theorem* not_of_not_implies
- \+ *theorem* dec_em
- \+ *theorem* by_contradiction
- \+ *theorem* not_not_iff
- \+ *theorem* not_not_elim
- \+ *theorem* of_not_implies
- \+ *theorem* not_and_of_not_left
- \+ *theorem* not_and_of_not_right
- \+ *theorem* and_implies_left
- \+ *theorem* and_implies_right
- \+ *theorem* and_of_and_of_implies_of_implies
- \+ *theorem* and_of_and_of_imp_left
- \+ *theorem* and_of_and_of_imp_right
- \+ *theorem* and_imp_iff
- \+ *theorem* and_not_self_iff
- \+ *theorem* not_and_self_iff
- \+ *theorem* or_of_or_of_implies_of_implies
- \+ *theorem* or_of_or_of_implies_left
- \+ *theorem* or_of_or_of_implies_right
- \+ *theorem* or.elim3
- \+ *theorem* or_resolve_right
- \+ *theorem* or_resolve_left
- \+ *theorem* or_implies_distrib
- \+ *theorem* or_iff_or
- \+ *theorem* and_distrib
- \+ *theorem* and_distrib_right
- \+ *theorem* or_distrib
- \+ *theorem* or_distrib_right
- \+ *theorem* implies_iff
- \+ *theorem* not_or_of_implies
- \+ *theorem* implies_of_not_or
- \+ *theorem* implies_iff_not_or
- \+ *theorem* not_implies_of_and_not
- \+ *theorem* and_not_of_not_implies
- \+ *theorem* not_implies_iff
- \+ *theorem* peirce
- \+ *theorem* peirce'
- \+ *theorem* not_and_of_not_or_not
- \+ *theorem* not_or_not_of_not_and
- \+ *theorem* not_or_not_of_not_and'
- \+ *theorem* not_and_iff
- \+ *theorem* not_or_of_not_and_not
- \+ *theorem* not_and_not_of_not_or
- \+ *theorem* not_or_iff
- \+ *theorem* or_iff_not_and_not
- \+ *theorem* and_iff_not_or_not
- \+ *theorem* forall_of_forall
- \+ *theorem* exists_of_exists
- \+ *theorem* forall_implies_of_exists_implies
- \+ *theorem* exists_implies_of_forall_implies
- \+ *theorem* exists_implies_distrib
- \+ *theorem* not_exists_of_forall_not
- \+ *theorem* not_exists_iff
- \+ *theorem* exists_not_of_not_forall
- \+ *theorem* not_forall_of_exists_not
- \+ *theorem* not_forall_iff
- \+ *theorem* forall_true_iff
- \+ *theorem* forall_p_iff_p
- \+ *theorem* exists_p_iff_p
- \+ *theorem* forall_and_distrib
- \+ *theorem* exists_or_distrib
- \+ *theorem* exists_and_distrib_left
- \+ *theorem* forall_or_distrib_left
- \+ *theorem* exists_prop_iff
- \+ *theorem* bexists.elim
- \+ *theorem* bexists.intro
- \+ *theorem* bforall_congr
- \+ *theorem* bexists_congr
- \+ *theorem* bforall_of_bforall
- \+ *theorem* bexists_of_bexists
- \+ *theorem* bforall_of_forall
- \+ *theorem* forall_of_bforall
- \+ *theorem* bexists_of_exists
- \+ *theorem* exists_of_bexists
- \+ *theorem* bforall_implies_of_bexists_implies
- \+ *theorem* bexists_implies_of_bforall_implies
- \+ *theorem* bexists_implies_distrib
- \+ *theorem* bforall_not_of_not_bexists
- \+ *theorem* not_bexists_of_bforall_not
- \+ *theorem* not_bexists_iff_bforall_not
- \+ *theorem* bexists_not_of_not_bforall
- \+ *theorem* not_bforall_of_bexists_not
- \+ *theorem* not_bforall_iff_bexists_not
- \+ *theorem* bforall_true_iff
- \+ *theorem* bforall_and_distrib
- \+ *theorem* bexists_or_distrib
- \- *theorem* forall_not_of_not_exists

Created pending/default.lean


Created theories/set_theory.lean
- \+ *def* arity
- \+ *def* Set
- \+ *def* Class

Created tools/auto/experiments/set_basic.lean
- \+ *lemma* mem_set_of
- \+ *lemma* bounded_forall_empty_iff
- \+ *lemma* bounded_forall_insert_iff
- \+ *lemma* image_comp
- \+ *lemma* image_subset
- \+ *lemma* bounded_forall_image_of_bounded_forall
- \+ *lemma* bounded_forall_image_iff
- \+ *lemma* image_insert_eq
- \+ *theorem* subset_def
- \+ *theorem* union_def
- \+ *theorem* inter_def
- \+ *theorem* union_subset
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* set_eq_def
- \+ *theorem* empty_def
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* mem_univ
- \+ *theorem* mem_univ_iff
- \+ *theorem* mem_univ_eq
- \+ *theorem* empty_ne_univ
- \+ *theorem* univ_def
- \+ *theorem* subset_univ
- \+ *theorem* eq_univ_of_univ_subset
- \+ *theorem* eq_univ_of_forall
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* mem_unionl
- \+ *theorem* mem_unionr
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union.elim
- \+ *theorem* mem_union_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_eq_self_of_subset_left
- \+ *theorem* union_eq_self_of_subset_right
- \+ *theorem* mem_inter_iff
- \+ *theorem* mem_inter_eq
- \+ *theorem* mem_inter
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* nonempty_of_inter_nonempty_right
- \+ *theorem* nonempty_of_inter_nonempty_left
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_left_comm'
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_univ
- \+ *theorem* univ_inter
- \+ *theorem* inter_subset_inter_right
- \+ *theorem* inter_subset_inter_left
- \+ *theorem* inter_eq_self_of_subset_left
- \+ *theorem* inter_eq_self_of_subset_right
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* insert_def
- \+ *theorem* subset_insert
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* insert_comm
- \+ *theorem* insert_ne_empty
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* forall_insert_of_forall
- \+ *theorem* singleton_def
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* insert_eq
- \+ *theorem* insert_of_has_insert
- \+ *theorem* pair_eq_singleton
- \+ *theorem* singleton_ne_empty
- \+ *theorem* mem_sep
- \+ *theorem* mem_sep_eq
- \+ *theorem* mem_sep_iff
- \+ *theorem* eq_sep_of_subset
- \+ *theorem* sep_subset
- \+ *theorem* forall_not_of_sep_empty
- \+ *theorem* mem_compl
- \+ *theorem* not_mem_of_mem_compl
- \+ *theorem* mem_compl_eq
- \+ *theorem* mem_compl_iff
- \+ *theorem* inter_compl_self
- \+ *theorem* compl_inter_self
- \+ *theorem* compl_empty
- \+ *theorem* compl_union
- \+ *theorem* compl_compl
- \+ *theorem* compl_inter
- \+ *theorem* compl_univ
- \+ *theorem* union_eq_compl_compl_inter_compl
- \+ *theorem* inter_eq_compl_compl_union_compl
- \+ *theorem* union_compl_self
- \+ *theorem* compl_union_self
- \+ *theorem* compl_comp_compl
- \+ *theorem* diff_eq
- \+ *theorem* mem_diff
- \+ *theorem* mem_of_mem_diff
- \+ *theorem* not_mem_of_mem_diff
- \+ *theorem* mem_diff_iff
- \+ *theorem* mem_diff_eq
- \+ *theorem* union_diff_cancel
- \+ *theorem* diff_subset
- \+ *theorem* compl_eq_univ_diff
- \+ *theorem* mem_powerset
- \+ *theorem* subset_of_mem_powerset
- \+ *theorem* mem_powerset_iff
- \+ *theorem* mem_image_eq
- \+ *theorem* mem_image
- \+ *theorem* mem_image_of_mem
- \+ *theorem* image_eq_image_of_eq_on
- \+ *theorem* image_union
- \+ *theorem* image_empty
- \+ *theorem* fix_set_compl
- \+ *theorem* mem_image_compl
- \+ *theorem* image_id
- \+ *theorem* compl_compl_image
- \+ *def* strict_subset
- \+ *def* eq_on
- \+ *def* mem_image_elim
- \+ *def* mem_image_elim_on

Created tools/auto/experiments/test1.lean


Created tools/auto/experiments/test2.lean
- \+ *lemma* NoMember

Created tools/auto/experiments/test3.lean
- \+ *theorem* foo:

Created tools/auto/finish.lean
- \+ *theorem* implies_and_iff
- \+ *theorem* curry_iff
- \+ *theorem* iff_def
- \+ *theorem* {u}
- \+ *theorem* by_contradiction_trick
- \+ *theorem* not_not_eq
- \+ *theorem* not_and_eq
- \+ *theorem* not_or_eq
- \+ *theorem* not_forall_eq
- \+ *theorem* not_exists_eq
- \+ *theorem* not_implies_eq
- \+ *theorem* classical.implies_iff_not_or
- \+ *def* common_normalize_lemma_names
- \+ *def* classical_normalize_lemma_names

Created tools/auto/mk_inhabitant.lean


Created tools/converter/binders.lean
- \+ *lemma* {u
- \+ *lemma* mem_image
- \+ *lemma* Inf_image
- \+ *lemma* Sup_image

Created tools/converter/interactive.lean


Created tools/converter/old_conv.lean


Created tools/parser/modal.lean
- \+ *def* varname
- \+ *def* size
- \+ *def* num_atoms
- \+ *def* atom
- \+ *def* unary_op
- \+ *def* binary_op
- \+ *def* strong_form_aux
- \+ *def* strong_form
- \+ *def* form_aux
- \+ *def* form
- \+ *def* form_of_string

Created tools/parser/parser.lean
- \+ *lemma* {u
- \+ *lemma* {u}
- \+ *def* parser
- \+ *def* parser_fmap
- \+ *def* parser_pure
- \+ *def* parser_bind
- \+ *def* list.deterministic_or
- \+ *def* parser_bignum
- \+ *def* parse
- \+ *def* item
- \+ *def* sat
- \+ *def* take_char
- \+ *def* take_string_aux
- \+ *def* take_string
- \+ *def* many_aux
- \+ *def* many
- \+ *def* many1
- \+ *def* sepby1
- \+ *def* sepby
- \+ *def* chainl1_rest
- \+ *def* chainl1
- \+ *def* chainl
- \+ *def* chainr1_rest
- \+ *def* chainr1
- \+ *def* chainr
- \+ *def* space
- \+ *def* token
- \+ *def* symb
- \+ *def* apply

Created tools/tactic/examples.lean
- \+ *lemma* mem_set_of
- \+ *theorem* subset_def
- \+ *theorem* union_def
- \+ *theorem* inter_def
- \+ *theorem* union_subset
- \+ *theorem* subset_inter
- \+ *def* my_id
- \+ *def* my_id_def

Created tools/tactic/tactic.lean


Created topology/continuity.lean
- \+ *lemma* univ_eq_true_false
- \+ *lemma* false_neq_true
- \+ *lemma* subtype.val_image
- \+ *lemma* continuous_id
- \+ *lemma* continuous_compose
- \+ *lemma* continuous_iff_towards
- \+ *lemma* continuous_iff_induced_le
- \+ *lemma* continuous_eq_le_coinduced
- \+ *lemma* continuous_generated_from
- \+ *lemma* continuous_induced_dom
- \+ *lemma* continuous_induced_rng
- \+ *lemma* continuous_coinduced_rng
- \+ *lemma* continuous_coinduced_dom
- \+ *lemma* continuous_inf_dom
- \+ *lemma* continuous_inf_rng_left
- \+ *lemma* continuous_inf_rng_right
- \+ *lemma* continuous_Inf_dom
- \+ *lemma* continuous_Inf_rng
- \+ *lemma* continuous_infi_dom
- \+ *lemma* continuous_infi_rng
- \+ *lemma* continuous_top
- \+ *lemma* continuous_bot
- \+ *lemma* continuous_sup_rng
- \+ *lemma* continuous_sup_dom_left
- \+ *lemma* continuous_sup_dom_right
- \+ *lemma* open_singleton_true
- \+ *lemma* continuous_Prop
- \+ *lemma* open_induced
- \+ *lemma* nhds_induced_eq_vmap
- \+ *lemma* map_nhds_induced_eq
- \+ *lemma* continuous_fst
- \+ *lemma* continuous_snd
- \+ *lemma* continuous_prod_mk
- \+ *lemma* open_set_prod
- \+ *lemma* prod_eq_generate_from
- \+ *lemma* nhds_prod_eq
- \+ *lemma* closure_prod_eq
- \+ *lemma* continuous_inl
- \+ *lemma* continuous_inr
- \+ *lemma* continuous_sum_rec
- \+ *lemma* continuous_subtype_val
- \+ *lemma* continuous_subtype_mk
- \+ *lemma* map_nhds_subtype_val_eq
- \+ *lemma* continuous_subtype_nhds_cover
- \+ *lemma* nhds_pi
- \+ *lemma* compact_pi_infinite
- \+ *theorem* classical.cases
- \+ *def* continuous

Created topology/topological_space.lean
- \+ *lemma* topological_space_eq
- \+ *lemma* open_univ
- \+ *lemma* open_inter
- \+ *lemma* open_sUnion
- \+ *lemma* open_Union
- \+ *lemma* open_empty
- \+ *lemma* closed_empty
- \+ *lemma* closed_univ
- \+ *lemma* closed_union
- \+ *lemma* closed_sInter
- \+ *lemma* closed_Inter
- \+ *lemma* closed_compl_iff_open
- \+ *lemma* open_compl_iff_closed
- \+ *lemma* open_diff
- \+ *lemma* open_interior
- \+ *lemma* interior_subset
- \+ *lemma* interior_maximal
- \+ *lemma* interior_eq_of_open
- \+ *lemma* interior_eq_iff_open
- \+ *lemma* subset_interior_iff_subset_of_open
- \+ *lemma* interior_mono
- \+ *lemma* interior_empty
- \+ *lemma* interior_univ
- \+ *lemma* interior_interior
- \+ *lemma* interior_inter
- \+ *lemma* interior_union_closed_of_interior_empty
- \+ *lemma* closed_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_minimal
- \+ *lemma* closure_eq_of_closed
- \+ *lemma* closure_eq_iff_closed
- \+ *lemma* closure_subset_iff_subset_of_closed
- \+ *lemma* closure_mono
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_closure
- \+ *lemma* closure_union
- \+ *lemma* interior_subset_closure
- \+ *lemma* closure_eq_compl_interior_compl
- \+ *lemma* interior_compl_eq
- \+ *lemma* closure_compl_eq
- \+ *lemma* nhds_sets
- \+ *lemma* map_nhds
- \+ *lemma* mem_nhds_sets_iff
- \+ *lemma* mem_nhds_sets
- \+ *lemma* return_le_nhds
- \+ *lemma* nhds_neq_bot
- \+ *lemma* interior_eq_nhds
- \+ *lemma* open_iff_nhds
- \+ *lemma* closure_eq_nhds
- \+ *lemma* closed_iff_nhds
- \+ *lemma* closed_Union_of_locally_finite
- \+ *lemma* compact_adherence_nhdset
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \+ *lemma* finite_subcover_of_compact
- \+ *lemma* eq_of_nhds_neq_bot
- \+ *lemma* nhds_generate_from
- \+ *lemma* t2_space_top
- \+ *lemma* le_of_nhds_le_nhds
- \+ *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* generate_from_le
- \+ *lemma* supr_eq_generate_from
- \+ *lemma* sup_eq_generate_from
- \+ *lemma* nhds_mono
- \+ *lemma* nhds_supr
- \+ *theorem* not_eq_empty_iff_exists
- \+ *def* open'
- \+ *def* closed
- \+ *def* interior
- \+ *def* closure
- \+ *def* nhds
- \+ *def* locally_finite
- \+ *def* compact
- \+ *def* generate_from
- \+ *def* topological_space.induced
- \+ *def* topological_space.coinduced

Created topology/uniform_space.lean
- \+ *lemma* swap_id_rel
- \+ *lemma* monotone_comp_rel
- \+ *lemma* prod_mk_mem_comp_rel
- \+ *lemma* id_comp_rel
- \+ *lemma* uniform_space_eq
- \+ *lemma* refl_le_uniformity
- \+ *lemma* refl_mem_uniformity
- \+ *lemma* symm_le_uniformity
- \+ *lemma* comp_le_uniformity
- \+ *lemma* comp_mem_uniformity_sets
- \+ *lemma* symm_of_uniformity
- \+ *lemma* comp_symm_of_uniformity
- \+ *lemma* uniformity_le_symm
- \+ *lemma* uniformity_eq_symm
- \+ *lemma* uniformity_lift_le_swap
- \+ *lemma* uniformity_lift_le_comp
- \+ *lemma* comp_le_uniformity3
- \+ *lemma* mem_nhds_uniformity_iff
- \+ *lemma* nhds_eq_uniformity
- \+ *lemma* mem_nhds_left
- \+ *lemma* mem_nhds_right
- \+ *lemma* lift_nhds_left
- \+ *lemma* lift_nhds_right
- \+ *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *lemma* nhds_eq_uniformity_prod
- \+ *lemma* nhdset_of_mem_uniformity
- \+ *lemma* closure_eq_inter_uniformity
- \+ *lemma* uniformity_eq_uniformity_closure
- \+ *lemma* uniformity_eq_uniformity_interior
- \+ *lemma* interior_mem_uniformity
- \+ *lemma* uniform_continuous_of_embedding
- \+ *lemma* continuous_of_uniform
- \+ *lemma* cauchy_downwards
- \+ *lemma* cauchy_nhds
- \+ *lemma* cauchy_pure
- \+ *lemma* le_nhds_of_cauchy_adhp
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *lemma* cauchy_map
- \+ *lemma* cauchy_vmap
- \+ *lemma* separated_equiv
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* totally_bounded_iff_filter
- \+ *lemma* totally_bounded_iff_ultrafilter
- \+ *lemma* compact_of_totally_bounded_complete
- \+ *lemma* complete_of_closed
- \+ *lemma* compact_of_totally_bounded_closed
- \+ *lemma* complete_space_extension
- \+ *lemma* uniform_continuous_quotient_mk
- \+ *lemma* vmap_quotient_le_uniformity
- \+ *lemma* complete_space_separation
- \+ *lemma* uniformly_extend_spec
- \+ *lemma* uniformly_extend_unique
- \+ *lemma* uniformly_extend_of_emb
- \+ *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* monotone_gen
- \+ *lemma* uniform_embedding_pure_cauchy
- \+ *lemma* pure_cauchy_dense
- \+ *lemma* uniform_continuous_vmap
- \+ *lemma* to_topological_space_vmap
- \+ *lemma* to_topological_space_mono
- \+ *lemma* supr_uniformity
- \+ *lemma* to_topological_space_top
- \+ *lemma* to_topological_space_bot
- \+ *lemma* to_topological_space_supr
- \+ *def* id_rel
- \+ *def* comp_rel
- \+ *def* uniformity
- \+ *def* uniform_continuous
- \+ *def* uniform_embedding
- \+ *def* cauchy
- \+ *def* separated
- \+ *def* totally_bounded
- \+ *def* Cauchy
- \+ *def* gen
- \+ *def* pure_cauchy
- \+ *def* uniform_space.vmap



## [2017-07-21 01:02:10-07:00](https://github.com/leanprover-community/mathlib/commit/21aca92)
Initial commit
#### Estimated changes

