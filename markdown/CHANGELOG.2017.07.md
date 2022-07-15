## [2017-07-30 00:50:04+01:00](https://github.com/leanprover-community/mathlib/commit/8f65496)
feat(data/fp): first pass at a floating point model
Hopefully this will be eventually moved to init so it can get a native representation.
#### Estimated changes
Added data/fp/basic.lean
- \+ *def* fp.div_nat_lt_two_pow
- \+ *def* fp.emax
- \+ *def* fp.emin
- \+ *def* fp.float.default_nan
- \+ *def* fp.float.is_finite
- \+ *theorem* fp.float.zero.valid
- \+ *def* fp.float.zero
- \+ *def* fp.prec
- \+ *def* fp.shift2
- \+ *def* fp.to_rat
- \+ *def* fp.valid_finite



## [2017-07-30 00:48:02+01:00](https://github.com/leanprover-community/mathlib/commit/bce43b3)
feat(data/rat): new rat representation using canonical elements
This yields better performance in long rational computations provided the numbers can be simplified.
#### Estimated changes
Modified algebra/group.lean


Modified data/int/basic.lean
- \+ *theorem* int.coe_nat_dvd_left
- \+ *theorem* int.coe_nat_dvd_right
- \+ *theorem* int.div_sign
- \+ *theorem* int.nat_abs_add_le
- \+ *theorem* int.nat_abs_mul
- \+ *theorem* int.nat_abs_neg_of_nat
- \+ *theorem* int.nat_succ_eq_int_succ
- \+ *theorem* int.neg_nat_succ
- \+ *theorem* int.neg_pred
- \+ *theorem* int.neg_succ
- \+ *theorem* int.neg_succ_of_nat_eq'
- \+ *def* int.pred
- \+ *theorem* int.pred_nat_succ
- \+ *theorem* int.pred_neg_pred
- \+ *theorem* int.pred_succ
- \+ *theorem* int.sign_mul
- \+ *def* int.succ
- \+ *theorem* int.succ_neg_nat_succ
- \+ *theorem* int.succ_neg_succ
- \+ *theorem* int.succ_pred

Modified data/nat/basic.lean


Modified data/nat/gcd.lean
- \- *theorem* nat.comprime_one_left
- \- *theorem* nat.comprime_one_right
- \+ *theorem* nat.coprime_one_left
- \+ *theorem* nat.coprime_one_right

Modified data/num/lemmas.lean


Modified data/rat.lean
- \+/\- *theorem* linear_order_cases_on_eq
- \+/\- *theorem* linear_order_cases_on_gt
- \+/\- *theorem* linear_order_cases_on_lt
- \- *theorem* not_antimono
- \+ *theorem* rat.add_def
- \+ *def* rat.ceil
- \+ *theorem* rat.div_mk_div_cancel_left
- \+ *def* rat.floor
- \+ *theorem* rat.inv_def
- \+ *theorem* rat.lift_binop_eq
- \+ *def* rat.mk
- \+ *theorem* rat.mk_eq
- \+ *theorem* rat.mk_eq_zero
- \+ *def* rat.mk_nat
- \+ *theorem* rat.mk_nat_eq
- \+ *theorem* rat.mk_nonneg
- \+ *def* rat.mk_pnat
- \+ *theorem* rat.mk_pnat_eq
- \+ *theorem* rat.mk_zero
- \+ *theorem* rat.mul_def
- \+ *theorem* rat.neg_def
- \+ *theorem* rat.nonneg_iff_zero_le
- \+ *theorem* rat.num_denom'
- \+ *theorem* rat.num_denom
- \+ *def* rat.of_int
- \+ *theorem* rat.zero_mk
- \+ *theorem* rat.zero_mk_nat
- \+ *theorem* rat.zero_mk_pnat
- \+ *theorem* rat.{u}
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
- \- *def* list.filter_map

Modified data/rat.lean


Modified pending/default.lean
- \- *theorem* nat.shiftl_succ
- \- *theorem* nat.shiftl_zero

Modified tactic/converter/binders.lean




## [2017-07-27 14:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/b37966e)
chore(.travis.yml): add Travis CI support
#### Estimated changes
Added .travis.yml


Modified README.md




## [2017-07-26 14:25:09+01:00](https://github.com/leanprover-community/mathlib/commit/b8ea20f)
fix(data): bitvec and vector are in the main repo
#### Estimated changes
Deleted data/bitvec.lean
- \- *def* bitvec.adc
- \- *def* bitvec.add_lsb
- \- *def* bitvec.and
- \- *def* bitvec.append
- \- *def* bitvec.bits_to_nat
- \- *theorem* bitvec.bits_to_nat_to_bool
- \- *theorem* bitvec.bits_to_nat_to_list
- \- *def* bitvec.fill_shr
- \- *def* bitvec.not
- \- *theorem* bitvec.of_nat_succ
- \- *def* bitvec.or
- \- *def* bitvec.sbb
- \- *def* bitvec.sborrow
- \- *def* bitvec.sge
- \- *def* bitvec.sgt
- \- *def* bitvec.shl
- \- *def* bitvec.sle
- \- *def* bitvec.slt
- \- *def* bitvec.sshr
- \- *theorem* bitvec.to_nat_append
- \- *theorem* bitvec.to_nat_of_nat
- \- *def* bitvec.uborrow
- \- *def* bitvec.uge
- \- *def* bitvec.ugt
- \- *def* bitvec.ule
- \- *def* bitvec.ult
- \- *def* bitvec.ushr
- \- *def* bitvec.xor
- \- *def* bitvec

Modified data/list/basic.lean
- \- *theorem* list.eq_nil_of_length_eq_zero
- \- *theorem* list.length_map₂
- \- *theorem* list.length_remove_nth
- \- *theorem* list.length_take
- \- *theorem* list.length_take_le
- \- *def* list.map₂
- \- *theorem* list.ne_nil_of_length_eq_succ
- \- *def* list.nth_le
- \- *def* list.remove_nth
- \- *def* list.update_nth

Modified data/list/comb.lean
- \- *theorem* list.length_map_accumr
- \- *theorem* list.length_map_accumr₂
- \- *def* list.map_accumr
- \- *def* list.map_accumr₂

Modified data/nat/basic.lean
- \- *theorem* nat.add_div_left
- \- *theorem* nat.add_div_right
- \- *theorem* nat.add_mod_left
- \- *theorem* nat.add_mod_right
- \- *theorem* nat.add_mul_div_left
- \- *theorem* nat.add_mul_div_right
- \- *theorem* nat.add_mul_mod_self_left
- \- *theorem* nat.add_mul_mod_self_right
- \- *theorem* nat.add_one_ne_zero
- \- *lemma* nat.binary_rec_eq
- \- *lemma* nat.bitwise_bit
- \- *lemma* nat.bitwise_bit_aux
- \- *theorem* nat.bitwise_swap
- \- *lemma* nat.bitwise_zero
- \- *lemma* nat.bitwise_zero_left
- \- *lemma* nat.bitwise_zero_right
- \- *lemma* nat.bodd_bit
- \- *theorem* nat.cond_to_bool_mod_two
- \- *theorem* nat.discriminate
- \- *lemma* nat.div2_bit
- \- *theorem* nat.div_mul_le_self
- \- *theorem* nat.dvd_antisymm
- \- *theorem* nat.dvd_iff_mod_eq_zero
- \- *theorem* nat.dvd_mod_iff
- \- *theorem* nat.dvd_of_mod_eq_zero
- \- *theorem* nat.dvd_of_mul_dvd_mul_left
- \- *theorem* nat.dvd_of_mul_dvd_mul_right
- \- *theorem* nat.dvd_sub
- \- *theorem* nat.eq_one_of_dvd_one
- \- *theorem* nat.eq_zero_of_add_eq_zero
- \- *theorem* nat.eq_zero_of_mul_eq_zero
- \- *theorem* nat.eq_zero_or_eq_succ_pred
- \- *theorem* nat.exists_eq_succ_of_ne_zero
- \- *def* nat.iterate
- \- *lemma* nat.land_bit
- \- *lemma* nat.ldiff_bit
- \- *theorem* nat.le_lt_antisymm
- \- *theorem* nat.le_mul_self
- \- *theorem* nat.le_of_dvd
- \- *theorem* nat.le_succ_of_pred_le
- \- *lemma* nat.lor_bit
- \- *theorem* nat.lt_le_antisymm
- \- *theorem* nat.lt_succ_of_lt
- \- *lemma* nat.lxor_bit
- \- *theorem* nat.min_succ_succ
- \- *theorem* nat.mod_eq_zero_of_dvd
- \- *theorem* nat.mod_le
- \- *theorem* nat.mod_pow_succ
- \- *theorem* nat.mul_div_left
- \- *theorem* nat.mul_div_right
- \- *theorem* nat.mul_mod_left
- \- *theorem* nat.mul_mod_mul_left
- \- *theorem* nat.mul_mod_mul_right
- \- *theorem* nat.mul_mod_right
- \- *theorem* nat.mul_pred_left
- \- *theorem* nat.mul_pred_right
- \- *theorem* nat.mul_self_le_mul_self
- \- *theorem* nat.mul_self_le_mul_self_iff
- \- *theorem* nat.mul_self_lt_mul_self
- \- *theorem* nat.mul_self_lt_mul_self_iff
- \- *theorem* nat.mul_sub_div
- \- *theorem* nat.one_add
- \- *def* nat.one_pos
- \- *lemma* nat.one_shiftl
- \- *theorem* nat.one_succ_zero
- \- *theorem* nat.pos_of_dvd_of_pos
- \- *theorem* nat.pos_pow_of_pos
- \- *theorem* nat.pow_le_pow_of_le_left
- \- *theorem* nat.pow_le_pow_of_le_right
- \- *theorem* nat.pow_lt_pow_of_lt_left
- \- *theorem* nat.pow_lt_pow_of_lt_right
- \- *theorem* nat.pow_one
- \- *theorem* nat.pred_inj
- \- *lemma* nat.shiftl'_add
- \- *lemma* nat.shiftl'_sub
- \- *lemma* nat.shiftl'_tt_eq_mul_pow
- \- *lemma* nat.shiftl_add
- \- *lemma* nat.shiftl_eq_mul_pow
- \- *lemma* nat.shiftl_sub
- \- *lemma* nat.shiftr_add
- \- *lemma* nat.shiftr_eq_div_pow
- \- *theorem* nat.sub_add_min_cancel
- \- *theorem* nat.sub_eq_sub_min
- \- *theorem* nat.sub_induction
- \- *theorem* nat.sub_mul_div
- \- *theorem* nat.sub_mul_mod
- \- *theorem* nat.sub_one_sub_lt
- \- *theorem* nat.succ_add_eq_succ_add
- \- *theorem* nat.succ_inj
- \- *theorem* nat.succ_mul_succ_eq
- \- *theorem* nat.succ_sub
- \- *theorem* nat.succ_sub_sub_succ
- \- *lemma* nat.test_bit_bitwise
- \- *lemma* nat.test_bit_land
- \- *lemma* nat.test_bit_ldiff
- \- *lemma* nat.test_bit_lor
- \- *lemma* nat.test_bit_lxor
- \- *lemma* nat.test_bit_succ
- \- *lemma* nat.test_bit_zero
- \- *theorem* nat.two_step_induction
- \- *theorem* nat.zero_pow
- \- *lemma* nat.zero_shiftl
- \- *lemma* nat.zero_shiftr

Modified data/num/basic.lean


Deleted data/vector.lean
- \- *def* vector.append
- \- *def* vector.cons
- \- *theorem* vector.cons_head_tail
- \- *def* vector.drop
- \- *def* vector.elim
- \- *def* vector.head
- \- *theorem* vector.head_cons
- \- *def* vector.length
- \- *def* vector.map
- \- *def* vector.map_accumr
- \- *def* vector.map_accumr₂
- \- *theorem* vector.map_cons
- \- *theorem* vector.map_nil
- \- *def* vector.map₂
- \- *def* vector.nil
- \- *def* vector.nth
- \- *def* vector.of_fn
- \- *def* vector.remove_nth
- \- *def* vector.repeat
- \- *def* vector.tail
- \- *theorem* vector.tail_cons
- \- *def* vector.take
- \- *def* vector.to_list
- \- *theorem* vector.to_list_append
- \- *theorem* vector.to_list_cons
- \- *theorem* vector.to_list_drop
- \- *theorem* vector.to_list_length
- \- *theorem* vector.to_list_mk
- \- *theorem* vector.to_list_nil
- \- *theorem* vector.to_list_take
- \- *def* vector



## [2017-07-25 13:51:39+01:00](https://github.com/leanprover-community/mathlib/commit/9451087)
refactor(*): move in list lemmas, adapt to change in list.union
#### Estimated changes
Modified data/hash_map.lean
- \+ *theorem* hash_map.insert_lemma
- \- *theorem* hash_map.insert_theorem

Modified data/list/basic.lean
- \+ *def* list.concat
- \+ *lemma* list.concat_eq_append
- \+ *def* list.filter_map
- \+ *def* list.find
- \+ *def* list.find_indexes
- \+ *def* list.find_indexes_aux
- \+ *theorem* list.index_of_cons_eq
- \+ *theorem* list.index_of_cons_ne
- \- *theorem* list.index_of_cons_of_eq
- \- *theorem* list.index_of_cons_of_ne
- \+ *theorem* list.index_of_cons_self
- \+ *theorem* list.index_of_eq_length
- \+/\- *theorem* list.index_of_lt_length
- \+/\- *theorem* list.index_of_nth
- \+ *theorem* list.index_of_nth_le
- \+/\- *theorem* list.index_of_of_not_mem
- \+ *def* list.indexes_of
- \+ *def* list.inits
- \+ *def* list.is_infix
- \+ *def* list.is_prefix
- \+ *def* list.is_suffix
- \+ *lemma* list.length_concat
- \+ *lemma* list.map_concat
- \+ *def* list.map₂
- \- *theorem* list.mem_append_of_mem_or_mem
- \- *theorem* list.mem_or_mem_of_mem_append
- \+/\- *theorem* list.mem_split
- \+/\- *theorem* list.not_mem_append
- \- *theorem* list.not_mem_of_index_of_eq_length
- \- *theorem* list.not_mem_of_not_mem_append_left
- \- *theorem* list.not_mem_of_not_mem_append_right
- \+ *def* list.nth_le
- \+ *def* list.remove_nth
- \+ *def* list.scanl
- \+ *def* list.scanr
- \+ *def* list.scanr_aux
- \+ *def* list.split_at
- \+/\- *theorem* list.sublist.refl
- \+/\- *theorem* list.sublist.trans
- \+ *def* list.sublists
- \+ *def* list.sublists_aux
- \+ *def* list.sum
- \+ *def* list.tails
- \+ *def* list.take_while
- \+ *def* list.to_array
- \+ *def* list.transpose
- \+ *def* list.transpose_aux
- \+ *def* list.update_nth

Modified data/list/comb.lean


Modified data/list/perm.lean
- \+/\- *theorem* list.perm.perm_insert
- \+/\- *theorem* list.perm.perm_insert_insert

Modified data/list/set.lean
- \+ *theorem* list.cons_union
- \- *theorem* list.disjoint.comm
- \+ *theorem* list.disjoint.symm
- \+ *theorem* list.disjoint_comm
- \- *theorem* list.disjoint_nil_right
- \+ *theorem* list.disjoint_singleton
- \- *theorem* list.erase_cons
- \+/\- *theorem* list.erase_dup_cons_of_mem
- \+/\- *theorem* list.erase_dup_cons_of_not_mem
- \+/\- *theorem* list.erase_dup_eq_of_nodup
- \+/\- *theorem* list.erase_dup_nil
- \+/\- *theorem* list.erase_nil
- \+/\- *theorem* list.insert.def
- \+/\- *theorem* list.insert_of_not_mem
- \+/\- *theorem* list.mem_erase_dup
- \- *theorem* list.mem_erase_dup_iff
- \+/\- *theorem* list.mem_insert_iff
- \- *theorem* list.mem_of_mem_erase_dup
- \+/\- *theorem* list.mem_or_mem_of_mem_union
- \+/\- *theorem* list.mem_union_iff
- \+ *theorem* list.nil_union
- \+ *theorem* list.nodup_append
- \- *theorem* list.nodup_append_of_nodup_of_nodup_of_disjoint
- \+ *theorem* list.nodup_union
- \- *theorem* list.nodup_union_of_nodup_of_nodup
- \+ *theorem* list.singleton_disjoint
- \- *theorem* list.union_cons
- \- *theorem* list.union_nil

Modified data/set/basic.lean
- \+/\- *theorem* set.mem_empty_eq
- \+/\- *theorem* set.mem_image_eq
- \+/\- *theorem* set.mem_sep_eq

Modified logic/basic.lean
- \+/\- *theorem* set_of_subset_set_of

Modified tactic/finish.lean




## [2017-07-24 00:42:20+01:00](https://github.com/leanprover-community/mathlib/commit/aa78466)
refactor(*): move in some nat lemmas
and other lemmas from init
#### Estimated changes
Added data/array/lemmas.lean
- \+ *theorem* array.mem_iff_list_mem
- \+ *theorem* array.mem_iff_rev_list_mem
- \+ *theorem* array.mem_iff_rev_list_mem_core
- \+ *theorem* array.push_back_rev_list
- \+ *lemma* array.push_back_rev_list_core
- \+ *theorem* array.push_back_to_list
- \+ *def* array.read_foreach
- \+ *def* array.read_foreach_aux
- \+ *def* array.read_map
- \+ *def* array.read_map₂
- \+ *lemma* array.read_write
- \+ *lemma* array.read_write_eq
- \+ *lemma* array.read_write_ne
- \+ *theorem* array.rev_list_length
- \+ *theorem* array.rev_list_length_aux
- \+ *theorem* array.rev_list_reverse
- \+ *theorem* array.rev_list_reverse_core
- \+ *theorem* array.to_array_to_list
- \+ *theorem* array.to_list_length
- \+ *theorem* array.to_list_nth
- \+ *theorem* array.to_list_nth_core
- \+ *theorem* array.to_list_reverse
- \+ *theorem* array.to_list_to_array

Modified data/bitvec.lean


Modified data/fin.lean
- \- *theorem* lt_succ_of_lt

Modified data/hash_map.lean


Modified data/int/basic.lean
- \+ *theorem* int.abs_div_le_abs
- \+ *theorem* int.add_mod_eq_add_mod_left
- \+ *theorem* int.add_mod_eq_add_mod_right
- \+ *theorem* int.add_mod_mod
- \+ *theorem* int.add_mod_self
- \+ *theorem* int.add_mod_self_left
- \+ *theorem* int.add_mul_mod_self
- \+ *theorem* int.add_mul_mod_self_left
- \+ *lemma* int.bit0_val
- \+ *lemma* int.bit1_val
- \+ *lemma* int.bit_coe_nat
- \+ *lemma* int.bit_decomp
- \+ *lemma* int.bit_neg_succ
- \+ *lemma* int.bit_val
- \+ *lemma* int.bit_zero
- \+ *theorem* int.bitwise_and
- \+ *lemma* int.bitwise_bit
- \+ *theorem* int.bitwise_diff
- \+ *theorem* int.bitwise_or
- \+ *theorem* int.bitwise_xor
- \+ *lemma* int.bodd_add
- \+ *theorem* int.bodd_add_div2
- \+ *lemma* int.bodd_bit
- \+ *lemma* int.bodd_mul
- \+ *lemma* int.bodd_neg
- \+ *lemma* int.bodd_neg_of_nat
- \+ *lemma* int.bodd_one
- \+ *lemma* int.bodd_sub_nat_nat
- \+ *lemma* int.bodd_two
- \+ *lemma* int.bodd_zero
- \+ *theorem* int.coe_nat_dvd_coe_nat_iff
- \+ *theorem* int.coe_nat_dvd_coe_nat_of_dvd
- \+ *lemma* int.div2_bit
- \+ *theorem* int.div2_val
- \+ *theorem* int.div_dvd_div
- \+ *theorem* int.div_eq_div_of_mul_eq_mul
- \+ *theorem* int.div_eq_zero_of_lt
- \+ *theorem* int.div_eq_zero_of_lt_abs
- \+ *theorem* int.div_le_self
- \+ *theorem* int.div_mul_cancel_of_mod_eq_zero
- \+ *theorem* int.div_neg'
- \+ *theorem* int.div_of_neg_of_pos
- \+ *theorem* int.div_pos_of_pos_of_dvd
- \+ *theorem* int.dvd_antisymm
- \+ *theorem* int.dvd_iff_mod_eq_zero
- \+ *theorem* int.dvd_of_coe_nat_dvd_coe_nat
- \+ *theorem* int.dvd_of_mod_eq_zero
- \+ *theorem* int.eq_one_of_dvd_one
- \+ *theorem* int.eq_one_of_mul_eq_one_left
- \+ *theorem* int.eq_one_of_mul_eq_one_right
- \+ *lemma* int.land_bit
- \+ *lemma* int.ldiff_bit
- \+ *theorem* int.le_of_dvd
- \+ *lemma* int.lnot_bit
- \+ *lemma* int.lor_bit
- \+ *theorem* int.lt_div_add_one_mul_self
- \+ *lemma* int.lxor_bit
- \+ *theorem* int.mod_abs
- \+ *theorem* int.mod_add_div
- \+ *theorem* int.mod_add_div_aux
- \+ *theorem* int.mod_add_mod
- \+ *theorem* int.mod_def
- \+ *theorem* int.mod_eq_mod_of_add_mod_eq_add_mod_left
- \+ *theorem* int.mod_eq_mod_of_add_mod_eq_add_mod_right
- \+ *theorem* int.mod_eq_of_lt
- \+ *theorem* int.mod_eq_zero_of_dvd
- \+ *theorem* int.mod_lt
- \+ *theorem* int.mod_lt_of_pos
- \+ *theorem* int.mod_neg
- \+ *theorem* int.mod_nonneg
- \+ *theorem* int.mod_one
- \+ *theorem* int.mod_self
- \+ *theorem* int.mod_zero
- \+ *theorem* int.mul_div_cancel_of_mod_eq_zero
- \+ *theorem* int.mul_div_mul_of_pos
- \+ *theorem* int.mul_div_mul_of_pos_left
- \+ *theorem* int.mul_mod_left
- \+ *theorem* int.mul_mod_mul_of_pos
- \+ *theorem* int.mul_mod_right
- \+ *theorem* int.neg_div_of_dvd
- \+ *theorem* int.neg_succ_of_nat_div
- \+ *theorem* int.neg_succ_of_nat_mod
- \+ *theorem* int.of_nat_div
- \+ *theorem* int.of_nat_mod
- \+ *lemma* int.one_shiftl
- \+ *lemma* int.shiftl_add
- \+ *lemma* int.shiftl_coe_nat
- \+ *lemma* int.shiftl_eq_mul_pow
- \+ *lemma* int.shiftl_neg
- \+ *lemma* int.shiftl_neg_succ
- \+ *lemma* int.shiftl_sub
- \+ *lemma* int.shiftr_add
- \+ *lemma* int.shiftr_coe_nat
- \+ *lemma* int.shiftr_eq_div_pow
- \+ *lemma* int.shiftr_neg
- \+ *lemma* int.shiftr_neg_succ
- \+ *lemma* int.test_bit_bitwise
- \+ *lemma* int.test_bit_land
- \+ *lemma* int.test_bit_ldiff
- \+ *lemma* int.test_bit_lnot
- \+ *lemma* int.test_bit_lor
- \+ *lemma* int.test_bit_lxor
- \+ *lemma* int.test_bit_succ
- \+ *lemma* int.test_bit_zero
- \+ *theorem* int.zero_mod
- \+ *lemma* int.zero_shiftl
- \+ *lemma* int.zero_shiftr
- \+ *def* int.{u}
- \- *def* nat_succ_eq_int_succ
- \- *theorem* neg_nat_succ
- \- *theorem* neg_pred
- \- *theorem* neg_succ
- \- *theorem* neg_succ_of_nat_eq'
- \- *theorem* of_nat_sub
- \- *def* pred
- \- *theorem* pred_nat_succ
- \- *theorem* pred_neg_pred
- \- *theorem* pred_succ
- \- *def* rec_nat_on
- \- *theorem* rec_nat_on_neg
- \- *def* succ
- \- *theorem* succ_neg_nat_succ
- \- *theorem* succ_neg_succ
- \- *theorem* succ_pred

Modified data/int/order.lean
- \+ *theorem* int.exists_greatest_of_bdd
- \+ *theorem* int.exists_least_of_bdd

Modified data/list/basic.lean
- \+ *theorem* list.app_subset_of_subset_of_subset
- \- *theorem* list.append.assoc
- \+ *theorem* list.append_foldl
- \+ *theorem* list.append_foldr
- \+ *theorem* list.append_inj
- \+ *theorem* list.append_inj_left
- \+ *theorem* list.append_inj_right
- \+ *theorem* list.append_ne_nil_of_ne_nil_left
- \+ *theorem* list.append_ne_nil_of_ne_nil_right
- \+ *theorem* list.append_right_inj
- \+ *theorem* list.concat_eq_reverse_cons
- \+ *theorem* list.cons_head_tail
- \+/\- *theorem* list.cons_ne_nil
- \+ *theorem* list.cons_sublist_cons
- \+ *theorem* list.cons_subset_of_subset_of_mem
- \+ *theorem* list.eq_nil_of_forall_not_mem
- \+ *lemma* list.eq_nil_of_infix_nil
- \+ *theorem* list.eq_nil_of_length_eq_zero
- \+ *theorem* list.eq_nil_of_map_eq_nil
- \+ *lemma* list.eq_nil_of_prefix_nil
- \+ *theorem* list.eq_nil_of_sublist_nil
- \+ *theorem* list.eq_nil_of_subset_nil
- \+ *lemma* list.eq_nil_of_suffix_nil
- \+ *theorem* list.eq_of_map_const
- \+ *lemma* list.exists_of_mem_bind
- \+ *theorem* list.exists_of_mem_join
- \+ *theorem* list.exists_of_mem_map
- \+ *theorem* list.ext
- \+ *theorem* list.ext_le
- \+ *theorem* list.filter_subset
- \+ *theorem* list.foldl_hom
- \+ *theorem* list.foldl_map
- \+ *lemma* list.foldr_eta
- \+ *theorem* list.foldr_hom
- \+ *theorem* list.foldr_map
- \+ *theorem* list.head_append
- \+ *lemma* list.infix_append
- \+ *lemma* list.infix_iff_prefix_suffix
- \+ *lemma* list.infix_of_prefix
- \+ *lemma* list.infix_of_suffix
- \+ *lemma* list.infix_refl
- \+/\- *def* list.inth
- \- *theorem* list.inth_succ
- \- *theorem* list.inth_zero
- \- *def* list.ith
- \- *theorem* list.ith_succ
- \- *theorem* list.ith_zero
- \+ *theorem* list.last_append
- \+ *theorem* list.last_concat
- \+ *theorem* list.last_cons
- \+ *lemma* list.length_le_of_infix
- \+ *theorem* list.length_map₂
- \+ *theorem* list.length_pos_of_mem
- \+ *theorem* list.length_remove_nth
- \+ *theorem* list.length_reverse
- \+ *theorem* list.length_take
- \+ *theorem* list.length_take_le
- \- *theorem* list.length_taken_le
- \+ *theorem* list.map_id'
- \+ *theorem* list.map_reverse
- \+ *theorem* list.mem_append_of_mem_or_mem
- \+ *lemma* list.mem_bind
- \+ *lemma* list.mem_bind_iff
- \+ *theorem* list.mem_filter_of_mem
- \+ *lemma* list.mem_inits
- \+ *theorem* list.mem_join
- \+ *theorem* list.mem_join_iff
- \+ *theorem* list.mem_map
- \+ *theorem* list.mem_map_iff
- \+ *theorem* list.mem_of_mem_cons_of_mem
- \+ *theorem* list.mem_of_mem_filter
- \+ *theorem* list.mem_of_ne_of_mem
- \+ *theorem* list.mem_or_mem_of_mem_append
- \+ *theorem* list.mem_reverse
- \+ *theorem* list.mem_singleton
- \+ *theorem* list.mem_singleton_iff
- \+ *theorem* list.mem_split
- \+ *lemma* list.mem_sublists
- \+ *lemma* list.mem_tails
- \+ *theorem* list.ne_and_not_mem_of_not_mem_cons
- \+ *theorem* list.ne_nil_of_length_eq_succ
- \+ *theorem* list.ne_of_not_mem_cons
- \+ *theorem* list.nil_sublist
- \+ *theorem* list.not_mem_append
- \+ *theorem* list.not_mem_cons_of_ne_of_not_mem
- \+ *theorem* list.not_mem_of_not_mem_append_left
- \+ *theorem* list.not_mem_of_not_mem_append_right
- \+ *theorem* list.not_mem_of_not_mem_cons
- \- *theorem* list.nth_eq_some
- \+ *theorem* list.nth_ge_len
- \+ *theorem* list.nth_le_nth
- \+ *theorem* list.nth_le_reverse
- \+ *theorem* list.nth_le_reverse_aux1
- \+ *theorem* list.nth_le_reverse_aux2
- \+ *theorem* list.of_mem_filter
- \+ *lemma* list.prefix_append
- \+ *lemma* list.prefix_refl
- \+ *theorem* list.reverse_append
- \+ *theorem* list.reverse_cons
- \+ *theorem* list.reverse_nil
- \+ *theorem* list.reverse_reverse
- \+ *theorem* list.reverse_singleton
- \+ *lemma* list.scanr_aux_cons
- \+ *lemma* list.scanr_cons
- \+ *lemma* list.scanr_nil
- \+ *lemma* list.span_eq_take_drop
- \+ *theorem* list.split_at_eq_take_drop
- \+ *theorem* list.sublist.refl
- \+ *theorem* list.sublist.trans
- \+ *theorem* list.sublist_app_of_sublist_left
- \+ *theorem* list.sublist_app_of_sublist_right
- \+ *theorem* list.sublist_append_left
- \+ *theorem* list.sublist_append_right
- \+ *theorem* list.sublist_cons
- \+ *theorem* list.sublist_cons_of_sublist
- \+ *theorem* list.sublist_of_cons_sublist
- \+ *theorem* list.sublist_of_cons_sublist_cons
- \+ *lemma* list.sublist_of_infix
- \+ *lemma* list.sublists_aux_cons_cons
- \+ *lemma* list.sublists_aux_eq_foldl
- \+ *theorem* list.subset_app_of_subset_left
- \+ *theorem* list.subset_app_of_subset_right
- \+ *theorem* list.subset_of_sublist
- \+ *lemma* list.suffix_append
- \+ *lemma* list.suffix_refl
- \+ *theorem* list.take_all
- \+ *theorem* list.take_all_of_ge
- \+ *theorem* list.take_append_drop
- \+ *theorem* list.take_cons
- \+ *theorem* list.take_nil
- \+ *theorem* list.take_take
- \+ *lemma* list.take_while_append_drop
- \+ *theorem* list.take_zero
- \- *theorem* list.taken_all
- \- *theorem* list.taken_all_of_ge
- \- *theorem* list.taken_cons
- \- *theorem* list.taken_nil
- \- *theorem* list.taken_zero

Modified data/list/perm.lean


Modified data/nat/basic.lean
- \- *def* iterate
- \+ *theorem* nat.add_div_left
- \+ *theorem* nat.add_div_right
- \+ *theorem* nat.add_mod_left
- \+ *theorem* nat.add_mod_right
- \+ *theorem* nat.add_mul_div_left
- \+ *theorem* nat.add_mul_div_right
- \+ *theorem* nat.add_mul_mod_self_left
- \+ *theorem* nat.add_mul_mod_self_right
- \- *theorem* nat.add_one
- \+ *lemma* nat.binary_rec_eq
- \+ *lemma* nat.bitwise_bit
- \+ *lemma* nat.bitwise_bit_aux
- \+ *theorem* nat.bitwise_swap
- \+ *lemma* nat.bitwise_zero
- \+ *lemma* nat.bitwise_zero_left
- \+ *lemma* nat.bitwise_zero_right
- \+ *lemma* nat.bodd_bit
- \+ *theorem* nat.cond_to_bool_mod_two
- \+/\- *theorem* nat.discriminate
- \+ *lemma* nat.div2_bit
- \+ *theorem* nat.div_mul_le_self
- \+ *theorem* nat.dvd_antisymm
- \+ *theorem* nat.dvd_iff_mod_eq_zero
- \+ *theorem* nat.dvd_mod_iff
- \+ *theorem* nat.dvd_of_mod_eq_zero
- \+ *theorem* nat.dvd_of_mul_dvd_mul_left
- \+ *theorem* nat.dvd_of_mul_dvd_mul_right
- \+ *theorem* nat.dvd_sub
- \+ *theorem* nat.eq_one_of_dvd_one
- \+ *theorem* nat.eq_zero_of_mul_eq_zero
- \+ *def* nat.iterate
- \+ *lemma* nat.land_bit
- \+ *lemma* nat.ldiff_bit
- \+ *theorem* nat.le_lt_antisymm
- \+ *theorem* nat.le_mul_self
- \+ *theorem* nat.le_of_dvd
- \+ *theorem* nat.le_succ_of_pred_le
- \+ *lemma* nat.lor_bit
- \+ *theorem* nat.lt_le_antisymm
- \+ *theorem* nat.lt_succ_of_lt
- \+ *lemma* nat.lxor_bit
- \+ *theorem* nat.min_succ_succ
- \+ *theorem* nat.mod_eq_zero_of_dvd
- \+ *theorem* nat.mod_le
- \+ *theorem* nat.mod_pow_succ
- \+ *theorem* nat.mul_div_left
- \+ *theorem* nat.mul_div_right
- \+ *theorem* nat.mul_mod_left
- \+ *theorem* nat.mul_mod_mul_left
- \+ *theorem* nat.mul_mod_mul_right
- \+ *theorem* nat.mul_mod_right
- \+ *theorem* nat.mul_pred_left
- \+ *theorem* nat.mul_pred_right
- \+ *theorem* nat.mul_self_le_mul_self
- \+ *theorem* nat.mul_self_le_mul_self_iff
- \+ *theorem* nat.mul_self_lt_mul_self
- \+ *theorem* nat.mul_self_lt_mul_self_iff
- \+ *theorem* nat.mul_sub_div
- \+ *def* nat.one_pos
- \+ *lemma* nat.one_shiftl
- \+ *theorem* nat.pos_of_dvd_of_pos
- \+ *theorem* nat.pos_pow_of_pos
- \+ *theorem* nat.pow_le_pow_of_le_left
- \+ *theorem* nat.pow_le_pow_of_le_right
- \+ *theorem* nat.pow_lt_pow_of_lt_left
- \+ *theorem* nat.pow_lt_pow_of_lt_right
- \+ *theorem* nat.pow_one
- \+ *theorem* nat.pred_inj
- \+ *lemma* nat.shiftl'_add
- \+ *lemma* nat.shiftl'_sub
- \+ *lemma* nat.shiftl'_tt_eq_mul_pow
- \+ *lemma* nat.shiftl_add
- \+ *lemma* nat.shiftl_eq_mul_pow
- \+ *lemma* nat.shiftl_sub
- \+ *lemma* nat.shiftr_add
- \+ *lemma* nat.shiftr_eq_div_pow
- \+ *theorem* nat.sub_add_min_cancel
- \+ *theorem* nat.sub_eq_sub_min
- \+ *theorem* nat.sub_mul_div
- \+ *theorem* nat.sub_mul_mod
- \+ *theorem* nat.sub_one_sub_lt
- \+ *theorem* nat.succ_mul_succ_eq
- \+ *theorem* nat.succ_sub
- \+ *theorem* nat.succ_sub_sub_succ
- \+ *lemma* nat.test_bit_bitwise
- \+ *lemma* nat.test_bit_land
- \+ *lemma* nat.test_bit_ldiff
- \+ *lemma* nat.test_bit_lor
- \+ *lemma* nat.test_bit_lxor
- \+ *lemma* nat.test_bit_succ
- \+ *lemma* nat.test_bit_zero
- \+ *theorem* nat.zero_pow
- \+ *lemma* nat.zero_shiftl
- \+ *lemma* nat.zero_shiftr

Modified data/nat/gcd.lean


Modified data/nat/sub.lean


Added data/option.lean
- \+ *def* option.iget

Modified data/seq/computation.lean


Modified data/seq/wseq.lean


Modified data/stream.lean




## [2017-07-23 19:02:57+01:00](https://github.com/leanprover-community/mathlib/commit/1b6322f)
chore(*): rfl-lemmas on same line
#### Estimated changes
Modified algebra/group.lean


Modified algebra/lattice/filter.lean
- \+/\- *theorem* filter.join_principal_eq_Sup
- \+/\- *theorem* filter.mem_join_sets
- \+/\- *theorem* filter.mem_principal_sets
- \+/\- *theorem* filter.principal_empty
- \+/\- *theorem* filter.principal_univ
- \+/\- *theorem* set.fmap_eq_image
- \+/\- *theorem* set.set_of_mem_eq

Modified algebra/order.lean


Modified data/bool.lean
- \+/\- *theorem* bool.bnot_false
- \+/\- *theorem* bool.bnot_true
- \+/\- *theorem* bool.cond_ff
- \+/\- *theorem* bool.cond_tt

Modified data/list/basic.lean
- \+/\- *theorem* list.count_nil
- \+/\- *theorem* list.head_cons
- \+/\- *theorem* list.index_of_cons
- \+/\- *theorem* list.index_of_nil
- \+/\- *theorem* list.inth_succ
- \+/\- *theorem* list.inth_zero
- \+/\- *theorem* list.ith_zero
- \+/\- *theorem* list.last_singleton
- \+/\- *theorem* list.tail_cons
- \+/\- *theorem* list.tail_nil

Modified data/stream.lean
- \+/\- *theorem* stream.all_def
- \+/\- *theorem* stream.any_def
- \+/\- *theorem* stream.approx_succ
- \+/\- *theorem* stream.approx_zero
- \+/\- *theorem* stream.composition
- \+/\- *theorem* stream.cons_append_stream
- \+/\- *theorem* stream.corec_def
- \+/\- *theorem* stream.corec_id_f_eq_iterate
- \+/\- *theorem* stream.drop_succ
- \+/\- *theorem* stream.even_tail
- \+/\- *theorem* stream.head_cons
- \+/\- *theorem* stream.head_even
- \+/\- *theorem* stream.head_iterate
- \+/\- *theorem* stream.head_map
- \+/\- *theorem* stream.head_zip
- \+/\- *theorem* stream.homomorphism
- \+/\- *theorem* stream.identity
- \+/\- *theorem* stream.inits_tail
- \+/\- *theorem* stream.interchange
- \+/\- *theorem* stream.map_const
- \+/\- *theorem* stream.map_eq_apply
- \+/\- *theorem* stream.map_id
- \+/\- *theorem* stream.map_map
- \+/\- *theorem* stream.map_tail
- \+/\- *theorem* stream.nil_append_stream
- \+/\- *theorem* stream.nth_const
- \+/\- *theorem* stream.nth_drop
- \+/\- *theorem* stream.nth_map
- \+/\- *theorem* stream.nth_nats
- \+/\- *theorem* stream.nth_succ
- \+/\- *theorem* stream.nth_zero_cons
- \+/\- *theorem* stream.nth_zero_iterate
- \+/\- *theorem* stream.nth_zip
- \+/\- *theorem* stream.odd_eq
- \+/\- *theorem* stream.tail_cons
- \+/\- *theorem* stream.tail_eq_drop
- \+/\- *theorem* stream.tail_zip
- \+/\- *theorem* stream.tails_eq_iterate

Modified topology/continuity.lean




## [2017-07-23 18:59:39+01:00](https://github.com/leanprover-community/mathlib/commit/4a28535)
refactor(*): attributes on same line
#### Estimated changes
Modified algebra/lattice/boolean_algebra.lean
- \+/\- *theorem* lattice.inf_neg_eq_bot
- \+/\- *theorem* lattice.neg_bot
- \+/\- *theorem* lattice.neg_eq_neg_iff
- \+/\- *theorem* lattice.neg_inf
- \+/\- *theorem* lattice.neg_inf_eq_bot
- \+/\- *theorem* lattice.neg_neg
- \+/\- *theorem* lattice.neg_sup
- \+/\- *theorem* lattice.neg_sup_eq_top
- \+/\- *theorem* lattice.neg_top
- \+/\- *theorem* lattice.sup_neg_eq_top

Modified algebra/lattice/complete_lattice.lean
- \+/\- *theorem* lattice.Inf_empty
- \+/\- *theorem* lattice.Inf_insert
- \+/\- *theorem* lattice.Inf_le
- \+/\- *theorem* lattice.Inf_le_iff
- \+/\- *theorem* lattice.Inf_singleton
- \+/\- *theorem* lattice.Inf_univ
- \+/\- *theorem* lattice.Sup_empty
- \+/\- *theorem* lattice.Sup_insert
- \+/\- *theorem* lattice.Sup_singleton
- \+/\- *theorem* lattice.Sup_univ
- \+/\- *theorem* lattice.foo'
- \+/\- *theorem* lattice.foo
- \+/\- *theorem* lattice.infi_congr_Prop
- \+/\- *theorem* lattice.infi_const
- \+/\- *theorem* lattice.infi_empty
- \+/\- *theorem* lattice.infi_emptyset
- \+/\- *theorem* lattice.infi_exists
- \+/\- *theorem* lattice.infi_false
- \+/\- *theorem* lattice.infi_infi_eq_left
- \+/\- *theorem* lattice.infi_infi_eq_right
- \+/\- *theorem* lattice.infi_insert
- \+/\- *theorem* lattice.infi_le'
- \+/\- *theorem* lattice.infi_singleton
- \+/\- *theorem* lattice.infi_true
- \+/\- *theorem* lattice.infi_union
- \+/\- *theorem* lattice.infi_unit
- \+/\- *theorem* lattice.infi_univ
- \+/\- *theorem* lattice.le_Sup
- \+/\- *theorem* lattice.le_Sup_iff
- \+/\- *theorem* lattice.le_infi_iff
- \+/\- *theorem* lattice.le_supr'
- \+/\- *theorem* lattice.supr_congr_Prop
- \+/\- *theorem* lattice.supr_const
- \+/\- *theorem* lattice.supr_empty
- \+/\- *theorem* lattice.supr_emptyset
- \+/\- *theorem* lattice.supr_exists
- \+/\- *theorem* lattice.supr_false
- \+/\- *theorem* lattice.supr_insert
- \+/\- *theorem* lattice.supr_le_iff
- \+/\- *theorem* lattice.supr_singleton
- \+/\- *theorem* lattice.supr_supr_eq_left
- \+/\- *theorem* lattice.supr_supr_eq_right
- \+/\- *theorem* lattice.supr_true
- \+/\- *theorem* lattice.supr_union
- \+/\- *theorem* lattice.supr_unit
- \+/\- *theorem* lattice.supr_univ

Modified algebra/lattice/filter.lean
- \+/\- *theorem* diff_empty
- \+/\- *theorem* filter.fmap_principal
- \+/\- *theorem* filter.inf_principal
- \+/\- *theorem* filter.infi_sets_induct
- \+/\- *theorem* filter.join_principal_eq_Sup
- \+/\- *theorem* filter.le_principal_iff
- \+/\- *theorem* filter.lift'_id
- \+/\- *theorem* filter.map_bot
- \+/\- *theorem* filter.map_compose
- \+/\- *theorem* filter.map_eq_bot_iff
- \+/\- *theorem* filter.map_id
- \+/\- *theorem* filter.map_principal
- \+/\- *theorem* filter.map_sup
- \+/\- *theorem* filter.mem_bot_sets
- \+/\- *theorem* filter.mem_inf_sets
- \+/\- *theorem* filter.mem_join_sets
- \+/\- *theorem* filter.mem_map
- \+/\- *theorem* filter.mem_principal_sets
- \+/\- *theorem* filter.mem_pure
- \+/\- *theorem* filter.mem_sup_sets
- \+/\- *theorem* filter.mem_top_sets_iff
- \+/\- *theorem* filter.principal_eq_bot_iff
- \+/\- *theorem* filter.principal_eq_iff_eq
- \+/\- *theorem* filter.sup_join
- \+/\- *theorem* filter.sup_principal
- \+/\- *theorem* filter.supr_join
- \+/\- *theorem* filter.supr_map
- \+/\- *theorem* filter.supr_principal
- \+/\- *theorem* filter.vmap_principal
- \+/\- *theorem* not_not_mem_iff
- \+/\- *theorem* prod.fst_swap
- \+/\- *theorem* prod.snd_swap
- \+/\- *theorem* prod.swap_prod_mk
- \+/\- *theorem* prod.swap_swap
- \+/\- *theorem* prod.swap_swap_eq
- \+/\- *theorem* set.prod_mk_mem_set_prod_eq
- \+/\- *theorem* set.prod_singleton_singleton
- \+/\- *theorem* set.set_of_mem_eq
- \+/\- *theorem* set.vimage_set_of_eq
- \+/\- *theorem* singleton_neq_emptyset

Modified data/bool.lean
- \+/\- *theorem* bool.absurd_of_eq_ff_of_eq_tt
- \+/\- *theorem* bool.band_assoc
- \+/\- *theorem* bool.band_comm
- \+/\- *theorem* bool.band_elim_left
- \+/\- *theorem* bool.band_elim_right
- \+/\- *theorem* bool.band_eq_ff
- \+/\- *theorem* bool.band_eq_tt
- \+/\- *theorem* bool.band_ff
- \+/\- *theorem* bool.band_intro
- \+/\- *theorem* bool.band_left_comm
- \+/\- *theorem* bool.band_self
- \+/\- *theorem* bool.band_tt
- \+/\- *theorem* bool.bnot_bnot
- \+/\- *theorem* bool.bnot_false
- \+/\- *theorem* bool.bnot_true
- \+/\- *theorem* bool.bor_assoc
- \+/\- *theorem* bool.bor_comm
- \+/\- *theorem* bool.bor_eq_ff
- \+/\- *theorem* bool.bor_eq_tt
- \+/\- *theorem* bool.bor_ff
- \+/\- *theorem* bool.bor_inl
- \+/\- *theorem* bool.bor_inr
- \+/\- *theorem* bool.bor_left_comm
- \+/\- *theorem* bool.bor_tt
- \+/\- *def* bool.bxor
- \+/\- *theorem* bool.bxor_assoc
- \+/\- *theorem* bool.bxor_comm
- \+/\- *theorem* bool.bxor_ff
- \+/\- *theorem* bool.bxor_left_comm
- \+/\- *theorem* bool.bxor_self
- \+/\- *theorem* bool.bxor_tt
- \+/\- *theorem* bool.coe_tt
- \+/\- *theorem* bool.cond_ff
- \+/\- *theorem* bool.cond_tt
- \+/\- *theorem* bool.dichotomy
- \+/\- *theorem* bool.eq_ff_of_bnot_eq_tt
- \+/\- *theorem* bool.eq_ff_of_ne_tt
- \+/\- *theorem* bool.eq_tt_of_bnot_eq_ff
- \+/\- *theorem* bool.eq_tt_of_ne_ff
- \+/\- *theorem* bool.ff_band
- \+/\- *theorem* bool.ff_bor
- \+/\- *theorem* bool.ff_bxor
- \+/\- *theorem* bool.ff_bxor_ff
- \+/\- *theorem* bool.ff_bxor_tt
- \+/\- *theorem* bool.or_of_bor_eq
- \+/\- *theorem* bool.tt_band
- \+/\- *theorem* bool.tt_bor
- \+/\- *theorem* bool.tt_bxor
- \+/\- *theorem* bool.tt_bxor_ff
- \+/\- *theorem* bool.tt_bxor_tt

Modified data/list/basic.lean
- \+/\- *theorem* list.append.assoc
- \+/\- *theorem* list.concat_append
- \+/\- *theorem* list.concat_ne_nil
- \+/\- *theorem* list.cons_ne_nil
- \+/\- *theorem* list.count_append
- \+/\- *theorem* list.count_concat
- \+/\- *theorem* list.count_cons_of_ne
- \+/\- *theorem* list.count_cons_self
- \+/\- *theorem* list.count_eq_zero_of_not_mem
- \+/\- *theorem* list.count_nil
- \+/\- *theorem* list.head_cons
- \+/\- *theorem* list.index_of_cons_of_eq
- \+/\- *theorem* list.index_of_cons_of_ne
- \+/\- *theorem* list.index_of_nil
- \+/\- *theorem* list.index_of_of_not_mem
- \+/\- *theorem* list.ith_succ
- \+/\- *theorem* list.ith_zero
- \+/\- *theorem* list.last_cons_cons
- \+/\- *theorem* list.last_singleton
- \+/\- *theorem* list.tail_cons
- \+/\- *theorem* list.tail_nil
- \+/\- *theorem* list.taken_nil
- \+/\- *theorem* list.taken_zero

Modified data/list/comb.lean
- \+/\- *theorem* list.all_cons
- \+/\- *theorem* list.all_nil
- \+/\- *theorem* list.any_cons
- \+/\- *theorem* list.any_nil
- \- *def* list.decidable_exists_mem
- \- *def* list.decidable_forall_mem
- \+/\- *theorem* list.exists_mem_cons_iff
- \+/\- *theorem* list.foldl_append
- \+/\- *theorem* list.foldl_cons
- \+/\- *theorem* list.foldl_nil
- \+/\- *theorem* list.foldr_append
- \+/\- *theorem* list.foldr_cons
- \+/\- *theorem* list.foldr_nil
- \+/\- *theorem* list.forall_mem_cons_iff
- \+/\- *theorem* list.length_map_accumr
- \+/\- *theorem* list.length_map_accumr₂
- \+/\- *theorem* list.length_replicate
- \+/\- *theorem* list.unzip_cons
- \+/\- *theorem* list.unzip_nil
- \+/\- *theorem* list.zip_cons_cons
- \+/\- *theorem* list.zip_nil_left
- \+/\- *theorem* list.zip_nil_right

Modified data/list/perm.lean
- \+/\- *theorem* list.perm.perm_app_comm
- \+/\- *theorem* list.perm.perm_cons_app_simp
- \+/\- *theorem* list.perm.perm_induction_on
- \+/\- *theorem* list.perm.perm_map
- \+/\- *theorem* list.perm.perm_rev_simp

Modified data/list/set.lean
- \+/\- *theorem* list.erase_cons_head
- \+/\- *theorem* list.erase_cons_tail
- \+/\- *theorem* list.erase_nil
- \+/\- *theorem* list.erase_of_not_mem
- \+/\- *theorem* list.insert_nil
- \+/\- *theorem* list.insert_of_mem
- \+/\- *theorem* list.insert_of_not_mem
- \+/\- *theorem* list.inter_cons_of_mem
- \+/\- *theorem* list.inter_cons_of_not_mem
- \+/\- *theorem* list.inter_nil
- \+/\- *theorem* list.length_erase_of_mem
- \+/\- *theorem* list.length_insert_of_mem
- \+/\- *theorem* list.length_insert_of_not_mem
- \+/\- *theorem* list.length_upto
- \+/\- *theorem* list.mem_erase_dup_iff
- \+/\- *theorem* list.mem_insert_iff
- \+/\- *theorem* list.mem_insert_of_mem
- \+/\- *theorem* list.mem_insert_self
- \+/\- *theorem* list.mem_inter_iff
- \+/\- *theorem* list.mem_union_iff
- \+/\- *theorem* list.union_cons
- \+/\- *theorem* list.union_nil
- \+/\- *theorem* list.upto_nil
- \+/\- *theorem* list.upto_succ

Modified data/list/sort.lean


Modified data/nat/basic.lean
- \+/\- *theorem* nat.succ_add_eq_succ_add

Modified data/nat/sub.lean
- \+/\- *theorem* nat.dist_comm
- \+/\- *theorem* nat.dist_self

Modified data/rat.lean
- \- *def* rat.decidable_nonneg

Modified data/set/basic.lean
- \+/\- *theorem* set.insert_eq_of_mem
- \+/\- *theorem* set.mem_insert_iff
- \+/\- *theorem* set.mem_sep_eq

Modified data/set/finite.lean
- \+/\- *theorem* set.finite_insert
- \+/\- *theorem* set.finite_singleton

Modified data/set/lattice.lean
- \+/\- *def* set.Inter
- \+/\- *def* set.Union
- \+/\- *theorem* set.bInter_empty
- \+/\- *theorem* set.bInter_insert
- \+/\- *theorem* set.bInter_singleton
- \+/\- *theorem* set.bInter_univ
- \+/\- *theorem* set.bUnion_empty
- \+/\- *theorem* set.bUnion_insert
- \+/\- *theorem* set.bUnion_singleton
- \+/\- *theorem* set.bUnion_univ
- \+/\- *theorem* set.insert_sdiff_singleton
- \+/\- *theorem* set.mem_Inter_eq
- \+/\- *theorem* set.mem_Union_eq
- \+/\- *theorem* set.mem_sInter_eq
- \+/\- *theorem* set.mem_sUnion_eq
- \+/\- *def* set.sInter
- \+/\- *theorem* set.sInter_empty
- \+/\- *theorem* set.sInter_image
- \+/\- *theorem* set.sInter_insert
- \+/\- *theorem* set.sInter_singleton
- \+/\- *theorem* set.sUnion_empty
- \+/\- *theorem* set.sUnion_image
- \+/\- *theorem* set.sUnion_insert
- \+/\- *theorem* set.sUnion_singleton
- \+/\- *theorem* set.sdiff_singleton_eq_same
- \+/\- *theorem* set.union_same_compl

Modified logic/basic.lean
- \+/\- *theorem* prod.exists
- \+/\- *theorem* prod.forall
- \+/\- *theorem* prod.mk.inj_iff
- \+/\- *theorem* set_of_subset_set_of

Modified tactic/converter/binders.lean
- \+/\- *theorem* mem_image

Modified tests/examples.lean
- \+/\- *theorem* mem_set_of

Modified topology/continuity.lean
- \+/\- *theorem* false_neq_true
- \+/\- *theorem* open_singleton_true

Modified topology/topological_space.lean
- \+/\- *theorem* closed_closure
- \+/\- *theorem* closed_compl_iff_open
- \+/\- *theorem* closed_empty
- \+/\- *theorem* closed_univ
- \+/\- *theorem* closure_closure
- \+/\- *theorem* closure_compl_eq
- \+/\- *theorem* closure_empty
- \+/\- *theorem* closure_union
- \+/\- *theorem* closure_univ
- \+/\- *theorem* interior_compl_eq
- \+/\- *theorem* interior_empty
- \+/\- *theorem* interior_inter
- \+/\- *theorem* interior_interior
- \+/\- *theorem* interior_univ
- \+/\- *theorem* nhds_neq_bot
- \+/\- *theorem* open_compl_iff_closed
- \+/\- *theorem* open_empty
- \+/\- *theorem* open_interior
- \+/\- *theorem* open_univ



## [2017-07-23 18:39:51+01:00](https://github.com/leanprover-community/mathlib/commit/a4b157b)
chore(data/nat): remove addl
#### Estimated changes
Modified data/nat/basic.lean
- \- *theorem* nat.add_eq_addl
- \- *def* nat.addl
- \- *theorem* nat.addl_succ_left
- \- *theorem* nat.addl_succ_right
- \- *theorem* nat.addl_zero_left
- \- *theorem* nat.addl_zero_right
- \- *theorem* nat.zero_has_zero



## [2017-07-23 18:29:16+01:00](https://github.com/leanprover-community/mathlib/commit/5816424)
refactor(*): use 'lemma' iff statement is private
#### Estimated changes
Modified algebra/lattice/basic.lean
- \+ *theorem* lattice.bot_inf_eq
- \- *lemma* lattice.bot_inf_eq
- \+ *theorem* lattice.bot_le
- \- *lemma* lattice.bot_le
- \+ *theorem* lattice.bot_sup_eq
- \- *lemma* lattice.bot_sup_eq
- \+ *theorem* lattice.bot_unique
- \- *lemma* lattice.bot_unique
- \+ *theorem* lattice.eq_bot_iff
- \- *lemma* lattice.eq_bot_iff
- \+ *theorem* lattice.eq_top_iff
- \- *lemma* lattice.eq_top_iff
- \+ *theorem* lattice.inf_assoc
- \- *lemma* lattice.inf_assoc
- \+ *theorem* lattice.inf_bot_eq
- \- *lemma* lattice.inf_bot_eq
- \+ *theorem* lattice.inf_comm
- \- *lemma* lattice.inf_comm
- \+ *theorem* lattice.inf_eq_top_iff
- \- *lemma* lattice.inf_eq_top_iff
- \+ *theorem* lattice.inf_idem
- \- *lemma* lattice.inf_idem
- \+ *theorem* lattice.inf_le_inf
- \- *lemma* lattice.inf_le_inf
- \+ *theorem* lattice.inf_le_left'
- \- *lemma* lattice.inf_le_left'
- \+ *theorem* lattice.inf_le_left
- \- *lemma* lattice.inf_le_left
- \+ *theorem* lattice.inf_le_left_of_le
- \- *lemma* lattice.inf_le_left_of_le
- \+ *theorem* lattice.inf_le_right'
- \- *lemma* lattice.inf_le_right'
- \+ *theorem* lattice.inf_le_right
- \- *lemma* lattice.inf_le_right
- \+ *theorem* lattice.inf_le_right_of_le
- \- *lemma* lattice.inf_le_right_of_le
- \+ *theorem* lattice.inf_of_le_left
- \- *lemma* lattice.inf_of_le_left
- \+ *theorem* lattice.inf_of_le_right
- \- *lemma* lattice.inf_of_le_right
- \+ *theorem* lattice.inf_sup_self
- \- *lemma* lattice.inf_sup_self
- \+ *theorem* lattice.inf_top_eq
- \- *lemma* lattice.inf_top_eq
- \+ *theorem* lattice.le_bot_iff
- \- *lemma* lattice.le_bot_iff
- \+ *theorem* lattice.le_inf
- \- *lemma* lattice.le_inf
- \+ *theorem* lattice.le_inf_iff
- \- *lemma* lattice.le_inf_iff
- \+ *theorem* lattice.le_inf_sup
- \- *lemma* lattice.le_inf_sup
- \+ *theorem* lattice.le_of_inf_eq
- \- *lemma* lattice.le_of_inf_eq
- \+ *theorem* lattice.le_of_sup_eq
- \- *lemma* lattice.le_of_sup_eq
- \+ *theorem* lattice.le_sup_left'
- \- *lemma* lattice.le_sup_left'
- \+ *theorem* lattice.le_sup_left
- \- *lemma* lattice.le_sup_left
- \+ *theorem* lattice.le_sup_left_of_le
- \- *lemma* lattice.le_sup_left_of_le
- \+ *theorem* lattice.le_sup_right'
- \- *lemma* lattice.le_sup_right'
- \+ *theorem* lattice.le_sup_right
- \- *lemma* lattice.le_sup_right
- \+ *theorem* lattice.le_sup_right_of_le
- \- *lemma* lattice.le_sup_right_of_le
- \+ *theorem* lattice.le_top
- \- *lemma* lattice.le_top
- \+ *theorem* lattice.neq_bot_of_le_neq_bot
- \- *lemma* lattice.neq_bot_of_le_neq_bot
- \+ *theorem* lattice.sup_assoc
- \- *lemma* lattice.sup_assoc
- \+ *theorem* lattice.sup_bot_eq
- \- *lemma* lattice.sup_bot_eq
- \+ *theorem* lattice.sup_comm
- \- *lemma* lattice.sup_comm
- \+ *theorem* lattice.sup_eq_bot_iff
- \- *lemma* lattice.sup_eq_bot_iff
- \+ *theorem* lattice.sup_idem
- \- *lemma* lattice.sup_idem
- \+ *theorem* lattice.sup_inf_le
- \- *lemma* lattice.sup_inf_le
- \+ *theorem* lattice.sup_inf_self
- \- *lemma* lattice.sup_inf_self
- \+ *theorem* lattice.sup_le
- \- *lemma* lattice.sup_le
- \+ *theorem* lattice.sup_le_iff
- \- *lemma* lattice.sup_le_iff
- \+ *theorem* lattice.sup_le_sup
- \- *lemma* lattice.sup_le_sup
- \+ *theorem* lattice.sup_of_le_left
- \- *lemma* lattice.sup_of_le_left
- \+ *theorem* lattice.sup_of_le_right
- \- *lemma* lattice.sup_of_le_right
- \+ *theorem* lattice.sup_top_eq
- \- *lemma* lattice.sup_top_eq
- \+ *theorem* lattice.top_inf_eq
- \- *lemma* lattice.top_inf_eq
- \+ *theorem* lattice.top_le_iff
- \- *lemma* lattice.top_le_iff
- \+ *theorem* lattice.top_sup_eq
- \- *lemma* lattice.top_sup_eq
- \+ *theorem* lattice.top_unique
- \- *lemma* lattice.top_unique
- \+ *theorem* le_antisymm'
- \- *lemma* le_antisymm'

Modified algebra/lattice/boolean_algebra.lean
- \+ *theorem* lattice.inf_neg_eq_bot
- \- *lemma* lattice.inf_neg_eq_bot
- \+ *theorem* lattice.inf_sup_left
- \- *lemma* lattice.inf_sup_left
- \+ *theorem* lattice.inf_sup_right
- \- *lemma* lattice.inf_sup_right
- \+ *theorem* lattice.le_neg_of_le_neg
- \- *lemma* lattice.le_neg_of_le_neg
- \+ *theorem* lattice.le_sup_inf
- \- *lemma* lattice.le_sup_inf
- \+ *theorem* lattice.neg_bot
- \- *lemma* lattice.neg_bot
- \+ *theorem* lattice.neg_eq_neg_iff
- \- *lemma* lattice.neg_eq_neg_iff
- \+ *theorem* lattice.neg_eq_neg_of_eq
- \- *lemma* lattice.neg_eq_neg_of_eq
- \+ *theorem* lattice.neg_inf
- \- *lemma* lattice.neg_inf
- \+ *theorem* lattice.neg_inf_eq_bot
- \- *lemma* lattice.neg_inf_eq_bot
- \+ *theorem* lattice.neg_le_iff_neg_le
- \- *lemma* lattice.neg_le_iff_neg_le
- \+ *theorem* lattice.neg_le_neg
- \- *lemma* lattice.neg_le_neg
- \+ *theorem* lattice.neg_le_neg_iff_le
- \- *lemma* lattice.neg_le_neg_iff_le
- \+ *theorem* lattice.neg_le_of_neg_le
- \- *lemma* lattice.neg_le_of_neg_le
- \+ *theorem* lattice.neg_neg
- \- *lemma* lattice.neg_neg
- \+ *theorem* lattice.neg_sup
- \- *lemma* lattice.neg_sup
- \+ *theorem* lattice.neg_sup_eq_top
- \- *lemma* lattice.neg_sup_eq_top
- \+ *theorem* lattice.neg_top
- \- *lemma* lattice.neg_top
- \+ *theorem* lattice.neg_unique
- \- *lemma* lattice.neg_unique
- \+ *theorem* lattice.sub_eq
- \- *lemma* lattice.sub_eq
- \+ *theorem* lattice.sub_eq_left
- \- *lemma* lattice.sub_eq_left
- \+ *theorem* lattice.sup_inf_left
- \- *lemma* lattice.sup_inf_left
- \+ *theorem* lattice.sup_inf_right
- \- *lemma* lattice.sup_inf_right
- \+ *theorem* lattice.sup_neg_eq_top
- \- *lemma* lattice.sup_neg_eq_top
- \+ *theorem* lattice.sup_sub_same
- \- *lemma* lattice.sup_sub_same

Modified algebra/lattice/bounded_lattice.lean
- \+ *theorem* lattice.monotone_and
- \- *lemma* lattice.monotone_and
- \+ *theorem* lattice.monotone_or
- \- *lemma* lattice.monotone_or

Modified algebra/lattice/complete_boolean_algebra.lean
- \+ *theorem* lattice.inf_Sup_eq
- \- *lemma* lattice.inf_Sup_eq
- \+ *theorem* lattice.neg_Inf
- \- *lemma* lattice.neg_Inf
- \+ *theorem* lattice.neg_Sup
- \- *lemma* lattice.neg_Sup
- \+ *theorem* lattice.neg_infi
- \- *lemma* lattice.neg_infi
- \+ *theorem* lattice.neg_supr
- \- *lemma* lattice.neg_supr
- \+ *theorem* lattice.sup_Inf_eq
- \- *lemma* lattice.sup_Inf_eq

Modified algebra/lattice/complete_lattice.lean
- \+ *theorem* lattice.Inf_empty
- \- *lemma* lattice.Inf_empty
- \+ *theorem* lattice.Inf_eq_infi
- \- *lemma* lattice.Inf_eq_infi
- \+ *theorem* lattice.Inf_image
- \- *lemma* lattice.Inf_image
- \+ *theorem* lattice.Inf_insert
- \- *lemma* lattice.Inf_insert
- \+ *theorem* lattice.Inf_le
- \- *lemma* lattice.Inf_le
- \+ *theorem* lattice.Inf_le_Inf
- \- *lemma* lattice.Inf_le_Inf
- \+ *theorem* lattice.Inf_le_Sup
- \- *lemma* lattice.Inf_le_Sup
- \+ *theorem* lattice.Inf_le_iff
- \- *lemma* lattice.Inf_le_iff
- \+ *theorem* lattice.Inf_le_of_le
- \- *lemma* lattice.Inf_le_of_le
- \+ *theorem* lattice.Inf_singleton
- \- *lemma* lattice.Inf_singleton
- \+ *theorem* lattice.Inf_union
- \- *lemma* lattice.Inf_union
- \+ *theorem* lattice.Inf_univ
- \- *lemma* lattice.Inf_univ
- \+ *theorem* lattice.Sup_empty
- \- *lemma* lattice.Sup_empty
- \+ *theorem* lattice.Sup_eq_supr
- \- *lemma* lattice.Sup_eq_supr
- \+ *theorem* lattice.Sup_image
- \- *lemma* lattice.Sup_image
- \+ *theorem* lattice.Sup_insert
- \- *lemma* lattice.Sup_insert
- \+ *theorem* lattice.Sup_inter_le
- \- *lemma* lattice.Sup_inter_le
- \+ *theorem* lattice.Sup_le
- \- *lemma* lattice.Sup_le
- \+ *theorem* lattice.Sup_le_Sup
- \- *lemma* lattice.Sup_le_Sup
- \+ *theorem* lattice.Sup_singleton
- \- *lemma* lattice.Sup_singleton
- \+ *theorem* lattice.Sup_union
- \- *lemma* lattice.Sup_union
- \+ *theorem* lattice.Sup_univ
- \- *lemma* lattice.Sup_univ
- \+ *theorem* lattice.foo'
- \- *lemma* lattice.foo'
- \+ *theorem* lattice.foo
- \- *lemma* lattice.foo
- \+ *theorem* lattice.infi_and
- \- *lemma* lattice.infi_and
- \+ *theorem* lattice.infi_comm
- \- *lemma* lattice.infi_comm
- \+ *theorem* lattice.infi_congr_Prop
- \- *lemma* lattice.infi_congr_Prop
- \+ *theorem* lattice.infi_const
- \- *lemma* lattice.infi_const
- \+ *theorem* lattice.infi_empty
- \- *lemma* lattice.infi_empty
- \+ *theorem* lattice.infi_emptyset
- \- *lemma* lattice.infi_emptyset
- \+ *theorem* lattice.infi_exists
- \- *lemma* lattice.infi_exists
- \+ *theorem* lattice.infi_false
- \- *lemma* lattice.infi_false
- \+ *theorem* lattice.infi_inf_eq
- \- *lemma* lattice.infi_inf_eq
- \+ *theorem* lattice.infi_infi_eq_left
- \- *lemma* lattice.infi_infi_eq_left
- \+ *theorem* lattice.infi_infi_eq_right
- \- *lemma* lattice.infi_infi_eq_right
- \+ *theorem* lattice.infi_insert
- \- *lemma* lattice.infi_insert
- \+ *theorem* lattice.infi_le'
- \- *lemma* lattice.infi_le'
- \+ *theorem* lattice.infi_le
- \- *lemma* lattice.infi_le
- \+ *theorem* lattice.infi_le_infi2
- \- *lemma* lattice.infi_le_infi2
- \+ *theorem* lattice.infi_le_infi
- \- *lemma* lattice.infi_le_infi
- \+ *theorem* lattice.infi_le_infi_const
- \- *lemma* lattice.infi_le_infi_const
- \+ *theorem* lattice.infi_le_of_le
- \- *lemma* lattice.infi_le_of_le
- \+ *theorem* lattice.infi_or
- \- *lemma* lattice.infi_or
- \+ *theorem* lattice.infi_prod
- \- *lemma* lattice.infi_prod
- \+ *theorem* lattice.infi_sigma
- \- *lemma* lattice.infi_sigma
- \+ *theorem* lattice.infi_singleton
- \- *lemma* lattice.infi_singleton
- \+ *theorem* lattice.infi_subtype
- \- *lemma* lattice.infi_subtype
- \+ *theorem* lattice.infi_sum
- \- *lemma* lattice.infi_sum
- \+ *theorem* lattice.infi_true
- \- *lemma* lattice.infi_true
- \+ *theorem* lattice.infi_union
- \- *lemma* lattice.infi_union
- \+ *theorem* lattice.infi_unit
- \- *lemma* lattice.infi_unit
- \+ *theorem* lattice.infi_univ
- \- *lemma* lattice.infi_univ
- \+ *theorem* lattice.le_Inf
- \- *lemma* lattice.le_Inf
- \+ *theorem* lattice.le_Inf_inter
- \- *lemma* lattice.le_Inf_inter
- \+ *theorem* lattice.le_Sup
- \- *lemma* lattice.le_Sup
- \+ *theorem* lattice.le_Sup_iff
- \- *lemma* lattice.le_Sup_iff
- \+ *theorem* lattice.le_Sup_of_le
- \- *lemma* lattice.le_Sup_of_le
- \+ *theorem* lattice.le_infi
- \- *lemma* lattice.le_infi
- \+ *theorem* lattice.le_infi_iff
- \- *lemma* lattice.le_infi_iff
- \+ *theorem* lattice.le_supr'
- \- *lemma* lattice.le_supr'
- \+ *theorem* lattice.le_supr
- \- *lemma* lattice.le_supr
- \+ *theorem* lattice.le_supr_of_le
- \- *lemma* lattice.le_supr_of_le
- \+ *theorem* lattice.monotone_Inf_of_monotone
- \- *lemma* lattice.monotone_Inf_of_monotone
- \+ *theorem* lattice.monotone_Sup_of_monotone
- \- *lemma* lattice.monotone_Sup_of_monotone
- \+ *theorem* lattice.supr_and
- \- *lemma* lattice.supr_and
- \+ *theorem* lattice.supr_comm
- \- *lemma* lattice.supr_comm
- \+ *theorem* lattice.supr_congr_Prop
- \- *lemma* lattice.supr_congr_Prop
- \+ *theorem* lattice.supr_const
- \- *lemma* lattice.supr_const
- \+ *theorem* lattice.supr_empty
- \- *lemma* lattice.supr_empty
- \+ *theorem* lattice.supr_emptyset
- \- *lemma* lattice.supr_emptyset
- \+ *theorem* lattice.supr_exists
- \- *lemma* lattice.supr_exists
- \+ *theorem* lattice.supr_false
- \- *lemma* lattice.supr_false
- \+ *theorem* lattice.supr_insert
- \- *lemma* lattice.supr_insert
- \+ *theorem* lattice.supr_le
- \- *lemma* lattice.supr_le
- \+ *theorem* lattice.supr_le_iff
- \- *lemma* lattice.supr_le_iff
- \+ *theorem* lattice.supr_le_supr2
- \- *lemma* lattice.supr_le_supr2
- \+ *theorem* lattice.supr_le_supr
- \- *lemma* lattice.supr_le_supr
- \+ *theorem* lattice.supr_le_supr_const
- \- *lemma* lattice.supr_le_supr_const
- \+ *theorem* lattice.supr_or
- \- *lemma* lattice.supr_or
- \+ *theorem* lattice.supr_prod
- \- *lemma* lattice.supr_prod
- \+ *theorem* lattice.supr_sigma
- \- *lemma* lattice.supr_sigma
- \+ *theorem* lattice.supr_singleton
- \- *lemma* lattice.supr_singleton
- \+ *theorem* lattice.supr_subtype
- \- *lemma* lattice.supr_subtype
- \+ *theorem* lattice.supr_sum
- \- *lemma* lattice.supr_sum
- \+ *theorem* lattice.supr_sup_eq
- \- *lemma* lattice.supr_sup_eq
- \+ *theorem* lattice.supr_supr_eq_left
- \- *lemma* lattice.supr_supr_eq_left
- \+ *theorem* lattice.supr_supr_eq_right
- \- *lemma* lattice.supr_supr_eq_right
- \+ *theorem* lattice.supr_true
- \- *lemma* lattice.supr_true
- \+ *theorem* lattice.supr_union
- \- *lemma* lattice.supr_union
- \+ *theorem* lattice.supr_unit
- \- *lemma* lattice.supr_unit
- \+ *theorem* lattice.supr_univ
- \- *lemma* lattice.supr_univ

Modified algebra/lattice/filter.lean
- \+ *theorem* Union_subset_Union2
- \- *lemma* Union_subset_Union2
- \+ *theorem* Union_subset_Union
- \- *lemma* Union_subset_Union
- \+ *theorem* Union_subset_Union_const
- \- *lemma* Union_subset_Union_const
- \+ *theorem* compl_image_set_of
- \- *lemma* compl_image_set_of
- \+ *theorem* diff_empty
- \- *lemma* diff_empty
- \+ *theorem* diff_neq_empty
- \- *lemma* diff_neq_empty
- \+ *theorem* directed_of_chain
- \- *lemma* directed_of_chain
- \+ *theorem* directed_on_Union
- \- *lemma* directed_on_Union
- \+ *theorem* eq_of_sup_eq_inf_eq
- \- *lemma* eq_of_sup_eq_inf_eq
- \+ *theorem* filter.Inf_sets_eq_finite
- \- *lemma* filter.Inf_sets_eq_finite
- \+ *theorem* filter.Inter_mem_sets
- \- *lemma* filter.Inter_mem_sets
- \+ *theorem* filter.bind_mono2
- \- *lemma* filter.bind_mono2
- \+ *theorem* filter.bind_mono
- \- *lemma* filter.bind_mono
- \+ *theorem* filter.bind_sup
- \- *lemma* filter.bind_sup
- \+ *theorem* filter.binfi_sup_eq
- \- *lemma* filter.binfi_sup_eq
- \+ *theorem* filter.empty_in_sets_eq_bot
- \- *lemma* filter.empty_in_sets_eq_bot
- \+ *theorem* filter.exists_sets_subset_iff
- \- *lemma* filter.exists_sets_subset_iff
- \+ *theorem* filter.exists_ultrafilter
- \- *lemma* filter.exists_ultrafilter
- \+ *theorem* filter.filter_eq
- \- *lemma* filter.filter_eq
- \+ *theorem* filter.filter_eq_bot_of_not_nonempty
- \- *lemma* filter.filter_eq_bot_of_not_nonempty
- \+ *theorem* filter.fmap_principal
- \- *lemma* filter.fmap_principal
- \+ *theorem* filter.forall_sets_neq_empty_iff_neq_bot
- \- *lemma* filter.forall_sets_neq_empty_iff_neq_bot
- \+ *theorem* filter.image_mem_map
- \- *lemma* filter.image_mem_map
- \+ *theorem* filter.inf_principal
- \- *lemma* filter.inf_principal
- \+ *theorem* filter.infi_neq_bot_iff_of_directed
- \- *lemma* filter.infi_neq_bot_iff_of_directed
- \+ *theorem* filter.infi_neq_bot_of_directed
- \- *lemma* filter.infi_neq_bot_of_directed
- \+ *theorem* filter.infi_sets_eq'
- \- *lemma* filter.infi_sets_eq'
- \+ *theorem* filter.infi_sets_eq
- \- *lemma* filter.infi_sets_eq
- \+ *theorem* filter.infi_sets_induct
- \- *lemma* filter.infi_sets_induct
- \+ *theorem* filter.infi_sup_eq
- \- *lemma* filter.infi_sup_eq
- \+ *theorem* filter.inhabited_of_mem_sets
- \- *lemma* filter.inhabited_of_mem_sets
- \+ *theorem* filter.inter_mem_sets
- \- *lemma* filter.inter_mem_sets
- \+ *theorem* filter.join_principal_eq_Sup
- \- *lemma* filter.join_principal_eq_Sup
- \+ *theorem* filter.le_lift'
- \- *lemma* filter.le_lift'
- \+ *theorem* filter.le_map_vmap
- \- *lemma* filter.le_map_vmap
- \+ *theorem* filter.le_of_ultrafilter
- \- *lemma* filter.le_of_ultrafilter
- \+ *theorem* filter.le_principal_iff
- \- *lemma* filter.le_principal_iff
- \+ *theorem* filter.le_vmap_iff_map_le
- \- *lemma* filter.le_vmap_iff_map_le
- \+ *theorem* filter.le_vmap_map
- \- *lemma* filter.le_vmap_map
- \+ *theorem* filter.lift'_cong
- \- *lemma* filter.lift'_cong
- \+ *theorem* filter.lift'_id
- \- *lemma* filter.lift'_id
- \+ *theorem* filter.lift'_inf_principal_eq
- \- *lemma* filter.lift'_inf_principal_eq
- \+ *theorem* filter.lift'_infi
- \- *lemma* filter.lift'_infi
- \+ *theorem* filter.lift'_lift'_assoc
- \- *lemma* filter.lift'_lift'_assoc
- \+ *theorem* filter.lift'_lift_assoc
- \- *lemma* filter.lift'_lift_assoc
- \+ *theorem* filter.lift'_mono'
- \- *lemma* filter.lift'_mono'
- \+ *theorem* filter.lift'_mono
- \- *lemma* filter.lift'_mono
- \+ *theorem* filter.lift'_neq_bot_iff
- \- *lemma* filter.lift'_neq_bot_iff
- \+ *theorem* filter.lift'_principal
- \- *lemma* filter.lift'_principal
- \+ *theorem* filter.lift_assoc
- \- *lemma* filter.lift_assoc
- \+ *theorem* filter.lift_comm
- \- *lemma* filter.lift_comm
- \+ *theorem* filter.lift_infi'
- \- *lemma* filter.lift_infi'
- \+ *theorem* filter.lift_infi
- \- *lemma* filter.lift_infi
- \+ *theorem* filter.lift_lift'_assoc
- \- *lemma* filter.lift_lift'_assoc
- \+ *theorem* filter.lift_lift'_same_eq_lift'
- \- *lemma* filter.lift_lift'_same_eq_lift'
- \+ *theorem* filter.lift_lift'_same_le_lift'
- \- *lemma* filter.lift_lift'_same_le_lift'
- \+ *theorem* filter.lift_lift_same_eq_lift
- \- *lemma* filter.lift_lift_same_eq_lift
- \+ *theorem* filter.lift_lift_same_le_lift
- \- *lemma* filter.lift_lift_same_le_lift
- \+ *theorem* filter.lift_mono'
- \- *lemma* filter.lift_mono'
- \+ *theorem* filter.lift_mono
- \- *lemma* filter.lift_mono
- \+ *theorem* filter.lift_neq_bot_iff
- \- *lemma* filter.lift_neq_bot_iff
- \+ *theorem* filter.lift_principal
- \- *lemma* filter.lift_principal
- \+ *theorem* filter.lift_sets_eq
- \- *lemma* filter.lift_sets_eq
- \+ *theorem* filter.map_binfi_eq
- \- *lemma* filter.map_binfi_eq
- \+ *theorem* filter.map_bot
- \- *lemma* filter.map_bot
- \+ *theorem* filter.map_compose
- \- *lemma* filter.map_compose
- \+ *theorem* filter.map_eq_bot_iff
- \- *lemma* filter.map_eq_bot_iff
- \+ *theorem* filter.map_eq_vmap_of_inverse
- \- *lemma* filter.map_eq_vmap_of_inverse
- \+ *theorem* filter.map_id
- \- *lemma* filter.map_id
- \+ *theorem* filter.map_infi_eq
- \- *lemma* filter.map_infi_eq
- \+ *theorem* filter.map_infi_le
- \- *lemma* filter.map_infi_le
- \+ *theorem* filter.map_lift'_eq2
- \- *lemma* filter.map_lift'_eq2
- \+ *theorem* filter.map_lift'_eq
- \- *lemma* filter.map_lift'_eq
- \+ *theorem* filter.map_lift_eq2
- \- *lemma* filter.map_lift_eq2
- \+ *theorem* filter.map_lift_eq
- \- *lemma* filter.map_lift_eq
- \+ *theorem* filter.map_mono
- \- *lemma* filter.map_mono
- \+ *theorem* filter.map_principal
- \- *lemma* filter.map_principal
- \+ *theorem* filter.map_sup
- \- *lemma* filter.map_sup
- \+ *theorem* filter.map_swap_vmap_swap_eq
- \- *lemma* filter.map_swap_vmap_swap_eq
- \+ *theorem* filter.map_vmap_le
- \- *lemma* filter.map_vmap_le
- \+ *theorem* filter.mem_bind_sets
- \- *lemma* filter.mem_bind_sets
- \+ *theorem* filter.mem_bot_sets
- \- *lemma* filter.mem_bot_sets
- \+ *theorem* filter.mem_inf_sets
- \- *lemma* filter.mem_inf_sets
- \+ *theorem* filter.mem_inf_sets_of_left
- \- *lemma* filter.mem_inf_sets_of_left
- \+ *theorem* filter.mem_inf_sets_of_right
- \- *lemma* filter.mem_inf_sets_of_right
- \+ *theorem* filter.mem_infi_sets
- \- *lemma* filter.mem_infi_sets
- \+ *theorem* filter.mem_join_sets
- \- *lemma* filter.mem_join_sets
- \+ *theorem* filter.mem_lift'
- \- *lemma* filter.mem_lift'
- \+ *theorem* filter.mem_lift'_iff
- \- *lemma* filter.mem_lift'_iff
- \+ *theorem* filter.mem_lift
- \- *lemma* filter.mem_lift
- \+ *theorem* filter.mem_lift_iff
- \- *lemma* filter.mem_lift_iff
- \+ *theorem* filter.mem_map
- \- *lemma* filter.mem_map
- \+ *theorem* filter.mem_of_finite_Union_ultrafilter
- \- *lemma* filter.mem_of_finite_Union_ultrafilter
- \+ *theorem* filter.mem_of_finite_sUnion_ultrafilter
- \- *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \+ *theorem* filter.mem_or_compl_mem_of_ultrafilter
- \- *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \+ *theorem* filter.mem_or_mem_of_ultrafilter
- \- *lemma* filter.mem_or_mem_of_ultrafilter
- \+ *theorem* filter.mem_principal_sets
- \- *lemma* filter.mem_principal_sets
- \+ *theorem* filter.mem_prod_iff
- \- *lemma* filter.mem_prod_iff
- \+ *theorem* filter.mem_prod_same_iff
- \- *lemma* filter.mem_prod_same_iff
- \+ *theorem* filter.mem_pure
- \- *lemma* filter.mem_pure
- \+ *theorem* filter.mem_return_sets
- \- *lemma* filter.mem_return_sets
- \+ *theorem* filter.mem_sets_of_neq_bot
- \- *lemma* filter.mem_sets_of_neq_bot
- \+ *theorem* filter.mem_sup_sets
- \- *lemma* filter.mem_sup_sets
- \+ *theorem* filter.mem_top_sets_iff
- \- *lemma* filter.mem_top_sets_iff
- \+ *theorem* filter.mem_vmap_of_mem
- \- *lemma* filter.mem_vmap_of_mem
- \+ *theorem* filter.monotone_lift'
- \- *lemma* filter.monotone_lift'
- \+ *theorem* filter.monotone_lift
- \- *lemma* filter.monotone_lift
- \+ *theorem* filter.monotone_map
- \- *lemma* filter.monotone_map
- \+ *theorem* filter.monotone_mem_sets
- \- *lemma* filter.monotone_mem_sets
- \+ *theorem* filter.monotone_principal
- \- *lemma* filter.monotone_principal
- \+ *theorem* filter.monotone_vmap
- \- *lemma* filter.monotone_vmap
- \+ *theorem* filter.principal_bind
- \- *lemma* filter.principal_bind
- \+ *theorem* filter.principal_empty
- \- *lemma* filter.principal_empty
- \+ *theorem* filter.principal_eq_bot_iff
- \- *lemma* filter.principal_eq_bot_iff
- \+ *theorem* filter.principal_eq_iff_eq
- \- *lemma* filter.principal_eq_iff_eq
- \+ *theorem* filter.principal_le_lift'
- \- *lemma* filter.principal_le_lift'
- \+ *theorem* filter.principal_mono
- \- *lemma* filter.principal_mono
- \+ *theorem* filter.principal_univ
- \- *lemma* filter.principal_univ
- \+ *theorem* filter.prod_comm
- \- *lemma* filter.prod_comm
- \+ *theorem* filter.prod_inf_prod
- \- *lemma* filter.prod_inf_prod
- \+ *theorem* filter.prod_lift'_lift'
- \- *lemma* filter.prod_lift'_lift'
- \+ *theorem* filter.prod_lift_lift
- \- *lemma* filter.prod_lift_lift
- \+ *theorem* filter.prod_map_map_eq
- \- *lemma* filter.prod_map_map_eq
- \+ *theorem* filter.prod_mem_prod
- \- *lemma* filter.prod_mem_prod
- \+ *theorem* filter.prod_mono
- \- *lemma* filter.prod_mono
- \+ *theorem* filter.prod_neq_bot
- \- *lemma* filter.prod_neq_bot
- \+ *theorem* filter.prod_principal_principal
- \- *lemma* filter.prod_principal_principal
- \+ *theorem* filter.prod_same_eq
- \- *lemma* filter.prod_same_eq
- \+ *theorem* filter.prod_vmap_vmap_eq
- \- *lemma* filter.prod_vmap_vmap_eq
- \+ *theorem* filter.return_neq_bot
- \- *lemma* filter.return_neq_bot
- \+ *theorem* filter.seq_mono
- \- *lemma* filter.seq_mono
- \+ *theorem* filter.sup_join
- \- *lemma* filter.sup_join
- \+ *theorem* filter.sup_principal
- \- *lemma* filter.sup_principal
- \+ *theorem* filter.supr_join
- \- *lemma* filter.supr_join
- \+ *theorem* filter.supr_map
- \- *lemma* filter.supr_map
- \+ *theorem* filter.supr_principal
- \- *lemma* filter.supr_principal
- \+ *theorem* filter.supr_sets_eq
- \- *lemma* filter.supr_sets_eq
- \+ *theorem* filter.ultrafilter_map
- \- *lemma* filter.ultrafilter_map
- \+ *theorem* filter.ultrafilter_of_le
- \- *lemma* filter.ultrafilter_of_le
- \+ *theorem* filter.ultrafilter_of_spec
- \- *lemma* filter.ultrafilter_of_spec
- \+ *theorem* filter.ultrafilter_of_split
- \- *lemma* filter.ultrafilter_of_split
- \+ *theorem* filter.ultrafilter_of_ultrafilter
- \- *lemma* filter.ultrafilter_of_ultrafilter
- \+ *theorem* filter.ultrafilter_pure
- \- *lemma* filter.ultrafilter_pure
- \+ *theorem* filter.ultrafilter_ultrafilter_of
- \- *lemma* filter.ultrafilter_ultrafilter_of
- \+ *theorem* filter.ultrafilter_unique
- \- *lemma* filter.ultrafilter_unique
- \+ *theorem* filter.univ_mem_sets'
- \- *lemma* filter.univ_mem_sets'
- \+ *theorem* filter.univ_mem_sets
- \- *lemma* filter.univ_mem_sets
- \+ *theorem* filter.vimage_mem_vmap
- \- *lemma* filter.vimage_mem_vmap
- \+ *theorem* filter.vmap_eq_lift'
- \- *lemma* filter.vmap_eq_lift'
- \+ *theorem* filter.vmap_lift'_eq2
- \- *lemma* filter.vmap_lift'_eq2
- \+ *theorem* filter.vmap_lift'_eq
- \- *lemma* filter.vmap_lift'_eq
- \+ *theorem* filter.vmap_lift_eq2
- \- *lemma* filter.vmap_lift_eq2
- \+ *theorem* filter.vmap_lift_eq
- \- *lemma* filter.vmap_lift_eq
- \+ *theorem* filter.vmap_map
- \- *lemma* filter.vmap_map
- \+ *theorem* filter.vmap_mono
- \- *lemma* filter.vmap_mono
- \+ *theorem* filter.vmap_neq_bot
- \- *lemma* filter.vmap_neq_bot
- \+ *theorem* filter.vmap_neq_bot_of_surj
- \- *lemma* filter.vmap_neq_bot_of_surj
- \+ *theorem* filter.vmap_principal
- \- *lemma* filter.vmap_principal
- \+ *theorem* filter.vmap_vmap_comp
- \- *lemma* filter.vmap_vmap_comp
- \+ *theorem* implies_implies_true_iff
- \- *lemma* implies_implies_true_iff
- \+ *theorem* inf_eq_bot_iff_le_compl
- \- *lemma* inf_eq_bot_iff_le_compl
- \+ *theorem* lattice.Inf_eq_finite_sets
- \- *lemma* lattice.Inf_eq_finite_sets
- \+ *theorem* lattice.Sup_le_iff
- \- *lemma* lattice.Sup_le_iff
- \+ *theorem* neg_subset_neg_iff_subset
- \- *lemma* neg_subset_neg_iff_subset
- \+ *theorem* not_not_mem_iff
- \- *lemma* not_not_mem_iff
- \+ *theorem* prod.fst_swap
- \- *lemma* prod.fst_swap
- \+ *theorem* prod.mk.eta
- \- *lemma* prod.mk.eta
- \+ *theorem* prod.snd_swap
- \- *lemma* prod.snd_swap
- \+ *theorem* prod.swap_prod_mk
- \- *lemma* prod.swap_prod_mk
- \+ *theorem* prod.swap_swap
- \- *lemma* prod.swap_swap
- \+ *theorem* prod.swap_swap_eq
- \- *lemma* prod.swap_swap_eq
- \+ *theorem* pure_seq_eq_map
- \- *lemma* pure_seq_eq_map
- \+ *theorem* sUnion_eq_Union
- \- *lemma* sUnion_eq_Union
- \+ *theorem* sUnion_mono
- \- *lemma* sUnion_mono
- \+ *theorem* set.diff_right_antimono
- \- *lemma* set.diff_right_antimono
- \+ *theorem* set.fmap_eq_image
- \- *lemma* set.fmap_eq_image
- \+ *theorem* set.image_eq_vimage_of_inverse
- \- *lemma* set.image_eq_vimage_of_inverse
- \+ *theorem* set.image_swap_eq_vimage_swap
- \- *lemma* set.image_swap_eq_vimage_swap
- \+ *theorem* set.image_swap_prod
- \- *lemma* set.image_swap_prod
- \+ *theorem* set.mem_image_iff_of_inverse
- \- *lemma* set.mem_image_iff_of_inverse
- \+ *theorem* set.mem_prod_eq
- \- *lemma* set.mem_prod_eq
- \+ *theorem* set.mem_seq_iff
- \- *lemma* set.mem_seq_iff
- \+ *theorem* set.monotone_inter
- \- *lemma* set.monotone_inter
- \+ *theorem* set.monotone_prod
- \- *lemma* set.monotone_prod
- \+ *theorem* set.monotone_set_of
- \- *lemma* set.monotone_set_of
- \+ *theorem* set.prod_image_image_eq
- \- *lemma* set.prod_image_image_eq
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
- \+ *theorem* set.prod_vimage_eq
- \- *lemma* set.prod_vimage_eq
- \+ *theorem* set.set_of_mem_eq
- \- *lemma* set.set_of_mem_eq
- \+ *theorem* set.vimage_set_of_eq
- \- *lemma* set.vimage_set_of_eq
- \+ *theorem* singleton_neq_emptyset
- \- *lemma* singleton_neq_emptyset

Modified algebra/lattice/fixed_points.lean
- \+ *theorem* ge_of_eq
- \- *lemma* ge_of_eq
- \+ *theorem* lattice.gfp_comp
- \- *lemma* lattice.gfp_comp
- \+ *theorem* lattice.gfp_eq
- \- *lemma* lattice.gfp_eq
- \+ *theorem* lattice.gfp_gfp
- \- *lemma* lattice.gfp_gfp
- \+ *theorem* lattice.gfp_induct
- \- *lemma* lattice.gfp_induct
- \+ *theorem* lattice.gfp_le
- \- *lemma* lattice.gfp_le
- \+ *theorem* lattice.le_gfp
- \- *lemma* lattice.le_gfp
- \+ *theorem* lattice.le_lfp
- \- *lemma* lattice.le_lfp
- \+ *theorem* lattice.lfp_comp
- \- *lemma* lattice.lfp_comp
- \+ *theorem* lattice.lfp_eq
- \- *lemma* lattice.lfp_eq
- \+ *theorem* lattice.lfp_induct
- \- *lemma* lattice.lfp_induct
- \+ *theorem* lattice.lfp_le
- \- *lemma* lattice.lfp_le
- \+ *theorem* lattice.lfp_lfp
- \- *lemma* lattice.lfp_lfp
- \+ *theorem* lattice.monotone_gfp
- \- *lemma* lattice.monotone_gfp
- \+ *theorem* lattice.monotone_lfp
- \- *lemma* lattice.monotone_lfp

Modified algebra/lattice/zorn.lean
- \+ *theorem* zorn.chain_chain_closure
- \- *lemma* zorn.chain_chain_closure
- \+ *theorem* zorn.chain_closure_closure
- \- *lemma* zorn.chain_closure_closure
- \+ *theorem* zorn.chain_closure_empty
- \- *lemma* zorn.chain_closure_empty
- \+ *theorem* zorn.chain_closure_succ_fixpoint
- \- *lemma* zorn.chain_closure_succ_fixpoint
- \+ *theorem* zorn.chain_closure_succ_fixpoint_iff
- \- *lemma* zorn.chain_closure_succ_fixpoint_iff
- \+ *theorem* zorn.chain_closure_total
- \- *lemma* zorn.chain_closure_total
- \+ *theorem* zorn.chain_insert
- \- *lemma* zorn.chain_insert
- \+ *theorem* zorn.chain_succ
- \- *lemma* zorn.chain_succ
- \+ *theorem* zorn.max_chain_spec
- \- *lemma* zorn.max_chain_spec
- \+ *theorem* zorn.succ_increasing
- \- *lemma* zorn.succ_increasing
- \+ *theorem* zorn.succ_spec
- \- *lemma* zorn.succ_spec
- \+ *theorem* zorn.super_of_not_max
- \- *lemma* zorn.super_of_not_max
- \+ *theorem* zorn.zorn
- \- *lemma* zorn.zorn
- \+ *theorem* zorn.zorn_weak_order
- \- *lemma* zorn.zorn_weak_order

Modified algebra/order.lean
- \+ *theorem* comp_le_comp_left_of_monotone
- \- *lemma* comp_le_comp_left_of_monotone
- \+ *theorem* le_dual_eq_le
- \- *lemma* le_dual_eq_le
- \+ *theorem* monotone_app
- \- *lemma* monotone_app
- \+ *theorem* monotone_comp
- \- *lemma* monotone_comp
- \+ *theorem* monotone_const
- \- *lemma* monotone_const
- \+ *theorem* monotone_id
- \- *lemma* monotone_id
- \+ *theorem* monotone_lam
- \- *lemma* monotone_lam

Modified data/bitvec.lean
- \+ *theorem* bitvec.bits_to_nat_to_list
- \- *lemma* bitvec.bits_to_nat_to_list
- \+ *theorem* bitvec.of_nat_succ
- \- *lemma* bitvec.of_nat_succ

Modified data/bool.lean
- \+ *theorem* bool.bxor_assoc
- \- *lemma* bool.bxor_assoc
- \+ *theorem* bool.bxor_comm
- \- *lemma* bool.bxor_comm
- \+ *theorem* bool.bxor_ff
- \- *lemma* bool.bxor_ff
- \+ *theorem* bool.bxor_left_comm
- \- *lemma* bool.bxor_left_comm
- \+ *theorem* bool.bxor_self
- \- *lemma* bool.bxor_self
- \+ *theorem* bool.bxor_tt
- \- *lemma* bool.bxor_tt
- \+ *theorem* bool.ff_bxor
- \- *lemma* bool.ff_bxor
- \+ *theorem* bool.ff_bxor_ff
- \- *lemma* bool.ff_bxor_ff
- \+ *theorem* bool.ff_bxor_tt
- \- *lemma* bool.ff_bxor_tt
- \+ *theorem* bool.tt_bxor
- \- *lemma* bool.tt_bxor
- \+ *theorem* bool.tt_bxor_ff
- \- *lemma* bool.tt_bxor_ff
- \+ *theorem* bool.tt_bxor_tt
- \- *lemma* bool.tt_bxor_tt

Modified data/fin.lean
- \+ *theorem* eq_of_lt_succ_of_not_lt
- \- *lemma* eq_of_lt_succ_of_not_lt
- \+ *theorem* lt_succ_of_lt
- \- *lemma* lt_succ_of_lt

Modified data/hash_map.lean
- \+ *theorem* bucket_array.foldl_eq_lem
- \- *lemma* bucket_array.foldl_eq_lem
- \- *theorem* hash_map.append_of_modify_aux
- \- *lemma* hash_map.insert_lemma
- \+ *theorem* hash_map.insert_theorem
- \- *theorem* hash_map.valid.modify_aux1
- \- *theorem* hash_map.valid.modify_aux2
- \- *theorem* hash_map.valid_aux.insert_lemma1

Modified data/int/basic.lean
- \+ *theorem* int.neg_add_neg
- \- *lemma* int.neg_add_neg

Modified data/list/basic.lean
- \+ *theorem* list.cons_inj
- \- *lemma* list.cons_inj
- \+ *theorem* list.cons_ne_nil
- \- *lemma* list.cons_ne_nil
- \+ *theorem* list.count_append
- \- *lemma* list.count_append
- \+ *theorem* list.count_concat
- \- *lemma* list.count_concat
- \+ *theorem* list.count_cons'
- \- *lemma* list.count_cons'
- \+ *theorem* list.count_cons
- \- *lemma* list.count_cons
- \+ *theorem* list.count_cons_ge_count
- \- *lemma* list.count_cons_ge_count
- \+ *theorem* list.count_cons_of_ne
- \- *lemma* list.count_cons_of_ne
- \+ *theorem* list.count_cons_self
- \- *lemma* list.count_cons_self
- \+ *theorem* list.count_eq_zero_of_not_mem
- \- *lemma* list.count_eq_zero_of_not_mem
- \+ *theorem* list.count_nil
- \- *lemma* list.count_nil
- \+ *theorem* list.count_pos_of_mem
- \- *lemma* list.count_pos_of_mem
- \+ *theorem* list.count_singleton
- \- *lemma* list.count_singleton
- \+ *theorem* list.head_eq_of_cons_eq
- \- *lemma* list.head_eq_of_cons_eq
- \+ *theorem* list.index_of_le_length
- \- *lemma* list.index_of_le_length
- \+ *theorem* list.index_of_lt_length
- \- *lemma* list.index_of_lt_length
- \+ *theorem* list.ith_succ
- \- *lemma* list.ith_succ
- \+ *theorem* list.ith_zero
- \- *lemma* list.ith_zero
- \+ *theorem* list.last_cons_cons
- \- *lemma* list.last_cons_cons
- \+ *theorem* list.last_singleton
- \- *lemma* list.last_singleton
- \+ *theorem* list.length_taken_le
- \- *lemma* list.length_taken_le
- \+ *theorem* list.mem_iff_count_pos
- \- *lemma* list.mem_iff_count_pos
- \+ *theorem* list.mem_of_count_pos
- \- *lemma* list.mem_of_count_pos
- \+ *theorem* list.not_mem_of_count_eq_zero
- \- *lemma* list.not_mem_of_count_eq_zero
- \+ *theorem* list.not_mem_of_index_of_eq_length
- \- *lemma* list.not_mem_of_index_of_eq_length
- \+ *theorem* list.tail_eq_of_cons_eq
- \- *lemma* list.tail_eq_of_cons_eq
- \+ *theorem* list.taken_all
- \- *lemma* list.taken_all
- \+ *theorem* list.taken_all_of_ge
- \- *lemma* list.taken_all_of_ge
- \+ *theorem* list.taken_cons
- \- *lemma* list.taken_cons
- \+ *theorem* list.taken_nil
- \- *lemma* list.taken_nil
- \+ *theorem* list.taken_zero
- \- *lemma* list.taken_zero

Modified data/list/comb.lean
- \+ *theorem* list.dmap_cons_of_neg
- \- *lemma* list.dmap_cons_of_neg
- \+ *theorem* list.dmap_cons_of_pos
- \- *lemma* list.dmap_cons_of_pos
- \+ *theorem* list.dmap_nil
- \- *lemma* list.dmap_nil
- \+ *theorem* list.exists_of_mem_dmap
- \- *lemma* list.exists_of_mem_dmap
- \+ *theorem* list.map_dmap_of_inv_of_pos
- \- *lemma* list.map_dmap_of_inv_of_pos
- \+ *theorem* list.mem_dmap
- \- *lemma* list.mem_dmap
- \+ *theorem* list.mem_of_dinj_of_mem_dmap
- \- *lemma* list.mem_of_dinj_of_mem_dmap
- \+ *theorem* list.not_mem_dmap_of_dinj_of_not_mem
- \- *lemma* list.not_mem_dmap_of_dinj_of_not_mem

Modified data/list/perm.lean
- \+ *theorem* list.perm.perm_insert_insert
- \- *lemma* list.perm.perm_insert_insert
- \+ *theorem* list.perm.perm_of_qeq
- \- *lemma* list.perm.perm_of_qeq

Modified data/list/set.lean
- \+ *theorem* list.disjoint.comm
- \- *lemma* list.disjoint.comm
- \+ *theorem* list.disjoint_append_of_disjoint_left
- \- *lemma* list.disjoint_append_of_disjoint_left
- \+ *theorem* list.disjoint_cons_of_not_mem_of_disjoint
- \- *lemma* list.disjoint_cons_of_not_mem_of_disjoint
- \+ *theorem* list.disjoint_left
- \- *lemma* list.disjoint_left
- \+ *theorem* list.disjoint_nil_left
- \- *lemma* list.disjoint_nil_left
- \+ *theorem* list.disjoint_nil_right
- \- *lemma* list.disjoint_nil_right
- \+ *theorem* list.disjoint_of_disjoint_append_left_left
- \- *lemma* list.disjoint_of_disjoint_append_left_left
- \+ *theorem* list.disjoint_of_disjoint_append_left_right
- \- *lemma* list.disjoint_of_disjoint_append_left_right
- \+ *theorem* list.disjoint_of_disjoint_append_right_left
- \- *lemma* list.disjoint_of_disjoint_append_right_left
- \+ *theorem* list.disjoint_of_disjoint_append_right_right
- \- *lemma* list.disjoint_of_disjoint_append_right_right
- \+ *theorem* list.disjoint_of_disjoint_cons_left
- \- *lemma* list.disjoint_of_disjoint_cons_left
- \+ *theorem* list.disjoint_of_disjoint_cons_right
- \- *lemma* list.disjoint_of_disjoint_cons_right
- \+ *theorem* list.disjoint_of_subset_left
- \- *lemma* list.disjoint_of_subset_left
- \+ *theorem* list.disjoint_of_subset_right
- \- *lemma* list.disjoint_of_subset_right
- \+ *theorem* list.disjoint_right
- \- *lemma* list.disjoint_right
- \+ *theorem* list.dmap_nodup_of_dinj
- \- *lemma* list.dmap_nodup_of_dinj
- \+ *theorem* list.erase_append_left
- \- *lemma* list.erase_append_left
- \+ *theorem* list.erase_append_right
- \- *lemma* list.erase_append_right
- \+ *theorem* list.erase_cons
- \- *lemma* list.erase_cons
- \+ *theorem* list.erase_cons_head
- \- *lemma* list.erase_cons_head
- \+ *theorem* list.erase_cons_tail
- \- *lemma* list.erase_cons_tail
- \+ *theorem* list.erase_nil
- \- *lemma* list.erase_nil
- \+ *theorem* list.erase_of_not_mem
- \- *lemma* list.erase_of_not_mem
- \+ *theorem* list.erase_sublist
- \- *lemma* list.erase_sublist
- \+ *theorem* list.erase_subset
- \- *lemma* list.erase_subset
- \+ *theorem* list.length_erase_of_mem
- \- *lemma* list.length_erase_of_mem
- \+ *theorem* list.upto_step
- \- *lemma* list.upto_step

Modified data/list/sort.lean
- \+ *theorem* nat.lt_succ_iff_le
- \- *lemma* nat.lt_succ_iff_le
- \+ *theorem* nat.succ_le_succ_iff
- \- *lemma* nat.succ_le_succ_iff

Modified data/nat/basic.lean
- \+ *theorem* nat.addl_succ_left
- \- *lemma* nat.addl_succ_left
- \+ *theorem* nat.addl_zero_left
- \- *lemma* nat.addl_zero_left
- \+ *theorem* nat.one_succ_zero
- \- *lemma* nat.one_succ_zero
- \+ *theorem* nat.zero_has_zero
- \- *lemma* nat.zero_has_zero

Modified data/nat/gcd.lean
- \+ *theorem* nat.gcd_eq_one_of_coprime
- \- *lemma* nat.gcd_eq_one_of_coprime

Modified data/nat/sub.lean
- \+ *theorem* nat.dist_pos_of_ne
- \- *lemma* nat.dist_pos_of_ne
- \+ *theorem* nat.dist_succ_succ
- \- *lemma* nat.dist_succ_succ

Modified data/num/lemmas.lean
- \+ *theorem* num.bitwise_to_nat
- \- *lemma* num.bitwise_to_nat
- \+ *theorem* num.land_to_nat
- \- *lemma* num.land_to_nat
- \+ *theorem* num.ldiff_to_nat
- \- *lemma* num.ldiff_to_nat
- \+ *theorem* num.lor_to_nat
- \- *lemma* num.lor_to_nat
- \+ *theorem* num.lxor_to_nat
- \- *lemma* num.lxor_to_nat
- \+ *theorem* num.shiftl_to_nat
- \- *lemma* num.shiftl_to_nat
- \+ *theorem* num.shiftr_to_nat
- \- *lemma* num.shiftr_to_nat
- \+ *theorem* num.test_bit_to_nat
- \- *lemma* num.test_bit_to_nat
- \- *lemma* pos_num.cmp_dec_lemma
- \+ *theorem* pos_num.cmp_dec_theorem

Modified data/rat.lean
- \+ *theorem* linear_order_cases_on_eq
- \- *lemma* linear_order_cases_on_eq
- \+ *theorem* linear_order_cases_on_gt
- \- *lemma* linear_order_cases_on_gt
- \+ *theorem* linear_order_cases_on_lt
- \- *lemma* linear_order_cases_on_lt
- \+ *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \- *lemma* mul_nonneg_iff_right_nonneg_of_pos
- \+ *theorem* not_antimono
- \- *lemma* not_antimono

Modified data/seq/computation.lean
- \+ *theorem* computation.destruct_map
- \- *lemma* computation.destruct_map
- \+ *theorem* computation.eq_of_bisim
- \- *lemma* computation.eq_of_bisim
- \+ *theorem* computation.lift_rel_rec.lem
- \- *lemma* computation.lift_rel_rec.lem
- \+ *theorem* computation.map_comp
- \- *lemma* computation.map_comp
- \+ *theorem* computation.map_ret'
- \- *lemma* computation.map_ret'
- \+ *theorem* computation.map_ret
- \- *lemma* computation.map_ret
- \+ *theorem* computation.map_think'
- \- *lemma* computation.map_think'
- \+ *theorem* computation.map_think
- \- *lemma* computation.map_think
- \+ *theorem* computation.ret_bind
- \- *lemma* computation.ret_bind
- \+ *theorem* computation.return_def
- \- *lemma* computation.return_def
- \+ *theorem* computation.think_bind
- \- *lemma* computation.think_bind

Modified data/seq/parallel.lean
- \+ *theorem* computation.map_parallel
- \- *lemma* computation.map_parallel
- \+ *theorem* computation.parallel_congr_lem
- \- *lemma* computation.parallel_congr_lem
- \+ *theorem* computation.terminates_parallel.aux
- \- *lemma* computation.terminates_parallel.aux

Modified data/seq/seq.lean
- \+ *theorem* seq.append_assoc
- \- *lemma* seq.append_assoc
- \+ *theorem* seq.append_nil
- \- *lemma* seq.append_nil
- \+ *theorem* seq.coinduction2
- \- *lemma* seq.coinduction2
- \+ *theorem* seq.coinduction
- \- *lemma* seq.coinduction
- \+ *theorem* seq.cons_append
- \- *lemma* seq.cons_append
- \+ *theorem* seq.eq_of_bisim
- \- *lemma* seq.eq_of_bisim
- \+ *theorem* seq.eq_or_mem_of_mem_cons
- \- *lemma* seq.eq_or_mem_of_mem_cons
- \+ *theorem* seq.exists_of_mem_map
- \- *lemma* seq.exists_of_mem_map
- \+ *theorem* seq.join_append
- \- *lemma* seq.join_append
- \+ *theorem* seq.join_cons
- \- *lemma* seq.join_cons
- \+ *theorem* seq.join_cons_cons
- \- *lemma* seq.join_cons_cons
- \+ *theorem* seq.join_cons_nil
- \- *lemma* seq.join_cons_nil
- \+ *theorem* seq.join_nil
- \- *lemma* seq.join_nil
- \+ *theorem* seq.map_comp
- \- *lemma* seq.map_comp
- \+ *theorem* seq.map_cons
- \- *lemma* seq.map_cons
- \+ *theorem* seq.map_id
- \- *lemma* seq.map_id
- \+ *theorem* seq.map_nil
- \- *lemma* seq.map_nil
- \+ *theorem* seq.map_nth
- \- *lemma* seq.map_nth
- \+ *theorem* seq.map_tail
- \- *lemma* seq.map_tail
- \+ *theorem* seq.mem_cons
- \- *lemma* seq.mem_cons
- \+ *theorem* seq.mem_cons_iff
- \- *lemma* seq.mem_cons_iff
- \+ *theorem* seq.mem_cons_of_mem
- \- *lemma* seq.mem_cons_of_mem
- \+ *theorem* seq.nil_append
- \- *lemma* seq.nil_append
- \+ *theorem* seq1.join_cons
- \- *lemma* seq1.join_cons
- \+ *theorem* seq1.join_nil
- \- *lemma* seq1.join_nil

Modified data/seq/wseq.lean
- \+ *theorem* wseq.append_assoc
- \- *lemma* wseq.append_assoc
- \+ *theorem* wseq.append_nil
- \- *lemma* wseq.append_nil
- \+ *theorem* wseq.cons_append
- \- *lemma* wseq.cons_append
- \+ *theorem* wseq.destruct_append
- \- *lemma* wseq.destruct_append
- \+ *theorem* wseq.destruct_join
- \- *lemma* wseq.destruct_join
- \+ *theorem* wseq.destruct_map
- \- *lemma* wseq.destruct_map
- \+ *theorem* wseq.exists_of_mem_map
- \- *lemma* wseq.exists_of_mem_map
- \+ *theorem* wseq.join_append
- \- *lemma* wseq.join_append
- \+ *theorem* wseq.map_comp
- \- *lemma* wseq.map_comp
- \+ *theorem* wseq.map_cons
- \- *lemma* wseq.map_cons
- \+ *theorem* wseq.map_nil
- \- *lemma* wseq.map_nil
- \+ *theorem* wseq.map_think
- \- *lemma* wseq.map_think
- \+ *theorem* wseq.nil_append
- \- *lemma* wseq.nil_append
- \+ *theorem* wseq.think_append
- \- *lemma* wseq.think_append

Modified data/set/basic.lean
- \+ *theorem* set.set_of_false
- \- *lemma* set.set_of_false

Modified data/set/finite.lean
- \+ *theorem* set.finite_image
- \- *lemma* set.finite_image
- \+ *theorem* set.finite_insert
- \- *lemma* set.finite_insert
- \+ *theorem* set.finite_sUnion
- \- *lemma* set.finite_sUnion
- \+ *theorem* set.finite_singleton
- \- *lemma* set.finite_singleton
- \+ *theorem* set.finite_subset
- \- *lemma* set.finite_subset
- \+ *theorem* set.finite_union
- \- *lemma* set.finite_union

Modified data/stream.lean
- \+ *theorem* stream.all_def
- \- *lemma* stream.all_def
- \+ *theorem* stream.any_def
- \- *lemma* stream.any_def
- \+ *theorem* stream.append_append_stream
- \- *lemma* stream.append_append_stream
- \+ *theorem* stream.append_approx_drop
- \- *lemma* stream.append_approx_drop
- \+ *theorem* stream.append_stream_head_tail
- \- *lemma* stream.append_stream_head_tail
- \+ *theorem* stream.approx_succ
- \- *lemma* stream.approx_succ
- \+ *theorem* stream.approx_zero
- \- *lemma* stream.approx_zero
- \+ *theorem* stream.bisim_simple
- \- *lemma* stream.bisim_simple
- \+ *theorem* stream.coinduction
- \- *lemma* stream.coinduction
- \+ *theorem* stream.composition
- \- *lemma* stream.composition
- \+ *theorem* stream.cons_append_stream
- \- *lemma* stream.cons_append_stream
- \+ *theorem* stream.cons_nth_inits_core
- \- *lemma* stream.cons_nth_inits_core
- \+ *theorem* stream.const_eq
- \- *lemma* stream.const_eq
- \+ *theorem* stream.corec'_eq
- \- *lemma* stream.corec'_eq
- \+ *theorem* stream.corec_def
- \- *lemma* stream.corec_def
- \+ *theorem* stream.corec_eq
- \- *lemma* stream.corec_eq
- \+ *theorem* stream.corec_id_f_eq_iterate
- \- *lemma* stream.corec_id_f_eq_iterate
- \+ *theorem* stream.corec_id_id_eq_const
- \- *lemma* stream.corec_id_id_eq_const
- \+ *theorem* stream.cycle_eq
- \- *lemma* stream.cycle_eq
- \+ *theorem* stream.cycle_singleton
- \- *lemma* stream.cycle_singleton
- \+ *theorem* stream.drop_append_stream
- \- *lemma* stream.drop_append_stream
- \+ *theorem* stream.drop_const
- \- *lemma* stream.drop_const
- \+ *theorem* stream.drop_drop
- \- *lemma* stream.drop_drop
- \+ *theorem* stream.drop_map
- \- *lemma* stream.drop_map
- \+ *theorem* stream.drop_succ
- \- *lemma* stream.drop_succ
- \+ *theorem* stream.drop_zip
- \- *lemma* stream.drop_zip
- \+ *theorem* stream.eq_of_bisim
- \- *lemma* stream.eq_of_bisim
- \+ *theorem* stream.eq_or_mem_of_mem_cons
- \- *lemma* stream.eq_or_mem_of_mem_cons
- \+ *theorem* stream.even_cons_cons
- \- *lemma* stream.even_cons_cons
- \+ *theorem* stream.even_interleave
- \- *lemma* stream.even_interleave
- \+ *theorem* stream.even_tail
- \- *lemma* stream.even_tail
- \+ *theorem* stream.exists_of_mem_map
- \- *lemma* stream.exists_of_mem_map
- \+ *theorem* stream.head_cons
- \- *lemma* stream.head_cons
- \+ *theorem* stream.head_even
- \- *lemma* stream.head_even
- \+ *theorem* stream.head_iterate
- \- *lemma* stream.head_iterate
- \+ *theorem* stream.head_map
- \- *lemma* stream.head_map
- \+ *theorem* stream.head_zip
- \- *lemma* stream.head_zip
- \+ *theorem* stream.homomorphism
- \- *lemma* stream.homomorphism
- \+ *theorem* stream.identity
- \- *lemma* stream.identity
- \+ *theorem* stream.inits_core_eq
- \- *lemma* stream.inits_core_eq
- \+ *theorem* stream.inits_eq
- \- *lemma* stream.inits_eq
- \+ *theorem* stream.inits_tail
- \- *lemma* stream.inits_tail
- \+ *theorem* stream.interchange
- \- *lemma* stream.interchange
- \+ *theorem* stream.interleave_eq
- \- *lemma* stream.interleave_eq
- \+ *theorem* stream.interleave_even_odd
- \- *lemma* stream.interleave_even_odd
- \+ *theorem* stream.interleave_tail_tail
- \- *lemma* stream.interleave_tail_tail
- \+ *theorem* stream.iterate_eq
- \- *lemma* stream.iterate_eq
- \+ *theorem* stream.iterate_id
- \- *lemma* stream.iterate_id
- \+ *theorem* stream.map_append_stream
- \- *lemma* stream.map_append_stream
- \+ *theorem* stream.map_cons
- \- *lemma* stream.map_cons
- \+ *theorem* stream.map_const
- \- *lemma* stream.map_const
- \+ *theorem* stream.map_eq
- \- *lemma* stream.map_eq
- \+ *theorem* stream.map_eq_apply
- \- *lemma* stream.map_eq_apply
- \+ *theorem* stream.map_id
- \- *lemma* stream.map_id
- \+ *theorem* stream.map_iterate
- \- *lemma* stream.map_iterate
- \+ *theorem* stream.map_map
- \- *lemma* stream.map_map
- \+ *theorem* stream.map_tail
- \- *lemma* stream.map_tail
- \+ *theorem* stream.mem_append_stream_left
- \- *lemma* stream.mem_append_stream_left
- \+ *theorem* stream.mem_append_stream_right
- \- *lemma* stream.mem_append_stream_right
- \+ *theorem* stream.mem_cons
- \- *lemma* stream.mem_cons
- \+ *theorem* stream.mem_cons_of_mem
- \- *lemma* stream.mem_cons_of_mem
- \+ *theorem* stream.mem_const
- \- *lemma* stream.mem_const
- \+ *theorem* stream.mem_cycle
- \- *lemma* stream.mem_cycle
- \+ *theorem* stream.mem_interleave_left
- \- *lemma* stream.mem_interleave_left
- \+ *theorem* stream.mem_interleave_right
- \- *lemma* stream.mem_interleave_right
- \+ *theorem* stream.mem_map
- \- *lemma* stream.mem_map
- \+ *theorem* stream.mem_of_mem_even
- \- *lemma* stream.mem_of_mem_even
- \+ *theorem* stream.mem_of_mem_odd
- \- *lemma* stream.mem_of_mem_odd
- \+ *theorem* stream.mem_of_nth_eq
- \- *lemma* stream.mem_of_nth_eq
- \+ *theorem* stream.nats_eq
- \- *lemma* stream.nats_eq
- \+ *theorem* stream.nil_append_stream
- \- *lemma* stream.nil_append_stream
- \+ *theorem* stream.nth_approx
- \- *lemma* stream.nth_approx
- \+ *theorem* stream.nth_const
- \- *lemma* stream.nth_const
- \+ *theorem* stream.nth_drop
- \- *lemma* stream.nth_drop
- \+ *theorem* stream.nth_even
- \- *lemma* stream.nth_even
- \+ *theorem* stream.nth_inits
- \- *lemma* stream.nth_inits
- \+ *theorem* stream.nth_interleave_left
- \- *lemma* stream.nth_interleave_left
- \+ *theorem* stream.nth_interleave_right
- \- *lemma* stream.nth_interleave_right
- \+ *theorem* stream.nth_map
- \- *lemma* stream.nth_map
- \+ *theorem* stream.nth_nats
- \- *lemma* stream.nth_nats
- \+ *theorem* stream.nth_odd
- \- *lemma* stream.nth_odd
- \+ *theorem* stream.nth_of_bisim
- \- *lemma* stream.nth_of_bisim
- \+ *theorem* stream.nth_succ
- \- *lemma* stream.nth_succ
- \+ *theorem* stream.nth_succ_iterate
- \- *lemma* stream.nth_succ_iterate
- \+ *theorem* stream.nth_tails
- \- *lemma* stream.nth_tails
- \+ *theorem* stream.nth_unfolds_head_tail
- \- *lemma* stream.nth_unfolds_head_tail
- \+ *theorem* stream.nth_zero_cons
- \- *lemma* stream.nth_zero_cons
- \+ *theorem* stream.nth_zero_iterate
- \- *lemma* stream.nth_zero_iterate
- \+ *theorem* stream.nth_zip
- \- *lemma* stream.nth_zip
- \+ *theorem* stream.odd_eq
- \- *lemma* stream.odd_eq
- \+ *theorem* stream.tail_cons
- \- *lemma* stream.tail_cons
- \+ *theorem* stream.tail_const
- \- *lemma* stream.tail_const
- \+ *theorem* stream.tail_drop
- \- *lemma* stream.tail_drop
- \+ *theorem* stream.tail_eq_drop
- \- *lemma* stream.tail_eq_drop
- \+ *theorem* stream.tail_even
- \- *lemma* stream.tail_even
- \+ *theorem* stream.tail_inits
- \- *lemma* stream.tail_inits
- \+ *theorem* stream.tail_interleave
- \- *lemma* stream.tail_interleave
- \+ *theorem* stream.tail_iterate
- \- *lemma* stream.tail_iterate
- \+ *theorem* stream.tail_map
- \- *lemma* stream.tail_map
- \+ *theorem* stream.tail_zip
- \- *lemma* stream.tail_zip
- \+ *theorem* stream.tails_eq
- \- *lemma* stream.tails_eq
- \+ *theorem* stream.tails_eq_iterate
- \- *lemma* stream.tails_eq_iterate
- \- *lemma* stream.take_lemma
- \+ *theorem* stream.take_theorem
- \+ *theorem* stream.unfolds_eq
- \- *lemma* stream.unfolds_eq
- \+ *theorem* stream.unfolds_head_eq
- \- *lemma* stream.unfolds_head_eq
- \+ *theorem* stream.zip_eq
- \- *lemma* stream.zip_eq
- \+ *theorem* stream.zip_inits_tails
- \- *lemma* stream.zip_inits_tails

Modified data/vector.lean
- \+ *theorem* vector.map_cons
- \- *lemma* vector.map_cons
- \+ *theorem* vector.map_nil
- \- *lemma* vector.map_nil
- \+ *theorem* vector.to_list_append
- \- *lemma* vector.to_list_append
- \+ *theorem* vector.to_list_cons
- \- *lemma* vector.to_list_cons
- \+ *theorem* vector.to_list_drop
- \- *lemma* vector.to_list_drop
- \+ *theorem* vector.to_list_length
- \- *lemma* vector.to_list_length
- \+ *theorem* vector.to_list_mk
- \- *lemma* vector.to_list_mk
- \+ *theorem* vector.to_list_nil
- \- *lemma* vector.to_list_nil
- \+ *theorem* vector.to_list_take
- \- *lemma* vector.to_list_take

Modified logic/basic.lean
- \+ *theorem* eq_iff_le_and_le
- \- *lemma* eq_iff_le_and_le
- \+ *theorem* forall_eq
- \- *lemma* forall_eq
- \+ *theorem* not_imp_iff_not_imp
- \- *lemma* not_imp_iff_not_imp
- \+ *theorem* or_imp_iff_and_imp
- \- *lemma* or_imp_iff_and_imp
- \+ *theorem* or_of_not_implies'
- \- *lemma* or_of_not_implies'
- \+ *theorem* or_of_not_implies
- \- *lemma* or_of_not_implies
- \+ *theorem* prod.exists
- \- *lemma* prod.exists
- \+ *theorem* prod.forall
- \- *lemma* prod.forall
- \+ *theorem* prod.mk.inj_iff
- \- *lemma* prod.mk.inj_iff
- \+ *theorem* set_of_subset_set_of
- \- *lemma* set_of_subset_set_of

Modified tactic/converter/binders.lean
- \+ *theorem* Inf_image
- \- *lemma* Inf_image
- \+ *theorem* Sup_image
- \- *lemma* Sup_image
- \+ *theorem* mem_image
- \- *lemma* mem_image
- \+ *theorem* {u
- \- *lemma* {u

Modified tests/examples.lean
- \+ *theorem* mem_set_of
- \- *lemma* mem_set_of

Modified tests/finish2.lean
- \+ *theorem* NoMember
- \- *lemma* NoMember

Modified topology/continuity.lean
- \+ *theorem* closure_prod_eq
- \- *lemma* closure_prod_eq
- \+ *theorem* compact_pi_infinite
- \- *lemma* compact_pi_infinite
- \+ *theorem* continuous_Inf_dom
- \- *lemma* continuous_Inf_dom
- \+ *theorem* continuous_Inf_rng
- \- *lemma* continuous_Inf_rng
- \+ *theorem* continuous_Prop
- \- *lemma* continuous_Prop
- \+ *theorem* continuous_bot
- \- *lemma* continuous_bot
- \+ *theorem* continuous_coinduced_dom
- \- *lemma* continuous_coinduced_dom
- \+ *theorem* continuous_coinduced_rng
- \- *lemma* continuous_coinduced_rng
- \+ *theorem* continuous_compose
- \- *lemma* continuous_compose
- \+ *theorem* continuous_eq_le_coinduced
- \- *lemma* continuous_eq_le_coinduced
- \+ *theorem* continuous_fst
- \- *lemma* continuous_fst
- \+ *theorem* continuous_generated_from
- \- *lemma* continuous_generated_from
- \+ *theorem* continuous_id
- \- *lemma* continuous_id
- \+ *theorem* continuous_iff_induced_le
- \- *lemma* continuous_iff_induced_le
- \+ *theorem* continuous_iff_towards
- \- *lemma* continuous_iff_towards
- \+ *theorem* continuous_induced_dom
- \- *lemma* continuous_induced_dom
- \+ *theorem* continuous_induced_rng
- \- *lemma* continuous_induced_rng
- \+ *theorem* continuous_inf_dom
- \- *lemma* continuous_inf_dom
- \+ *theorem* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_left
- \+ *theorem* continuous_inf_rng_right
- \- *lemma* continuous_inf_rng_right
- \+ *theorem* continuous_infi_dom
- \- *lemma* continuous_infi_dom
- \+ *theorem* continuous_infi_rng
- \- *lemma* continuous_infi_rng
- \+ *theorem* continuous_inl
- \- *lemma* continuous_inl
- \+ *theorem* continuous_inr
- \- *lemma* continuous_inr
- \+ *theorem* continuous_prod_mk
- \- *lemma* continuous_prod_mk
- \+ *theorem* continuous_snd
- \- *lemma* continuous_snd
- \+ *theorem* continuous_subtype_mk
- \- *lemma* continuous_subtype_mk
- \+ *theorem* continuous_subtype_nhds_cover
- \- *lemma* continuous_subtype_nhds_cover
- \+ *theorem* continuous_subtype_val
- \- *lemma* continuous_subtype_val
- \+ *theorem* continuous_sum_rec
- \- *lemma* continuous_sum_rec
- \+ *theorem* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_left
- \+ *theorem* continuous_sup_dom_right
- \- *lemma* continuous_sup_dom_right
- \+ *theorem* continuous_sup_rng
- \- *lemma* continuous_sup_rng
- \+ *theorem* continuous_top
- \- *lemma* continuous_top
- \+ *theorem* false_neq_true
- \- *lemma* false_neq_true
- \+ *theorem* map_nhds_induced_eq
- \- *lemma* map_nhds_induced_eq
- \+ *theorem* map_nhds_subtype_val_eq
- \- *lemma* map_nhds_subtype_val_eq
- \+ *theorem* nhds_induced_eq_vmap
- \- *lemma* nhds_induced_eq_vmap
- \+ *theorem* nhds_pi
- \- *lemma* nhds_pi
- \+ *theorem* nhds_prod_eq
- \- *lemma* nhds_prod_eq
- \+ *theorem* open_induced
- \- *lemma* open_induced
- \+ *theorem* open_set_prod
- \- *lemma* open_set_prod
- \+ *theorem* open_singleton_true
- \- *lemma* open_singleton_true
- \+ *theorem* prod_eq_generate_from
- \- *lemma* prod_eq_generate_from
- \+ *theorem* subtype.val_image
- \- *lemma* subtype.val_image
- \+ *theorem* univ_eq_true_false
- \- *lemma* univ_eq_true_false

Modified topology/topological_space.lean
- \+ *theorem* closed_Inter
- \- *lemma* closed_Inter
- \+ *theorem* closed_Union_of_locally_finite
- \- *lemma* closed_Union_of_locally_finite
- \+ *theorem* closed_closure
- \- *lemma* closed_closure
- \+ *theorem* closed_compl_iff_open
- \- *lemma* closed_compl_iff_open
- \+ *theorem* closed_empty
- \- *lemma* closed_empty
- \+ *theorem* closed_iff_nhds
- \- *lemma* closed_iff_nhds
- \+ *theorem* closed_sInter
- \- *lemma* closed_sInter
- \+ *theorem* closed_union
- \- *lemma* closed_union
- \+ *theorem* closed_univ
- \- *lemma* closed_univ
- \+ *theorem* closure_closure
- \- *lemma* closure_closure
- \+ *theorem* closure_compl_eq
- \- *lemma* closure_compl_eq
- \+ *theorem* closure_empty
- \- *lemma* closure_empty
- \+ *theorem* closure_eq_compl_interior_compl
- \- *lemma* closure_eq_compl_interior_compl
- \+ *theorem* closure_eq_iff_closed
- \- *lemma* closure_eq_iff_closed
- \+ *theorem* closure_eq_nhds
- \- *lemma* closure_eq_nhds
- \+ *theorem* closure_eq_of_closed
- \- *lemma* closure_eq_of_closed
- \+ *theorem* closure_minimal
- \- *lemma* closure_minimal
- \+ *theorem* closure_mono
- \- *lemma* closure_mono
- \+ *theorem* closure_subset_iff_subset_of_closed
- \- *lemma* closure_subset_iff_subset_of_closed
- \+ *theorem* closure_union
- \- *lemma* closure_union
- \+ *theorem* closure_univ
- \- *lemma* closure_univ
- \+ *theorem* compact_adherence_nhdset
- \- *lemma* compact_adherence_nhdset
- \+ *theorem* compact_iff_ultrafilter_le_nhds
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \+ *theorem* eq_of_nhds_eq_nhds
- \- *lemma* eq_of_nhds_eq_nhds
- \+ *theorem* eq_of_nhds_neq_bot
- \- *lemma* eq_of_nhds_neq_bot
- \+ *theorem* finite_subcover_of_compact
- \- *lemma* finite_subcover_of_compact
- \+ *theorem* generate_from_le
- \- *lemma* generate_from_le
- \+ *theorem* interior_compl_eq
- \- *lemma* interior_compl_eq
- \+ *theorem* interior_empty
- \- *lemma* interior_empty
- \+ *theorem* interior_eq_iff_open
- \- *lemma* interior_eq_iff_open
- \+ *theorem* interior_eq_nhds
- \- *lemma* interior_eq_nhds
- \+ *theorem* interior_eq_of_open
- \- *lemma* interior_eq_of_open
- \+ *theorem* interior_inter
- \- *lemma* interior_inter
- \+ *theorem* interior_interior
- \- *lemma* interior_interior
- \+ *theorem* interior_maximal
- \- *lemma* interior_maximal
- \+ *theorem* interior_mono
- \- *lemma* interior_mono
- \+ *theorem* interior_subset
- \- *lemma* interior_subset
- \+ *theorem* interior_subset_closure
- \- *lemma* interior_subset_closure
- \+ *theorem* interior_union_closed_of_interior_empty
- \- *lemma* interior_union_closed_of_interior_empty
- \+ *theorem* interior_univ
- \- *lemma* interior_univ
- \+ *theorem* le_of_nhds_le_nhds
- \- *lemma* le_of_nhds_le_nhds
- \+ *theorem* map_nhds
- \- *lemma* map_nhds
- \+ *theorem* mem_nhds_sets
- \- *lemma* mem_nhds_sets
- \+ *theorem* mem_nhds_sets_iff
- \- *lemma* mem_nhds_sets_iff
- \+ *theorem* nhds_mono
- \- *lemma* nhds_mono
- \+ *theorem* nhds_neq_bot
- \- *lemma* nhds_neq_bot
- \+ *theorem* nhds_sets
- \- *lemma* nhds_sets
- \+ *theorem* nhds_supr
- \- *lemma* nhds_supr
- \+ *theorem* open_Union
- \- *lemma* open_Union
- \+ *theorem* open_compl_iff_closed
- \- *lemma* open_compl_iff_closed
- \+ *theorem* open_diff
- \- *lemma* open_diff
- \+ *theorem* open_empty
- \- *lemma* open_empty
- \+ *theorem* open_iff_nhds
- \- *lemma* open_iff_nhds
- \+ *theorem* open_inter
- \- *lemma* open_inter
- \+ *theorem* open_interior
- \- *lemma* open_interior
- \+ *theorem* open_sUnion
- \- *lemma* open_sUnion
- \+ *theorem* open_univ
- \- *lemma* open_univ
- \+ *theorem* return_le_nhds
- \- *lemma* return_le_nhds
- \+ *theorem* subset_closure
- \- *lemma* subset_closure
- \+ *theorem* subset_interior_iff_subset_of_open
- \- *lemma* subset_interior_iff_subset_of_open
- \+ *theorem* sup_eq_generate_from
- \- *lemma* sup_eq_generate_from
- \+ *theorem* supr_eq_generate_from
- \- *lemma* supr_eq_generate_from
- \+ *theorem* t2_space_top
- \- *lemma* t2_space_top
- \+ *theorem* topological_space.nhds_generate_from
- \- *lemma* topological_space.nhds_generate_from
- \+ *theorem* topological_space_eq
- \- *lemma* topological_space_eq

Modified topology/uniform_space.lean
- \+ *theorem* Cauchy.monotone_gen
- \- *lemma* Cauchy.monotone_gen
- \+ *theorem* Cauchy.pure_cauchy_dense
- \- *lemma* Cauchy.pure_cauchy_dense
- \+ *theorem* Cauchy.uniform_embedding_pure_cauchy
- \- *lemma* Cauchy.uniform_embedding_pure_cauchy
- \+ *theorem* cauchy_downwards
- \- *lemma* cauchy_downwards
- \+ *theorem* cauchy_map
- \- *lemma* cauchy_map
- \+ *theorem* cauchy_nhds
- \- *lemma* cauchy_nhds
- \+ *theorem* cauchy_of_totally_bounded_of_ultrafilter
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *theorem* cauchy_pure
- \- *lemma* cauchy_pure
- \+ *theorem* cauchy_vmap
- \- *lemma* cauchy_vmap
- \+ *theorem* closure_eq_inter_uniformity
- \- *lemma* closure_eq_inter_uniformity
- \+ *theorem* comp_le_uniformity3
- \- *lemma* comp_le_uniformity3
- \+ *theorem* comp_le_uniformity
- \- *lemma* comp_le_uniformity
- \+ *theorem* comp_mem_uniformity_sets
- \- *lemma* comp_mem_uniformity_sets
- \+ *theorem* comp_symm_of_uniformity
- \- *lemma* comp_symm_of_uniformity
- \+ *theorem* compact_of_totally_bounded_closed
- \- *lemma* compact_of_totally_bounded_closed
- \+ *theorem* compact_of_totally_bounded_complete
- \- *lemma* compact_of_totally_bounded_complete
- \+ *theorem* complete_of_closed
- \- *lemma* complete_of_closed
- \+ *theorem* complete_space_extension
- \- *lemma* complete_space_extension
- \+ *theorem* complete_space_separation
- \- *lemma* complete_space_separation
- \+ *theorem* continuous_of_uniform
- \- *lemma* continuous_of_uniform
- \+ *theorem* id_comp_rel
- \- *lemma* id_comp_rel
- \+ *theorem* interior_mem_uniformity
- \- *lemma* interior_mem_uniformity
- \+ *theorem* le_nhds_iff_adhp_of_cauchy
- \- *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *theorem* le_nhds_of_cauchy_adhp
- \- *lemma* le_nhds_of_cauchy_adhp
- \+ *theorem* lift_nhds_left
- \- *lemma* lift_nhds_left
- \+ *theorem* lift_nhds_right
- \- *lemma* lift_nhds_right
- \+ *theorem* mem_nhds_left
- \- *lemma* mem_nhds_left
- \+ *theorem* mem_nhds_right
- \- *lemma* mem_nhds_right
- \+ *theorem* mem_nhds_uniformity_iff
- \- *lemma* mem_nhds_uniformity_iff
- \+ *theorem* monotone_comp_rel
- \- *lemma* monotone_comp_rel
- \+ *theorem* nhds_eq_uniformity
- \- *lemma* nhds_eq_uniformity
- \+ *theorem* nhds_eq_uniformity_prod
- \- *lemma* nhds_eq_uniformity_prod
- \+ *theorem* nhds_nhds_eq_uniformity_uniformity_prod
- \- *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *theorem* nhdset_of_mem_uniformity
- \- *lemma* nhdset_of_mem_uniformity
- \+ *theorem* prod_mk_mem_comp_rel
- \- *lemma* prod_mk_mem_comp_rel
- \+ *theorem* refl_le_uniformity
- \- *lemma* refl_le_uniformity
- \+ *theorem* refl_mem_uniformity
- \- *lemma* refl_mem_uniformity
- \+ *theorem* separated_equiv
- \- *lemma* separated_equiv
- \+ *theorem* supr_uniformity
- \- *lemma* supr_uniformity
- \+ *theorem* swap_id_rel
- \- *lemma* swap_id_rel
- \+ *theorem* symm_le_uniformity
- \- *lemma* symm_le_uniformity
- \+ *theorem* symm_of_uniformity
- \- *lemma* symm_of_uniformity
- \+ *theorem* to_topological_space_bot
- \- *lemma* to_topological_space_bot
- \+ *theorem* to_topological_space_mono
- \- *lemma* to_topological_space_mono
- \+ *theorem* to_topological_space_supr
- \- *lemma* to_topological_space_supr
- \+ *theorem* to_topological_space_top
- \- *lemma* to_topological_space_top
- \+ *theorem* to_topological_space_vmap
- \- *lemma* to_topological_space_vmap
- \+ *theorem* totally_bounded_iff_filter
- \- *lemma* totally_bounded_iff_filter
- \+ *theorem* totally_bounded_iff_ultrafilter
- \- *lemma* totally_bounded_iff_ultrafilter
- \+ *theorem* uniform_continuous_of_embedding
- \- *lemma* uniform_continuous_of_embedding
- \+ *theorem* uniform_continuous_quotient_mk
- \- *lemma* uniform_continuous_quotient_mk
- \+ *theorem* uniform_continuous_uniformly_extend
- \- *lemma* uniform_continuous_uniformly_extend
- \+ *theorem* uniform_continuous_vmap
- \- *lemma* uniform_continuous_vmap
- \+ *theorem* uniform_space_eq
- \- *lemma* uniform_space_eq
- \+ *theorem* uniformity_eq_symm
- \- *lemma* uniformity_eq_symm
- \+ *theorem* uniformity_eq_uniformity_closure
- \- *lemma* uniformity_eq_uniformity_closure
- \+ *theorem* uniformity_eq_uniformity_interior
- \- *lemma* uniformity_eq_uniformity_interior
- \+ *theorem* uniformity_le_symm
- \- *lemma* uniformity_le_symm
- \+ *theorem* uniformity_lift_le_comp
- \- *lemma* uniformity_lift_le_comp
- \+ *theorem* uniformity_lift_le_swap
- \- *lemma* uniformity_lift_le_swap
- \+ *theorem* uniformly_extend_of_emb
- \- *lemma* uniformly_extend_of_emb
- \+ *theorem* uniformly_extend_spec
- \- *lemma* uniformly_extend_spec
- \+ *theorem* uniformly_extend_unique
- \- *lemma* uniformly_extend_unique
- \+ *theorem* vmap_quotient_le_uniformity
- \- *lemma* vmap_quotient_le_uniformity



## [2017-07-23 18:13:37+01:00](https://github.com/leanprover-community/mathlib/commit/b9f1d64)
refactor(*): use . instead of ^.
#### Estimated changes
Modified algebra/group.lean


Modified algebra/lattice/basic.lean


Modified algebra/lattice/boolean_algebra.lean


Modified algebra/lattice/complete_boolean_algebra.lean


Modified algebra/lattice/complete_lattice.lean


Modified algebra/lattice/filter.lean
- \+/\- *lemma* filter.bind_mono
- \+/\- *lemma* filter.empty_in_sets_eq_bot
- \+/\- *lemma* filter.filter_eq
- \+/\- *lemma* filter.inhabited_of_mem_sets
- \+/\- *lemma* filter.inter_mem_sets
- \+/\- *lemma* filter.le_principal_iff
- \+/\- *lemma* filter.lift'_cong
- \+/\- *lemma* filter.lift'_mono'
- \+/\- *lemma* filter.lift'_mono
- \+/\- *lemma* filter.lift'_neq_bot_iff
- \+/\- *lemma* filter.lift_mono'
- \+/\- *lemma* filter.lift_mono
- \+/\- *lemma* filter.lift_neq_bot_iff
- \+/\- *lemma* filter.lift_sets_eq
- \+/\- *lemma* filter.map_lift'_eq
- \+/\- *lemma* filter.mem_bot_sets
- \+/\- *lemma* filter.mem_join_sets
- \+/\- *lemma* filter.mem_lift'
- \+/\- *lemma* filter.mem_lift'_iff
- \+/\- *lemma* filter.mem_lift
- \+/\- *lemma* filter.mem_principal_sets
- \+/\- *lemma* filter.mem_return_sets
- \+/\- *lemma* filter.monotone_mem_sets
- \+/\- *lemma* filter.principal_le_lift'
- \+/\- *lemma* filter.prod_same_eq
- \+/\- *lemma* filter.supr_sets_eq
- \+/\- *lemma* filter.univ_mem_sets'
- \+/\- *lemma* filter.univ_mem_sets

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
- \+/\- *lemma* nhds_sets
- \+/\- *lemma* topological_space_eq

Modified topology/uniform_space.lean




## [2017-07-23 18:07:49+01:00](https://github.com/leanprover-community/mathlib/commit/9d01cb8)
refactor(algebra/lattice): use *experiment files, move set.lattice to .basic
#### Estimated changes
Modified algebra/lattice/basic.lean
- \+/\- *lemma* lattice.bot_inf_eq
- \+/\- *lemma* lattice.bot_le
- \+/\- *lemma* lattice.bot_sup_eq
- \+/\- *lemma* lattice.inf_bot_eq
- \+/\- *lemma* lattice.inf_eq_top_iff
- \+/\- *lemma* lattice.inf_idem
- \+ *lemma* lattice.inf_le_left'
- \+ *lemma* lattice.inf_le_right'
- \+/\- *lemma* lattice.inf_top_eq
- \+ *lemma* lattice.le_bot_iff
- \+/\- *lemma* lattice.le_inf_iff
- \+ *lemma* lattice.le_sup_left'
- \+ *lemma* lattice.le_sup_right'
- \+/\- *lemma* lattice.le_top
- \+/\- *lemma* lattice.sup_bot_eq
- \+/\- *lemma* lattice.sup_eq_bot_iff
- \+/\- *lemma* lattice.sup_idem
- \+/\- *lemma* lattice.sup_le_iff
- \+/\- *lemma* lattice.sup_top_eq
- \+/\- *lemma* lattice.top_inf_eq
- \+ *lemma* lattice.top_le_iff
- \+/\- *lemma* lattice.top_sup_eq
- \+ *lemma* le_antisymm'

Deleted algebra/lattice/basic_experiment.lean
- \- *lemma* lattice.bot_inf_eq
- \- *lemma* lattice.bot_le
- \- *lemma* lattice.bot_sup_eq
- \- *lemma* lattice.bot_unique
- \- *lemma* lattice.eq_bot_iff
- \- *lemma* lattice.eq_top_iff
- \- *def* lattice.imp
- \- *lemma* lattice.inf_assoc
- \- *lemma* lattice.inf_bot_eq
- \- *lemma* lattice.inf_comm
- \- *lemma* lattice.inf_eq_top_iff
- \- *lemma* lattice.inf_idem
- \- *lemma* lattice.inf_le_inf
- \- *lemma* lattice.inf_le_left'
- \- *lemma* lattice.inf_le_left
- \- *lemma* lattice.inf_le_left_of_le
- \- *lemma* lattice.inf_le_right'
- \- *lemma* lattice.inf_le_right
- \- *lemma* lattice.inf_le_right_of_le
- \- *lemma* lattice.inf_of_le_left
- \- *lemma* lattice.inf_of_le_right
- \- *lemma* lattice.inf_sup_self
- \- *lemma* lattice.inf_top_eq
- \- *lemma* lattice.le_bot_iff
- \- *lemma* lattice.le_inf
- \- *lemma* lattice.le_inf_iff
- \- *lemma* lattice.le_inf_sup
- \- *lemma* lattice.le_of_inf_eq
- \- *lemma* lattice.le_of_sup_eq
- \- *lemma* lattice.le_sup_left'
- \- *lemma* lattice.le_sup_left
- \- *lemma* lattice.le_sup_left_of_le
- \- *lemma* lattice.le_sup_right'
- \- *lemma* lattice.le_sup_right
- \- *lemma* lattice.le_sup_right_of_le
- \- *lemma* lattice.le_top
- \- *lemma* lattice.neq_bot_of_le_neq_bot
- \- *lemma* lattice.sup_assoc
- \- *lemma* lattice.sup_bot_eq
- \- *lemma* lattice.sup_comm
- \- *lemma* lattice.sup_eq_bot_iff
- \- *lemma* lattice.sup_idem
- \- *lemma* lattice.sup_inf_le
- \- *lemma* lattice.sup_inf_self
- \- *lemma* lattice.sup_le
- \- *lemma* lattice.sup_le_iff
- \- *lemma* lattice.sup_le_sup
- \- *lemma* lattice.sup_of_le_left
- \- *lemma* lattice.sup_of_le_right
- \- *lemma* lattice.sup_top_eq
- \- *lemma* lattice.top_inf_eq
- \- *lemma* lattice.top_le_iff
- \- *lemma* lattice.top_sup_eq
- \- *lemma* lattice.top_unique
- \- *lemma* le_antisymm'

Modified algebra/lattice/bounded_lattice.lean


Deleted algebra/lattice/bounded_lattice_experiment.lean
- \- *lemma* lattice.monotone_and
- \- *lemma* lattice.monotone_or

Modified algebra/lattice/complete_boolean_algebra.lean


Modified algebra/lattice/complete_lattice.lean
- \+ *lemma* lattice.foo'
- \+ *lemma* lattice.foo
- \+ *lemma* lattice.infi_le'
- \+ *lemma* lattice.le_supr'
- \- *theorem* set.subset_union_left
- \- *theorem* set.subset_union_right

Deleted algebra/lattice/complete_lattice_experiment.lean
- \- *theorem* insert_def
- \- *theorem* insert_eq_of_mem
- \- *theorem* insert_of_has_insert
- \- *theorem* inter_def
- \- *theorem* inter_left_comm
- \- *def* lattice.Inf
- \- *lemma* lattice.Inf_empty
- \- *lemma* lattice.Inf_eq_infi
- \- *lemma* lattice.Inf_image
- \- *lemma* lattice.Inf_insert
- \- *lemma* lattice.Inf_le
- \- *lemma* lattice.Inf_le_Inf
- \- *lemma* lattice.Inf_le_Sup
- \- *lemma* lattice.Inf_le_iff
- \- *lemma* lattice.Inf_le_of_le
- \- *lemma* lattice.Inf_singleton
- \- *lemma* lattice.Inf_union
- \- *lemma* lattice.Inf_univ
- \- *def* lattice.Sup
- \- *lemma* lattice.Sup_empty
- \- *lemma* lattice.Sup_eq_supr
- \- *lemma* lattice.Sup_image
- \- *lemma* lattice.Sup_insert
- \- *lemma* lattice.Sup_inter_le
- \- *lemma* lattice.Sup_le
- \- *lemma* lattice.Sup_le_Sup
- \- *lemma* lattice.Sup_singleton
- \- *lemma* lattice.Sup_union
- \- *lemma* lattice.Sup_univ
- \- *lemma* lattice.foo'
- \- *lemma* lattice.foo
- \- *def* lattice.infi
- \- *lemma* lattice.infi_and
- \- *lemma* lattice.infi_comm
- \- *lemma* lattice.infi_congr_Prop
- \- *lemma* lattice.infi_const
- \- *lemma* lattice.infi_empty
- \- *lemma* lattice.infi_emptyset
- \- *lemma* lattice.infi_exists
- \- *lemma* lattice.infi_false
- \- *lemma* lattice.infi_inf_eq
- \- *lemma* lattice.infi_infi_eq_left
- \- *lemma* lattice.infi_infi_eq_right
- \- *lemma* lattice.infi_insert
- \- *lemma* lattice.infi_le'
- \- *lemma* lattice.infi_le
- \- *lemma* lattice.infi_le_infi2
- \- *lemma* lattice.infi_le_infi
- \- *lemma* lattice.infi_le_infi_const
- \- *lemma* lattice.infi_le_of_le
- \- *lemma* lattice.infi_or
- \- *lemma* lattice.infi_prod
- \- *lemma* lattice.infi_sigma
- \- *lemma* lattice.infi_singleton
- \- *lemma* lattice.infi_subtype
- \- *lemma* lattice.infi_sum
- \- *lemma* lattice.infi_true
- \- *lemma* lattice.infi_union
- \- *lemma* lattice.infi_unit
- \- *lemma* lattice.infi_univ
- \- *theorem* lattice.insert_of_has_insert
- \- *lemma* lattice.le_Inf
- \- *lemma* lattice.le_Inf_inter
- \- *lemma* lattice.le_Sup
- \- *lemma* lattice.le_Sup_iff
- \- *lemma* lattice.le_Sup_of_le
- \- *lemma* lattice.le_infi
- \- *lemma* lattice.le_infi_iff
- \- *lemma* lattice.le_supr'
- \- *lemma* lattice.le_supr
- \- *lemma* lattice.le_supr_of_le
- \- *lemma* lattice.monotone_Inf_of_monotone
- \- *lemma* lattice.monotone_Sup_of_monotone
- \- *def* lattice.supr
- \- *lemma* lattice.supr_and
- \- *lemma* lattice.supr_comm
- \- *lemma* lattice.supr_congr_Prop
- \- *lemma* lattice.supr_const
- \- *lemma* lattice.supr_empty
- \- *lemma* lattice.supr_emptyset
- \- *lemma* lattice.supr_exists
- \- *lemma* lattice.supr_false
- \- *lemma* lattice.supr_insert
- \- *lemma* lattice.supr_le
- \- *lemma* lattice.supr_le_iff
- \- *lemma* lattice.supr_le_supr2
- \- *lemma* lattice.supr_le_supr
- \- *lemma* lattice.supr_le_supr_const
- \- *lemma* lattice.supr_or
- \- *lemma* lattice.supr_prod
- \- *lemma* lattice.supr_sigma
- \- *lemma* lattice.supr_singleton
- \- *lemma* lattice.supr_subtype
- \- *lemma* lattice.supr_sum
- \- *lemma* lattice.supr_sup_eq
- \- *lemma* lattice.supr_supr_eq_left
- \- *lemma* lattice.supr_supr_eq_right
- \- *lemma* lattice.supr_true
- \- *lemma* lattice.supr_union
- \- *lemma* lattice.supr_unit
- \- *lemma* lattice.supr_univ
- \- *theorem* mem_insert_iff
- \- *theorem* mem_inter_eq
- \- *lemma* mem_set_of
- \- *lemma* mem_set_of_eq
- \- *theorem* mem_singleton
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_union_eq
- \- *theorem* mem_univ_eq
- \- *lemma* nmem_set_of_eq
- \- *theorem* set_eq_def
- \- *lemma* set_of_false
- \- *theorem* singleton_def
- \- *theorem* singleton_eq_singleton_iff
- \- *theorem* subset_def
- \- *theorem* subset_insert
- \- *theorem* subset_univ
- \- *theorem* union_def
- \- *theorem* union_left_comm

Modified data/seq/wseq.lean


Modified data/set/basic.lean
- \+ *theorem* set.bounded_forall_empty_iff
- \+ *theorem* set.bounded_forall_image_iff
- \+ *theorem* set.bounded_forall_image_of_bounded_forall
- \+ *theorem* set.bounded_forall_insert_iff
- \+ *theorem* set.compl_comp_compl
- \+ *theorem* set.compl_compl
- \+ *theorem* set.compl_compl_image
- \+ *theorem* set.compl_empty
- \+ *theorem* set.compl_eq_univ_diff
- \+ *theorem* set.compl_inter
- \+ *theorem* set.compl_inter_self
- \+ *theorem* set.compl_union
- \+ *theorem* set.compl_union_self
- \+ *theorem* set.compl_univ
- \+ *theorem* set.diff_eq
- \+ *theorem* set.diff_subset
- \+ *theorem* set.empty_def
- \+ *theorem* set.empty_inter
- \- *lemma* set.empty_inter
- \+ *theorem* set.empty_ne_univ
- \+ *theorem* set.empty_subset
- \- *lemma* set.empty_subset
- \+ *theorem* set.empty_union
- \- *lemma* set.empty_union
- \+ *theorem* set.eq_empty_of_forall_not_mem
- \- *lemma* set.eq_empty_of_forall_not_mem
- \+ *theorem* set.eq_empty_of_subset_empty
- \- *lemma* set.eq_empty_of_subset_empty
- \+ *theorem* set.eq_of_mem_singleton
- \+ *theorem* set.eq_of_subset_of_subset
- \- *lemma* set.eq_of_subset_of_subset
- \+ *def* set.eq_on
- \+ *theorem* set.eq_or_mem_of_mem_insert
- \+ *theorem* set.eq_sep_of_subset
- \+ *theorem* set.eq_univ_of_forall
- \+ *theorem* set.eq_univ_of_univ_subset
- \+ *theorem* set.eq_vimage_subtype_val_iff
- \+ *theorem* set.exists_mem_of_ne_empty
- \+ *theorem* set.ext
- \- *lemma* set.ext
- \+ *theorem* set.fix_set_compl
- \+ *theorem* set.forall_insert_of_forall
- \+ *theorem* set.forall_not_of_sep_empty
- \+ *theorem* set.forall_of_forall_insert
- \+ *theorem* set.image_comp
- \+ *theorem* set.image_empty
- \+ *theorem* set.image_eq_image_of_eq_on
- \+ *theorem* set.image_id
- \+ *theorem* set.image_insert_eq
- \+ *theorem* set.image_subset
- \+ *theorem* set.image_subset_iff_subset_vimage
- \+ *theorem* set.image_union
- \+ *theorem* set.insert_comm
- \+ *theorem* set.insert_def
- \+ *theorem* set.insert_eq
- \+ *theorem* set.insert_eq_of_mem
- \+ *theorem* set.insert_ne_empty
- \+ *theorem* set.insert_of_has_insert
- \+ *theorem* set.inter_assoc
- \- *lemma* set.inter_assoc
- \+ *theorem* set.inter_comm
- \- *lemma* set.inter_comm
- \+ *theorem* set.inter_compl_self
- \+ *theorem* set.inter_def
- \+ *theorem* set.inter_distrib_left
- \+ *theorem* set.inter_distrib_right
- \+ *theorem* set.inter_empty
- \- *lemma* set.inter_empty
- \+ *theorem* set.inter_eq_compl_compl_union_compl
- \+ *theorem* set.inter_eq_self_of_subset_left
- \+ *theorem* set.inter_eq_self_of_subset_right
- \+ *theorem* set.inter_left_comm
- \+ *theorem* set.inter_right_comm
- \+ *theorem* set.inter_self
- \- *lemma* set.inter_self
- \+ *theorem* set.inter_subset_inter
- \+ *theorem* set.inter_subset_inter_left
- \+ *theorem* set.inter_subset_inter_right
- \+ *theorem* set.inter_subset_left
- \+ *theorem* set.inter_subset_right
- \+ *theorem* set.inter_univ
- \+ *theorem* set.mem_compl
- \+ *theorem* set.mem_compl_eq
- \+ *theorem* set.mem_compl_iff
- \+ *theorem* set.mem_diff
- \+ *theorem* set.mem_diff_eq
- \+ *theorem* set.mem_diff_iff
- \+ *theorem* set.mem_empty_eq
- \- *lemma* set.mem_empty_eq
- \+ *theorem* set.mem_image
- \+ *theorem* set.mem_image_compl
- \+ *def* set.mem_image_elim
- \+ *def* set.mem_image_elim_on
- \+ *theorem* set.mem_image_eq
- \+ *theorem* set.mem_image_of_mem
- \+ *theorem* set.mem_insert
- \+ *theorem* set.mem_insert_iff
- \+ *theorem* set.mem_insert_of_mem
- \+ *theorem* set.mem_inter
- \+ *theorem* set.mem_inter_eq
- \+ *theorem* set.mem_inter_iff
- \+ *theorem* set.mem_of_mem_diff
- \+ *theorem* set.mem_of_mem_insert_of_ne
- \+ *theorem* set.mem_of_mem_inter_left
- \+ *theorem* set.mem_of_mem_inter_right
- \+ *theorem* set.mem_of_subset_of_mem
- \- *lemma* set.mem_of_subset_of_mem
- \+ *theorem* set.mem_or_mem_of_mem_union
- \+ *theorem* set.mem_powerset
- \+ *theorem* set.mem_powerset_iff
- \+ *theorem* set.mem_sep
- \+ *theorem* set.mem_sep_eq
- \+ *theorem* set.mem_sep_iff
- \+ *theorem* set.mem_set_of_eq
- \+ *theorem* set.mem_singleton
- \+ *theorem* set.mem_singleton_iff
- \+ *theorem* set.mem_singleton_of_eq
- \+ *theorem* set.mem_union.elim
- \+ *theorem* set.mem_union_eq
- \+ *theorem* set.mem_union_iff
- \+ *theorem* set.mem_union_left
- \+ *theorem* set.mem_union_right
- \+ *theorem* set.mem_univ
- \+ *theorem* set.mem_univ_eq
- \+ *theorem* set.mem_univ_iff
- \+ *theorem* set.mem_vimage_eq
- \+ *theorem* set.mono_image
- \+ *theorem* set.ne_empty_of_mem
- \- *lemma* set.ne_empty_of_mem
- \+ *theorem* set.nmem_set_of_eq
- \+ *theorem* set.nonempty_of_inter_nonempty_left
- \+ *theorem* set.nonempty_of_inter_nonempty_right
- \+ *theorem* set.not_mem_empty
- \- *lemma* set.not_mem_empty
- \+ *theorem* set.not_mem_of_mem_compl
- \+ *theorem* set.not_mem_of_mem_diff
- \+ *theorem* set.pair_eq_singleton
- \+ *def* set.pairwise_on
- \+ *theorem* set.sep_subset
- \+ *theorem* set.set_eq_def
- \+ *lemma* set.set_of_false
- \+ *theorem* set.singleton_def
- \+ *theorem* set.singleton_eq_singleton_iff
- \+ *theorem* set.singleton_ne_empty
- \+ *theorem* set.singleton_subset_iff
- \+ *theorem* set.ssubset_def
- \+ *theorem* set.ssubset_insert
- \+ *def* set.strict_subset
- \+ *theorem* set.subset.antisymm
- \- *lemma* set.subset.antisymm
- \+ *theorem* set.subset.refl
- \- *lemma* set.subset.refl
- \+ *theorem* set.subset.trans
- \- *lemma* set.subset.trans
- \+ *theorem* set.subset_def
- \+ *theorem* set.subset_empty_iff
- \+ *theorem* set.subset_insert
- \+ *theorem* set.subset_inter
- \+ *theorem* set.subset_of_mem_powerset
- \+ *theorem* set.subset_union_left
- \+ *theorem* set.subset_union_right
- \+ *theorem* set.subset_univ
- \+ *theorem* set.union_assoc
- \- *lemma* set.union_assoc
- \+ *theorem* set.union_comm
- \- *lemma* set.union_comm
- \+ *theorem* set.union_compl_self
- \+ *theorem* set.union_def
- \+ *theorem* set.union_diff_cancel
- \+ *theorem* set.union_distrib_left
- \+ *theorem* set.union_distrib_right
- \+ *theorem* set.union_empty
- \- *lemma* set.union_empty
- \+ *theorem* set.union_eq_compl_compl_inter_compl
- \+ *theorem* set.union_eq_self_of_subset_left
- \+ *theorem* set.union_eq_self_of_subset_right
- \+ *theorem* set.union_insert_eq
- \+ *theorem* set.union_left_comm
- \+ *theorem* set.union_right_comm
- \+ *theorem* set.union_self
- \- *lemma* set.union_self
- \+ *theorem* set.union_subset
- \+ *theorem* set.union_subset_iff
- \+ *theorem* set.union_subset_union
- \+ *theorem* set.univ_def
- \+ *theorem* set.univ_inter
- \+ *def* set.vimage
- \+ *theorem* set.vimage_comp
- \+ *theorem* set.vimage_compl
- \+ *theorem* set.vimage_empty
- \+ *theorem* set.vimage_id
- \+ *theorem* set.vimage_image_eq
- \+ *theorem* set.vimage_inter
- \+ *theorem* set.vimage_mono
- \+ *theorem* set.vimage_union
- \+ *theorem* set.vimage_univ

Modified data/set/lattice.lean
- \- *lemma* set.bounded_forall_empty_iff
- \- *lemma* set.bounded_forall_image_iff
- \- *lemma* set.bounded_forall_image_of_bounded_forall
- \- *lemma* set.bounded_forall_insert_iff
- \- *theorem* set.compl_comp_compl
- \- *theorem* set.compl_compl
- \- *theorem* set.compl_compl_image
- \- *theorem* set.compl_empty
- \- *theorem* set.compl_eq_univ_diff
- \- *theorem* set.compl_inter
- \- *theorem* set.compl_inter_self
- \- *theorem* set.compl_union
- \- *theorem* set.compl_union_self
- \- *theorem* set.compl_univ
- \- *theorem* set.diff_eq
- \- *theorem* set.diff_subset
- \+ *theorem* set.disjoint_bot_left
- \- *lemma* set.disjoint_bot_left
- \+ *theorem* set.disjoint_bot_right
- \- *lemma* set.disjoint_bot_right
- \+ *theorem* set.disjoint_symm
- \- *lemma* set.disjoint_symm
- \- *theorem* set.empty_ne_univ
- \- *theorem* set.eq_of_mem_singleton
- \- *def* set.eq_on
- \- *theorem* set.eq_or_mem_of_mem_insert
- \- *theorem* set.eq_sep_of_subset
- \- *theorem* set.eq_univ_of_forall
- \- *theorem* set.eq_univ_of_univ_subset
- \- *lemma* set.eq_vimage_subtype_val_iff
- \- *theorem* set.exists_mem_of_ne_empty
- \- *theorem* set.fix_set_compl
- \- *theorem* set.forall_insert_of_forall
- \- *theorem* set.forall_not_of_sep_empty
- \- *theorem* set.forall_of_forall_insert
- \- *lemma* set.image_comp
- \- *theorem* set.image_empty
- \- *theorem* set.image_eq_image_of_eq_on
- \- *theorem* set.image_id
- \- *lemma* set.image_insert_eq
- \- *lemma* set.image_subset
- \- *theorem* set.image_subset_iff_subset_vimage
- \- *theorem* set.image_union
- \- *theorem* set.insert_comm
- \- *theorem* set.insert_def
- \- *theorem* set.insert_eq
- \- *theorem* set.insert_eq_of_mem
- \- *theorem* set.insert_ne_empty
- \- *theorem* set.insert_of_has_insert
- \+ *theorem* set.insert_sdiff_singleton
- \- *lemma* set.insert_sdiff_singleton
- \- *theorem* set.inter_compl_self
- \- *theorem* set.inter_def
- \- *theorem* set.inter_distrib_left
- \- *theorem* set.inter_distrib_right
- \- *theorem* set.inter_eq_compl_compl_union_compl
- \- *theorem* set.inter_eq_self_of_subset_left
- \- *theorem* set.inter_eq_self_of_subset_right
- \- *theorem* set.inter_left_comm
- \- *theorem* set.inter_right_comm
- \- *theorem* set.inter_subset_inter
- \- *theorem* set.inter_subset_inter_left
- \- *theorem* set.inter_subset_inter_right
- \- *theorem* set.inter_subset_left
- \- *theorem* set.inter_subset_right
- \- *theorem* set.inter_univ
- \- *theorem* set.mem_compl
- \- *theorem* set.mem_compl_eq
- \- *theorem* set.mem_compl_iff
- \- *theorem* set.mem_diff
- \- *theorem* set.mem_diff_eq
- \- *theorem* set.mem_diff_iff
- \- *theorem* set.mem_image
- \- *theorem* set.mem_image_compl
- \- *def* set.mem_image_elim
- \- *def* set.mem_image_elim_on
- \- *theorem* set.mem_image_eq
- \- *theorem* set.mem_image_of_mem
- \- *theorem* set.mem_insert
- \- *theorem* set.mem_insert_iff
- \- *theorem* set.mem_insert_of_mem
- \- *theorem* set.mem_inter
- \- *theorem* set.mem_inter_eq
- \- *theorem* set.mem_inter_iff
- \- *theorem* set.mem_of_mem_diff
- \- *theorem* set.mem_of_mem_insert_of_ne
- \- *theorem* set.mem_of_mem_inter_left
- \- *theorem* set.mem_of_mem_inter_right
- \- *theorem* set.mem_or_mem_of_mem_union
- \- *theorem* set.mem_powerset
- \- *theorem* set.mem_powerset_iff
- \- *theorem* set.mem_sep
- \- *theorem* set.mem_sep_eq
- \- *theorem* set.mem_sep_iff
- \- *lemma* set.mem_set_of
- \- *lemma* set.mem_set_of_eq
- \- *theorem* set.mem_singleton
- \- *theorem* set.mem_singleton_iff
- \- *theorem* set.mem_singleton_of_eq
- \- *theorem* set.mem_union.elim
- \- *theorem* set.mem_union_eq
- \- *theorem* set.mem_union_iff
- \- *theorem* set.mem_union_left
- \- *theorem* set.mem_union_right
- \- *theorem* set.mem_unionl
- \- *theorem* set.mem_unionr
- \- *theorem* set.mem_univ
- \- *theorem* set.mem_univ_eq
- \- *theorem* set.mem_univ_iff
- \- *lemma* set.mem_vimage_eq
- \- *theorem* set.mono_image
- \+ *theorem* set.monotone_vimage
- \- *lemma* set.monotone_vimage
- \- *lemma* set.nmem_set_of_eq
- \- *theorem* set.nonempty_of_inter_nonempty_left
- \- *theorem* set.nonempty_of_inter_nonempty_right
- \- *theorem* set.not_mem_of_mem_compl
- \- *theorem* set.not_mem_of_mem_diff
- \- *theorem* set.pair_eq_singleton
- \- *def* set.pairwise_on
- \+ *theorem* set.sdiff_singleton_eq_same
- \- *lemma* set.sdiff_singleton_eq_same
- \- *theorem* set.sep_subset
- \- *theorem* set.set_eq_def
- \- *lemma* set.set_of_false
- \- *theorem* set.singleton_def
- \- *theorem* set.singleton_eq_singleton_iff
- \- *theorem* set.singleton_ne_empty
- \- *lemma* set.singleton_subset_iff
- \- *theorem* set.ssubset_def
- \- *lemma* set.ssubset_insert
- \- *def* set.strict_subset
- \- *theorem* set.subset_def
- \- *theorem* set.subset_empty_iff
- \- *theorem* set.subset_insert
- \- *theorem* set.subset_inter
- \- *theorem* set.subset_of_mem_powerset
- \- *theorem* set.subset_univ
- \- *theorem* set.union_compl_self
- \- *theorem* set.union_def
- \- *theorem* set.union_diff_cancel
- \- *theorem* set.union_distrib_left
- \- *theorem* set.union_distrib_right
- \- *theorem* set.union_eq_compl_compl_inter_compl
- \- *theorem* set.union_eq_self_of_subset_left
- \- *theorem* set.union_eq_self_of_subset_right
- \- *lemma* set.union_insert_eq
- \- *theorem* set.union_left_comm
- \- *theorem* set.union_right_comm
- \+ *theorem* set.union_same_compl
- \- *lemma* set.union_same_compl
- \+ *theorem* set.union_sdiff_same
- \- *lemma* set.union_sdiff_same
- \- *theorem* set.union_subset
- \- *lemma* set.union_subset_iff
- \- *theorem* set.union_subset_union
- \- *theorem* set.univ_def
- \- *theorem* set.univ_inter
- \- *def* set.vimage
- \+ *theorem* set.vimage_Union
- \- *lemma* set.vimage_Union
- \- *lemma* set.vimage_comp
- \- *lemma* set.vimage_compl
- \- *lemma* set.vimage_empty
- \- *lemma* set.vimage_id
- \- *lemma* set.vimage_image_eq
- \- *lemma* set.vimage_inter
- \- *lemma* set.vimage_mono
- \+ *theorem* set.vimage_sUnion
- \- *lemma* set.vimage_sUnion
- \- *lemma* set.vimage_union
- \- *lemma* set.vimage_univ

Deleted tests/finish_set_basic.lean
- \- *lemma* set.bounded_forall_empty_iff
- \- *lemma* set.bounded_forall_image_iff
- \- *lemma* set.bounded_forall_image_of_bounded_forall
- \- *lemma* set.bounded_forall_insert_iff
- \- *theorem* set.compl_comp_compl
- \- *theorem* set.compl_compl
- \- *theorem* set.compl_compl_image
- \- *theorem* set.compl_empty
- \- *theorem* set.compl_eq_univ_diff
- \- *theorem* set.compl_inter
- \- *theorem* set.compl_inter_self
- \- *theorem* set.compl_union
- \- *theorem* set.compl_union_self
- \- *theorem* set.compl_univ
- \- *theorem* set.diff_eq
- \- *theorem* set.diff_subset
- \- *theorem* set.empty_def
- \- *theorem* set.empty_ne_univ
- \- *theorem* set.eq_of_mem_singleton
- \- *def* set.eq_on
- \- *theorem* set.eq_or_mem_of_mem_insert
- \- *theorem* set.eq_sep_of_subset
- \- *theorem* set.eq_univ_of_forall
- \- *theorem* set.eq_univ_of_univ_subset
- \- *theorem* set.exists_mem_of_ne_empty
- \- *theorem* set.fix_set_compl
- \- *theorem* set.forall_insert_of_forall
- \- *theorem* set.forall_not_of_sep_empty
- \- *theorem* set.forall_of_forall_insert
- \- *lemma* set.image_comp
- \- *theorem* set.image_empty
- \- *theorem* set.image_eq_image_of_eq_on
- \- *theorem* set.image_id
- \- *lemma* set.image_insert_eq
- \- *lemma* set.image_subset
- \- *theorem* set.image_union
- \- *theorem* set.insert_comm
- \- *theorem* set.insert_def
- \- *theorem* set.insert_eq
- \- *theorem* set.insert_eq_of_mem
- \- *theorem* set.insert_ne_empty
- \- *theorem* set.insert_of_has_insert
- \- *theorem* set.inter_compl_self
- \- *theorem* set.inter_def
- \- *theorem* set.inter_distrib_left
- \- *theorem* set.inter_distrib_right
- \- *theorem* set.inter_eq_compl_compl_union_compl
- \- *theorem* set.inter_eq_self_of_subset_left
- \- *theorem* set.inter_eq_self_of_subset_right
- \- *theorem* set.inter_left_comm
- \- *theorem* set.inter_right_comm
- \- *theorem* set.inter_subset_inter_left
- \- *theorem* set.inter_subset_inter_right
- \- *theorem* set.inter_subset_left
- \- *theorem* set.inter_subset_right
- \- *theorem* set.inter_univ
- \- *theorem* set.mem_compl
- \- *theorem* set.mem_compl_eq
- \- *theorem* set.mem_compl_iff
- \- *theorem* set.mem_diff
- \- *theorem* set.mem_diff_eq
- \- *theorem* set.mem_diff_iff
- \- *theorem* set.mem_image
- \- *theorem* set.mem_image_compl
- \- *def* set.mem_image_elim
- \- *def* set.mem_image_elim_on
- \- *theorem* set.mem_image_eq
- \- *theorem* set.mem_image_of_mem
- \- *theorem* set.mem_insert
- \- *theorem* set.mem_insert_iff
- \- *theorem* set.mem_insert_of_mem
- \- *theorem* set.mem_inter
- \- *theorem* set.mem_inter_eq
- \- *theorem* set.mem_inter_iff
- \- *theorem* set.mem_of_mem_diff
- \- *theorem* set.mem_of_mem_insert_of_ne
- \- *theorem* set.mem_of_mem_inter_left
- \- *theorem* set.mem_of_mem_inter_right
- \- *theorem* set.mem_or_mem_of_mem_union
- \- *theorem* set.mem_powerset
- \- *theorem* set.mem_powerset_iff
- \- *theorem* set.mem_sep
- \- *theorem* set.mem_sep_eq
- \- *theorem* set.mem_sep_iff
- \- *lemma* set.mem_set_of
- \- *theorem* set.mem_singleton
- \- *theorem* set.mem_singleton_iff
- \- *theorem* set.mem_singleton_of_eq
- \- *theorem* set.mem_union.elim
- \- *theorem* set.mem_union_eq
- \- *theorem* set.mem_union_iff
- \- *theorem* set.mem_union_left
- \- *theorem* set.mem_union_right
- \- *theorem* set.mem_unionl
- \- *theorem* set.mem_unionr
- \- *theorem* set.mem_univ
- \- *theorem* set.mem_univ_eq
- \- *theorem* set.mem_univ_iff
- \- *theorem* set.nonempty_of_inter_nonempty_left
- \- *theorem* set.nonempty_of_inter_nonempty_right
- \- *theorem* set.not_mem_of_mem_compl
- \- *theorem* set.not_mem_of_mem_diff
- \- *theorem* set.pair_eq_singleton
- \- *theorem* set.sep_subset
- \- *theorem* set.set_eq_def
- \- *theorem* set.singleton_def
- \- *theorem* set.singleton_ne_empty
- \- *def* set.strict_subset
- \- *theorem* set.subset_def
- \- *theorem* set.subset_empty_iff
- \- *theorem* set.subset_insert
- \- *theorem* set.subset_inter
- \- *theorem* set.subset_of_mem_powerset
- \- *theorem* set.subset_univ
- \- *theorem* set.union_compl_self
- \- *theorem* set.union_def
- \- *theorem* set.union_diff_cancel
- \- *theorem* set.union_distrib_left
- \- *theorem* set.union_distrib_right
- \- *theorem* set.union_eq_compl_compl_inter_compl
- \- *theorem* set.union_eq_self_of_subset_left
- \- *theorem* set.union_eq_self_of_subset_right
- \- *theorem* set.union_left_comm
- \- *theorem* set.union_right_comm
- \- *theorem* set.union_subset
- \- *theorem* set.univ_def
- \- *theorem* set.univ_inter

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
- \- *def* form_of_string

Deleted tools/parser/parser.lean
- \- *def* list.deterministic_or
- \- *def* parser.apply
- \- *def* parser.chainl1
- \- *def* parser.chainl1_rest
- \- *def* parser.chainl
- \- *def* parser.chainr1
- \- *def* parser.chainr1_rest
- \- *def* parser.chainr
- \- *def* parser.item
- \- *def* parser.many1
- \- *def* parser.many
- \- *def* parser.many_aux
- \- *def* parser.parse
- \- *def* parser.parser_bignum
- \- *def* parser.sat
- \- *def* parser.sepby1
- \- *def* parser.sepby
- \- *def* parser.space
- \- *def* parser.symb
- \- *def* parser.take_char
- \- *def* parser.take_string
- \- *def* parser.take_string_aux
- \- *def* parser.token
- \- *def* parser
- \- *def* parser_bind
- \- *def* parser_fmap
- \- *def* parser_pure
- \- *lemma* {u
- \- *lemma* {u}

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
Added .gitignore


Added algebra/group.lean
- \+ *theorem* eq_iff_eq_of_sub_eq_sub
- \+ *theorem* eq_iff_sub_eq_zero
- \+ *theorem* eq_inv_iff_eq_inv
- \+ *theorem* eq_of_mul_inv_eq_one
- \+ *theorem* eq_one_of_inv_eq_one
- \+ *theorem* eq_sub_iff_add_eq
- \+ *theorem* inv_eq_inv_iff_eq
- \+ *theorem* inv_eq_one_iff_eq_one
- \+ *theorem* left_inverse_add_left_sub
- \+ *theorem* left_inverse_add_right_neg_add
- \+ *theorem* left_inverse_inv
- \+ *theorem* left_inverse_neg_add_add_right
- \+ *theorem* left_inverse_sub_add_left
- \+ *theorem* mul_eq_iff_eq_inv_mul
- \+ *theorem* mul_eq_iff_eq_mul_inv
- \+ *theorem* sub_eq_iff_eq_add

Added algebra/group_power.lean
- \+ *def* gpow
- \+ *theorem* gpow_add
- \+ *theorem* gpow_comm
- \+ *theorem* inv_pow
- \+ *def* monoid.pow
- \+ *theorem* mul_pow
- \+ *theorem* one_pow
- \+ *theorem* pow_add
- \+ *theorem* pow_comm
- \+ *theorem* pow_ge_one_of_ge_one
- \+ *def* pow_int
- \+ *theorem* pow_inv_comm
- \+ *theorem* pow_mul
- \+ *def* pow_nat
- \+ *theorem* pow_one
- \+ *theorem* pow_pos
- \+ *theorem* pow_sub
- \+ *theorem* pow_succ'
- \+ *theorem* pow_succ
- \+ *theorem* pow_zero

Added algebra/lattice/README.md


Added algebra/lattice/basic.lean
- \+ *lemma* lattice.bot_inf_eq
- \+ *lemma* lattice.bot_le
- \+ *lemma* lattice.bot_sup_eq
- \+ *lemma* lattice.bot_unique
- \+ *lemma* lattice.eq_bot_iff
- \+ *lemma* lattice.eq_top_iff
- \+ *lemma* lattice.inf_assoc
- \+ *lemma* lattice.inf_bot_eq
- \+ *lemma* lattice.inf_comm
- \+ *lemma* lattice.inf_eq_top_iff
- \+ *lemma* lattice.inf_idem
- \+ *lemma* lattice.inf_le_inf
- \+ *lemma* lattice.inf_le_left
- \+ *lemma* lattice.inf_le_left_of_le
- \+ *lemma* lattice.inf_le_right
- \+ *lemma* lattice.inf_le_right_of_le
- \+ *lemma* lattice.inf_of_le_left
- \+ *lemma* lattice.inf_of_le_right
- \+ *lemma* lattice.inf_sup_self
- \+ *lemma* lattice.inf_top_eq
- \+ *lemma* lattice.le_inf
- \+ *lemma* lattice.le_inf_iff
- \+ *lemma* lattice.le_inf_sup
- \+ *lemma* lattice.le_of_inf_eq
- \+ *lemma* lattice.le_of_sup_eq
- \+ *lemma* lattice.le_sup_left
- \+ *lemma* lattice.le_sup_left_of_le
- \+ *lemma* lattice.le_sup_right
- \+ *lemma* lattice.le_sup_right_of_le
- \+ *lemma* lattice.le_top
- \+ *lemma* lattice.neq_bot_of_le_neq_bot
- \+ *lemma* lattice.sup_assoc
- \+ *lemma* lattice.sup_bot_eq
- \+ *lemma* lattice.sup_comm
- \+ *lemma* lattice.sup_eq_bot_iff
- \+ *lemma* lattice.sup_idem
- \+ *lemma* lattice.sup_inf_le
- \+ *lemma* lattice.sup_inf_self
- \+ *lemma* lattice.sup_le
- \+ *lemma* lattice.sup_le_iff
- \+ *lemma* lattice.sup_le_sup
- \+ *lemma* lattice.sup_of_le_left
- \+ *lemma* lattice.sup_of_le_right
- \+ *lemma* lattice.sup_top_eq
- \+ *lemma* lattice.top_inf_eq
- \+ *lemma* lattice.top_sup_eq
- \+ *lemma* lattice.top_unique

Added algebra/lattice/basic_experiment.lean
- \+ *lemma* lattice.bot_inf_eq
- \+ *lemma* lattice.bot_le
- \+ *lemma* lattice.bot_sup_eq
- \+ *lemma* lattice.bot_unique
- \+ *lemma* lattice.eq_bot_iff
- \+ *lemma* lattice.eq_top_iff
- \+ *def* lattice.imp
- \+ *lemma* lattice.inf_assoc
- \+ *lemma* lattice.inf_bot_eq
- \+ *lemma* lattice.inf_comm
- \+ *lemma* lattice.inf_eq_top_iff
- \+ *lemma* lattice.inf_idem
- \+ *lemma* lattice.inf_le_inf
- \+ *lemma* lattice.inf_le_left'
- \+ *lemma* lattice.inf_le_left
- \+ *lemma* lattice.inf_le_left_of_le
- \+ *lemma* lattice.inf_le_right'
- \+ *lemma* lattice.inf_le_right
- \+ *lemma* lattice.inf_le_right_of_le
- \+ *lemma* lattice.inf_of_le_left
- \+ *lemma* lattice.inf_of_le_right
- \+ *lemma* lattice.inf_sup_self
- \+ *lemma* lattice.inf_top_eq
- \+ *lemma* lattice.le_bot_iff
- \+ *lemma* lattice.le_inf
- \+ *lemma* lattice.le_inf_iff
- \+ *lemma* lattice.le_inf_sup
- \+ *lemma* lattice.le_of_inf_eq
- \+ *lemma* lattice.le_of_sup_eq
- \+ *lemma* lattice.le_sup_left'
- \+ *lemma* lattice.le_sup_left
- \+ *lemma* lattice.le_sup_left_of_le
- \+ *lemma* lattice.le_sup_right'
- \+ *lemma* lattice.le_sup_right
- \+ *lemma* lattice.le_sup_right_of_le
- \+ *lemma* lattice.le_top
- \+ *lemma* lattice.neq_bot_of_le_neq_bot
- \+ *lemma* lattice.sup_assoc
- \+ *lemma* lattice.sup_bot_eq
- \+ *lemma* lattice.sup_comm
- \+ *lemma* lattice.sup_eq_bot_iff
- \+ *lemma* lattice.sup_idem
- \+ *lemma* lattice.sup_inf_le
- \+ *lemma* lattice.sup_inf_self
- \+ *lemma* lattice.sup_le
- \+ *lemma* lattice.sup_le_iff
- \+ *lemma* lattice.sup_le_sup
- \+ *lemma* lattice.sup_of_le_left
- \+ *lemma* lattice.sup_of_le_right
- \+ *lemma* lattice.sup_top_eq
- \+ *lemma* lattice.top_inf_eq
- \+ *lemma* lattice.top_le_iff
- \+ *lemma* lattice.top_sup_eq
- \+ *lemma* lattice.top_unique
- \+ *lemma* le_antisymm'

Added algebra/lattice/boolean_algebra.lean
- \+ *lemma* lattice.inf_neg_eq_bot
- \+ *lemma* lattice.inf_sup_left
- \+ *lemma* lattice.inf_sup_right
- \+ *lemma* lattice.le_neg_of_le_neg
- \+ *lemma* lattice.le_sup_inf
- \+ *lemma* lattice.neg_bot
- \+ *lemma* lattice.neg_eq_neg_iff
- \+ *lemma* lattice.neg_eq_neg_of_eq
- \+ *lemma* lattice.neg_inf
- \+ *lemma* lattice.neg_inf_eq_bot
- \+ *lemma* lattice.neg_le_iff_neg_le
- \+ *lemma* lattice.neg_le_neg
- \+ *lemma* lattice.neg_le_neg_iff_le
- \+ *lemma* lattice.neg_le_of_neg_le
- \+ *lemma* lattice.neg_neg
- \+ *lemma* lattice.neg_sup
- \+ *lemma* lattice.neg_sup_eq_top
- \+ *lemma* lattice.neg_top
- \+ *lemma* lattice.neg_unique
- \+ *lemma* lattice.sub_eq
- \+ *lemma* lattice.sub_eq_left
- \+ *lemma* lattice.sup_inf_left
- \+ *lemma* lattice.sup_inf_right
- \+ *lemma* lattice.sup_neg_eq_top
- \+ *lemma* lattice.sup_sub_same

Added algebra/lattice/bounded_lattice.lean
- \+ *lemma* lattice.monotone_and
- \+ *lemma* lattice.monotone_or

Added algebra/lattice/bounded_lattice_experiment.lean
- \+ *lemma* lattice.monotone_and
- \+ *lemma* lattice.monotone_or

Added algebra/lattice/complete_boolean_algebra.lean
- \+ *lemma* lattice.inf_Sup_eq
- \+ *lemma* lattice.neg_Inf
- \+ *lemma* lattice.neg_Sup
- \+ *lemma* lattice.neg_infi
- \+ *lemma* lattice.neg_supr
- \+ *lemma* lattice.sup_Inf_eq

Added algebra/lattice/complete_lattice.lean
- \+ *def* lattice.Inf
- \+ *lemma* lattice.Inf_empty
- \+ *lemma* lattice.Inf_eq_infi
- \+ *lemma* lattice.Inf_image
- \+ *lemma* lattice.Inf_insert
- \+ *lemma* lattice.Inf_le
- \+ *lemma* lattice.Inf_le_Inf
- \+ *lemma* lattice.Inf_le_Sup
- \+ *lemma* lattice.Inf_le_iff
- \+ *lemma* lattice.Inf_le_of_le
- \+ *lemma* lattice.Inf_singleton
- \+ *lemma* lattice.Inf_union
- \+ *lemma* lattice.Inf_univ
- \+ *def* lattice.Sup
- \+ *lemma* lattice.Sup_empty
- \+ *lemma* lattice.Sup_eq_supr
- \+ *lemma* lattice.Sup_image
- \+ *lemma* lattice.Sup_insert
- \+ *lemma* lattice.Sup_inter_le
- \+ *lemma* lattice.Sup_le
- \+ *lemma* lattice.Sup_le_Sup
- \+ *lemma* lattice.Sup_singleton
- \+ *lemma* lattice.Sup_union
- \+ *lemma* lattice.Sup_univ
- \+ *def* lattice.infi
- \+ *lemma* lattice.infi_and
- \+ *lemma* lattice.infi_comm
- \+ *lemma* lattice.infi_congr_Prop
- \+ *lemma* lattice.infi_const
- \+ *lemma* lattice.infi_empty
- \+ *lemma* lattice.infi_emptyset
- \+ *lemma* lattice.infi_exists
- \+ *lemma* lattice.infi_false
- \+ *lemma* lattice.infi_inf_eq
- \+ *lemma* lattice.infi_infi_eq_left
- \+ *lemma* lattice.infi_infi_eq_right
- \+ *lemma* lattice.infi_insert
- \+ *lemma* lattice.infi_le
- \+ *lemma* lattice.infi_le_infi2
- \+ *lemma* lattice.infi_le_infi
- \+ *lemma* lattice.infi_le_infi_const
- \+ *lemma* lattice.infi_le_of_le
- \+ *lemma* lattice.infi_or
- \+ *lemma* lattice.infi_prod
- \+ *lemma* lattice.infi_sigma
- \+ *lemma* lattice.infi_singleton
- \+ *lemma* lattice.infi_subtype
- \+ *lemma* lattice.infi_sum
- \+ *lemma* lattice.infi_true
- \+ *lemma* lattice.infi_union
- \+ *lemma* lattice.infi_unit
- \+ *lemma* lattice.infi_univ
- \+ *theorem* lattice.insert_of_has_insert
- \+ *lemma* lattice.le_Inf
- \+ *lemma* lattice.le_Inf_inter
- \+ *lemma* lattice.le_Sup
- \+ *lemma* lattice.le_Sup_iff
- \+ *lemma* lattice.le_Sup_of_le
- \+ *lemma* lattice.le_infi
- \+ *lemma* lattice.le_infi_iff
- \+ *lemma* lattice.le_supr
- \+ *lemma* lattice.le_supr_of_le
- \+ *lemma* lattice.monotone_Inf_of_monotone
- \+ *lemma* lattice.monotone_Sup_of_monotone
- \+ *def* lattice.supr
- \+ *lemma* lattice.supr_and
- \+ *lemma* lattice.supr_comm
- \+ *lemma* lattice.supr_congr_Prop
- \+ *lemma* lattice.supr_const
- \+ *lemma* lattice.supr_empty
- \+ *lemma* lattice.supr_emptyset
- \+ *lemma* lattice.supr_exists
- \+ *lemma* lattice.supr_false
- \+ *lemma* lattice.supr_insert
- \+ *lemma* lattice.supr_le
- \+ *lemma* lattice.supr_le_iff
- \+ *lemma* lattice.supr_le_supr2
- \+ *lemma* lattice.supr_le_supr
- \+ *lemma* lattice.supr_le_supr_const
- \+ *lemma* lattice.supr_or
- \+ *lemma* lattice.supr_prod
- \+ *lemma* lattice.supr_sigma
- \+ *lemma* lattice.supr_singleton
- \+ *lemma* lattice.supr_subtype
- \+ *lemma* lattice.supr_sum
- \+ *lemma* lattice.supr_sup_eq
- \+ *lemma* lattice.supr_supr_eq_left
- \+ *lemma* lattice.supr_supr_eq_right
- \+ *lemma* lattice.supr_true
- \+ *lemma* lattice.supr_union
- \+ *lemma* lattice.supr_unit
- \+ *lemma* lattice.supr_univ
- \+ *theorem* set.subset_union_left
- \+ *theorem* set.subset_union_right

Added algebra/lattice/complete_lattice_experiment.lean
- \+ *theorem* insert_def
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* insert_of_has_insert
- \+ *theorem* inter_def
- \+ *theorem* inter_left_comm
- \+ *def* lattice.Inf
- \+ *lemma* lattice.Inf_empty
- \+ *lemma* lattice.Inf_eq_infi
- \+ *lemma* lattice.Inf_image
- \+ *lemma* lattice.Inf_insert
- \+ *lemma* lattice.Inf_le
- \+ *lemma* lattice.Inf_le_Inf
- \+ *lemma* lattice.Inf_le_Sup
- \+ *lemma* lattice.Inf_le_iff
- \+ *lemma* lattice.Inf_le_of_le
- \+ *lemma* lattice.Inf_singleton
- \+ *lemma* lattice.Inf_union
- \+ *lemma* lattice.Inf_univ
- \+ *def* lattice.Sup
- \+ *lemma* lattice.Sup_empty
- \+ *lemma* lattice.Sup_eq_supr
- \+ *lemma* lattice.Sup_image
- \+ *lemma* lattice.Sup_insert
- \+ *lemma* lattice.Sup_inter_le
- \+ *lemma* lattice.Sup_le
- \+ *lemma* lattice.Sup_le_Sup
- \+ *lemma* lattice.Sup_singleton
- \+ *lemma* lattice.Sup_union
- \+ *lemma* lattice.Sup_univ
- \+ *lemma* lattice.foo'
- \+ *lemma* lattice.foo
- \+ *def* lattice.infi
- \+ *lemma* lattice.infi_and
- \+ *lemma* lattice.infi_comm
- \+ *lemma* lattice.infi_congr_Prop
- \+ *lemma* lattice.infi_const
- \+ *lemma* lattice.infi_empty
- \+ *lemma* lattice.infi_emptyset
- \+ *lemma* lattice.infi_exists
- \+ *lemma* lattice.infi_false
- \+ *lemma* lattice.infi_inf_eq
- \+ *lemma* lattice.infi_infi_eq_left
- \+ *lemma* lattice.infi_infi_eq_right
- \+ *lemma* lattice.infi_insert
- \+ *lemma* lattice.infi_le'
- \+ *lemma* lattice.infi_le
- \+ *lemma* lattice.infi_le_infi2
- \+ *lemma* lattice.infi_le_infi
- \+ *lemma* lattice.infi_le_infi_const
- \+ *lemma* lattice.infi_le_of_le
- \+ *lemma* lattice.infi_or
- \+ *lemma* lattice.infi_prod
- \+ *lemma* lattice.infi_sigma
- \+ *lemma* lattice.infi_singleton
- \+ *lemma* lattice.infi_subtype
- \+ *lemma* lattice.infi_sum
- \+ *lemma* lattice.infi_true
- \+ *lemma* lattice.infi_union
- \+ *lemma* lattice.infi_unit
- \+ *lemma* lattice.infi_univ
- \+ *theorem* lattice.insert_of_has_insert
- \+ *lemma* lattice.le_Inf
- \+ *lemma* lattice.le_Inf_inter
- \+ *lemma* lattice.le_Sup
- \+ *lemma* lattice.le_Sup_iff
- \+ *lemma* lattice.le_Sup_of_le
- \+ *lemma* lattice.le_infi
- \+ *lemma* lattice.le_infi_iff
- \+ *lemma* lattice.le_supr'
- \+ *lemma* lattice.le_supr
- \+ *lemma* lattice.le_supr_of_le
- \+ *lemma* lattice.monotone_Inf_of_monotone
- \+ *lemma* lattice.monotone_Sup_of_monotone
- \+ *def* lattice.supr
- \+ *lemma* lattice.supr_and
- \+ *lemma* lattice.supr_comm
- \+ *lemma* lattice.supr_congr_Prop
- \+ *lemma* lattice.supr_const
- \+ *lemma* lattice.supr_empty
- \+ *lemma* lattice.supr_emptyset
- \+ *lemma* lattice.supr_exists
- \+ *lemma* lattice.supr_false
- \+ *lemma* lattice.supr_insert
- \+ *lemma* lattice.supr_le
- \+ *lemma* lattice.supr_le_iff
- \+ *lemma* lattice.supr_le_supr2
- \+ *lemma* lattice.supr_le_supr
- \+ *lemma* lattice.supr_le_supr_const
- \+ *lemma* lattice.supr_or
- \+ *lemma* lattice.supr_prod
- \+ *lemma* lattice.supr_sigma
- \+ *lemma* lattice.supr_singleton
- \+ *lemma* lattice.supr_subtype
- \+ *lemma* lattice.supr_sum
- \+ *lemma* lattice.supr_sup_eq
- \+ *lemma* lattice.supr_supr_eq_left
- \+ *lemma* lattice.supr_supr_eq_right
- \+ *lemma* lattice.supr_true
- \+ *lemma* lattice.supr_union
- \+ *lemma* lattice.supr_unit
- \+ *lemma* lattice.supr_univ
- \+ *theorem* mem_insert_iff
- \+ *theorem* mem_inter_eq
- \+ *lemma* mem_set_of
- \+ *lemma* mem_set_of_eq
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* mem_univ_eq
- \+ *lemma* nmem_set_of_eq
- \+ *theorem* set_eq_def
- \+ *lemma* set_of_false
- \+ *theorem* singleton_def
- \+ *theorem* singleton_eq_singleton_iff
- \+ *theorem* subset_def
- \+ *theorem* subset_insert
- \+ *theorem* subset_univ
- \+ *theorem* union_def
- \+ *theorem* union_left_comm

Added algebra/lattice/default.lean


Added algebra/lattice/filter.lean
- \+ *lemma* Union_subset_Union2
- \+ *lemma* Union_subset_Union
- \+ *lemma* Union_subset_Union_const
- \+ *theorem* bind_assoc
- \+ *lemma* compl_image_set_of
- \+ *lemma* diff_empty
- \+ *lemma* diff_neq_empty
- \+ *def* directed
- \+ *lemma* directed_of_chain
- \+ *def* directed_on
- \+ *lemma* directed_on_Union
- \+ *lemma* eq_of_sup_eq_inf_eq
- \+ *lemma* filter.Inf_sets_eq_finite
- \+ *lemma* filter.Inter_mem_sets
- \+ *def* filter.at_bot
- \+ *def* filter.at_top
- \+ *theorem* filter.bind_def
- \+ *lemma* filter.bind_mono2
- \+ *lemma* filter.bind_mono
- \+ *lemma* filter.bind_sup
- \+ *lemma* filter.binfi_sup_eq
- \+ *def* filter.cofinite
- \+ *lemma* filter.empty_in_sets_eq_bot
- \+ *lemma* filter.exists_sets_subset_iff
- \+ *lemma* filter.exists_ultrafilter
- \+ *lemma* filter.filter_eq
- \+ *lemma* filter.filter_eq_bot_of_not_nonempty
- \+ *lemma* filter.fmap_principal
- \+ *lemma* filter.forall_sets_neq_empty_iff_neq_bot
- \+ *lemma* filter.image_mem_map
- \+ *lemma* filter.inf_principal
- \+ *lemma* filter.infi_neq_bot_iff_of_directed
- \+ *lemma* filter.infi_neq_bot_of_directed
- \+ *lemma* filter.infi_sets_eq'
- \+ *lemma* filter.infi_sets_eq
- \+ *lemma* filter.infi_sets_induct
- \+ *lemma* filter.infi_sup_eq
- \+ *lemma* filter.inhabited_of_mem_sets
- \+ *lemma* filter.inter_mem_sets
- \+ *def* filter.join
- \+ *lemma* filter.join_principal_eq_Sup
- \+ *lemma* filter.le_lift'
- \+ *lemma* filter.le_map_vmap
- \+ *lemma* filter.le_of_ultrafilter
- \+ *lemma* filter.le_principal_iff
- \+ *lemma* filter.le_vmap_iff_map_le
- \+ *lemma* filter.le_vmap_map
- \+ *lemma* filter.lift'_cong
- \+ *lemma* filter.lift'_id
- \+ *lemma* filter.lift'_inf_principal_eq
- \+ *lemma* filter.lift'_infi
- \+ *lemma* filter.lift'_lift'_assoc
- \+ *lemma* filter.lift'_lift_assoc
- \+ *lemma* filter.lift'_mono'
- \+ *lemma* filter.lift'_mono
- \+ *lemma* filter.lift'_neq_bot_iff
- \+ *lemma* filter.lift'_principal
- \+ *lemma* filter.lift_assoc
- \+ *lemma* filter.lift_comm
- \+ *lemma* filter.lift_infi'
- \+ *lemma* filter.lift_infi
- \+ *lemma* filter.lift_lift'_assoc
- \+ *lemma* filter.lift_lift'_same_eq_lift'
- \+ *lemma* filter.lift_lift'_same_le_lift'
- \+ *lemma* filter.lift_lift_same_eq_lift
- \+ *lemma* filter.lift_lift_same_le_lift
- \+ *lemma* filter.lift_mono'
- \+ *lemma* filter.lift_mono
- \+ *lemma* filter.lift_neq_bot_iff
- \+ *lemma* filter.lift_principal
- \+ *lemma* filter.lift_sets_eq
- \+ *def* filter.map
- \+ *lemma* filter.map_binfi_eq
- \+ *lemma* filter.map_bot
- \+ *lemma* filter.map_compose
- \+ *lemma* filter.map_eq_bot_iff
- \+ *lemma* filter.map_eq_vmap_of_inverse
- \+ *lemma* filter.map_id
- \+ *lemma* filter.map_infi_eq
- \+ *lemma* filter.map_infi_le
- \+ *lemma* filter.map_lift'_eq2
- \+ *lemma* filter.map_lift'_eq
- \+ *lemma* filter.map_lift_eq2
- \+ *lemma* filter.map_lift_eq
- \+ *lemma* filter.map_mono
- \+ *lemma* filter.map_principal
- \+ *lemma* filter.map_sup
- \+ *lemma* filter.map_swap_vmap_swap_eq
- \+ *lemma* filter.map_vmap_le
- \+ *lemma* filter.mem_bind_sets
- \+ *lemma* filter.mem_bot_sets
- \+ *lemma* filter.mem_inf_sets
- \+ *lemma* filter.mem_inf_sets_of_left
- \+ *lemma* filter.mem_inf_sets_of_right
- \+ *lemma* filter.mem_infi_sets
- \+ *lemma* filter.mem_join_sets
- \+ *lemma* filter.mem_lift'
- \+ *lemma* filter.mem_lift'_iff
- \+ *lemma* filter.mem_lift
- \+ *lemma* filter.mem_lift_iff
- \+ *lemma* filter.mem_map
- \+ *lemma* filter.mem_of_finite_Union_ultrafilter
- \+ *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \+ *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \+ *lemma* filter.mem_or_mem_of_ultrafilter
- \+ *lemma* filter.mem_principal_sets
- \+ *lemma* filter.mem_prod_iff
- \+ *lemma* filter.mem_prod_same_iff
- \+ *lemma* filter.mem_pure
- \+ *lemma* filter.mem_return_sets
- \+ *lemma* filter.mem_sets_of_neq_bot
- \+ *lemma* filter.mem_sup_sets
- \+ *lemma* filter.mem_top_sets_iff
- \+ *lemma* filter.mem_vmap_of_mem
- \+ *lemma* filter.monotone_lift'
- \+ *lemma* filter.monotone_lift
- \+ *lemma* filter.monotone_map
- \+ *lemma* filter.monotone_mem_sets
- \+ *lemma* filter.monotone_principal
- \+ *lemma* filter.monotone_vmap
- \+ *def* filter.principal
- \+ *lemma* filter.principal_bind
- \+ *lemma* filter.principal_empty
- \+ *lemma* filter.principal_eq_bot_iff
- \+ *lemma* filter.principal_eq_iff_eq
- \+ *lemma* filter.principal_le_lift'
- \+ *lemma* filter.principal_mono
- \+ *lemma* filter.principal_univ
- \+ *lemma* filter.prod_comm
- \+ *lemma* filter.prod_inf_prod
- \+ *lemma* filter.prod_lift'_lift'
- \+ *lemma* filter.prod_lift_lift
- \+ *lemma* filter.prod_map_map_eq
- \+ *lemma* filter.prod_mem_prod
- \+ *lemma* filter.prod_mono
- \+ *lemma* filter.prod_neq_bot
- \+ *lemma* filter.prod_principal_principal
- \+ *lemma* filter.prod_same_eq
- \+ *lemma* filter.prod_vmap_vmap_eq
- \+ *theorem* filter.pure_def
- \+ *lemma* filter.return_neq_bot
- \+ *lemma* filter.seq_mono
- \+ *lemma* filter.sup_join
- \+ *lemma* filter.sup_principal
- \+ *lemma* filter.supr_join
- \+ *lemma* filter.supr_map
- \+ *lemma* filter.supr_principal
- \+ *lemma* filter.supr_sets_eq
- \+ *def* filter.towards
- \+ *def* filter.ultrafilter
- \+ *lemma* filter.ultrafilter_map
- \+ *lemma* filter.ultrafilter_of_le
- \+ *lemma* filter.ultrafilter_of_spec
- \+ *lemma* filter.ultrafilter_of_split
- \+ *lemma* filter.ultrafilter_of_ultrafilter
- \+ *lemma* filter.ultrafilter_pure
- \+ *lemma* filter.ultrafilter_ultrafilter_of
- \+ *lemma* filter.ultrafilter_unique
- \+ *lemma* filter.univ_mem_sets'
- \+ *lemma* filter.univ_mem_sets
- \+ *lemma* filter.vimage_mem_vmap
- \+ *def* filter.vmap
- \+ *lemma* filter.vmap_eq_lift'
- \+ *lemma* filter.vmap_lift'_eq2
- \+ *lemma* filter.vmap_lift'_eq
- \+ *lemma* filter.vmap_lift_eq2
- \+ *lemma* filter.vmap_lift_eq
- \+ *lemma* filter.vmap_map
- \+ *lemma* filter.vmap_mono
- \+ *lemma* filter.vmap_neq_bot
- \+ *lemma* filter.vmap_neq_bot_of_surj
- \+ *lemma* filter.vmap_principal
- \+ *lemma* filter.vmap_vmap_comp
- \+ *lemma* implies_implies_true_iff
- \+ *lemma* inf_eq_bot_iff_le_compl
- \+ *lemma* lattice.Inf_eq_finite_sets
- \+ *lemma* lattice.Sup_le_iff
- \+ *theorem* map_bind
- \+ *lemma* neg_subset_neg_iff_subset
- \+ *lemma* not_not_mem_iff
- \+ *lemma* prod.fst_swap
- \+ *lemma* prod.mk.eta
- \+ *lemma* prod.snd_swap
- \+ *def* prod.swap
- \+ *lemma* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap
- \+ *lemma* prod.swap_swap_eq
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* sUnion_eq_Union
- \+ *lemma* sUnion_mono
- \+ *theorem* seq_bind_eq
- \+ *theorem* seq_eq_bind_map
- \+ *theorem* set.bind_def
- \+ *lemma* set.diff_right_antimono
- \+ *lemma* set.fmap_eq_image
- \+ *lemma* set.image_eq_vimage_of_inverse
- \+ *lemma* set.image_swap_eq_vimage_swap
- \+ *lemma* set.image_swap_prod
- \+ *lemma* set.mem_image_iff_of_inverse
- \+ *lemma* set.mem_prod_eq
- \+ *lemma* set.mem_seq_iff
- \+ *lemma* set.monotone_inter
- \+ *lemma* set.monotone_prod
- \+ *lemma* set.monotone_set_of
- \+ *theorem* set.ne_empty_iff_exists_mem
- \+ *lemma* set.prod_image_image_eq
- \+ *lemma* set.prod_inter_prod
- \+ *lemma* set.prod_mk_mem_set_prod_eq
- \+ *lemma* set.prod_mono
- \+ *lemma* set.prod_neq_empty_iff
- \+ *lemma* set.prod_singleton_singleton
- \+ *lemma* set.prod_vimage_eq
- \+ *lemma* set.set_of_mem_eq
- \+ *lemma* set.vimage_set_of_eq
- \+ *lemma* singleton_neq_emptyset
- \+ *def* upwards

Added algebra/lattice/fixed_points.lean
- \+ *lemma* ge_of_eq
- \+ *def* lattice.gfp
- \+ *lemma* lattice.gfp_comp
- \+ *lemma* lattice.gfp_eq
- \+ *lemma* lattice.gfp_gfp
- \+ *lemma* lattice.gfp_induct
- \+ *lemma* lattice.gfp_le
- \+ *lemma* lattice.le_gfp
- \+ *lemma* lattice.le_lfp
- \+ *def* lattice.lfp
- \+ *lemma* lattice.lfp_comp
- \+ *lemma* lattice.lfp_eq
- \+ *lemma* lattice.lfp_induct
- \+ *lemma* lattice.lfp_le
- \+ *lemma* lattice.lfp_lfp
- \+ *lemma* lattice.monotone_gfp
- \+ *lemma* lattice.monotone_lfp

Added algebra/lattice/zorn.lean
- \+ *def* zorn.chain
- \+ *lemma* zorn.chain_chain_closure
- \+ *lemma* zorn.chain_closure_closure
- \+ *lemma* zorn.chain_closure_empty
- \+ *lemma* zorn.chain_closure_succ_fixpoint
- \+ *lemma* zorn.chain_closure_succ_fixpoint_iff
- \+ *lemma* zorn.chain_closure_total
- \+ *lemma* zorn.chain_insert
- \+ *lemma* zorn.chain_succ
- \+ *def* zorn.is_max_chain
- \+ *def* zorn.max_chain
- \+ *lemma* zorn.max_chain_spec
- \+ *def* zorn.succ_chain
- \+ *lemma* zorn.succ_increasing
- \+ *lemma* zorn.succ_spec
- \+ *def* zorn.super_chain
- \+ *lemma* zorn.super_of_not_max
- \+ *lemma* zorn.zorn
- \+ *lemma* zorn.zorn_weak_order

Added algebra/order.lean
- \+ *lemma* comp_le_comp_left_of_monotone
- \+ *lemma* le_dual_eq_le
- \+ *theorem* le_max_left_iff_true
- \+ *theorem* le_max_right_iff_true
- \+ *theorem* max.left_comm
- \+ *theorem* max.right_comm
- \+ *theorem* min_right_comm
- \+ *def* monotone
- \+ *lemma* monotone_app
- \+ *lemma* monotone_comp
- \+ *lemma* monotone_const
- \+ *lemma* monotone_id
- \+ *lemma* monotone_lam
- \+ *def* weak_order_dual

Added algebra/ring.lean
- \+ *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \+ *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \+ *theorem* mul_add_eq_mul_add_iff_sub_mul_add_eq
- \+ *theorem* mul_neg_one_eq_neg
- \+ *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \+ *theorem* sub_mul_add_eq_of_mul_add_eq_mul_add

Added data/bitvec.lean
- \+ *def* bitvec.adc
- \+ *def* bitvec.add_lsb
- \+ *def* bitvec.and
- \+ *def* bitvec.append
- \+ *def* bitvec.bits_to_nat
- \+ *theorem* bitvec.bits_to_nat_to_bool
- \+ *lemma* bitvec.bits_to_nat_to_list
- \+ *def* bitvec.fill_shr
- \+ *def* bitvec.not
- \+ *lemma* bitvec.of_nat_succ
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

Added data/bool.lean
- \+ *theorem* bool.absurd_of_eq_ff_of_eq_tt
- \+ *theorem* bool.band_assoc
- \+ *theorem* bool.band_comm
- \+ *theorem* bool.band_elim_left
- \+ *theorem* bool.band_elim_right
- \+ *theorem* bool.band_eq_ff
- \+ *theorem* bool.band_eq_tt
- \+ *theorem* bool.band_ff
- \+ *theorem* bool.band_intro
- \+ *theorem* bool.band_left_comm
- \+ *theorem* bool.band_self
- \+ *theorem* bool.band_tt
- \+ *theorem* bool.bnot_bnot
- \+ *theorem* bool.bnot_false
- \+ *theorem* bool.bnot_true
- \+ *theorem* bool.bor_assoc
- \+ *theorem* bool.bor_comm
- \+ *theorem* bool.bor_eq_ff
- \+ *theorem* bool.bor_eq_tt
- \+ *theorem* bool.bor_ff
- \+ *theorem* bool.bor_inl
- \+ *theorem* bool.bor_inr
- \+ *theorem* bool.bor_left_comm
- \+ *theorem* bool.bor_tt
- \+ *def* bool.bxor
- \+ *lemma* bool.bxor_assoc
- \+ *lemma* bool.bxor_comm
- \+ *lemma* bool.bxor_ff
- \+ *lemma* bool.bxor_left_comm
- \+ *lemma* bool.bxor_self
- \+ *lemma* bool.bxor_tt
- \+ *theorem* bool.coe_tt
- \+ *theorem* bool.cond_ff
- \+ *theorem* bool.cond_tt
- \+ *theorem* bool.dichotomy
- \+ *theorem* bool.eq_ff_of_bnot_eq_tt
- \+ *theorem* bool.eq_ff_of_ne_tt
- \+ *theorem* bool.eq_tt_of_bnot_eq_ff
- \+ *theorem* bool.eq_tt_of_ne_ff
- \+ *theorem* bool.ff_band
- \+ *theorem* bool.ff_bor
- \+ *lemma* bool.ff_bxor
- \+ *lemma* bool.ff_bxor_ff
- \+ *lemma* bool.ff_bxor_tt
- \+ *theorem* bool.or_of_bor_eq
- \+ *theorem* bool.tt_band
- \+ *theorem* bool.tt_bor
- \+ *lemma* bool.tt_bxor
- \+ *lemma* bool.tt_bxor_ff
- \+ *lemma* bool.tt_bxor_tt

Added data/fin.lean
- \+ *lemma* eq_of_lt_succ_of_not_lt
- \+ *lemma* lt_succ_of_lt
- \+ *def* raise_fin

Added data/hash_map.lean
- \+ *def* bucket_array.as_list
- \+ *def* bucket_array.foldl
- \+ *theorem* bucket_array.foldl_eq
- \+ *lemma* bucket_array.foldl_eq_lem
- \+ *theorem* bucket_array.mem_as_list
- \+ *def* bucket_array.modify
- \+ *def* bucket_array.read
- \+ *def* bucket_array.write
- \+ *def* bucket_array
- \+ *theorem* hash_map.append_of_modify
- \+ *theorem* hash_map.append_of_modify_aux
- \+ *def* hash_map.contains
- \+ *def* hash_map.contains_aux
- \+ *theorem* hash_map.contains_aux_iff
- \+ *theorem* hash_map.contains_iff
- \+ *def* hash_map.entries
- \+ *theorem* hash_map.entries_empty
- \+ *def* hash_map.erase
- \+ *def* hash_map.erase_aux
- \+ *def* hash_map.find
- \+ *def* hash_map.find_aux
- \+ *theorem* hash_map.find_aux_iff
- \+ *theorem* hash_map.find_empty
- \+ *theorem* hash_map.find_erase
- \+ *theorem* hash_map.find_erase_eq
- \+ *theorem* hash_map.find_erase_ne
- \+ *theorem* hash_map.find_iff
- \+ *theorem* hash_map.find_insert
- \+ *theorem* hash_map.find_insert_eq
- \+ *theorem* hash_map.find_insert_ne
- \+ *def* hash_map.fold
- \+ *def* hash_map.insert
- \+ *def* hash_map.insert_all
- \+ *lemma* hash_map.insert_lemma
- \+ *def* hash_map.keys
- \+ *theorem* hash_map.keys_empty
- \+ *theorem* hash_map.mem_erase
- \+ *theorem* hash_map.mem_insert
- \+ *theorem* hash_map.mk_as_list
- \+ *def* hash_map.mk_idx
- \+ *theorem* hash_map.not_contains_empty
- \+ *def* hash_map.of_list
- \+ *def* hash_map.reinsert_aux
- \+ *def* hash_map.replace_aux
- \+ *theorem* hash_map.valid.as_list_length
- \+ *theorem* hash_map.valid.as_list_nodup
- \+ *theorem* hash_map.valid.contains_aux_iff
- \+ *theorem* hash_map.valid.eq'
- \+ *theorem* hash_map.valid.eq
- \+ *theorem* hash_map.valid.erase
- \+ *theorem* hash_map.valid.erase_aux
- \+ *theorem* hash_map.valid.find_aux_iff
- \+ *theorem* hash_map.valid.insert
- \+ *theorem* hash_map.valid.mk
- \+ *theorem* hash_map.valid.modify
- \+ *theorem* hash_map.valid.modify_aux1
- \+ *theorem* hash_map.valid.modify_aux2
- \+ *theorem* hash_map.valid.nodup
- \+ *theorem* hash_map.valid.replace
- \+ *theorem* hash_map.valid.replace_aux
- \+ *def* hash_map.valid
- \+ *theorem* hash_map.valid_aux.eq
- \+ *theorem* hash_map.valid_aux.insert_lemma1
- \+ *theorem* hash_map.valid_aux.nodup
- \+ *theorem* hash_map.valid_aux.unfold_cons
- \+ *def* mk_hash_map

Added data/int/basic.lean
- \+ *lemma* int.neg_add_neg
- \+ *theorem* int.of_nat_add_neg_succ_of_nat_of_ge
- \+ *theorem* int.of_nat_add_neg_succ_of_nat_of_lt
- \+ *def* nat_succ_eq_int_succ
- \+ *theorem* neg_nat_succ
- \+ *theorem* neg_pred
- \+ *theorem* neg_succ
- \+ *theorem* neg_succ_of_nat_eq'
- \+ *theorem* of_nat_sub
- \+ *def* pred
- \+ *theorem* pred_nat_succ
- \+ *theorem* pred_neg_pred
- \+ *theorem* pred_succ
- \+ *def* rec_nat_on
- \+ *theorem* rec_nat_on_neg
- \+ *def* succ
- \+ *theorem* succ_neg_nat_succ
- \+ *theorem* succ_neg_succ
- \+ *theorem* succ_pred

Added data/int/order.lean


Added data/lazy_list.lean
- \+ *def* lazy_list.append
- \+ *def* lazy_list.approx
- \+ *def* lazy_list.filter
- \+ *def* lazy_list.for
- \+ *def* lazy_list.head
- \+ *def* lazy_list.join
- \+ *def* lazy_list.map
- \+ *def* lazy_list.map₂
- \+ *def* lazy_list.nth
- \+ *def* lazy_list.of_list
- \+ *def* lazy_list.singleton
- \+ *def* lazy_list.tail
- \+ *def* lazy_list.to_list
- \+ *def* lazy_list.zip

Added data/list/basic.lean
- \+ *theorem* list.append.assoc
- \+ *theorem* list.append_concat
- \+ *theorem* list.concat_append
- \+ *theorem* list.concat_cons
- \+ *theorem* list.concat_ne_nil
- \+ *theorem* list.concat_nil
- \+ *lemma* list.cons_inj
- \+ *lemma* list.cons_ne_nil
- \+ *def* list.count
- \+ *lemma* list.count_append
- \+ *lemma* list.count_concat
- \+ *lemma* list.count_cons'
- \+ *lemma* list.count_cons
- \+ *lemma* list.count_cons_ge_count
- \+ *lemma* list.count_cons_of_ne
- \+ *lemma* list.count_cons_self
- \+ *lemma* list.count_eq_zero_of_not_mem
- \+ *lemma* list.count_nil
- \+ *lemma* list.count_pos_of_mem
- \+ *lemma* list.count_singleton
- \+ *theorem* list.head_cons
- \+ *lemma* list.head_eq_of_cons_eq
- \+ *theorem* list.index_of_cons
- \+ *theorem* list.index_of_cons_of_eq
- \+ *theorem* list.index_of_cons_of_ne
- \+ *lemma* list.index_of_le_length
- \+ *lemma* list.index_of_lt_length
- \+ *theorem* list.index_of_nil
- \+ *theorem* list.index_of_nth
- \+ *theorem* list.index_of_of_not_mem
- \+ *def* list.inth
- \+ *theorem* list.inth_succ
- \+ *theorem* list.inth_zero
- \+ *def* list.ith
- \+ *lemma* list.ith_succ
- \+ *lemma* list.ith_zero
- \+ *theorem* list.last_congr
- \+ *lemma* list.last_cons_cons
- \+ *lemma* list.last_singleton
- \+ *lemma* list.length_taken_le
- \+ *lemma* list.mem_iff_count_pos
- \+ *lemma* list.mem_of_count_pos
- \+ *lemma* list.not_mem_of_count_eq_zero
- \+ *lemma* list.not_mem_of_index_of_eq_length
- \+ *theorem* list.nth_eq_some
- \+ *def* list.permutations
- \+ *def* list.permutations_aux.F
- \+ *def* list.permutations_aux.eqn_1
- \+ *def* list.permutations_aux.eqn_2
- \+ *def* list.permutations_aux2
- \+ *def* list.permutations_aux
- \+ *theorem* list.tail_cons
- \+ *lemma* list.tail_eq_of_cons_eq
- \+ *theorem* list.tail_nil
- \+ *lemma* list.taken_all
- \+ *lemma* list.taken_all_of_ge
- \+ *lemma* list.taken_cons
- \+ *lemma* list.taken_nil
- \+ *lemma* list.taken_zero

Added data/list/comb.lean
- \+ *theorem* list.all_cons
- \+ *theorem* list.all_eq_tt_iff
- \+ *theorem* list.all_eq_tt_of_forall
- \+ *theorem* list.all_nil
- \+ *theorem* list.any_cons
- \+ *theorem* list.any_eq_tt_iff
- \+ *theorem* list.any_nil
- \+ *theorem* list.any_of_mem
- \+ *def* list.decidable_exists_mem
- \+ *def* list.decidable_forall_mem
- \+ *def* list.dinj
- \+ *def* list.dinj₁
- \+ *def* list.dmap
- \+ *lemma* list.dmap_cons_of_neg
- \+ *lemma* list.dmap_cons_of_pos
- \+ *lemma* list.dmap_nil
- \+ *theorem* list.eq_of_mem_map_pair₁
- \+ *theorem* list.exists_mem_cons_iff
- \+ *theorem* list.exists_mem_cons_of
- \+ *theorem* list.exists_mem_cons_of_exists
- \+ *theorem* list.exists_of_any_eq_tt
- \+ *lemma* list.exists_of_mem_dmap
- \+ *def* list.flat
- \+ *theorem* list.foldl_append
- \+ *theorem* list.foldl_cons
- \+ *theorem* list.foldl_eq_foldr
- \+ *theorem* list.foldl_eq_of_comm_of_assoc
- \+ *theorem* list.foldl_nil
- \+ *theorem* list.foldl_reverse
- \+ *theorem* list.foldr_append
- \+ *theorem* list.foldr_cons
- \+ *theorem* list.foldr_nil
- \+ *theorem* list.foldr_reverse
- \+ *theorem* list.forall_mem_cons
- \+ *theorem* list.forall_mem_cons_iff
- \+ *theorem* list.forall_mem_eq_tt_of_all_eq_tt
- \+ *theorem* list.forall_mem_nil
- \+ *theorem* list.forall_mem_of_forall_mem_cons
- \+ *theorem* list.length_mapAccumR
- \+ *theorem* list.length_mapAccumR₂
- \+ *theorem* list.length_map_accumr
- \+ *theorem* list.length_map_accumr₂
- \+ *theorem* list.length_product
- \+ *theorem* list.length_replicate
- \+ *def* list.mapAccumR
- \+ *def* list.mapAccumR₂
- \+ *def* list.map_accumr
- \+ *def* list.map_accumr₂
- \+ *lemma* list.map_dmap_of_inv_of_pos
- \+ *theorem* list.map₂_nil1
- \+ *theorem* list.map₂_nil2
- \+ *lemma* list.mem_dmap
- \+ *lemma* list.mem_of_dinj_of_mem_dmap
- \+ *theorem* list.mem_of_mem_map_pair₁
- \+ *theorem* list.mem_of_mem_product_left
- \+ *theorem* list.mem_of_mem_product_right
- \+ *theorem* list.mem_product
- \+ *theorem* list.nil_product
- \+ *theorem* list.not_exists_mem_nil
- \+ *lemma* list.not_mem_dmap_of_dinj_of_not_mem
- \+ *theorem* list.of_forall_mem_cons
- \+ *theorem* list.or_exists_of_exists_mem_cons
- \+ *def* list.product
- \+ *theorem* list.product_cons
- \+ *theorem* list.product_nil
- \+ *def* list.replicate
- \+ *theorem* list.unzip_cons'
- \+ *theorem* list.unzip_cons
- \+ *theorem* list.unzip_nil
- \+ *theorem* list.zip_cons_cons
- \+ *theorem* list.zip_nil_left
- \+ *theorem* list.zip_nil_right
- \+ *theorem* list.zip_unzip

Added data/list/default.lean


Added data/list/perm.lean
- \+ *theorem* list.perm.count_eq_count_of_perm
- \+ *theorem* list.perm.eq_nil_of_perm_nil
- \+ *theorem* list.perm.eq_singleton_of_perm
- \+ *theorem* list.perm.eq_singleton_of_perm_inv
- \+ *theorem* list.perm.eqv
- \+ *theorem* list.perm.erase_perm_erase_of_perm
- \+ *theorem* list.perm.foldl_eq_of_perm
- \+ *theorem* list.perm.foldr_eq_of_perm
- \+ *theorem* list.perm.length_eq_length_of_perm
- \+ *theorem* list.perm.length_eq_of_qeq
- \+ *theorem* list.perm.mem_cons_of_qeq
- \+ *theorem* list.perm.mem_head_of_qeq
- \+ *theorem* list.perm.mem_iff_mem_of_perm
- \+ *theorem* list.perm.mem_of_perm
- \+ *theorem* list.perm.mem_tail_of_qeq
- \+ *theorem* list.perm.nodup_of_perm_of_nodup
- \+ *theorem* list.perm.not_mem_of_perm
- \+ *theorem* list.perm.not_perm_nil_cons
- \+ *theorem* list.perm.perm_app
- \+ *theorem* list.perm.perm_app_comm
- \+ *theorem* list.perm.perm_app_inv
- \+ *theorem* list.perm.perm_app_inv_left
- \+ *theorem* list.perm.perm_app_inv_right
- \+ *theorem* list.perm.perm_app_left
- \+ *theorem* list.perm.perm_app_right
- \+ *theorem* list.perm.perm_cons_app
- \+ *theorem* list.perm.perm_cons_app_cons
- \+ *theorem* list.perm.perm_cons_app_simp
- \+ *theorem* list.perm.perm_cons_inv
- \+ *theorem* list.perm.perm_erase
- \+ *theorem* list.perm.perm_erase_dup_of_perm
- \+ *theorem* list.perm.perm_ext
- \+ *theorem* list.perm.perm_filter
- \+ *theorem* list.perm.perm_iff_forall_count_eq_count
- \+ *theorem* list.perm.perm_iff_forall_mem_count_eq_count
- \+ *theorem* list.perm.perm_induction_on
- \+ *theorem* list.perm.perm_insert
- \+ *lemma* list.perm.perm_insert_insert
- \+ *theorem* list.perm.perm_inter
- \+ *theorem* list.perm.perm_inter_left
- \+ *theorem* list.perm.perm_inter_right
- \+ *theorem* list.perm.perm_inv_core
- \+ *theorem* list.perm.perm_map
- \+ *theorem* list.perm.perm_middle
- \+ *theorem* list.perm.perm_middle_simp
- \+ *theorem* list.perm.perm_of_forall_count_eq
- \+ *lemma* list.perm.perm_of_qeq
- \+ *theorem* list.perm.perm_product
- \+ *theorem* list.perm.perm_product_left
- \+ *theorem* list.perm.perm_product_right
- \+ *theorem* list.perm.perm_rev
- \+ *theorem* list.perm.perm_rev_simp
- \+ *theorem* list.perm.perm_union
- \+ *theorem* list.perm.perm_union_left
- \+ *theorem* list.perm.perm_union_right
- \+ *theorem* list.perm.qeq_app
- \+ *theorem* list.perm.qeq_of_mem
- \+ *theorem* list.perm.qeq_split
- \+ *theorem* list.perm.xswap

Added data/list/set.lean
- \+ *lemma* list.disjoint.comm
- \+ *def* list.disjoint
- \+ *lemma* list.disjoint_append_of_disjoint_left
- \+ *lemma* list.disjoint_cons_of_not_mem_of_disjoint
- \+ *lemma* list.disjoint_left
- \+ *lemma* list.disjoint_nil_left
- \+ *lemma* list.disjoint_nil_right
- \+ *lemma* list.disjoint_of_disjoint_append_left_left
- \+ *lemma* list.disjoint_of_disjoint_append_left_right
- \+ *lemma* list.disjoint_of_disjoint_append_right_left
- \+ *lemma* list.disjoint_of_disjoint_append_right_right
- \+ *lemma* list.disjoint_of_disjoint_cons_left
- \+ *lemma* list.disjoint_of_disjoint_cons_right
- \+ *theorem* list.disjoint_of_nodup_append
- \+ *lemma* list.disjoint_of_subset_left
- \+ *lemma* list.disjoint_of_subset_right
- \+ *lemma* list.disjoint_right
- \+ *lemma* list.dmap_nodup_of_dinj
- \+ *theorem* list.eq_or_mem_of_mem_insert
- \+ *lemma* list.erase_append_left
- \+ *lemma* list.erase_append_right
- \+ *lemma* list.erase_cons
- \+ *lemma* list.erase_cons_head
- \+ *lemma* list.erase_cons_tail
- \+ *def* list.erase_dup
- \+ *theorem* list.erase_dup_cons_of_mem
- \+ *theorem* list.erase_dup_cons_of_not_mem
- \+ *theorem* list.erase_dup_eq_of_nodup
- \+ *theorem* list.erase_dup_nil
- \+ *theorem* list.erase_dup_sublist
- \+ *theorem* list.erase_dup_subset
- \+ *lemma* list.erase_nil
- \+ *lemma* list.erase_of_not_mem
- \+ *lemma* list.erase_sublist
- \+ *lemma* list.erase_subset
- \+ *theorem* list.forall_mem_insert_of_forall_mem
- \+ *theorem* list.forall_mem_inter_of_forall_left
- \+ *theorem* list.forall_mem_inter_of_forall_right
- \+ *theorem* list.forall_mem_of_forall_mem_union_left
- \+ *theorem* list.forall_mem_of_forall_mem_union_right
- \+ *theorem* list.forall_mem_union
- \+ *theorem* list.insert.def
- \+ *theorem* list.insert_nil
- \+ *theorem* list.insert_of_mem
- \+ *theorem* list.insert_of_not_mem
- \+ *theorem* list.inter_cons_of_mem
- \+ *theorem* list.inter_cons_of_not_mem
- \+ *theorem* list.inter_eq_nil_of_disjoint
- \+ *theorem* list.inter_nil
- \+ *lemma* list.length_erase_of_mem
- \+ *theorem* list.length_insert_of_mem
- \+ *theorem* list.length_insert_of_not_mem
- \+ *theorem* list.length_upto
- \+ *theorem* list.lt_of_mem_upto
- \+ *theorem* list.mem_erase_dup
- \+ *theorem* list.mem_erase_dup_iff
- \+ *theorem* list.mem_erase_of_ne_of_mem
- \+ *theorem* list.mem_erase_of_nodup
- \+ *theorem* list.mem_insert_iff
- \+ *theorem* list.mem_insert_of_mem
- \+ *theorem* list.mem_insert_self
- \+ *theorem* list.mem_inter_iff
- \+ *theorem* list.mem_inter_of_mem_of_mem
- \+ *theorem* list.mem_of_mem_erase
- \+ *theorem* list.mem_of_mem_erase_dup
- \+ *theorem* list.mem_of_mem_inter_left
- \+ *theorem* list.mem_of_mem_inter_right
- \+ *theorem* list.mem_or_mem_of_mem_union
- \+ *theorem* list.mem_union_iff
- \+ *theorem* list.mem_union_left
- \+ *theorem* list.mem_union_right
- \+ *theorem* list.mem_upto_of_lt
- \+ *theorem* list.mem_upto_succ_of_mem_upto
- \+ *theorem* list.nodup_app_comm
- \+ *theorem* list.nodup_append_of_nodup_of_nodup_of_disjoint
- \+ *theorem* list.nodup_concat
- \+ *theorem* list.nodup_cons
- \+ *theorem* list.nodup_erase_dup
- \+ *theorem* list.nodup_erase_of_nodup
- \+ *theorem* list.nodup_filter
- \+ *theorem* list.nodup_head
- \+ *theorem* list.nodup_insert
- \+ *theorem* list.nodup_inter_of_nodup
- \+ *theorem* list.nodup_map
- \+ *theorem* list.nodup_middle
- \+ *theorem* list.nodup_nil
- \+ *theorem* list.nodup_of_nodup_append_left
- \+ *theorem* list.nodup_of_nodup_append_right
- \+ *theorem* list.nodup_of_nodup_cons
- \+ *theorem* list.nodup_of_nodup_map
- \+ *theorem* list.nodup_of_sublist
- \+ *theorem* list.nodup_product
- \+ *theorem* list.nodup_singleton
- \+ *theorem* list.nodup_union_of_nodup_of_nodup
- \+ *theorem* list.nodup_upto
- \+ *theorem* list.not_mem_of_nodup_cons
- \+ *theorem* list.not_nodup_cons_of_mem
- \+ *theorem* list.not_nodup_cons_of_not_nodup
- \+ *theorem* list.subset_erase_dup
- \+ *theorem* list.union_cons
- \+ *theorem* list.union_nil
- \+ *def* list.upto
- \+ *theorem* list.upto_ne_nil_of_ne_zero
- \+ *theorem* list.upto_nil
- \+ *lemma* list.upto_step
- \+ *theorem* list.upto_succ

Added data/list/sort.lean
- \+ *theorem* list.forall_mem_rel_of_sorted_cons
- \+ *def* list.insertion_sort
- \+ *theorem* list.length_split_le
- \+ *theorem* list.length_split_lt
- \+ *def* list.merge
- \+ *def* list.merge_sort
- \+ *theorem* list.merge_sort_cons_cons
- \+ *def* list.ordered_insert
- \+ *theorem* list.perm_insertion_sort
- \+ *theorem* list.perm_merge
- \+ *theorem* list.perm_merge_sort
- \+ *theorem* list.perm_ordered_insert
- \+ *theorem* list.perm_split
- \+ *def* list.sorted
- \+ *theorem* list.sorted_cons
- \+ *theorem* list.sorted_insert_sort
- \+ *theorem* list.sorted_merge
- \+ *theorem* list.sorted_merge_sort
- \+ *theorem* list.sorted_nil
- \+ *theorem* list.sorted_of_sorted_cons
- \+ *theorem* list.sorted_ordered_insert
- \+ *theorem* list.sorted_singleton
- \+ *def* list.split
- \+ *theorem* list.split_cons_of_eq
- \+ *theorem* nat.add_pos_iff_pos_or_pos
- \+ *theorem* nat.add_pos_left
- \+ *theorem* nat.add_pos_right
- \+ *lemma* nat.lt_succ_iff_le
- \+ *lemma* nat.succ_le_succ_iff

Added data/nat/basic.lean
- \+ *def* iterate
- \+ *theorem* nat.add_eq_addl
- \+ *theorem* nat.add_one
- \+ *theorem* nat.add_one_ne_zero
- \+ *def* nat.addl
- \+ *lemma* nat.addl_succ_left
- \+ *theorem* nat.addl_succ_right
- \+ *lemma* nat.addl_zero_left
- \+ *theorem* nat.addl_zero_right
- \+ *theorem* nat.discriminate
- \+ *theorem* nat.eq_zero_of_add_eq_zero
- \+ *theorem* nat.eq_zero_or_eq_succ_pred
- \+ *theorem* nat.exists_eq_succ_of_ne_zero
- \+ *theorem* nat.one_add
- \+ *lemma* nat.one_succ_zero
- \+ *theorem* nat.sub_induction
- \+ *theorem* nat.succ_add_eq_succ_add
- \+ *theorem* nat.succ_inj
- \+ *theorem* nat.two_step_induction
- \+ *lemma* nat.zero_has_zero

Added data/nat/bquant.lean
- \+ *def* ball'
- \+ *def* ball
- \+ *theorem* ball_of_ball_succ'
- \+ *theorem* ball_of_ball_succ
- \+ *theorem* ball_succ_of_ball
- \+ *theorem* ball_zero'
- \+ *theorem* ball_zero
- \+ *theorem* not_ball_of_not
- \+ *theorem* not_ball_succ_of_not_ball
- \+ *def* step_p

Added data/nat/gcd.lean
- \+ *theorem* nat.comprime_one_left
- \+ *theorem* nat.comprime_one_right
- \+ *theorem* nat.coprime_div_gcd_div_gcd
- \+ *theorem* nat.coprime_mul
- \+ *theorem* nat.coprime_mul_right
- \+ *theorem* nat.coprime_of_coprime_dvd_left
- \+ *theorem* nat.coprime_of_coprime_dvd_right
- \+ *theorem* nat.coprime_of_coprime_mul_left
- \+ *theorem* nat.coprime_of_coprime_mul_left_right
- \+ *theorem* nat.coprime_of_coprime_mul_right
- \+ *theorem* nat.coprime_of_coprime_mul_right_right
- \+ *theorem* nat.coprime_of_dvd'
- \+ *theorem* nat.coprime_of_dvd
- \+ *theorem* nat.coprime_pow
- \+ *theorem* nat.coprime_pow_left
- \+ *theorem* nat.coprime_pow_right
- \+ *theorem* nat.coprime_swap
- \+ *theorem* nat.dvd_gcd
- \+ *theorem* nat.dvd_lcm_left
- \+ *theorem* nat.dvd_lcm_right
- \+ *theorem* nat.dvd_of_coprime_of_dvd_mul_left
- \+ *theorem* nat.dvd_of_coprime_of_dvd_mul_right
- \+ *theorem* nat.eq_zero_of_gcd_eq_zero_left
- \+ *theorem* nat.eq_zero_of_gcd_eq_zero_right
- \+ *theorem* nat.exists_coprime
- \+ *theorem* nat.exists_eq_prod_and_dvd_and_dvd
- \+ *theorem* nat.gcd_assoc
- \+ *theorem* nat.gcd_comm
- \+ *theorem* nat.gcd_div
- \+ *theorem* nat.gcd_dvd
- \+ *theorem* nat.gcd_dvd_gcd_mul_left
- \+ *theorem* nat.gcd_dvd_gcd_mul_left_right
- \+ *theorem* nat.gcd_dvd_gcd_mul_right
- \+ *theorem* nat.gcd_dvd_gcd_mul_right_right
- \+ *theorem* nat.gcd_dvd_gcd_of_dvd_left
- \+ *theorem* nat.gcd_dvd_gcd_of_dvd_right
- \+ *theorem* nat.gcd_dvd_left
- \+ *theorem* nat.gcd_dvd_right
- \+ *lemma* nat.gcd_eq_one_of_coprime
- \+ *theorem* nat.gcd_mul_lcm
- \+ *theorem* nat.gcd_mul_left
- \+ *theorem* nat.gcd_mul_left_cancel_of_coprime
- \+ *theorem* nat.gcd_mul_left_cancel_of_coprime_right
- \+ *theorem* nat.gcd_mul_right
- \+ *theorem* nat.gcd_mul_right_cancel_of_coprime
- \+ *theorem* nat.gcd_mul_right_cancel_of_coprime_right
- \+ *theorem* nat.gcd_one_right
- \+ *theorem* nat.gcd_pos_of_pos_left
- \+ *theorem* nat.gcd_pos_of_pos_right
- \+ *theorem* nat.lcm_assoc
- \+ *theorem* nat.lcm_comm
- \+ *theorem* nat.lcm_dvd
- \+ *theorem* nat.lcm_one_left
- \+ *theorem* nat.lcm_one_right
- \+ *theorem* nat.lcm_self
- \+ *theorem* nat.lcm_zero_left
- \+ *theorem* nat.lcm_zero_right
- \+ *theorem* nat.not_coprime_of_dvd_of_dvd

Added data/nat/sub.lean
- \+ *theorem* nat.dist.def
- \+ *theorem* nat.dist.triangle_inequality
- \+ *def* nat.dist
- \+ *theorem* nat.dist_add_add_left
- \+ *theorem* nat.dist_add_add_right
- \+ *theorem* nat.dist_comm
- \+ *theorem* nat.dist_eq_intro
- \+ *theorem* nat.dist_eq_sub_of_ge
- \+ *theorem* nat.dist_eq_sub_of_le
- \+ *theorem* nat.dist_eq_zero
- \+ *theorem* nat.dist_mul_left
- \+ *theorem* nat.dist_mul_right
- \+ *lemma* nat.dist_pos_of_ne
- \+ *theorem* nat.dist_self
- \+ *lemma* nat.dist_succ_succ
- \+ *theorem* nat.dist_zero_left
- \+ *theorem* nat.dist_zero_right
- \+ *theorem* nat.eq_of_dist_eq_zero

Added data/num/basic.lean
- \+ *def* cast_num
- \+ *def* cast_pos_num
- \+ *def* int.of_snum
- \+ *def* int.of_znum
- \+ *def* nat.of_num
- \+ *def* nat.of_pos_num
- \+ *def* num.bit
- \+ *def* num.cmp
- \+ *def* num.of_nat
- \+ *def* num.pred
- \+ *def* num.size
- \+ *def* num.succ'
- \+ *def* num.succ
- \+ *def* num.to_znum
- \+ *def* nzsnum.bit0
- \+ *def* nzsnum.bit1
- \+ *def* nzsnum.drec'
- \+ *def* nzsnum.head
- \+ *def* nzsnum.not
- \+ *def* nzsnum.sign
- \+ *def* nzsnum.tail
- \+ *def* pos_num.bit
- \+ *def* pos_num.cmp
- \+ *def* pos_num.is_one
- \+ *def* pos_num.of_nat
- \+ *def* pos_num.of_nat_succ
- \+ *def* pos_num.pred'
- \+ *def* pos_num.pred
- \+ *def* pos_num.psub
- \+ *def* pos_num.size
- \+ *def* pos_num.succ
- \+ *def* snum.bit0
- \+ *def* snum.bit1
- \+ *def* snum.bit
- \+ *theorem* snum.bit_one
- \+ *theorem* snum.bit_zero
- \+ *def* snum.bits
- \+ *def* snum.cadd
- \+ *def* snum.czadd
- \+ *def* snum.drec'
- \+ *def* snum.head
- \+ *def* snum.not
- \+ *def* snum.pred
- \+ *def* snum.rec'
- \+ *def* snum.sign
- \+ *def* snum.succ
- \+ *def* snum.tail
- \+ *def* snum.test_bit
- \+ *def* znum.pred
- \+ *def* znum.succ
- \+ *def* znum.zneg

Added data/num/bitwise.lean
- \+ *def* num.land
- \+ *def* num.ldiff
- \+ *def* num.lor
- \+ *def* num.lxor
- \+ *def* num.one_bits
- \+ *def* num.shiftl
- \+ *def* num.shiftr
- \+ *def* num.test_bit
- \+ *def* pos_num.land
- \+ *def* pos_num.ldiff
- \+ *def* pos_num.lor
- \+ *def* pos_num.lxor
- \+ *def* pos_num.one_bits
- \+ *def* pos_num.shiftl
- \+ *def* pos_num.shiftr
- \+ *def* pos_num.test_bit

Added data/num/lemmas.lean
- \+ *theorem* num.add_of_nat
- \+ *theorem* num.add_succ
- \+ *theorem* num.add_to_nat
- \+ *theorem* num.add_zero
- \+ *theorem* num.bit_to_nat
- \+ *lemma* num.bitwise_to_nat
- \+ *theorem* num.cmp_dec
- \+ *theorem* num.cmp_swap
- \+ *lemma* num.land_to_nat
- \+ *lemma* num.ldiff_to_nat
- \+ *theorem* num.le_iff_cmp
- \+ *lemma* num.lor_to_nat
- \+ *theorem* num.lt_iff_cmp
- \+ *lemma* num.lxor_to_nat
- \+ *theorem* num.mul_to_nat
- \+ *theorem* num.of_nat_inj
- \+ *theorem* num.of_to_nat
- \+ *theorem* num.one_to_nat
- \+ *theorem* num.pred_to_nat
- \+ *lemma* num.shiftl_to_nat
- \+ *lemma* num.shiftr_to_nat
- \+ *theorem* num.succ'_to_nat
- \+ *theorem* num.succ_to_nat
- \+ *lemma* num.test_bit_to_nat
- \+ *theorem* num.to_nat_inj
- \+ *theorem* num.to_of_nat
- \+ *theorem* num.zero_add
- \+ *theorem* num.zero_to_nat
- \+ *theorem* pos_num.add_one
- \+ *theorem* pos_num.add_succ
- \+ *theorem* pos_num.add_to_nat
- \+ *theorem* pos_num.bit0_of_bit0
- \+ *theorem* pos_num.bit1_of_bit1
- \+ *theorem* pos_num.bit_to_nat
- \+ *theorem* pos_num.cmp_dec
- \+ *lemma* pos_num.cmp_dec_lemma
- \+ *theorem* pos_num.cmp_swap
- \+ *theorem* pos_num.le_iff_cmp
- \+ *theorem* pos_num.lt_iff_cmp
- \+ *theorem* pos_num.mul_to_nat
- \+ *theorem* pos_num.of_to_nat
- \+ *theorem* pos_num.one_add
- \+ *theorem* pos_num.one_to_nat
- \+ *theorem* pos_num.pred'_to_nat
- \+ *theorem* pos_num.pred_to_nat
- \+ *theorem* pos_num.succ_to_nat
- \+ *theorem* pos_num.to_nat_inj
- \+ *theorem* pos_num.to_nat_pos

Added data/pfun.lean
- \+ *def* pfun.as_subtype
- \+ *theorem* pfun.bind_defined
- \+ *def* pfun.dom
- \+ *theorem* pfun.dom_iff_graph
- \+ *def* pfun.eval_opt
- \+ *def* pfun.fn
- \+ *def* pfun.graph
- \+ *theorem* pfun.pure_defined
- \+ *def* pfun.ran
- \+ *def* pfun.restrict
- \+ *def* pfun
- \+ *def* roption.assert
- \+ *theorem* roption.assert_defined
- \+ *theorem* roption.bind_assoc
- \+ *theorem* roption.bind_defined
- \+ *theorem* roption.bind_some_eq_map
- \+ *theorem* roption.dom_iff_mem
- \+ *theorem* roption.eq_ret_of_mem
- \+ *theorem* roption.exists_of_mem_bind
- \+ *theorem* roption.mem_bind
- \+ *theorem* roption.mem_ret
- \+ *theorem* roption.mem_ret_iff
- \+ *theorem* roption.mem_some
- \+ *theorem* roption.mem_unique
- \+ *def* roption.of_option
- \+ *theorem* roption.of_to_option
- \+ *def* roption.restrict
- \+ *theorem* roption.some_bind
- \+ *theorem* roption.to_of_option
- \+ *def* roption.to_option

Added data/pnat.lean
- \+ *def* nat.succ_pnat
- \+ *def* nat.to_pnat'
- \+ *def* nat.to_pnat
- \+ *theorem* pnat.nat_coe_val
- \+ *theorem* pnat.to_pnat'_coe
- \+ *theorem* pnat.to_pnat'_val
- \+ *def* pnat

Added data/rat.lean
- \+ *def* linear_order_cases_on
- \+ *lemma* linear_order_cases_on_eq
- \+ *lemma* linear_order_cases_on_gt
- \+ *lemma* linear_order_cases_on_lt
- \+ *lemma* mul_nonneg_iff_right_nonneg_of_pos
- \+ *lemma* not_antimono
- \+ *def* rat.decidable_nonneg
- \+ *def* rat

Added data/seq/computation.lean
- \+ *def* computation.bind.F
- \+ *def* computation.bind.G
- \+ *def* computation.bind
- \+ *theorem* computation.bind_assoc
- \+ *theorem* computation.bind_congr
- \+ *theorem* computation.bind_promises
- \+ *theorem* computation.bind_ret'
- \+ *theorem* computation.bind_ret
- \+ *def* computation.bisim_o
- \+ *def* computation.cases_on
- \+ *def* computation.corec.F
- \+ *def* computation.corec
- \+ *def* computation.corec_eq
- \+ *def* computation.destruct
- \+ *theorem* computation.destruct_empty
- \+ *theorem* computation.destruct_eq_ret
- \+ *theorem* computation.destruct_eq_think
- \+ *lemma* computation.destruct_map
- \+ *theorem* computation.destruct_ret
- \+ *theorem* computation.destruct_think
- \+ *def* computation.empty
- \+ *theorem* computation.empty_orelse
- \+ *theorem* computation.empty_promises
- \+ *theorem* computation.eq_empty_of_not_terminates
- \+ *lemma* computation.eq_of_bisim
- \+ *theorem* computation.eq_of_ret_mem
- \+ *def* computation.eq_thinkN'
- \+ *def* computation.eq_thinkN
- \+ *theorem* computation.equiv.equivalence
- \+ *theorem* computation.equiv.refl
- \+ *theorem* computation.equiv.symm
- \+ *theorem* computation.equiv.trans
- \+ *def* computation.equiv
- \+ *theorem* computation.equiv_of_mem
- \+ *theorem* computation.equiv_ret_of_mem
- \+ *theorem* computation.exists_of_lift_rel_left
- \+ *theorem* computation.exists_of_lift_rel_right
- \+ *theorem* computation.exists_of_mem_bind
- \+ *theorem* computation.exists_of_mem_map
- \+ *def* computation.exists_results_of_mem
- \+ *def* computation.get
- \+ *theorem* computation.get_bind
- \+ *def* computation.get_eq_of_mem
- \+ *def* computation.get_eq_of_promises
- \+ *theorem* computation.get_equiv
- \+ *def* computation.get_mem
- \+ *def* computation.get_promises
- \+ *theorem* computation.get_ret
- \+ *theorem* computation.get_think
- \+ *theorem* computation.get_thinkN
- \+ *theorem* computation.has_bind_eq_bind
- \+ *theorem* computation.has_map_eq_map
- \+ *def* computation.head
- \+ *theorem* computation.head_empty
- \+ *theorem* computation.head_ret
- \+ *theorem* computation.head_think
- \+ *def* computation.is_bisimulation
- \+ *def* computation.join
- \+ *theorem* computation.le_stable
- \+ *def* computation.length
- \+ *theorem* computation.length_bind
- \+ *theorem* computation.length_ret
- \+ *theorem* computation.length_think
- \+ *theorem* computation.length_thinkN
- \+ *theorem* computation.lift_eq_iff_equiv
- \+ *def* computation.lift_rel.equiv
- \+ *def* computation.lift_rel.imp
- \+ *def* computation.lift_rel.refl
- \+ *theorem* computation.lift_rel.swap
- \+ *def* computation.lift_rel.symm
- \+ *def* computation.lift_rel.trans
- \+ *def* computation.lift_rel
- \+ *def* computation.lift_rel_aux.ret_left
- \+ *def* computation.lift_rel_aux.ret_right
- \+ *theorem* computation.lift_rel_aux.swap
- \+ *def* computation.lift_rel_aux
- \+ *theorem* computation.lift_rel_bind
- \+ *theorem* computation.lift_rel_congr
- \+ *theorem* computation.lift_rel_def
- \+ *theorem* computation.lift_rel_map
- \+ *theorem* computation.lift_rel_mem_cases
- \+ *theorem* computation.lift_rel_of_mem
- \+ *lemma* computation.lift_rel_rec.lem
- \+ *theorem* computation.lift_rel_rec
- \+ *theorem* computation.lift_rel_return
- \+ *theorem* computation.lift_rel_return_left
- \+ *theorem* computation.lift_rel_return_right
- \+ *theorem* computation.lift_rel_think_left
- \+ *theorem* computation.lift_rel_think_right
- \+ *def* computation.lmap
- \+ *def* computation.map
- \+ *lemma* computation.map_comp
- \+ *theorem* computation.map_congr
- \+ *theorem* computation.map_id
- \+ *lemma* computation.map_ret'
- \+ *lemma* computation.map_ret
- \+ *lemma* computation.map_think'
- \+ *lemma* computation.map_think
- \+ *theorem* computation.mem_bind
- \+ *theorem* computation.mem_map
- \+ *def* computation.mem_of_get_eq
- \+ *def* computation.mem_of_promises
- \+ *theorem* computation.mem_promises
- \+ *def* computation.mem_rec_on
- \+ *theorem* computation.mem_unique
- \+ *theorem* computation.not_mem_empty
- \+ *theorem* computation.not_terminates_empty
- \+ *theorem* computation.of_results_bind
- \+ *theorem* computation.of_results_think
- \+ *theorem* computation.of_thinkN_terminates
- \+ *theorem* computation.of_think_mem
- \+ *theorem* computation.of_think_terminates
- \+ *def* computation.orelse
- \+ *theorem* computation.orelse_empty
- \+ *theorem* computation.orelse_ret
- \+ *theorem* computation.orelse_think
- \+ *def* computation.promises
- \+ *theorem* computation.promises_congr
- \+ *def* computation.rel_of_lift_rel
- \+ *def* computation.results.len_unique
- \+ *def* computation.results.length
- \+ *def* computation.results.mem
- \+ *def* computation.results.terminates
- \+ *def* computation.results.val_unique
- \+ *def* computation.results
- \+ *theorem* computation.results_bind
- \+ *def* computation.results_of_terminates'
- \+ *def* computation.results_of_terminates
- \+ *theorem* computation.results_ret
- \+ *theorem* computation.results_think
- \+ *theorem* computation.results_thinkN
- \+ *theorem* computation.results_thinkN_ret
- \+ *theorem* computation.results_think_iff
- \+ *lemma* computation.ret_bind
- \+ *theorem* computation.ret_mem
- \+ *theorem* computation.ret_orelse
- \+ *def* computation.return
- \+ *lemma* computation.return_def
- \+ *def* computation.rmap
- \+ *def* computation.run_for
- \+ *def* computation.tail
- \+ *theorem* computation.tail_empty
- \+ *theorem* computation.tail_ret
- \+ *theorem* computation.tail_think
- \+ *def* computation.terminates
- \+ *theorem* computation.terminates_congr
- \+ *theorem* computation.terminates_def
- \+ *theorem* computation.terminates_map_iff
- \+ *def* computation.terminates_of_lift_rel
- \+ *theorem* computation.terminates_of_mem
- \+ *def* computation.terminates_rec_on
- \+ *def* computation.think
- \+ *def* computation.thinkN
- \+ *theorem* computation.thinkN_equiv
- \+ *theorem* computation.thinkN_mem
- \+ *lemma* computation.think_bind
- \+ *theorem* computation.think_empty
- \+ *theorem* computation.think_equiv
- \+ *theorem* computation.think_mem
- \+ *def* computation

Added data/seq/parallel.lean
- \+ *theorem* computation.exists_of_mem_parallel
- \+ *lemma* computation.map_parallel
- \+ *theorem* computation.mem_parallel
- \+ *def* computation.parallel.aux1
- \+ *def* computation.parallel.aux2
- \+ *def* computation.parallel
- \+ *theorem* computation.parallel_congr_left
- \+ *lemma* computation.parallel_congr_lem
- \+ *theorem* computation.parallel_congr_right
- \+ *theorem* computation.parallel_empty
- \+ *theorem* computation.parallel_promises
- \+ *def* computation.parallel_rec
- \+ *lemma* computation.terminates_parallel.aux
- \+ *theorem* computation.terminates_parallel

Added data/seq/seq.lean
- \+ *def* seq.append
- \+ *lemma* seq.append_assoc
- \+ *lemma* seq.append_nil
- \+ *def* seq.bisim_o
- \+ *def* seq.cases_on
- \+ *lemma* seq.coinduction2
- \+ *lemma* seq.coinduction
- \+ *def* seq.cons
- \+ *lemma* seq.cons_append
- \+ *def* seq.corec.F
- \+ *def* seq.corec
- \+ *def* seq.corec_eq
- \+ *def* seq.destruct
- \+ *theorem* seq.destruct_cons
- \+ *theorem* seq.destruct_eq_cons
- \+ *theorem* seq.destruct_eq_nil
- \+ *theorem* seq.destruct_nil
- \+ *def* seq.drop
- \+ *theorem* seq.dropn_add
- \+ *theorem* seq.dropn_tail
- \+ *lemma* seq.eq_of_bisim
- \+ *lemma* seq.eq_or_mem_of_mem_cons
- \+ *lemma* seq.exists_of_mem_map
- \+ *def* seq.head
- \+ *theorem* seq.head_cons
- \+ *theorem* seq.head_dropn
- \+ *theorem* seq.head_eq_destruct
- \+ *theorem* seq.head_nil
- \+ *def* seq.is_bisimulation
- \+ *def* seq.join
- \+ *lemma* seq.join_append
- \+ *lemma* seq.join_cons
- \+ *lemma* seq.join_cons_cons
- \+ *lemma* seq.join_cons_nil
- \+ *lemma* seq.join_nil
- \+ *theorem* seq.le_stable
- \+ *def* seq.map
- \+ *theorem* seq.map_append
- \+ *lemma* seq.map_comp
- \+ *lemma* seq.map_cons
- \+ *lemma* seq.map_id
- \+ *lemma* seq.map_nil
- \+ *lemma* seq.map_nth
- \+ *lemma* seq.map_tail
- \+ *def* seq.mem_append_left
- \+ *lemma* seq.mem_cons
- \+ *lemma* seq.mem_cons_iff
- \+ *lemma* seq.mem_cons_of_mem
- \+ *theorem* seq.mem_map
- \+ *theorem* seq.mem_rec_on
- \+ *def* seq.nil
- \+ *lemma* seq.nil_append
- \+ *theorem* seq.not_mem_nil
- \+ *def* seq.nth
- \+ *theorem* seq.nth_tail
- \+ *def* seq.of_lazy_list
- \+ *def* seq.of_list
- \+ *def* seq.of_list_append
- \+ *def* seq.of_list_cons
- \+ *def* seq.of_list_nil
- \+ *def* seq.of_mem_append
- \+ *def* seq.of_stream
- \+ *def* seq.of_stream_append
- \+ *def* seq.of_stream_cons
- \+ *def* seq.omap
- \+ *def* seq.split_at
- \+ *def* seq.tail
- \+ *theorem* seq.tail_cons
- \+ *theorem* seq.tail_nil
- \+ *def* seq.take
- \+ *def* seq.to_list'
- \+ *def* seq.to_list
- \+ *def* seq.to_list_or_stream
- \+ *def* seq.to_stream
- \+ *def* seq.unzip
- \+ *def* seq.zip
- \+ *def* seq.zip_with
- \+ *def* seq1.bind
- \+ *theorem* seq1.bind_assoc
- \+ *theorem* seq1.bind_ret
- \+ *def* seq1.join
- \+ *lemma* seq1.join_cons
- \+ *theorem* seq1.join_join
- \+ *theorem* seq1.join_map_ret
- \+ *lemma* seq1.join_nil
- \+ *def* seq1.map
- \+ *theorem* seq1.map_id
- \+ *theorem* seq1.map_join'
- \+ *theorem* seq1.map_join
- \+ *def* seq1.ret
- \+ *theorem* seq1.ret_bind
- \+ *def* seq1.to_seq
- \+ *def* seq1
- \+ *def* seq

Added data/seq/wseq.lean
- \+ *def* wseq.all
- \+ *def* wseq.any
- \+ *def* wseq.append
- \+ *lemma* wseq.append_assoc
- \+ *lemma* wseq.append_nil
- \+ *def* wseq.bind
- \+ *theorem* wseq.bind_assoc
- \+ *theorem* wseq.bind_congr
- \+ *theorem* wseq.bind_ret
- \+ *theorem* wseq.bisim_o.imp
- \+ *def* wseq.bisim_o
- \+ *def* wseq.cases_on
- \+ *def* wseq.collect
- \+ *def* wseq.compute
- \+ *def* wseq.cons
- \+ *lemma* wseq.cons_append
- \+ *theorem* wseq.cons_congr
- \+ *def* wseq.destruct
- \+ *def* wseq.destruct_append.aux
- \+ *lemma* wseq.destruct_append
- \+ *theorem* wseq.destruct_congr
- \+ *theorem* wseq.destruct_congr_iff
- \+ *theorem* wseq.destruct_cons
- \+ *theorem* wseq.destruct_dropn
- \+ *theorem* wseq.destruct_flatten
- \+ *def* wseq.destruct_join.aux
- \+ *lemma* wseq.destruct_join
- \+ *lemma* wseq.destruct_map
- \+ *theorem* wseq.destruct_nil
- \+ *theorem* wseq.destruct_of_seq
- \+ *theorem* wseq.destruct_some_of_destruct_tail_some
- \+ *theorem* wseq.destruct_tail
- \+ *theorem* wseq.destruct_terminates_of_nth_terminates
- \+ *theorem* wseq.destruct_think
- \+ *def* wseq.drop.aux
- \+ *def* wseq.drop.aux_none
- \+ *def* wseq.drop
- \+ *theorem* wseq.dropn_add
- \+ *theorem* wseq.dropn_congr
- \+ *theorem* wseq.dropn_cons
- \+ *theorem* wseq.dropn_nil
- \+ *theorem* wseq.dropn_of_seq
- \+ *theorem* wseq.dropn_tail
- \+ *theorem* wseq.dropn_think
- \+ *theorem* wseq.eq_or_mem_iff_mem
- \+ *theorem* wseq.equiv.equivalence
- \+ *theorem* wseq.equiv.ext
- \+ *theorem* wseq.equiv.refl
- \+ *theorem* wseq.equiv.symm
- \+ *theorem* wseq.equiv.trans
- \+ *def* wseq.equiv
- \+ *theorem* wseq.exists_dropn_of_mem
- \+ *theorem* wseq.exists_nth_of_mem
- \+ *theorem* wseq.exists_of_lift_rel_left
- \+ *theorem* wseq.exists_of_lift_rel_right
- \+ *theorem* wseq.exists_of_mem_bind
- \+ *theorem* wseq.exists_of_mem_join
- \+ *lemma* wseq.exists_of_mem_map
- \+ *def* wseq.filter
- \+ *def* wseq.filter_map
- \+ *def* wseq.find
- \+ *def* wseq.find_index
- \+ *def* wseq.find_indexes
- \+ *def* wseq.flatten
- \+ *theorem* wseq.flatten_congr
- \+ *theorem* wseq.flatten_equiv
- \+ *theorem* wseq.flatten_ret
- \+ *theorem* wseq.flatten_think
- \+ *def* wseq.get
- \+ *def* wseq.head
- \+ *theorem* wseq.head_congr
- \+ *theorem* wseq.head_cons
- \+ *theorem* wseq.head_nil
- \+ *theorem* wseq.head_of_seq
- \+ *theorem* wseq.head_some_of_head_tail_some
- \+ *theorem* wseq.head_some_of_nth_some
- \+ *theorem* wseq.head_terminates_iff
- \+ *theorem* wseq.head_terminates_of_head_tail_terminates
- \+ *theorem* wseq.head_terminates_of_mem
- \+ *theorem* wseq.head_terminates_of_nth_terminates
- \+ *theorem* wseq.head_think
- \+ *def* wseq.index_of
- \+ *def* wseq.indexes_of
- \+ *def* wseq.inits
- \+ *def* wseq.is_empty
- \+ *def* wseq.is_finite
- \+ *def* wseq.join
- \+ *lemma* wseq.join_append
- \+ *theorem* wseq.join_congr
- \+ *def* wseq.join_cons
- \+ *theorem* wseq.join_join
- \+ *theorem* wseq.join_map_ret
- \+ *def* wseq.join_nil
- \+ *theorem* wseq.join_ret
- \+ *def* wseq.join_think
- \+ *def* wseq.length
- \+ *theorem* wseq.length_eq_map
- \+ *def* wseq.lift_rel.equiv
- \+ *def* wseq.lift_rel.refl
- \+ *def* wseq.lift_rel.swap
- \+ *def* wseq.lift_rel.swap_lem
- \+ *def* wseq.lift_rel.symm
- \+ *def* wseq.lift_rel.trans
- \+ *def* wseq.lift_rel
- \+ *theorem* wseq.lift_rel_append
- \+ *theorem* wseq.lift_rel_bind
- \+ *def* wseq.lift_rel_cons
- \+ *theorem* wseq.lift_rel_destruct
- \+ *theorem* wseq.lift_rel_destruct_iff
- \+ *theorem* wseq.lift_rel_dropn_destruct
- \+ *theorem* wseq.lift_rel_flatten
- \+ *theorem* wseq.lift_rel_join.lem
- \+ *theorem* wseq.lift_rel_join
- \+ *theorem* wseq.lift_rel_map
- \+ *def* wseq.lift_rel_nil
- \+ *theorem* wseq.lift_rel_o.imp
- \+ *theorem* wseq.lift_rel_o.imp_right
- \+ *def* wseq.lift_rel_o.swap
- \+ *def* wseq.lift_rel_o
- \+ *def* wseq.lift_rel_think_left
- \+ *def* wseq.lift_rel_think_right
- \+ *def* wseq.map
- \+ *theorem* wseq.map_append
- \+ *lemma* wseq.map_comp
- \+ *theorem* wseq.map_congr
- \+ *lemma* wseq.map_cons
- \+ *theorem* wseq.map_id
- \+ *theorem* wseq.map_join
- \+ *lemma* wseq.map_nil
- \+ *theorem* wseq.map_ret
- \+ *lemma* wseq.map_think
- \+ *def* wseq.mem_append_left
- \+ *theorem* wseq.mem_congr
- \+ *theorem* wseq.mem_cons
- \+ *theorem* wseq.mem_cons_iff
- \+ *theorem* wseq.mem_cons_of_mem
- \+ *theorem* wseq.mem_map
- \+ *theorem* wseq.mem_of_mem_dropn
- \+ *theorem* wseq.mem_of_mem_tail
- \+ *theorem* wseq.mem_rec_on
- \+ *theorem* wseq.mem_think
- \+ *def* wseq.nil
- \+ *lemma* wseq.nil_append
- \+ *theorem* wseq.not_mem_nil
- \+ *def* wseq.nth
- \+ *theorem* wseq.nth_add
- \+ *theorem* wseq.nth_congr
- \+ *theorem* wseq.nth_mem
- \+ *theorem* wseq.nth_of_seq
- \+ *theorem* wseq.nth_tail
- \+ *theorem* wseq.nth_terminates_le
- \+ *def* wseq.of_list
- \+ *def* wseq.of_list_cons
- \+ *def* wseq.of_list_nil
- \+ *def* wseq.of_mem_append
- \+ *def* wseq.of_seq
- \+ *def* wseq.of_stream
- \+ *def* wseq.productive
- \+ *theorem* wseq.productive_congr
- \+ *def* wseq.remove_nth
- \+ *def* wseq.ret
- \+ *theorem* wseq.ret_bind
- \+ *def* wseq.scanl
- \+ *theorem* wseq.seq_destruct_cons
- \+ *theorem* wseq.seq_destruct_nil
- \+ *theorem* wseq.seq_destruct_think
- \+ *def* wseq.split_at
- \+ *def* wseq.tail.aux
- \+ *def* wseq.tail
- \+ *theorem* wseq.tail_congr
- \+ *theorem* wseq.tail_cons
- \+ *theorem* wseq.tail_nil
- \+ *theorem* wseq.tail_of_seq
- \+ *theorem* wseq.tail_think
- \+ *def* wseq.take
- \+ *def* wseq.think
- \+ *lemma* wseq.think_append
- \+ *theorem* wseq.think_congr
- \+ *theorem* wseq.think_equiv
- \+ *def* wseq.to_list'_cons
- \+ *def* wseq.to_list'_map
- \+ *def* wseq.to_list'_nil
- \+ *def* wseq.to_list'_think
- \+ *def* wseq.to_list
- \+ *def* wseq.to_list_cons
- \+ *def* wseq.to_list_nil
- \+ *theorem* wseq.to_list_of_list
- \+ *def* wseq.to_seq
- \+ *theorem* wseq.to_seq_of_seq
- \+ *def* wseq.union
- \+ *def* wseq.update_nth
- \+ *def* wseq.zip
- \+ *def* wseq.zip_with
- \+ *def* wseq

Added data/set/basic.lean
- \+ *lemma* set.empty_inter
- \+ *lemma* set.empty_subset
- \+ *lemma* set.empty_union
- \+ *lemma* set.eq_empty_of_forall_not_mem
- \+ *lemma* set.eq_empty_of_subset_empty
- \+ *lemma* set.eq_of_subset_of_subset
- \+ *lemma* set.ext
- \+ *lemma* set.inter_assoc
- \+ *lemma* set.inter_comm
- \+ *lemma* set.inter_empty
- \+ *lemma* set.inter_self
- \+ *lemma* set.mem_empty_eq
- \+ *lemma* set.mem_of_subset_of_mem
- \+ *lemma* set.ne_empty_of_mem
- \+ *lemma* set.not_mem_empty
- \+ *lemma* set.subset.antisymm
- \+ *lemma* set.subset.refl
- \+ *lemma* set.subset.trans
- \+ *lemma* set.union_assoc
- \+ *lemma* set.union_comm
- \+ *lemma* set.union_empty
- \+ *lemma* set.union_self

Added data/set/default.lean


Added data/set/finite.lean
- \+ *lemma* set.finite_image
- \+ *lemma* set.finite_insert
- \+ *lemma* set.finite_sUnion
- \+ *lemma* set.finite_singleton
- \+ *lemma* set.finite_subset
- \+ *lemma* set.finite_union

Added data/set/lattice.lean
- \+ *def* set.Inter
- \+ *theorem* set.Inter_eq_comp_Union_comp
- \+ *theorem* set.Inter_eq_sInter_image
- \+ *def* set.Union
- \+ *theorem* set.Union_eq_comp_Inter_comp
- \+ *theorem* set.Union_eq_sUnion_image
- \+ *theorem* set.Union_subset
- \+ *theorem* set.Union_subset_iff
- \+ *theorem* set.bInter_empty
- \+ *theorem* set.bInter_insert
- \+ *theorem* set.bInter_pair
- \+ *theorem* set.bInter_singleton
- \+ *theorem* set.bInter_subset_of_mem
- \+ *theorem* set.bInter_union
- \+ *theorem* set.bInter_univ
- \+ *theorem* set.bUnion_empty
- \+ *theorem* set.bUnion_insert
- \+ *theorem* set.bUnion_pair
- \+ *theorem* set.bUnion_singleton
- \+ *theorem* set.bUnion_subset
- \+ *theorem* set.bUnion_union
- \+ *theorem* set.bUnion_univ
- \+ *lemma* set.bounded_forall_empty_iff
- \+ *lemma* set.bounded_forall_image_iff
- \+ *lemma* set.bounded_forall_image_of_bounded_forall
- \+ *lemma* set.bounded_forall_insert_iff
- \+ *theorem* set.compl_Inter
- \+ *theorem* set.compl_Union
- \+ *theorem* set.compl_comp_compl
- \+ *theorem* set.compl_compl
- \+ *theorem* set.compl_compl_image
- \+ *theorem* set.compl_empty
- \+ *theorem* set.compl_eq_univ_diff
- \+ *theorem* set.compl_inter
- \+ *theorem* set.compl_inter_self
- \+ *theorem* set.compl_sInter
- \+ *theorem* set.compl_sUnion
- \+ *theorem* set.compl_union
- \+ *theorem* set.compl_union_self
- \+ *theorem* set.compl_univ
- \+ *theorem* set.diff_eq
- \+ *theorem* set.diff_subset
- \+ *def* set.disjoint
- \+ *lemma* set.disjoint_bot_left
- \+ *lemma* set.disjoint_bot_right
- \+ *lemma* set.disjoint_symm
- \+ *theorem* set.empty_ne_univ
- \+ *theorem* set.eq_of_mem_singleton
- \+ *def* set.eq_on
- \+ *theorem* set.eq_or_mem_of_mem_insert
- \+ *theorem* set.eq_sep_of_subset
- \+ *theorem* set.eq_univ_of_forall
- \+ *theorem* set.eq_univ_of_univ_subset
- \+ *lemma* set.eq_vimage_subtype_val_iff
- \+ *theorem* set.exists_mem_of_ne_empty
- \+ *theorem* set.fix_set_compl
- \+ *theorem* set.forall_insert_of_forall
- \+ *theorem* set.forall_not_of_sep_empty
- \+ *theorem* set.forall_of_forall_insert
- \+ *lemma* set.image_comp
- \+ *theorem* set.image_empty
- \+ *theorem* set.image_eq_image_of_eq_on
- \+ *theorem* set.image_id
- \+ *lemma* set.image_insert_eq
- \+ *lemma* set.image_subset
- \+ *theorem* set.image_subset_iff_subset_vimage
- \+ *theorem* set.image_union
- \+ *theorem* set.insert_comm
- \+ *theorem* set.insert_def
- \+ *theorem* set.insert_eq
- \+ *theorem* set.insert_eq_of_mem
- \+ *theorem* set.insert_ne_empty
- \+ *theorem* set.insert_of_has_insert
- \+ *lemma* set.insert_sdiff_singleton
- \+ *theorem* set.inter_compl_self
- \+ *theorem* set.inter_def
- \+ *theorem* set.inter_distrib_Union_left
- \+ *theorem* set.inter_distrib_left
- \+ *theorem* set.inter_distrib_right
- \+ *theorem* set.inter_empty_of_inter_sUnion_empty
- \+ *theorem* set.inter_eq_compl_compl_union_compl
- \+ *theorem* set.inter_eq_self_of_subset_left
- \+ *theorem* set.inter_eq_self_of_subset_right
- \+ *theorem* set.inter_left_comm
- \+ *theorem* set.inter_right_comm
- \+ *theorem* set.inter_subset_inter
- \+ *theorem* set.inter_subset_inter_left
- \+ *theorem* set.inter_subset_inter_right
- \+ *theorem* set.inter_subset_left
- \+ *theorem* set.inter_subset_right
- \+ *theorem* set.inter_univ
- \+ *theorem* set.mem_Inter
- \+ *theorem* set.mem_Inter_eq
- \+ *theorem* set.mem_Union_eq
- \+ *theorem* set.mem_bInter
- \+ *theorem* set.mem_bUnion
- \+ *theorem* set.mem_compl
- \+ *theorem* set.mem_compl_eq
- \+ *theorem* set.mem_compl_iff
- \+ *theorem* set.mem_diff
- \+ *theorem* set.mem_diff_eq
- \+ *theorem* set.mem_diff_iff
- \+ *theorem* set.mem_image
- \+ *theorem* set.mem_image_compl
- \+ *def* set.mem_image_elim
- \+ *def* set.mem_image_elim_on
- \+ *theorem* set.mem_image_eq
- \+ *theorem* set.mem_image_of_mem
- \+ *theorem* set.mem_insert
- \+ *theorem* set.mem_insert_iff
- \+ *theorem* set.mem_insert_of_mem
- \+ *theorem* set.mem_inter
- \+ *theorem* set.mem_inter_eq
- \+ *theorem* set.mem_inter_iff
- \+ *theorem* set.mem_of_mem_diff
- \+ *theorem* set.mem_of_mem_insert_of_ne
- \+ *theorem* set.mem_of_mem_inter_left
- \+ *theorem* set.mem_of_mem_inter_right
- \+ *theorem* set.mem_or_mem_of_mem_union
- \+ *theorem* set.mem_powerset
- \+ *theorem* set.mem_powerset_iff
- \+ *theorem* set.mem_sInter
- \+ *theorem* set.mem_sInter_eq
- \+ *theorem* set.mem_sUnion
- \+ *theorem* set.mem_sUnion_eq
- \+ *theorem* set.mem_sep
- \+ *theorem* set.mem_sep_eq
- \+ *theorem* set.mem_sep_iff
- \+ *lemma* set.mem_set_of
- \+ *lemma* set.mem_set_of_eq
- \+ *theorem* set.mem_singleton
- \+ *theorem* set.mem_singleton_iff
- \+ *theorem* set.mem_singleton_of_eq
- \+ *theorem* set.mem_union.elim
- \+ *theorem* set.mem_union_eq
- \+ *theorem* set.mem_union_iff
- \+ *theorem* set.mem_union_left
- \+ *theorem* set.mem_union_right
- \+ *theorem* set.mem_unionl
- \+ *theorem* set.mem_unionr
- \+ *theorem* set.mem_univ
- \+ *theorem* set.mem_univ_eq
- \+ *theorem* set.mem_univ_iff
- \+ *lemma* set.mem_vimage_eq
- \+ *theorem* set.mono_image
- \+ *lemma* set.monotone_vimage
- \+ *lemma* set.nmem_set_of_eq
- \+ *theorem* set.nonempty_of_inter_nonempty_left
- \+ *theorem* set.nonempty_of_inter_nonempty_right
- \+ *theorem* set.not_mem_of_mem_compl
- \+ *theorem* set.not_mem_of_mem_diff
- \+ *theorem* set.not_mem_of_not_mem_sUnion
- \+ *theorem* set.pair_eq_singleton
- \+ *def* set.pairwise_on
- \+ *def* set.sInter
- \+ *theorem* set.sInter_empty
- \+ *theorem* set.sInter_eq_comp_sUnion_compl
- \+ *theorem* set.sInter_image
- \+ *theorem* set.sInter_insert
- \+ *theorem* set.sInter_singleton
- \+ *theorem* set.sInter_subset_of_mem
- \+ *theorem* set.sInter_union
- \+ *theorem* set.sUnion_empty
- \+ *theorem* set.sUnion_eq_compl_sInter_compl
- \+ *theorem* set.sUnion_image
- \+ *theorem* set.sUnion_insert
- \+ *theorem* set.sUnion_singleton
- \+ *theorem* set.sUnion_subset
- \+ *theorem* set.sUnion_subset_iff
- \+ *theorem* set.sUnion_union
- \+ *lemma* set.sdiff_singleton_eq_same
- \+ *theorem* set.sep_subset
- \+ *theorem* set.set_eq_def
- \+ *lemma* set.set_of_false
- \+ *theorem* set.singleton_def
- \+ *theorem* set.singleton_eq_singleton_iff
- \+ *theorem* set.singleton_ne_empty
- \+ *lemma* set.singleton_subset_iff
- \+ *theorem* set.ssubset_def
- \+ *lemma* set.ssubset_insert
- \+ *def* set.strict_subset
- \+ *theorem* set.subset_Inter
- \+ *theorem* set.subset_bInter
- \+ *theorem* set.subset_bUnion_of_mem
- \+ *theorem* set.subset_def
- \+ *theorem* set.subset_empty_iff
- \+ *theorem* set.subset_insert
- \+ *theorem* set.subset_inter
- \+ *theorem* set.subset_of_mem_powerset
- \+ *theorem* set.subset_sInter
- \+ *theorem* set.subset_sUnion_of_mem
- \+ *theorem* set.subset_univ
- \+ *theorem* set.union_compl_self
- \+ *theorem* set.union_def
- \+ *theorem* set.union_diff_cancel
- \+ *theorem* set.union_distrib_Inter_left
- \+ *theorem* set.union_distrib_left
- \+ *theorem* set.union_distrib_right
- \+ *theorem* set.union_eq_compl_compl_inter_compl
- \+ *theorem* set.union_eq_self_of_subset_left
- \+ *theorem* set.union_eq_self_of_subset_right
- \+ *lemma* set.union_insert_eq
- \+ *theorem* set.union_left_comm
- \+ *theorem* set.union_right_comm
- \+ *lemma* set.union_same_compl
- \+ *lemma* set.union_sdiff_same
- \+ *theorem* set.union_subset
- \+ *lemma* set.union_subset_iff
- \+ *theorem* set.union_subset_union
- \+ *theorem* set.univ_def
- \+ *theorem* set.univ_inter
- \+ *def* set.vimage
- \+ *lemma* set.vimage_Union
- \+ *lemma* set.vimage_comp
- \+ *lemma* set.vimage_compl
- \+ *lemma* set.vimage_empty
- \+ *lemma* set.vimage_id
- \+ *lemma* set.vimage_image_eq
- \+ *lemma* set.vimage_inter
- \+ *lemma* set.vimage_mono
- \+ *lemma* set.vimage_sUnion
- \+ *lemma* set.vimage_union
- \+ *lemma* set.vimage_univ

Added data/stream.lean
- \+ *def* stream.all
- \+ *lemma* stream.all_def
- \+ *def* stream.any
- \+ *lemma* stream.any_def
- \+ *lemma* stream.append_append_stream
- \+ *lemma* stream.append_approx_drop
- \+ *def* stream.append_stream
- \+ *lemma* stream.append_stream_head_tail
- \+ *def* stream.apply
- \+ *def* stream.approx
- \+ *lemma* stream.approx_succ
- \+ *lemma* stream.approx_zero
- \+ *lemma* stream.bisim_simple
- \+ *lemma* stream.coinduction
- \+ *lemma* stream.composition
- \+ *def* stream.cons
- \+ *lemma* stream.cons_append_stream
- \+ *lemma* stream.cons_nth_inits_core
- \+ *def* stream.const
- \+ *lemma* stream.const_eq
- \+ *def* stream.corec'
- \+ *lemma* stream.corec'_eq
- \+ *def* stream.corec
- \+ *lemma* stream.corec_def
- \+ *lemma* stream.corec_eq
- \+ *lemma* stream.corec_id_f_eq_iterate
- \+ *lemma* stream.corec_id_id_eq_const
- \+ *def* stream.corec_on
- \+ *def* stream.cycle
- \+ *lemma* stream.cycle_eq
- \+ *lemma* stream.cycle_singleton
- \+ *def* stream.drop
- \+ *lemma* stream.drop_append_stream
- \+ *lemma* stream.drop_const
- \+ *lemma* stream.drop_drop
- \+ *lemma* stream.drop_map
- \+ *lemma* stream.drop_succ
- \+ *lemma* stream.drop_zip
- \+ *lemma* stream.eq_of_bisim
- \+ *lemma* stream.eq_or_mem_of_mem_cons
- \+ *def* stream.even
- \+ *lemma* stream.even_cons_cons
- \+ *lemma* stream.even_interleave
- \+ *lemma* stream.even_tail
- \+ *lemma* stream.exists_of_mem_map
- \+ *def* stream.head
- \+ *lemma* stream.head_cons
- \+ *lemma* stream.head_even
- \+ *lemma* stream.head_iterate
- \+ *lemma* stream.head_map
- \+ *lemma* stream.head_zip
- \+ *lemma* stream.homomorphism
- \+ *lemma* stream.identity
- \+ *def* stream.inits
- \+ *def* stream.inits_core
- \+ *lemma* stream.inits_core_eq
- \+ *lemma* stream.inits_eq
- \+ *lemma* stream.inits_tail
- \+ *lemma* stream.interchange
- \+ *def* stream.interleave
- \+ *lemma* stream.interleave_eq
- \+ *lemma* stream.interleave_even_odd
- \+ *lemma* stream.interleave_tail_tail
- \+ *def* stream.is_bisimulation
- \+ *def* stream.iterate
- \+ *lemma* stream.iterate_eq
- \+ *lemma* stream.iterate_id
- \+ *def* stream.map
- \+ *lemma* stream.map_append_stream
- \+ *lemma* stream.map_cons
- \+ *lemma* stream.map_const
- \+ *lemma* stream.map_eq
- \+ *lemma* stream.map_eq_apply
- \+ *lemma* stream.map_id
- \+ *lemma* stream.map_iterate
- \+ *lemma* stream.map_map
- \+ *lemma* stream.map_tail
- \+ *lemma* stream.mem_append_stream_left
- \+ *lemma* stream.mem_append_stream_right
- \+ *lemma* stream.mem_cons
- \+ *lemma* stream.mem_cons_of_mem
- \+ *lemma* stream.mem_const
- \+ *lemma* stream.mem_cycle
- \+ *lemma* stream.mem_interleave_left
- \+ *lemma* stream.mem_interleave_right
- \+ *lemma* stream.mem_map
- \+ *lemma* stream.mem_of_mem_even
- \+ *lemma* stream.mem_of_mem_odd
- \+ *lemma* stream.mem_of_nth_eq
- \+ *def* stream.nats
- \+ *lemma* stream.nats_eq
- \+ *lemma* stream.nil_append_stream
- \+ *def* stream.nth
- \+ *lemma* stream.nth_approx
- \+ *lemma* stream.nth_const
- \+ *lemma* stream.nth_drop
- \+ *lemma* stream.nth_even
- \+ *lemma* stream.nth_inits
- \+ *lemma* stream.nth_interleave_left
- \+ *lemma* stream.nth_interleave_right
- \+ *lemma* stream.nth_map
- \+ *lemma* stream.nth_nats
- \+ *lemma* stream.nth_odd
- \+ *lemma* stream.nth_of_bisim
- \+ *lemma* stream.nth_succ
- \+ *lemma* stream.nth_succ_iterate
- \+ *lemma* stream.nth_tails
- \+ *lemma* stream.nth_unfolds_head_tail
- \+ *lemma* stream.nth_zero_cons
- \+ *lemma* stream.nth_zero_iterate
- \+ *lemma* stream.nth_zip
- \+ *def* stream.odd
- \+ *lemma* stream.odd_eq
- \+ *def* stream.pure
- \+ *def* stream.tail
- \+ *lemma* stream.tail_cons
- \+ *lemma* stream.tail_const
- \+ *lemma* stream.tail_drop
- \+ *lemma* stream.tail_eq_drop
- \+ *lemma* stream.tail_even
- \+ *lemma* stream.tail_inits
- \+ *lemma* stream.tail_interleave
- \+ *lemma* stream.tail_iterate
- \+ *lemma* stream.tail_map
- \+ *lemma* stream.tail_zip
- \+ *def* stream.tails
- \+ *lemma* stream.tails_eq
- \+ *lemma* stream.tails_eq_iterate
- \+ *lemma* stream.take_lemma
- \+ *def* stream.unfolds
- \+ *lemma* stream.unfolds_eq
- \+ *lemma* stream.unfolds_head_eq
- \+ *def* stream.zip
- \+ *lemma* stream.zip_eq
- \+ *lemma* stream.zip_inits_tails
- \+ *def* stream

Added data/vector.lean
- \+ *def* vector.append
- \+ *def* vector.cons
- \+ *theorem* vector.cons_head_tail
- \+ *def* vector.drop
- \+ *def* vector.elim
- \+ *def* vector.head
- \+ *theorem* vector.head_cons
- \+ *def* vector.length
- \+ *def* vector.map
- \+ *def* vector.map_accumr
- \+ *def* vector.map_accumr₂
- \+ *lemma* vector.map_cons
- \+ *lemma* vector.map_nil
- \+ *def* vector.map₂
- \+ *def* vector.nil
- \+ *def* vector.nth
- \+ *def* vector.of_fn
- \+ *def* vector.remove_nth
- \+ *def* vector.repeat
- \+ *def* vector.tail
- \+ *theorem* vector.tail_cons
- \+ *def* vector.take
- \+ *def* vector.to_list
- \+ *lemma* vector.to_list_append
- \+ *lemma* vector.to_list_cons
- \+ *lemma* vector.to_list_drop
- \+ *lemma* vector.to_list_length
- \+ *lemma* vector.to_list_mk
- \+ *lemma* vector.to_list_nil
- \+ *lemma* vector.to_list_take
- \+ *def* vector

Added leanpkg.toml


Added logic/basic.lean
- \+ *theorem* and_distrib
- \+ *theorem* and_distrib_right
- \+ *theorem* and_iff_not_or_not
- \+ *theorem* and_imp_iff
- \+ *theorem* and_implies_left
- \+ *theorem* and_implies_right
- \+ *theorem* and_not_of_not_implies
- \+ *theorem* and_not_self_iff
- \+ *theorem* and_of_and_of_imp_left
- \+ *theorem* and_of_and_of_imp_right
- \+ *theorem* and_of_and_of_implies_of_implies
- \+ *theorem* bexists.elim
- \+ *theorem* bexists.intro
- \+ *theorem* bexists_congr
- \+ *theorem* bexists_implies_distrib
- \+ *theorem* bexists_implies_of_bforall_implies
- \+ *theorem* bexists_not_of_not_bforall
- \+ *theorem* bexists_of_bexists
- \+ *theorem* bexists_of_exists
- \+ *theorem* bexists_or_distrib
- \+ *theorem* bforall_and_distrib
- \+ *theorem* bforall_congr
- \+ *theorem* bforall_implies_of_bexists_implies
- \+ *theorem* bforall_not_of_not_bexists
- \+ *theorem* bforall_of_bforall
- \+ *theorem* bforall_of_forall
- \+ *theorem* bforall_true_iff
- \+ *theorem* by_contradiction
- \+ *theorem* classical.bexists_not_of_not_bforall
- \+ *theorem* classical.exists_not_of_not_forall
- \+ *theorem* classical.forall_or_distrib_left
- \+ *theorem* classical.not_bforall_iff_bexists_not
- \+ *theorem* classical.not_forall_iff
- \+ *theorem* dec_em
- \+ *lemma* eq_iff_le_and_le
- \+ *theorem* exists_and_distrib_left
- \+ *theorem* exists_implies_distrib
- \+ *theorem* exists_implies_of_forall_implies
- \+ *theorem* exists_not_of_not_forall
- \+ *theorem* exists_of_bexists
- \+ *theorem* exists_of_exists
- \+ *theorem* exists_or_distrib
- \+ *theorem* exists_p_iff_p
- \+ *theorem* exists_prop_iff
- \+ *theorem* forall_and_distrib
- \+ *lemma* forall_eq
- \+ *theorem* forall_implies_of_exists_implies
- \+ *theorem* forall_of_bforall
- \+ *theorem* forall_of_forall
- \+ *theorem* forall_or_distrib_left
- \+ *theorem* forall_p_iff_p
- \+ *theorem* forall_true_iff
- \+ *theorem* implies_false_iff
- \+ *theorem* implies_iff
- \+ *theorem* implies_iff_not_or
- \+ *theorem* implies_intro
- \+ *theorem* implies_of_not_or
- \+ *theorem* implies_self
- \+ *theorem* not_and_iff
- \+ *theorem* not_and_not_of_not_or
- \+ *theorem* not_and_of_not_left
- \+ *theorem* not_and_of_not_or_not
- \+ *theorem* not_and_of_not_right
- \+ *theorem* not_and_self_iff
- \+ *theorem* not_bexists_iff_bforall_not
- \+ *theorem* not_bexists_of_bforall_not
- \+ *theorem* not_bforall_iff_bexists_not
- \+ *theorem* not_bforall_of_bexists_not
- \+ *theorem* not_exists_iff
- \+ *theorem* not_exists_of_forall_not
- \+ *theorem* not_forall_iff
- \+ *theorem* not_forall_of_exists_not
- \+ *lemma* not_imp_iff_not_imp
- \+ *theorem* not_implies_iff
- \+ *theorem* not_implies_of_and_not
- \+ *theorem* not_not_elim
- \+ *theorem* not_not_iff
- \+ *theorem* not_not_of_not_implies
- \+ *theorem* not_of_not_implies
- \+ *theorem* not_or_iff
- \+ *theorem* not_or_not_of_not_and'
- \+ *theorem* not_or_not_of_not_and
- \+ *theorem* not_or_of_implies
- \+ *theorem* not_or_of_not_and_not
- \+ *theorem* of_not_implies
- \+ *theorem* or.elim3
- \+ *theorem* or_distrib
- \+ *theorem* or_distrib_right
- \+ *theorem* or_iff_not_and_not
- \+ *theorem* or_iff_or
- \+ *lemma* or_imp_iff_and_imp
- \+ *theorem* or_implies_distrib
- \+ *lemma* or_of_not_implies'
- \+ *lemma* or_of_not_implies
- \+ *theorem* or_of_or_of_implies_left
- \+ *theorem* or_of_or_of_implies_of_implies
- \+ *theorem* or_of_or_of_implies_right
- \+ *theorem* or_resolve_left
- \+ *theorem* or_resolve_right
- \+ *theorem* peirce'
- \+ *theorem* peirce
- \+ *lemma* prod.exists
- \+ *lemma* prod.forall
- \+ *lemma* prod.mk.inj_iff
- \+ *lemma* set_of_subset_set_of
- \+ *theorem* {u}

Added pending/default.lean
- \+ *theorem* nat.shiftl_succ
- \+ *theorem* nat.shiftl_zero

Added theories/set_theory.lean
- \+ *def* Class.Class_to_Cong
- \+ *def* Class.Cong_to_Class
- \+ *def* Class.Union
- \+ *theorem* Class.Union_hom
- \+ *theorem* Class.diff_hom
- \+ *theorem* Class.empty_hom
- \+ *def* Class.fval
- \+ *theorem* Class.fval_ex
- \+ *theorem* Class.insert_hom
- \+ *theorem* Class.inter_hom
- \+ *def* Class.iota
- \+ *theorem* Class.iota_ex
- \+ *theorem* Class.iota_val
- \+ *theorem* Class.mem_hom_left
- \+ *theorem* Class.mem_hom_right
- \+ *theorem* Class.mem_univ
- \+ *theorem* Class.of_Set.inj
- \+ *def* Class.of_Set
- \+ *def* Class.powerset
- \+ *theorem* Class.powerset_hom
- \+ *theorem* Class.sep_hom
- \+ *theorem* Class.subset_hom
- \+ *def* Class.to_Set
- \+ *theorem* Class.to_Set_of_Set
- \+ *theorem* Class.union_hom
- \+ *def* Class.univ
- \+ *def* Class
- \+ *def* Set.Union
- \+ *theorem* Set.Union_lem
- \+ *theorem* Set.Union_singleton
- \+ *def* Set.choice_is_func
- \+ *def* Set.choice_mem
- \+ *def* Set.choice_mem_aux
- \+ *def* Set.empty
- \+ *def* Set.eq_empty
- \+ *def* Set.ext
- \+ *def* Set.ext_iff
- \+ *def* Set.funs
- \+ *def* Set.image.mk
- \+ *def* Set.image
- \+ *theorem* Set.induction_on
- \+ *def* Set.is_func
- \+ *def* Set.map_fval
- \+ *theorem* Set.map_is_func
- \+ *theorem* Set.map_unique
- \+ *def* Set.mem
- \+ *theorem* Set.mem_Union
- \+ *theorem* Set.mem_diff
- \+ *def* Set.mem_empty
- \+ *def* Set.mem_funs
- \+ *def* Set.mem_image
- \+ *def* Set.mem_insert
- \+ *theorem* Set.mem_inter
- \+ *theorem* Set.mem_map
- \+ *theorem* Set.mem_pair
- \+ *theorem* Set.mem_pair_sep
- \+ *theorem* Set.mem_powerset
- \+ *def* Set.mem_prod
- \+ *theorem* Set.mem_sep
- \+ *theorem* Set.mem_singleton'
- \+ *theorem* Set.mem_singleton
- \+ *theorem* Set.mem_union
- \+ *def* Set.omega
- \+ *theorem* Set.omega_succ
- \+ *theorem* Set.omega_zero
- \+ *def* Set.pair
- \+ *def* Set.pair_inj
- \+ *def* Set.pair_mem_prod
- \+ *def* Set.pair_sep
- \+ *def* Set.powerset
- \+ *def* Set.prod
- \+ *theorem* Set.regularity
- \+ *theorem* Set.singleton_inj
- \+ *theorem* Set.subset_iff
- \+ *def* Set.to_set
- \+ *def* Set
- \+ *def* arity
- \+ *def* pSet.Union
- \+ *def* pSet.arity.equiv
- \+ *def* pSet.definable.eq
- \+ *def* pSet.definable.eq_mk
- \+ *def* pSet.definable.resp
- \+ *def* pSet.embed
- \+ *def* pSet.equiv.eq
- \+ *def* pSet.equiv.euc
- \+ *def* pSet.equiv.ext
- \+ *def* pSet.equiv.refl
- \+ *def* pSet.equiv.symm
- \+ *def* pSet.equiv.trans
- \+ *def* pSet.equiv
- \+ *def* pSet.func
- \+ *def* pSet.image
- \+ *def* pSet.lift_mem_embed
- \+ *def* pSet.mem.congr_left
- \+ *def* pSet.mem.congr_right
- \+ *def* pSet.mem.ext
- \+ *def* pSet.mem.mk
- \+ *def* pSet.mem
- \+ *theorem* pSet.mem_Union
- \+ *def* pSet.mem_empty
- \+ *def* pSet.mem_image
- \+ *theorem* pSet.mem_powerset
- \+ *def* pSet.mk_type_func
- \+ *def* pSet.of_nat
- \+ *def* pSet.omega
- \+ *def* pSet.powerset
- \+ *def* pSet.resp.equiv
- \+ *def* pSet.resp.euc
- \+ *def* pSet.resp.eval
- \+ *def* pSet.resp.eval_aux
- \+ *def* pSet.resp.eval_val
- \+ *def* pSet.resp.f
- \+ *def* pSet.resp.refl
- \+ *def* pSet.resp
- \+ *def* pSet.subset.congr_left
- \+ *def* pSet.subset.congr_right
- \+ *def* pSet.to_set
- \+ *def* pSet.type

Added tools/auto/experiments/set_basic.lean
- \+ *lemma* set.bounded_forall_empty_iff
- \+ *lemma* set.bounded_forall_image_iff
- \+ *lemma* set.bounded_forall_image_of_bounded_forall
- \+ *lemma* set.bounded_forall_insert_iff
- \+ *theorem* set.compl_comp_compl
- \+ *theorem* set.compl_compl
- \+ *theorem* set.compl_compl_image
- \+ *theorem* set.compl_empty
- \+ *theorem* set.compl_eq_univ_diff
- \+ *theorem* set.compl_inter
- \+ *theorem* set.compl_inter_self
- \+ *theorem* set.compl_union
- \+ *theorem* set.compl_union_self
- \+ *theorem* set.compl_univ
- \+ *theorem* set.diff_eq
- \+ *theorem* set.diff_subset
- \+ *theorem* set.empty_def
- \+ *theorem* set.empty_ne_univ
- \+ *theorem* set.eq_of_mem_singleton
- \+ *def* set.eq_on
- \+ *theorem* set.eq_or_mem_of_mem_insert
- \+ *theorem* set.eq_sep_of_subset
- \+ *theorem* set.eq_univ_of_forall
- \+ *theorem* set.eq_univ_of_univ_subset
- \+ *theorem* set.exists_mem_of_ne_empty
- \+ *theorem* set.fix_set_compl
- \+ *theorem* set.forall_insert_of_forall
- \+ *theorem* set.forall_not_of_sep_empty
- \+ *theorem* set.forall_of_forall_insert
- \+ *lemma* set.image_comp
- \+ *theorem* set.image_empty
- \+ *theorem* set.image_eq_image_of_eq_on
- \+ *theorem* set.image_id
- \+ *lemma* set.image_insert_eq
- \+ *lemma* set.image_subset
- \+ *theorem* set.image_union
- \+ *theorem* set.insert_comm
- \+ *theorem* set.insert_def
- \+ *theorem* set.insert_eq
- \+ *theorem* set.insert_eq_of_mem
- \+ *theorem* set.insert_ne_empty
- \+ *theorem* set.insert_of_has_insert
- \+ *theorem* set.inter_compl_self
- \+ *theorem* set.inter_def
- \+ *theorem* set.inter_distrib_left
- \+ *theorem* set.inter_distrib_right
- \+ *theorem* set.inter_eq_compl_compl_union_compl
- \+ *theorem* set.inter_eq_self_of_subset_left
- \+ *theorem* set.inter_eq_self_of_subset_right
- \+ *theorem* set.inter_left_comm
- \+ *theorem* set.inter_right_comm
- \+ *theorem* set.inter_subset_inter_left
- \+ *theorem* set.inter_subset_inter_right
- \+ *theorem* set.inter_subset_left
- \+ *theorem* set.inter_subset_right
- \+ *theorem* set.inter_univ
- \+ *theorem* set.mem_compl
- \+ *theorem* set.mem_compl_eq
- \+ *theorem* set.mem_compl_iff
- \+ *theorem* set.mem_diff
- \+ *theorem* set.mem_diff_eq
- \+ *theorem* set.mem_diff_iff
- \+ *theorem* set.mem_image
- \+ *theorem* set.mem_image_compl
- \+ *def* set.mem_image_elim
- \+ *def* set.mem_image_elim_on
- \+ *theorem* set.mem_image_eq
- \+ *theorem* set.mem_image_of_mem
- \+ *theorem* set.mem_insert
- \+ *theorem* set.mem_insert_iff
- \+ *theorem* set.mem_insert_of_mem
- \+ *theorem* set.mem_inter
- \+ *theorem* set.mem_inter_eq
- \+ *theorem* set.mem_inter_iff
- \+ *theorem* set.mem_of_mem_diff
- \+ *theorem* set.mem_of_mem_insert_of_ne
- \+ *theorem* set.mem_of_mem_inter_left
- \+ *theorem* set.mem_of_mem_inter_right
- \+ *theorem* set.mem_or_mem_of_mem_union
- \+ *theorem* set.mem_powerset
- \+ *theorem* set.mem_powerset_iff
- \+ *theorem* set.mem_sep
- \+ *theorem* set.mem_sep_eq
- \+ *theorem* set.mem_sep_iff
- \+ *lemma* set.mem_set_of
- \+ *theorem* set.mem_singleton
- \+ *theorem* set.mem_singleton_iff
- \+ *theorem* set.mem_singleton_of_eq
- \+ *theorem* set.mem_union.elim
- \+ *theorem* set.mem_union_eq
- \+ *theorem* set.mem_union_iff
- \+ *theorem* set.mem_union_left
- \+ *theorem* set.mem_union_right
- \+ *theorem* set.mem_unionl
- \+ *theorem* set.mem_unionr
- \+ *theorem* set.mem_univ
- \+ *theorem* set.mem_univ_eq
- \+ *theorem* set.mem_univ_iff
- \+ *theorem* set.nonempty_of_inter_nonempty_left
- \+ *theorem* set.nonempty_of_inter_nonempty_right
- \+ *theorem* set.not_mem_of_mem_compl
- \+ *theorem* set.not_mem_of_mem_diff
- \+ *theorem* set.pair_eq_singleton
- \+ *theorem* set.sep_subset
- \+ *theorem* set.set_eq_def
- \+ *theorem* set.singleton_def
- \+ *theorem* set.singleton_ne_empty
- \+ *def* set.strict_subset
- \+ *theorem* set.subset_def
- \+ *theorem* set.subset_empty_iff
- \+ *theorem* set.subset_insert
- \+ *theorem* set.subset_inter
- \+ *theorem* set.subset_of_mem_powerset
- \+ *theorem* set.subset_univ
- \+ *theorem* set.union_compl_self
- \+ *theorem* set.union_def
- \+ *theorem* set.union_diff_cancel
- \+ *theorem* set.union_distrib_left
- \+ *theorem* set.union_distrib_right
- \+ *theorem* set.union_eq_compl_compl_inter_compl
- \+ *theorem* set.union_eq_self_of_subset_left
- \+ *theorem* set.union_eq_self_of_subset_right
- \+ *theorem* set.union_left_comm
- \+ *theorem* set.union_right_comm
- \+ *theorem* set.union_subset
- \+ *theorem* set.univ_def
- \+ *theorem* set.univ_inter

Added tools/auto/experiments/test1.lean


Added tools/auto/experiments/test2.lean
- \+ *lemma* NoMember

Added tools/auto/experiments/test3.lean
- \+ *theorem* foo:

Added tools/auto/finish.lean
- \+ *theorem* auto.by_contradiction_trick
- \+ *theorem* auto.classical.implies_iff_not_or
- \+ *def* auto.classical_normalize_lemma_names
- \+ *def* auto.common_normalize_lemma_names
- \+ *theorem* auto.not_and_eq
- \+ *theorem* auto.not_exists_eq
- \+ *theorem* auto.not_forall_eq
- \+ *theorem* auto.not_implies_eq
- \+ *theorem* auto.not_not_eq
- \+ *theorem* auto.not_or_eq
- \+ *theorem* curry_iff
- \+ *theorem* iff_def
- \+ *theorem* implies_and_iff
- \+ *theorem* {u}

Added tools/auto/mk_inhabitant.lean


Added tools/converter/binders.lean
- \+ *lemma* Inf_image
- \+ *lemma* Sup_image
- \+ *lemma* mem_image
- \+ *lemma* {u

Added tools/converter/interactive.lean


Added tools/converter/old_conv.lean


Added tools/parser/modal.lean
- \+ *def* form_of_string

Added tools/parser/parser.lean
- \+ *def* list.deterministic_or
- \+ *def* parser.apply
- \+ *def* parser.chainl1
- \+ *def* parser.chainl1_rest
- \+ *def* parser.chainl
- \+ *def* parser.chainr1
- \+ *def* parser.chainr1_rest
- \+ *def* parser.chainr
- \+ *def* parser.item
- \+ *def* parser.many1
- \+ *def* parser.many
- \+ *def* parser.many_aux
- \+ *def* parser.parse
- \+ *def* parser.parser_bignum
- \+ *def* parser.sat
- \+ *def* parser.sepby1
- \+ *def* parser.sepby
- \+ *def* parser.space
- \+ *def* parser.symb
- \+ *def* parser.take_char
- \+ *def* parser.take_string
- \+ *def* parser.take_string_aux
- \+ *def* parser.token
- \+ *def* parser
- \+ *def* parser_bind
- \+ *def* parser_fmap
- \+ *def* parser_pure
- \+ *lemma* {u
- \+ *lemma* {u}

Added tools/tactic/examples.lean
- \+ *theorem* inter_def
- \+ *lemma* mem_set_of
- \+ *def* my_id
- \+ *def* my_id_def
- \+ *theorem* subset_def
- \+ *theorem* subset_inter
- \+ *theorem* union_def
- \+ *theorem* union_subset

Added tools/tactic/tactic.lean


Added topology/continuity.lean
- \+ *theorem* classical.cases
- \+ *lemma* closure_prod_eq
- \+ *lemma* compact_pi_infinite
- \+ *def* continuous
- \+ *lemma* continuous_Inf_dom
- \+ *lemma* continuous_Inf_rng
- \+ *lemma* continuous_Prop
- \+ *lemma* continuous_bot
- \+ *lemma* continuous_coinduced_dom
- \+ *lemma* continuous_coinduced_rng
- \+ *lemma* continuous_compose
- \+ *lemma* continuous_eq_le_coinduced
- \+ *lemma* continuous_fst
- \+ *lemma* continuous_generated_from
- \+ *lemma* continuous_id
- \+ *lemma* continuous_iff_induced_le
- \+ *lemma* continuous_iff_towards
- \+ *lemma* continuous_induced_dom
- \+ *lemma* continuous_induced_rng
- \+ *lemma* continuous_inf_dom
- \+ *lemma* continuous_inf_rng_left
- \+ *lemma* continuous_inf_rng_right
- \+ *lemma* continuous_infi_dom
- \+ *lemma* continuous_infi_rng
- \+ *lemma* continuous_inl
- \+ *lemma* continuous_inr
- \+ *lemma* continuous_prod_mk
- \+ *lemma* continuous_snd
- \+ *lemma* continuous_subtype_mk
- \+ *lemma* continuous_subtype_nhds_cover
- \+ *lemma* continuous_subtype_val
- \+ *lemma* continuous_sum_rec
- \+ *lemma* continuous_sup_dom_left
- \+ *lemma* continuous_sup_dom_right
- \+ *lemma* continuous_sup_rng
- \+ *lemma* continuous_top
- \+ *lemma* false_neq_true
- \+ *lemma* map_nhds_induced_eq
- \+ *lemma* map_nhds_subtype_val_eq
- \+ *lemma* nhds_induced_eq_vmap
- \+ *lemma* nhds_pi
- \+ *lemma* nhds_prod_eq
- \+ *lemma* open_induced
- \+ *lemma* open_set_prod
- \+ *lemma* open_singleton_true
- \+ *lemma* prod_eq_generate_from
- \+ *lemma* subtype.val_image
- \+ *lemma* univ_eq_true_false

Added topology/topological_space.lean
- \+ *def* closed
- \+ *lemma* closed_Inter
- \+ *lemma* closed_Union_of_locally_finite
- \+ *lemma* closed_closure
- \+ *lemma* closed_compl_iff_open
- \+ *lemma* closed_empty
- \+ *lemma* closed_iff_nhds
- \+ *lemma* closed_sInter
- \+ *lemma* closed_union
- \+ *lemma* closed_univ
- \+ *def* closure
- \+ *lemma* closure_closure
- \+ *lemma* closure_compl_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_eq_compl_interior_compl
- \+ *lemma* closure_eq_iff_closed
- \+ *lemma* closure_eq_nhds
- \+ *lemma* closure_eq_of_closed
- \+ *lemma* closure_minimal
- \+ *lemma* closure_mono
- \+ *lemma* closure_subset_iff_subset_of_closed
- \+ *lemma* closure_union
- \+ *lemma* closure_univ
- \+ *def* compact
- \+ *lemma* compact_adherence_nhdset
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \+ *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* eq_of_nhds_neq_bot
- \+ *lemma* finite_subcover_of_compact
- \+ *lemma* generate_from_le
- \+ *def* interior
- \+ *lemma* interior_compl_eq
- \+ *lemma* interior_empty
- \+ *lemma* interior_eq_iff_open
- \+ *lemma* interior_eq_nhds
- \+ *lemma* interior_eq_of_open
- \+ *lemma* interior_inter
- \+ *lemma* interior_interior
- \+ *lemma* interior_maximal
- \+ *lemma* interior_mono
- \+ *lemma* interior_subset
- \+ *lemma* interior_subset_closure
- \+ *lemma* interior_union_closed_of_interior_empty
- \+ *lemma* interior_univ
- \+ *lemma* le_of_nhds_le_nhds
- \+ *def* locally_finite
- \+ *lemma* map_nhds
- \+ *lemma* mem_nhds_sets
- \+ *lemma* mem_nhds_sets_iff
- \+ *def* nhds
- \+ *lemma* nhds_mono
- \+ *lemma* nhds_neq_bot
- \+ *lemma* nhds_sets
- \+ *lemma* nhds_supr
- \+ *theorem* not_eq_empty_iff_exists
- \+ *def* open'
- \+ *lemma* open_Union
- \+ *lemma* open_compl_iff_closed
- \+ *lemma* open_diff
- \+ *lemma* open_empty
- \+ *lemma* open_iff_nhds
- \+ *lemma* open_inter
- \+ *lemma* open_interior
- \+ *lemma* open_sUnion
- \+ *lemma* open_univ
- \+ *lemma* return_le_nhds
- \+ *lemma* subset_closure
- \+ *lemma* subset_interior_iff_subset_of_open
- \+ *lemma* sup_eq_generate_from
- \+ *lemma* supr_eq_generate_from
- \+ *lemma* t2_space_top
- \+ *def* topological_space.coinduced
- \+ *def* topological_space.generate_from
- \+ *def* topological_space.induced
- \+ *lemma* topological_space.nhds_generate_from
- \+ *lemma* topological_space_eq

Added topology/uniform_space.lean
- \+ *def* Cauchy.gen
- \+ *lemma* Cauchy.monotone_gen
- \+ *def* Cauchy.pure_cauchy
- \+ *lemma* Cauchy.pure_cauchy_dense
- \+ *lemma* Cauchy.uniform_embedding_pure_cauchy
- \+ *def* Cauchy
- \+ *def* cauchy
- \+ *lemma* cauchy_downwards
- \+ *lemma* cauchy_map
- \+ *lemma* cauchy_nhds
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* cauchy_pure
- \+ *lemma* cauchy_vmap
- \+ *lemma* closure_eq_inter_uniformity
- \+ *lemma* comp_le_uniformity3
- \+ *lemma* comp_le_uniformity
- \+ *lemma* comp_mem_uniformity_sets
- \+ *def* comp_rel
- \+ *lemma* comp_symm_of_uniformity
- \+ *lemma* compact_of_totally_bounded_closed
- \+ *lemma* compact_of_totally_bounded_complete
- \+ *lemma* complete_of_closed
- \+ *lemma* complete_space_extension
- \+ *lemma* complete_space_separation
- \+ *lemma* continuous_of_uniform
- \+ *lemma* id_comp_rel
- \+ *def* id_rel
- \+ *lemma* interior_mem_uniformity
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *lemma* le_nhds_of_cauchy_adhp
- \+ *lemma* lift_nhds_left
- \+ *lemma* lift_nhds_right
- \+ *lemma* mem_nhds_left
- \+ *lemma* mem_nhds_right
- \+ *lemma* mem_nhds_uniformity_iff
- \+ *lemma* monotone_comp_rel
- \+ *lemma* nhds_eq_uniformity
- \+ *lemma* nhds_eq_uniformity_prod
- \+ *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *lemma* nhdset_of_mem_uniformity
- \+ *lemma* prod_mk_mem_comp_rel
- \+ *lemma* refl_le_uniformity
- \+ *lemma* refl_mem_uniformity
- \+ *def* separated
- \+ *lemma* separated_equiv
- \+ *lemma* supr_uniformity
- \+ *lemma* swap_id_rel
- \+ *lemma* symm_le_uniformity
- \+ *lemma* symm_of_uniformity
- \+ *lemma* to_topological_space_bot
- \+ *lemma* to_topological_space_mono
- \+ *lemma* to_topological_space_supr
- \+ *lemma* to_topological_space_top
- \+ *lemma* to_topological_space_vmap
- \+ *def* totally_bounded
- \+ *lemma* totally_bounded_iff_filter
- \+ *lemma* totally_bounded_iff_ultrafilter
- \+ *def* uniform_continuous
- \+ *lemma* uniform_continuous_of_embedding
- \+ *lemma* uniform_continuous_quotient_mk
- \+ *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* uniform_continuous_vmap
- \+ *def* uniform_embedding
- \+ *def* uniform_space.vmap
- \+ *lemma* uniform_space_eq
- \+ *def* uniformity
- \+ *lemma* uniformity_eq_symm
- \+ *lemma* uniformity_eq_uniformity_closure
- \+ *lemma* uniformity_eq_uniformity_interior
- \+ *lemma* uniformity_le_symm
- \+ *lemma* uniformity_lift_le_comp
- \+ *lemma* uniformity_lift_le_swap
- \+ *lemma* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_spec
- \+ *lemma* uniformly_extend_unique
- \+ *lemma* vmap_quotient_le_uniformity



## [2017-07-21 01:02:10-07:00](https://github.com/leanprover-community/mathlib/commit/21aca92)
Initial commit
#### Estimated changes

