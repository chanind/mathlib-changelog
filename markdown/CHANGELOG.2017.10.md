## [2017-10-25 22:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/ff43691)
fix(analysis/real): remove import for old file
note: exists_subtype is now subtype.exists in logic/basic
#### Estimated changes
Modified analysis/real.lean




## [2017-10-25 21:55:10-04:00](https://github.com/leanprover-community/mathlib/commit/3cd6229)
refactor(analysis/real): use more coe instead of of_rat
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/measure_theory/borel_space.lean
- \- *lemma* measure_theory.borel_eq_generate_from_Iio_of_rat
- \+ *lemma* measure_theory.borel_eq_generate_from_Iio_rat
- \- *lemma* measure_theory.borel_eq_generate_from_Ioo_of_rat_of_rat
- \+ *lemma* measure_theory.borel_eq_generate_from_Ioo_rat
- \- *lemma* measure_theory.is_topological_basis_Ioo_of_rat_of_rat
- \+ *lemma* measure_theory.is_topological_basis_Ioo_rat

Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/real.lean
- \- *lemma* exists_lt_of_rat_of_rat_gt
- \+ *lemma* exists_lt_rat
- \+ *lemma* exists_rat_btwn
- \+ *lemma* exists_rat_lt

Modified data/int/basic.lean
- \+ *theorem* int.cast_abs
- \+ *theorem* int.cast_max
- \+ *theorem* int.cast_min

Modified data/nat/cast.lean
- \+ *theorem* nat.cast_max
- \+ *theorem* nat.cast_min

Modified data/rat.lean
- \+ *theorem* rat.cast_abs
- \+ *theorem* rat.cast_max
- \+ *theorem* rat.cast_min

Deleted data/subtype.lean
- \- *theorem* exists_subtype
- \- *lemma* forall_subtype



## [2017-10-24 22:57:22-04:00](https://github.com/leanprover-community/mathlib/commit/2dd035a)
Merge remote-tracking branch 'cipher1024/master'
#### Estimated changes
Added meta/expr.lean


Added tactic/norm_num.lean
- \+ *lemma* norm_num.bit0_le_one
- \+ *lemma* norm_num.bit0_le_zero
- \+ *lemma* norm_num.bit1_le_bit0
- \+ *lemma* norm_num.bit1_le_one
- \+ *lemma* norm_num.bit1_le_zero
- \+ *lemma* norm_num.one_le_bit0
- \+ *lemma* norm_num.one_le_bit1
- \+ *lemma* norm_num.one_le_one
- \+ *lemma* norm_num.pow_bit0
- \+ *lemma* norm_num.pow_bit0_helper
- \+ *lemma* norm_num.pow_bit1
- \+ *lemma* norm_num.pow_bit1_helper
- \+ *lemma* norm_num.pow_eq_pow_nat
- \+ *lemma* norm_num.pow_eq_pow_nat_helper
- \+ *lemma* norm_num.pow_one
- \+ *lemma* norm_num.pow_zero
- \+ *lemma* norm_num.zero_le_bit0
- \+ *lemma* norm_num.zero_le_bit1
- \+ *lemma* norm_num.zero_le_one
- \+ *lemma* norm_num.zero_le_zero
- \+ *def* num.add1
- \+ *def* num.add_n
- \+ *lemma* num.bit0_le_bit0
- \+ *lemma* num.denote_add1
- \+ *lemma* num.denote_le_denote_of_num_le
- \+ *lemma* num.denote_le_denote_of_pos_num_le
- \+ *lemma* num.denote_le_denote_of_znum_le
- \+ *def* num.num_le
- \+ *lemma* num.one_le_denote
- \+ *def* num.pos_le
- \+ *lemma* num.zero_le_denote
- \+ *def* num.znum_le
- \+ *def* tactic.interactive.znum.to_neg
- \+ *def* tactic.interactive.znum.to_pos

Added tests/norm_num.lean




## [2017-10-24 22:31:12-04:00](https://github.com/leanprover-community/mathlib/commit/dd9f766)
feat(data/num,data/nat/cast,...): nat,num,int,rat.cast, list stuff
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* inv_comm_of_comm

Modified algebra/group.lean
- \+ *theorem* eq_inv_iff_mul_eq_one
- \+/\- *theorem* eq_inv_mul_iff_mul_eq
- \+/\- *theorem* eq_mul_inv_iff_mul_eq
- \+/\- *theorem* eq_sub_iff_add_eq
- \+ *theorem* inv_eq_iff_mul_eq_one
- \+/\- *theorem* inv_mul_eq_iff_eq_mul
- \+/\- *theorem* mul_inv_eq_iff_eq_mul

Modified algebra/group_power.lean
- \+ *theorem* nat.pow_eq_pow_nat

Modified algebra/ordered_ring.lean
- \+ *theorem* mul_nonneg_iff_right_nonneg_of_pos

Modified analysis/limits.lean
- \+/\- *lemma* mul_add_one_le_pow

Modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* measure_theory.tendsto_of_nat_at_top_at_top

Modified analysis/metric_space.lean


Deleted analysis/of_nat.lean
- \- *lemma* exists_lt_of_nat
- \- *lemma* int_of_nat_eq_of_nat
- \- *def* of_nat
- \- *lemma* of_nat_add
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_one
- \- *lemma* of_nat_pos
- \- *lemma* of_nat_sub
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* zero_le_of_nat

Modified analysis/real.lean
- \+ *theorem* coe_rat_eq_of_rat
- \+ *lemma* exists_lt_nat
- \+/\- *def* lift_rat_fun
- \+/\- *def* lift_rat_op

Modified data/encodable.lean
- \+/\- *def* encodable_of_equiv

Modified data/equiv.lean
- \+ *lemma* equiv.apply_inverse_apply
- \+ *def* equiv.int_equiv_nat
- \+ *def* equiv.int_equiv_nat_sum_nat
- \+ *def* equiv.psigma_equiv_sigma
- \+ *def* equiv.psum_equiv_sum
- \+ *def* equiv.sigma_congr_left
- \+ *def* equiv.sigma_congr_right
- \+ *def* equiv.sigma_equiv_prod
- \+ *def* equiv.sigma_equiv_prod_of_equiv

Modified data/finset/basic.lean


Modified data/int/basic.lean
- \+ *theorem* int.cast_add
- \+ *theorem* int.cast_bit0
- \+ *theorem* int.cast_bit1
- \+ *theorem* int.cast_coe_nat
- \+ *theorem* int.cast_eq_zero
- \+ *theorem* int.cast_id
- \+ *theorem* int.cast_inj
- \+ *theorem* int.cast_le
- \+ *theorem* int.cast_lt
- \+ *theorem* int.cast_lt_zero
- \+ *theorem* int.cast_mul
- \+ *theorem* int.cast_ne_zero
- \+ *theorem* int.cast_neg
- \+ *theorem* int.cast_neg_of_nat
- \+ *theorem* int.cast_neg_succ_of_nat
- \+ *theorem* int.cast_nonneg
- \+ *theorem* int.cast_nonpos
- \+ *theorem* int.cast_of_nat
- \+ *theorem* int.cast_one
- \+ *theorem* int.cast_pos
- \+ *theorem* int.cast_sub
- \+ *theorem* int.cast_sub_nat_nat
- \+ *theorem* int.cast_zero
- \+ *theorem* int.coe_nat_dvd
- \- *theorem* int.coe_nat_dvd_coe_nat_iff
- \- *theorem* int.coe_nat_dvd_coe_nat_of_dvd
- \- *theorem* int.coe_nat_dvd_left
- \- *theorem* int.coe_nat_dvd_right
- \+ *theorem* int.coe_nat_eq_zero
- \+ *theorem* int.coe_nat_inj'
- \+ *theorem* int.coe_nat_le
- \+ *theorem* int.coe_nat_lt
- \+ *theorem* int.coe_nat_ne_zero
- \+ *theorem* int.coe_nat_pos
- \+ *theorem* int.dvd_nat_abs
- \- *theorem* int.dvd_of_coe_nat_dvd_coe_nat
- \+ *theorem* int.mul_cast_comm
- \+ *theorem* int.nat_abs_dvd
- \+ *theorem* int.nat_cast_eq_coe_nat

Modified data/list/basic.lean
- \+ *theorem* list.diff_cons
- \+ *theorem* list.diff_eq_foldl
- \+ *theorem* list.diff_nil
- \+ *theorem* list.erase_comm

Modified data/list/perm.lean
- \+ *theorem* list.count_le_of_subperm
- \+ *theorem* list.countp_le_of_subperm
- \+ *theorem* list.exists_perm_append_of_sublist
- \- *theorem* list.exists_sublist_perm_of_subset_nodup
- \+ *theorem* list.length_le_of_subperm
- \- *theorem* list.mem_iff_mem_of_perm
- \+/\- *theorem* list.mem_of_perm
- \+ *theorem* list.perm.subperm_left
- \+ *theorem* list.perm.subperm_right
- \- *theorem* list.perm_app_inv_right
- \+ *theorem* list.perm_app_right_iff
- \+ *theorem* list.perm_diff_left
- \+ *theorem* list.perm_diff_right
- \+ *theorem* list.perm_subset
- \+ *theorem* list.subperm.antisymm
- \+ *theorem* list.subperm.exists_of_length_lt
- \+ *theorem* list.subperm.perm_of_length_le
- \+ *theorem* list.subperm.refl
- \+ *theorem* list.subperm.trans
- \+ *def* list.subperm
- \+ *theorem* list.subperm_app_left
- \+ *theorem* list.subperm_app_right
- \+ *theorem* list.subperm_cons
- \+ *theorem* list.subperm_of_perm
- \+ *theorem* list.subperm_of_sublist
- \+ *theorem* list.subperm_of_subset_nodup
- \+ *theorem* list.subset_of_subperm

Modified data/list/sort.lean


Added data/nat/cast.lean
- \+ *theorem* nat.cast_add
- \+ *theorem* nat.cast_add_one
- \+ *theorem* nat.cast_bit0
- \+ *theorem* nat.cast_bit1
- \+ *theorem* nat.cast_eq_zero
- \+ *theorem* nat.cast_id
- \+ *theorem* nat.cast_inj
- \+ *theorem* nat.cast_le
- \+ *theorem* nat.cast_lt
- \+ *theorem* nat.cast_mul
- \+ *theorem* nat.cast_ne_zero
- \+ *theorem* nat.cast_nonneg
- \+ *theorem* nat.cast_one
- \+ *theorem* nat.cast_pos
- \+ *theorem* nat.cast_pred
- \+ *theorem* nat.cast_sub
- \+ *theorem* nat.cast_succ
- \+ *theorem* nat.cast_zero
- \+ *theorem* nat.mul_cast_comm

Modified data/num/basic.lean
- \- *def* int.of_znum
- \- *def* int.znum_coe
- \- *def* nat.of_num
- \- *def* nat.of_pos_num
- \- *def* num.nat_num_coe
- \+/\- *def* nzsnum.drec'
- \+/\- *def* snum.drec'
- \+ *def* znum.cmp

Modified data/num/bitwise.lean


Modified data/num/lemmas.lean
- \- *theorem* num.add_to_nat
- \+ *theorem* num.cast_add
- \+ *theorem* num.cast_cmp'
- \+ *theorem* num.cast_cmp
- \+ *theorem* num.cast_inj
- \+ *theorem* num.cast_le
- \+ *theorem* num.cast_lt
- \+ *theorem* num.cast_mul
- \+ *theorem* num.cast_one
- \+ *theorem* num.cast_succ'
- \+ *theorem* num.cast_succ
- \+ *theorem* num.cast_zero
- \- *theorem* num.cmp_dec
- \+ *theorem* num.cmp_eq
- \+/\- *theorem* num.lt_iff_cmp
- \- *theorem* num.mul_to_nat
- \- *theorem* num.one_to_nat
- \- *theorem* num.succ'_to_nat
- \- *theorem* num.succ_to_nat
- \- *theorem* num.zero_to_nat
- \- *theorem* pos_num.add_to_nat
- \+ *theorem* pos_num.cast_add
- \+ *theorem* pos_num.cast_add_comm
- \+ *theorem* pos_num.cast_add_comm_lemma_1
- \+ *theorem* pos_num.cast_add_comm_lemma_2
- \+ *theorem* pos_num.cast_add_one_comm
- \+ *theorem* pos_num.cast_cmp'
- \+ *theorem* pos_num.cast_cmp
- \+ *theorem* pos_num.cast_inj
- \+ *theorem* pos_num.cast_le
- \+ *theorem* pos_num.cast_lt
- \+ *theorem* pos_num.cast_mul
- \+ *theorem* pos_num.cast_one
- \+ *theorem* pos_num.cast_pos
- \+ *theorem* pos_num.cast_succ
- \- *theorem* pos_num.cmp_dec
- \- *theorem* pos_num.cmp_dec_theorem
- \+ *theorem* pos_num.cmp_eq
- \+/\- *theorem* pos_num.lt_iff_cmp
- \- *theorem* pos_num.mul_to_nat
- \+ *theorem* pos_num.one_le_cast
- \- *theorem* pos_num.one_to_nat
- \- *theorem* pos_num.succ_to_nat
- \+/\- *theorem* pos_num.to_nat_inj
- \- *theorem* pos_num.to_nat_pos
- \+ *theorem* znum.cast_one
- \+ *theorem* znum.cast_zero

Deleted data/num/norm_num.lean
- \- *lemma* norm_num.bit0_le_one
- \- *lemma* norm_num.bit0_le_zero
- \- *lemma* norm_num.bit1_le_bit0
- \- *lemma* norm_num.bit1_le_one
- \- *lemma* norm_num.bit1_le_zero
- \- *lemma* norm_num.one_le_bit0
- \- *lemma* norm_num.one_le_bit1
- \- *lemma* norm_num.one_le_one
- \- *lemma* norm_num.pow_bit0
- \- *lemma* norm_num.pow_bit0_helper
- \- *lemma* norm_num.pow_bit1
- \- *lemma* norm_num.pow_bit1_helper
- \- *lemma* norm_num.pow_eq_pow_nat
- \- *lemma* norm_num.pow_eq_pow_nat_helper
- \- *lemma* norm_num.pow_one
- \- *lemma* norm_num.pow_zero
- \- *lemma* norm_num.zero_le_bit0
- \- *lemma* norm_num.zero_le_bit1
- \- *lemma* norm_num.zero_le_one
- \- *lemma* norm_num.zero_le_zero
- \- *def* num.add1
- \- *def* num.add_n
- \- *lemma* num.bit0_le_bit0
- \- *lemma* num.denote_add1
- \- *lemma* num.denote_le_denote_of_num_le
- \- *lemma* num.denote_le_denote_of_pos_num_le
- \- *lemma* num.denote_le_denote_of_znum_le
- \- *def* num.num_le
- \- *lemma* num.one_le_denote
- \- *def* num.pos_le
- \- *lemma* num.zero_le_denote
- \- *def* num.znum_le
- \- *def* tactic.interactive.znum.to_neg
- \- *def* tactic.interactive.znum.to_pos

Modified data/option.lean
- \+ *lemma* option.bind_eq_some
- \+ *lemma* option.bind_none
- \+/\- *lemma* option.bind_some
- \+/\- *def* option.filter
- \+/\- *def* option.guard
- \+/\- *lemma* option.guard_eq_some
- \+/\- *def* option.iget
- \+ *lemma* option.is_some_iff_exists
- \+ *lemma* option.map_eq_some
- \+ *lemma* option.map_none
- \+ *lemma* option.map_some
- \+/\- *lemma* option.mem_def
- \+ *lemma* option.none_ne_some
- \+/\- *lemma* option.some_inj

Modified data/rat.lean
- \- *def* linear_order_cases_on
- \- *theorem* linear_order_cases_on_eq
- \- *theorem* linear_order_cases_on_gt
- \- *theorem* linear_order_cases_on_lt
- \- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+ *theorem* rat.cast_add
- \+ *theorem* rat.cast_add_of_ne_zero
- \+ *theorem* rat.cast_bit0
- \+ *theorem* rat.cast_bit1
- \+ *theorem* rat.cast_coe_int
- \+ *theorem* rat.cast_coe_nat
- \+ *theorem* rat.cast_eq_zero
- \+ *theorem* rat.cast_id
- \+ *theorem* rat.cast_inj
- \+ *theorem* rat.cast_le
- \+ *theorem* rat.cast_lt
- \+ *theorem* rat.cast_lt_zero
- \+ *theorem* rat.cast_mk
- \+ *theorem* rat.cast_mk_of_ne_zero
- \+ *theorem* rat.cast_mul
- \+ *theorem* rat.cast_mul_of_ne_zero
- \+ *theorem* rat.cast_ne_zero
- \+ *theorem* rat.cast_neg
- \+ *theorem* rat.cast_nonneg
- \+ *theorem* rat.cast_nonpos
- \+ *theorem* rat.cast_of_int
- \+ *theorem* rat.cast_one
- \+ *theorem* rat.cast_pos
- \+ *theorem* rat.cast_sub
- \+ *theorem* rat.cast_sub_of_ne_zero
- \+ *theorem* rat.cast_zero
- \- *theorem* rat.coe_int_add
- \+/\- *theorem* rat.coe_int_eq_mk
- \+ *theorem* rat.coe_int_eq_of_int
- \- *theorem* rat.coe_int_inj
- \- *theorem* rat.coe_int_le
- \- *theorem* rat.coe_int_lt
- \- *theorem* rat.coe_int_mul
- \- *theorem* rat.coe_int_neg
- \- *theorem* rat.coe_int_one
- \- *theorem* rat.coe_int_sub
- \- *theorem* rat.coe_nat_rat_eq_mk
- \+ *theorem* rat.denom_dvd
- \+ *theorem* rat.mk_eq_div
- \+ *theorem* rat.mul_cast_comm
- \+ *theorem* rat.num_dvd
- \+ *theorem* rat.of_int_eq_mk

Modified data/set/enumerate.lean


Deleted meta/expr.lean




## [2017-10-17 00:02:03-04:00](https://github.com/leanprover-community/mathlib/commit/2e7651a)
feat(data/num): add tactics for evaluating arithmetic expressions made of literals, including `x \le y` and `x ^ y`
#### Estimated changes
Modified data/num/basic.lean
- \+ *def* cast_znum
- \+ *def* int.znum_coe
- \+ *def* num.nat_num_coe

Modified data/num/lemmas.lean


Added data/num/norm_num.lean
- \+ *lemma* norm_num.bit0_le_one
- \+ *lemma* norm_num.bit0_le_zero
- \+ *lemma* norm_num.bit1_le_bit0
- \+ *lemma* norm_num.bit1_le_one
- \+ *lemma* norm_num.bit1_le_zero
- \+ *lemma* norm_num.one_le_bit0
- \+ *lemma* norm_num.one_le_bit1
- \+ *lemma* norm_num.one_le_one
- \+ *lemma* norm_num.pow_bit0
- \+ *lemma* norm_num.pow_bit0_helper
- \+ *lemma* norm_num.pow_bit1
- \+ *lemma* norm_num.pow_bit1_helper
- \+ *lemma* norm_num.pow_eq_pow_nat
- \+ *lemma* norm_num.pow_eq_pow_nat_helper
- \+ *lemma* norm_num.pow_one
- \+ *lemma* norm_num.pow_zero
- \+ *lemma* norm_num.zero_le_bit0
- \+ *lemma* norm_num.zero_le_bit1
- \+ *lemma* norm_num.zero_le_one
- \+ *lemma* norm_num.zero_le_zero
- \+ *def* num.add1
- \+ *def* num.add_n
- \+ *lemma* num.bit0_le_bit0
- \+ *lemma* num.denote_add1
- \+ *lemma* num.denote_le_denote_of_num_le
- \+ *lemma* num.denote_le_denote_of_pos_num_le
- \+ *lemma* num.denote_le_denote_of_znum_le
- \+ *def* num.num_le
- \+ *lemma* num.one_le_denote
- \+ *def* num.pos_le
- \+ *lemma* num.zero_le_denote
- \+ *def* num.znum_le
- \+ *def* tactic.interactive.znum.to_neg
- \+ *def* tactic.interactive.znum.to_pos

Added meta/expr.lean




## [2017-10-15 02:26:24-04:00](https://github.com/leanprover-community/mathlib/commit/5ad8020)
Merge remote-tracking branch 'minchaowu/master'
#### Estimated changes
Modified analysis/real.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/uniform_space.lean


Modified data/set/basic.lean
- \+ *theorem* set.image_subset_iff
- \- *theorem* set.image_subset_iff_subset_preimage
- \+ *theorem* set.inter_preimage_subset
- \+ *theorem* set.preimage_diff
- \+ *theorem* set.subset_image_union
- \+ *theorem* set.union_preimage_subset

Added data/set/function.lean
- \+ *lemma* set.bij_on.mk
- \+ *def* set.bij_on
- \+ *theorem* set.bij_on_comp
- \+ *theorem* set.bij_on_of_eq_on
- \+ *theorem* set.bij_on_of_inv_on
- \+ *lemma* set.bijective_iff_bij_on_univ
- \+ *theorem* set.eq_on_of_left_inv_of_right_inv
- \+ *lemma* set.image_eq_of_bij_on
- \+ *lemma* set.image_eq_of_maps_to_of_surj_on
- \+ *theorem* set.image_subset_of_maps_to
- \+ *theorem* set.image_subset_of_maps_to_of_subset
- \+ *def* set.inj_on
- \+ *theorem* set.inj_on_comp
- \+ *theorem* set.inj_on_empty
- \+ *lemma* set.inj_on_of_bij_on
- \+ *theorem* set.inj_on_of_eq_on
- \+ *theorem* set.inj_on_of_inj_on_of_subset
- \+ *theorem* set.inj_on_of_left_inv_on
- \+ *lemma* set.injective_iff_inj_on_univ
- \+ *def* set.inv_on
- \+ *def* set.left_inv_on
- \+ *theorem* set.left_inv_on_comp
- \+ *theorem* set.left_inv_on_of_eq_on_left
- \+ *theorem* set.left_inv_on_of_eq_on_right
- \+ *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \+ *def* set.maps_to
- \+ *theorem* set.maps_to_comp
- \+ *lemma* set.maps_to_of_bij_on
- \+ *theorem* set.maps_to_of_eq_on
- \+ *theorem* set.maps_to_univ_univ
- \+ *def* set.right_inv_on
- \+ *theorem* set.right_inv_on_comp
- \+ *theorem* set.right_inv_on_of_eq_on_left
- \+ *theorem* set.right_inv_on_of_eq_on_right
- \+ *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \+ *def* set.surj_on
- \+ *theorem* set.surj_on_comp
- \+ *lemma* set.surj_on_of_bij_on
- \+ *theorem* set.surj_on_of_eq_on
- \+ *theorem* set.surj_on_of_right_inv_on
- \+ *lemma* set.surjective_iff_surj_on_univ

Modified order/filter.lean


Modified order/galois_connection.lean




## [2017-10-15 01:58:58-04:00](https://github.com/leanprover-community/mathlib/commit/8f4327a)
feat(*): working on list/basic, robusting simp proofs
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *theorem* list.prod_repeat
- \- *theorem* list.prod_replicate

Modified algebra/field.lean
- \+ *lemma* division_ring.neg_inv

Modified algebra/functions.lean
- \+ *lemma* lt_max_iff

Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/metric_space.lean


Modified analysis/of_nat.lean


Modified analysis/real.lean
- \+ *lemma* of_rat_inj
- \+ *lemma* of_rat_injective
- \+ *lemma* of_rat_lt
- \- *lemma* of_rat_lt_of_rat

Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/bool.lean
- \- *theorem* bool.band_eq_ff
- \- *theorem* bool.band_eq_tt
- \- *theorem* bool.band_ff
- \- *theorem* bool.band_self
- \- *theorem* bool.band_tt
- \- *theorem* bool.bnot_bnot
- \- *theorem* bool.bor_eq_ff
- \- *theorem* bool.bor_eq_tt
- \- *theorem* bool.bor_ff
- \+/\- *theorem* bool.bor_inl
- \+/\- *theorem* bool.bor_inr
- \- *theorem* bool.bor_tt
- \- *def* bool.bxor
- \- *theorem* bool.bxor_ff
- \- *theorem* bool.bxor_self
- \- *theorem* bool.bxor_tt
- \+ *theorem* bool.coe_sort_ff
- \+ *theorem* bool.coe_sort_tt
- \- *theorem* bool.coe_tt
- \- *theorem* bool.ff_band
- \- *theorem* bool.ff_bor
- \- *theorem* bool.ff_bxor
- \- *theorem* bool.ff_bxor_ff
- \- *theorem* bool.ff_bxor_tt
- \- *theorem* bool.or_of_bor_eq
- \+ *theorem* bool.to_bool_bool
- \+ *theorem* bool.to_bool_false
- \+ *theorem* bool.to_bool_true
- \- *theorem* bool.tt_band
- \- *theorem* bool.tt_bor
- \- *theorem* bool.tt_bxor
- \- *theorem* bool.tt_bxor_ff
- \- *theorem* bool.tt_bxor_tt

Modified data/encodable.lean
- \+ *theorem* encode_injective

Modified data/equiv.lean
- \+ *def* equiv.list_equiv_of_equiv
- \+ *def* equiv.list_equiv_self_of_equiv_nat
- \+ *def* equiv.list_nat_equiv_nat

Modified data/finset/basic.lean
- \+ *theorem* finset.card_range
- \- *theorem* finset.card_upto
- \+ *theorem* finset.exists_mem_insert
- \- *theorem* finset.exists_mem_insert_iff
- \+ *theorem* finset.exists_nat_subset_range
- \- *theorem* finset.exists_nat_subset_upto
- \+ *theorem* finset.forall_mem_insert
- \- *theorem* finset.forall_mem_insert_iff
- \- *theorem* finset.lt_of_mem_upto
- \- *theorem* finset.mem_empty_iff
- \+ *theorem* finset.mem_erase
- \- *theorem* finset.mem_erase_iff
- \+ *theorem* finset.mem_filter
- \- *theorem* finset.mem_filter_iff
- \+/\- *theorem* finset.mem_insert
- \- *theorem* finset.mem_insert_iff
- \+ *theorem* finset.mem_insert_self
- \+/\- *theorem* finset.mem_inter
- \- *theorem* finset.mem_inter_iff
- \+ *theorem* finset.mem_inter_of_mem
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+ *theorem* finset.mem_range
- \+/\- *theorem* finset.mem_sdiff_iff
- \+/\- *theorem* finset.mem_singleton_self
- \+/\- *theorem* finset.mem_to_finset
- \- *theorem* finset.mem_to_finset_iff
- \+ *theorem* finset.mem_to_finset_of_mem
- \+ *theorem* finset.mem_union
- \- *theorem* finset.mem_union_iff
- \- *theorem* finset.mem_upto_iff
- \- *theorem* finset.mem_upto_of_lt
- \- *theorem* finset.mem_upto_succ_of_mem_upto
- \+/\- *theorem* finset.not_mem_empty
- \+ *theorem* finset.not_mem_range_self
- \- *theorem* finset.not_mem_upto
- \+ *def* finset.range
- \+ *theorem* finset.range_subset
- \+ *theorem* finset.range_succ
- \+ *theorem* finset.range_zero
- \- *def* finset.upto
- \- *theorem* finset.upto_subset_upto_iff
- \- *theorem* finset.upto_succ
- \- *theorem* finset.upto_zero
- \- *lemma* lt_max_iff

Modified data/finset/fold.lean
- \- *lemma* heq_iff_eq

Modified data/hash_map.lean
- \+/\- *theorem* bucket_array.mem_as_list
- \+/\- *theorem* hash_map.contains_aux_iff
- \+/\- *theorem* hash_map.find_aux_iff

Modified data/list/basic.lean
- \+ *theorem* list.all_cons
- \+ *theorem* list.all_iff_forall
- \+ *theorem* list.all_iff_forall_prop
- \+ *theorem* list.all_nil
- \+ *theorem* list.any_cons
- \+ *theorem* list.any_iff_exists
- \+ *theorem* list.any_iff_exists_prop
- \+ *theorem* list.any_nil
- \+ *theorem* list.any_of_mem
- \+ *theorem* list.append_inj'
- \+ *theorem* list.append_inj_left'
- \+ *theorem* list.append_inj_right'
- \+ *theorem* list.append_left_cancel
- \+ *theorem* list.append_right_cancel
- \- *theorem* list.append_right_inj
- \+ *theorem* list.append_sublist_append_left
- \+ *theorem* list.append_sublist_append_of_sublist_right
- \+ *theorem* list.append_sublist_append_right
- \+ *theorem* list.chain.iff
- \+ *theorem* list.chain.iff_mem
- \+ *theorem* list.chain.imp
- \+ *theorem* list.chain_cons
- \+ *theorem* list.chain_iff_pairwise
- \+ *theorem* list.chain_lt_range'
- \+ *theorem* list.chain_map
- \+ *theorem* list.chain_map_of_chain
- \+ *theorem* list.chain_of_chain_cons
- \+ *theorem* list.chain_of_chain_map
- \+ *theorem* list.chain_of_pairwise
- \+ *theorem* list.chain_singleton
- \+ *theorem* list.chain_split
- \+ *theorem* list.chain_succ_range'
- \+/\- *def* list.concat
- \+ *theorem* list.concat_eq_append
- \- *lemma* list.concat_eq_append
- \+ *theorem* list.cons_inj'
- \+/\- *theorem* list.cons_inj
- \+ *theorem* list.cons_sublist_cons_iff
- \+ *theorem* list.cons_union
- \+/\- *def* list.count
- \+/\- *theorem* list.count_append
- \+ *theorem* list.count_eq_one_of_mem
- \+ *theorem* list.count_le_of_sublist
- \+ *theorem* list.count_pos
- \+/\- *theorem* list.count_pos_of_mem
- \+ *theorem* list.count_repeat
- \+ *def* list.countp
- \+ *theorem* list.countp_append
- \+ *theorem* list.countp_cons_of_neg
- \+ *theorem* list.countp_cons_of_pos
- \+ *theorem* list.countp_eq_length_filter
- \+ *theorem* list.countp_le_of_sublist
- \+ *theorem* list.countp_nil
- \+ *theorem* list.countp_pos_of_mem
- \+ *theorem* list.disjoint.symm
- \+ *def* list.disjoint
- \+ *theorem* list.disjoint_append_left
- \+ *theorem* list.disjoint_append_of_disjoint_left
- \+ *theorem* list.disjoint_append_right
- \+ *theorem* list.disjoint_comm
- \+ *theorem* list.disjoint_cons_left
- \+ *theorem* list.disjoint_cons_right
- \+ *theorem* list.disjoint_iff_ne
- \+ *theorem* list.disjoint_left
- \+ *theorem* list.disjoint_nil_left
- \+ *theorem* list.disjoint_of_disjoint_append_left_left
- \+ *theorem* list.disjoint_of_disjoint_append_left_right
- \+ *theorem* list.disjoint_of_disjoint_append_right_left
- \+ *theorem* list.disjoint_of_disjoint_append_right_right
- \+ *theorem* list.disjoint_of_disjoint_cons_left
- \+ *theorem* list.disjoint_of_disjoint_cons_right
- \+ *theorem* list.disjoint_of_nodup_append
- \+ *theorem* list.disjoint_of_subset_left
- \+ *theorem* list.disjoint_of_subset_right
- \+ *theorem* list.disjoint_right
- \+ *theorem* list.disjoint_singleton
- \+ *theorem* list.eq_nil_iff_forall_not_mem
- \+ *theorem* list.eq_nil_of_infix_nil
- \- *lemma* list.eq_nil_of_infix_nil
- \+ *theorem* list.eq_nil_of_prefix_nil
- \- *lemma* list.eq_nil_of_prefix_nil
- \+ *theorem* list.eq_nil_of_suffix_nil
- \- *lemma* list.eq_nil_of_suffix_nil
- \+ *theorem* list.eq_of_infix_of_length_eq
- \- *theorem* list.eq_of_map_const
- \+ *theorem* list.eq_of_mem_map_const
- \+ *theorem* list.eq_of_mem_repeat
- \+ *theorem* list.eq_of_mem_singleton
- \+ *theorem* list.eq_of_prefix_of_length_eq
- \+ *theorem* list.eq_of_sublist_of_length_eq
- \+ *theorem* list.eq_of_suffix_of_length_eq
- \+ *theorem* list.eq_or_mem_of_mem_insert
- \+ *theorem* list.eq_repeat'
- \+ *theorem* list.eq_repeat
- \+ *theorem* list.eq_repeat_of_mem
- \+ *theorem* list.erase_append_left
- \+ *theorem* list.erase_append_right
- \+ *theorem* list.erase_cons
- \+ *theorem* list.erase_cons_head
- \+ *theorem* list.erase_cons_tail
- \+ *def* list.erase_dup
- \+ *theorem* list.erase_dup_append
- \+ *theorem* list.erase_dup_cons_of_mem'
- \+ *theorem* list.erase_dup_cons_of_mem
- \+ *theorem* list.erase_dup_cons_of_not_mem'
- \+ *theorem* list.erase_dup_cons_of_not_mem
- \+ *theorem* list.erase_dup_eq_self
- \+ *theorem* list.erase_dup_nil
- \+ *theorem* list.erase_dup_sublist
- \+ *theorem* list.erase_dup_subset
- \+ *theorem* list.erase_nil
- \+ *theorem* list.erase_of_not_mem
- \+ *theorem* list.erase_sublist
- \+ *theorem* list.erase_subset
- \+ *theorem* list.exists_erase_eq
- \+ *theorem* list.exists_mem_cons_iff
- \+ *theorem* list.exists_mem_cons_of
- \+ *theorem* list.exists_mem_cons_of_exists
- \+ *theorem* list.exists_mem_of_countp_pos
- \+ *theorem* list.exists_mem_of_length_pos
- \+ *theorem* list.exists_of_mem_bind
- \- *lemma* list.exists_of_mem_bind
- \+ *theorem* list.filter_eq_nil
- \+ *theorem* list.filter_eq_self
- \+ *theorem* list.filter_filter_map
- \+ *theorem* list.filter_map_cons_none
- \+ *theorem* list.filter_map_cons_some
- \+ *theorem* list.filter_map_eq_filter
- \+ *theorem* list.filter_map_eq_map
- \+ *theorem* list.filter_map_filter
- \+ *theorem* list.filter_map_filter_map
- \+ *theorem* list.filter_map_map
- \+ *theorem* list.filter_map_nil
- \+ *theorem* list.filter_map_some
- \+ *theorem* list.filter_map_sublist_filter_map
- \+ *theorem* list.filter_sublist_filter
- \+/\- *theorem* list.filter_subset
- \+/\- *def* list.find
- \+ *theorem* list.find_cons_of_neg
- \+ *theorem* list.find_cons_of_pos
- \+ *theorem* list.find_eq_none
- \+ *theorem* list.find_mem
- \+ *theorem* list.find_nil
- \+ *theorem* list.find_some
- \+ *theorem* list.foldl1_eq_foldr1
- \+ *theorem* list.foldl_append
- \+ *theorem* list.foldl_cons
- \+ *theorem* list.foldl_eq_foldr
- \+ *theorem* list.foldl_eq_of_comm_of_assoc
- \+ *theorem* list.foldl_nil
- \+ *theorem* list.foldl_reverse
- \+ *theorem* list.foldr_append
- \+ *theorem* list.foldr_cons
- \+ *theorem* list.foldr_eta
- \- *lemma* list.foldr_eta
- \+ *theorem* list.foldr_nil
- \+ *theorem* list.foldr_reverse
- \+ *theorem* list.forall_mem_cons'
- \+ *theorem* list.forall_mem_cons
- \+ *theorem* list.forall_mem_inter_of_forall_left
- \+ *theorem* list.forall_mem_inter_of_forall_right
- \+ *theorem* list.forall_mem_ne
- \+ *theorem* list.forall_mem_nil
- \+ *theorem* list.forall_mem_of_forall_mem_cons
- \+ *theorem* list.forall_mem_of_forall_mem_union_left
- \+ *theorem* list.forall_mem_of_forall_mem_union_right
- \+ *theorem* list.forall_mem_pw_filter
- \+ *theorem* list.forall_mem_union
- \+/\- *theorem* list.head_eq_of_cons_eq
- \+ *theorem* list.infix_append
- \- *lemma* list.infix_append
- \+ *theorem* list.infix_iff_prefix_suffix
- \- *lemma* list.infix_iff_prefix_suffix
- \+ *theorem* list.infix_of_prefix
- \- *lemma* list.infix_of_prefix
- \+ *theorem* list.infix_of_suffix
- \- *lemma* list.infix_of_suffix
- \+ *theorem* list.infix_refl
- \- *lemma* list.infix_refl
- \+/\- *def* list.inits
- \+ *theorem* list.insert.def
- \+ *theorem* list.insert_nil
- \+ *theorem* list.insert_of_mem
- \+ *theorem* list.insert_of_not_mem
- \+ *theorem* list.inter_cons_of_mem
- \+ *theorem* list.inter_cons_of_not_mem
- \+ *theorem* list.inter_eq_nil_iff_disjoint
- \+ *theorem* list.inter_nil
- \+ *theorem* list.inter_subset_left
- \+ *theorem* list.inter_subset_right
- \+/\- *def* list.inth
- \+ *theorem* list.iota_eq_reverse_range'
- \+ *theorem* list.is_infix.trans
- \+ *theorem* list.is_prefix.trans
- \+ *theorem* list.is_suffix.trans
- \+ *theorem* list.le_count_iff_repeat_sublist
- \+ *theorem* list.length_concat
- \- *lemma* list.length_concat
- \+ *theorem* list.length_erase_of_mem
- \+ *theorem* list.length_insert_of_mem
- \+ *theorem* list.length_insert_of_not_mem
- \+ *theorem* list.length_iota
- \+ *theorem* list.length_le_of_infix
- \- *lemma* list.length_le_of_infix
- \+ *theorem* list.length_product
- \+ *theorem* list.length_range'
- \+ *theorem* list.length_range
- \+ *theorem* list.map_concat
- \- *lemma* list.map_concat
- \+ *theorem* list.map_const
- \+ *theorem* list.map_filter_map
- \+ *theorem* list.map_filter_map_of_inv
- \+ *theorem* list.map₂_nil
- \+ *theorem* list.mem_bind
- \- *lemma* list.mem_bind
- \- *lemma* list.mem_bind_iff
- \+ *theorem* list.mem_bind_of_mem
- \+ *theorem* list.mem_erase_dup
- \+ *theorem* list.mem_erase_iff_of_nodup
- \+ *theorem* list.mem_erase_of_ne_of_mem
- \+ *theorem* list.mem_erase_of_nodup
- \+ *theorem* list.mem_filter
- \- *theorem* list.mem_filter_iff
- \+ *theorem* list.mem_filter_map
- \+/\- *theorem* list.mem_filter_of_mem
- \- *theorem* list.mem_iff_count_pos
- \+ *theorem* list.mem_inits
- \- *lemma* list.mem_inits
- \+ *theorem* list.mem_insert_iff
- \+ *theorem* list.mem_insert_of_mem
- \+ *theorem* list.mem_insert_self
- \+ *theorem* list.mem_inter
- \+ *theorem* list.mem_inter_of_mem_of_mem
- \+ *theorem* list.mem_iota
- \+/\- *theorem* list.mem_join
- \- *theorem* list.mem_join_iff
- \+ *theorem* list.mem_join_of_mem
- \+/\- *theorem* list.mem_map
- \- *theorem* list.mem_map_iff
- \+ *theorem* list.mem_map_of_inj
- \+ *theorem* list.mem_map_of_mem
- \+/\- *theorem* list.mem_of_count_pos
- \+ *theorem* list.mem_of_mem_erase
- \+/\- *theorem* list.mem_of_mem_filter
- \+ *theorem* list.mem_of_mem_inter_left
- \+ *theorem* list.mem_of_mem_inter_right
- \+ *theorem* list.mem_product
- \+ *theorem* list.mem_range'
- \+ *theorem* list.mem_range
- \+/\- *theorem* list.mem_reverse
- \+/\- *theorem* list.mem_singleton
- \- *theorem* list.mem_singleton_iff
- \+ *theorem* list.mem_singleton_self
- \+/\- *theorem* list.mem_split
- \+ *theorem* list.mem_sublists
- \- *lemma* list.mem_sublists
- \+ *theorem* list.mem_tails
- \- *lemma* list.mem_tails
- \+ *theorem* list.mem_union
- \+ *theorem* list.mem_union_left
- \+ *theorem* list.mem_union_right
- \+ *theorem* list.nil_map₂
- \+ *theorem* list.nil_product
- \+ *theorem* list.nil_union
- \+ *def* list.nodup
- \+ *theorem* list.nodup_app_comm
- \+ *theorem* list.nodup_append
- \+ *theorem* list.nodup_append_of_nodup
- \+ *theorem* list.nodup_bind
- \+ *theorem* list.nodup_concat
- \+ *theorem* list.nodup_cons
- \+ *theorem* list.nodup_cons_of_nodup
- \+ *theorem* list.nodup_erase_dup
- \+ *theorem* list.nodup_erase_eq_filter
- \+ *theorem* list.nodup_erase_of_nodup
- \+ *theorem* list.nodup_filter
- \+ *theorem* list.nodup_filter_map
- \+ *theorem* list.nodup_iff_count_le_one
- \+ *theorem* list.nodup_iff_sublist
- \+ *theorem* list.nodup_insert
- \+ *theorem* list.nodup_inter_of_nodup
- \+ *theorem* list.nodup_iota
- \+ *theorem* list.nodup_join
- \+ *theorem* list.nodup_map
- \+ *theorem* list.nodup_map_on
- \+ *theorem* list.nodup_middle
- \+ *theorem* list.nodup_nil
- \+ *theorem* list.nodup_of_nodup_append_left
- \+ *theorem* list.nodup_of_nodup_append_right
- \+ *theorem* list.nodup_of_nodup_cons
- \+ *theorem* list.nodup_of_nodup_map
- \+ *theorem* list.nodup_of_sublist
- \+ *theorem* list.nodup_product
- \+ *theorem* list.nodup_range'
- \+ *theorem* list.nodup_range
- \+ *theorem* list.nodup_reverse
- \+ *theorem* list.nodup_singleton
- \+ *theorem* list.nodup_union
- \+ *theorem* list.not_exists_mem_nil
- \+/\- *theorem* list.not_mem_append
- \+ *theorem* list.not_mem_of_nodup_cons
- \+ *theorem* list.not_mem_range_self
- \+ *theorem* list.not_nodup_cons_of_mem
- \+ *theorem* list.not_nodup_pair
- \+/\- *theorem* list.of_mem_filter
- \+ *theorem* list.or_exists_of_exists_mem_cons
- \+ *theorem* list.pairwise.iff
- \+ *theorem* list.pairwise.iff_mem
- \+ *theorem* list.pairwise.imp
- \+ *theorem* list.pairwise_app_comm
- \+ *theorem* list.pairwise_append
- \+ *theorem* list.pairwise_cons
- \+ *theorem* list.pairwise_filter
- \+ *theorem* list.pairwise_filter_map
- \+ *theorem* list.pairwise_filter_map_of_pairwise
- \+ *theorem* list.pairwise_filter_of_pairwise
- \+ *theorem* list.pairwise_gt_iota
- \+ *theorem* list.pairwise_join
- \+ *theorem* list.pairwise_lt_range'
- \+ *theorem* list.pairwise_lt_range
- \+ *theorem* list.pairwise_map
- \+ *theorem* list.pairwise_map_of_pairwise
- \+ *theorem* list.pairwise_middle
- \+ *theorem* list.pairwise_of_forall
- \+ *theorem* list.pairwise_of_pairwise_cons
- \+ *theorem* list.pairwise_of_pairwise_map
- \+ *theorem* list.pairwise_of_sublist
- \+ *theorem* list.pairwise_pair
- \+ *theorem* list.pairwise_pw_filter
- \+ *theorem* list.pairwise_reverse
- \+ *theorem* list.pairwise_singleton
- \+ *theorem* list.prefix_append
- \- *lemma* list.prefix_append
- \+ *theorem* list.prefix_concat
- \+ *theorem* list.prefix_refl
- \- *lemma* list.prefix_refl
- \+ *def* list.prod
- \+ *def* list.product
- \+ *theorem* list.product_cons
- \+ *theorem* list.product_nil
- \+ *def* list.pw_filter
- \+ *theorem* list.pw_filter_cons_of_neg
- \+ *theorem* list.pw_filter_cons_of_pos
- \+ *theorem* list.pw_filter_eq_self
- \+ *theorem* list.pw_filter_nil
- \+ *theorem* list.pw_filter_sublist
- \+ *theorem* list.pw_filter_subset
- \+ *def* list.range'
- \+ *theorem* list.range'_append
- \+ *theorem* list.range'_concat
- \+ *theorem* list.range'_sublist_right
- \+ *theorem* list.range'_subset_right
- \+ *theorem* list.range_core_range'
- \+ *theorem* list.range_eq_range'
- \+ *theorem* list.range_sublist
- \+ *theorem* list.range_subset
- \+ *theorem* list.rel_of_chain_cons
- \+ *theorem* list.rel_of_pairwise_cons
- \+ *theorem* list.repeat_sublist_repeat
- \+ *theorem* list.repeat_subset_singleton
- \+ *theorem* list.reverse_cons'
- \+ *theorem* list.reverse_sublist
- \+ *theorem* list.reverse_sublist_iff
- \+ *theorem* list.scanr_aux_cons
- \- *lemma* list.scanr_aux_cons
- \+ *theorem* list.scanr_cons
- \- *lemma* list.scanr_cons
- \+ *theorem* list.scanr_nil
- \- *lemma* list.scanr_nil
- \+ *theorem* list.singleton_disjoint
- \+ *theorem* list.singleton_sublist
- \+ *theorem* list.span_eq_take_drop
- \- *lemma* list.span_eq_take_drop
- \+ *theorem* list.sublist_antisymm
- \+/\- *theorem* list.sublist_app_of_sublist_left
- \+/\- *theorem* list.sublist_app_of_sublist_right
- \+ *theorem* list.sublist_of_infix
- \- *lemma* list.sublist_of_infix
- \+ *theorem* list.sublist_of_prefix
- \+ *theorem* list.sublist_of_suffix
- \+ *theorem* list.sublist_suffix_of_union
- \+ *theorem* list.sublists_aux_cons_cons
- \- *lemma* list.sublists_aux_cons_cons
- \+ *theorem* list.sublists_aux_eq_foldl
- \- *lemma* list.sublists_aux_eq_foldl
- \+ *theorem* list.subset_erase_dup
- \+ *theorem* list.subset_inter
- \+ *theorem* list.suffix_append
- \- *lemma* list.suffix_append
- \+ *theorem* list.suffix_cons
- \+ *theorem* list.suffix_insert
- \+ *theorem* list.suffix_refl
- \- *lemma* list.suffix_refl
- \+ *theorem* list.suffix_union_right
- \+/\- *def* list.sum
- \+/\- *theorem* list.tail_eq_of_cons_eq
- \+/\- *def* list.tails
- \+ *theorem* list.take_while_append_drop
- \- *lemma* list.take_while_append_drop
- \+ *theorem* list.union_sublist_append
- \+ *theorem* list.unzip_cons
- \+ *theorem* list.unzip_nil
- \+ *theorem* list.zip_cons_cons
- \+ *theorem* list.zip_nil_left
- \+ *theorem* list.zip_nil_right
- \+ *theorem* list.zip_unzip

Deleted data/list/comb.lean
- \- *theorem* list.all_cons
- \- *theorem* list.all_eq_tt_iff
- \- *theorem* list.all_eq_tt_of_forall
- \- *theorem* list.all_nil
- \- *theorem* list.any_cons
- \- *theorem* list.any_eq_tt_iff
- \- *theorem* list.any_nil
- \- *theorem* list.any_of_mem
- \- *def* list.dinj
- \- *def* list.dinj₁
- \- *def* list.dmap
- \- *theorem* list.dmap_cons_of_neg
- \- *theorem* list.dmap_cons_of_pos
- \- *theorem* list.dmap_nil
- \- *theorem* list.eq_of_mem_map_pair₁
- \- *theorem* list.exists_mem_cons_iff
- \- *theorem* list.exists_mem_cons_of
- \- *theorem* list.exists_mem_cons_of_exists
- \- *theorem* list.exists_of_any_eq_tt
- \- *theorem* list.exists_of_mem_dmap
- \- *def* list.flat
- \- *theorem* list.foldl_append
- \- *theorem* list.foldl_cons
- \- *theorem* list.foldl_eq_foldr
- \- *theorem* list.foldl_eq_of_comm_of_assoc
- \- *theorem* list.foldl_nil
- \- *theorem* list.foldl_reverse
- \- *theorem* list.foldr_append
- \- *theorem* list.foldr_cons
- \- *theorem* list.foldr_nil
- \- *theorem* list.foldr_reverse
- \- *theorem* list.forall_mem_cons
- \- *theorem* list.forall_mem_cons_iff
- \- *theorem* list.forall_mem_eq_tt_of_all_eq_tt
- \- *theorem* list.forall_mem_nil
- \- *theorem* list.forall_mem_of_forall_mem_cons
- \- *theorem* list.length_mapAccumR
- \- *theorem* list.length_mapAccumR₂
- \- *theorem* list.length_product
- \- *theorem* list.length_replicate
- \- *def* list.mapAccumR
- \- *def* list.mapAccumR₂
- \- *theorem* list.map_dmap_of_inv_of_pos
- \- *theorem* list.map₂_nil1
- \- *theorem* list.map₂_nil2
- \- *theorem* list.mem_dmap
- \- *theorem* list.mem_of_dinj_of_mem_dmap
- \- *theorem* list.mem_of_mem_map_pair₁
- \- *theorem* list.mem_of_mem_product_left
- \- *theorem* list.mem_of_mem_product_right
- \- *theorem* list.mem_product
- \- *theorem* list.nil_product
- \- *theorem* list.not_exists_mem_nil
- \- *theorem* list.not_mem_dmap_of_dinj_of_not_mem
- \- *theorem* list.of_forall_mem_cons
- \- *theorem* list.or_exists_of_exists_mem_cons
- \- *def* list.product
- \- *theorem* list.product_cons
- \- *theorem* list.product_nil
- \- *def* list.replicate
- \- *theorem* list.unzip_cons'
- \- *theorem* list.unzip_cons
- \- *theorem* list.unzip_nil
- \- *theorem* list.zip_cons_cons
- \- *theorem* list.zip_nil_left
- \- *theorem* list.zip_nil_right
- \- *theorem* list.zip_unzip

Modified data/list/default.lean


Modified data/list/perm.lean
- \+ *theorem* list.concat_perm
- \+ *theorem* list.cons_perm_iff_perm_erase
- \+ *theorem* list.eq_nil_of_perm_nil
- \+ *theorem* list.eq_singleton_of_perm
- \+ *theorem* list.eq_singleton_of_perm_inv
- \+ *theorem* list.erase_perm_erase
- \+ *theorem* list.exists_perm_sublist
- \+ *theorem* list.exists_sublist_perm_of_subset_nodup
- \+ *theorem* list.foldl_eq_of_perm
- \+ *theorem* list.foldr_eq_of_perm
- \+ *theorem* list.mem_iff_mem_of_perm
- \+ *theorem* list.mem_of_perm
- \+ *theorem* list.not_perm_nil_cons
- \- *theorem* list.perm.count_eq_count_of_perm
- \- *def* list.perm.decidable_perm
- \- *def* list.perm.decidable_perm_aux
- \- *theorem* list.perm.eq_nil_of_perm_nil
- \- *theorem* list.perm.eq_singleton_of_perm
- \- *theorem* list.perm.eq_singleton_of_perm_inv
- \+/\- *theorem* list.perm.eqv
- \- *theorem* list.perm.erase_perm_erase_of_perm
- \- *theorem* list.perm.foldl_eq_of_perm
- \- *theorem* list.perm.foldr_eq_of_perm
- \- *theorem* list.perm.length_eq_length_of_perm
- \- *theorem* list.perm.length_eq_of_qeq
- \- *theorem* list.perm.mem_cons_of_qeq
- \- *theorem* list.perm.mem_head_of_qeq
- \- *theorem* list.perm.mem_iff_mem_of_perm
- \- *theorem* list.perm.mem_of_perm
- \- *theorem* list.perm.mem_tail_of_qeq
- \- *theorem* list.perm.nodup_of_perm_of_nodup
- \- *theorem* list.perm.not_mem_of_perm
- \- *theorem* list.perm.not_perm_nil_cons
- \- *theorem* list.perm.perm_app
- \- *theorem* list.perm.perm_app_comm
- \- *theorem* list.perm.perm_app_cons
- \- *theorem* list.perm.perm_app_inv
- \- *theorem* list.perm.perm_app_inv_left
- \- *theorem* list.perm.perm_app_inv_right
- \- *theorem* list.perm.perm_app_left
- \- *theorem* list.perm.perm_app_right
- \- *theorem* list.perm.perm_cons_app
- \- *theorem* list.perm.perm_cons_app_cons
- \- *theorem* list.perm.perm_cons_app_simp
- \- *theorem* list.perm.perm_cons_inv
- \- *theorem* list.perm.perm_erase
- \- *theorem* list.perm.perm_erase_dup_of_perm
- \- *theorem* list.perm.perm_ext
- \- *theorem* list.perm.perm_filter
- \- *theorem* list.perm.perm_iff_forall_count_eq_count
- \- *theorem* list.perm.perm_iff_forall_mem_count_eq_count
- \- *theorem* list.perm.perm_induction_on
- \- *theorem* list.perm.perm_insert
- \- *theorem* list.perm.perm_insert_insert
- \- *theorem* list.perm.perm_inter
- \- *theorem* list.perm.perm_inter_left
- \- *theorem* list.perm.perm_inter_right
- \- *theorem* list.perm.perm_inv_core
- \- *theorem* list.perm.perm_map
- \- *theorem* list.perm.perm_middle
- \- *theorem* list.perm.perm_middle_simp
- \- *theorem* list.perm.perm_of_forall_count_eq
- \- *theorem* list.perm.perm_of_qeq
- \- *theorem* list.perm.perm_product
- \- *theorem* list.perm.perm_product_left
- \- *theorem* list.perm.perm_product_right
- \- *theorem* list.perm.perm_rev
- \- *theorem* list.perm.perm_rev_simp
- \- *theorem* list.perm.perm_union
- \- *theorem* list.perm.perm_union_left
- \- *theorem* list.perm.perm_union_right
- \- *theorem* list.perm.qeq_app
- \- *theorem* list.perm.qeq_of_mem
- \- *theorem* list.perm.qeq_split
- \- *theorem* list.perm.subset_of_mem_of_subset_of_qeq
- \- *theorem* list.perm.xswap
- \+ *theorem* list.perm_app
- \+ *theorem* list.perm_app_comm
- \+ *theorem* list.perm_app_cons
- \+ *theorem* list.perm_app_inv_right
- \+ *theorem* list.perm_app_left
- \+ *theorem* list.perm_app_left_iff
- \+ *theorem* list.perm_app_right
- \+ *theorem* list.perm_bind_left
- \+ *theorem* list.perm_bind_right
- \+ *theorem* list.perm_cons
- \+ *theorem* list.perm_cons_app
- \+ *theorem* list.perm_cons_app_cons
- \+ *theorem* list.perm_cons_inv
- \+ *theorem* list.perm_count
- \+ *theorem* list.perm_countp
- \+ *theorem* list.perm_erase
- \+ *theorem* list.perm_erase_dup_of_perm
- \+ *theorem* list.perm_ext
- \+ *theorem* list.perm_filter
- \+ *theorem* list.perm_filter_map
- \+ *theorem* list.perm_iff_count
- \+ *theorem* list.perm_induction_on
- \+ *theorem* list.perm_insert
- \+ *theorem* list.perm_insert_swap
- \+ *theorem* list.perm_inter
- \+ *theorem* list.perm_inter_left
- \+ *theorem* list.perm_inter_right
- \+ *theorem* list.perm_inv_core
- \+ *theorem* list.perm_length
- \+ *theorem* list.perm_map
- \+ *theorem* list.perm_middle
- \+ *theorem* list.perm_nodup
- \+ *theorem* list.perm_pairwise
- \+ *theorem* list.perm_product
- \+ *theorem* list.perm_product_left
- \+ *theorem* list.perm_product_right
- \+ *theorem* list.perm_repeat
- \+ *theorem* list.perm_union
- \+ *theorem* list.perm_union_left
- \+ *theorem* list.perm_union_right
- \+ *theorem* list.reverse_perm
- \+ *theorem* list.xswap

Deleted data/list/set.lean
- \- *theorem* list.cons_union
- \- *theorem* list.disjoint.symm
- \- *def* list.disjoint
- \- *theorem* list.disjoint_append_of_disjoint_left
- \- *theorem* list.disjoint_comm
- \- *theorem* list.disjoint_cons_of_not_mem_of_disjoint
- \- *theorem* list.disjoint_left
- \- *theorem* list.disjoint_nil_left
- \- *theorem* list.disjoint_of_disjoint_append_left_left
- \- *theorem* list.disjoint_of_disjoint_append_left_right
- \- *theorem* list.disjoint_of_disjoint_append_right_left
- \- *theorem* list.disjoint_of_disjoint_append_right_right
- \- *theorem* list.disjoint_of_disjoint_cons_left
- \- *theorem* list.disjoint_of_disjoint_cons_right
- \- *theorem* list.disjoint_of_nodup_append
- \- *theorem* list.disjoint_of_subset_left
- \- *theorem* list.disjoint_of_subset_right
- \- *theorem* list.disjoint_right
- \- *theorem* list.disjoint_singleton
- \- *theorem* list.dmap_nodup_of_dinj
- \- *theorem* list.eq_or_mem_of_mem_insert
- \- *theorem* list.erase_append_left
- \- *theorem* list.erase_append_right
- \- *theorem* list.erase_cons_head
- \- *theorem* list.erase_cons_tail
- \- *def* list.erase_dup
- \- *theorem* list.erase_dup_cons_of_mem
- \- *theorem* list.erase_dup_cons_of_not_mem
- \- *theorem* list.erase_dup_eq_of_nodup
- \- *theorem* list.erase_dup_nil
- \- *theorem* list.erase_dup_sublist
- \- *theorem* list.erase_dup_subset
- \- *theorem* list.erase_nil
- \- *theorem* list.erase_of_not_mem
- \- *theorem* list.erase_sublist
- \- *theorem* list.erase_subset
- \- *theorem* list.forall_mem_insert_of_forall_mem
- \- *theorem* list.forall_mem_inter_of_forall_left
- \- *theorem* list.forall_mem_inter_of_forall_right
- \- *theorem* list.forall_mem_of_forall_mem_union_left
- \- *theorem* list.forall_mem_of_forall_mem_union_right
- \- *theorem* list.forall_mem_union
- \- *theorem* list.insert.def
- \- *theorem* list.insert_nil
- \- *theorem* list.insert_of_mem
- \- *theorem* list.insert_of_not_mem
- \- *theorem* list.inter_cons_of_mem
- \- *theorem* list.inter_cons_of_not_mem
- \- *theorem* list.inter_eq_nil_of_disjoint
- \- *theorem* list.inter_nil
- \- *theorem* list.length_erase_of_mem
- \- *theorem* list.length_erase_of_not_mem
- \- *theorem* list.length_insert_of_mem
- \- *theorem* list.length_insert_of_not_mem
- \- *theorem* list.length_upto
- \- *theorem* list.lt_of_mem_upto
- \- *theorem* list.mem_erase_dup
- \- *theorem* list.mem_erase_iff_of_nodup
- \- *theorem* list.mem_erase_of_ne_of_mem
- \- *theorem* list.mem_erase_of_nodup
- \- *theorem* list.mem_insert_iff
- \- *theorem* list.mem_insert_of_mem
- \- *theorem* list.mem_insert_self
- \- *theorem* list.mem_inter_iff
- \- *theorem* list.mem_inter_of_mem_of_mem
- \- *theorem* list.mem_of_mem_erase
- \- *theorem* list.mem_of_mem_inter_left
- \- *theorem* list.mem_of_mem_inter_right
- \- *theorem* list.mem_or_mem_of_mem_union
- \- *theorem* list.mem_union_iff
- \- *theorem* list.mem_union_left
- \- *theorem* list.mem_union_right
- \- *theorem* list.mem_upto_of_lt
- \- *theorem* list.mem_upto_succ_of_mem_upto
- \- *theorem* list.nil_union
- \- *theorem* list.nodup_app_comm
- \- *theorem* list.nodup_append
- \- *theorem* list.nodup_concat
- \- *theorem* list.nodup_cons
- \- *theorem* list.nodup_erase_dup
- \- *theorem* list.nodup_erase_of_nodup
- \- *theorem* list.nodup_filter
- \- *theorem* list.nodup_head
- \- *theorem* list.nodup_insert
- \- *theorem* list.nodup_inter_of_nodup
- \- *theorem* list.nodup_map
- \- *theorem* list.nodup_map_on
- \- *theorem* list.nodup_middle
- \- *theorem* list.nodup_nil
- \- *theorem* list.nodup_of_nodup_append_left
- \- *theorem* list.nodup_of_nodup_append_right
- \- *theorem* list.nodup_of_nodup_cons
- \- *theorem* list.nodup_of_nodup_map
- \- *theorem* list.nodup_of_sublist
- \- *theorem* list.nodup_product
- \- *theorem* list.nodup_singleton
- \- *theorem* list.nodup_union
- \- *theorem* list.nodup_upto
- \- *theorem* list.not_mem_of_nodup_cons
- \- *theorem* list.not_nodup_cons_of_mem
- \- *theorem* list.not_nodup_cons_of_not_nodup
- \- *theorem* list.singleton_disjoint
- \- *theorem* list.subset_erase_dup
- \- *def* list.upto
- \- *theorem* list.upto_ne_nil_of_ne_zero
- \- *theorem* list.upto_nil
- \- *theorem* list.upto_step
- \- *theorem* list.upto_succ

Modified data/list/sort.lean
- \+ *theorem* list.eq_of_sorted_of_perm
- \- *lemma* list.eq_of_sorted_of_perm
- \- *theorem* list.forall_mem_rel_of_sorted_cons
- \+/\- *def* list.insertion_sort
- \+/\- *def* list.ordered_insert
- \+ *theorem* list.rel_of_sorted_cons
- \+/\- *def* list.sorted
- \+/\- *theorem* list.sorted_cons
- \+/\- *theorem* list.sorted_nil
- \+/\- *theorem* list.sorted_of_sorted_cons
- \+/\- *theorem* list.sorted_singleton

Modified data/nat/pairing.lean
- \+ *theorem* nat.mkpair_unpair'

Modified data/option.lean
- \+/\- *def* option.filter
- \+ *def* option.guard
- \+ *lemma* option.guard_eq_some
- \+/\- *def* option.iget
- \+ *lemma* option.mem_def
- \+ *lemma* option.some_inj

Modified data/prod.lean
- \+ *lemma* prod.swap_left_inverse
- \+ *lemma* prod.swap_right_inverse

Modified data/rat.lean


Modified data/seq/wseq.lean


Modified data/set/basic.lean
- \+/\- *theorem* set.ball_image_iff
- \+ *theorem* set.compl_image
- \+/\- *lemma* set.forall_range_iff
- \+/\- *theorem* set.image_eq_preimage_of_inverse
- \+ *theorem* set.image_preimage_eq
- \- *lemma* set.image_subset_eq
- \+ *theorem* set.image_subset_preimage_of_inverse
- \- *theorem* set.image_union_supset
- \- *theorem* set.inter_preimage_subset
- \+/\- *theorem* set.mem_image
- \+ *theorem* set.mem_image_iff_bex
- \+ *theorem* set.mem_image_iff_of_inverse
- \- *lemma* set.mem_image_iff_of_inverse
- \+ *theorem* set.mem_of_eq_of_mem
- \- *lemma* set.mem_of_eq_of_mem
- \+/\- *def* set.pairwise_on
- \- *theorem* set.preimage_diff
- \+/\- *theorem* set.preimage_image_eq
- \+ *theorem* set.preimage_subset_image_of_inverse
- \+/\- *lemma* set.range_of_surjective
- \+/\- *theorem* set.subset.trans
- \+/\- *theorem* set.subset_preimage_image
- \- *theorem* set.union_preimage_subset

Modified data/set/countable.lean
- \+/\- *def* set.countable
- \- *def* set.encodable_of_inj

Modified data/set/enumerate.lean


Deleted data/set/function.lean
- \- *lemma* set.bij_on.mk
- \- *def* set.bij_on
- \- *theorem* set.bij_on_comp
- \- *theorem* set.bij_on_of_eq_on
- \- *theorem* set.bij_on_of_inv_on
- \- *lemma* set.bijective_iff_bij_on_univ
- \- *theorem* set.eq_on_of_left_inv_of_right_inv
- \- *lemma* set.image_eq_of_bij_on
- \- *lemma* set.image_eq_of_maps_to_of_surj_on
- \- *theorem* set.image_subset_of_maps_to
- \- *theorem* set.image_subset_of_maps_to_of_subset
- \- *def* set.inj_on
- \- *theorem* set.inj_on_comp
- \- *theorem* set.inj_on_empty
- \- *lemma* set.inj_on_of_bij_on
- \- *theorem* set.inj_on_of_eq_on
- \- *theorem* set.inj_on_of_inj_on_of_subset
- \- *theorem* set.inj_on_of_left_inv_on
- \- *lemma* set.injective_iff_inj_on_univ
- \- *def* set.inv_on
- \- *def* set.left_inv_on
- \- *theorem* set.left_inv_on_comp
- \- *theorem* set.left_inv_on_of_eq_on_left
- \- *theorem* set.left_inv_on_of_eq_on_right
- \- *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \- *def* set.maps_to
- \- *theorem* set.maps_to_comp
- \- *lemma* set.maps_to_of_bij_on
- \- *theorem* set.maps_to_of_eq_on
- \- *theorem* set.maps_to_univ_univ
- \- *def* set.right_inv_on
- \- *theorem* set.right_inv_on_comp
- \- *theorem* set.right_inv_on_of_eq_on_left
- \- *theorem* set.right_inv_on_of_eq_on_right
- \- *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \- *def* set.surj_on
- \- *theorem* set.surj_on_comp
- \- *lemma* set.surj_on_of_bij_on
- \- *theorem* set.surj_on_of_eq_on
- \- *theorem* set.surj_on_of_right_inv_on
- \- *lemma* set.surjective_iff_surj_on_univ

Modified data/set/prod.lean
- \+ *lemma* set.mem_prod
- \+/\- *lemma* set.mem_prod_eq

Modified logic/basic.lean
- \+ *lemma* and_iff_left_of_imp
- \+ *lemma* and_iff_right_of_imp
- \+ *theorem* exists_and_distrib_right
- \+ *lemma* heq_iff_eq
- \+ *theorem* sigma.exists
- \+ *theorem* sigma.forall
- \+ *theorem* sigma.mk.inj_iff
- \+ *theorem* subtype.exists
- \+ *theorem* subtype.forall

Renamed logic/function_inverse.lean to logic/function.lean
- \+ *theorem* function.injective.eq_iff
- \+ *lemma* function.injective.has_left_inverse
- \+ *lemma* function.injective_surj_inv
- \+ *theorem* function.inv_fun_eq
- \+ *theorem* function.inv_fun_eq_of_injective_of_right_inverse
- \+ *theorem* function.inv_fun_on_eq'
- \+ *theorem* function.inv_fun_on_eq
- \+ *theorem* function.inv_fun_on_mem
- \+ *theorem* function.inv_fun_on_neg
- \+ *theorem* function.inv_fun_on_pos
- \+ *lemma* function.left_inverse_inv_fun
- \+ *theorem* function.partial_inv_eq
- \+ *theorem* function.partial_inv_eq_of_eq
- \+ *lemma* function.right_inverse_inv_fun
- \+ *lemma* function.right_inverse_surj_inv
- \+ *lemma* function.surj_inv_eq
- \+ *lemma* function.surjective.has_right_inverse
- \- *lemma* set.has_left_inverse
- \- *lemma* set.has_right_inverse
- \- *lemma* set.injective_surj_inv
- \- *def* set.inv_fun
- \- *theorem* set.inv_fun_eq
- \- *theorem* set.inv_fun_eq_of_injective_of_right_inverse
- \- *def* set.inv_fun_on
- \- *theorem* set.inv_fun_on_eq'
- \- *theorem* set.inv_fun_on_eq
- \- *theorem* set.inv_fun_on_mem
- \- *theorem* set.inv_fun_on_neg
- \- *theorem* set.inv_fun_on_pos
- \- *lemma* set.left_inverse_inv_fun
- \- *lemma* set.right_inverse_inv_fun
- \- *lemma* set.right_inverse_surj_inv
- \- *def* set.surj_inv
- \- *lemma* set.surj_inv_eq

Modified order/filter.lean


Modified tactic/interactive.lean


Modified tactic/rcases.lean




## [2017-10-02 00:06:27-05:00](https://github.com/leanprover-community/mathlib/commit/e951a75)
Merge branch 'master' into master
#### Estimated changes
Modified data/set/basic.lean
- \+ *theorem* set.image_preimage_subset
- \+ *lemma* set.image_subset_eq
- \+ *theorem* set.image_union_supset
- \+ *theorem* set.inter_preimage_subset
- \+ *theorem* set.preimage_diff
- \+ *theorem* set.subset_preimage_image
- \+ *theorem* set.union_preimage_subset

Added data/set/function.lean
- \+ *lemma* set.bij_on.mk
- \+ *def* set.bij_on
- \+ *theorem* set.bij_on_comp
- \+ *theorem* set.bij_on_of_eq_on
- \+ *theorem* set.bij_on_of_inv_on
- \+ *lemma* set.bijective_iff_bij_on_univ
- \+ *theorem* set.eq_on_of_left_inv_of_right_inv
- \+ *lemma* set.image_eq_of_bij_on
- \+ *lemma* set.image_eq_of_maps_to_of_surj_on
- \+ *theorem* set.image_subset_of_maps_to
- \+ *theorem* set.image_subset_of_maps_to_of_subset
- \+ *def* set.inj_on
- \+ *theorem* set.inj_on_comp
- \+ *theorem* set.inj_on_empty
- \+ *lemma* set.inj_on_of_bij_on
- \+ *theorem* set.inj_on_of_eq_on
- \+ *theorem* set.inj_on_of_inj_on_of_subset
- \+ *theorem* set.inj_on_of_left_inv_on
- \+ *lemma* set.injective_iff_inj_on_univ
- \+ *def* set.inv_on
- \+ *def* set.left_inv_on
- \+ *theorem* set.left_inv_on_comp
- \+ *theorem* set.left_inv_on_of_eq_on_left
- \+ *theorem* set.left_inv_on_of_eq_on_right
- \+ *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \+ *def* set.maps_to
- \+ *theorem* set.maps_to_comp
- \+ *lemma* set.maps_to_of_bij_on
- \+ *theorem* set.maps_to_of_eq_on
- \+ *theorem* set.maps_to_univ_univ
- \+ *def* set.right_inv_on
- \+ *theorem* set.right_inv_on_comp
- \+ *theorem* set.right_inv_on_of_eq_on_left
- \+ *theorem* set.right_inv_on_of_eq_on_right
- \+ *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \+ *def* set.surj_on
- \+ *theorem* set.surj_on_comp
- \+ *lemma* set.surj_on_of_bij_on
- \+ *theorem* set.surj_on_of_eq_on
- \+ *theorem* set.surj_on_of_right_inv_on
- \+ *lemma* set.surjective_iff_surj_on_univ

