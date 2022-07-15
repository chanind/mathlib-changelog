## [2017-08-30 20:12:20-04:00](https://github.com/leanprover-community/mathlib/commit/dbc8f86)
feat(topology/measurable_space): measurability is closed under id and comp
#### Estimated changes
Modified topology/measurable_space.lean
- \+/\- *def* measurable
- \+ *lemma* measurable_comp
- \+ *lemma* measurable_id



## [2017-08-30 18:33:58-04:00](https://github.com/leanprover-community/mathlib/commit/4ef0ea8)
feat(topology/ennreal): add subtraction
#### Estimated changes
Modified order/complete_lattice.lean


Modified topology/ennreal.lean
- \+ *lemma* Sup_eq_top
- \+ *lemma* ennreal.Inf_add
- \+ *lemma* ennreal.Sup_add
- \+ *lemma* ennreal.add_sub_cancel_of_le
- \+ *lemma* ennreal.le_add_left
- \+ *lemma* ennreal.le_add_right
- \+ *lemma* ennreal.le_sub_iff_add_le
- \+ *lemma* ennreal.lt_iff_exists_of_real
- \+ *lemma* ennreal.lt_of_add_lt_add_left
- \+ *lemma* ennreal.not_infty_lt
- \+ *lemma* ennreal.of_real_lt_infty
- \+/\- *lemma* ennreal.of_real_lt_of_real_iff
- \+ *lemma* ennreal.sub_add_cancel_of_le
- \+ *lemma* ennreal.sub_add_self_eq_max
- \+ *lemma* ennreal.sub_eq_zero_of_le
- \+ *lemma* ennreal.sub_infty
- \+ *lemma* ennreal.sub_le_sub
- \+ *lemma* ennreal.sub_zero
- \+ *lemma* ennreal.zero_sub
- \+ *lemma* lt_Sup_iff



## [2017-08-30 11:17:07-05:00](https://github.com/leanprover-community/mathlib/commit/f93f7e7)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-08-29 23:40:45-04:00](https://github.com/leanprover-community/mathlib/commit/cb7fb9b)
feat(topology): basic setup for measurable spaces
#### Estimated changes
Added topology/measurable_space.lean
- \+ *def* is_measurable
- \+ *lemma* is_measurable_Union
- \+ *lemma* is_measurable_compl
- \+ *lemma* is_measurable_empty
- \+ *def* measurable
- \+ *lemma* measurable_space.comap_bot
- \+ *lemma* measurable_space.comap_comp
- \+ *lemma* measurable_space.comap_id
- \+ *lemma* measurable_space.comap_le_iff_le_map
- \+ *lemma* measurable_space.comap_map_le
- \+ *lemma* measurable_space.comap_mono
- \+ *lemma* measurable_space.comap_sup
- \+ *lemma* measurable_space.comap_supr
- \+ *lemma* measurable_space.gc_comap_map
- \+ *lemma* measurable_space.le_map_comap
- \+ *lemma* measurable_space.map_comp
- \+ *lemma* measurable_space.map_id
- \+ *lemma* measurable_space.map_inf
- \+ *lemma* measurable_space.map_infi
- \+ *lemma* measurable_space.map_mono
- \+ *lemma* measurable_space.map_top
- \+ *lemma* measurable_space.monotone_comap
- \+ *lemma* measurable_space.monotone_map
- \+ *structure* measurable_space
- \+ *lemma* measurable_space_eq



## [2017-08-29 19:20:11-04:00](https://github.com/leanprover-community/mathlib/commit/51042cd)
feat(topology/ennreal): add extended non-negative real numbers
#### Estimated changes
Modified algebra/big_operators.lean


Added topology/ennreal.lean
- \+ *lemma* ennreal.add_infty
- \+ *lemma* ennreal.add_le_add
- \+ *lemma* ennreal.forall_ennreal
- \+ *lemma* ennreal.infty_add
- \+ *lemma* ennreal.infty_le_iff
- \+ *lemma* ennreal.infty_mem_upper_bounds
- \+ *lemma* ennreal.infty_mul
- \+ *lemma* ennreal.infty_mul_of_real
- \+ *lemma* ennreal.infty_ne_of_real
- \+ *lemma* ennreal.infty_ne_zero
- \+ *lemma* ennreal.is_lub_of_real
- \+ *lemma* ennreal.le_infty
- \+ *lemma* ennreal.le_of_real_iff
- \+ *lemma* ennreal.le_zero_iff_eq
- \+ *lemma* ennreal.mul_infty
- \+ *lemma* ennreal.mul_le_mul
- \+ *def* ennreal.of_ennreal
- \+ *lemma* ennreal.of_ennreal_of_real
- \+ *lemma* ennreal.of_nonneg_real_eq_of_real
- \+ *def* ennreal.of_real
- \+ *lemma* ennreal.of_real_add_of_real
- \+ *lemma* ennreal.of_real_eq_of_real_of
- \+ *lemma* ennreal.of_real_eq_one_iff
- \+ *lemma* ennreal.of_real_eq_zero_iff
- \+ *lemma* ennreal.of_real_le_of_real_iff
- \+ *lemma* ennreal.of_real_lt_of_real_iff
- \+ *lemma* ennreal.of_real_mem_upper_bounds
- \+ *lemma* ennreal.of_real_mul_infty
- \+ *lemma* ennreal.of_real_mul_of_real
- \+ *lemma* ennreal.of_real_ne_infty
- \+ *lemma* ennreal.of_real_ne_of_real_of
- \+ *lemma* ennreal.of_real_of_ennreal
- \+ *lemma* ennreal.of_real_one
- \+ *lemma* ennreal.of_real_zero
- \+ *lemma* ennreal.one_eq_of_real_iff
- \+ *lemma* ennreal.zero_eq_of_real_iff
- \+ *lemma* ennreal.zero_le_of_ennreal
- \+ *lemma* ennreal.zero_ne_infty
- \+ *inductive* ennreal
- \+ *lemma* zero_le_mul

Modified topology/real.lean
- \+/\- *lemma* exists_supremum_real



## [2017-08-28 21:34:47-04:00](https://github.com/leanprover-community/mathlib/commit/76ae12c)
fix(algbera/big_operators): remove simp attr for sum/mul-distributivity rules
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.mul_sum
- \+/\- *lemma* finset.sum_mul



## [2017-08-28 21:30:00-04:00](https://github.com/leanprover-community/mathlib/commit/edfbf3c)
feat(algebra/big_operators): add semiring and integral_domain rules
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* exists_false
- \+ *lemma* finset.mul_sum
- \+ *lemma* finset.prod_const_one
- \+ *lemma* finset.prod_eq_zero
- \+ *lemma* finset.prod_eq_zero_iff
- \+/\- *lemma* finset.prod_hom
- \+/\- *lemma* finset.prod_inv_distrib
- \+ *lemma* finset.sum_le_sum
- \+ *lemma* finset.sum_le_zero
- \+ *lemma* finset.sum_mul
- \+/\- *lemma* finset.sum_sub_distrib
- \+ *lemma* finset.zero_le_sum



## [2017-08-28 19:34:30-04:00](https://github.com/leanprover-community/mathlib/commit/50ed0e4)
feat(algebra/big_operators): add congruence rule and morphism laws
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_congr
- \+/\- *lemma* finset.prod_empty
- \+ *lemma* finset.prod_hom
- \+/\- *lemma* finset.prod_image
- \+/\- *lemma* finset.prod_insert
- \+ *lemma* finset.prod_inv_distrib
- \+/\- *lemma* finset.prod_mul_distrib
- \+/\- *lemma* finset.prod_singleton
- \+/\- *lemma* finset.prod_to_finset_of_nodup
- \+ *lemma* finset.sum_sub_distrib

Modified data/finset/fold.lean
- \+ *lemma* finset.fold_congr
- \+/\- *lemma* finset.fold_hom
- \+/\- *lemma* finset.fold_image
- \+/\- *lemma* finset.fold_insert
- \+/\- *lemma* finset.fold_op_distrib
- \+/\- *lemma* finset.fold_singleton
- \+ *lemma* list.map_congr



## [2017-08-28 18:34:33-04:00](https://github.com/leanprover-community/mathlib/commit/4ed43d9)
feat(data/finset): add fold; add simp rules for insert, empty, singleton and mem
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_insert
- \- *lemma* finset.prod_to_finset
- \+ *lemma* finset.prod_to_finset_of_nodup
- \+ *lemma* finset.prod_union_inter
- \- *lemma* finset.prod_union_inter_eq
- \- *lemma* foldl_mul_assoc
- \- *lemma* foldl_mul_eq_mul_foldr
- \+ *theorem* list.prod_append
- \+ *theorem* list.prod_cons
- \+ *lemma* list.prod_eq_of_perm
- \+ *theorem* list.prod_join
- \+ *theorem* list.prod_nil
- \+ *theorem* list.prod_replicate
- \+ *lemma* list.prod_reverse
- \- *theorem* prod_append
- \- *theorem* prod_cons
- \- *lemma* prod_eq_of_perm
- \- *theorem* prod_join
- \- *theorem* prod_nil
- \- *theorem* prod_replicate

Modified data/finset/basic.lean
- \+/\- *theorem* finset.card_empty
- \+/\- *theorem* finset.card_erase_of_mem
- \- *theorem* finset.card_erase_of_not_mem
- \+/\- *theorem* finset.card_insert_le
- \- *theorem* finset.card_insert_of_mem
- \+/\- *theorem* finset.card_insert_of_not_mem
- \+/\- *theorem* finset.card_upto
- \+/\- *theorem* finset.empty_inter
- \+/\- *theorem* finset.empty_subset
- \+/\- *theorem* finset.empty_union
- \+/\- *theorem* finset.eq_empty_of_card_eq_zero
- \+/\- *theorem* finset.eq_empty_of_forall_not_mem
- \+/\- *theorem* finset.eq_empty_of_subset_empty
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq
- \- *theorem* finset.eq_of_subset_of_subset
- \- *theorem* finset.eq_or_mem_of_mem_insert
- \+/\- *theorem* finset.erase_empty
- \+/\- *theorem* finset.erase_eq_of_not_mem
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+/\- *theorem* finset.erase_subset
- \+/\- *theorem* finset.erase_subset_erase
- \+/\- *theorem* finset.erase_subset_of_subset_insert
- \+/\- *theorem* finset.exists_mem_of_ne_empty
- \+/\- *theorem* finset.forall_of_forall_insert
- \+/\- *theorem* finset.insert.comm
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+/\- *theorem* finset.insert_erase
- \+/\- *theorem* finset.insert_erase_subset
- \+ *theorem* finset.insert_idem
- \+/\- *theorem* finset.insert_inter_of_mem
- \+/\- *theorem* finset.insert_inter_of_not_mem
- \+ *theorem* finset.insert_ne_empty
- \+ *theorem* finset.insert_singelton_self_eq
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \+/\- *theorem* finset.inter_assoc
- \+/\- *theorem* finset.inter_comm
- \+/\- *theorem* finset.inter_empty
- \+ *theorem* finset.inter_insert_of_mem
- \+ *theorem* finset.inter_insert_of_not_mem
- \+/\- *theorem* finset.inter_left_comm
- \+/\- *theorem* finset.inter_right_comm
- \+/\- *theorem* finset.inter_self
- \+ *theorem* finset.inter_singleton_of_mem
- \+ *theorem* finset.inter_singleton_of_not_mem
- \+/\- *theorem* finset.lt_of_mem_upto
- \+/\- *theorem* finset.mem_empty_iff
- \+/\- *theorem* finset.mem_erase_iff
- \+/\- *theorem* finset.mem_erase_of_ne_of_mem
- \+/\- *theorem* finset.mem_insert
- \+/\- *theorem* finset.mem_insert_iff
- \+/\- *theorem* finset.mem_insert_of_mem
- \+/\- *theorem* finset.mem_inter_iff
- \+/\- *theorem* finset.mem_of_mem_erase
- \+/\- *theorem* finset.mem_of_mem_insert_of_ne
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \- *theorem* finset.mem_to_finset_of_nodup
- \+ *lemma* finset.mem_to_finset_of_nodup_eq
- \+/\- *theorem* finset.mem_union_iff
- \- *theorem* finset.mem_union_l
- \- *theorem* finset.mem_union_r
- \+/\- *theorem* finset.mem_upto_iff
- \+/\- *theorem* finset.mem_upto_of_lt
- \+/\- *theorem* finset.mem_upto_succ_of_mem_upto
- \+/\- *lemma* finset.ne_empty_of_card_eq_succ
- \+/\- *theorem* finset.ne_of_mem_erase
- \+/\- *theorem* finset.not_mem_empty
- \+/\- *theorem* finset.not_mem_erase
- \- *theorem* finset.pair_eq_singleton
- \- *theorem* finset.perm_insert_cons_of_not_mem
- \+/\- *theorem* finset.singleton_inter_of_mem
- \+/\- *theorem* finset.singleton_inter_of_not_mem
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.subset_insert
- \+/\- *theorem* finset.subset_insert_of_erase_subset
- \+/\- *theorem* finset.union_assoc
- \+/\- *theorem* finset.union_comm
- \+/\- *theorem* finset.union_empty
- \+ *theorem* finset.union_insert
- \+/\- *theorem* finset.union_self
- \+/\- *def* finset.upto
- \+/\- *theorem* finset.upto_succ
- \+ *lemma* or_self_or
- \+ *theorem* perm_insert_cons_of_not_mem

Added data/finset/default.lean


Added data/finset/fold.lean
- \+ *def* finset.fold
- \+ *lemma* finset.fold_empty
- \+ *lemma* finset.fold_hom
- \+ *lemma* finset.fold_image
- \+ *lemma* finset.fold_insert
- \+ *lemma* finset.fold_op_distrib
- \+ *lemma* finset.fold_singleton
- \+ *lemma* finset.fold_to_finset_of_nodup
- \+ *lemma* finset.fold_union_inter
- \+ *lemma* list.fold_op_eq_of_perm
- \+ *lemma* list.foldl_assoc
- \+ *lemma* list.foldl_assoc_comm_cons
- \+ *lemma* list.foldl_op_eq_op_foldr_assoc

Modified data/list/set.lean
- \+ *theorem* list.mem_erase_iff_of_nodup
- \+/\- *theorem* list.mem_erase_of_nodup



## [2017-08-28 12:56:25-05:00](https://github.com/leanprover-community/mathlib/commit/1aa7efa)
Merge remote-tracking branch 'upstream/master'
#### Estimated changes



## [2017-08-27 20:58:30-04:00](https://github.com/leanprover-community/mathlib/commit/b031441)
feat(algebra): add small theory of big operators on commutative monoids
#### Estimated changes
Added algebra/big_operators.lean
- \+ *lemma* finset.prod_empty
- \+ *lemma* finset.prod_image
- \+ *lemma* finset.prod_insert
- \+ *lemma* finset.prod_mul_distrib
- \+ *lemma* finset.prod_singleton
- \+ *lemma* finset.prod_to_finset
- \+ *lemma* finset.prod_union
- \+ *lemma* finset.prod_union_inter_eq
- \+ *lemma* foldl_mul_assoc
- \+ *lemma* foldl_mul_eq_mul_foldr
- \+ *theorem* prod_append
- \+ *theorem* prod_cons
- \+ *lemma* prod_eq_of_perm
- \+ *theorem* prod_join
- \+ *theorem* prod_nil
- \+ *theorem* prod_replicate



## [2017-08-27 20:57:59-04:00](https://github.com/leanprover-community/mathlib/commit/c17d11b)
fix(data/finset): use the type class projections for insert; hide most constants using protected; add image of finset
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.card_empty
- \- *def* finset.empty
- \+/\- *theorem* finset.empty_inter
- \+/\- *theorem* finset.empty_subset
- \+/\- *theorem* finset.empty_union
- \+/\- *theorem* finset.eq_empty_of_subset_empty
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq
- \+ *lemma* finset.erase_dup_map_erase_dup_eq
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+ *lemma* finset.image_id
- \+ *lemma* finset.image_image
- \+ *lemma* finset.image_to_finset
- \+ *lemma* finset.image_to_finset_of_nodup
- \+/\- *theorem* finset.insert.comm
- \- *def* finset.insert
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+ *theorem* finset.insert_inter_of_mem
- \+ *theorem* finset.insert_inter_of_not_mem
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \- *def* finset.inter
- \+/\- *theorem* finset.inter_empty
- \+/\- *theorem* finset.mem_insert
- \+/\- *theorem* finset.mem_insert_iff
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.perm_insert_cons_of_not_mem
- \+/\- *theorem* finset.singleton_inter_of_mem
- \+/\- *theorem* finset.singleton_inter_of_not_mem
- \- *def* finset.subset
- \- *def* finset.subset_aux
- \+/\- *theorem* finset.subset_empty_iff
- \- *def* finset.union
- \+/\- *theorem* finset.union_empty
- \+/\- *theorem* finset.upto_succ
- \+/\- *theorem* finset.upto_zero
- \+/\- *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \+/\- *theorem* list.length_erase_of_not_mem
- \+/\- *theorem* list.nodup_map
- \+ *theorem* list.nodup_map_on



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/f2b4d2e)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+/\- *theorem* finset.exists_mem_empty_iff
- \+/\- *theorem* finset.exists_mem_insert_iff
- \+/\- *theorem* finset.forall_mem_empty_iff
- \+/\- *theorem* finset.forall_mem_insert_iff
- \+/\- *theorem* finset.insert.comm
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \+/\- *theorem* finset.mem_insert
- \+/\- *theorem* finset.mem_insert_iff
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \+/\- *theorem* finset.pair_eq_singleton
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.upto_succ



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/79ed1c3)
refactor(data/finset): add type class instances
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq
- \- *theorem* finset.exists_mem_empty_eq
- \+/\- *theorem* finset.exists_mem_empty_iff
- \- *theorem* finset.exists_mem_insert_eq
- \+/\- *theorem* finset.exists_mem_insert_iff
- \- *theorem* finset.forall_mem_empty_eq
- \+/\- *theorem* finset.forall_mem_empty_iff
- \- *theorem* finset.forall_mem_insert_eq
- \+/\- *theorem* finset.forall_mem_insert_iff
- \+/\- *theorem* finset.forall_of_forall_insert
- \+/\- *theorem* finset.insert_eq
- \- *theorem* finset.mem_empty_eq
- \- *theorem* finset.mem_erase_eq
- \- *theorem* finset.mem_insert_eq
- \- *theorem* finset.mem_inter_eq
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \- *theorem* finset.mem_union_eq
- \- *theorem* finset.mem_upto_eq
- \+/\- *theorem* finset.pair_eq_singleton
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.upto_succ



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/73ae11b)
refactor(data/finset): fix formatting issues
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.mem_empty_iff
- \+/\- *theorem* finset.not_mem_empty
- \+/\- *def* finset.subset_aux
- \+/\- *def* finset
- \+/\- *def* nodup_list



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/8dbee5b)
feat(data/finset): add basics for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+ *theorem* finset.exists_mem_empty_eq
- \+/\- *theorem* finset.exists_mem_empty_iff
- \+ *theorem* finset.exists_mem_insert_eq
- \+/\- *theorem* finset.exists_mem_insert_iff
- \+ *theorem* finset.forall_mem_empty_eq
- \+/\- *theorem* finset.forall_mem_empty_iff
- \+ *theorem* finset.forall_mem_insert_eq
- \+/\- *theorem* finset.forall_mem_insert_iff
- \+/\- *theorem* finset.forall_of_forall_insert
- \+/\- *theorem* finset.insert.comm
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \+ *theorem* finset.mem_empty_eq
- \+/\- *theorem* finset.mem_empty_iff
- \+ *theorem* finset.mem_erase_eq
- \+/\- *theorem* finset.mem_insert
- \+ *theorem* finset.mem_insert_eq
- \+/\- *theorem* finset.mem_insert_iff
- \+ *theorem* finset.mem_inter_eq
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \+ *theorem* finset.mem_union_eq
- \+ *theorem* finset.mem_upto_eq
- \+/\- *theorem* finset.not_mem_empty
- \+/\- *theorem* finset.pair_eq_singleton
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *def* finset.subset_aux
- \+/\- *theorem* finset.upto_succ
- \+/\- *def* finset
- \+/\- *def* nodup_list



## [2017-08-27 12:30:11-05:00](https://github.com/leanprover-community/mathlib/commit/e678531)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq



## [2017-08-27 12:05:34-05:00](https://github.com/leanprover-community/mathlib/commit/b64eb68)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+/\- *theorem* finset.exists_mem_empty_iff
- \+/\- *theorem* finset.exists_mem_insert_iff
- \+/\- *theorem* finset.forall_mem_empty_iff
- \+/\- *theorem* finset.forall_mem_insert_iff
- \+/\- *theorem* finset.insert.comm
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \+/\- *theorem* finset.mem_insert
- \+/\- *theorem* finset.mem_insert_iff
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \+/\- *theorem* finset.pair_eq_singleton
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.upto_succ



## [2017-08-27 12:05:00-05:00](https://github.com/leanprover-community/mathlib/commit/5292cf1)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
Added data/finset/basic.lean
- \+ *def* finset.card
- \+ *theorem* finset.card_empty
- \+ *theorem* finset.card_erase_of_mem
- \+ *theorem* finset.card_erase_of_not_mem
- \+ *theorem* finset.card_insert_le
- \+ *theorem* finset.card_insert_of_mem
- \+ *theorem* finset.card_insert_of_not_mem
- \+ *theorem* finset.card_upto
- \+ *def* finset.empty
- \+ *theorem* finset.empty_inter
- \+ *theorem* finset.empty_subset
- \+ *theorem* finset.empty_union
- \+ *theorem* finset.eq_empty_of_card_eq_zero
- \+ *theorem* finset.eq_empty_of_forall_not_mem
- \+ *theorem* finset.eq_empty_of_subset_empty
- \+ *theorem* finset.eq_of_mem_singleton
- \+ *theorem* finset.eq_of_singleton_eq
- \+ *theorem* finset.eq_of_subset_of_subset
- \+ *theorem* finset.eq_or_mem_of_mem_insert
- \+ *def* finset.erase
- \+ *theorem* finset.erase_empty
- \+ *theorem* finset.erase_eq_of_not_mem
- \+ *theorem* finset.erase_insert
- \+ *theorem* finset.erase_insert_subset
- \+ *theorem* finset.erase_subset
- \+ *theorem* finset.erase_subset_erase
- \+ *theorem* finset.erase_subset_of_subset_insert
- \+ *theorem* finset.exists_mem_empty_iff
- \+ *theorem* finset.exists_mem_insert_iff
- \+ *theorem* finset.exists_mem_of_ne_empty
- \+ *theorem* finset.ext
- \+ *theorem* finset.forall_mem_empty_iff
- \+ *theorem* finset.forall_mem_insert_iff
- \+ *theorem* finset.forall_of_forall_insert
- \+ *theorem* finset.insert.comm
- \+ *def* finset.insert
- \+ *theorem* finset.insert_eq
- \+ *theorem* finset.insert_eq_of_mem
- \+ *theorem* finset.insert_erase
- \+ *theorem* finset.insert_erase_subset
- \+ *theorem* finset.insert_subset_insert
- \+ *theorem* finset.insert_union
- \+ *def* finset.inter
- \+ *theorem* finset.inter_assoc
- \+ *theorem* finset.inter_comm
- \+ *theorem* finset.inter_distrib_left
- \+ *theorem* finset.inter_distrib_right
- \+ *theorem* finset.inter_empty
- \+ *theorem* finset.inter_left_comm
- \+ *theorem* finset.inter_right_comm
- \+ *theorem* finset.inter_self
- \+ *theorem* finset.lt_of_mem_upto
- \+ *def* finset.mem
- \+ *theorem* finset.mem_empty_iff
- \+ *theorem* finset.mem_erase_iff
- \+ *theorem* finset.mem_erase_of_ne_of_mem
- \+ *theorem* finset.mem_insert
- \+ *theorem* finset.mem_insert_iff
- \+ *theorem* finset.mem_insert_of_mem
- \+ *theorem* finset.mem_inter
- \+ *theorem* finset.mem_inter_iff
- \+ *theorem* finset.mem_list_of_mem
- \+ *theorem* finset.mem_of_mem_erase
- \+ *theorem* finset.mem_of_mem_insert_of_ne
- \+ *theorem* finset.mem_of_mem_inter_left
- \+ *theorem* finset.mem_of_mem_inter_right
- \+ *theorem* finset.mem_of_mem_list
- \+ *theorem* finset.mem_of_subset_of_mem
- \+ *theorem* finset.mem_or_mem_of_mem_union
- \+ *theorem* finset.mem_singleton
- \+ *theorem* finset.mem_singleton_iff
- \+ *theorem* finset.mem_singleton_of_eq
- \+ *theorem* finset.mem_to_finset
- \+ *theorem* finset.mem_to_finset_of_nodup
- \+ *theorem* finset.mem_union_iff
- \+ *theorem* finset.mem_union_l
- \+ *theorem* finset.mem_union_left
- \+ *theorem* finset.mem_union_r
- \+ *theorem* finset.mem_union_right
- \+ *theorem* finset.mem_upto_iff
- \+ *theorem* finset.mem_upto_of_lt
- \+ *theorem* finset.mem_upto_succ_of_mem_upto
- \+ *lemma* finset.ne_empty_of_card_eq_succ
- \+ *theorem* finset.ne_of_mem_erase
- \+ *theorem* finset.not_mem_empty
- \+ *theorem* finset.not_mem_erase
- \+ *theorem* finset.pair_eq_singleton
- \+ *theorem* finset.perm_insert_cons_of_not_mem
- \+ *theorem* finset.singleton_inter_of_mem
- \+ *theorem* finset.singleton_inter_of_not_mem
- \+ *theorem* finset.singleton_ne_empty
- \+ *theorem* finset.subset.antisymm
- \+ *theorem* finset.subset.refl
- \+ *theorem* finset.subset.trans
- \+ *def* finset.subset
- \+ *def* finset.subset_aux
- \+ *theorem* finset.subset_empty_iff
- \+ *theorem* finset.subset_insert
- \+ *theorem* finset.subset_insert_iff
- \+ *theorem* finset.subset_insert_of_erase_subset
- \+ *theorem* finset.subset_of_forall
- \+ *def* finset.to_finset
- \+ *lemma* finset.to_finset_eq_of_nodup
- \+ *def* finset.to_finset_of_nodup
- \+ *def* finset.union
- \+ *theorem* finset.union_assoc
- \+ *theorem* finset.union_comm
- \+ *theorem* finset.union_distrib_left
- \+ *theorem* finset.union_distrib_right
- \+ *theorem* finset.union_empty
- \+ *theorem* finset.union_left_comm
- \+ *theorem* finset.union_right_comm
- \+ *theorem* finset.union_self
- \+ *def* finset.upto
- \+ *theorem* finset.upto_succ
- \+ *theorem* finset.upto_zero
- \+ *def* finset
- \+ *def* nodup_list
- \+ *def* to_nodup_list
- \+ *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \+ *theorem* list.length_erase_of_not_mem



## [2017-08-27 12:26:42-04:00](https://github.com/leanprover-community/mathlib/commit/1f992c9)
fix(.): adapt to Lean changes: type class parameters to structures are now type class parameters in the projections and constructor
#### Estimated changes
Modified algebra/module.lean
- \+/\- *theorem* mul_smul
- \+/\- *theorem* smul_left_distrib
- \+/\- *theorem* smul_right_distrib

Modified data/fp/basic.lean
- \+/\- *def* fp.float.default_nan

Modified order/basic.lean


Modified topology/topological_space.lean
- \+/\- *lemma* t2_separation

Modified topology/topological_structures.lean




## [2017-08-26 15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/5b3b136)
feat(topology): port metric space from lean2
#### Estimated changes
Modified algebra/field.lean


Modified algebra/group.lean
- \+ *lemma* abs_eq_zero_iff

Modified data/rat.lean


Modified order/basic.lean
- \+ *lemma* dense
- \+ *lemma* eq_of_le_of_forall_ge
- \+ *lemma* eq_of_le_of_forall_le
- \+ *lemma* le_of_forall_ge
- \+ *lemma* le_of_forall_le
- \+ *lemma* no_bot
- \+ *lemma* no_top

Modified order/complete_lattice.lean
- \- *theorem* lattice.foo'
- \- *theorem* lattice.foo
- \+ *lemma* lattice.inf_infi
- \+ *lemma* lattice.infi_inf

Modified order/filter.lean
- \+/\- *lemma* filter.mem_prod_iff
- \+/\- *lemma* filter.mem_prod_same_iff
- \+/\- *lemma* filter.prod_comm
- \+ *lemma* filter.prod_def
- \+ *lemma* filter.prod_infi_left
- \+ *lemma* filter.prod_infi_right
- \+/\- *lemma* filter.prod_mem_prod
- \+/\- *lemma* filter.prod_same_eq
- \+ *lemma* filter.tendsto_infi'
- \+ *lemma* filter.tendsto_infi
- \+ *lemma* filter.tendsto_principal_principal

Added topology/metric_space.lean
- \+ *def* closed_ball
- \+ *lemma* continuous_dist'
- \+ *lemma* continuous_dist
- \+ *def* dist
- \+ *lemma* dist_comm
- \+ *lemma* dist_eq_zero_iff
- \+ *lemma* dist_nonneg
- \+ *lemma* dist_pos_of_ne
- \+ *lemma* dist_self
- \+ *lemma* dist_triangle
- \+ *lemma* eq_of_dist_eq_zero
- \+ *lemma* eq_of_forall_dist_le
- \+ *lemma* exists_subtype
- \+ *theorem* is_closed_closed_ball
- \+ *theorem* is_open_metric
- \+ *theorem* is_open_open_ball
- \+ *theorem* mem_nhds_sets_iff_metric
- \+ *theorem* mem_open_ball
- \+ *lemma* ne_of_dist_pos
- \+ *theorem* nhds_eq_metric
- \+ *def* open_ball
- \+ *theorem* open_ball_eq_empty_of_nonpos
- \+ *lemma* open_ball_subset_open_ball_of_le
- \+ *theorem* pos_of_mem_open_ball
- \+ *lemma* tendsto_dist
- \+ *lemma* uniform_continuous_dist'
- \+ *lemma* uniform_continuous_dist
- \+ *lemma* uniformity_dist'
- \+ *lemma* uniformity_dist
- \+ *lemma* zero_eq_dist_iff

Modified topology/real.lean
- \- *lemma* zero_lt_two

Modified topology/uniform_space.lean
- \+ *lemma* uniformity_prod_eq_prod



## [2017-08-26 15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/f1fba68)
feat(algebra): porting modules from lean2
#### Estimated changes
Added algebra/module.lean
- \+ *theorem* mul_smul
- \+ *theorem* neg_smul
- \+ *theorem* one_smul
- \+ *def* ring.to_module
- \+ *theorem* smul_left_distrib
- \+ *theorem* smul_neg
- \+ *theorem* smul_right_distrib
- \+ *theorem* smul_sub_left_distrib
- \+ *theorem* smul_zero
- \+ *theorem* sub_smul_right_distrib
- \+ *theorem* zero_smul



## [2017-08-26 15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/d1cbb8f)
fix(algebra/group): add every transport theorem from main Lean repository
#### Estimated changes
Modified algebra/group.lean


Deleted data/finset/basic.lean
- \- *def* finset.card
- \- *theorem* finset.card_empty
- \- *theorem* finset.card_erase_of_mem
- \- *theorem* finset.card_erase_of_not_mem
- \- *theorem* finset.card_insert_le
- \- *theorem* finset.card_insert_of_mem
- \- *theorem* finset.card_insert_of_not_mem
- \- *theorem* finset.card_upto
- \- *def* finset.empty
- \- *theorem* finset.empty_inter
- \- *theorem* finset.empty_subset
- \- *theorem* finset.empty_union
- \- *theorem* finset.eq_empty_of_card_eq_zero
- \- *theorem* finset.eq_empty_of_forall_not_mem
- \- *theorem* finset.eq_empty_of_subset_empty
- \- *theorem* finset.eq_of_mem_singleton
- \- *theorem* finset.eq_of_singleton_eq
- \- *theorem* finset.eq_of_subset_of_subset
- \- *theorem* finset.eq_or_mem_of_mem_insert
- \- *def* finset.erase
- \- *theorem* finset.erase_empty
- \- *theorem* finset.erase_eq_of_not_mem
- \- *theorem* finset.erase_insert
- \- *theorem* finset.erase_insert_subset
- \- *theorem* finset.erase_subset
- \- *theorem* finset.erase_subset_erase
- \- *theorem* finset.erase_subset_of_subset_insert
- \- *theorem* finset.exists_mem_empty_iff
- \- *theorem* finset.exists_mem_insert_iff
- \- *theorem* finset.exists_mem_of_ne_empty
- \- *theorem* finset.ext
- \- *theorem* finset.forall_mem_empty_iff
- \- *theorem* finset.forall_mem_insert_iff
- \- *theorem* finset.forall_of_forall_insert
- \- *theorem* finset.insert.comm
- \- *def* finset.insert
- \- *theorem* finset.insert_eq
- \- *theorem* finset.insert_eq_of_mem
- \- *theorem* finset.insert_erase
- \- *theorem* finset.insert_erase_subset
- \- *theorem* finset.insert_subset_insert
- \- *theorem* finset.insert_union
- \- *def* finset.inter
- \- *theorem* finset.inter_assoc
- \- *theorem* finset.inter_comm
- \- *theorem* finset.inter_distrib_left
- \- *theorem* finset.inter_distrib_right
- \- *theorem* finset.inter_empty
- \- *theorem* finset.inter_left_comm
- \- *theorem* finset.inter_right_comm
- \- *theorem* finset.inter_self
- \- *theorem* finset.lt_of_mem_upto
- \- *def* finset.mem
- \- *theorem* finset.mem_empty_iff
- \- *theorem* finset.mem_erase_iff
- \- *theorem* finset.mem_erase_of_ne_of_mem
- \- *theorem* finset.mem_insert
- \- *theorem* finset.mem_insert_iff
- \- *theorem* finset.mem_insert_of_mem
- \- *theorem* finset.mem_inter
- \- *theorem* finset.mem_inter_iff
- \- *theorem* finset.mem_list_of_mem
- \- *theorem* finset.mem_of_mem_erase
- \- *theorem* finset.mem_of_mem_insert_of_ne
- \- *theorem* finset.mem_of_mem_inter_left
- \- *theorem* finset.mem_of_mem_inter_right
- \- *theorem* finset.mem_of_mem_list
- \- *theorem* finset.mem_of_subset_of_mem
- \- *theorem* finset.mem_or_mem_of_mem_union
- \- *theorem* finset.mem_singleton
- \- *theorem* finset.mem_singleton_iff
- \- *theorem* finset.mem_singleton_of_eq
- \- *theorem* finset.mem_to_finset
- \- *theorem* finset.mem_to_finset_of_nodup
- \- *theorem* finset.mem_union_iff
- \- *theorem* finset.mem_union_l
- \- *theorem* finset.mem_union_left
- \- *theorem* finset.mem_union_r
- \- *theorem* finset.mem_union_right
- \- *theorem* finset.mem_upto_iff
- \- *theorem* finset.mem_upto_of_lt
- \- *theorem* finset.mem_upto_succ_of_mem_upto
- \- *lemma* finset.ne_empty_of_card_eq_succ
- \- *theorem* finset.ne_of_mem_erase
- \- *theorem* finset.not_mem_empty
- \- *theorem* finset.not_mem_erase
- \- *theorem* finset.pair_eq_singleton
- \- *theorem* finset.perm_insert_cons_of_not_mem
- \- *theorem* finset.singleton_inter_of_mem
- \- *theorem* finset.singleton_inter_of_not_mem
- \- *theorem* finset.singleton_ne_empty
- \- *theorem* finset.subset.antisymm
- \- *theorem* finset.subset.refl
- \- *theorem* finset.subset.trans
- \- *def* finset.subset
- \- *def* finset.subset_aux
- \- *theorem* finset.subset_empty_iff
- \- *theorem* finset.subset_insert
- \- *theorem* finset.subset_insert_iff
- \- *theorem* finset.subset_insert_of_erase_subset
- \- *theorem* finset.subset_of_forall
- \- *def* finset.to_finset
- \- *lemma* finset.to_finset_eq_of_nodup
- \- *def* finset.to_finset_of_nodup
- \- *def* finset.union
- \- *theorem* finset.union_assoc
- \- *theorem* finset.union_comm
- \- *theorem* finset.union_distrib_left
- \- *theorem* finset.union_distrib_right
- \- *theorem* finset.union_empty
- \- *theorem* finset.union_left_comm
- \- *theorem* finset.union_right_comm
- \- *theorem* finset.union_self
- \- *def* finset.upto
- \- *theorem* finset.upto_succ
- \- *theorem* finset.upto_zero
- \- *def* finset
- \- *def* nodup_list
- \- *def* to_nodup_list
- \- *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \- *theorem* list.length_erase_of_not_mem

Modified topology/real.lean




## [2017-08-26 13:03:40-05:00](https://github.com/leanprover-community/mathlib/commit/67a2f39)
refactor(data/finset): add type class instances
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* finset.eq_of_mem_singleton
- \+/\- *theorem* finset.eq_of_singleton_eq
- \- *theorem* finset.exists_mem_empty_eq
- \+/\- *theorem* finset.exists_mem_empty_iff
- \- *theorem* finset.exists_mem_insert_eq
- \+/\- *theorem* finset.exists_mem_insert_iff
- \- *theorem* finset.forall_mem_empty_eq
- \+/\- *theorem* finset.forall_mem_empty_iff
- \- *theorem* finset.forall_mem_insert_eq
- \+/\- *theorem* finset.forall_mem_insert_iff
- \+/\- *theorem* finset.forall_of_forall_insert
- \+/\- *theorem* finset.insert_eq
- \- *theorem* finset.mem_empty_eq
- \- *theorem* finset.mem_erase_eq
- \- *theorem* finset.mem_insert_eq
- \- *theorem* finset.mem_inter_eq
- \+/\- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_list
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_iff
- \+/\- *theorem* finset.mem_singleton_of_eq
- \- *theorem* finset.mem_union_eq
- \- *theorem* finset.mem_upto_eq
- \+/\- *theorem* finset.pair_eq_singleton
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.upto_succ



## [2017-08-26 12:24:58-05:00](https://github.com/leanprover-community/mathlib/commit/cde1bd8)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
Modified topology/continuity.lean
- \+ *lemma* is_open_prod
- \+ *lemma* is_open_prod_iff
- \- *lemma* is_open_set_prod

Modified topology/real.lean
- \- *lemma* continuous_add_rat
- \- *lemma* continuous_add_real'
- \- *lemma* continuous_add_real
- \- *lemma* continuous_neg_rat
- \- *lemma* continuous_neg_real
- \- *lemma* continuous_sub_real
- \+/\- *lemma* exists_supremum_real
- \- *lemma* is_closed_ge
- \- *lemma* is_closed_le
- \- *lemma* is_closed_le_real
- \- *lemma* is_open_gt
- \- *lemma* is_open_lt
- \- *lemma* is_open_lt_real
- \- *lemma* tendsto_add_rat
- \- *lemma* tendsto_mul_rat
- \- *lemma* tendsto_neg_rat

Added topology/topological_structures.lean
- \+ *lemma* continuous_add'
- \+ *lemma* continuous_add
- \+ *lemma* continuous_mul
- \+ *lemma* continuous_neg'
- \+ *lemma* continuous_neg
- \+ *lemma* continuous_sub
- \+ *lemma* dense_or_discrete
- \+ *lemma* is_closed_le
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_lt_fst_snd
- \+ *lemma* order_separated
- \+ *lemma* tendsto_add
- \+ *lemma* tendsto_mul
- \+ *lemma* tendsto_neg
- \+ *lemma* tendsto_sub



## [2017-08-25 13:00:17-05:00](https://github.com/leanprover-community/mathlib/commit/dff0ffd)
refactor(data/finset): fix formatting issues
#### Estimated changes
Added data/finset/basic.lean
- \+ *def* finset.card
- \+ *theorem* finset.card_empty
- \+ *theorem* finset.card_erase_of_mem
- \+ *theorem* finset.card_erase_of_not_mem
- \+ *theorem* finset.card_insert_le
- \+ *theorem* finset.card_insert_of_mem
- \+ *theorem* finset.card_insert_of_not_mem
- \+ *theorem* finset.card_upto
- \+ *def* finset.empty
- \+ *theorem* finset.empty_inter
- \+ *theorem* finset.empty_subset
- \+ *theorem* finset.empty_union
- \+ *theorem* finset.eq_empty_of_card_eq_zero
- \+ *theorem* finset.eq_empty_of_forall_not_mem
- \+ *theorem* finset.eq_empty_of_subset_empty
- \+ *theorem* finset.eq_of_mem_singleton
- \+ *theorem* finset.eq_of_singleton_eq
- \+ *theorem* finset.eq_of_subset_of_subset
- \+ *theorem* finset.eq_or_mem_of_mem_insert
- \+ *def* finset.erase
- \+ *theorem* finset.erase_empty
- \+ *theorem* finset.erase_eq_of_not_mem
- \+ *theorem* finset.erase_insert
- \+ *theorem* finset.erase_insert_subset
- \+ *theorem* finset.erase_subset
- \+ *theorem* finset.erase_subset_erase
- \+ *theorem* finset.erase_subset_of_subset_insert
- \+ *theorem* finset.exists_mem_empty_eq
- \+ *theorem* finset.exists_mem_empty_iff
- \+ *theorem* finset.exists_mem_insert_eq
- \+ *theorem* finset.exists_mem_insert_iff
- \+ *theorem* finset.exists_mem_of_ne_empty
- \+ *theorem* finset.ext
- \+ *theorem* finset.forall_mem_empty_eq
- \+ *theorem* finset.forall_mem_empty_iff
- \+ *theorem* finset.forall_mem_insert_eq
- \+ *theorem* finset.forall_mem_insert_iff
- \+ *theorem* finset.forall_of_forall_insert
- \+ *theorem* finset.insert.comm
- \+ *def* finset.insert
- \+ *theorem* finset.insert_eq
- \+ *theorem* finset.insert_eq_of_mem
- \+ *theorem* finset.insert_erase
- \+ *theorem* finset.insert_erase_subset
- \+ *theorem* finset.insert_subset_insert
- \+ *theorem* finset.insert_union
- \+ *def* finset.inter
- \+ *theorem* finset.inter_assoc
- \+ *theorem* finset.inter_comm
- \+ *theorem* finset.inter_distrib_left
- \+ *theorem* finset.inter_distrib_right
- \+ *theorem* finset.inter_empty
- \+ *theorem* finset.inter_left_comm
- \+ *theorem* finset.inter_right_comm
- \+ *theorem* finset.inter_self
- \+ *theorem* finset.lt_of_mem_upto
- \+ *def* finset.mem
- \+ *theorem* finset.mem_empty_eq
- \+ *theorem* finset.mem_empty_iff
- \+ *theorem* finset.mem_erase_eq
- \+ *theorem* finset.mem_erase_iff
- \+ *theorem* finset.mem_erase_of_ne_of_mem
- \+ *theorem* finset.mem_insert
- \+ *theorem* finset.mem_insert_eq
- \+ *theorem* finset.mem_insert_iff
- \+ *theorem* finset.mem_insert_of_mem
- \+ *theorem* finset.mem_inter
- \+ *theorem* finset.mem_inter_eq
- \+ *theorem* finset.mem_inter_iff
- \+ *theorem* finset.mem_list_of_mem
- \+ *theorem* finset.mem_of_mem_erase
- \+ *theorem* finset.mem_of_mem_insert_of_ne
- \+ *theorem* finset.mem_of_mem_inter_left
- \+ *theorem* finset.mem_of_mem_inter_right
- \+ *theorem* finset.mem_of_mem_list
- \+ *theorem* finset.mem_of_subset_of_mem
- \+ *theorem* finset.mem_or_mem_of_mem_union
- \+ *theorem* finset.mem_singleton
- \+ *theorem* finset.mem_singleton_iff
- \+ *theorem* finset.mem_singleton_of_eq
- \+ *theorem* finset.mem_to_finset
- \+ *theorem* finset.mem_to_finset_of_nodup
- \+ *theorem* finset.mem_union_eq
- \+ *theorem* finset.mem_union_iff
- \+ *theorem* finset.mem_union_l
- \+ *theorem* finset.mem_union_left
- \+ *theorem* finset.mem_union_r
- \+ *theorem* finset.mem_union_right
- \+ *theorem* finset.mem_upto_eq
- \+ *theorem* finset.mem_upto_iff
- \+ *theorem* finset.mem_upto_of_lt
- \+ *theorem* finset.mem_upto_succ_of_mem_upto
- \+ *lemma* finset.ne_empty_of_card_eq_succ
- \+ *theorem* finset.ne_of_mem_erase
- \+ *theorem* finset.not_mem_empty
- \+ *theorem* finset.not_mem_erase
- \+ *theorem* finset.pair_eq_singleton
- \+ *theorem* finset.perm_insert_cons_of_not_mem
- \+ *theorem* finset.singleton_inter_of_mem
- \+ *theorem* finset.singleton_inter_of_not_mem
- \+ *theorem* finset.singleton_ne_empty
- \+ *theorem* finset.subset.antisymm
- \+ *theorem* finset.subset.refl
- \+ *theorem* finset.subset.trans
- \+ *def* finset.subset
- \+ *def* finset.subset_aux
- \+ *theorem* finset.subset_empty_iff
- \+ *theorem* finset.subset_insert
- \+ *theorem* finset.subset_insert_iff
- \+ *theorem* finset.subset_insert_of_erase_subset
- \+ *theorem* finset.subset_of_forall
- \+ *def* finset.to_finset
- \+ *lemma* finset.to_finset_eq_of_nodup
- \+ *def* finset.to_finset_of_nodup
- \+ *def* finset.union
- \+ *theorem* finset.union_assoc
- \+ *theorem* finset.union_comm
- \+ *theorem* finset.union_distrib_left
- \+ *theorem* finset.union_distrib_right
- \+ *theorem* finset.union_empty
- \+ *theorem* finset.union_left_comm
- \+ *theorem* finset.union_right_comm
- \+ *theorem* finset.union_self
- \+ *def* finset.upto
- \+ *theorem* finset.upto_succ
- \+ *theorem* finset.upto_zero
- \+ *def* finset
- \+ *def* nodup_list
- \+ *def* to_nodup_list
- \+ *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \+ *theorem* list.length_erase_of_not_mem

Modified topology/continuity.lean
- \- *lemma* is_open_prod
- \- *lemma* is_open_prod_iff
- \+ *lemma* is_open_set_prod

Modified topology/real.lean
- \+ *lemma* continuous_add_rat
- \+ *lemma* continuous_add_real'
- \+ *lemma* continuous_add_real
- \+ *lemma* continuous_neg_rat
- \+ *lemma* continuous_neg_real
- \+ *lemma* continuous_sub_real
- \+/\- *lemma* exists_supremum_real
- \+ *lemma* is_closed_ge
- \+ *lemma* is_closed_le
- \+ *lemma* is_closed_le_real
- \+ *lemma* is_open_gt
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_lt_real
- \+ *lemma* tendsto_add_rat
- \+ *lemma* tendsto_mul_rat
- \+ *lemma* tendsto_neg_rat

Deleted topology/topological_structures.lean
- \- *lemma* continuous_add'
- \- *lemma* continuous_add
- \- *lemma* continuous_mul
- \- *lemma* continuous_neg'
- \- *lemma* continuous_neg
- \- *lemma* continuous_sub
- \- *lemma* dense_or_discrete
- \- *lemma* is_closed_le
- \- *lemma* is_open_lt
- \- *lemma* is_open_lt_fst_snd
- \- *lemma* order_separated
- \- *lemma* tendsto_add
- \- *lemma* tendsto_mul
- \- *lemma* tendsto_neg
- \- *lemma* tendsto_sub



## [2017-08-24 19:09:36-04:00](https://github.com/leanprover-community/mathlib/commit/7c72de2)
feat(topology): add topological structures for groups, ring, and linear orders; add instances for rat and real
#### Estimated changes
Deleted data/finset/basic.lean
- \- *def* finset.card
- \- *theorem* finset.card_empty
- \- *theorem* finset.card_erase_of_mem
- \- *theorem* finset.card_erase_of_not_mem
- \- *theorem* finset.card_insert_le
- \- *theorem* finset.card_insert_of_mem
- \- *theorem* finset.card_insert_of_not_mem
- \- *theorem* finset.card_upto
- \- *def* finset.empty
- \- *theorem* finset.empty_inter
- \- *theorem* finset.empty_subset
- \- *theorem* finset.empty_union
- \- *theorem* finset.eq_empty_of_card_eq_zero
- \- *theorem* finset.eq_empty_of_forall_not_mem
- \- *theorem* finset.eq_empty_of_subset_empty
- \- *theorem* finset.eq_of_mem_singleton
- \- *theorem* finset.eq_of_singleton_eq
- \- *theorem* finset.eq_of_subset_of_subset
- \- *theorem* finset.eq_or_mem_of_mem_insert
- \- *def* finset.erase
- \- *theorem* finset.erase_empty
- \- *theorem* finset.erase_eq_of_not_mem
- \- *theorem* finset.erase_insert
- \- *theorem* finset.erase_insert_subset
- \- *theorem* finset.erase_subset
- \- *theorem* finset.erase_subset_erase
- \- *theorem* finset.erase_subset_of_subset_insert
- \- *theorem* finset.exists_mem_empty_eq
- \- *theorem* finset.exists_mem_empty_iff
- \- *theorem* finset.exists_mem_insert_eq
- \- *theorem* finset.exists_mem_insert_iff
- \- *theorem* finset.exists_mem_of_ne_empty
- \- *theorem* finset.ext
- \- *theorem* finset.forall_mem_empty_eq
- \- *theorem* finset.forall_mem_empty_iff
- \- *theorem* finset.forall_mem_insert_eq
- \- *theorem* finset.forall_mem_insert_iff
- \- *theorem* finset.forall_of_forall_insert
- \- *theorem* finset.insert.comm
- \- *def* finset.insert
- \- *theorem* finset.insert_eq
- \- *theorem* finset.insert_eq_of_mem
- \- *theorem* finset.insert_erase
- \- *theorem* finset.insert_erase_subset
- \- *theorem* finset.insert_subset_insert
- \- *theorem* finset.insert_union
- \- *def* finset.inter
- \- *theorem* finset.inter_assoc
- \- *theorem* finset.inter_comm
- \- *theorem* finset.inter_distrib_left
- \- *theorem* finset.inter_distrib_right
- \- *theorem* finset.inter_empty
- \- *theorem* finset.inter_left_comm
- \- *theorem* finset.inter_right_comm
- \- *theorem* finset.inter_self
- \- *theorem* finset.lt_of_mem_upto
- \- *def* finset.mem
- \- *theorem* finset.mem_empty_eq
- \- *theorem* finset.mem_empty_iff
- \- *theorem* finset.mem_erase_eq
- \- *theorem* finset.mem_erase_iff
- \- *theorem* finset.mem_erase_of_ne_of_mem
- \- *theorem* finset.mem_insert
- \- *theorem* finset.mem_insert_eq
- \- *theorem* finset.mem_insert_iff
- \- *theorem* finset.mem_insert_of_mem
- \- *theorem* finset.mem_inter
- \- *theorem* finset.mem_inter_eq
- \- *theorem* finset.mem_inter_iff
- \- *theorem* finset.mem_list_of_mem
- \- *theorem* finset.mem_of_mem_erase
- \- *theorem* finset.mem_of_mem_insert_of_ne
- \- *theorem* finset.mem_of_mem_inter_left
- \- *theorem* finset.mem_of_mem_inter_right
- \- *theorem* finset.mem_of_mem_list
- \- *theorem* finset.mem_of_subset_of_mem
- \- *theorem* finset.mem_or_mem_of_mem_union
- \- *theorem* finset.mem_singleton
- \- *theorem* finset.mem_singleton_iff
- \- *theorem* finset.mem_singleton_of_eq
- \- *theorem* finset.mem_to_finset
- \- *theorem* finset.mem_to_finset_of_nodup
- \- *theorem* finset.mem_union_eq
- \- *theorem* finset.mem_union_iff
- \- *theorem* finset.mem_union_l
- \- *theorem* finset.mem_union_left
- \- *theorem* finset.mem_union_r
- \- *theorem* finset.mem_union_right
- \- *theorem* finset.mem_upto_eq
- \- *theorem* finset.mem_upto_iff
- \- *theorem* finset.mem_upto_of_lt
- \- *theorem* finset.mem_upto_succ_of_mem_upto
- \- *lemma* finset.ne_empty_of_card_eq_succ
- \- *theorem* finset.ne_of_mem_erase
- \- *theorem* finset.not_mem_empty
- \- *theorem* finset.not_mem_erase
- \- *theorem* finset.pair_eq_singleton
- \- *theorem* finset.perm_insert_cons_of_not_mem
- \- *theorem* finset.singleton_inter_of_mem
- \- *theorem* finset.singleton_inter_of_not_mem
- \- *theorem* finset.singleton_ne_empty
- \- *theorem* finset.subset.antisymm
- \- *theorem* finset.subset.refl
- \- *theorem* finset.subset.trans
- \- *def* finset.subset
- \- *def* finset.subset_aux
- \- *theorem* finset.subset_empty_iff
- \- *theorem* finset.subset_insert
- \- *theorem* finset.subset_insert_iff
- \- *theorem* finset.subset_insert_of_erase_subset
- \- *theorem* finset.subset_of_forall
- \- *def* finset.to_finset
- \- *lemma* finset.to_finset_eq_of_nodup
- \- *def* finset.to_finset_of_nodup
- \- *def* finset.union
- \- *theorem* finset.union_assoc
- \- *theorem* finset.union_comm
- \- *theorem* finset.union_distrib_left
- \- *theorem* finset.union_distrib_right
- \- *theorem* finset.union_empty
- \- *theorem* finset.union_left_comm
- \- *theorem* finset.union_right_comm
- \- *theorem* finset.union_self
- \- *def* finset.upto
- \- *theorem* finset.upto_succ
- \- *theorem* finset.upto_zero
- \- *def* finset
- \- *def* nodup_list
- \- *def* to_nodup_list
- \- *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \- *theorem* list.length_erase_of_not_mem

Modified topology/continuity.lean
- \+ *lemma* is_open_prod
- \+ *lemma* is_open_prod_iff
- \- *lemma* is_open_set_prod

Modified topology/real.lean
- \- *lemma* continuous_add_rat
- \- *lemma* continuous_add_real'
- \- *lemma* continuous_add_real
- \- *lemma* continuous_neg_rat
- \- *lemma* continuous_neg_real
- \- *lemma* continuous_sub_real
- \+/\- *lemma* exists_supremum_real
- \- *lemma* is_closed_ge
- \- *lemma* is_closed_le
- \- *lemma* is_closed_le_real
- \- *lemma* is_open_gt
- \- *lemma* is_open_lt
- \- *lemma* is_open_lt_real
- \- *lemma* tendsto_add_rat
- \- *lemma* tendsto_mul_rat
- \- *lemma* tendsto_neg_rat

Added topology/topological_structures.lean
- \+ *lemma* continuous_add'
- \+ *lemma* continuous_add
- \+ *lemma* continuous_mul
- \+ *lemma* continuous_neg'
- \+ *lemma* continuous_neg
- \+ *lemma* continuous_sub
- \+ *lemma* dense_or_discrete
- \+ *lemma* is_closed_le
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_lt_fst_snd
- \+ *lemma* order_separated
- \+ *lemma* tendsto_add
- \+ *lemma* tendsto_mul
- \+ *lemma* tendsto_neg
- \+ *lemma* tendsto_sub



## [2017-08-24 16:21:01-05:00](https://github.com/leanprover-community/mathlib/commit/7df585e)
feat(data/finset): add basics for finsets
#### Estimated changes
Added data/finset/basic.lean
- \+ *def* finset.card
- \+ *theorem* finset.card_empty
- \+ *theorem* finset.card_erase_of_mem
- \+ *theorem* finset.card_erase_of_not_mem
- \+ *theorem* finset.card_insert_le
- \+ *theorem* finset.card_insert_of_mem
- \+ *theorem* finset.card_insert_of_not_mem
- \+ *theorem* finset.card_upto
- \+ *def* finset.empty
- \+ *theorem* finset.empty_inter
- \+ *theorem* finset.empty_subset
- \+ *theorem* finset.empty_union
- \+ *theorem* finset.eq_empty_of_card_eq_zero
- \+ *theorem* finset.eq_empty_of_forall_not_mem
- \+ *theorem* finset.eq_empty_of_subset_empty
- \+ *theorem* finset.eq_of_mem_singleton
- \+ *theorem* finset.eq_of_singleton_eq
- \+ *theorem* finset.eq_of_subset_of_subset
- \+ *theorem* finset.eq_or_mem_of_mem_insert
- \+ *def* finset.erase
- \+ *theorem* finset.erase_empty
- \+ *theorem* finset.erase_eq_of_not_mem
- \+ *theorem* finset.erase_insert
- \+ *theorem* finset.erase_insert_subset
- \+ *theorem* finset.erase_subset
- \+ *theorem* finset.erase_subset_erase
- \+ *theorem* finset.erase_subset_of_subset_insert
- \+ *theorem* finset.exists_mem_empty_eq
- \+ *theorem* finset.exists_mem_empty_iff
- \+ *theorem* finset.exists_mem_insert_eq
- \+ *theorem* finset.exists_mem_insert_iff
- \+ *theorem* finset.exists_mem_of_ne_empty
- \+ *theorem* finset.ext
- \+ *theorem* finset.forall_mem_empty_eq
- \+ *theorem* finset.forall_mem_empty_iff
- \+ *theorem* finset.forall_mem_insert_eq
- \+ *theorem* finset.forall_mem_insert_iff
- \+ *theorem* finset.forall_of_forall_insert
- \+ *theorem* finset.insert.comm
- \+ *def* finset.insert
- \+ *theorem* finset.insert_eq
- \+ *theorem* finset.insert_eq_of_mem
- \+ *theorem* finset.insert_erase
- \+ *theorem* finset.insert_erase_subset
- \+ *theorem* finset.insert_subset_insert
- \+ *theorem* finset.insert_union
- \+ *def* finset.inter
- \+ *theorem* finset.inter_assoc
- \+ *theorem* finset.inter_comm
- \+ *theorem* finset.inter_distrib_left
- \+ *theorem* finset.inter_distrib_right
- \+ *theorem* finset.inter_empty
- \+ *theorem* finset.inter_left_comm
- \+ *theorem* finset.inter_right_comm
- \+ *theorem* finset.inter_self
- \+ *theorem* finset.lt_of_mem_upto
- \+ *def* finset.mem
- \+ *theorem* finset.mem_empty_eq
- \+ *theorem* finset.mem_empty_iff
- \+ *theorem* finset.mem_erase_eq
- \+ *theorem* finset.mem_erase_iff
- \+ *theorem* finset.mem_erase_of_ne_of_mem
- \+ *theorem* finset.mem_insert
- \+ *theorem* finset.mem_insert_eq
- \+ *theorem* finset.mem_insert_iff
- \+ *theorem* finset.mem_insert_of_mem
- \+ *theorem* finset.mem_inter
- \+ *theorem* finset.mem_inter_eq
- \+ *theorem* finset.mem_inter_iff
- \+ *theorem* finset.mem_list_of_mem
- \+ *theorem* finset.mem_of_mem_erase
- \+ *theorem* finset.mem_of_mem_insert_of_ne
- \+ *theorem* finset.mem_of_mem_inter_left
- \+ *theorem* finset.mem_of_mem_inter_right
- \+ *theorem* finset.mem_of_mem_list
- \+ *theorem* finset.mem_of_subset_of_mem
- \+ *theorem* finset.mem_or_mem_of_mem_union
- \+ *theorem* finset.mem_singleton
- \+ *theorem* finset.mem_singleton_iff
- \+ *theorem* finset.mem_singleton_of_eq
- \+ *theorem* finset.mem_to_finset
- \+ *theorem* finset.mem_to_finset_of_nodup
- \+ *theorem* finset.mem_union_eq
- \+ *theorem* finset.mem_union_iff
- \+ *theorem* finset.mem_union_l
- \+ *theorem* finset.mem_union_left
- \+ *theorem* finset.mem_union_r
- \+ *theorem* finset.mem_union_right
- \+ *theorem* finset.mem_upto_eq
- \+ *theorem* finset.mem_upto_iff
- \+ *theorem* finset.mem_upto_of_lt
- \+ *theorem* finset.mem_upto_succ_of_mem_upto
- \+ *lemma* finset.ne_empty_of_card_eq_succ
- \+ *theorem* finset.ne_of_mem_erase
- \+ *theorem* finset.not_mem_empty
- \+ *theorem* finset.not_mem_erase
- \+ *theorem* finset.pair_eq_singleton
- \+ *theorem* finset.perm_insert_cons_of_not_mem
- \+ *theorem* finset.singleton_inter_of_mem
- \+ *theorem* finset.singleton_inter_of_not_mem
- \+ *theorem* finset.singleton_ne_empty
- \+ *theorem* finset.subset.antisymm
- \+ *theorem* finset.subset.refl
- \+ *theorem* finset.subset.trans
- \+ *def* finset.subset
- \+ *def* finset.subset_aux
- \+ *theorem* finset.subset_empty_iff
- \+ *theorem* finset.subset_insert
- \+ *theorem* finset.subset_insert_iff
- \+ *theorem* finset.subset_insert_of_erase_subset
- \+ *theorem* finset.subset_of_forall
- \+ *def* finset.to_finset
- \+ *lemma* finset.to_finset_eq_of_nodup
- \+ *def* finset.to_finset_of_nodup
- \+ *def* finset.union
- \+ *theorem* finset.union_assoc
- \+ *theorem* finset.union_comm
- \+ *theorem* finset.union_distrib_left
- \+ *theorem* finset.union_distrib_right
- \+ *theorem* finset.union_empty
- \+ *theorem* finset.union_left_comm
- \+ *theorem* finset.union_right_comm
- \+ *theorem* finset.union_self
- \+ *def* finset.upto
- \+ *theorem* finset.upto_succ
- \+ *theorem* finset.upto_zero
- \+ *def* finset
- \+ *def* nodup_list
- \+ *def* to_nodup_list
- \+ *def* to_nodup_list_of_nodup

Modified data/list/set.lean
- \+ *theorem* list.length_erase_of_not_mem



## [2017-08-24 13:50:09-04:00](https://github.com/leanprover-community/mathlib/commit/33b22b0)
data/option: add filter
#### Estimated changes
Modified data/option.lean
- \+ *def* option.filter



## [2017-08-24 13:46:34-04:00](https://github.com/leanprover-community/mathlib/commit/4320c41)
chore(*): rename stdlib to mathlib
#### Estimated changes
Modified README.md


Modified leanpkg.toml




## [2017-08-24 13:34:45-04:00](https://github.com/leanprover-community/mathlib/commit/9566a5b)
Merge pull request [#10](https://github.com/leanprover-community/mathlib/pull/10) from johoelzl/repair
rat is order-dense in real; cleanup continuity proof for inv
#### Estimated changes



## [2017-08-23 16:42:36-04:00](https://github.com/leanprover-community/mathlib/commit/963bcad)
rat is order-dense in real; cleanup continuity proof for inv
#### Estimated changes
Modified topology/real.lean
- \- *lemma* closure_of_rat_image_eq
- \+ *lemma* closure_of_rat_image_le_eq
- \+ *lemma* closure_of_rat_image_le_le_eq
- \+ *lemma* exists_pos_of_rat
- \+ *lemma* ge_mem_nhds
- \+ *lemma* le_mem_nhds
- \+ *lemma* mem_zero_nhd_le
- \+/\- *lemma* tendsto_mul_bnd_rat



## [2017-08-23 16:41:48-04:00](https://github.com/leanprover-community/mathlib/commit/d708489)
adapt to Lean changes
#### Estimated changes
Modified theories/set_theory.lean
- \+/\- *def* pSet.resp.eval_val



## [2017-08-22 17:03:16-04:00](https://github.com/leanprover-community/mathlib/commit/3d81768)
fix(data/list/perm): replace broken match with cases proof
#### Estimated changes
Modified data/list/perm.lean




## [2017-08-22 16:36:24-04:00](https://github.com/leanprover-community/mathlib/commit/2780e70)
Adapt to changes in equation compiler:
* Names are not necessary propagated when `rfl` is eliminated on two
  variables. Replace `rfl` by `eq.refl n`.
* it looks like that delta, beta, eta conversion rules are applied later now,
  so some statements of the form `assume <x, (h : t), ...` do not work anymore.
* there is still a problem in `data/list/perm.lean`
#### Estimated changes
Modified data/seq/computation.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified order/filter.lean


Modified theories/set_theory.lean


Modified topology/continuity.lean


Modified topology/real.lean


Modified topology/uniform_space.lean




## [2017-08-18 03:14:49-04:00](https://github.com/leanprover-community/mathlib/commit/c5c5b50)
feat(tactic/rcases): recursive cases (with patterns)
This variant on `cases` (which I hope will eventually replace `cases`) allows the specification of patterns for the `with` clause, composed of anonymous constructors and vertical bars, as in `rcases (t : a ∧ b ∨ c ∧ (d ∨ e)) with ⟨ha, hb⟩ | ⟨hc, hd | he⟩`. As with destructuring `let`, if too many arguments are given to a constructor it is treated as a right-associative nested case, i.e. `⟨ha, hb, hc⟩` becomes `⟨ha, ⟨hb, hc⟩⟩` and `ha | hb | hc` becomes `ha | ⟨hb |  hc⟩`.
#### Estimated changes
Added tactic/default.lean


Added tactic/interactive.lean


Added tactic/rcases.lean
- \+ *def* tactic.rcases_patt.name
- \+ *inductive* tactic.rcases_patt



## [2017-08-16 14:06:45-07:00](https://github.com/leanprover-community/mathlib/commit/fb6bab2)
fix(data/list/perm): pending issues
#### Estimated changes
Modified data/list/perm.lean
- \+ *def* list.perm.decidable_perm
- \+ *def* list.perm.decidable_perm_aux
- \+ *theorem* list.perm.perm_app_cons
- \+ *theorem* list.perm.subset_of_mem_of_subset_of_qeq



## [2017-08-16 14:05:41-07:00](https://github.com/leanprover-community/mathlib/commit/11bcaeb)
refactor(data/lazy_list): lazy_list was moved back to core lib
#### Estimated changes
Deleted data/lazy_list.lean
- \- *def* lazy_list.append
- \- *def* lazy_list.approx
- \- *def* lazy_list.filter
- \- *def* lazy_list.for
- \- *def* lazy_list.head
- \- *def* lazy_list.join
- \- *def* lazy_list.map
- \- *def* lazy_list.map₂
- \- *def* lazy_list.nth
- \- *def* lazy_list.of_list
- \- *def* lazy_list.singleton
- \- *def* lazy_list.tail
- \- *def* lazy_list.to_list
- \- *def* lazy_list.zip
- \- *inductive* lazy_list



## [2017-08-16 13:48:22-07:00](https://github.com/leanprover-community/mathlib/commit/af0b10c)
fix(data/num/basic): vector and bitvec are not in the init folder anymore
#### Estimated changes
Modified data/num/basic.lean




## [2017-08-16 13:47:32-07:00](https://github.com/leanprover-community/mathlib/commit/9b2b11f)
refactor(data): stream library was moved back to core lib
#### Estimated changes
Deleted data/stream.lean
- \- *def* stream.all
- \- *theorem* stream.all_def
- \- *def* stream.any
- \- *theorem* stream.any_def
- \- *theorem* stream.append_append_stream
- \- *theorem* stream.append_approx_drop
- \- *def* stream.append_stream
- \- *theorem* stream.append_stream_head_tail
- \- *def* stream.apply
- \- *def* stream.approx
- \- *theorem* stream.approx_succ
- \- *theorem* stream.approx_zero
- \- *theorem* stream.bisim_simple
- \- *theorem* stream.coinduction
- \- *theorem* stream.composition
- \- *def* stream.cons
- \- *theorem* stream.cons_append_stream
- \- *theorem* stream.cons_nth_inits_core
- \- *def* stream.const
- \- *theorem* stream.const_eq
- \- *def* stream.corec'
- \- *theorem* stream.corec'_eq
- \- *def* stream.corec
- \- *theorem* stream.corec_def
- \- *theorem* stream.corec_eq
- \- *theorem* stream.corec_id_f_eq_iterate
- \- *theorem* stream.corec_id_id_eq_const
- \- *def* stream.corec_on
- \- *def* stream.cycle
- \- *theorem* stream.cycle_eq
- \- *theorem* stream.cycle_singleton
- \- *def* stream.drop
- \- *theorem* stream.drop_append_stream
- \- *theorem* stream.drop_const
- \- *theorem* stream.drop_drop
- \- *theorem* stream.drop_map
- \- *theorem* stream.drop_succ
- \- *theorem* stream.drop_zip
- \- *theorem* stream.eq_of_bisim
- \- *theorem* stream.eq_or_mem_of_mem_cons
- \- *def* stream.even
- \- *theorem* stream.even_cons_cons
- \- *theorem* stream.even_interleave
- \- *theorem* stream.even_tail
- \- *theorem* stream.exists_of_mem_map
- \- *def* stream.head
- \- *theorem* stream.head_cons
- \- *theorem* stream.head_even
- \- *theorem* stream.head_iterate
- \- *theorem* stream.head_map
- \- *theorem* stream.head_zip
- \- *theorem* stream.homomorphism
- \- *theorem* stream.identity
- \- *def* stream.inits
- \- *def* stream.inits_core
- \- *theorem* stream.inits_core_eq
- \- *theorem* stream.inits_eq
- \- *theorem* stream.inits_tail
- \- *theorem* stream.interchange
- \- *def* stream.interleave
- \- *theorem* stream.interleave_eq
- \- *theorem* stream.interleave_even_odd
- \- *theorem* stream.interleave_tail_tail
- \- *def* stream.is_bisimulation
- \- *def* stream.iterate
- \- *theorem* stream.iterate_eq
- \- *theorem* stream.iterate_id
- \- *def* stream.map
- \- *theorem* stream.map_append_stream
- \- *theorem* stream.map_cons
- \- *theorem* stream.map_const
- \- *theorem* stream.map_eq
- \- *theorem* stream.map_eq_apply
- \- *theorem* stream.map_id
- \- *theorem* stream.map_iterate
- \- *theorem* stream.map_map
- \- *theorem* stream.map_tail
- \- *theorem* stream.mem_append_stream_left
- \- *theorem* stream.mem_append_stream_right
- \- *theorem* stream.mem_cons
- \- *theorem* stream.mem_cons_of_mem
- \- *theorem* stream.mem_const
- \- *theorem* stream.mem_cycle
- \- *theorem* stream.mem_interleave_left
- \- *theorem* stream.mem_interleave_right
- \- *theorem* stream.mem_map
- \- *theorem* stream.mem_of_mem_even
- \- *theorem* stream.mem_of_mem_odd
- \- *theorem* stream.mem_of_nth_eq
- \- *def* stream.nats
- \- *theorem* stream.nats_eq
- \- *theorem* stream.nil_append_stream
- \- *def* stream.nth
- \- *theorem* stream.nth_approx
- \- *theorem* stream.nth_const
- \- *theorem* stream.nth_drop
- \- *theorem* stream.nth_even
- \- *theorem* stream.nth_inits
- \- *theorem* stream.nth_interleave_left
- \- *theorem* stream.nth_interleave_right
- \- *theorem* stream.nth_map
- \- *theorem* stream.nth_nats
- \- *theorem* stream.nth_odd
- \- *theorem* stream.nth_of_bisim
- \- *theorem* stream.nth_succ
- \- *theorem* stream.nth_succ_iterate
- \- *theorem* stream.nth_tails
- \- *theorem* stream.nth_unfolds_head_tail
- \- *theorem* stream.nth_zero_cons
- \- *theorem* stream.nth_zero_iterate
- \- *theorem* stream.nth_zip
- \- *def* stream.odd
- \- *theorem* stream.odd_eq
- \- *def* stream.pure
- \- *def* stream.tail
- \- *theorem* stream.tail_cons
- \- *theorem* stream.tail_const
- \- *theorem* stream.tail_drop
- \- *theorem* stream.tail_eq_drop
- \- *theorem* stream.tail_even
- \- *theorem* stream.tail_inits
- \- *theorem* stream.tail_interleave
- \- *theorem* stream.tail_iterate
- \- *theorem* stream.tail_map
- \- *theorem* stream.tail_zip
- \- *def* stream.tails
- \- *theorem* stream.tails_eq
- \- *theorem* stream.tails_eq_iterate
- \- *theorem* stream.take_theorem
- \- *def* stream.unfolds
- \- *theorem* stream.unfolds_eq
- \- *theorem* stream.unfolds_head_eq
- \- *def* stream.zip
- \- *theorem* stream.zip_eq
- \- *theorem* stream.zip_inits_tails
- \- *def* stream



## [2017-08-11 19:03:01-04:00](https://github.com/leanprover-community/mathlib/commit/6d90728)
use Galois connections in filter library
#### Estimated changes
Modified order/filter.lean
- \+ *lemma* filter.gc_map_vmap
- \+/\- *lemma* filter.image_mem_map
- \+/\- *lemma* filter.le_vmap_map
- \+/\- *lemma* filter.map_bot
- \+/\- *lemma* filter.map_compose
- \+/\- *lemma* filter.map_eq_bot_iff
- \+/\- *lemma* filter.map_id
- \+ *lemma* filter.map_le_iff_vmap_le
- \+/\- *lemma* filter.map_map
- \+/\- *lemma* filter.map_mono
- \+/\- *lemma* filter.map_ne_bot
- \+/\- *lemma* filter.map_sup
- \+ *lemma* filter.map_supr
- \+/\- *lemma* filter.map_vmap_le
- \+/\- *lemma* filter.mem_map
- \+/\- *theorem* filter.mem_vmap
- \+/\- *lemma* filter.monotone_map
- \+/\- *lemma* filter.monotone_vmap
- \+/\- *theorem* filter.preimage_mem_vmap
- \- *lemma* filter.supr_map
- \+ *lemma* filter.vmap_id
- \+/\- *lemma* filter.vmap_inf
- \+/\- *lemma* filter.vmap_infi
- \+/\- *lemma* filter.vmap_mono
- \+/\- *theorem* filter.vmap_principal
- \+/\- *lemma* filter.vmap_sup
- \+ *lemma* filter.vmap_top
- \+/\- *lemma* filter.vmap_vmap_comp

Modified topology/topological_space.lean




## [2017-08-11 18:26:35-04:00](https://github.com/leanprover-community/mathlib/commit/ce09c18)
add Galois connection, also add a couple of order theoretic results
#### Estimated changes
Modified order/basic.lean
- \+ *def* preorder_dual

Added order/bounds.lean
- \+ *lemma* eq_of_is_glb_of_is_glb
- \+ *lemma* eq_of_is_greatest_of_is_greatest
- \+ *lemma* eq_of_is_least_of_is_least
- \+ *lemma* eq_of_is_lub_of_is_lub
- \+ *lemma* is_glb_Inf
- \+ *lemma* is_glb_empty
- \+ *lemma* is_glb_iff_Inf_eq
- \+ *lemma* is_glb_iff_eq_of_is_glb
- \+ *lemma* is_glb_iff_inf_eq
- \+ *lemma* is_glb_iff_infi_eq
- \+ *lemma* is_glb_infi
- \+ *lemma* is_glb_insert_inf
- \+ *lemma* is_glb_singleton
- \+ *lemma* is_glb_union_inf
- \+ *lemma* is_greatest_iff_eq_of_is_greatest
- \+ *lemma* is_least_iff_eq_of_is_least
- \+ *lemma* is_lub_Sup
- \+ *lemma* is_lub_empty
- \+ *lemma* is_lub_iff_Sup_eq
- \+ *lemma* is_lub_iff_eq_of_is_lub
- \+ *lemma* is_lub_iff_sup_eq
- \+ *lemma* is_lub_iff_supr_eq
- \+ *lemma* is_lub_insert_sup
- \+ *lemma* is_lub_singleton
- \+ *lemma* is_lub_supr
- \+ *lemma* is_lub_union_sup
- \+ *lemma* mem_lower_bounds_image
- \+ *lemma* mem_upper_bounds_image

Modified order/default.lean


Added order/galois_connection.lean
- \+ *lemma* galois_connection.decreasing_l_u
- \+ *lemma* galois_connection.increasing_u_l
- \+ *lemma* galois_connection.is_glb_l
- \+ *lemma* galois_connection.is_glb_u_image
- \+ *lemma* galois_connection.is_lub_l_image
- \+ *lemma* galois_connection.is_lub_u
- \+ *lemma* galois_connection.l_bot
- \+ *lemma* galois_connection.l_le
- \+ *lemma* galois_connection.l_sup
- \+ *lemma* galois_connection.l_supr
- \+ *lemma* galois_connection.l_u_l_eq_l
- \+ *lemma* galois_connection.le_u
- \+ *lemma* galois_connection.lower_bounds_u_image_subset
- \+ *lemma* galois_connection.monotone_intro
- \+ *lemma* galois_connection.monotone_l
- \+ *lemma* galois_connection.monotone_u
- \+ *lemma* galois_connection.u_inf
- \+ *lemma* galois_connection.u_infi
- \+ *lemma* galois_connection.u_l_u_eq_u
- \+ *lemma* galois_connection.u_top
- \+ *lemma* galois_connection.upper_bounds_l_image_subset
- \+ *def* galois_connection
- \+ *lemma* nat.galois_connection_mul_div



## [2017-08-11 18:14:46-04:00](https://github.com/leanprover-community/mathlib/commit/2e8bd34)
add set.range function
`range` is stronger than `f '' univ`, as `f` can be a function from an arbitrary `Sort` instead of `Type`
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.forall_range_iff
- \+ *lemma* set.mem_range
- \+ *def* set.range
- \+ *lemma* set.range_compose
- \+ *lemma* set.range_id
- \+ *lemma* set.range_of_surjective

Modified order/complete_lattice.lean
- \+/\- *theorem* lattice.Inf_image
- \+ *lemma* lattice.Inf_range
- \+/\- *theorem* lattice.Sup_image
- \+ *lemma* lattice.Sup_range
- \+ *lemma* lattice.infi_range
- \+ *lemma* lattice.supr_range



## [2017-08-11 18:06:23-04:00](https://github.com/leanprover-community/mathlib/commit/e27aae8)
introduce top level dir `order`: move `algebra.order` and content of `algebra.lattice`
#### Estimated changes
Deleted algebra/lattice/README.md


Deleted algebra/lattice/default.lean


Modified data/set/lattice.lean


Renamed algebra/order.lean to order/basic.lean


Renamed algebra/lattice/boolean_algebra.lean to order/boolean_algebra.lean


Renamed algebra/lattice/bounded_lattice.lean to order/bounded_lattice.lean


Renamed algebra/lattice/complete_boolean_algebra.lean to order/complete_boolean_algebra.lean


Renamed algebra/lattice/complete_lattice.lean to order/complete_lattice.lean


Added order/default.lean


Renamed algebra/lattice/filter.lean to order/filter.lean


Renamed algebra/lattice/fixed_points.lean to order/fixed_points.lean


Renamed algebra/lattice/basic.lean to order/lattice.lean


Renamed algebra/lattice/zorn.lean to order/zorn.lean


Modified tactic/converter/binders.lean


Modified topology/real.lean


Modified topology/topological_space.lean


Modified topology/uniform_space.lean




## [2017-08-11 17:57:57-04:00](https://github.com/leanprover-community/mathlib/commit/218c1dd)
algebra/lattice/filter: cleanup move theorems to appropriate places
#### Estimated changes
Modified algebra/lattice/boolean_algebra.lean
- \+ *lemma* lattice.eq_of_sup_eq_inf_eq
- \+ *lemma* lattice.inf_eq_bot_iff_le_compl

Modified algebra/lattice/filter.lean
- \- *lemma* Union_subset_Union2
- \- *lemma* Union_subset_Union
- \- *lemma* Union_subset_Union_const
- \- *lemma* bind_assoc
- \- *lemma* classical.cases
- \- *lemma* compl_image_set_of
- \- *lemma* diff_empty
- \- *lemma* diff_neq_empty
- \- *lemma* eq_of_sup_eq_inf_eq
- \- *lemma* false_neq_true
- \- *lemma* implies_implies_true_iff
- \- *lemma* inf_eq_bot_iff_le_compl
- \- *lemma* map_bind
- \- *lemma* neg_subset_neg_iff_subset
- \- *lemma* not_not_mem_iff
- \- *lemma* not_or_iff_implies
- \- *lemma* prod.fst_swap
- \- *lemma* prod.mk.eta
- \- *lemma* prod.snd_swap
- \- *def* prod.swap
- \- *lemma* prod.swap_prod_mk
- \- *lemma* prod.swap_swap
- \- *lemma* prod.swap_swap_eq
- \- *lemma* pure_seq_eq_map
- \- *lemma* sUnion_eq_Union
- \- *lemma* sUnion_mono
- \- *lemma* seq_bind_eq
- \- *lemma* seq_eq_bind_map
- \- *lemma* set.bind_def
- \- *lemma* set.diff_right_antimono
- \- *lemma* set.fmap_eq_image
- \- *lemma* set.image_Union
- \- *lemma* set.image_inter
- \- *lemma* set.image_singleton
- \- *theorem* set.image_swap_eq_preimage_swap
- \- *lemma* set.image_swap_prod
- \- *lemma* set.mem_prod_eq
- \- *lemma* set.mem_seq_iff
- \- *theorem* set.monotone_prod
- \- *lemma* set.ne_empty_iff_exists_mem
- \- *lemma* set.not_eq_empty_iff_exists
- \- *theorem* set.preimage_set_of_eq
- \- *lemma* set.prod_image_image_eq
- \- *lemma* set.prod_inter_prod
- \- *lemma* set.prod_mk_mem_set_prod_eq
- \- *lemma* set.prod_mono
- \- *lemma* set.prod_neq_empty_iff
- \- *theorem* set.prod_preimage_eq
- \- *lemma* set.prod_singleton_singleton
- \- *lemma* set.set_of_mem_eq
- \- *lemma* set.univ_eq_true_false
- \- *lemma* singleton_neq_emptyset

Added category/basic.lean
- \+ *lemma* bind_assoc
- \+ *lemma* map_bind
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* seq_bind_eq
- \+ *lemma* seq_eq_bind_map

Added data/prod.lean
- \+ *lemma* prod.fst_swap
- \+ *lemma* prod.mk.eta
- \+ *lemma* prod.snd_swap
- \+ *def* prod.swap
- \+ *lemma* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap
- \+ *lemma* prod.swap_swap_eq

Modified data/set/basic.lean
- \+ *lemma* set.compl_image_set_of
- \+ *lemma* set.compl_subset_of_compl_subset
- \+ *lemma* set.diff_empty
- \+ *lemma* set.diff_neq_empty
- \+ *lemma* set.diff_right_antimono
- \+ *lemma* set.diff_subset_diff
- \+ *lemma* set.image_inter
- \+ *lemma* set.image_singleton
- \+ *lemma* set.mem_of_mem_of_subset
- \+ *lemma* set.ne_empty_iff_exists_mem
- \+ *lemma* set.not_eq_empty_iff_exists
- \+ *lemma* set.not_not_mem_iff
- \+ *theorem* set.preimage_set_of_eq
- \+ *lemma* set.set_of_mem_eq
- \+/\- *theorem* set.singleton_ne_empty
- \+ *lemma* set.univ_eq_true_false

Modified data/set/default.lean


Modified data/set/lattice.lean
- \+ *lemma* set.Union_subset_Union2
- \+ *lemma* set.Union_subset_Union
- \+ *lemma* set.Union_subset_Union_const
- \+ *lemma* set.bind_def
- \+ *lemma* set.compl_subset_compl_iff_subset
- \+ *lemma* set.fmap_eq_image
- \+ *lemma* set.image_Union
- \+ *lemma* set.mem_seq_iff
- \+ *lemma* set.sUnion_eq_Union
- \+ *lemma* set.sUnion_mono
- \+ *lemma* set.univ_subtype

Added data/set/prod.lean
- \+ *theorem* set.image_swap_eq_preimage_swap
- \+ *lemma* set.image_swap_prod
- \+ *lemma* set.mem_prod_eq
- \+ *theorem* set.monotone_prod
- \+ *lemma* set.prod_image_image_eq
- \+ *lemma* set.prod_inter_prod
- \+ *lemma* set.prod_mk_mem_set_prod_eq
- \+ *lemma* set.prod_mono
- \+ *lemma* set.prod_neq_empty_iff
- \+ *theorem* set.prod_preimage_eq
- \+ *lemma* set.prod_singleton_singleton

Modified logic/basic.lean
- \+ *lemma* classical.cases
- \+ *lemma* false_neq_true
- \+ *theorem* not_and_iff_imp_not
- \+ *lemma* {u

Modified topology/topological_space.lean
- \- *lemma* compl_subset_of_compl_subset
- \- *lemma* diff_subset_diff
- \- *lemma* mem_of_mem_of_subset
- \- *lemma* not_and_iff_imp_not
- \- *lemma* univ_subtype

Modified topology/uniform_space.lean




## [2017-08-10 16:50:12-04:00](https://github.com/leanprover-community/mathlib/commit/178e746)
rename towards -> tendsto
#### Estimated changes
Modified algebra/lattice/filter.lean
- \+ *def* filter.tendsto
- \+ *lemma* filter.tendsto_compose
- \+ *lemma* filter.tendsto_cong
- \+ *lemma* filter.tendsto_fst
- \+ *lemma* filter.tendsto_id'
- \+ *lemma* filter.tendsto_id
- \+ *lemma* filter.tendsto_inf
- \+ *lemma* filter.tendsto_map'
- \+ *lemma* filter.tendsto_map
- \+ *lemma* filter.tendsto_prod_mk
- \+ *lemma* filter.tendsto_snd
- \+ *lemma* filter.tendsto_vmap''
- \+ *lemma* filter.tendsto_vmap'
- \+ *lemma* filter.tendsto_vmap
- \- *def* filter.towards
- \- *lemma* filter.towards_compose
- \- *lemma* filter.towards_cong
- \- *lemma* filter.towards_fst
- \- *lemma* filter.towards_id'
- \- *lemma* filter.towards_id
- \- *lemma* filter.towards_inf
- \- *lemma* filter.towards_map'
- \- *lemma* filter.towards_map
- \- *lemma* filter.towards_prod_mk
- \- *lemma* filter.towards_snd
- \- *lemma* filter.towards_vmap''
- \- *lemma* filter.towards_vmap'
- \- *lemma* filter.towards_vmap

Modified topology/continuity.lean
- \+ *lemma* continuous_iff_tendsto
- \- *lemma* continuous_iff_towards
- \+ *lemma* dense_embedding.tendsto_ext
- \- *lemma* dense_embedding.towards_ext
- \+ *lemma* tendsto_nhds_iff_of_embedding
- \- *lemma* towards_nhds_iff_of_embedding

Modified topology/real.lean
- \+/\- *lemma* lift_rat_fun_of_rat
- \+/\- *lemma* of_rat_add
- \+/\- *lemma* of_rat_inv
- \+/\- *lemma* of_rat_mul
- \+/\- *lemma* of_rat_neg
- \+/\- *lemma* of_rat_one
- \+/\- *lemma* of_rat_sub
- \+/\- *lemma* of_rat_zero
- \+ *lemma* tendsto_add_rat
- \+ *lemma* tendsto_add_rat_zero'
- \+ *lemma* tendsto_add_rat_zero
- \+ *lemma* tendsto_inv_pos_rat
- \+ *lemma* tendsto_inv_rat
- \+ *lemma* tendsto_inv_real
- \+ *lemma* tendsto_mul_bnd_rat'
- \+ *lemma* tendsto_mul_bnd_rat
- \+ *lemma* tendsto_mul_rat'
- \+ *lemma* tendsto_mul_rat
- \+ *lemma* tendsto_neg_rat
- \+ *lemma* tendsto_neg_rat_zero
- \+ *lemma* tendsto_of_uniform_continuous_subtype
- \+ *lemma* tendsto_sub_rat'
- \+ *lemma* tendsto_sub_uniformity_zero_nhd'
- \+ *lemma* tendsto_sub_uniformity_zero_nhd
- \+ *lemma* tendsto_zero_nhds
- \- *lemma* towards_add_rat
- \- *lemma* towards_add_rat_zero'
- \- *lemma* towards_add_rat_zero
- \- *lemma* towards_inv_pos_rat
- \- *lemma* towards_inv_rat
- \- *lemma* towards_inv_real
- \- *lemma* towards_mul_bnd_rat'
- \- *lemma* towards_mul_bnd_rat
- \- *lemma* towards_mul_rat'
- \- *lemma* towards_mul_rat
- \- *lemma* towards_neg_rat
- \- *lemma* towards_neg_rat_zero
- \- *lemma* towards_of_uniform_continuous_subtype
- \- *lemma* towards_sub_rat'
- \- *lemma* towards_sub_uniformity_zero_nhd'
- \- *lemma* towards_sub_uniformity_zero_nhd
- \- *lemma* towards_zero_nhds

Modified topology/topological_space.lean
- \+ *lemma* tendsto_const_nhds
- \+ *lemma* tendsto_nhds
- \+ *lemma* tendsto_nhds_unique
- \- *lemma* towards_const_nhds
- \- *lemma* towards_nhds
- \- *lemma* towards_nhds_unique

Modified topology/uniform_space.lean
- \+ *lemma* tendsto_const_uniformity
- \+ *lemma* tendsto_left_nhds_uniformity
- \+ *lemma* tendsto_prod_uniformity_fst
- \+ *lemma* tendsto_prod_uniformity_snd
- \+ *lemma* tendsto_right_nhds_uniformity
- \+ *lemma* tendsto_swap_uniformity
- \- *lemma* towards_const_uniformity
- \- *lemma* towards_left_nhds_uniformity
- \- *lemma* towards_prod_uniformity_fst
- \- *lemma* towards_prod_uniformity_snd
- \- *lemma* towards_right_nhds_uniformity
- \- *lemma* towards_swap_uniformity



## [2017-08-10 16:41:03-04:00](https://github.com/leanprover-community/mathlib/commit/2ac1f20)
rename open -> is_open, closed -> is_closed
#### Estimated changes
Modified topology/continuity.lean
- \- *lemma* closed_diagonal
- \- *lemma* closed_eq
- \- *lemma* closed_prod
- \- *lemma* closed_property2
- \- *lemma* closed_property3
- \- *lemma* closed_property
- \+/\- *def* continuous
- \+/\- *lemma* continuous_Prop
- \- *lemma* continuous_iff_closed
- \+ *lemma* continuous_iff_is_closed
- \- *lemma* continuous_subtype_closed_cover
- \+ *lemma* continuous_subtype_is_closed_cover
- \- *lemma* embedding_closed
- \+ *lemma* embedding_is_closed
- \+ *lemma* is_closed_diagonal
- \+ *lemma* is_closed_eq
- \+ *lemma* is_closed_prod
- \+ *lemma* is_closed_property2
- \+ *lemma* is_closed_property3
- \+ *lemma* is_closed_property
- \+ *theorem* is_open_induced
- \+ *lemma* is_open_set_prod
- \+ *lemma* is_open_singleton_true
- \- *theorem* open_induced
- \- *lemma* open_set_prod
- \- *lemma* open_singleton_true

Modified topology/real.lean
- \- *lemma* closed_ge
- \- *lemma* closed_imp
- \- *lemma* closed_le
- \- *lemma* closed_le_real
- \+ *lemma* is_closed_ge
- \+ *lemma* is_closed_imp
- \+ *lemma* is_closed_le
- \+ *lemma* is_closed_le_real
- \+ *lemma* is_open_gt
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_lt_real
- \- *lemma* open_gt
- \- *lemma* open_lt
- \- *lemma* open_lt_real

Modified topology/topological_space.lean
- \- *def* closed
- \- *lemma* closed_Inter
- \- *lemma* closed_Union
- \- *lemma* closed_Union_of_locally_finite
- \- *lemma* closed_closure
- \- *lemma* closed_compl_iff
- \- *lemma* closed_empty
- \- *lemma* closed_iff_nhds
- \- *lemma* closed_induced_iff
- \- *lemma* closed_inter
- \- *lemma* closed_sInter
- \- *lemma* closed_singleton
- \- *lemma* closed_union
- \- *lemma* closed_univ
- \+/\- *def* closure
- \- *lemma* closure_eq_iff_closed
- \+ *lemma* closure_eq_iff_is_closed
- \- *lemma* closure_eq_of_closed
- \+ *lemma* closure_eq_of_is_closed
- \+/\- *lemma* closure_inter_open
- \+/\- *lemma* closure_minimal
- \- *lemma* closure_subset_iff_subset_of_closed
- \+ *lemma* closure_subset_iff_subset_of_is_closed
- \- *lemma* compact_of_closed_subset
- \+ *lemma* compact_of_is_closed_subset
- \+/\- *lemma* generate_from_le
- \+/\- *def* interior
- \+/\- *lemma* interior_eq_iff_open
- \+/\- *lemma* interior_eq_of_open
- \+/\- *lemma* interior_maximal
- \- *lemma* interior_union_closed_of_interior_empty
- \+ *lemma* interior_union_is_closed_of_interior_empty
- \+ *def* is_closed
- \+ *lemma* is_closed_Inter
- \+ *lemma* is_closed_Union
- \+ *lemma* is_closed_Union_of_locally_finite
- \+ *lemma* is_closed_closure
- \+ *lemma* is_closed_compl_iff
- \+ *lemma* is_closed_empty
- \+ *lemma* is_closed_iff_nhds
- \+ *lemma* is_closed_induced_iff
- \+ *lemma* is_closed_inter
- \+ *lemma* is_closed_sInter
- \+ *lemma* is_closed_singleton
- \+ *lemma* is_closed_union
- \+ *lemma* is_closed_univ
- \+ *def* is_open
- \+ *lemma* is_open_Union
- \+ *lemma* is_open_compl_iff
- \+ *lemma* is_open_diff
- \+ *lemma* is_open_empty
- \+ *lemma* is_open_iff_nhds
- \+ *lemma* is_open_inter
- \+ *lemma* is_open_interior
- \+ *lemma* is_open_sUnion
- \+ *lemma* is_open_union
- \+ *lemma* is_open_univ
- \+/\- *lemma* mem_nhds_sets
- \+/\- *def* nhds
- \- *lemma* nhds_closed
- \+ *lemma* nhds_is_closed
- \+/\- *lemma* nhds_sets
- \- *def* open'
- \- *lemma* open_Union
- \- *lemma* open_compl_iff
- \- *lemma* open_diff
- \- *lemma* open_empty
- \- *lemma* open_iff_nhds
- \- *lemma* open_inter
- \- *lemma* open_interior
- \- *lemma* open_sUnion
- \- *lemma* open_union
- \- *lemma* open_univ
- \+/\- *lemma* subset_interior_iff_subset_of_open
- \+/\- *lemma* topological_space_eq
- \+/\- *lemma* towards_nhds

Modified topology/uniform_space.lean
- \- *lemma* compact_of_totally_bounded_closed
- \+ *lemma* compact_of_totally_bounded_is_closed
- \- *lemma* complete_of_closed
- \+ *lemma* complete_of_is_closed
- \+ *lemma* is_open_uniformity
- \- *lemma* mem_uniformity_closed
- \+ *lemma* mem_uniformity_is_closed
- \- *lemma* open_uniformity



## [2017-08-10 16:36:59-04:00](https://github.com/leanprover-community/mathlib/commit/7882677)
construct reals as complete, linear ordered field
#### Estimated changes
Added algebra/field.lean
- \+ *lemma* abs_inv
- \+ *lemma* div_le_iff_le_mul_of_pos
- \+ *lemma* inv_neg
- \+ *lemma* inv_sub_inv_eq
- \+ *lemma* ivl_stretch
- \+ *lemma* ivl_translate
- \+ *lemma* le_div_iff_mul_le_of_pos
- \+ *lemma* lt_div_iff

Modified algebra/group.lean
- \+ *lemma* abs_le_iff
- \+ *lemma* le_sub_iff_add_le
- \+ *lemma* sub_le_iff_le_add

Modified algebra/lattice/complete_lattice.lean
- \+ *def* ord_continuous
- \+ *lemma* ord_continuous_mono
- \+ *lemma* ord_continuous_sup

Modified algebra/lattice/filter.lean
- \+ *lemma* Union_subset_Union2
- \- *theorem* Union_subset_Union2
- \+ *lemma* Union_subset_Union
- \- *theorem* Union_subset_Union
- \+ *lemma* Union_subset_Union_const
- \- *theorem* Union_subset_Union_const
- \+ *lemma* bind_assoc
- \- *theorem* bind_assoc
- \+ *lemma* classical.cases
- \+ *lemma* compl_image_set_of
- \- *theorem* compl_image_set_of
- \+ *lemma* diff_empty
- \- *theorem* diff_empty
- \+ *lemma* diff_neq_empty
- \- *theorem* diff_neq_empty
- \+ *lemma* directed_on_Union
- \- *theorem* directed_on_Union
- \+ *lemma* eq_of_sup_eq_inf_eq
- \- *theorem* eq_of_sup_eq_inf_eq
- \+ *lemma* false_neq_true
- \+ *lemma* filter.Inf_sets_eq_finite
- \- *theorem* filter.Inf_sets_eq_finite
- \+ *lemma* filter.Inter_mem_sets
- \- *theorem* filter.Inter_mem_sets
- \+ *lemma* filter.bind_def
- \- *theorem* filter.bind_def
- \+ *lemma* filter.bind_mono2
- \- *theorem* filter.bind_mono2
- \+ *lemma* filter.bind_mono
- \- *theorem* filter.bind_mono
- \+ *lemma* filter.bind_sup
- \- *theorem* filter.bind_sup
- \+ *lemma* filter.binfi_sup_eq
- \- *theorem* filter.binfi_sup_eq
- \+ *lemma* filter.empty_in_sets_eq_bot
- \- *theorem* filter.empty_in_sets_eq_bot
- \+ *lemma* filter.exists_sets_subset_iff
- \- *theorem* filter.exists_sets_subset_iff
- \+ *lemma* filter.exists_ultrafilter
- \- *theorem* filter.exists_ultrafilter
- \+ *lemma* filter.filter_eq
- \- *theorem* filter.filter_eq
- \+ *lemma* filter.filter_eq_bot_of_not_nonempty
- \- *theorem* filter.filter_eq_bot_of_not_nonempty
- \+ *lemma* filter.fmap_principal
- \- *theorem* filter.fmap_principal
- \+ *lemma* filter.forall_sets_neq_empty_iff_neq_bot
- \- *theorem* filter.forall_sets_neq_empty_iff_neq_bot
- \+ *lemma* filter.image_mem_map
- \- *theorem* filter.image_mem_map
- \+ *lemma* filter.inf_principal
- \- *theorem* filter.inf_principal
- \+ *lemma* filter.infi_neq_bot_iff_of_directed
- \- *theorem* filter.infi_neq_bot_iff_of_directed
- \+ *lemma* filter.infi_neq_bot_of_directed
- \- *theorem* filter.infi_neq_bot_of_directed
- \+ *lemma* filter.infi_sets_eq'
- \- *theorem* filter.infi_sets_eq'
- \+ *lemma* filter.infi_sets_eq
- \- *theorem* filter.infi_sets_eq
- \+ *lemma* filter.infi_sets_induct
- \- *theorem* filter.infi_sets_induct
- \+ *lemma* filter.infi_sup_eq
- \- *theorem* filter.infi_sup_eq
- \+ *lemma* filter.inhabited_of_mem_sets
- \- *theorem* filter.inhabited_of_mem_sets
- \+ *lemma* filter.inter_mem_inf_sets
- \+ *lemma* filter.inter_mem_sets
- \- *theorem* filter.inter_mem_sets
- \+ *lemma* filter.join_principal_eq_Sup
- \- *theorem* filter.join_principal_eq_Sup
- \+ *lemma* filter.le_lift'
- \- *theorem* filter.le_lift'
- \+ *lemma* filter.le_map_vmap'
- \+ *lemma* filter.le_map_vmap
- \- *theorem* filter.le_map_vmap
- \+ *lemma* filter.le_of_ultrafilter
- \- *theorem* filter.le_of_ultrafilter
- \+ *lemma* filter.le_principal_iff
- \- *theorem* filter.le_principal_iff
- \+ *lemma* filter.le_vmap_iff_map_le
- \- *theorem* filter.le_vmap_iff_map_le
- \+ *lemma* filter.le_vmap_map
- \- *theorem* filter.le_vmap_map
- \+ *lemma* filter.lift'_cong
- \- *theorem* filter.lift'_cong
- \+ *lemma* filter.lift'_id
- \- *theorem* filter.lift'_id
- \+ *lemma* filter.lift'_inf_principal_eq
- \- *theorem* filter.lift'_inf_principal_eq
- \+ *lemma* filter.lift'_infi
- \- *theorem* filter.lift'_infi
- \+ *lemma* filter.lift'_le
- \+ *lemma* filter.lift'_lift'_assoc
- \- *theorem* filter.lift'_lift'_assoc
- \+ *lemma* filter.lift'_lift_assoc
- \- *theorem* filter.lift'_lift_assoc
- \+ *lemma* filter.lift'_mono'
- \- *theorem* filter.lift'_mono'
- \+ *lemma* filter.lift'_mono
- \- *theorem* filter.lift'_mono
- \+ *lemma* filter.lift'_neq_bot_iff
- \- *theorem* filter.lift'_neq_bot_iff
- \+ *lemma* filter.lift'_principal
- \- *theorem* filter.lift'_principal
- \+ *lemma* filter.lift_assoc
- \- *theorem* filter.lift_assoc
- \+ *lemma* filter.lift_comm
- \- *theorem* filter.lift_comm
- \+ *lemma* filter.lift_infi'
- \- *theorem* filter.lift_infi'
- \+ *lemma* filter.lift_infi
- \- *theorem* filter.lift_infi
- \+ *lemma* filter.lift_le
- \+ *lemma* filter.lift_lift'_assoc
- \- *theorem* filter.lift_lift'_assoc
- \+ *lemma* filter.lift_lift'_same_eq_lift'
- \- *theorem* filter.lift_lift'_same_eq_lift'
- \+ *lemma* filter.lift_lift'_same_le_lift'
- \- *theorem* filter.lift_lift'_same_le_lift'
- \+ *lemma* filter.lift_lift_same_eq_lift
- \- *theorem* filter.lift_lift_same_eq_lift
- \+ *lemma* filter.lift_lift_same_le_lift
- \- *theorem* filter.lift_lift_same_le_lift
- \+ *lemma* filter.lift_mono'
- \- *theorem* filter.lift_mono'
- \+ *lemma* filter.lift_mono
- \- *theorem* filter.lift_mono
- \+ *lemma* filter.lift_neq_bot_iff
- \- *theorem* filter.lift_neq_bot_iff
- \+ *lemma* filter.lift_principal
- \- *theorem* filter.lift_principal
- \+ *lemma* filter.lift_sets_eq
- \- *theorem* filter.lift_sets_eq
- \+ *lemma* filter.map_binfi_eq
- \- *theorem* filter.map_binfi_eq
- \+ *lemma* filter.map_bot
- \- *theorem* filter.map_bot
- \+ *lemma* filter.map_compose
- \- *theorem* filter.map_compose
- \+ *lemma* filter.map_cong
- \+ *lemma* filter.map_eq_bot_iff
- \- *theorem* filter.map_eq_bot_iff
- \+ *lemma* filter.map_eq_vmap_of_inverse
- \- *theorem* filter.map_eq_vmap_of_inverse
- \+ *lemma* filter.map_id
- \- *theorem* filter.map_id
- \+ *lemma* filter.map_inf
- \+ *lemma* filter.map_infi_eq
- \- *theorem* filter.map_infi_eq
- \+ *lemma* filter.map_infi_le
- \- *theorem* filter.map_infi_le
- \+ *lemma* filter.map_inj
- \+ *lemma* filter.map_lift'_eq2
- \- *theorem* filter.map_lift'_eq2
- \+ *lemma* filter.map_lift'_eq
- \- *theorem* filter.map_lift'_eq
- \+ *lemma* filter.map_lift_eq2
- \- *theorem* filter.map_lift_eq2
- \+ *lemma* filter.map_lift_eq
- \- *theorem* filter.map_lift_eq
- \+ *lemma* filter.map_map
- \+ *lemma* filter.map_mono
- \- *theorem* filter.map_mono
- \+ *lemma* filter.map_ne_bot
- \+ *lemma* filter.map_principal
- \- *theorem* filter.map_principal
- \+ *lemma* filter.map_sup
- \- *theorem* filter.map_sup
- \+ *lemma* filter.map_swap_vmap_swap_eq
- \- *theorem* filter.map_swap_vmap_swap_eq
- \+ *lemma* filter.map_vmap_le
- \- *theorem* filter.map_vmap_le
- \+ *lemma* filter.mem_bind_sets
- \- *theorem* filter.mem_bind_sets
- \+ *lemma* filter.mem_bot_sets
- \- *theorem* filter.mem_bot_sets
- \+ *lemma* filter.mem_inf_sets
- \- *theorem* filter.mem_inf_sets
- \+ *lemma* filter.mem_inf_sets_of_left
- \- *theorem* filter.mem_inf_sets_of_left
- \+ *lemma* filter.mem_inf_sets_of_right
- \- *theorem* filter.mem_inf_sets_of_right
- \+ *lemma* filter.mem_infi_sets
- \- *theorem* filter.mem_infi_sets
- \+ *lemma* filter.mem_join_sets
- \- *theorem* filter.mem_join_sets
- \+ *lemma* filter.mem_lift'
- \- *theorem* filter.mem_lift'
- \+ *lemma* filter.mem_lift'_iff
- \- *theorem* filter.mem_lift'_iff
- \+ *lemma* filter.mem_lift
- \- *theorem* filter.mem_lift
- \+ *lemma* filter.mem_lift_iff
- \- *theorem* filter.mem_lift_iff
- \+ *lemma* filter.mem_map
- \- *theorem* filter.mem_map
- \+ *lemma* filter.mem_of_finite_Union_ultrafilter
- \- *theorem* filter.mem_of_finite_Union_ultrafilter
- \+ *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \- *theorem* filter.mem_of_finite_sUnion_ultrafilter
- \+ *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \- *theorem* filter.mem_or_compl_mem_of_ultrafilter
- \+ *lemma* filter.mem_or_mem_of_ultrafilter
- \- *theorem* filter.mem_or_mem_of_ultrafilter
- \+ *lemma* filter.mem_principal_sets
- \- *theorem* filter.mem_principal_sets
- \+ *lemma* filter.mem_prod_iff
- \- *theorem* filter.mem_prod_iff
- \+ *lemma* filter.mem_prod_same_iff
- \- *theorem* filter.mem_prod_same_iff
- \+ *lemma* filter.mem_pure
- \- *theorem* filter.mem_pure
- \+ *lemma* filter.mem_return_sets
- \- *theorem* filter.mem_return_sets
- \+ *lemma* filter.mem_sets_of_neq_bot
- \- *theorem* filter.mem_sets_of_neq_bot
- \+ *lemma* filter.mem_sup_sets
- \- *theorem* filter.mem_sup_sets
- \+ *lemma* filter.mem_top_sets_iff
- \- *theorem* filter.mem_top_sets_iff
- \+ *theorem* filter.mem_vmap
- \- *theorem* filter.mem_vmap_of_mem
- \+ *lemma* filter.monotone_map
- \- *theorem* filter.monotone_map
- \+ *lemma* filter.monotone_mem_sets
- \- *theorem* filter.monotone_mem_sets
- \+ *lemma* filter.monotone_principal
- \- *theorem* filter.monotone_principal
- \+ *lemma* filter.monotone_vmap
- \- *theorem* filter.monotone_vmap
- \+/\- *theorem* filter.preimage_mem_vmap
- \+ *lemma* filter.principal_bind
- \- *theorem* filter.principal_bind
- \+ *lemma* filter.principal_empty
- \- *theorem* filter.principal_empty
- \+ *lemma* filter.principal_eq_bot_iff
- \- *theorem* filter.principal_eq_bot_iff
- \+ *lemma* filter.principal_eq_iff_eq
- \- *theorem* filter.principal_eq_iff_eq
- \+ *lemma* filter.principal_le_lift'
- \- *theorem* filter.principal_le_lift'
- \+ *lemma* filter.principal_mono
- \- *theorem* filter.principal_mono
- \+ *lemma* filter.principal_univ
- \- *theorem* filter.principal_univ
- \+ *lemma* filter.prod_comm
- \- *theorem* filter.prod_comm
- \+ *lemma* filter.prod_inf_prod
- \- *theorem* filter.prod_inf_prod
- \+ *lemma* filter.prod_lift'_lift'
- \- *theorem* filter.prod_lift'_lift'
- \+ *lemma* filter.prod_lift_lift
- \- *theorem* filter.prod_lift_lift
- \+ *lemma* filter.prod_map_map_eq
- \- *theorem* filter.prod_map_map_eq
- \+ *lemma* filter.prod_mem_prod
- \- *theorem* filter.prod_mem_prod
- \+ *lemma* filter.prod_mono
- \- *theorem* filter.prod_mono
- \+ *lemma* filter.prod_neq_bot
- \- *theorem* filter.prod_neq_bot
- \+ *lemma* filter.prod_principal_principal
- \- *theorem* filter.prod_principal_principal
- \+ *lemma* filter.prod_same_eq
- \- *theorem* filter.prod_same_eq
- \+ *lemma* filter.prod_vmap_vmap_eq
- \- *theorem* filter.prod_vmap_vmap_eq
- \+ *lemma* filter.pure_def
- \- *theorem* filter.pure_def
- \+ *lemma* filter.return_neq_bot
- \- *theorem* filter.return_neq_bot
- \+ *lemma* filter.seq_mono
- \- *theorem* filter.seq_mono
- \+ *lemma* filter.sup_join
- \- *theorem* filter.sup_join
- \+ *lemma* filter.sup_principal
- \- *theorem* filter.sup_principal
- \+ *lemma* filter.supr_join
- \- *theorem* filter.supr_join
- \+ *lemma* filter.supr_map
- \- *theorem* filter.supr_map
- \+ *lemma* filter.supr_principal
- \- *theorem* filter.supr_principal
- \+ *lemma* filter.supr_sets_eq
- \- *theorem* filter.supr_sets_eq
- \+ *lemma* filter.towards_compose
- \+ *lemma* filter.towards_cong
- \+ *lemma* filter.towards_fst
- \+ *lemma* filter.towards_id'
- \+ *lemma* filter.towards_id
- \+ *lemma* filter.towards_inf
- \+ *lemma* filter.towards_map'
- \+ *lemma* filter.towards_map
- \+ *lemma* filter.towards_prod_mk
- \+ *lemma* filter.towards_snd
- \+ *lemma* filter.towards_vmap''
- \+ *lemma* filter.towards_vmap'
- \+ *lemma* filter.towards_vmap
- \+ *lemma* filter.ultrafilter_map
- \- *theorem* filter.ultrafilter_map
- \+ *lemma* filter.ultrafilter_of_le
- \- *theorem* filter.ultrafilter_of_le
- \+ *lemma* filter.ultrafilter_of_spec
- \- *theorem* filter.ultrafilter_of_spec
- \+ *lemma* filter.ultrafilter_of_split
- \- *theorem* filter.ultrafilter_of_split
- \+ *lemma* filter.ultrafilter_of_ultrafilter
- \- *theorem* filter.ultrafilter_of_ultrafilter
- \+ *lemma* filter.ultrafilter_pure
- \- *theorem* filter.ultrafilter_pure
- \+ *lemma* filter.ultrafilter_ultrafilter_of
- \- *theorem* filter.ultrafilter_ultrafilter_of
- \+ *lemma* filter.ultrafilter_unique
- \- *theorem* filter.ultrafilter_unique
- \+ *lemma* filter.univ_mem_sets'
- \- *theorem* filter.univ_mem_sets'
- \+ *lemma* filter.univ_mem_sets
- \- *theorem* filter.univ_mem_sets
- \+ *lemma* filter.vmap_bot
- \+ *lemma* filter.vmap_inf
- \+ *lemma* filter.vmap_infi
- \+ *lemma* filter.vmap_lift_eq
- \- *theorem* filter.vmap_lift_eq
- \+ *lemma* filter.vmap_map
- \- *theorem* filter.vmap_map
- \+ *lemma* filter.vmap_mono
- \- *theorem* filter.vmap_mono
- \+ *lemma* filter.vmap_neq_bot
- \- *theorem* filter.vmap_neq_bot
- \+ *lemma* filter.vmap_neq_bot_of_surj
- \- *theorem* filter.vmap_neq_bot_of_surj
- \+ *lemma* filter.vmap_sup
- \+ *lemma* filter.vmap_vmap_comp
- \- *theorem* filter.vmap_vmap_comp
- \+ *lemma* implies_implies_true_iff
- \- *theorem* implies_implies_true_iff
- \+ *lemma* inf_eq_bot_iff_le_compl
- \- *theorem* inf_eq_bot_iff_le_compl
- \+ *lemma* lattice.Inf_eq_finite_sets
- \- *theorem* lattice.Inf_eq_finite_sets
- \+ *lemma* map_bind
- \- *theorem* map_bind
- \+ *lemma* neg_subset_neg_iff_subset
- \- *theorem* neg_subset_neg_iff_subset
- \+ *lemma* not_not_mem_iff
- \- *theorem* not_not_mem_iff
- \+ *lemma* not_or_iff_implies
- \+ *lemma* prod.fst_swap
- \- *theorem* prod.fst_swap
- \+ *lemma* prod.mk.eta
- \- *theorem* prod.mk.eta
- \+ *lemma* prod.snd_swap
- \- *theorem* prod.snd_swap
- \+ *lemma* prod.swap_prod_mk
- \- *theorem* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap
- \- *theorem* prod.swap_swap
- \+ *lemma* prod.swap_swap_eq
- \- *theorem* prod.swap_swap_eq
- \+ *lemma* pure_seq_eq_map
- \- *theorem* pure_seq_eq_map
- \+ *lemma* sUnion_eq_Union
- \- *theorem* sUnion_eq_Union
- \+ *lemma* sUnion_mono
- \- *theorem* sUnion_mono
- \+ *lemma* seq_bind_eq
- \- *theorem* seq_bind_eq
- \+ *lemma* seq_eq_bind_map
- \- *theorem* seq_eq_bind_map
- \+ *lemma* set.bind_def
- \- *theorem* set.bind_def
- \+ *lemma* set.diff_right_antimono
- \- *theorem* set.diff_right_antimono
- \+ *lemma* set.fmap_eq_image
- \- *theorem* set.fmap_eq_image
- \+ *lemma* set.image_Union
- \- *theorem* set.image_eq_preimage_of_inverse
- \+ *lemma* set.image_inter
- \+ *lemma* set.image_singleton
- \+ *lemma* set.image_swap_prod
- \- *theorem* set.image_swap_prod
- \- *theorem* set.mem_image_iff_of_inverse
- \+ *lemma* set.mem_prod_eq
- \- *theorem* set.mem_prod_eq
- \+ *lemma* set.mem_seq_iff
- \- *theorem* set.mem_seq_iff
- \+ *lemma* set.ne_empty_iff_exists_mem
- \- *theorem* set.ne_empty_iff_exists_mem
- \+ *lemma* set.not_eq_empty_iff_exists
- \+ *lemma* set.prod_image_image_eq
- \- *theorem* set.prod_image_image_eq
- \+ *lemma* set.prod_inter_prod
- \- *theorem* set.prod_inter_prod
- \+ *lemma* set.prod_mk_mem_set_prod_eq
- \- *theorem* set.prod_mk_mem_set_prod_eq
- \+ *lemma* set.prod_mono
- \- *theorem* set.prod_mono
- \+ *lemma* set.prod_neq_empty_iff
- \- *theorem* set.prod_neq_empty_iff
- \+ *lemma* set.prod_singleton_singleton
- \- *theorem* set.prod_singleton_singleton
- \+ *lemma* set.set_of_mem_eq
- \- *theorem* set.set_of_mem_eq
- \+ *lemma* set.univ_eq_true_false
- \+ *lemma* singleton_neq_emptyset
- \- *theorem* singleton_neq_emptyset

Modified algebra/order.lean
- \+ *lemma* not_le_iff
- \+ *lemma* not_lt_iff
- \+ *def* partial_order_dual
- \- *def* weak_order_dual

Modified algebra/ring.lean


Modified data/int/order.lean
- \+ *lemma* int.le_of_of_nat_le_of_nat
- \+ *lemma* int.of_nat_le_of_nat_of_le

Modified data/nat/basic.lean
- \+ *lemma* nat.le_add_one_iff
- \+ *lemma* nat.le_zero_iff

Modified data/rat.lean
- \+ *lemma* rat.coe_int_add
- \+ *lemma* rat.coe_int_eq_mk
- \+ *lemma* rat.coe_int_one
- \+ *lemma* rat.coe_int_sub
- \+ *lemma* rat.coe_nat_rat_eq_mk
- \+ *lemma* rat.exists_upper_nat_bound
- \+ *lemma* rat.le_of_of_int_le_of_int
- \+ *def* rat.nat_ceil
- \+ *lemma* rat.nat_ceil_add_one_eq
- \+ *lemma* rat.nat_ceil_lt_add_one
- \+ *lemma* rat.nat_ceil_min
- \+ *lemma* rat.nat_ceil_mono
- \+ *lemma* rat.nat_ceil_spec
- \+ *lemma* rat.nat_ceil_zero

Modified data/set/basic.lean
- \+ *theorem* set.image_eq_preimage_of_inverse
- \+ *lemma* set.mem_image_iff_of_inverse
- \+ *lemma* set.mem_of_eq_of_mem
- \+ *lemma* set.set_compr_eq_eq_singleton
- \+/\- *theorem* set.subset.trans

Modified data/set/finite.lean
- \+ *lemma* set.finite_le_nat

Modified data/set/lattice.lean
- \+ *lemma* set.monotone_image

Modified topology/continuity.lean
- \- *theorem* classical.cases
- \+ *lemma* closed_diagonal
- \+ *lemma* closed_eq
- \+ *lemma* closed_prod
- \+ *lemma* closed_property2
- \+ *lemma* closed_property3
- \+ *lemma* closed_property
- \+ *lemma* closure_induced
- \+ *lemma* closure_prod_eq
- \- *theorem* closure_prod_eq
- \+ *lemma* closure_subtype
- \+ *lemma* compact_image
- \+ *lemma* compact_pi_infinite
- \- *theorem* compact_pi_infinite
- \+ *lemma* continuous_Inf_dom
- \- *theorem* continuous_Inf_dom
- \+ *lemma* continuous_Inf_rng
- \- *theorem* continuous_Inf_rng
- \+ *lemma* continuous_Prop
- \- *theorem* continuous_Prop
- \+ *lemma* continuous_bot
- \- *theorem* continuous_bot
- \+ *lemma* continuous_coinduced_dom
- \- *theorem* continuous_coinduced_dom
- \+ *lemma* continuous_coinduced_rng
- \- *theorem* continuous_coinduced_rng
- \+ *lemma* continuous_compose
- \- *theorem* continuous_compose
- \+ *lemma* continuous_const
- \+ *lemma* continuous_eq_le_coinduced
- \- *theorem* continuous_eq_le_coinduced
- \+ *lemma* continuous_fst
- \- *theorem* continuous_fst
- \+ *lemma* continuous_id
- \- *theorem* continuous_id
- \+ *lemma* continuous_iff_closed
- \+ *lemma* continuous_iff_induced_le
- \- *theorem* continuous_iff_induced_le
- \+ *lemma* continuous_iff_of_embedding
- \+ *lemma* continuous_iff_towards
- \- *theorem* continuous_iff_towards
- \+ *lemma* continuous_induced_dom
- \- *theorem* continuous_induced_dom
- \+ *lemma* continuous_induced_rng
- \- *theorem* continuous_induced_rng
- \+ *lemma* continuous_inf_dom
- \- *theorem* continuous_inf_dom
- \+ *lemma* continuous_inf_rng_left
- \- *theorem* continuous_inf_rng_left
- \+ *lemma* continuous_inf_rng_right
- \- *theorem* continuous_inf_rng_right
- \+ *lemma* continuous_infi_dom
- \- *theorem* continuous_infi_dom
- \+ *lemma* continuous_infi_rng
- \- *theorem* continuous_infi_rng
- \+ *lemma* continuous_inl
- \- *theorem* continuous_inl
- \+ *lemma* continuous_inr
- \- *theorem* continuous_inr
- \+ *lemma* continuous_prod_mk
- \- *theorem* continuous_prod_mk
- \+ *lemma* continuous_snd
- \- *theorem* continuous_snd
- \+ *lemma* continuous_subtype_closed_cover
- \+ *lemma* continuous_subtype_mk
- \- *theorem* continuous_subtype_mk
- \+ *lemma* continuous_subtype_nhds_cover
- \- *theorem* continuous_subtype_nhds_cover
- \+ *lemma* continuous_subtype_val
- \- *theorem* continuous_subtype_val
- \+ *lemma* continuous_sum_rec
- \- *theorem* continuous_sum_rec
- \+ *lemma* continuous_sup_dom_left
- \- *theorem* continuous_sup_dom_left
- \+ *lemma* continuous_sup_dom_right
- \- *theorem* continuous_sup_dom_right
- \+ *lemma* continuous_sup_rng
- \- *theorem* continuous_sup_rng
- \+ *lemma* continuous_top
- \- *theorem* continuous_top
- \+ *lemma* dense_embedding.closure_image_univ
- \+ *lemma* dense_embedding.continuous_ext
- \+ *def* dense_embedding.ext
- \+ *lemma* dense_embedding.ext_e_eq
- \+ *lemma* dense_embedding.ext_eq
- \+ *lemma* dense_embedding.inj_iff
- \+ *def* dense_embedding.subtype_emb
- \+ *lemma* dense_embedding.towards_ext
- \+ *lemma* dense_embedding.vmap_nhds_neq_bot
- \+ *structure* dense_embedding
- \+ *def* embedding
- \+ *lemma* embedding_closed
- \+ *lemma* embedding_compose
- \+ *lemma* embedding_graph
- \+ *lemma* embedding_id
- \+ *lemma* embedding_of_embedding_compose
- \+ *lemma* embedding_open
- \+ *lemma* embedding_prod_mk
- \+ *lemma* embedding_subtype_val
- \- *theorem* false_neq_true
- \+ *lemma* image_closure_subset_closure_image
- \+ *lemma* image_preimage_eq_inter_rng
- \+ *lemma* induced_compose
- \+ *lemma* induced_id
- \+ *lemma* induced_mono
- \+ *lemma* induced_sup
- \+ *lemma* map_nhds_induced_eq
- \- *theorem* map_nhds_induced_eq
- \+ *lemma* map_nhds_subtype_val_eq
- \- *theorem* map_nhds_subtype_val_eq
- \+ *lemma* mem_closure_of_continuous2
- \+ *lemma* mem_closure_of_continuous
- \+ *lemma* nhds_induced_eq_vmap
- \- *theorem* nhds_induced_eq_vmap
- \+ *lemma* nhds_pi
- \- *theorem* nhds_pi
- \+ *lemma* nhds_prod_eq
- \- *theorem* nhds_prod_eq
- \+ *lemma* nhds_subtype_eq_vmap
- \+ *lemma* open_set_prod
- \- *theorem* open_set_prod
- \+ *lemma* open_singleton_true
- \- *theorem* open_singleton_true
- \+ *lemma* prod_eq_generate_from
- \- *theorem* prod_eq_generate_from
- \+ *lemma* subtype.val_image
- \- *theorem* subtype.val_image
- \+ *lemma* towards_nhds_iff_of_embedding
- \- *theorem* univ_eq_true_false
- \+ *lemma* univ_prod_univ

Added topology/real.lean
- \+ *lemma* abs_real_eq_abs
- \+ *lemma* closed_ge
- \+ *lemma* closed_imp
- \+ *lemma* closed_le
- \+ *lemma* closed_le_real
- \+ *lemma* closure_of_rat_image_eq
- \+ *lemma* compact_ivl
- \+ *lemma* continuous_abs_rat
- \+ *lemma* continuous_abs_real
- \+ *lemma* continuous_add_rat
- \+ *lemma* continuous_add_real'
- \+ *lemma* continuous_add_real
- \+ *lemma* continuous_inv_real'
- \+ *lemma* continuous_inv_real
- \+ *lemma* continuous_mul_real'
- \+ *lemma* continuous_mul_real
- \+ *lemma* continuous_neg_rat
- \+ *lemma* continuous_neg_real
- \+ *lemma* continuous_sub_real
- \+ *lemma* dense_embedding_of_rat
- \+ *lemma* dense_embedding_of_rat_of_rat
- \+ *lemma* eq_0_of_nonneg_of_neg_nonneg
- \+ *lemma* exists_lt_of_rat
- \+ *lemma* exists_supremum_real
- \+ *lemma* forall_subtype_iff
- \+ *lemma* gt_mem_nhds
- \+ *def* lift_rat_fun
- \+ *lemma* lift_rat_fun_of_rat
- \+ *def* lift_rat_op
- \+ *lemma* lift_rat_op_of_rat_of_rat
- \+ *lemma* lt_mem_nhds
- \+ *lemma* map_neg_rat
- \+ *lemma* map_neg_real
- \+ *lemma* mem_nonneg_of_continuous2
- \+ *lemma* mem_uniformity_rat
- \+ *lemma* mem_uniformity_real_iff
- \+ *lemma* mem_zero_nhd
- \+ *lemma* mem_zero_nhd_iff
- \+ *lemma* neg_preimage_closure
- \+ *lemma* nhds_0_eq_zero_nhd
- \+ *lemma* nhds_eq_map_zero_nhd
- \+ *def* nonneg
- \+ *def* of_rat
- \+ *lemma* of_rat_abs
- \+ *lemma* of_rat_add
- \+ *lemma* of_rat_inv
- \+ *lemma* of_rat_le_of_rat
- \+ *lemma* of_rat_lt_of_rat
- \+ *lemma* of_rat_mem_nonneg
- \+ *lemma* of_rat_mem_nonneg_iff
- \+ *lemma* of_rat_mul
- \+ *lemma* of_rat_neg
- \+ *lemma* of_rat_one
- \+ *lemma* of_rat_sub
- \+ *lemma* of_rat_zero
- \+ *lemma* one_lt_two
- \+ *lemma* open_gt
- \+ *lemma* open_lt
- \+ *lemma* open_lt_real
- \+ *lemma* preimage_neg_rat
- \+ *lemma* preimage_neg_real
- \+ *lemma* pure_zero_le_zero_nhd
- \+ *lemma* quot_mk_image_univ_eq
- \+ *def* real
- \+ *lemma* totally_bounded_01_rat
- \+ *lemma* towards_add_rat
- \+ *lemma* towards_add_rat_zero'
- \+ *lemma* towards_add_rat_zero
- \+ *lemma* towards_inv_pos_rat
- \+ *lemma* towards_inv_rat
- \+ *lemma* towards_inv_real
- \+ *lemma* towards_mul_bnd_rat'
- \+ *lemma* towards_mul_bnd_rat
- \+ *lemma* towards_mul_rat'
- \+ *lemma* towards_mul_rat
- \+ *lemma* towards_neg_rat
- \+ *lemma* towards_neg_rat_zero
- \+ *lemma* towards_of_uniform_continuous_subtype
- \+ *lemma* towards_sub_rat'
- \+ *lemma* towards_sub_uniformity_zero_nhd'
- \+ *lemma* towards_sub_uniformity_zero_nhd
- \+ *lemma* towards_zero_nhds
- \+ *lemma* two_eq_of_rat_two
- \+ *lemma* uniform_continuous_abs_rat
- \+ *lemma* uniform_continuous_abs_real
- \+ *lemma* uniform_continuous_add_rat
- \+ *lemma* uniform_continuous_add_real
- \+ *lemma* uniform_continuous_inv_pos_rat
- \+ *lemma* uniform_continuous_mul_rat
- \+ *lemma* uniform_continuous_neg_rat
- \+ *lemma* uniform_continuous_neg_real
- \+ *lemma* uniform_continuous_rat'
- \+ *lemma* uniform_continuous_rat
- \+ *lemma* uniform_embedding_add_rat
- \+ *lemma* uniform_embedding_mul_rat
- \+ *lemma* uniform_embedding_of_rat
- \+ *lemma* uniformity_rat
- \+ *lemma* zero_le_iff_nonneg
- \+ *lemma* zero_lt_two
- \+ *def* zero_nhd

Modified topology/topological_space.lean
- \+ *lemma* closed_Inter
- \- *theorem* closed_Inter
- \+ *lemma* closed_Union
- \+ *lemma* closed_Union_of_locally_finite
- \- *theorem* closed_Union_of_locally_finite
- \+ *lemma* closed_closure
- \- *theorem* closed_closure
- \+ *lemma* closed_compl_iff
- \- *theorem* closed_compl_iff_open
- \+ *lemma* closed_empty
- \- *theorem* closed_empty
- \+ *lemma* closed_iff_nhds
- \- *theorem* closed_iff_nhds
- \+ *lemma* closed_induced_iff
- \+ *lemma* closed_inter
- \+ *lemma* closed_sInter
- \- *theorem* closed_sInter
- \+ *lemma* closed_singleton
- \+ *lemma* closed_union
- \- *theorem* closed_union
- \+ *lemma* closed_univ
- \- *theorem* closed_univ
- \+ *lemma* closure_closure
- \- *theorem* closure_closure
- \+ *lemma* closure_compl_eq
- \- *theorem* closure_compl_eq
- \+ *lemma* closure_diff
- \+ *lemma* closure_empty
- \- *theorem* closure_empty
- \+ *lemma* closure_eq_compl_interior_compl
- \- *theorem* closure_eq_compl_interior_compl
- \+ *lemma* closure_eq_iff_closed
- \- *theorem* closure_eq_iff_closed
- \+ *lemma* closure_eq_nhds
- \- *theorem* closure_eq_nhds
- \+ *lemma* closure_eq_of_closed
- \- *theorem* closure_eq_of_closed
- \+ *lemma* closure_inter_open
- \+ *lemma* closure_minimal
- \- *theorem* closure_minimal
- \+ *lemma* closure_mono
- \- *theorem* closure_mono
- \+ *lemma* closure_singleton
- \+ *lemma* closure_subset_iff_subset_of_closed
- \- *theorem* closure_subset_iff_subset_of_closed
- \+ *lemma* closure_union
- \- *theorem* closure_union
- \+ *lemma* closure_univ
- \- *theorem* closure_univ
- \+/\- *def* compact
- \+ *lemma* compact_adherence_nhdset
- \- *theorem* compact_adherence_nhdset
- \+ *lemma* compact_elim_finite_subcover
- \+ *lemma* compact_elim_finite_subcover_image
- \+ *lemma* compact_empty
- \+ *lemma* compact_iff_finite_subcover
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \- *theorem* compact_iff_ultrafilter_le_nhds
- \+ *lemma* compact_of_closed_subset
- \+ *lemma* compact_of_finite_subcover
- \+ *lemma* compact_singleton
- \+ *lemma* compl_singleton_mem_nhds
- \+ *lemma* compl_subset_of_compl_subset
- \+ *lemma* diff_subset_diff
- \+ *lemma* eq_of_nhds_eq_nhds
- \- *theorem* eq_of_nhds_eq_nhds
- \+ *lemma* eq_of_nhds_neq_bot
- \- *theorem* eq_of_nhds_neq_bot
- \- *theorem* finite_subcover_of_compact
- \+ *lemma* generate_from_le
- \- *theorem* generate_from_le
- \+ *lemma* interior_compl_eq
- \- *theorem* interior_compl_eq
- \+ *lemma* interior_empty
- \- *theorem* interior_empty
- \+ *lemma* interior_eq_iff_open
- \- *theorem* interior_eq_iff_open
- \+ *lemma* interior_eq_nhds
- \- *theorem* interior_eq_nhds
- \+ *lemma* interior_eq_of_open
- \- *theorem* interior_eq_of_open
- \+ *lemma* interior_inter
- \- *theorem* interior_inter
- \+ *lemma* interior_interior
- \- *theorem* interior_interior
- \+ *lemma* interior_maximal
- \- *theorem* interior_maximal
- \+ *lemma* interior_mono
- \- *theorem* interior_mono
- \+ *lemma* interior_subset
- \- *theorem* interior_subset
- \+ *lemma* interior_subset_closure
- \- *theorem* interior_subset_closure
- \+ *lemma* interior_union_closed_of_interior_empty
- \- *theorem* interior_union_closed_of_interior_empty
- \+ *lemma* interior_univ
- \- *theorem* interior_univ
- \+ *lemma* le_of_nhds_le_nhds
- \- *theorem* le_of_nhds_le_nhds
- \+ *lemma* lim_eq
- \+ *lemma* lim_nhds_eq
- \+ *lemma* lim_nhds_eq_of_closure
- \+ *lemma* lim_spec
- \+ *lemma* locally_finite_of_finite
- \+ *lemma* locally_finite_subset
- \+ *lemma* map_nhds
- \- *theorem* map_nhds
- \+ *lemma* mem_nhds_sets
- \- *theorem* mem_nhds_sets
- \+ *lemma* mem_nhds_sets_iff
- \- *theorem* mem_nhds_sets_iff
- \+ *lemma* mem_of_mem_of_subset
- \+ *lemma* mem_of_nhds
- \+ *lemma* nhds_closed
- \+ *lemma* nhds_eq_nhds_iff
- \+ *lemma* nhds_le_nhds_iff
- \+ *lemma* nhds_mono
- \- *theorem* nhds_mono
- \+ *lemma* nhds_neq_bot
- \- *theorem* nhds_neq_bot
- \+ *lemma* nhds_sets
- \- *theorem* nhds_sets
- \+ *lemma* nhds_supr
- \- *theorem* nhds_supr
- \+ *lemma* not_and_iff_imp_not
- \- *theorem* not_eq_empty_iff_exists
- \+ *lemma* open_Union
- \- *theorem* open_Union
- \+ *lemma* open_compl_iff
- \- *theorem* open_compl_iff_closed
- \+ *lemma* open_diff
- \- *theorem* open_diff
- \+ *lemma* open_empty
- \- *theorem* open_empty
- \+ *lemma* open_iff_nhds
- \- *theorem* open_iff_nhds
- \+ *lemma* open_inter
- \- *theorem* open_inter
- \+ *lemma* open_interior
- \- *theorem* open_interior
- \+ *lemma* open_sUnion
- \- *theorem* open_sUnion
- \+ *lemma* open_union
- \+ *lemma* open_univ
- \- *theorem* open_univ
- \+ *lemma* return_le_nhds
- \- *theorem* return_le_nhds
- \+ *lemma* subset_closure
- \- *theorem* subset_closure
- \+ *lemma* subset_interior_iff_subset_of_open
- \- *theorem* subset_interior_iff_subset_of_open
- \+ *lemma* sup_eq_generate_from
- \- *theorem* sup_eq_generate_from
- \+ *lemma* supr_eq_generate_from
- \- *theorem* supr_eq_generate_from
- \+ *lemma* t2_separation
- \+ *lemma* t2_space_top
- \- *theorem* t2_space_top
- \+ *lemma* topological_space.nhds_generate_from
- \- *theorem* topological_space.nhds_generate_from
- \+ *lemma* topological_space_eq
- \- *theorem* topological_space_eq
- \+ *lemma* towards_const_nhds
- \+ *lemma* towards_nhds
- \+ *lemma* towards_nhds_unique
- \+ *lemma* univ_subtype

Modified topology/uniform_space.lean
- \+ *lemma* Cauchy.monotone_gen
- \- *theorem* Cauchy.monotone_gen
- \+ *lemma* Cauchy.pure_cauchy_dense
- \- *theorem* Cauchy.pure_cauchy_dense
- \+ *lemma* Cauchy.uniform_embedding_pure_cauchy
- \- *theorem* Cauchy.uniform_embedding_pure_cauchy
- \- *def* cauchy
- \+ *lemma* cauchy_downwards
- \- *theorem* cauchy_downwards
- \+ *lemma* cauchy_map
- \- *theorem* cauchy_map
- \+ *lemma* cauchy_nhds
- \- *theorem* cauchy_nhds
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \- *theorem* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* cauchy_pure
- \- *theorem* cauchy_pure
- \+ *lemma* cauchy_vmap
- \- *theorem* cauchy_vmap
- \+ *lemma* closure_eq_inter_uniformity
- \- *theorem* closure_eq_inter_uniformity
- \+ *lemma* closure_image_mem_nhds_of_uniform_embedding
- \+ *lemma* comp_le_uniformity3
- \- *theorem* comp_le_uniformity3
- \+ *lemma* comp_le_uniformity
- \- *theorem* comp_le_uniformity
- \+ *lemma* comp_mem_uniformity_sets
- \- *theorem* comp_mem_uniformity_sets
- \+/\- *def* comp_rel
- \+ *lemma* comp_symm_of_uniformity
- \- *theorem* comp_symm_of_uniformity
- \+ *lemma* compact_of_totally_bounded_closed
- \- *theorem* compact_of_totally_bounded_closed
- \+ *lemma* compact_of_totally_bounded_complete
- \- *theorem* compact_of_totally_bounded_complete
- \+ *lemma* complete_of_closed
- \- *theorem* complete_of_closed
- \+ *lemma* complete_space_extension
- \- *theorem* complete_space_extension
- \+ *lemma* complete_space_separation
- \- *theorem* complete_space_separation
- \+ *lemma* continuous_of_uniform
- \- *theorem* continuous_of_uniform
- \+ *lemma* dense_embedding_of_uniform_embedding
- \+ *lemma* forall_quotient_iff
- \+ *lemma* id_comp_rel
- \- *theorem* id_comp_rel
- \+ *lemma* interior_mem_uniformity
- \- *theorem* interior_mem_uniformity
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \- *theorem* le_nhds_iff_adhp_of_cauchy
- \+ *lemma* le_nhds_of_cauchy_adhp
- \- *theorem* le_nhds_of_cauchy_adhp
- \+ *lemma* lift_nhds_left
- \- *theorem* lift_nhds_left
- \+ *lemma* lift_nhds_right
- \- *theorem* lift_nhds_right
- \+ *lemma* mem_nhds_left
- \- *theorem* mem_nhds_left
- \+ *lemma* mem_nhds_right
- \- *theorem* mem_nhds_right
- \+ *lemma* mem_nhds_uniformity_iff
- \- *theorem* mem_nhds_uniformity_iff
- \+ *lemma* mem_uniform_prod
- \+ *lemma* mem_uniformity_closed
- \+ *lemma* nhds_eq_uniformity
- \- *theorem* nhds_eq_uniformity
- \+ *lemma* nhds_eq_uniformity_prod
- \- *theorem* nhds_eq_uniformity_prod
- \+ *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \- *theorem* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *lemma* nhdset_of_mem_uniformity
- \- *theorem* nhdset_of_mem_uniformity
- \+ *lemma* open_uniformity
- \+ *lemma* prod_mk_mem_comp_rel
- \- *theorem* prod_mk_mem_comp_rel
- \+ *lemma* refl_le_uniformity
- \- *theorem* refl_le_uniformity
- \+ *lemma* refl_mem_uniformity
- \- *theorem* refl_mem_uniformity
- \- *def* separated
- \+ *lemma* separated_equiv
- \- *theorem* separated_equiv
- \+ *lemma* separated_separation
- \+ *lemma* sup_uniformity
- \+ *lemma* supr_uniformity
- \- *theorem* supr_uniformity
- \+ *lemma* symm_le_uniformity
- \- *theorem* symm_le_uniformity
- \+ *lemma* symm_of_uniformity
- \- *theorem* symm_of_uniformity
- \+ *lemma* to_topological_space_Sup
- \+ *lemma* to_topological_space_bot
- \- *theorem* to_topological_space_bot
- \+ *lemma* to_topological_space_mono
- \- *theorem* to_topological_space_mono
- \+ *lemma* to_topological_space_prod
- \+ *lemma* to_topological_space_subtype
- \+ *lemma* to_topological_space_sup
- \+ *lemma* to_topological_space_supr
- \- *theorem* to_topological_space_supr
- \+ *lemma* to_topological_space_top
- \- *theorem* to_topological_space_top
- \+ *lemma* totally_bounded_closure
- \+ *lemma* totally_bounded_iff_filter
- \- *theorem* totally_bounded_iff_filter
- \+ *lemma* totally_bounded_iff_ultrafilter
- \- *theorem* totally_bounded_iff_ultrafilter
- \+ *lemma* totally_bounded_image
- \+ *lemma* totally_bounded_subset
- \+ *lemma* towards_const_uniformity
- \+ *lemma* towards_left_nhds_uniformity
- \+ *lemma* towards_prod_uniformity_fst
- \+ *lemma* towards_prod_uniformity_snd
- \+ *lemma* towards_right_nhds_uniformity
- \+ *lemma* towards_swap_uniformity
- \- *def* uniform_continuous
- \+ *lemma* uniform_continuous_compose
- \+ *lemma* uniform_continuous_const
- \+ *lemma* uniform_continuous_fst
- \+ *lemma* uniform_continuous_of_embedding
- \- *theorem* uniform_continuous_of_embedding
- \+ *lemma* uniform_continuous_prod_mk
- \+ *lemma* uniform_continuous_quotient_mk
- \- *theorem* uniform_continuous_quotient_mk
- \+ *lemma* uniform_continuous_snd
- \+ *lemma* uniform_continuous_subtype_mk
- \+ *lemma* uniform_continuous_subtype_val
- \+ *lemma* uniform_continuous_uniformly_extend
- \- *theorem* uniform_continuous_uniformly_extend
- \+ *lemma* uniform_continuous_vmap'
- \+ *lemma* uniform_continuous_vmap
- \- *theorem* uniform_continuous_vmap
- \- *def* uniform_embedding
- \+ *lemma* uniform_embedding_prod
- \+ *lemma* uniform_embedding_subtype_emb
- \+ *lemma* uniform_extend_subtype
- \+ *def* uniform_space.core.to_topological_space
- \+ *structure* uniform_space.core
- \+ *lemma* uniform_space.core_eq
- \+ *def* uniform_space.of_core
- \+ *def* uniform_space.of_core_eq
- \+ *lemma* uniform_space.of_core_eq_to_core
- \+ *lemma* uniform_space.to_core_to_topological_space
- \+ *lemma* uniform_space_eq
- \- *theorem* uniform_space_eq
- \+/\- *def* uniformity
- \+ *lemma* uniformity_eq_symm
- \- *theorem* uniformity_eq_symm
- \+ *lemma* uniformity_eq_uniformity_closure
- \- *theorem* uniformity_eq_uniformity_closure
- \+ *lemma* uniformity_eq_uniformity_interior
- \- *theorem* uniformity_eq_uniformity_interior
- \+ *lemma* uniformity_le_symm
- \- *theorem* uniformity_le_symm
- \+ *lemma* uniformity_lift_le_comp
- \- *theorem* uniformity_lift_le_comp
- \+ *lemma* uniformity_prod
- \+ *lemma* uniformity_subtype
- \+ *lemma* uniformly_extend_exists
- \+ *lemma* uniformly_extend_of_emb
- \- *theorem* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_spec
- \- *theorem* uniformly_extend_spec
- \- *theorem* uniformly_extend_unique
- \+ *lemma* vmap_quotient_eq_uniformity
- \+ *lemma* vmap_quotient_le_uniformity
- \- *theorem* vmap_quotient_le_uniformity



## [2017-08-02 22:32:47+01:00](https://github.com/leanprover-community/mathlib/commit/64b6151)
refactor(data/set/basic,*): vimage -> preimage, add notation
#### Estimated changes
Modified algebra/lattice/filter.lean
- \+/\- *theorem* filter.mem_vmap_of_mem
- \+ *theorem* filter.preimage_mem_vmap
- \- *theorem* filter.vimage_mem_vmap
- \+/\- *theorem* filter.vmap_principal
- \+ *theorem* set.image_eq_preimage_of_inverse
- \- *theorem* set.image_eq_vimage_of_inverse
- \+ *theorem* set.image_swap_eq_preimage_swap
- \- *theorem* set.image_swap_eq_vimage_swap
- \+ *theorem* set.preimage_set_of_eq
- \+ *theorem* set.prod_preimage_eq
- \- *theorem* set.prod_vimage_eq
- \- *theorem* set.vimage_set_of_eq

Modified data/set/basic.lean
- \+ *theorem* set.eq_preimage_subtype_val_iff
- \- *theorem* set.eq_vimage_subtype_val_iff
- \+/\- *theorem* set.image_comp
- \+/\- *theorem* set.image_empty
- \+/\- *theorem* set.image_id
- \+/\- *theorem* set.image_subset
- \+ *theorem* set.image_subset_iff_subset_preimage
- \- *theorem* set.image_subset_iff_subset_vimage
- \+/\- *def* set.mem_image_elim_on
- \+/\- *theorem* set.mem_image_eq
- \+/\- *theorem* set.mem_image_of_mem
- \+ *theorem* set.mem_preimage_eq
- \- *theorem* set.mem_vimage_eq
- \+/\- *theorem* set.mono_image
- \+ *def* set.preimage
- \+ *theorem* set.preimage_comp
- \+ *theorem* set.preimage_compl
- \+ *theorem* set.preimage_empty
- \+ *theorem* set.preimage_id
- \+ *theorem* set.preimage_image_eq
- \+ *theorem* set.preimage_inter
- \+ *theorem* set.preimage_mono
- \+ *theorem* set.preimage_union
- \+ *theorem* set.preimage_univ
- \- *def* set.vimage
- \- *theorem* set.vimage_comp
- \- *theorem* set.vimage_compl
- \- *theorem* set.vimage_empty
- \- *theorem* set.vimage_id
- \- *theorem* set.vimage_image_eq
- \- *theorem* set.vimage_inter
- \- *theorem* set.vimage_mono
- \- *theorem* set.vimage_union
- \- *theorem* set.vimage_univ

Modified data/set/lattice.lean
- \+ *theorem* set.monotone_preimage
- \- *theorem* set.monotone_vimage
- \+ *theorem* set.preimage_Union
- \+ *theorem* set.preimage_sUnion
- \- *theorem* set.vimage_Union
- \- *theorem* set.vimage_sUnion

Modified topology/continuity.lean
- \+/\- *def* continuous
- \+/\- *theorem* open_induced

Modified topology/topological_space.lean


Modified topology/uniform_space.lean




## [2017-08-02 22:17:36+01:00](https://github.com/leanprover-community/mathlib/commit/41a2376)
refactor(algebra/group,group_power): clean up proofs
#### Estimated changes
Modified algebra/group.lean
- \+/\- *theorem* eq_iff_eq_of_sub_eq_sub
- \+/\- *theorem* eq_iff_sub_eq_zero
- \+/\- *theorem* eq_inv_iff_eq_inv
- \+/\- *theorem* eq_of_mul_inv_eq_one
- \+/\- *theorem* eq_one_of_inv_eq_one
- \+/\- *theorem* eq_sub_iff_add_eq
- \+/\- *theorem* inv_eq_inv_iff_eq
- \+/\- *theorem* inv_eq_one_iff_eq_one
- \+/\- *theorem* left_inverse_add_left_sub
- \+/\- *theorem* left_inverse_add_right_neg_add
- \+/\- *theorem* left_inverse_inv
- \+/\- *theorem* left_inverse_neg_add_add_right
- \+/\- *theorem* left_inverse_sub_add_left
- \+/\- *theorem* mul_eq_iff_eq_inv_mul
- \+/\- *theorem* mul_eq_iff_eq_mul_inv
- \+/\- *theorem* sub_eq_iff_eq_add

Modified algebra/group_power.lean
- \- *theorem* gpow_comm
- \+ *theorem* gpow_mul_comm
- \+/\- *theorem* one_pow
- \+/\- *theorem* pow_add
- \- *theorem* pow_comm
- \+/\- *def* pow_int
- \+ *theorem* pow_mul_comm'
- \+ *theorem* pow_mul_comm
- \+/\- *def* pow_nat
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_succ



## [2017-08-02 16:24:02+01:00](https://github.com/leanprover-community/mathlib/commit/3e9e4b6)
refactor(*): move theorems and do minor polishing
#### Estimated changes
Modified data/bool.lean


Modified data/list/basic.lean
- \+/\- *theorem* list.concat_cons

Modified data/list/sort.lean
- \- *theorem* nat.add_pos_iff_pos_or_pos
- \- *theorem* nat.add_pos_left
- \- *theorem* nat.add_pos_right
- \- *theorem* nat.lt_succ_iff_le
- \- *theorem* nat.succ_le_succ_iff

Modified data/nat/basic.lean
- \+ *theorem* nat.add_pos_iff_pos_or_pos
- \+ *theorem* nat.add_pos_left
- \+ *theorem* nat.add_pos_right
- \+ *theorem* nat.lt_succ_iff_le
- \+ *theorem* nat.succ_le_succ_iff

Modified logic/basic.lean
- \+ *theorem* and_implies_iff
- \+ *theorem* bexists_def
- \+ *theorem* iff_def
- \+ *theorem* implies_and_iff

Modified tactic/finish.lean
- \- *theorem* curry_iff
- \- *theorem* iff_def
- \- *theorem* implies_and_iff
- \- *theorem* {u}



## [2017-08-02 16:21:24+01:00](https://github.com/leanprover-community/mathlib/commit/da0c346)
fix(*): fix wrt changes in lean
#### Estimated changes
Modified algebra/lattice/bounded_lattice.lean


Modified algebra/lattice/complete_lattice.lean
- \- *theorem* lattice.Inf_le_iff
- \+ *theorem* lattice.Sup_le_iff
- \+ *theorem* lattice.le_Inf_iff
- \- *theorem* lattice.le_Sup_iff

Modified algebra/lattice/filter.lean
- \+/\- *theorem* directed_of_chain
- \+/\- *def* filter.at_bot
- \+/\- *def* filter.at_top
- \+/\- *theorem* filter.monotone_lift'
- \+/\- *theorem* filter.monotone_lift
- \- *theorem* lattice.Sup_le_iff
- \+/\- *theorem* set.monotone_inter
- \+/\- *theorem* set.monotone_prod
- \+/\- *theorem* set.monotone_set_of

Modified algebra/lattice/fixed_points.lean
- \+/\- *theorem* ge_of_eq

Modified algebra/order.lean
- \+/\- *theorem* comp_le_comp_left_of_monotone

Modified data/num/lemmas.lean


Modified data/set/basic.lean
- \+/\- *theorem* set.mem_set_of_eq

Modified tactic/alias.lean
- \- *def* tactic.alias.alias_attr

Modified topology/uniform_space.lean
- \+/\- *theorem* monotone_comp_rel



## [2017-08-02 15:24:33+01:00](https://github.com/leanprover-community/mathlib/commit/6392b05)
refactor(*): switch from order_pair to partial_order
#### Estimated changes
Modified algebra/lattice/basic.lean
- \+/\- *theorem* le_antisymm'

Modified algebra/lattice/bounded_lattice.lean


Modified algebra/lattice/complete_lattice.lean


Modified algebra/lattice/filter.lean
- \+/\- *theorem* directed_of_chain
- \+/\- *def* filter.at_bot
- \+/\- *def* filter.at_top
- \+/\- *theorem* filter.monotone_lift'
- \+/\- *theorem* filter.monotone_lift
- \+/\- *theorem* set.monotone_inter
- \+/\- *theorem* set.monotone_prod
- \+/\- *theorem* set.monotone_set_of

Modified algebra/lattice/fixed_points.lean
- \+/\- *theorem* ge_of_eq
- \+/\- *theorem* lattice.gfp_comp
- \+/\- *theorem* lattice.lfp_comp

Modified algebra/lattice/zorn.lean
- \+ *theorem* zorn.zorn_partial_order
- \- *theorem* zorn.zorn_weak_order

Modified algebra/order.lean
- \+/\- *theorem* comp_le_comp_left_of_monotone
- \+/\- *theorem* le_dual_eq_le
- \+/\- *def* weak_order_dual

Modified data/hash_map.lean


Modified data/list/set.lean


Modified data/num/lemmas.lean


Modified data/rat.lean
- \+/\- *def* rat.mk_nat
- \+/\- *def* rat.mk_pnat

Modified data/set/lattice.lean


Modified logic/basic.lean
- \+/\- *theorem* eq_iff_le_and_le

Modified topology/topological_space.lean


Modified topology/uniform_space.lean
- \+/\- *theorem* monotone_comp_rel



## [2017-08-01 03:44:00+01:00](https://github.com/leanprover-community/mathlib/commit/fe81186)
fix(tactic/alias): autogenerated alias names
#### Estimated changes
Modified tactic/alias.lean




## [2017-08-01 02:30:49+01:00](https://github.com/leanprover-community/mathlib/commit/1191b4d)
feat(tactic/alias): support biconditional aliases
#### Estimated changes
Modified tactic/alias.lean
- \- *def* alias_attr
- \+ *def* tactic.alias.alias_attr



## [2017-08-01 00:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/fb21c1a)
feat(tactic/alias): alias command
#### Estimated changes
Added tactic/alias.lean
- \+ *def* alias_attr

