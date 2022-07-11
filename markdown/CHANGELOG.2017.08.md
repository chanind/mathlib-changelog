## [2017-08-30 20:12:20-04:00](https://github.com/leanprover-community/mathlib/commit/dbc8f86)
feat(topology/measurable_space): measurability is closed under id and comp
#### Estimated changes
Modified topology/measurable_space.lean
- \+ *lemma* measurable_id
- \+ *lemma* measurable_comp
- \+/\- *def* measurable



## [2017-08-30 18:33:58-04:00](https://github.com/leanprover-community/mathlib/commit/4ef0ea8)
feat(topology/ennreal): add subtraction
#### Estimated changes
Modified order/complete_lattice.lean


Modified topology/ennreal.lean
- \+ *lemma* lt_Sup_iff
- \+ *lemma* Sup_eq_top
- \+ *lemma* not_infty_lt
- \+ *lemma* of_real_lt_infty
- \+/\- *lemma* of_real_lt_of_real_iff
- \+ *lemma* lt_iff_exists_of_real
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* le_add_left
- \+ *lemma* le_add_right
- \+ *lemma* Inf_add
- \+ *lemma* Sup_add
- \+ *lemma* sub_eq_zero_of_le
- \+ *lemma* sub_add_cancel_of_le
- \+ *lemma* add_sub_cancel_of_le
- \+ *lemma* sub_add_self_eq_max
- \+ *lemma* sub_le_sub
- \+ *lemma* le_sub_iff_add_le
- \+ *lemma* zero_sub
- \+ *lemma* sub_infty
- \+ *lemma* sub_zero



## [2017-08-30 11:17:07-05:00](https://github.com/leanprover-community/mathlib/commit/f93f7e7)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-08-29 23:40:45-04:00](https://github.com/leanprover-community/mathlib/commit/cb7fb9b)
feat(topology): basic setup for measurable spaces
#### Estimated changes
Created topology/measurable_space.lean
- \+ *lemma* is_measurable_empty
- \+ *lemma* is_measurable_compl
- \+ *lemma* is_measurable_Union
- \+ *lemma* measurable_space_eq
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* comap_le_iff_le_map
- \+ *lemma* gc_comap_map
- \+ *lemma* map_mono
- \+ *lemma* monotone_map
- \+ *lemma* comap_mono
- \+ *lemma* monotone_comap
- \+ *lemma* comap_bot
- \+ *lemma* comap_sup
- \+ *lemma* comap_supr
- \+ *lemma* map_top
- \+ *lemma* map_inf
- \+ *lemma* map_infi
- \+ *lemma* comap_map_le
- \+ *lemma* le_map_comap
- \+ *def* is_measurable
- \+ *def* measurable



## [2017-08-29 19:20:11-04:00](https://github.com/leanprover-community/mathlib/commit/51042cd)
feat(topology/ennreal): add extended non-negative real numbers
#### Estimated changes
Modified algebra/big_operators.lean


Created topology/ennreal.lean
- \+ *lemma* zero_le_mul
- \+ *lemma* of_ennreal_of_real
- \+ *lemma* zero_le_of_ennreal
- \+ *lemma* of_real_of_ennreal
- \+ *lemma* forall_ennreal
- \+ *lemma* of_real_zero
- \+ *lemma* of_real_one
- \+ *lemma* zero_ne_infty
- \+ *lemma* infty_ne_zero
- \+ *lemma* of_real_ne_infty
- \+ *lemma* infty_ne_of_real
- \+ *lemma* of_real_eq_of_real_of
- \+ *lemma* of_real_ne_of_real_of
- \+ *lemma* of_real_eq_zero_iff
- \+ *lemma* zero_eq_of_real_iff
- \+ *lemma* of_real_eq_one_iff
- \+ *lemma* one_eq_of_real_iff
- \+ *lemma* of_nonneg_real_eq_of_real
- \+ *lemma* of_real_add_of_real
- \+ *lemma* add_infty
- \+ *lemma* infty_add
- \+ *lemma* of_real_mul_of_real
- \+ *lemma* of_real_mul_infty
- \+ *lemma* infty_mul_of_real
- \+ *lemma* mul_infty
- \+ *lemma* infty_mul
- \+ *lemma* infty_le_iff
- \+ *lemma* le_infty
- \+ *lemma* of_real_le_of_real_iff
- \+ *lemma* le_of_real_iff
- \+ *lemma* le_zero_iff_eq
- \+ *lemma* of_real_lt_of_real_iff
- \+ *lemma* add_le_add
- \+ *lemma* mul_le_mul
- \+ *lemma* infty_mem_upper_bounds
- \+ *lemma* of_real_mem_upper_bounds
- \+ *lemma* is_lub_of_real
- \+ *def* of_real
- \+ *def* of_ennreal

Modified topology/real.lean
- \+/\- *lemma* exists_supremum_real



## [2017-08-28 21:34:47-04:00](https://github.com/leanprover-community/mathlib/commit/76ae12c)
fix(algbera/big_operators): remove simp attr for sum/mul-distributivity rules
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* sum_mul
- \+/\- *lemma* mul_sum



## [2017-08-28 21:30:00-04:00](https://github.com/leanprover-community/mathlib/commit/edfbf3c)
feat(algebra/big_operators): add semiring and integral_domain rules
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* exists_false
- \+/\- *lemma* prod_hom
- \+ *lemma* prod_const_one
- \+/\- *lemma* prod_inv_distrib
- \+/\- *lemma* sum_sub_distrib
- \+ *lemma* sum_le_sum
- \+ *lemma* zero_le_sum
- \+ *lemma* sum_le_zero
- \+ *lemma* sum_mul
- \+ *lemma* mul_sum
- \+ *lemma* prod_eq_zero
- \+ *lemma* prod_eq_zero_iff



## [2017-08-28 19:34:30-04:00](https://github.com/leanprover-community/mathlib/commit/50ed0e4)
feat(algebra/big_operators): add congruence rule and morphism laws
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_empty
- \+/\- *lemma* prod_to_finset_of_nodup
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* prod_image
- \+ *lemma* prod_congr
- \+/\- *lemma* prod_mul_distrib
- \+ *lemma* prod_hom
- \+ *lemma* prod_inv_distrib
- \+ *lemma* sum_sub_distrib

Modified data/finset/fold.lean
- \+ *lemma* map_congr
- \+/\- *lemma* fold_insert
- \+/\- *lemma* fold_singleton
- \+/\- *lemma* fold_image
- \+ *lemma* fold_congr
- \+/\- *lemma* fold_op_distrib
- \+/\- *lemma* fold_hom



## [2017-08-28 18:34:33-04:00](https://github.com/leanprover-community/mathlib/commit/4ed43d9)
feat(data/finset): add fold; add simp rules for insert, empty, singleton and mem
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_reverse
- \+ *lemma* prod_to_finset_of_nodup
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_image
- \+ *lemma* prod_union_inter
- \- *lemma* foldl_mul_assoc
- \- *lemma* foldl_mul_eq_mul_foldr
- \- *lemma* prod_to_finset
- \- *lemma* prod_union_inter_eq
- \+/\- *theorem* prod_nil
- \+/\- *theorem* prod_cons
- \+/\- *theorem* prod_append
- \+/\- *theorem* prod_replicate

Modified data/finset/basic.lean
- \+ *lemma* or_self_or
- \+ *lemma* mem_to_finset_of_nodup_eq
- \+/\- *lemma* ne_empty_of_card_eq_succ
- \+/\- *theorem* perm_insert_cons_of_not_mem
- \+/\- *theorem* subset.refl
- \+/\- *theorem* subset.trans
- \+/\- *theorem* mem_of_subset_of_mem
- \+/\- *theorem* subset.antisymm
- \+/\- *theorem* subset_of_forall
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* mem_empty_iff
- \+/\- *theorem* empty_subset
- \+/\- *theorem* eq_empty_of_forall_not_mem
- \+/\- *theorem* eq_empty_of_subset_empty
- \+/\- *theorem* subset_empty_iff
- \+/\- *theorem* exists_mem_of_ne_empty
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* mem_of_mem_insert_of_ne
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* insert.comm
- \+ *theorem* insert_idem
- \+ *theorem* insert_ne_empty
- \+/\- *theorem* subset_insert
- \+/\- *theorem* insert_subset_insert
- \+/\- *theorem* forall_of_forall_insert
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq
- \+/\- *theorem* singleton_ne_empty
- \+ *theorem* insert_singelton_self_eq
- \+/\- *theorem* mem_union_iff
- \+/\- *theorem* mem_union_left
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_assoc
- \+/\- *theorem* union_self
- \+/\- *theorem* union_empty
- \+/\- *theorem* empty_union
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+ *theorem* union_insert
- \+/\- *theorem* mem_inter_iff
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm
- \+/\- *theorem* inter_self
- \+/\- *theorem* inter_empty
- \+/\- *theorem* empty_inter
- \+/\- *theorem* insert_inter_of_mem
- \+ *theorem* inter_insert_of_mem
- \+/\- *theorem* insert_inter_of_not_mem
- \+ *theorem* inter_insert_of_not_mem
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+ *theorem* inter_singleton_of_mem
- \+ *theorem* inter_singleton_of_not_mem
- \+/\- *theorem* mem_erase_iff
- \+/\- *theorem* not_mem_erase
- \+/\- *theorem* erase_empty
- \+/\- *theorem* ne_of_mem_erase
- \+/\- *theorem* mem_of_mem_erase
- \+/\- *theorem* mem_erase_of_ne_of_mem
- \+/\- *theorem* erase_insert
- \+/\- *theorem* insert_erase
- \+/\- *theorem* erase_subset_erase
- \+/\- *theorem* erase_subset
- \+/\- *theorem* erase_eq_of_not_mem
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* erase_subset_of_subset_insert
- \+/\- *theorem* insert_erase_subset
- \+/\- *theorem* subset_insert_of_erase_subset
- \+/\- *theorem* lt_of_mem_upto
- \+/\- *theorem* mem_upto_succ_of_mem_upto
- \+/\- *theorem* mem_upto_of_lt
- \+/\- *theorem* mem_upto_iff
- \+/\- *theorem* upto_succ
- \+/\- *theorem* card_empty
- \+/\- *theorem* card_insert_of_not_mem
- \+/\- *theorem* card_insert_le
- \+/\- *theorem* eq_empty_of_card_eq_zero
- \+/\- *theorem* card_erase_of_mem
- \+/\- *theorem* card_upto
- \- *theorem* mem_to_finset_of_nodup
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* pair_eq_singleton
- \- *theorem* card_insert_of_mem
- \- *theorem* card_erase_of_not_mem
- \- *theorem* mem_union_l
- \- *theorem* mem_union_r
- \- *theorem* eq_of_subset_of_subset
- \+/\- *def* nodup_list
- \+/\- *def* erase
- \+/\- *def* upto
- \+/\- *def* card

Created data/finset/default.lean


Created data/finset/fold.lean
- \+ *lemma* foldl_assoc
- \+ *lemma* foldl_op_eq_op_foldr_assoc
- \+ *lemma* foldl_assoc_comm_cons
- \+ *lemma* fold_op_eq_of_perm
- \+ *lemma* fold_to_finset_of_nodup
- \+ *lemma* fold_empty
- \+ *lemma* fold_insert
- \+ *lemma* fold_singleton
- \+ *lemma* fold_image
- \+ *lemma* fold_op_distrib
- \+ *lemma* fold_hom
- \+ *lemma* fold_union_inter
- \+ *def* fold

Modified data/list/set.lean
- \+ *theorem* mem_erase_iff_of_nodup
- \+/\- *theorem* mem_erase_of_nodup



## [2017-08-28 12:56:25-05:00](https://github.com/leanprover-community/mathlib/commit/1aa7efa)
Merge remote-tracking branch 'upstream/master'
#### Estimated changes



## [2017-08-27 20:58:30-04:00](https://github.com/leanprover-community/mathlib/commit/b031441)
feat(algebra): add small theory of big operators on commutative monoids
#### Estimated changes
Created algebra/big_operators.lean
- \+ *lemma* foldl_mul_assoc
- \+ *lemma* foldl_mul_eq_mul_foldr
- \+ *lemma* prod_eq_of_perm
- \+ *lemma* prod_empty
- \+ *lemma* prod_to_finset
- \+ *lemma* prod_insert
- \+ *lemma* prod_singleton
- \+ *lemma* prod_union_inter_eq
- \+ *lemma* prod_union
- \+ *lemma* prod_mul_distrib
- \+ *lemma* prod_image
- \+ *theorem* prod_nil
- \+ *theorem* prod_cons
- \+ *theorem* prod_append
- \+ *theorem* prod_join
- \+ *theorem* prod_replicate



## [2017-08-27 20:57:59-04:00](https://github.com/leanprover-community/mathlib/commit/c17d11b)
fix(data/finset): use the type class projections for insert; hide most constants using protected; add image of finset
#### Estimated changes
Modified data/finset/basic.lean
- \+ *lemma* erase_dup_map_erase_dup_eq
- \+ *lemma* image_to_finset
- \+ *lemma* image_to_finset_of_nodup
- \+ *lemma* image_id
- \+ *lemma* image_image
- \+/\- *theorem* card_empty
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* insert.comm
- \+/\- *theorem* perm_insert_cons_of_not_mem
- \+/\- *theorem* erase_insert
- \+/\- *theorem* union_empty
- \+/\- *theorem* empty_union
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+/\- *theorem* inter_empty
- \+/\- *theorem* empty_inter
- \+ *theorem* insert_inter_of_mem
- \+ *theorem* insert_inter_of_not_mem
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+/\- *theorem* empty_subset
- \+/\- *theorem* eq_empty_of_subset_empty
- \+/\- *theorem* subset_empty_iff
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* insert_subset_insert
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ
- \+/\- *def* to_nodup_list_of_nodup
- \- *def* empty
- \- *def* insert
- \- *def* union
- \- *def* inter
- \- *def* subset_aux
- \- *def* subset

Modified data/list/set.lean
- \+/\- *theorem* length_erase_of_not_mem
- \+ *theorem* nodup_map_on
- \+/\- *theorem* nodup_map



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/f2b4d2e)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* insert.comm
- \+/\- *theorem* erase_insert
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* insert_subset_insert
- \+/\- *theorem* upto_succ
- \+/\- *theorem* exists_mem_empty_iff
- \+/\- *theorem* exists_mem_insert_iff
- \+/\- *theorem* forall_mem_empty_iff
- \+/\- *theorem* forall_mem_insert_iff



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/79ed1c3)
refactor(data/finset): add type class instances
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* forall_of_forall_insert
- \+/\- *theorem* insert_eq
- \+/\- *theorem* upto_succ
- \+/\- *theorem* exists_mem_empty_iff
- \+/\- *theorem* exists_mem_insert_iff
- \+/\- *theorem* forall_mem_empty_iff
- \+/\- *theorem* forall_mem_insert_iff
- \- *theorem* mem_empty_eq
- \- *theorem* mem_insert_eq
- \- *theorem* mem_erase_eq
- \- *theorem* mem_union_eq
- \- *theorem* mem_inter_eq
- \- *theorem* mem_upto_eq
- \- *theorem* exists_mem_empty_eq
- \- *theorem* exists_mem_insert_eq
- \- *theorem* forall_mem_empty_eq
- \- *theorem* forall_mem_insert_eq



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/73ae11b)
refactor(data/finset): fix formatting issues
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* mem_empty_iff
- \+/\- *def* nodup_list
- \+/\- *def* finset
- \+/\- *def* subset_aux



## [2017-08-27 13:33:07-04:00](https://github.com/leanprover-community/mathlib/commit/8dbee5b)
feat(data/finset): add basics for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* mem_empty_iff
- \+ *theorem* mem_empty_eq
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_iff
- \+ *theorem* mem_insert_eq
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* forall_of_forall_insert
- \+/\- *theorem* insert.comm
- \+ *theorem* mem_erase_eq
- \+/\- *theorem* erase_insert
- \+ *theorem* mem_union_eq
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+ *theorem* mem_inter_eq
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* insert_subset_insert
- \+ *theorem* mem_upto_eq
- \+/\- *theorem* upto_succ
- \+/\- *theorem* exists_mem_empty_iff
- \+ *theorem* exists_mem_empty_eq
- \+/\- *theorem* exists_mem_insert_iff
- \+ *theorem* exists_mem_insert_eq
- \+/\- *theorem* forall_mem_empty_iff
- \+ *theorem* forall_mem_empty_eq
- \+/\- *theorem* forall_mem_insert_iff
- \+ *theorem* forall_mem_insert_eq
- \+/\- *def* nodup_list
- \+/\- *def* finset
- \+/\- *def* subset_aux



## [2017-08-27 12:30:11-05:00](https://github.com/leanprover-community/mathlib/commit/e678531)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq



## [2017-08-27 12:05:34-05:00](https://github.com/leanprover-community/mathlib/commit/b64eb68)
refactor(data/finset): use generic set notation for finsets
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* insert.comm
- \+/\- *theorem* erase_insert
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* insert_subset_insert
- \+/\- *theorem* upto_succ
- \+/\- *theorem* exists_mem_empty_iff
- \+/\- *theorem* exists_mem_insert_iff
- \+/\- *theorem* forall_mem_empty_iff
- \+/\- *theorem* forall_mem_insert_iff



## [2017-08-27 12:05:00-05:00](https://github.com/leanprover-community/mathlib/commit/5292cf1)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
Created data/finset/basic.lean
- \+ *lemma* to_finset_eq_of_nodup
- \+ *lemma* ne_empty_of_card_eq_succ
- \+ *theorem* mem_of_mem_list
- \+ *theorem* mem_list_of_mem
- \+ *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_of_nodup
- \+ *theorem* ext
- \+ *theorem* not_mem_empty
- \+ *theorem* mem_empty_iff
- \+ *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* card_empty
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* eq_of_singleton_eq
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* singleton_ne_empty
- \+ *theorem* pair_eq_singleton
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* insert.comm
- \+ *theorem* card_insert_of_mem
- \+ *theorem* card_insert_of_not_mem
- \+ *theorem* card_insert_le
- \+ *theorem* perm_insert_cons_of_not_mem
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* eq_empty_of_card_eq_zero
- \+ *theorem* not_mem_erase
- \+ *theorem* card_erase_of_mem
- \+ *theorem* card_erase_of_not_mem
- \+ *theorem* erase_empty
- \+ *theorem* ne_of_mem_erase
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_erase_iff
- \+ *theorem* erase_insert
- \+ *theorem* insert_erase
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_l
- \+ *theorem* mem_union_right
- \+ *theorem* mem_union_r
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union_iff
- \+ *theorem* union_comm
- \+ *theorem* union_assoc
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_self
- \+ *theorem* union_empty
- \+ *theorem* empty_union
- \+ *theorem* insert_eq
- \+ *theorem* insert_union
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter
- \+ *theorem* mem_inter_iff
- \+ *theorem* inter_comm
- \+ *theorem* inter_assoc
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_self
- \+ *theorem* inter_empty
- \+ *theorem* empty_inter
- \+ *theorem* singleton_inter_of_mem
- \+ *theorem* singleton_inter_of_not_mem
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* empty_subset
- \+ *theorem* subset.refl
- \+ *theorem* subset.trans
- \+ *theorem* mem_of_subset_of_mem
- \+ *theorem* subset.antisymm
- \+ *theorem* eq_of_subset_of_subset
- \+ *theorem* subset_of_forall
- \+ *theorem* subset_insert
- \+ *theorem* eq_empty_of_subset_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* erase_subset_erase
- \+ *theorem* erase_subset
- \+ *theorem* erase_eq_of_not_mem
- \+ *theorem* erase_insert_subset
- \+ *theorem* erase_subset_of_subset_insert
- \+ *theorem* insert_erase_subset
- \+ *theorem* insert_subset_insert
- \+ *theorem* subset_insert_of_erase_subset
- \+ *theorem* subset_insert_iff
- \+ *theorem* card_upto
- \+ *theorem* lt_of_mem_upto
- \+ *theorem* mem_upto_succ_of_mem_upto
- \+ *theorem* mem_upto_of_lt
- \+ *theorem* mem_upto_iff
- \+ *theorem* upto_zero
- \+ *theorem* upto_succ
- \+ *theorem* exists_mem_empty_iff
- \+ *theorem* exists_mem_insert_iff
- \+ *theorem* forall_mem_empty_iff
- \+ *theorem* forall_mem_insert_iff
- \+ *def* nodup_list
- \+ *def* to_nodup_list_of_nodup
- \+ *def* to_nodup_list
- \+ *def* finset
- \+ *def* to_finset_of_nodup
- \+ *def* to_finset
- \+ *def* mem
- \+ *def* empty
- \+ *def* card
- \+ *def* insert
- \+ *def* erase
- \+ *def* union
- \+ *def* inter
- \+ *def* subset_aux
- \+ *def* subset
- \+ *def* upto

Modified data/list/set.lean
- \+ *theorem* length_erase_of_not_mem



## [2017-08-27 12:26:42-04:00](https://github.com/leanprover-community/mathlib/commit/1f992c9)
fix(.): adapt to Lean changes: type class parameters to structures are now type class parameters in the projections and constructor
#### Estimated changes
Modified algebra/module.lean
- \+/\- *theorem* smul_left_distrib
- \+/\- *theorem* smul_right_distrib
- \+/\- *theorem* mul_smul

Modified data/fp/basic.lean
- \+/\- *def* default_nan

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
- \+ *lemma* no_top
- \+ *lemma* no_bot
- \+ *lemma* dense
- \+ *lemma* le_of_forall_le
- \+ *lemma* eq_of_le_of_forall_le
- \+ *lemma* le_of_forall_ge
- \+ *lemma* eq_of_le_of_forall_ge

Modified order/complete_lattice.lean
- \+ *lemma* infi_inf
- \+ *lemma* inf_infi
- \- *theorem* foo
- \- *theorem* foo'

Modified order/filter.lean
- \+ *lemma* tendsto_infi
- \+ *lemma* tendsto_infi'
- \+ *lemma* tendsto_principal_principal
- \+/\- *lemma* prod_mem_prod
- \+/\- *lemma* prod_same_eq
- \+/\- *lemma* mem_prod_iff
- \+ *lemma* prod_def
- \+ *lemma* prod_infi_left
- \+ *lemma* prod_infi_right
- \+/\- *lemma* mem_prod_same_iff
- \+/\- *lemma* prod_comm

Created topology/metric_space.lean
- \+ *lemma* exists_subtype
- \+ *lemma* dist_self
- \+ *lemma* eq_of_dist_eq_zero
- \+ *lemma* dist_comm
- \+ *lemma* dist_eq_zero_iff
- \+ *lemma* zero_eq_dist_iff
- \+ *lemma* dist_triangle
- \+ *lemma* uniformity_dist
- \+ *lemma* uniformity_dist'
- \+ *lemma* dist_nonneg
- \+ *lemma* dist_pos_of_ne
- \+ *lemma* ne_of_dist_pos
- \+ *lemma* eq_of_forall_dist_le
- \+ *lemma* uniform_continuous_dist'
- \+ *lemma* uniform_continuous_dist
- \+ *lemma* continuous_dist'
- \+ *lemma* continuous_dist
- \+ *lemma* tendsto_dist
- \+ *lemma* open_ball_subset_open_ball_of_le
- \+ *theorem* open_ball_eq_empty_of_nonpos
- \+ *theorem* pos_of_mem_open_ball
- \+ *theorem* mem_open_ball
- \+ *theorem* is_open_open_ball
- \+ *theorem* is_closed_closed_ball
- \+ *theorem* nhds_eq_metric
- \+ *theorem* mem_nhds_sets_iff_metric
- \+ *theorem* is_open_metric
- \+ *theorem* is_closed_metric
- \+ *theorem* uniform_continuous_metric_iff
- \+ *theorem* continuous_metric_iff
- \+ *def* dist
- \+ *def* open_ball
- \+ *def* closed_ball

Modified topology/real.lean
- \- *lemma* zero_lt_two

Modified topology/uniform_space.lean
- \+ *lemma* uniformity_prod_eq_prod



## [2017-08-26 15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/f1fba68)
feat(algebra): porting modules from lean2
#### Estimated changes
Created algebra/module.lean
- \+ *theorem* smul_left_distrib
- \+ *theorem* smul_right_distrib
- \+ *theorem* mul_smul
- \+ *theorem* one_smul
- \+ *theorem* zero_smul
- \+ *theorem* smul_zero
- \+ *theorem* neg_smul
- \+ *theorem* smul_neg
- \+ *theorem* smul_sub_left_distrib
- \+ *theorem* sub_smul_right_distrib
- \+ *def* ring.to_module



## [2017-08-26 15:40:07-04:00](https://github.com/leanprover-community/mathlib/commit/d1cbb8f)
fix(algebra/group): add every transport theorem from main Lean repository
#### Estimated changes
Modified algebra/group.lean


Deleted data/finset/basic.lean
- \- *lemma* to_finset_eq_of_nodup
- \- *lemma* ne_empty_of_card_eq_succ
- \- *theorem* mem_of_mem_list
- \- *theorem* mem_list_of_mem
- \- *theorem* mem_to_finset
- \- *theorem* mem_to_finset_of_nodup
- \- *theorem* ext
- \- *theorem* not_mem_empty
- \- *theorem* mem_empty_iff
- \- *theorem* eq_empty_of_forall_not_mem
- \- *theorem* card_empty
- \- *theorem* mem_insert
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* mem_of_mem_insert_of_ne
- \- *theorem* mem_insert_iff
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_singleton
- \- *theorem* mem_singleton_of_eq
- \- *theorem* eq_of_mem_singleton
- \- *theorem* eq_of_singleton_eq
- \- *theorem* insert_eq_of_mem
- \- *theorem* singleton_ne_empty
- \- *theorem* pair_eq_singleton
- \- *theorem* forall_of_forall_insert
- \- *theorem* insert.comm
- \- *theorem* card_insert_of_mem
- \- *theorem* card_insert_of_not_mem
- \- *theorem* card_insert_le
- \- *theorem* perm_insert_cons_of_not_mem
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* eq_empty_of_card_eq_zero
- \- *theorem* not_mem_erase
- \- *theorem* card_erase_of_mem
- \- *theorem* card_erase_of_not_mem
- \- *theorem* erase_empty
- \- *theorem* ne_of_mem_erase
- \- *theorem* mem_of_mem_erase
- \- *theorem* mem_erase_of_ne_of_mem
- \- *theorem* mem_erase_iff
- \- *theorem* erase_insert
- \- *theorem* insert_erase
- \- *theorem* mem_union_left
- \- *theorem* mem_union_l
- \- *theorem* mem_union_right
- \- *theorem* mem_union_r
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* mem_union_iff
- \- *theorem* union_comm
- \- *theorem* union_assoc
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* union_self
- \- *theorem* union_empty
- \- *theorem* empty_union
- \- *theorem* insert_eq
- \- *theorem* insert_union
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* mem_inter
- \- *theorem* mem_inter_iff
- \- *theorem* inter_comm
- \- *theorem* inter_assoc
- \- *theorem* inter_left_comm
- \- *theorem* inter_right_comm
- \- *theorem* inter_self
- \- *theorem* inter_empty
- \- *theorem* empty_inter
- \- *theorem* singleton_inter_of_mem
- \- *theorem* singleton_inter_of_not_mem
- \- *theorem* inter_distrib_left
- \- *theorem* inter_distrib_right
- \- *theorem* union_distrib_left
- \- *theorem* union_distrib_right
- \- *theorem* empty_subset
- \- *theorem* subset.refl
- \- *theorem* subset.trans
- \- *theorem* mem_of_subset_of_mem
- \- *theorem* subset.antisymm
- \- *theorem* eq_of_subset_of_subset
- \- *theorem* subset_of_forall
- \- *theorem* subset_insert
- \- *theorem* eq_empty_of_subset_empty
- \- *theorem* subset_empty_iff
- \- *theorem* erase_subset_erase
- \- *theorem* erase_subset
- \- *theorem* erase_eq_of_not_mem
- \- *theorem* erase_insert_subset
- \- *theorem* erase_subset_of_subset_insert
- \- *theorem* insert_erase_subset
- \- *theorem* insert_subset_insert
- \- *theorem* subset_insert_of_erase_subset
- \- *theorem* subset_insert_iff
- \- *theorem* card_upto
- \- *theorem* lt_of_mem_upto
- \- *theorem* mem_upto_succ_of_mem_upto
- \- *theorem* mem_upto_of_lt
- \- *theorem* mem_upto_iff
- \- *theorem* upto_zero
- \- *theorem* upto_succ
- \- *theorem* exists_mem_empty_iff
- \- *theorem* exists_mem_insert_iff
- \- *theorem* forall_mem_empty_iff
- \- *theorem* forall_mem_insert_iff
- \- *def* nodup_list
- \- *def* to_nodup_list_of_nodup
- \- *def* to_nodup_list
- \- *def* finset
- \- *def* to_finset_of_nodup
- \- *def* to_finset
- \- *def* mem
- \- *def* empty
- \- *def* card
- \- *def* insert
- \- *def* erase
- \- *def* union
- \- *def* inter
- \- *def* subset_aux
- \- *def* subset
- \- *def* upto

Modified data/list/set.lean
- \- *theorem* length_erase_of_not_mem

Modified topology/real.lean




## [2017-08-26 13:03:40-05:00](https://github.com/leanprover-community/mathlib/commit/67a2f39)
refactor(data/finset): add type class instances
#### Estimated changes
Modified data/finset/basic.lean
- \+/\- *theorem* mem_of_mem_list
- \+/\- *theorem* mem_list_of_mem
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* eq_of_singleton_eq
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* forall_of_forall_insert
- \+/\- *theorem* insert_eq
- \+/\- *theorem* upto_succ
- \+/\- *theorem* exists_mem_empty_iff
- \+/\- *theorem* exists_mem_insert_iff
- \+/\- *theorem* forall_mem_empty_iff
- \+/\- *theorem* forall_mem_insert_iff
- \- *theorem* mem_empty_eq
- \- *theorem* mem_insert_eq
- \- *theorem* mem_erase_eq
- \- *theorem* mem_union_eq
- \- *theorem* mem_inter_eq
- \- *theorem* mem_upto_eq
- \- *theorem* exists_mem_empty_eq
- \- *theorem* exists_mem_insert_eq
- \- *theorem* forall_mem_empty_eq
- \- *theorem* forall_mem_insert_eq



## [2017-08-26 12:24:58-05:00](https://github.com/leanprover-community/mathlib/commit/cde1bd8)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
Modified topology/continuity.lean
- \+ *lemma* is_open_prod
- \+ *lemma* is_open_prod_iff
- \- *lemma* is_open_set_prod

Modified topology/real.lean
- \+/\- *lemma* uniform_embedding_add_rat
- \+/\- *lemma* uniform_embedding_mul_rat
- \+/\- *lemma* nhds_0_eq_zero_nhd
- \+/\- *lemma* exists_supremum_real
- \- *lemma* continuous_add_rat
- \- *lemma* tendsto_add_rat
- \- *lemma* continuous_neg_rat
- \- *lemma* tendsto_neg_rat
- \- *lemma* is_open_lt
- \- *lemma* is_open_gt
- \- *lemma* is_closed_le
- \- *lemma* is_closed_ge
- \- *lemma* tendsto_mul_rat
- \- *lemma* continuous_neg_real
- \- *lemma* continuous_add_real'
- \- *lemma* continuous_add_real
- \- *lemma* continuous_sub_real
- \- *lemma* is_closed_le_real
- \- *lemma* is_open_lt_real

Created topology/topological_structures.lean
- \+ *lemma* dense_or_discrete
- \+ *lemma* continuous_add'
- \+ *lemma* continuous_add
- \+ *lemma* tendsto_add
- \+ *lemma* continuous_neg'
- \+ *lemma* continuous_neg
- \+ *lemma* tendsto_neg
- \+ *lemma* continuous_sub
- \+ *lemma* tendsto_sub
- \+ *lemma* continuous_mul
- \+ *lemma* tendsto_mul
- \+ *lemma* order_separated
- \+ *lemma* is_open_lt_fst_snd
- \+ *lemma* is_open_lt
- \+ *lemma* is_closed_le



## [2017-08-25 13:00:17-05:00](https://github.com/leanprover-community/mathlib/commit/dff0ffd)
refactor(data/finset): fix formatting issues
#### Estimated changes
Created data/finset/basic.lean
- \+ *lemma* to_finset_eq_of_nodup
- \+ *lemma* ne_empty_of_card_eq_succ
- \+ *theorem* mem_of_mem_list
- \+ *theorem* mem_list_of_mem
- \+ *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_of_nodup
- \+ *theorem* ext
- \+ *theorem* not_mem_empty
- \+ *theorem* mem_empty_iff
- \+ *theorem* mem_empty_eq
- \+ *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* card_empty
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* mem_insert_eq
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* eq_of_singleton_eq
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* singleton_ne_empty
- \+ *theorem* pair_eq_singleton
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* insert.comm
- \+ *theorem* card_insert_of_mem
- \+ *theorem* card_insert_of_not_mem
- \+ *theorem* card_insert_le
- \+ *theorem* perm_insert_cons_of_not_mem
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* eq_empty_of_card_eq_zero
- \+ *theorem* not_mem_erase
- \+ *theorem* card_erase_of_mem
- \+ *theorem* card_erase_of_not_mem
- \+ *theorem* erase_empty
- \+ *theorem* ne_of_mem_erase
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_erase_iff
- \+ *theorem* mem_erase_eq
- \+ *theorem* erase_insert
- \+ *theorem* insert_erase
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_l
- \+ *theorem* mem_union_right
- \+ *theorem* mem_union_r
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* union_comm
- \+ *theorem* union_assoc
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_self
- \+ *theorem* union_empty
- \+ *theorem* empty_union
- \+ *theorem* insert_eq
- \+ *theorem* insert_union
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter
- \+ *theorem* mem_inter_iff
- \+ *theorem* mem_inter_eq
- \+ *theorem* inter_comm
- \+ *theorem* inter_assoc
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_self
- \+ *theorem* inter_empty
- \+ *theorem* empty_inter
- \+ *theorem* singleton_inter_of_mem
- \+ *theorem* singleton_inter_of_not_mem
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* empty_subset
- \+ *theorem* subset.refl
- \+ *theorem* subset.trans
- \+ *theorem* mem_of_subset_of_mem
- \+ *theorem* subset.antisymm
- \+ *theorem* eq_of_subset_of_subset
- \+ *theorem* subset_of_forall
- \+ *theorem* subset_insert
- \+ *theorem* eq_empty_of_subset_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* erase_subset_erase
- \+ *theorem* erase_subset
- \+ *theorem* erase_eq_of_not_mem
- \+ *theorem* erase_insert_subset
- \+ *theorem* erase_subset_of_subset_insert
- \+ *theorem* insert_erase_subset
- \+ *theorem* insert_subset_insert
- \+ *theorem* subset_insert_of_erase_subset
- \+ *theorem* subset_insert_iff
- \+ *theorem* card_upto
- \+ *theorem* lt_of_mem_upto
- \+ *theorem* mem_upto_succ_of_mem_upto
- \+ *theorem* mem_upto_of_lt
- \+ *theorem* mem_upto_iff
- \+ *theorem* mem_upto_eq
- \+ *theorem* upto_zero
- \+ *theorem* upto_succ
- \+ *theorem* exists_mem_empty_iff
- \+ *theorem* exists_mem_empty_eq
- \+ *theorem* exists_mem_insert_iff
- \+ *theorem* exists_mem_insert_eq
- \+ *theorem* forall_mem_empty_iff
- \+ *theorem* forall_mem_empty_eq
- \+ *theorem* forall_mem_insert_iff
- \+ *theorem* forall_mem_insert_eq
- \+ *def* nodup_list
- \+ *def* to_nodup_list_of_nodup
- \+ *def* to_nodup_list
- \+ *def* finset
- \+ *def* to_finset_of_nodup
- \+ *def* to_finset
- \+ *def* mem
- \+ *def* empty
- \+ *def* card
- \+ *def* insert
- \+ *def* erase
- \+ *def* union
- \+ *def* inter
- \+ *def* subset_aux
- \+ *def* subset
- \+ *def* upto

Modified data/list/set.lean
- \+ *theorem* length_erase_of_not_mem

Modified topology/continuity.lean
- \+ *lemma* is_open_set_prod
- \- *lemma* is_open_prod
- \- *lemma* is_open_prod_iff

Modified topology/real.lean
- \+ *lemma* continuous_add_rat
- \+ *lemma* tendsto_add_rat
- \+ *lemma* continuous_neg_rat
- \+ *lemma* tendsto_neg_rat
- \+/\- *lemma* uniform_embedding_add_rat
- \+/\- *lemma* uniform_embedding_mul_rat
- \+/\- *lemma* nhds_0_eq_zero_nhd
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_gt
- \+ *lemma* is_closed_le
- \+ *lemma* is_closed_ge
- \+ *lemma* tendsto_mul_rat
- \+ *lemma* continuous_neg_real
- \+ *lemma* continuous_add_real'
- \+ *lemma* continuous_add_real
- \+ *lemma* continuous_sub_real
- \+ *lemma* is_closed_le_real
- \+ *lemma* is_open_lt_real
- \+/\- *lemma* exists_supremum_real

Deleted topology/topological_structures.lean
- \- *lemma* dense_or_discrete
- \- *lemma* continuous_add'
- \- *lemma* continuous_add
- \- *lemma* tendsto_add
- \- *lemma* continuous_neg'
- \- *lemma* continuous_neg
- \- *lemma* tendsto_neg
- \- *lemma* continuous_sub
- \- *lemma* tendsto_sub
- \- *lemma* continuous_mul
- \- *lemma* tendsto_mul
- \- *lemma* order_separated
- \- *lemma* is_open_lt_fst_snd
- \- *lemma* is_open_lt
- \- *lemma* is_closed_le



## [2017-08-24 19:09:36-04:00](https://github.com/leanprover-community/mathlib/commit/7c72de2)
feat(topology): add topological structures for groups, ring, and linear orders; add instances for rat and real
#### Estimated changes
Deleted data/finset/basic.lean
- \- *lemma* to_finset_eq_of_nodup
- \- *lemma* ne_empty_of_card_eq_succ
- \- *theorem* mem_of_mem_list
- \- *theorem* mem_list_of_mem
- \- *theorem* mem_to_finset
- \- *theorem* mem_to_finset_of_nodup
- \- *theorem* ext
- \- *theorem* not_mem_empty
- \- *theorem* mem_empty_iff
- \- *theorem* mem_empty_eq
- \- *theorem* eq_empty_of_forall_not_mem
- \- *theorem* card_empty
- \- *theorem* mem_insert
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* mem_of_mem_insert_of_ne
- \- *theorem* mem_insert_iff
- \- *theorem* mem_insert_eq
- \- *theorem* mem_singleton_iff
- \- *theorem* mem_singleton
- \- *theorem* mem_singleton_of_eq
- \- *theorem* eq_of_mem_singleton
- \- *theorem* eq_of_singleton_eq
- \- *theorem* insert_eq_of_mem
- \- *theorem* singleton_ne_empty
- \- *theorem* pair_eq_singleton
- \- *theorem* forall_of_forall_insert
- \- *theorem* insert.comm
- \- *theorem* card_insert_of_mem
- \- *theorem* card_insert_of_not_mem
- \- *theorem* card_insert_le
- \- *theorem* perm_insert_cons_of_not_mem
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* eq_empty_of_card_eq_zero
- \- *theorem* not_mem_erase
- \- *theorem* card_erase_of_mem
- \- *theorem* card_erase_of_not_mem
- \- *theorem* erase_empty
- \- *theorem* ne_of_mem_erase
- \- *theorem* mem_of_mem_erase
- \- *theorem* mem_erase_of_ne_of_mem
- \- *theorem* mem_erase_iff
- \- *theorem* mem_erase_eq
- \- *theorem* erase_insert
- \- *theorem* insert_erase
- \- *theorem* mem_union_left
- \- *theorem* mem_union_l
- \- *theorem* mem_union_right
- \- *theorem* mem_union_r
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* mem_union_iff
- \- *theorem* mem_union_eq
- \- *theorem* union_comm
- \- *theorem* union_assoc
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* union_self
- \- *theorem* union_empty
- \- *theorem* empty_union
- \- *theorem* insert_eq
- \- *theorem* insert_union
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* mem_inter
- \- *theorem* mem_inter_iff
- \- *theorem* mem_inter_eq
- \- *theorem* inter_comm
- \- *theorem* inter_assoc
- \- *theorem* inter_left_comm
- \- *theorem* inter_right_comm
- \- *theorem* inter_self
- \- *theorem* inter_empty
- \- *theorem* empty_inter
- \- *theorem* singleton_inter_of_mem
- \- *theorem* singleton_inter_of_not_mem
- \- *theorem* inter_distrib_left
- \- *theorem* inter_distrib_right
- \- *theorem* union_distrib_left
- \- *theorem* union_distrib_right
- \- *theorem* empty_subset
- \- *theorem* subset.refl
- \- *theorem* subset.trans
- \- *theorem* mem_of_subset_of_mem
- \- *theorem* subset.antisymm
- \- *theorem* eq_of_subset_of_subset
- \- *theorem* subset_of_forall
- \- *theorem* subset_insert
- \- *theorem* eq_empty_of_subset_empty
- \- *theorem* subset_empty_iff
- \- *theorem* erase_subset_erase
- \- *theorem* erase_subset
- \- *theorem* erase_eq_of_not_mem
- \- *theorem* erase_insert_subset
- \- *theorem* erase_subset_of_subset_insert
- \- *theorem* insert_erase_subset
- \- *theorem* insert_subset_insert
- \- *theorem* subset_insert_of_erase_subset
- \- *theorem* subset_insert_iff
- \- *theorem* card_upto
- \- *theorem* lt_of_mem_upto
- \- *theorem* mem_upto_succ_of_mem_upto
- \- *theorem* mem_upto_of_lt
- \- *theorem* mem_upto_iff
- \- *theorem* mem_upto_eq
- \- *theorem* upto_zero
- \- *theorem* upto_succ
- \- *theorem* exists_mem_empty_iff
- \- *theorem* exists_mem_empty_eq
- \- *theorem* exists_mem_insert_iff
- \- *theorem* exists_mem_insert_eq
- \- *theorem* forall_mem_empty_iff
- \- *theorem* forall_mem_empty_eq
- \- *theorem* forall_mem_insert_iff
- \- *theorem* forall_mem_insert_eq
- \- *def* nodup_list
- \- *def* to_nodup_list_of_nodup
- \- *def* to_nodup_list
- \- *def* finset
- \- *def* to_finset_of_nodup
- \- *def* to_finset
- \- *def* mem
- \- *def* empty
- \- *def* card
- \- *def* insert
- \- *def* erase
- \- *def* union
- \- *def* inter
- \- *def* subset_aux
- \- *def* subset
- \- *def* upto

Modified data/list/set.lean
- \- *theorem* length_erase_of_not_mem

Modified topology/continuity.lean
- \+ *lemma* is_open_prod
- \+ *lemma* is_open_prod_iff
- \- *lemma* is_open_set_prod

Modified topology/real.lean
- \+/\- *lemma* uniform_embedding_add_rat
- \+/\- *lemma* uniform_embedding_mul_rat
- \+/\- *lemma* nhds_0_eq_zero_nhd
- \+/\- *lemma* exists_supremum_real
- \- *lemma* continuous_add_rat
- \- *lemma* tendsto_add_rat
- \- *lemma* continuous_neg_rat
- \- *lemma* tendsto_neg_rat
- \- *lemma* is_open_lt
- \- *lemma* is_open_gt
- \- *lemma* is_closed_le
- \- *lemma* is_closed_ge
- \- *lemma* tendsto_mul_rat
- \- *lemma* continuous_neg_real
- \- *lemma* continuous_add_real'
- \- *lemma* continuous_add_real
- \- *lemma* continuous_sub_real
- \- *lemma* is_closed_le_real
- \- *lemma* is_open_lt_real

Created topology/topological_structures.lean
- \+ *lemma* dense_or_discrete
- \+ *lemma* continuous_add'
- \+ *lemma* continuous_add
- \+ *lemma* tendsto_add
- \+ *lemma* continuous_neg'
- \+ *lemma* continuous_neg
- \+ *lemma* tendsto_neg
- \+ *lemma* continuous_sub
- \+ *lemma* tendsto_sub
- \+ *lemma* continuous_mul
- \+ *lemma* tendsto_mul
- \+ *lemma* order_separated
- \+ *lemma* is_open_lt_fst_snd
- \+ *lemma* is_open_lt
- \+ *lemma* is_closed_le



## [2017-08-24 16:21:01-05:00](https://github.com/leanprover-community/mathlib/commit/7df585e)
feat(data/finset): add basics for finsets
#### Estimated changes
Created data/finset/basic.lean
- \+ *lemma* to_finset_eq_of_nodup
- \+ *lemma* ne_empty_of_card_eq_succ
- \+ *theorem* mem_of_mem_list
- \+ *theorem* mem_list_of_mem
- \+ *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_of_nodup
- \+ *theorem* ext
- \+ *theorem* not_mem_empty
- \+ *theorem* mem_empty_iff
- \+ *theorem* mem_empty_eq
- \+ *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* card_empty
- \+ *theorem* mem_insert
- \+ *theorem* mem_insert_of_mem
- \+ *theorem* eq_or_mem_of_mem_insert
- \+ *theorem* mem_of_mem_insert_of_ne
- \+ *theorem* mem_insert_iff
- \+ *theorem* mem_insert_eq
- \+ *theorem* mem_singleton_iff
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_of_eq
- \+ *theorem* eq_of_mem_singleton
- \+ *theorem* eq_of_singleton_eq
- \+ *theorem* insert_eq_of_mem
- \+ *theorem* singleton_ne_empty
- \+ *theorem* pair_eq_singleton
- \+ *theorem* forall_of_forall_insert
- \+ *theorem* insert.comm
- \+ *theorem* card_insert_of_mem
- \+ *theorem* card_insert_of_not_mem
- \+ *theorem* card_insert_le
- \+ *theorem* perm_insert_cons_of_not_mem
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* eq_empty_of_card_eq_zero
- \+ *theorem* not_mem_erase
- \+ *theorem* card_erase_of_mem
- \+ *theorem* card_erase_of_not_mem
- \+ *theorem* erase_empty
- \+ *theorem* ne_of_mem_erase
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_erase_iff
- \+ *theorem* mem_erase_eq
- \+ *theorem* erase_insert
- \+ *theorem* insert_erase
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_l
- \+ *theorem* mem_union_right
- \+ *theorem* mem_union_r
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* mem_union_iff
- \+ *theorem* mem_union_eq
- \+ *theorem* union_comm
- \+ *theorem* union_assoc
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_self
- \+ *theorem* union_empty
- \+ *theorem* empty_union
- \+ *theorem* insert_eq
- \+ *theorem* insert_union
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter
- \+ *theorem* mem_inter_iff
- \+ *theorem* mem_inter_eq
- \+ *theorem* inter_comm
- \+ *theorem* inter_assoc
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_self
- \+ *theorem* inter_empty
- \+ *theorem* empty_inter
- \+ *theorem* singleton_inter_of_mem
- \+ *theorem* singleton_inter_of_not_mem
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* empty_subset
- \+ *theorem* subset.refl
- \+ *theorem* subset.trans
- \+ *theorem* mem_of_subset_of_mem
- \+ *theorem* subset.antisymm
- \+ *theorem* eq_of_subset_of_subset
- \+ *theorem* subset_of_forall
- \+ *theorem* subset_insert
- \+ *theorem* eq_empty_of_subset_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* erase_subset_erase
- \+ *theorem* erase_subset
- \+ *theorem* erase_eq_of_not_mem
- \+ *theorem* erase_insert_subset
- \+ *theorem* erase_subset_of_subset_insert
- \+ *theorem* insert_erase_subset
- \+ *theorem* insert_subset_insert
- \+ *theorem* subset_insert_of_erase_subset
- \+ *theorem* subset_insert_iff
- \+ *theorem* card_upto
- \+ *theorem* lt_of_mem_upto
- \+ *theorem* mem_upto_succ_of_mem_upto
- \+ *theorem* mem_upto_of_lt
- \+ *theorem* mem_upto_iff
- \+ *theorem* mem_upto_eq
- \+ *theorem* upto_zero
- \+ *theorem* upto_succ
- \+ *theorem* exists_mem_empty_iff
- \+ *theorem* exists_mem_empty_eq
- \+ *theorem* exists_mem_insert_iff
- \+ *theorem* exists_mem_insert_eq
- \+ *theorem* forall_mem_empty_iff
- \+ *theorem* forall_mem_empty_eq
- \+ *theorem* forall_mem_insert_iff
- \+ *theorem* forall_mem_insert_eq
- \+ *def* nodup_list
- \+ *def* to_nodup_list_of_nodup
- \+ *def* to_nodup_list
- \+ *def* finset
- \+ *def* to_finset_of_nodup
- \+ *def* to_finset
- \+ *def* mem
- \+ *def* empty
- \+ *def* card
- \+ *def* insert
- \+ *def* erase
- \+ *def* union
- \+ *def* inter
- \+ *def* subset_aux
- \+ *def* subset
- \+ *def* upto

Modified data/list/set.lean
- \+ *theorem* length_erase_of_not_mem



## [2017-08-24 13:50:09-04:00](https://github.com/leanprover-community/mathlib/commit/33b22b0)
data/option: add filter
#### Estimated changes
Modified data/option.lean
- \+ *def* filter



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
- \+ *lemma* mem_zero_nhd_le
- \+/\- *lemma* tendsto_mul_bnd_rat
- \+ *lemma* le_mem_nhds
- \+ *lemma* ge_mem_nhds
- \+/\- *lemma* uniform_continuous_rat'
- \+/\- *lemma* uniform_continuous_abs_rat
- \+/\- *lemma* continuous_abs_rat
- \+ *lemma* closure_of_rat_image_le_eq
- \+ *lemma* closure_of_rat_image_le_le_eq
- \+ *lemma* exists_pos_of_rat
- \- *lemma* closure_of_rat_image_eq



## [2017-08-23 16:41:48-04:00](https://github.com/leanprover-community/mathlib/commit/d708489)
adapt to Lean changes
#### Estimated changes
Modified theories/set_theory.lean




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
Created tactic/default.lean


Created tactic/interactive.lean


Created tactic/rcases.lean
- \+ *def* rcases_patt.name



## [2017-08-16 14:06:45-07:00](https://github.com/leanprover-community/mathlib/commit/fb6bab2)
fix(data/list/perm): pending issues
#### Estimated changes
Modified data/list/perm.lean
- \+/\- *theorem* perm_app_cons
- \+/\- *theorem* subset_of_mem_of_subset_of_qeq
- \+/\- *def* decidable_perm_aux
- \+/\- *def* decidable_perm



## [2017-08-16 14:05:41-07:00](https://github.com/leanprover-community/mathlib/commit/11bcaeb)
refactor(data/lazy_list): lazy_list was moved back to core lib
#### Estimated changes
Deleted data/lazy_list.lean
- \- *def* singleton
- \- *def* of_list
- \- *def* to_list
- \- *def* head
- \- *def* tail
- \- *def* append
- \- *def* map
- \- *def* map₂
- \- *def* zip
- \- *def* join
- \- *def* for
- \- *def* approx
- \- *def* filter
- \- *def* nth



## [2017-08-16 13:48:22-07:00](https://github.com/leanprover-community/mathlib/commit/af0b10c)
fix(data/num/basic): vector and bitvec are not in the init folder anymore
#### Estimated changes
Modified data/num/basic.lean




## [2017-08-16 13:47:32-07:00](https://github.com/leanprover-community/mathlib/commit/9b2b11f)
refactor(data): stream library was moved back to core lib
#### Estimated changes
Deleted data/stream.lean
- \- *theorem* nth_zero_cons
- \- *theorem* head_cons
- \- *theorem* tail_cons
- \- *theorem* tail_drop
- \- *theorem* nth_drop
- \- *theorem* tail_eq_drop
- \- *theorem* drop_drop
- \- *theorem* nth_succ
- \- *theorem* drop_succ
- \- *theorem* all_def
- \- *theorem* any_def
- \- *theorem* mem_cons
- \- *theorem* mem_cons_of_mem
- \- *theorem* eq_or_mem_of_mem_cons
- \- *theorem* mem_of_nth_eq
- \- *theorem* drop_map
- \- *theorem* nth_map
- \- *theorem* tail_map
- \- *theorem* head_map
- \- *theorem* map_eq
- \- *theorem* map_cons
- \- *theorem* map_id
- \- *theorem* map_map
- \- *theorem* map_tail
- \- *theorem* mem_map
- \- *theorem* exists_of_mem_map
- \- *theorem* drop_zip
- \- *theorem* nth_zip
- \- *theorem* head_zip
- \- *theorem* tail_zip
- \- *theorem* zip_eq
- \- *theorem* mem_const
- \- *theorem* const_eq
- \- *theorem* tail_const
- \- *theorem* map_const
- \- *theorem* nth_const
- \- *theorem* drop_const
- \- *theorem* head_iterate
- \- *theorem* tail_iterate
- \- *theorem* iterate_eq
- \- *theorem* nth_zero_iterate
- \- *theorem* nth_succ_iterate
- \- *theorem* bisim_simple
- \- *theorem* coinduction
- \- *theorem* iterate_id
- \- *theorem* map_iterate
- \- *theorem* corec_def
- \- *theorem* corec_eq
- \- *theorem* corec_id_id_eq_const
- \- *theorem* corec_id_f_eq_iterate
- \- *theorem* corec'_eq
- \- *theorem* unfolds_eq
- \- *theorem* nth_unfolds_head_tail
- \- *theorem* unfolds_head_eq
- \- *theorem* interleave_eq
- \- *theorem* tail_interleave
- \- *theorem* interleave_tail_tail
- \- *theorem* nth_interleave_left
- \- *theorem* nth_interleave_right
- \- *theorem* mem_interleave_left
- \- *theorem* mem_interleave_right
- \- *theorem* odd_eq
- \- *theorem* head_even
- \- *theorem* tail_even
- \- *theorem* even_cons_cons
- \- *theorem* even_tail
- \- *theorem* even_interleave
- \- *theorem* interleave_even_odd
- \- *theorem* nth_even
- \- *theorem* nth_odd
- \- *theorem* mem_of_mem_even
- \- *theorem* mem_of_mem_odd
- \- *theorem* nil_append_stream
- \- *theorem* cons_append_stream
- \- *theorem* append_append_stream
- \- *theorem* map_append_stream
- \- *theorem* drop_append_stream
- \- *theorem* append_stream_head_tail
- \- *theorem* mem_append_stream_right
- \- *theorem* mem_append_stream_left
- \- *theorem* approx_zero
- \- *theorem* approx_succ
- \- *theorem* nth_approx
- \- *theorem* append_approx_drop
- \- *theorem* take_theorem
- \- *theorem* cycle_eq
- \- *theorem* mem_cycle
- \- *theorem* cycle_singleton
- \- *theorem* tails_eq
- \- *theorem* nth_tails
- \- *theorem* tails_eq_iterate
- \- *theorem* inits_core_eq
- \- *theorem* tail_inits
- \- *theorem* inits_tail
- \- *theorem* cons_nth_inits_core
- \- *theorem* nth_inits
- \- *theorem* inits_eq
- \- *theorem* zip_inits_tails
- \- *theorem* identity
- \- *theorem* composition
- \- *theorem* homomorphism
- \- *theorem* interchange
- \- *theorem* map_eq_apply
- \- *theorem* nth_nats
- \- *theorem* nats_eq
- \- *def* stream
- \- *def* cons
- \- *def* head
- \- *def* tail
- \- *def* drop
- \- *def* nth
- \- *def* all
- \- *def* any
- \- *def* map
- \- *def* zip
- \- *def* const
- \- *def* iterate
- \- *def* corec
- \- *def* corec_on
- \- *def* corec'
- \- *def* unfolds
- \- *def* interleave
- \- *def* even
- \- *def* odd
- \- *def* append_stream
- \- *def* approx
- \- *def* cycle
- \- *def* tails
- \- *def* inits_core
- \- *def* inits
- \- *def* pure
- \- *def* apply
- \- *def* nats



## [2017-08-11 19:03:01-04:00](https://github.com/leanprover-community/mathlib/commit/6d90728)
use Galois connections in filter library
#### Estimated changes
Modified order/filter.lean
- \+/\- *lemma* mem_map
- \+/\- *lemma* image_mem_map
- \+/\- *lemma* map_id
- \+/\- *lemma* map_compose
- \+/\- *lemma* map_map
- \+ *lemma* vmap_id
- \+/\- *lemma* vmap_vmap_comp
- \+ *lemma* map_le_iff_vmap_le
- \+ *lemma* gc_map_vmap
- \+/\- *lemma* map_mono
- \+/\- *lemma* monotone_map
- \+/\- *lemma* vmap_mono
- \+/\- *lemma* monotone_vmap
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* vmap_top
- \+/\- *lemma* vmap_inf
- \+/\- *lemma* vmap_infi
- \+/\- *lemma* map_vmap_le
- \+/\- *lemma* le_vmap_map
- \+/\- *lemma* vmap_bot
- \+/\- *lemma* vmap_sup
- \+/\- *lemma* le_map_vmap'
- \+/\- *lemma* le_map_vmap
- \+/\- *lemma* vmap_map
- \+/\- *lemma* map_inj
- \+/\- *lemma* vmap_neq_bot
- \+/\- *lemma* vmap_neq_bot_of_surj
- \+/\- *lemma* le_vmap_iff_map_le
- \+/\- *lemma* map_eq_bot_iff
- \+/\- *lemma* map_ne_bot
- \- *lemma* supr_map
- \+/\- *theorem* mem_vmap
- \+/\- *theorem* preimage_mem_vmap
- \+/\- *theorem* vmap_principal

Modified topology/topological_space.lean




## [2017-08-11 18:26:35-04:00](https://github.com/leanprover-community/mathlib/commit/ce09c18)
add Galois connection, also add a couple of order theoretic results
#### Estimated changes
Modified order/basic.lean
- \+ *def* preorder_dual

Created order/bounds.lean
- \+ *lemma* mem_upper_bounds_image
- \+ *lemma* mem_lower_bounds_image
- \+ *lemma* is_lub_singleton
- \+ *lemma* is_glb_singleton
- \+ *lemma* eq_of_is_least_of_is_least
- \+ *lemma* is_least_iff_eq_of_is_least
- \+ *lemma* eq_of_is_greatest_of_is_greatest
- \+ *lemma* is_greatest_iff_eq_of_is_greatest
- \+ *lemma* eq_of_is_lub_of_is_lub
- \+ *lemma* is_lub_iff_eq_of_is_lub
- \+ *lemma* eq_of_is_glb_of_is_glb
- \+ *lemma* is_glb_iff_eq_of_is_glb
- \+ *lemma* is_glb_empty
- \+ *lemma* is_lub_empty
- \+ *lemma* is_lub_union_sup
- \+ *lemma* is_glb_union_inf
- \+ *lemma* is_lub_insert_sup
- \+ *lemma* is_lub_iff_sup_eq
- \+ *lemma* is_glb_insert_inf
- \+ *lemma* is_glb_iff_inf_eq
- \+ *lemma* is_lub_Sup
- \+ *lemma* is_lub_supr
- \+ *lemma* is_lub_iff_supr_eq
- \+ *lemma* is_lub_iff_Sup_eq
- \+ *lemma* is_glb_Inf
- \+ *lemma* is_glb_infi
- \+ *lemma* is_glb_iff_infi_eq
- \+ *lemma* is_glb_iff_Inf_eq

Modified order/default.lean


Created order/galois_connection.lean
- \+ *lemma* monotone_intro
- \+ *lemma* l_le
- \+ *lemma* le_u
- \+ *lemma* increasing_u_l
- \+ *lemma* decreasing_l_u
- \+ *lemma* monotone_u
- \+ *lemma* monotone_l
- \+ *lemma* upper_bounds_l_image_subset
- \+ *lemma* lower_bounds_u_image_subset
- \+ *lemma* is_lub_l_image
- \+ *lemma* is_glb_u_image
- \+ *lemma* is_glb_l
- \+ *lemma* is_lub_u
- \+ *lemma* u_l_u_eq_u
- \+ *lemma* l_u_l_eq_l
- \+ *lemma* u_top
- \+ *lemma* l_bot
- \+ *lemma* l_sup
- \+ *lemma* u_inf
- \+ *lemma* l_supr
- \+ *lemma* u_infi
- \+ *lemma* galois_connection_mul_div
- \+ *def* galois_connection



## [2017-08-11 18:14:46-04:00](https://github.com/leanprover-community/mathlib/commit/2e8bd34)
add set.range function
`range` is stronger than `f '' univ`, as `f` can be a function from an arbitrary `Sort` instead of `Type`
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* mem_range
- \+ *lemma* forall_range_iff
- \+ *lemma* range_of_surjective
- \+ *lemma* range_id
- \+ *lemma* range_compose
- \+ *def* range

Modified order/complete_lattice.lean
- \+ *lemma* Sup_range
- \+ *lemma* Inf_range
- \+ *lemma* supr_range
- \+ *lemma* infi_range
- \+/\- *theorem* Inf_image
- \+/\- *theorem* Sup_image



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


Created order/default.lean


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
- \+ *lemma* eq_of_sup_eq_inf_eq
- \+ *lemma* inf_eq_bot_iff_le_compl

Modified algebra/lattice/filter.lean
- \- *lemma* classical.cases
- \- *lemma* false_neq_true
- \- *lemma* pure_seq_eq_map
- \- *lemma* map_bind
- \- *lemma* seq_bind_eq
- \- *lemma* seq_eq_bind_map
- \- *lemma* bind_assoc
- \- *lemma* prod.mk.eta
- \- *lemma* prod.swap_swap
- \- *lemma* prod.fst_swap
- \- *lemma* prod.snd_swap
- \- *lemma* prod.swap_prod_mk
- \- *lemma* prod.swap_swap_eq
- \- *lemma* bind_def
- \- *lemma* ne_empty_iff_exists_mem
- \- *lemma* fmap_eq_image
- \- *lemma* mem_seq_iff
- \- *lemma* univ_eq_true_false
- \- *lemma* not_eq_empty_iff_exists
- \- *lemma* image_inter
- \- *lemma* image_Union
- \- *lemma* image_singleton
- \- *lemma* mem_prod_eq
- \- *lemma* prod_mono
- \- *lemma* prod_inter_prod
- \- *lemma* image_swap_prod
- \- *lemma* prod_image_image_eq
- \- *lemma* prod_singleton_singleton
- \- *lemma* prod_neq_empty_iff
- \- *lemma* prod_mk_mem_set_prod_eq
- \- *lemma* set_of_mem_eq
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
- \- *lemma* not_or_iff_implies
- \- *theorem* prod_preimage_eq
- \- *theorem* monotone_prod
- \- *theorem* preimage_set_of_eq
- \- *theorem* image_swap_eq_preimage_swap
- \- *def* prod.swap

Created category/basic.lean
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* map_bind
- \+ *lemma* seq_bind_eq
- \+ *lemma* seq_eq_bind_map
- \+ *lemma* bind_assoc

Created data/prod.lean
- \+ *lemma* prod.mk.eta
- \+ *lemma* prod.swap_swap
- \+ *lemma* prod.fst_swap
- \+ *lemma* prod.snd_swap
- \+ *lemma* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap_eq
- \+ *def* prod.swap

Modified data/set/basic.lean
- \+ *lemma* mem_of_mem_of_subset
- \+ *lemma* set_of_mem_eq
- \+ *lemma* not_not_mem_iff
- \+ *lemma* ne_empty_iff_exists_mem
- \+ *lemma* not_eq_empty_iff_exists
- \+ *lemma* compl_subset_of_compl_subset
- \+ *lemma* diff_subset_diff
- \+ *lemma* diff_right_antimono
- \+ *lemma* diff_neq_empty
- \+ *lemma* diff_empty
- \+ *lemma* image_inter
- \+ *lemma* image_singleton
- \+ *lemma* compl_image_set_of
- \+ *lemma* univ_eq_true_false
- \+/\- *theorem* singleton_ne_empty
- \+ *theorem* preimage_set_of_eq

Modified data/set/default.lean


Modified data/set/lattice.lean
- \+ *lemma* sUnion_mono
- \+ *lemma* Union_subset_Union
- \+ *lemma* Union_subset_Union2
- \+ *lemma* Union_subset_Union_const
- \+ *lemma* sUnion_eq_Union
- \+ *lemma* compl_subset_compl_iff_subset
- \+ *lemma* image_Union
- \+ *lemma* univ_subtype
- \+ *lemma* bind_def
- \+ *lemma* fmap_eq_image
- \+ *lemma* mem_seq_iff

Created data/set/prod.lean
- \+ *lemma* mem_prod_eq
- \+ *lemma* prod_mono
- \+ *lemma* prod_inter_prod
- \+ *lemma* image_swap_prod
- \+ *lemma* prod_image_image_eq
- \+ *lemma* prod_singleton_singleton
- \+ *lemma* prod_neq_empty_iff
- \+ *lemma* prod_mk_mem_set_prod_eq
- \+ *theorem* prod_preimage_eq
- \+ *theorem* monotone_prod
- \+ *theorem* image_swap_eq_preimage_swap

Modified logic/basic.lean
- \+ *lemma* false_neq_true
- \+ *lemma* {u
- \+ *lemma* cases
- \+ *theorem* not_and_iff_imp_not

Modified topology/topological_space.lean
- \- *lemma* compl_subset_of_compl_subset
- \- *lemma* not_and_iff_imp_not
- \- *lemma* diff_subset_diff
- \- *lemma* mem_of_mem_of_subset
- \- *lemma* univ_subtype

Modified topology/uniform_space.lean




## [2017-08-10 16:50:12-04:00](https://github.com/leanprover-community/mathlib/commit/178e746)
rename towards -> tendsto
#### Estimated changes
Modified algebra/lattice/filter.lean
- \+ *lemma* tendsto_cong
- \+ *lemma* tendsto_id'
- \+ *lemma* tendsto_id
- \+ *lemma* tendsto_compose
- \+ *lemma* tendsto_map
- \+ *lemma* tendsto_map'
- \+ *lemma* tendsto_vmap
- \+ *lemma* tendsto_vmap'
- \+ *lemma* tendsto_vmap''
- \+ *lemma* tendsto_inf
- \+ *lemma* tendsto_fst
- \+ *lemma* tendsto_snd
- \+ *lemma* tendsto_prod_mk
- \- *lemma* towards_cong
- \- *lemma* towards_id'
- \- *lemma* towards_id
- \- *lemma* towards_compose
- \- *lemma* towards_map
- \- *lemma* towards_map'
- \- *lemma* towards_vmap
- \- *lemma* towards_vmap'
- \- *lemma* towards_vmap''
- \- *lemma* towards_inf
- \- *lemma* towards_fst
- \- *lemma* towards_snd
- \- *lemma* towards_prod_mk
- \+ *def* tendsto
- \- *def* towards

Modified topology/continuity.lean
- \+ *lemma* continuous_iff_tendsto
- \+ *lemma* tendsto_nhds_iff_of_embedding
- \+ *lemma* tendsto_ext
- \- *lemma* continuous_iff_towards
- \- *lemma* towards_nhds_iff_of_embedding
- \- *lemma* towards_ext

Modified topology/real.lean
- \+ *lemma* tendsto_zero_nhds
- \+ *lemma* tendsto_neg_rat_zero
- \+ *lemma* tendsto_add_rat_zero
- \+ *lemma* tendsto_add_rat_zero'
- \+ *lemma* tendsto_sub_rat'
- \+ *lemma* tendsto_mul_bnd_rat
- \+ *lemma* tendsto_mul_bnd_rat'
- \+ *lemma* tendsto_mul_rat'
- \+ *lemma* tendsto_sub_uniformity_zero_nhd
- \+ *lemma* tendsto_sub_uniformity_zero_nhd'
- \+ *lemma* tendsto_add_rat
- \+ *lemma* tendsto_neg_rat
- \+ *lemma* tendsto_of_uniform_continuous_subtype
- \+ *lemma* tendsto_inv_pos_rat
- \+ *lemma* tendsto_inv_rat
- \+ *lemma* tendsto_mul_rat
- \+/\- *lemma* lift_rat_fun_of_rat
- \+/\- *lemma* of_rat_zero
- \+/\- *lemma* of_rat_one
- \+/\- *lemma* of_rat_neg
- \+/\- *lemma* of_rat_add
- \+/\- *lemma* of_rat_sub
- \+/\- *lemma* of_rat_mul
- \+/\- *lemma* of_rat_inv
- \+ *lemma* tendsto_inv_real
- \- *lemma* towards_zero_nhds
- \- *lemma* towards_neg_rat_zero
- \- *lemma* towards_add_rat_zero
- \- *lemma* towards_add_rat_zero'
- \- *lemma* towards_sub_rat'
- \- *lemma* towards_mul_bnd_rat
- \- *lemma* towards_mul_bnd_rat'
- \- *lemma* towards_mul_rat'
- \- *lemma* towards_sub_uniformity_zero_nhd
- \- *lemma* towards_sub_uniformity_zero_nhd'
- \- *lemma* towards_add_rat
- \- *lemma* towards_neg_rat
- \- *lemma* towards_of_uniform_continuous_subtype
- \- *lemma* towards_inv_pos_rat
- \- *lemma* towards_inv_rat
- \- *lemma* towards_mul_rat
- \- *lemma* towards_inv_real

Modified topology/topological_space.lean
- \+ *lemma* tendsto_nhds
- \+ *lemma* tendsto_const_nhds
- \+ *lemma* tendsto_nhds_unique
- \- *lemma* towards_nhds
- \- *lemma* towards_const_nhds
- \- *lemma* towards_nhds_unique

Modified topology/uniform_space.lean
- \+ *lemma* tendsto_swap_uniformity
- \+ *lemma* tendsto_const_uniformity
- \+ *lemma* tendsto_right_nhds_uniformity
- \+ *lemma* tendsto_left_nhds_uniformity
- \+ *lemma* tendsto_prod_uniformity_fst
- \+ *lemma* tendsto_prod_uniformity_snd
- \- *lemma* towards_swap_uniformity
- \- *lemma* towards_const_uniformity
- \- *lemma* towards_right_nhds_uniformity
- \- *lemma* towards_left_nhds_uniformity
- \- *lemma* towards_prod_uniformity_fst
- \- *lemma* towards_prod_uniformity_snd



## [2017-08-10 16:41:03-04:00](https://github.com/leanprover-community/mathlib/commit/2ac1f20)
rename open -> is_open, closed -> is_closed
#### Estimated changes
Modified topology/continuity.lean
- \+ *lemma* continuous_iff_is_closed
- \+ *lemma* embedding_is_closed
- \+ *lemma* is_open_singleton_true
- \+/\- *lemma* continuous_Prop
- \+ *lemma* is_open_set_prod
- \+ *lemma* is_closed_prod
- \+ *lemma* is_closed_diagonal
- \+ *lemma* is_closed_eq
- \+ *lemma* continuous_subtype_is_closed_cover
- \+ *lemma* is_closed_property
- \+ *lemma* is_closed_property2
- \+ *lemma* is_closed_property3
- \- *lemma* continuous_iff_closed
- \- *lemma* embedding_closed
- \- *lemma* open_singleton_true
- \- *lemma* open_set_prod
- \- *lemma* closed_prod
- \- *lemma* closed_diagonal
- \- *lemma* closed_eq
- \- *lemma* continuous_subtype_closed_cover
- \- *lemma* closed_property
- \- *lemma* closed_property2
- \- *lemma* closed_property3
- \+ *theorem* is_open_induced
- \- *theorem* open_induced
- \+/\- *def* continuous

Modified topology/real.lean
- \+ *lemma* is_open_lt
- \+ *lemma* is_open_gt
- \+ *lemma* is_closed_le
- \+ *lemma* is_closed_ge
- \+ *lemma* is_closed_le_real
- \+ *lemma* is_open_lt_real
- \+ *lemma* is_closed_imp
- \- *lemma* open_lt
- \- *lemma* open_gt
- \- *lemma* closed_le
- \- *lemma* closed_ge
- \- *lemma* closed_le_real
- \- *lemma* open_lt_real
- \- *lemma* closed_imp

Modified topology/topological_space.lean
- \+/\- *lemma* topological_space_eq
- \+ *lemma* is_open_univ
- \+ *lemma* is_open_inter
- \+ *lemma* is_open_sUnion
- \+ *lemma* is_open_union
- \+ *lemma* is_open_Union
- \+ *lemma* is_open_empty
- \+ *lemma* is_closed_empty
- \+ *lemma* is_closed_univ
- \+ *lemma* is_closed_union
- \+ *lemma* is_closed_sInter
- \+ *lemma* is_closed_Inter
- \+ *lemma* is_open_compl_iff
- \+ *lemma* is_closed_compl_iff
- \+ *lemma* is_open_diff
- \+ *lemma* is_closed_inter
- \+ *lemma* is_closed_Union
- \+ *lemma* is_open_interior
- \+/\- *lemma* interior_maximal
- \+/\- *lemma* interior_eq_of_open
- \+/\- *lemma* interior_eq_iff_open
- \+/\- *lemma* subset_interior_iff_subset_of_open
- \+ *lemma* interior_union_is_closed_of_interior_empty
- \+ *lemma* is_closed_closure
- \+/\- *lemma* closure_minimal
- \+ *lemma* closure_eq_of_is_closed
- \+ *lemma* closure_eq_iff_is_closed
- \+ *lemma* closure_subset_iff_subset_of_is_closed
- \+/\- *lemma* towards_nhds
- \+/\- *lemma* nhds_sets
- \+/\- *lemma* mem_nhds_sets
- \+ *lemma* is_open_iff_nhds
- \+ *lemma* is_closed_iff_nhds
- \+/\- *lemma* closure_inter_open
- \+ *lemma* is_closed_Union_of_locally_finite
- \+ *lemma* compact_of_is_closed_subset
- \+ *lemma* is_closed_singleton
- \+ *lemma* nhds_is_closed
- \+ *lemma* is_closed_induced_iff
- \+/\- *lemma* generate_from_le
- \- *lemma* open_univ
- \- *lemma* open_inter
- \- *lemma* open_sUnion
- \- *lemma* open_union
- \- *lemma* open_Union
- \- *lemma* open_empty
- \- *lemma* closed_empty
- \- *lemma* closed_univ
- \- *lemma* closed_union
- \- *lemma* closed_sInter
- \- *lemma* closed_Inter
- \- *lemma* open_compl_iff
- \- *lemma* closed_compl_iff
- \- *lemma* open_diff
- \- *lemma* closed_inter
- \- *lemma* closed_Union
- \- *lemma* open_interior
- \- *lemma* interior_union_closed_of_interior_empty
- \- *lemma* closed_closure
- \- *lemma* closure_eq_of_closed
- \- *lemma* closure_eq_iff_closed
- \- *lemma* closure_subset_iff_subset_of_closed
- \- *lemma* open_iff_nhds
- \- *lemma* closed_iff_nhds
- \- *lemma* closed_Union_of_locally_finite
- \- *lemma* compact_of_closed_subset
- \- *lemma* closed_singleton
- \- *lemma* nhds_closed
- \- *lemma* closed_induced_iff
- \+ *def* is_open
- \+ *def* is_closed
- \+/\- *def* interior
- \+/\- *def* closure
- \+/\- *def* nhds
- \- *def* open'
- \- *def* closed

Modified topology/uniform_space.lean
- \+ *lemma* is_open_uniformity
- \+ *lemma* mem_uniformity_is_closed
- \+ *lemma* complete_of_is_closed
- \+ *lemma* compact_of_totally_bounded_is_closed
- \- *lemma* open_uniformity
- \- *lemma* mem_uniformity_closed
- \- *lemma* complete_of_closed
- \- *lemma* compact_of_totally_bounded_closed



## [2017-08-10 16:36:59-04:00](https://github.com/leanprover-community/mathlib/commit/7882677)
construct reals as complete, linear ordered field
#### Estimated changes
Created algebra/field.lean
- \+ *lemma* inv_sub_inv_eq
- \+ *lemma* le_div_iff_mul_le_of_pos
- \+ *lemma* div_le_iff_le_mul_of_pos
- \+ *lemma* lt_div_iff
- \+ *lemma* ivl_translate
- \+ *lemma* ivl_stretch
- \+ *lemma* abs_inv
- \+ *lemma* inv_neg

Modified algebra/group.lean
- \+ *lemma* le_sub_iff_add_le
- \+ *lemma* sub_le_iff_le_add
- \+ *lemma* abs_le_iff

Modified algebra/lattice/complete_lattice.lean
- \+ *lemma* ord_continuous_sup
- \+ *lemma* ord_continuous_mono
- \+ *def* ord_continuous

Modified algebra/lattice/filter.lean
- \+ *lemma* classical.cases
- \+ *lemma* false_neq_true
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* map_bind
- \+ *lemma* seq_bind_eq
- \+ *lemma* seq_eq_bind_map
- \+ *lemma* bind_assoc
- \+ *lemma* prod.mk.eta
- \+ *lemma* prod.swap_swap
- \+ *lemma* prod.fst_swap
- \+ *lemma* prod.snd_swap
- \+ *lemma* prod.swap_prod_mk
- \+ *lemma* prod.swap_swap_eq
- \+ *lemma* Inf_eq_finite_sets
- \+ *lemma* bind_def
- \+ *lemma* ne_empty_iff_exists_mem
- \+ *lemma* fmap_eq_image
- \+ *lemma* mem_seq_iff
- \+ *lemma* univ_eq_true_false
- \+ *lemma* not_eq_empty_iff_exists
- \+ *lemma* image_inter
- \+ *lemma* image_Union
- \+ *lemma* image_singleton
- \+ *lemma* mem_prod_eq
- \+ *lemma* prod_mono
- \+ *lemma* prod_inter_prod
- \+ *lemma* image_swap_prod
- \+ *lemma* prod_image_image_eq
- \+ *lemma* prod_singleton_singleton
- \+ *lemma* prod_neq_empty_iff
- \+ *lemma* prod_mk_mem_set_prod_eq
- \+ *lemma* set_of_mem_eq
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
- \+ *lemma* not_or_iff_implies
- \+ *lemma* directed_on_Union
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
- \+ *lemma* pure_def
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
- \+ *lemma* inter_mem_inf_sets
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
- \+ *lemma* map_map
- \+ *lemma* map_sup
- \+ *lemma* supr_map
- \+ *lemma* map_bot
- \+ *lemma* map_eq_bot_iff
- \+ *lemma* map_ne_bot
- \+ *lemma* map_mono
- \+ *lemma* monotone_map
- \+ *lemma* map_cong
- \+ *lemma* map_infi_le
- \+ *lemma* map_infi_eq
- \+ *lemma* map_binfi_eq
- \+ *lemma* map_inf
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
- \+ *lemma* vmap_mono
- \+ *lemma* monotone_vmap
- \+ *lemma* vmap_bot
- \+ *lemma* vmap_sup
- \+ *lemma* vmap_inf
- \+ *lemma* le_map_vmap'
- \+ *lemma* le_map_vmap
- \+ *lemma* vmap_map
- \+ *lemma* map_inj
- \+ *lemma* vmap_neq_bot
- \+ *lemma* vmap_neq_bot_of_surj
- \+ *lemma* map_vmap_le
- \+ *lemma* le_vmap_map
- \+ *lemma* vmap_vmap_comp
- \+ *lemma* le_vmap_iff_map_le
- \+ *lemma* vmap_infi
- \+ *lemma* towards_cong
- \+ *lemma* towards_id'
- \+ *lemma* towards_id
- \+ *lemma* towards_compose
- \+ *lemma* towards_map
- \+ *lemma* towards_map'
- \+ *lemma* towards_vmap
- \+ *lemma* towards_vmap'
- \+ *lemma* towards_vmap''
- \+ *lemma* towards_inf
- \+ *lemma* lift_sets_eq
- \+ *lemma* mem_lift
- \+ *lemma* mem_lift_iff
- \+ *lemma* lift_le
- \+ *lemma* lift_mono
- \+ *lemma* lift_mono'
- \+ *lemma* map_lift_eq
- \+ *lemma* vmap_lift_eq
- \+ *lemma* map_lift_eq2
- \+ *lemma* lift_comm
- \+ *lemma* lift_assoc
- \+ *lemma* lift_lift_same_le_lift
- \+ *lemma* lift_lift_same_eq_lift
- \+ *lemma* lift_principal
- \+ *lemma* lift_neq_bot_iff
- \+ *lemma* mem_lift'
- \+ *lemma* mem_lift'_iff
- \+ *lemma* lift'_le
- \+ *lemma* lift'_mono
- \+ *lemma* lift'_mono'
- \+ *lemma* lift'_cong
- \+ *lemma* map_lift'_eq
- \+ *lemma* map_lift'_eq2
- \+ *lemma* lift'_principal
- \+ *lemma* principal_le_lift'
- \+ *lemma* lift_lift'_assoc
- \+ *lemma* lift'_lift'_assoc
- \+ *lemma* lift'_lift_assoc
- \+ *lemma* lift_lift'_same_le_lift'
- \+ *lemma* lift_lift'_same_eq_lift'
- \+ *lemma* lift'_inf_principal_eq
- \+ *lemma* lift'_neq_bot_iff
- \+ *lemma* lift'_id
- \+ *lemma* le_lift'
- \+ *lemma* prod_mem_prod
- \+ *lemma* mem_prod_iff
- \+ *lemma* prod_same_eq
- \+ *lemma* mem_prod_same_iff
- \+ *lemma* prod_comm
- \+ *lemma* prod_lift_lift
- \+ *lemma* prod_lift'_lift'
- \+ *lemma* towards_fst
- \+ *lemma* towards_snd
- \+ *lemma* towards_prod_mk
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
- \+ *theorem* mem_vmap
- \+/\- *theorem* preimage_mem_vmap
- \- *theorem* pure_seq_eq_map
- \- *theorem* map_bind
- \- *theorem* seq_bind_eq
- \- *theorem* seq_eq_bind_map
- \- *theorem* bind_assoc
- \- *theorem* prod.mk.eta
- \- *theorem* prod.swap_swap
- \- *theorem* prod.fst_swap
- \- *theorem* prod.snd_swap
- \- *theorem* prod.swap_prod_mk
- \- *theorem* prod.swap_swap_eq
- \- *theorem* Inf_eq_finite_sets
- \- *theorem* bind_def
- \- *theorem* ne_empty_iff_exists_mem
- \- *theorem* fmap_eq_image
- \- *theorem* mem_seq_iff
- \- *theorem* mem_prod_eq
- \- *theorem* prod_mono
- \- *theorem* prod_inter_prod
- \- *theorem* image_swap_prod
- \- *theorem* prod_image_image_eq
- \- *theorem* prod_singleton_singleton
- \- *theorem* prod_neq_empty_iff
- \- *theorem* prod_mk_mem_set_prod_eq
- \- *theorem* set_of_mem_eq
- \- *theorem* mem_image_iff_of_inverse
- \- *theorem* image_eq_preimage_of_inverse
- \- *theorem* diff_right_antimono
- \- *theorem* sUnion_mono
- \- *theorem* Union_subset_Union
- \- *theorem* Union_subset_Union2
- \- *theorem* Union_subset_Union_const
- \- *theorem* diff_neq_empty
- \- *theorem* diff_empty
- \- *theorem* implies_implies_true_iff
- \- *theorem* not_not_mem_iff
- \- *theorem* singleton_neq_emptyset
- \- *theorem* eq_of_sup_eq_inf_eq
- \- *theorem* inf_eq_bot_iff_le_compl
- \- *theorem* compl_image_set_of
- \- *theorem* neg_subset_neg_iff_subset
- \- *theorem* sUnion_eq_Union
- \- *theorem* directed_on_Union
- \- *theorem* filter_eq
- \- *theorem* univ_mem_sets'
- \- *theorem* univ_mem_sets
- \- *theorem* inter_mem_sets
- \- *theorem* Inter_mem_sets
- \- *theorem* exists_sets_subset_iff
- \- *theorem* monotone_mem_sets
- \- *theorem* mem_join_sets
- \- *theorem* mem_principal_sets
- \- *theorem* le_principal_iff
- \- *theorem* principal_mono
- \- *theorem* monotone_principal
- \- *theorem* principal_eq_iff_eq
- \- *theorem* map_principal
- \- *theorem* join_principal_eq_Sup
- \- *theorem* pure_def
- \- *theorem* mem_inf_sets_of_left
- \- *theorem* mem_inf_sets_of_right
- \- *theorem* mem_bot_sets
- \- *theorem* empty_in_sets_eq_bot
- \- *theorem* inhabited_of_mem_sets
- \- *theorem* filter_eq_bot_of_not_nonempty
- \- *theorem* forall_sets_neq_empty_iff_neq_bot
- \- *theorem* mem_sets_of_neq_bot
- \- *theorem* mem_sup_sets
- \- *theorem* mem_inf_sets
- \- *theorem* infi_sets_eq
- \- *theorem* infi_sets_eq'
- \- *theorem* Inf_sets_eq_finite
- \- *theorem* supr_sets_eq
- \- *theorem* sup_join
- \- *theorem* supr_join
- \- *theorem* binfi_sup_eq
- \- *theorem* infi_sup_eq
- \- *theorem* inf_principal
- \- *theorem* sup_principal
- \- *theorem* supr_principal
- \- *theorem* principal_univ
- \- *theorem* principal_empty
- \- *theorem* principal_eq_bot_iff
- \- *theorem* mem_pure
- \- *theorem* mem_map
- \- *theorem* image_mem_map
- \- *theorem* map_id
- \- *theorem* map_compose
- \- *theorem* map_sup
- \- *theorem* supr_map
- \- *theorem* map_bot
- \- *theorem* map_eq_bot_iff
- \- *theorem* map_mono
- \- *theorem* monotone_map
- \- *theorem* map_infi_le
- \- *theorem* map_infi_eq
- \- *theorem* map_binfi_eq
- \- *theorem* mem_bind_sets
- \- *theorem* bind_mono
- \- *theorem* bind_sup
- \- *theorem* bind_mono2
- \- *theorem* principal_bind
- \- *theorem* seq_mono
- \- *theorem* fmap_principal
- \- *theorem* mem_return_sets
- \- *theorem* infi_neq_bot_of_directed
- \- *theorem* infi_neq_bot_iff_of_directed
- \- *theorem* return_neq_bot
- \- *theorem* mem_vmap_of_mem
- \- *theorem* vmap_mono
- \- *theorem* monotone_vmap
- \- *theorem* le_map_vmap
- \- *theorem* vmap_map
- \- *theorem* vmap_neq_bot
- \- *theorem* vmap_neq_bot_of_surj
- \- *theorem* map_vmap_le
- \- *theorem* le_vmap_map
- \- *theorem* vmap_vmap_comp
- \- *theorem* le_vmap_iff_map_le
- \- *theorem* lift_sets_eq
- \- *theorem* mem_lift
- \- *theorem* mem_lift_iff
- \- *theorem* lift_mono
- \- *theorem* lift_mono'
- \- *theorem* map_lift_eq
- \- *theorem* vmap_lift_eq
- \- *theorem* map_lift_eq2
- \- *theorem* lift_comm
- \- *theorem* lift_assoc
- \- *theorem* lift_lift_same_le_lift
- \- *theorem* lift_lift_same_eq_lift
- \- *theorem* lift_principal
- \- *theorem* lift_neq_bot_iff
- \- *theorem* mem_lift'
- \- *theorem* mem_lift'_iff
- \- *theorem* lift'_mono
- \- *theorem* lift'_mono'
- \- *theorem* lift'_cong
- \- *theorem* map_lift'_eq
- \- *theorem* map_lift'_eq2
- \- *theorem* lift'_principal
- \- *theorem* principal_le_lift'
- \- *theorem* lift_lift'_assoc
- \- *theorem* lift'_lift'_assoc
- \- *theorem* lift'_lift_assoc
- \- *theorem* lift_lift'_same_le_lift'
- \- *theorem* lift_lift'_same_eq_lift'
- \- *theorem* lift'_inf_principal_eq
- \- *theorem* lift'_neq_bot_iff
- \- *theorem* lift'_id
- \- *theorem* le_lift'
- \- *theorem* prod_mem_prod
- \- *theorem* prod_same_eq
- \- *theorem* mem_prod_iff
- \- *theorem* mem_prod_same_iff
- \- *theorem* prod_comm
- \- *theorem* prod_lift_lift
- \- *theorem* prod_lift'_lift'
- \- *theorem* prod_map_map_eq
- \- *theorem* prod_vmap_vmap_eq
- \- *theorem* prod_inf_prod
- \- *theorem* prod_neq_bot
- \- *theorem* prod_principal_principal
- \- *theorem* mem_infi_sets
- \- *theorem* mem_top_sets_iff
- \- *theorem* infi_sets_induct
- \- *theorem* lift_infi
- \- *theorem* lift_infi'
- \- *theorem* lift'_infi
- \- *theorem* map_eq_vmap_of_inverse
- \- *theorem* map_swap_vmap_swap_eq
- \- *theorem* ultrafilter_pure
- \- *theorem* ultrafilter_unique
- \- *theorem* exists_ultrafilter
- \- *theorem* le_of_ultrafilter
- \- *theorem* mem_or_compl_mem_of_ultrafilter
- \- *theorem* mem_or_mem_of_ultrafilter
- \- *theorem* mem_of_finite_sUnion_ultrafilter
- \- *theorem* mem_of_finite_Union_ultrafilter
- \- *theorem* ultrafilter_of_split
- \- *theorem* ultrafilter_map
- \- *theorem* ultrafilter_of_spec
- \- *theorem* ultrafilter_of_le
- \- *theorem* ultrafilter_ultrafilter_of
- \- *theorem* ultrafilter_of_ultrafilter
- \+/\- *def* towards

Modified algebra/order.lean
- \+ *lemma* not_le_iff
- \+ *lemma* not_lt_iff
- \+ *def* partial_order_dual
- \- *def* weak_order_dual

Modified algebra/ring.lean


Modified data/int/order.lean
- \+ *lemma* of_nat_le_of_nat_of_le
- \+ *lemma* le_of_of_nat_le_of_nat

Modified data/nat/basic.lean
- \+ *lemma* le_zero_iff
- \+ *lemma* le_add_one_iff

Modified data/rat.lean
- \+ *lemma* coe_int_eq_mk
- \+ *lemma* coe_nat_rat_eq_mk
- \+ *lemma* coe_int_add
- \+ *lemma* coe_int_sub
- \+ *lemma* coe_int_one
- \+ *lemma* le_of_of_int_le_of_int
- \+ *lemma* exists_upper_nat_bound
- \+ *lemma* nat_ceil_spec
- \+ *lemma* nat_ceil_min
- \+ *lemma* nat_ceil_mono
- \+ *lemma* nat_ceil_zero
- \+ *lemma* nat_ceil_add_one_eq
- \+ *lemma* nat_ceil_lt_add_one
- \+ *def* nat_ceil

Modified data/set/basic.lean
- \+ *lemma* mem_of_eq_of_mem
- \+ *lemma* set_compr_eq_eq_singleton
- \+ *lemma* mem_image_iff_of_inverse
- \+/\- *theorem* subset.trans
- \+ *theorem* image_eq_preimage_of_inverse

Modified data/set/finite.lean
- \+ *lemma* finite_le_nat

Modified data/set/lattice.lean
- \+ *lemma* monotone_image

Modified topology/continuity.lean
- \+ *lemma* image_preimage_eq_inter_rng
- \+ *lemma* subtype.val_image
- \+ *lemma* univ_prod_univ
- \+ *lemma* continuous_id
- \+ *lemma* continuous_compose
- \+ *lemma* continuous_iff_towards
- \+ *lemma* continuous_const
- \+ *lemma* continuous_iff_closed
- \+ *lemma* image_closure_subset_closure_image
- \+ *lemma* compact_image
- \+ *lemma* continuous_iff_induced_le
- \+ *lemma* continuous_eq_le_coinduced
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
- \+ *lemma* induced_mono
- \+ *lemma* induced_id
- \+ *lemma* induced_compose
- \+ *lemma* induced_sup
- \+ *lemma* embedding_id
- \+ *lemma* embedding_compose
- \+ *lemma* embedding_prod_mk
- \+ *lemma* embedding_of_embedding_compose
- \+ *lemma* embedding_open
- \+ *lemma* embedding_closed
- \+ *lemma* open_singleton_true
- \+ *lemma* continuous_Prop
- \+ *lemma* nhds_induced_eq_vmap
- \+ *lemma* map_nhds_induced_eq
- \+ *lemma* closure_induced
- \+ *lemma* continuous_fst
- \+ *lemma* continuous_snd
- \+ *lemma* continuous_prod_mk
- \+ *lemma* open_set_prod
- \+ *lemma* prod_eq_generate_from
- \+ *lemma* nhds_prod_eq
- \+ *lemma* closure_prod_eq
- \+ *lemma* closed_prod
- \+ *lemma* closed_diagonal
- \+ *lemma* closed_eq
- \+ *lemma* continuous_inl
- \+ *lemma* continuous_inr
- \+ *lemma* continuous_sum_rec
- \+ *lemma* towards_nhds_iff_of_embedding
- \+ *lemma* continuous_iff_of_embedding
- \+ *lemma* embedding_graph
- \+ *lemma* embedding_subtype_val
- \+ *lemma* continuous_subtype_val
- \+ *lemma* continuous_subtype_mk
- \+ *lemma* map_nhds_subtype_val_eq
- \+ *lemma* nhds_subtype_eq_vmap
- \+ *lemma* continuous_subtype_nhds_cover
- \+ *lemma* continuous_subtype_closed_cover
- \+ *lemma* closure_subtype
- \+ *lemma* nhds_pi
- \+ *lemma* compact_pi_infinite
- \+ *lemma* inj_iff
- \+ *lemma* closure_image_univ
- \+ *lemma* vmap_nhds_neq_bot
- \+ *lemma* ext_eq
- \+ *lemma* ext_e_eq
- \+ *lemma* towards_ext
- \+ *lemma* continuous_ext
- \+ *lemma* closed_property
- \+ *lemma* closed_property2
- \+ *lemma* closed_property3
- \+ *lemma* mem_closure_of_continuous
- \+ *lemma* mem_closure_of_continuous2
- \- *theorem* classical.cases
- \- *theorem* univ_eq_true_false
- \- *theorem* false_neq_true
- \- *theorem* subtype.val_image
- \- *theorem* continuous_id
- \- *theorem* continuous_compose
- \- *theorem* continuous_iff_towards
- \- *theorem* continuous_iff_induced_le
- \- *theorem* continuous_eq_le_coinduced
- \- *theorem* continuous_induced_dom
- \- *theorem* continuous_induced_rng
- \- *theorem* continuous_coinduced_rng
- \- *theorem* continuous_coinduced_dom
- \- *theorem* continuous_inf_dom
- \- *theorem* continuous_inf_rng_left
- \- *theorem* continuous_inf_rng_right
- \- *theorem* continuous_Inf_dom
- \- *theorem* continuous_Inf_rng
- \- *theorem* continuous_infi_dom
- \- *theorem* continuous_infi_rng
- \- *theorem* continuous_top
- \- *theorem* continuous_bot
- \- *theorem* continuous_sup_rng
- \- *theorem* continuous_sup_dom_left
- \- *theorem* continuous_sup_dom_right
- \- *theorem* open_singleton_true
- \- *theorem* continuous_Prop
- \- *theorem* nhds_induced_eq_vmap
- \- *theorem* map_nhds_induced_eq
- \- *theorem* continuous_fst
- \- *theorem* continuous_snd
- \- *theorem* continuous_prod_mk
- \- *theorem* open_set_prod
- \- *theorem* prod_eq_generate_from
- \- *theorem* nhds_prod_eq
- \- *theorem* closure_prod_eq
- \- *theorem* continuous_inl
- \- *theorem* continuous_inr
- \- *theorem* continuous_sum_rec
- \- *theorem* continuous_subtype_val
- \- *theorem* continuous_subtype_mk
- \- *theorem* map_nhds_subtype_val_eq
- \- *theorem* continuous_subtype_nhds_cover
- \- *theorem* nhds_pi
- \- *theorem* compact_pi_infinite
- \+ *def* embedding
- \+ *def* ext
- \+ *def* subtype_emb

Created topology/real.lean
- \+ *lemma* quot_mk_image_univ_eq
- \+ *lemma* forall_subtype_iff
- \+ *lemma* one_lt_two
- \+ *lemma* zero_lt_two
- \+ *lemma* mem_zero_nhd
- \+ *lemma* mem_zero_nhd_iff
- \+ *lemma* towards_zero_nhds
- \+ *lemma* pure_zero_le_zero_nhd
- \+ *lemma* towards_neg_rat_zero
- \+ *lemma* towards_add_rat_zero
- \+ *lemma* towards_add_rat_zero'
- \+ *lemma* towards_sub_rat'
- \+ *lemma* towards_mul_bnd_rat
- \+ *lemma* towards_mul_bnd_rat'
- \+ *lemma* towards_mul_rat'
- \+ *lemma* uniformity_rat
- \+ *lemma* mem_uniformity_rat
- \+ *lemma* uniform_continuous_rat
- \+ *lemma* towards_sub_uniformity_zero_nhd
- \+ *lemma* towards_sub_uniformity_zero_nhd'
- \+ *lemma* uniform_continuous_add_rat
- \+ *lemma* uniform_continuous_neg_rat
- \+ *lemma* continuous_add_rat
- \+ *lemma* towards_add_rat
- \+ *lemma* continuous_neg_rat
- \+ *lemma* towards_neg_rat
- \+ *lemma* uniform_embedding_add_rat
- \+ *lemma* uniform_embedding_mul_rat
- \+ *lemma* nhds_eq_map_zero_nhd
- \+ *lemma* nhds_0_eq_zero_nhd
- \+ *lemma* lt_mem_nhds
- \+ *lemma* gt_mem_nhds
- \+ *lemma* open_lt
- \+ *lemma* open_gt
- \+ *lemma* closed_le
- \+ *lemma* closed_ge
- \+ *lemma* uniform_continuous_inv_pos_rat
- \+ *lemma* towards_of_uniform_continuous_subtype
- \+ *lemma* towards_inv_pos_rat
- \+ *lemma* towards_inv_rat
- \+ *lemma* uniform_continuous_mul_rat
- \+ *lemma* towards_mul_rat
- \+ *lemma* uniform_continuous_rat'
- \+ *lemma* uniform_continuous_abs_rat
- \+ *lemma* continuous_abs_rat
- \+ *lemma* totally_bounded_01_rat
- \+ *lemma* uniform_embedding_of_rat
- \+ *lemma* dense_embedding_of_rat
- \+ *lemma* dense_embedding_of_rat_of_rat
- \+ *lemma* lift_rat_fun_of_rat
- \+ *lemma* lift_rat_op_of_rat_of_rat
- \+ *lemma* of_rat_zero
- \+ *lemma* of_rat_one
- \+ *lemma* of_rat_neg
- \+ *lemma* of_rat_add
- \+ *lemma* of_rat_sub
- \+ *lemma* of_rat_mul
- \+ *lemma* of_rat_inv
- \+ *lemma* uniform_continuous_neg_real
- \+ *lemma* continuous_neg_real
- \+ *lemma* uniform_continuous_add_real
- \+ *lemma* continuous_add_real'
- \+ *lemma* continuous_add_real
- \+ *lemma* continuous_sub_real
- \+ *lemma* of_rat_mem_nonneg
- \+ *lemma* of_rat_mem_nonneg_iff
- \+ *lemma* of_rat_le_of_rat
- \+ *lemma* two_eq_of_rat_two
- \+ *lemma* mem_nonneg_of_continuous2
- \+ *lemma* zero_le_iff_nonneg
- \+ *lemma* eq_0_of_nonneg_of_neg_nonneg
- \+ *lemma* preimage_neg_real
- \+ *lemma* neg_preimage_closure
- \+ *lemma* of_rat_lt_of_rat
- \+ *lemma* preimage_neg_rat
- \+ *lemma* map_neg_real
- \+ *lemma* map_neg_rat
- \+ *lemma* closed_le_real
- \+ *lemma* open_lt_real
- \+ *lemma* closure_of_rat_image_eq
- \+ *lemma* closed_imp
- \+ *lemma* abs_real_eq_abs
- \+ *lemma* uniform_continuous_abs_real
- \+ *lemma* continuous_abs_real
- \+ *lemma* of_rat_abs
- \+ *lemma* mem_uniformity_real_iff
- \+ *lemma* exists_lt_of_rat
- \+ *lemma* continuous_mul_real
- \+ *lemma* continuous_mul_real'
- \+ *lemma* towards_inv_real
- \+ *lemma* continuous_inv_real'
- \+ *lemma* continuous_inv_real
- \+ *lemma* compact_ivl
- \+ *lemma* exists_supremum_real
- \+ *def* zero_nhd
- \+ *def* real
- \+ *def* of_rat
- \+ *def* lift_rat_fun
- \+ *def* lift_rat_op
- \+ *def* nonneg

Modified topology/topological_space.lean
- \+ *lemma* compl_subset_of_compl_subset
- \+ *lemma* not_and_iff_imp_not
- \+ *lemma* diff_subset_diff
- \+ *lemma* mem_of_mem_of_subset
- \+ *lemma* univ_subtype
- \+ *lemma* topological_space_eq
- \+ *lemma* open_univ
- \+ *lemma* open_inter
- \+ *lemma* open_sUnion
- \+ *lemma* open_union
- \+ *lemma* open_Union
- \+ *lemma* open_empty
- \+ *lemma* closed_empty
- \+ *lemma* closed_univ
- \+ *lemma* closed_union
- \+ *lemma* closed_sInter
- \+ *lemma* closed_Inter
- \+ *lemma* open_compl_iff
- \+ *lemma* closed_compl_iff
- \+ *lemma* open_diff
- \+ *lemma* closed_inter
- \+ *lemma* closed_Union
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
- \+ *lemma* towards_nhds
- \+ *lemma* towards_const_nhds
- \+ *lemma* nhds_sets
- \+ *lemma* map_nhds
- \+ *lemma* mem_nhds_sets_iff
- \+ *lemma* mem_of_nhds
- \+ *lemma* mem_nhds_sets
- \+ *lemma* return_le_nhds
- \+ *lemma* nhds_neq_bot
- \+ *lemma* interior_eq_nhds
- \+ *lemma* open_iff_nhds
- \+ *lemma* closure_eq_nhds
- \+ *lemma* closed_iff_nhds
- \+ *lemma* closure_inter_open
- \+ *lemma* closure_diff
- \+ *lemma* locally_finite_of_finite
- \+ *lemma* locally_finite_subset
- \+ *lemma* closed_Union_of_locally_finite
- \+ *lemma* compact_of_closed_subset
- \+ *lemma* compact_adherence_nhdset
- \+ *lemma* compact_iff_ultrafilter_le_nhds
- \+ *lemma* compact_elim_finite_subcover
- \+ *lemma* compact_elim_finite_subcover_image
- \+ *lemma* compact_of_finite_subcover
- \+ *lemma* compact_iff_finite_subcover
- \+ *lemma* compact_empty
- \+ *lemma* compact_singleton
- \+ *lemma* closed_singleton
- \+ *lemma* compl_singleton_mem_nhds
- \+ *lemma* closure_singleton
- \+ *lemma* t2_separation
- \+ *lemma* eq_of_nhds_neq_bot
- \+ *lemma* nhds_eq_nhds_iff
- \+ *lemma* nhds_le_nhds_iff
- \+ *lemma* towards_nhds_unique
- \+ *lemma* nhds_closed
- \+ *lemma* nhds_generate_from
- \+ *lemma* closed_induced_iff
- \+ *lemma* t2_space_top
- \+ *lemma* le_of_nhds_le_nhds
- \+ *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* generate_from_le
- \+ *lemma* supr_eq_generate_from
- \+ *lemma* sup_eq_generate_from
- \+ *lemma* nhds_mono
- \+ *lemma* nhds_supr
- \+ *lemma* lim_spec
- \+ *lemma* lim_eq
- \+ *lemma* lim_nhds_eq
- \+ *lemma* lim_nhds_eq_of_closure
- \- *theorem* topological_space_eq
- \- *theorem* open_univ
- \- *theorem* open_inter
- \- *theorem* open_sUnion
- \- *theorem* open_Union
- \- *theorem* open_empty
- \- *theorem* closed_empty
- \- *theorem* closed_univ
- \- *theorem* closed_union
- \- *theorem* closed_sInter
- \- *theorem* closed_Inter
- \- *theorem* closed_compl_iff_open
- \- *theorem* open_compl_iff_closed
- \- *theorem* open_diff
- \- *theorem* open_interior
- \- *theorem* interior_subset
- \- *theorem* interior_maximal
- \- *theorem* interior_eq_of_open
- \- *theorem* interior_eq_iff_open
- \- *theorem* subset_interior_iff_subset_of_open
- \- *theorem* interior_mono
- \- *theorem* interior_empty
- \- *theorem* interior_univ
- \- *theorem* interior_interior
- \- *theorem* interior_inter
- \- *theorem* interior_union_closed_of_interior_empty
- \- *theorem* closed_closure
- \- *theorem* subset_closure
- \- *theorem* closure_minimal
- \- *theorem* closure_eq_of_closed
- \- *theorem* closure_eq_iff_closed
- \- *theorem* closure_subset_iff_subset_of_closed
- \- *theorem* closure_mono
- \- *theorem* closure_empty
- \- *theorem* closure_univ
- \- *theorem* closure_closure
- \- *theorem* closure_union
- \- *theorem* interior_subset_closure
- \- *theorem* closure_eq_compl_interior_compl
- \- *theorem* interior_compl_eq
- \- *theorem* closure_compl_eq
- \- *theorem* nhds_sets
- \- *theorem* map_nhds
- \- *theorem* mem_nhds_sets_iff
- \- *theorem* mem_nhds_sets
- \- *theorem* return_le_nhds
- \- *theorem* nhds_neq_bot
- \- *theorem* interior_eq_nhds
- \- *theorem* open_iff_nhds
- \- *theorem* closure_eq_nhds
- \- *theorem* closed_iff_nhds
- \- *theorem* not_eq_empty_iff_exists
- \- *theorem* closed_Union_of_locally_finite
- \- *theorem* compact_adherence_nhdset
- \- *theorem* compact_iff_ultrafilter_le_nhds
- \- *theorem* finite_subcover_of_compact
- \- *theorem* eq_of_nhds_neq_bot
- \- *theorem* nhds_generate_from
- \- *theorem* t2_space_top
- \- *theorem* le_of_nhds_le_nhds
- \- *theorem* eq_of_nhds_eq_nhds
- \- *theorem* generate_from_le
- \- *theorem* supr_eq_generate_from
- \- *theorem* sup_eq_generate_from
- \- *theorem* nhds_mono
- \- *theorem* nhds_supr
- \+/\- *def* compact

Modified topology/uniform_space.lean
- \+ *lemma* forall_quotient_iff
- \+ *lemma* prod_mk_mem_comp_rel
- \+ *lemma* id_comp_rel
- \+ *lemma* uniform_space.core_eq
- \+ *lemma* uniform_space.to_core_to_topological_space
- \+ *lemma* uniform_space_eq
- \+ *lemma* uniform_space.of_core_eq_to_core
- \+ *lemma* open_uniformity
- \+ *lemma* refl_le_uniformity
- \+ *lemma* refl_mem_uniformity
- \+ *lemma* symm_le_uniformity
- \+ *lemma* comp_le_uniformity
- \+ *lemma* towards_swap_uniformity
- \+ *lemma* towards_const_uniformity
- \+ *lemma* comp_mem_uniformity_sets
- \+ *lemma* symm_of_uniformity
- \+ *lemma* comp_symm_of_uniformity
- \+ *lemma* uniformity_le_symm
- \+ *lemma* uniformity_eq_symm
- \+ *lemma* uniformity_lift_le_comp
- \+ *lemma* comp_le_uniformity3
- \+ *lemma* mem_nhds_uniformity_iff
- \+ *lemma* nhds_eq_uniformity
- \+ *lemma* mem_nhds_left
- \+ *lemma* mem_nhds_right
- \+ *lemma* towards_right_nhds_uniformity
- \+ *lemma* towards_left_nhds_uniformity
- \+ *lemma* lift_nhds_left
- \+ *lemma* lift_nhds_right
- \+ *lemma* nhds_nhds_eq_uniformity_uniformity_prod
- \+ *lemma* nhds_eq_uniformity_prod
- \+ *lemma* nhdset_of_mem_uniformity
- \+ *lemma* closure_eq_inter_uniformity
- \+ *lemma* uniformity_eq_uniformity_closure
- \+ *lemma* uniformity_eq_uniformity_interior
- \+ *lemma* interior_mem_uniformity
- \+ *lemma* mem_uniformity_closed
- \+ *lemma* uniform_continuous_const
- \+ *lemma* uniform_continuous_compose
- \+ *lemma* uniform_continuous_of_embedding
- \+ *lemma* dense_embedding_of_uniform_embedding
- \+ *lemma* continuous_of_uniform
- \+ *lemma* closure_image_mem_nhds_of_uniform_embedding
- \+ *lemma* cauchy_downwards
- \+ *lemma* cauchy_nhds
- \+ *lemma* cauchy_pure
- \+ *lemma* le_nhds_of_cauchy_adhp
- \+ *lemma* le_nhds_iff_adhp_of_cauchy
- \+ *lemma* cauchy_map
- \+ *lemma* cauchy_vmap
- \+ *lemma* separated_equiv
- \+ *lemma* totally_bounded_subset
- \+ *lemma* totally_bounded_closure
- \+ *lemma* totally_bounded_image
- \+ *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* totally_bounded_iff_filter
- \+ *lemma* totally_bounded_iff_ultrafilter
- \+ *lemma* compact_of_totally_bounded_complete
- \+ *lemma* complete_of_closed
- \+ *lemma* compact_of_totally_bounded_closed
- \+ *lemma* complete_space_extension
- \+ *lemma* uniform_continuous_quotient_mk
- \+ *lemma* vmap_quotient_le_uniformity
- \+ *lemma* vmap_quotient_eq_uniformity
- \+ *lemma* complete_space_separation
- \+ *lemma* separated_separation
- \+ *lemma* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_exists
- \+ *lemma* uniformly_extend_spec
- \+ *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* monotone_gen
- \+ *lemma* uniform_embedding_pure_cauchy
- \+ *lemma* pure_cauchy_dense
- \+ *lemma* supr_uniformity
- \+ *lemma* sup_uniformity
- \+ *lemma* uniform_continuous_vmap
- \+ *lemma* uniform_continuous_vmap'
- \+ *lemma* to_topological_space_mono
- \+ *lemma* to_topological_space_top
- \+ *lemma* to_topological_space_bot
- \+ *lemma* to_topological_space_supr
- \+ *lemma* to_topological_space_Sup
- \+ *lemma* to_topological_space_sup
- \+ *lemma* uniformity_subtype
- \+ *lemma* uniform_continuous_subtype_val
- \+ *lemma* uniform_continuous_subtype_mk
- \+ *lemma* uniform_embedding_subtype_emb
- \+ *lemma* uniform_extend_subtype
- \+ *lemma* uniformity_prod
- \+ *lemma* mem_uniform_prod
- \+ *lemma* towards_prod_uniformity_fst
- \+ *lemma* towards_prod_uniformity_snd
- \+ *lemma* uniform_continuous_fst
- \+ *lemma* uniform_continuous_snd
- \+ *lemma* uniform_continuous_prod_mk
- \+ *lemma* uniform_embedding_prod
- \+ *lemma* to_topological_space_prod
- \+ *lemma* to_topological_space_subtype
- \- *theorem* prod_mk_mem_comp_rel
- \- *theorem* id_comp_rel
- \- *theorem* uniform_space_eq
- \- *theorem* refl_le_uniformity
- \- *theorem* refl_mem_uniformity
- \- *theorem* symm_le_uniformity
- \- *theorem* comp_le_uniformity
- \- *theorem* comp_mem_uniformity_sets
- \- *theorem* symm_of_uniformity
- \- *theorem* comp_symm_of_uniformity
- \- *theorem* uniformity_le_symm
- \- *theorem* uniformity_eq_symm
- \- *theorem* uniformity_lift_le_comp
- \- *theorem* comp_le_uniformity3
- \- *theorem* mem_nhds_uniformity_iff
- \- *theorem* nhds_eq_uniformity
- \- *theorem* mem_nhds_left
- \- *theorem* mem_nhds_right
- \- *theorem* lift_nhds_left
- \- *theorem* lift_nhds_right
- \- *theorem* nhds_nhds_eq_uniformity_uniformity_prod
- \- *theorem* nhds_eq_uniformity_prod
- \- *theorem* nhdset_of_mem_uniformity
- \- *theorem* closure_eq_inter_uniformity
- \- *theorem* uniformity_eq_uniformity_closure
- \- *theorem* uniformity_eq_uniformity_interior
- \- *theorem* interior_mem_uniformity
- \- *theorem* uniform_continuous_of_embedding
- \- *theorem* continuous_of_uniform
- \- *theorem* cauchy_downwards
- \- *theorem* cauchy_nhds
- \- *theorem* cauchy_pure
- \- *theorem* le_nhds_of_cauchy_adhp
- \- *theorem* le_nhds_iff_adhp_of_cauchy
- \- *theorem* cauchy_map
- \- *theorem* cauchy_vmap
- \- *theorem* separated_equiv
- \- *theorem* cauchy_of_totally_bounded_of_ultrafilter
- \- *theorem* totally_bounded_iff_filter
- \- *theorem* totally_bounded_iff_ultrafilter
- \- *theorem* compact_of_totally_bounded_complete
- \- *theorem* complete_of_closed
- \- *theorem* compact_of_totally_bounded_closed
- \- *theorem* complete_space_extension
- \- *theorem* uniform_continuous_quotient_mk
- \- *theorem* vmap_quotient_le_uniformity
- \- *theorem* complete_space_separation
- \- *theorem* uniformly_extend_spec
- \- *theorem* uniformly_extend_unique
- \- *theorem* uniformly_extend_of_emb
- \- *theorem* uniform_continuous_uniformly_extend
- \- *theorem* monotone_gen
- \- *theorem* uniform_embedding_pure_cauchy
- \- *theorem* pure_cauchy_dense
- \- *theorem* uniform_continuous_vmap
- \- *theorem* to_topological_space_mono
- \- *theorem* supr_uniformity
- \- *theorem* to_topological_space_top
- \- *theorem* to_topological_space_bot
- \- *theorem* to_topological_space_supr
- \+/\- *def* comp_rel
- \+ *def* uniform_space.core.to_topological_space
- \+ *def* uniform_space.of_core
- \+ *def* uniform_space.of_core_eq
- \+/\- *def* uniformity
- \- *def* uniform_continuous
- \- *def* uniform_embedding
- \- *def* cauchy
- \- *def* separated



## [2017-08-02 22:32:47+01:00](https://github.com/leanprover-community/mathlib/commit/64b6151)
refactor(data/set/basic,*): vimage -> preimage, add notation
#### Estimated changes
Modified algebra/lattice/filter.lean
- \+ *theorem* prod_preimage_eq
- \+ *theorem* preimage_set_of_eq
- \+ *theorem* image_eq_preimage_of_inverse
- \+ *theorem* image_swap_eq_preimage_swap
- \+/\- *theorem* mem_vmap_of_mem
- \+/\- *theorem* vmap_principal
- \+ *theorem* preimage_mem_vmap
- \- *theorem* prod_vimage_eq
- \- *theorem* vimage_set_of_eq
- \- *theorem* image_eq_vimage_of_inverse
- \- *theorem* image_swap_eq_vimage_swap
- \- *theorem* vimage_mem_vmap

Modified data/set/basic.lean
- \+/\- *theorem* mem_image_eq
- \+/\- *theorem* mem_image_of_mem
- \+/\- *theorem* mono_image
- \+ *theorem* image_subset_iff_subset_preimage
- \+/\- *theorem* image_comp
- \+/\- *theorem* image_subset
- \+/\- *theorem* image_empty
- \+/\- *theorem* image_id
- \+ *theorem* preimage_empty
- \+ *theorem* mem_preimage_eq
- \+ *theorem* preimage_mono
- \+ *theorem* preimage_image_eq
- \+ *theorem* preimage_univ
- \+ *theorem* preimage_inter
- \+ *theorem* preimage_union
- \+ *theorem* preimage_compl
- \+ *theorem* preimage_id
- \+ *theorem* preimage_comp
- \+ *theorem* eq_preimage_subtype_val_iff
- \- *theorem* image_subset_iff_subset_vimage
- \- *theorem* vimage_empty
- \- *theorem* mem_vimage_eq
- \- *theorem* vimage_mono
- \- *theorem* vimage_image_eq
- \- *theorem* vimage_univ
- \- *theorem* vimage_inter
- \- *theorem* vimage_union
- \- *theorem* vimage_compl
- \- *theorem* vimage_id
- \- *theorem* vimage_comp
- \- *theorem* eq_vimage_subtype_val_iff
- \+/\- *def* mem_image_elim_on
- \+ *def* preimage
- \- *def* vimage

Modified data/set/lattice.lean
- \+ *theorem* monotone_preimage
- \+ *theorem* preimage_Union
- \+ *theorem* preimage_sUnion
- \- *theorem* monotone_vimage
- \- *theorem* vimage_Union
- \- *theorem* vimage_sUnion

Modified topology/continuity.lean
- \+/\- *theorem* open_induced
- \+/\- *def* continuous

Modified topology/topological_space.lean


Modified topology/uniform_space.lean




## [2017-08-02 22:17:36+01:00](https://github.com/leanprover-community/mathlib/commit/41a2376)
refactor(algebra/group,group_power): clean up proofs
#### Estimated changes
Modified algebra/group.lean


Modified algebra/group_power.lean
- \+/\- *theorem* pow_succ
- \+ *theorem* pow_mul_comm'
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_add
- \+/\- *theorem* one_pow
- \+ *theorem* pow_mul_comm
- \+ *theorem* gpow_mul_comm
- \- *theorem* pow_comm
- \- *theorem* gpow_comm
- \+/\- *def* pow_nat
- \+/\- *def* pow_int



## [2017-08-02 16:24:02+01:00](https://github.com/leanprover-community/mathlib/commit/3e9e4b6)
refactor(*): move theorems and do minor polishing
#### Estimated changes
Modified data/bool.lean


Modified data/list/basic.lean
- \+/\- *theorem* concat_cons

Modified data/list/sort.lean
- \- *theorem* add_pos_left
- \- *theorem* add_pos_right
- \- *theorem* add_pos_iff_pos_or_pos
- \- *theorem* succ_le_succ_iff
- \- *theorem* lt_succ_iff_le

Modified data/nat/basic.lean
- \+ *theorem* add_pos_left
- \+ *theorem* add_pos_right
- \+ *theorem* add_pos_iff_pos_or_pos
- \+ *theorem* succ_le_succ_iff
- \+ *theorem* lt_succ_iff_le

Modified logic/basic.lean
- \+ *theorem* implies_and_iff
- \+ *theorem* and_implies_iff
- \+ *theorem* iff_def
- \+ *theorem* bexists_def

Modified tactic/finish.lean
- \- *theorem* implies_and_iff
- \- *theorem* curry_iff
- \- *theorem* iff_def
- \- *theorem* {u}



## [2017-08-02 16:21:24+01:00](https://github.com/leanprover-community/mathlib/commit/da0c346)
fix(*): fix wrt changes in lean
#### Estimated changes
Modified algebra/lattice/bounded_lattice.lean


Modified algebra/lattice/complete_lattice.lean
- \+ *theorem* Sup_le_iff
- \+ *theorem* le_Inf_iff
- \- *theorem* le_Sup_iff
- \- *theorem* Inf_le_iff

Modified algebra/lattice/filter.lean
- \+/\- *theorem* monotone_prod
- \+/\- *theorem* monotone_inter
- \+/\- *theorem* monotone_set_of
- \+/\- *theorem* directed_of_chain
- \+/\- *theorem* monotone_lift
- \+/\- *theorem* monotone_lift'
- \- *theorem* Sup_le_iff
- \+/\- *def* at_top
- \+/\- *def* at_bot

Modified algebra/lattice/fixed_points.lean
- \+/\- *theorem* ge_of_eq

Modified algebra/order.lean
- \+/\- *theorem* comp_le_comp_left_of_monotone

Modified data/num/lemmas.lean


Modified data/set/basic.lean
- \+/\- *theorem* mem_set_of_eq

Modified tactic/alias.lean
- \- *def* alias_attr

Modified topology/uniform_space.lean
- \+/\- *theorem* monotone_comp_rel



## [2017-08-02 15:24:33+01:00](https://github.com/leanprover-community/mathlib/commit/6392b05)
refactor(*): switch from order_pair to partial_order
#### Estimated changes
Modified algebra/lattice/basic.lean


Modified algebra/lattice/bounded_lattice.lean


Modified algebra/lattice/complete_lattice.lean


Modified algebra/lattice/filter.lean
- \+/\- *theorem* monotone_prod
- \+/\- *theorem* monotone_inter
- \+/\- *theorem* monotone_set_of
- \+/\- *theorem* directed_of_chain
- \+/\- *theorem* monotone_lift
- \+/\- *theorem* monotone_lift'
- \+/\- *def* at_top
- \+/\- *def* at_bot

Modified algebra/lattice/fixed_points.lean
- \+/\- *theorem* ge_of_eq
- \+/\- *theorem* lfp_comp
- \+/\- *theorem* gfp_comp

Modified algebra/lattice/zorn.lean
- \+ *theorem* zorn_partial_order
- \- *theorem* zorn_weak_order

Modified algebra/order.lean
- \+/\- *theorem* le_dual_eq_le
- \+/\- *theorem* comp_le_comp_left_of_monotone
- \+/\- *def* weak_order_dual

Modified data/hash_map.lean


Modified data/list/set.lean


Modified data/num/lemmas.lean


Modified data/rat.lean
- \+/\- *def* mk_pnat
- \+/\- *def* mk_nat

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




## [2017-08-01 00:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/fb21c1a)
feat(tactic/alias): alias command
#### Estimated changes
Created tactic/alias.lean
- \+ *theorem* alias1
- \+ *theorem* alias2
- \+ *def* alias_attr

