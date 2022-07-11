## [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f57e59f)
feat(data/analysis): calculations with filters / topologies + misc
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* prod_image
- \+/\- *lemma* prod_union_inter
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_sdiff
- \+/\- *lemma* prod_bind
- \+/\- *lemma* prod_sigma
- \+/\- *lemma* exists_ne_one_of_prod_ne_one
- \+ *theorem* prod_eq_fold

Modified algebra/ordered_group.lean
- \+/\- *lemma* zero_le

Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* mem_interior_iff_mem_nhds
- \+ *lemma* is_open_iff_mem_nhds
- \+/\- *lemma* mem_nhds_of_is_topological_basis

Created data/analysis/filter.lean
- \+ *theorem* coe_mk
- \+ *theorem* of_equiv_val
- \+ *theorem* mem_to_filter_sets
- \+ *theorem* mem_sets
- \+ *theorem* of_equiv_σ
- \+ *theorem* of_equiv_F
- \+ *theorem* principal_σ
- \+ *theorem* principal_F
- \+ *theorem* top_σ
- \+ *theorem* top_F
- \+ *theorem* bot_σ
- \+ *theorem* bot_F
- \+ *theorem* map_σ
- \+ *theorem* map_F
- \+ *theorem* le_iff
- \+ *theorem* tendsto_iff
- \+ *theorem* ne_bot_iff
- \+ *def* of_equiv
- \+ *def* to_filter
- \+ *def* of_eq
- \+ *def* of_filter

Created data/analysis/topology.lean
- \+ *theorem* coe_mk
- \+ *theorem* of_equiv_val
- \+ *theorem* to_topsp_is_topological_basis
- \+ *theorem* mem_nhds_to_topsp
- \+ *theorem* is_open_iff
- \+ *theorem* is_closed_iff
- \+ *theorem* mem_interior_iff
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* of_equiv_σ
- \+ *theorem* of_equiv_F
- \+ *theorem* nhds_σ
- \+ *theorem* nhds_F
- \+ *theorem* tendsto_nhds_iff
- \+ *theorem* locally_finite.realizer.to_locally_finite
- \+ *theorem* locally_finite_iff_exists_realizer
- \+ *def* of_equiv
- \+ *def* compact.realizer

Modified data/equiv.lean
- \+/\- *theorem* apply_inverse_apply
- \+/\- *theorem* inverse_apply_apply
- \+/\- *theorem* apply_eq_iff_eq

Modified data/finset.lean
- \+/\- *theorem* singleton_val
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_empty
- \+ *theorem* singleton_eq_singleton
- \+ *theorem* insert_empty_eq_singleton
- \+ *theorem* insert_singleton_self_eq
- \+ *theorem* inter_eq_empty_iff_disjoint
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+/\- *theorem* inter_singleton_of_mem
- \+/\- *theorem* inter_singleton_of_not_mem
- \+/\- *theorem* image_singleton
- \+/\- *theorem* fold_insert
- \+/\- *theorem* fold_singleton
- \+/\- *theorem* fold_image
- \+/\- *theorem* fold_union_inter
- \+/\- *theorem* fold_insert_idem
- \- *theorem* insert_singelton_self_eq
- \+ *def* singleton

Modified data/fintype.lean
- \+ *theorem* exists_equiv_fin
- \+ *def* card
- \+ *def* equiv_fin

Modified data/list/basic.lean
- \+ *theorem* pairwise_iff_nth_le
- \+ *theorem* nodup_iff_nth_le_inj

Modified data/multiset.lean
- \+/\- *theorem* mem_add

Modified data/nat/prime.lean
- \+ *def* factors

Modified data/quot.lean
- \+ *theorem* nonempty_of_trunc

Modified data/set/basic.lean
- \+ *lemma* range_iff_surjective
- \+/\- *lemma* range_id
- \- *lemma* range_of_surjective
- \+/\- *theorem* subset_empty_iff
- \+ *theorem* subset_eq_empty
- \+ *theorem* subset_ne_empty
- \+ *theorem* eq_univ_iff_forall
- \+/\- *theorem* eq_univ_of_forall
- \+/\- *theorem* inter_subset_left
- \+/\- *theorem* inter_subset_right
- \+ *theorem* subset_inter_iff

Modified data/set/finite.lean
- \+ *theorem* finite_mem_finset

Modified logic/basic.lean
- \+ *theorem* iff_of_eq
- \+ *theorem* iff_iff_eq

Modified order/basic.lean
- \+/\- *def* monotone

Modified order/filter.lean
- \+ *lemma* map_def
- \+/\- *lemma* bind_def
- \+/\- *lemma* mem_bind_sets
- \+/\- *lemma* bind_mono
- \+/\- *lemma* bind_sup
- \+/\- *lemma* bind_mono2
- \+/\- *lemma* principal_bind
- \- *lemma* fmap_principal
- \+ *def* bind



## [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/b207991)
refactor(data/multiset): move multiset, finset, ordered_monoid
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/default.lean


Modified algebra/ordered_group.lean
- \+ *lemma* add_le_add_left'
- \+ *lemma* add_le_add_right'
- \+ *lemma* lt_of_add_lt_add_left'
- \+ *lemma* add_le_add'
- \+ *lemma* le_add_of_nonneg_right'
- \+ *lemma* le_add_of_nonneg_left'
- \+ *lemma* lt_of_add_lt_add_right'
- \+ *lemma* le_add_of_nonneg_of_le'
- \+ *lemma* le_add_of_le_of_nonneg'
- \+ *lemma* add_nonneg'
- \+ *lemma* add_pos_of_pos_of_nonneg'
- \+ *lemma* add_pos'
- \+ *lemma* add_pos_of_nonneg_of_pos'
- \+ *lemma* add_nonpos'
- \+ *lemma* add_le_of_nonpos_of_le'
- \+ *lemma* add_le_of_le_of_nonpos'
- \+ *lemma* add_neg_of_neg_of_nonpos'
- \+ *lemma* add_neg_of_nonpos_of_neg'
- \+ *lemma* add_neg'
- \+ *lemma* lt_add_of_nonneg_of_lt'
- \+ *lemma* lt_add_of_lt_of_nonneg'
- \+ *lemma* lt_add_of_pos_of_lt'
- \+ *lemma* lt_add_of_lt_of_pos'
- \+ *lemma* add_lt_of_nonpos_of_lt'
- \+ *lemma* add_lt_of_lt_of_nonpos'
- \+ *lemma* add_lt_of_neg_of_lt'
- \+ *lemma* add_lt_of_lt_of_neg'
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \+ *lemma* le_iff_exists_add
- \+ *lemma* zero_le
- \+ *lemma* add_eq_zero_iff

Deleted algebra/ordered_monoid.lean
- \- *lemma* add_le_add_left'
- \- *lemma* add_le_add_right'
- \- *lemma* lt_of_add_lt_add_left'
- \- *lemma* add_le_add'
- \- *lemma* le_add_of_nonneg_right'
- \- *lemma* le_add_of_nonneg_left'
- \- *lemma* lt_of_add_lt_add_right'
- \- *lemma* le_add_of_nonneg_of_le'
- \- *lemma* le_add_of_le_of_nonneg'
- \- *lemma* add_nonneg'
- \- *lemma* add_pos_of_pos_of_nonneg'
- \- *lemma* add_pos'
- \- *lemma* add_pos_of_nonneg_of_pos'
- \- *lemma* add_nonpos'
- \- *lemma* add_le_of_nonpos_of_le'
- \- *lemma* add_le_of_le_of_nonpos'
- \- *lemma* add_neg_of_neg_of_nonpos'
- \- *lemma* add_neg_of_nonpos_of_neg'
- \- *lemma* add_neg'
- \- *lemma* lt_add_of_nonneg_of_lt'
- \- *lemma* lt_add_of_lt_of_nonneg'
- \- *lemma* lt_add_of_pos_of_lt'
- \- *lemma* lt_add_of_lt_of_pos'
- \- *lemma* add_lt_of_nonpos_of_lt'
- \- *lemma* add_lt_of_lt_of_nonpos'
- \- *lemma* add_lt_of_neg_of_lt'
- \- *lemma* add_lt_of_lt_of_neg'
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \- *lemma* le_iff_exists_add
- \- *lemma* zero_le
- \- *lemma* add_eq_zero_iff

Modified analysis/ennreal.lean


Modified data/encodable.lean


Renamed data/finset/basic.lean to data/finset.lean


Deleted data/finset/default.lean


Renamed data/finset/fintype.lean to data/fintype.lean


Renamed data/multiset/basic.lean to data/multiset.lean


Modified data/set/finite.lean




## [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f9b6671)
Revert "fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/1871)"
This reverts commit b9dcc64a998c417551d95f3b0d9b8ee8b690d21b.
#### Estimated changes
Modified algebra/group.lean




## [2017-11-28 19:14:05+01:00](https://github.com/leanprover-community/mathlib/commit/67aecac)
fix(data/option): adapt to https://github.com/leanprover/lean/commit/f6b113849b367d49fc4a506f0698c7f1e062851e
#### Estimated changes
Modified data/option.lean




## [2017-11-24 05:22:02-05:00](https://github.com/leanprover-community/mathlib/commit/2c84af1)
feat(data/set/finite): unify fintype and finite developments
Here fintype is the "constructive" one, which exhibits a list enumerating the set (quotiented over permutations), while "finite" merely states the existence of such a list.
#### Estimated changes
Modified algebra/big_operators.lean


Modified analysis/real.lean


Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_open_sInter

Modified analysis/topology/uniform_space.lean


Modified data/bool.lean


Modified data/encodable.lean
- \+ *def* encodable_of_list
- \+ *def* trunc_encodable_of_fintype

Modified data/finset/basic.lean


Modified data/finset/fintype.lean
- \+ *theorem* mem_univ_val

Modified data/list/basic.lean
- \+/\- *theorem* nodup_filter_map

Modified data/set/basic.lean
- \+ *theorem* mem_def

Modified data/set/countable.lean
- \+/\- *lemma* countable.to_encodable
- \+/\- *lemma* countable_encodable'
- \+/\- *lemma* countable_finite

Modified data/set/finite.lean
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* finite_prod
- \+ *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_val
- \+ *theorem* finite.mem_to_finset
- \+ *theorem* finite_empty
- \+/\- *theorem* finite_insert
- \+ *theorem* finite.induction_on
- \+/\- *theorem* finite_singleton
- \+/\- *theorem* finite_union
- \+/\- *theorem* finite_subset
- \+/\- *theorem* finite_image
- \+ *theorem* finite_Union
- \+/\- *theorem* finite_sUnion
- \+ *def* finite
- \+ *def* fintype_of_finset
- \+ *def* to_finset
- \+ *def* fintype_insert'
- \+ *def* fintype_subset
- \+ *def* fintype_of_fintype_image

Modified data/set/lattice.lean
- \+ *lemma* sUnion_eq_Union'

Modified logic/basic.lean


Modified logic/function.lean
- \+ *theorem* injective_of_partial_inv
- \+ *theorem* injective_of_partial_inv_right
- \+ *theorem* partial_inv_of_injective
- \- *theorem* partial_inv_eq
- \- *theorem* partial_inv_eq_of_eq
- \+ *def* is_partial_inv

Modified order/filter.lean


Modified tests/finish3.lean




## [2017-11-24 05:19:35-05:00](https://github.com/leanprover-community/mathlib/commit/e576429)
feat(data/multiset): filter_map
#### Estimated changes
Modified data/multiset/basic.lean
- \+ *theorem* coe_filter_map
- \+ *theorem* filter_map_zero
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
- \+ *theorem* filter_map_le_filter_map
- \+ *theorem* nodup_filter_map
- \+ *def* filter_map



## [2017-11-24 05:18:50-05:00](https://github.com/leanprover-community/mathlib/commit/bade51a)
feat(data/quot): add trunc type (like nonempty in Type)
It is named after the propositional truncation operator in HoTT, although of course the behavior is a bit different in a proof irrelevant setting.
#### Estimated changes
Modified data/quot.lean
- \- *lemma* forall_quotient_iff
- \+ *theorem* forall_quotient_iff
- \+ *theorem* quot.out_eq
- \+ *theorem* quotient.out_eq
- \+ *theorem* quotient.mk_out
- \+ *theorem* ind
- \+ *theorem* exists_rep
- \+ *theorem* out_eq
- \+ *def* {u}
- \+ *def* mk
- \+ *def* lift



## [2017-11-23 23:33:09-05:00](https://github.com/leanprover-community/mathlib/commit/16d40d7)
feat(data/finset): fintype, multiset.sort, list.pmap
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_bind
- \+/\- *lemma* prod_product

Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified data/encodable.lean


Modified data/equiv.lean
- \- *lemma* map_comp
- \- *lemma* map_id
- \- *lemma* left_inverse.f_g_eq_id
- \- *lemma* right_inverse.g_f_eq_id
- \- *lemma* coe_fn_mk
- \- *lemma* eq_of_to_fun_eq
- \- *lemma* coe_fn_symm_mk
- \- *lemma* id_apply
- \- *lemma* comp_apply
- \- *lemma* apply_inverse_apply
- \- *lemma* inverse_apply_apply
- \- *lemma* eq_iff_eq_of_injective
- \- *lemma* apply_eq_iff_eq
- \- *lemma* apply_eq_iff_eq_inverse_apply
- \- *lemma* empty_of_not_nonempty
- \- *lemma* arrow_empty_unit
- \- *lemma* swap_core_self
- \- *lemma* swap_core_swap_core
- \- *lemma* swap_core_comm
- \- *lemma* swap_self
- \- *lemma* swap_comm
- \- *lemma* swap_apply_def
- \- *lemma* swap_apply_left
- \- *lemma* swap_apply_right
- \- *lemma* swap_apply_of_ne_of_ne
- \- *lemma* swap_swap
- \- *lemma* swap_comp_apply
- \+ *theorem* map_comp
- \+ *theorem* map_id
- \+ *theorem* left_inverse.f_g_eq_id
- \+ *theorem* right_inverse.g_f_eq_id
- \+ *theorem* coe_fn_mk
- \+ *theorem* eq_of_to_fun_eq
- \+ *theorem* coe_fn_symm_mk
- \+ *theorem* id_apply
- \+ *theorem* comp_apply
- \+ *theorem* apply_inverse_apply
- \+ *theorem* inverse_apply_apply
- \+ *theorem* apply_eq_iff_eq
- \+ *theorem* apply_eq_iff_eq_inverse_apply
- \+ *theorem* swap_core_self
- \+ *theorem* swap_core_swap_core
- \+ *theorem* swap_core_comm
- \+ *theorem* swap_self
- \+ *theorem* swap_comm
- \+ *theorem* swap_apply_def
- \+ *theorem* swap_apply_left
- \+ *theorem* swap_apply_right
- \+ *theorem* swap_apply_of_ne_of_ne
- \+ *theorem* swap_swap
- \+ *theorem* swap_comp_apply
- \+ *def* empty_of_not_nonempty
- \+ *def* arrow_empty_unit
- \+ *def* sum_equiv_sigma_bool

Modified data/finset/basic.lean
- \+ *theorem* mem_mk
- \+ *theorem* attach_val
- \+ *theorem* mem_attach
- \+ *theorem* bind_val
- \+ *theorem* bind_empty
- \+ *theorem* mem_bind
- \+ *theorem* bind_insert
- \+ *theorem* image_bind
- \+ *theorem* bind_image
- \+ *theorem* bind_to_finset
- \+ *theorem* product_val
- \+ *theorem* mem_product
- \+ *theorem* product_eq_bind
- \+ *theorem* mem_sigma
- \+ *theorem* sigma_mono
- \+ *theorem* sigma_eq_bind
- \+ *theorem* fold_empty
- \+ *theorem* fold_insert
- \+ *theorem* fold_singleton
- \+ *theorem* fold_image
- \+ *theorem* fold_congr
- \+ *theorem* fold_op_distrib
- \+ *theorem* fold_hom
- \+ *theorem* fold_union_inter
- \+ *theorem* fold_insert_idem
- \+ *theorem* sort_sorted
- \+ *theorem* sort_eq
- \+ *theorem* sort_nodup
- \+ *theorem* sort_to_finset
- \- *theorem* mem_univ
- \- *theorem* subset_univ
- \+ *def* attach
- \+ *def* fold
- \+ *def* sort
- \- *def* fintype.of_multiset
- \- *def* fintype.of_list
- \- *def* univ

Modified data/finset/default.lean


Created data/finset/fintype.lean
- \+ *theorem* mem_univ
- \+ *theorem* subset_univ
- \+ *def* univ
- \+ *def* of_multiset
- \+ *def* of_list
- \+ *def* of_bijective
- \+ *def* of_surjective
- \+ *def* of_equiv

Deleted data/finset/fold.lean
- \- *theorem* fold_empty
- \- *theorem* fold_insert
- \- *theorem* fold_singleton
- \- *theorem* fold_image
- \- *theorem* fold_congr
- \- *theorem* fold_op_distrib
- \- *theorem* fold_hom
- \- *theorem* fold_union_inter
- \- *theorem* fold_insert_idem
- \- *theorem* bind_empty
- \- *theorem* bind_insert
- \- *theorem* mem_bind
- \- *theorem* image_bind
- \- *theorem* bind_image
- \- *theorem* bind_to_finset
- \- *theorem* product_val
- \- *theorem* mem_product
- \- *theorem* product_eq_bind
- \- *theorem* mem_sigma
- \- *theorem* sigma_mono
- \- *def* fold

Modified data/list/basic.lean
- \+ *theorem* pmap_eq_map
- \+ *theorem* pmap_congr
- \+ *theorem* map_pmap
- \+ *theorem* pmap_eq_map_attach
- \+ *theorem* attach_map_val
- \+ *theorem* mem_attach
- \+ *theorem* mem_pmap
- \+ *theorem* nil_sigma
- \+ *theorem* sigma_cons
- \+ *theorem* sigma_nil
- \+ *theorem* mem_sigma
- \+ *theorem* length_sigma
- \+ *theorem* nodup_attach
- \+ *theorem* nodup_pmap
- \+ *theorem* nodup_sigma
- \+ *def* pmap
- \+ *def* attach
- \+ *def* sigma

Modified data/list/perm.lean
- \+ *theorem* perm_pmap

Modified data/list/sort.lean
- \+/\- *def* split

Modified data/multiset/basic.lean
- \+ *theorem* prod_repeat
- \+ *theorem* coe_sigma
- \+ *theorem* zero_sigma
- \+ *theorem* cons_sigma
- \+ *theorem* sigma_singleton
- \+ *theorem* add_sigma
- \+ *theorem* sigma_add
- \+ *theorem* mem_sigma
- \+ *theorem* coe_pmap
- \+ *theorem* coe_attach
- \+ *theorem* pmap_eq_map
- \+ *theorem* pmap_congr
- \+ *theorem* map_pmap
- \+ *theorem* pmap_eq_map_attach
- \+ *theorem* attach_map_val
- \+ *theorem* mem_attach
- \+ *theorem* mem_pmap
- \+ *theorem* count_smul
- \+ *theorem* nodup_attach
- \+ *theorem* nodup_pmap
- \+ *theorem* nodup_sigma
- \+ *theorem* le_smul_erase_dup
- \+ *theorem* coe_sort
- \+ *theorem* sort_sorted
- \+ *theorem* sort_eq
- \+ *def* pmap
- \+ *def* attach
- \+ *def* sort

Modified logic/basic.lean
- \- *lemma* false_neq_true
- \- *lemma* and_iff_left_of_imp
- \- *lemma* and_iff_right_of_imp
- \- *lemma* heq_iff_eq
- \- *lemma* cases
- \- *lemma* or_not
- \+ *theorem* false_neq_true
- \+ *theorem* and_iff_left_of_imp
- \+ *theorem* and_iff_right_of_imp
- \+ *theorem* heq_iff_eq
- \+/\- *theorem* forall_true_iff'
- \+/\- *theorem* forall_2_true_iff
- \+/\- *theorem* forall_3_true_iff
- \+ *theorem* cases
- \+ *theorem* or_not

Modified logic/function.lean
- \+/\- *theorem* injective.eq_iff
- \+ *def* injective.decidable_eq



## [2017-11-23 22:09:45-05:00](https://github.com/leanprover-community/mathlib/commit/c03c16d)
feat(algebra/group_power): remove overloaded ^ notation, add smul
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* division_ring.inv_comm_of_comm
- \- *lemma* inv_comm_of_comm

Modified algebra/group.lean


Modified algebra/group_power.lean
- \+/\- *theorem* pow_zero
- \+ *theorem* smul_succ
- \+/\- *theorem* pow_one
- \+ *theorem* add_monoid.smul_one
- \+ *theorem* smul_succ'
- \+ *theorem* add_monoid.zero_smul
- \+ *theorem* add_monoid.smul_mul
- \+ *theorem* smul_bit1
- \+ *theorem* list.sum_repeat
- \+ *theorem* nat.pow_eq_pow
- \+ *theorem* add_monoid.add_smul
- \+ *theorem* add_monoid.neg_smul
- \+/\- *theorem* pow_inv_comm
- \- *theorem* has_pow_nat_eq_pow_nat
- \- *theorem* nat.pow_eq_pow_nat
- \+/\- *def* monoid.pow
- \- *def* pow_nat
- \- *def* pow_int

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified data/rat.lean


Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-23 06:50:37-05:00](https://github.com/leanprover-community/mathlib/commit/33aa50b)
feat(tactic/generalize_proofs): generalize proofs tactic
Borrowed from leanprover/lean[#1704](https://github.com/leanprover-community/mathlib/pull/1704)
#### Estimated changes
Created tactic/generalize_proofs.lean


Modified tactic/interactive.lean




## [2017-11-22 05:33:59-05:00](https://github.com/leanprover-community/mathlib/commit/902b94d)
refactor(data/finset): redefine finsets as subtype of multisets
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* prod_to_finset_of_nodup

Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_structures.lean


Modified data/encodable.lean


Modified data/finset/basic.lean
- \- *lemma* to_finset_eq_of_nodup
- \- *lemma* mem_to_finset_of_nodup_eq
- \- *lemma* sdiff_union_of_subset
- \- *lemma* sdiff_inter_self
- \- *lemma* sdiff_subset_sdiff
- \- *lemma* image_empty
- \- *lemma* mem_image_iff
- \- *lemma* erase_dup_map_erase_dup_eq
- \- *lemma* image_to_finset
- \- *lemma* image_to_finset_of_nodup
- \- *lemma* image_id
- \- *lemma* image_image
- \- *lemma* image_subset_image
- \- *lemma* image_filter
- \- *lemma* image_union
- \- *lemma* image_inter
- \- *lemma* image_singleton
- \- *lemma* image_insert
- \- *lemma* image_eq_empty_iff
- \- *lemma* ne_empty_of_card_eq_succ
- \+ *theorem* eq_of_veq
- \+ *theorem* val_inj
- \+ *theorem* erase_dup_eq_self
- \+ *theorem* mem_def
- \+/\- *theorem* ext
- \+ *theorem* subset_def
- \+/\- *theorem* subset.refl
- \+/\- *theorem* subset.trans
- \+ *theorem* mem_of_subset
- \+/\- *theorem* subset_iff
- \+ *theorem* val_le_iff
- \+ *theorem* empty_val
- \+/\- *theorem* not_mem_empty
- \+ *theorem* ne_empty_of_mem
- \+/\- *theorem* empty_subset
- \+/\- *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* val_eq_zero
- \+ *theorem* subset_empty
- \+/\- *theorem* exists_mem_of_ne_empty
- \+ *theorem* has_insert_eq_insert
- \+ *theorem* insert_def
- \+ *theorem* insert_val
- \+ *theorem* insert_val'
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_insert_self
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* mem_of_mem_insert_of_ne
- \+/\- *theorem* insert_eq_of_mem
- \+/\- *theorem* insert.comm
- \+/\- *theorem* insert_idem
- \+/\- *theorem* insert_ne_empty
- \+ *theorem* insert_subset
- \+/\- *theorem* subset_insert
- \+/\- *theorem* insert_subset_insert
- \+ *theorem* singleton_val
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* insert_singelton_self_eq
- \+ *theorem* union_val_nd
- \+ *theorem* union_val
- \+/\- *theorem* mem_union
- \+/\- *theorem* mem_union_left
- \+/\- *theorem* mem_union_right
- \+/\- *theorem* union_subset
- \+/\- *theorem* subset_union_left
- \+/\- *theorem* subset_union_right
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_assoc
- \+/\- *theorem* union_idempotent
- \+/\- *theorem* union_left_comm
- \+/\- *theorem* union_right_comm
- \+/\- *theorem* union_self
- \+/\- *theorem* union_empty
- \+/\- *theorem* empty_union
- \+/\- *theorem* insert_eq
- \+/\- *theorem* insert_union
- \+/\- *theorem* union_insert
- \+ *theorem* inter_val_nd
- \+ *theorem* inter_val
- \+/\- *theorem* mem_inter
- \+/\- *theorem* mem_of_mem_inter_left
- \+/\- *theorem* mem_of_mem_inter_right
- \+/\- *theorem* inter_subset_left
- \+/\- *theorem* inter_subset_right
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm
- \+/\- *theorem* inter_self
- \+/\- *theorem* inter_empty
- \+/\- *theorem* empty_inter
- \+ *theorem* erase_val
- \+/\- *theorem* mem_erase
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
- \+/\- *theorem* subset_insert_iff
- \+/\- *theorem* erase_insert_subset
- \+/\- *theorem* insert_erase_subset
- \+ *theorem* mem_sdiff
- \+ *theorem* sdiff_union_of_subset
- \+ *theorem* union_sdiff_of_subset
- \+ *theorem* inter_sdiff_self
- \+ *theorem* sdiff_inter_self
- \+ *theorem* sdiff_subset_sdiff
- \+ *theorem* filter_val
- \+/\- *theorem* mem_filter
- \+/\- *theorem* filter_subset
- \+/\- *theorem* filter_filter
- \+/\- *theorem* filter_false
- \+/\- *theorem* filter_union
- \+ *theorem* filter_or
- \+ *theorem* filter_and
- \+ *theorem* filter_not
- \+ *theorem* sdiff_eq_filter
- \+/\- *theorem* filter_union_filter_neg_eq
- \+/\- *theorem* filter_inter_filter_neg_eq
- \+ *theorem* range_val
- \+/\- *theorem* mem_range
- \+/\- *theorem* range_succ
- \+/\- *theorem* not_mem_range_self
- \+/\- *theorem* range_subset
- \+/\- *theorem* exists_nat_subset_range
- \+ *theorem* to_finset_val
- \+ *theorem* to_finset_eq
- \+/\- *theorem* mem_to_finset
- \+ *theorem* mem_univ
- \+ *theorem* subset_univ
- \+ *theorem* image_val
- \+ *theorem* image_empty
- \+ *theorem* mem_image
- \+ *theorem* mem_image_of_mem
- \+ *theorem* image_to_finset
- \+ *theorem* image_val_of_inj_on
- \+ *theorem* image_id
- \+ *theorem* image_image
- \+ *theorem* image_subset_image
- \+ *theorem* image_filter
- \+ *theorem* image_union
- \+ *theorem* image_inter
- \+ *theorem* image_singleton
- \+ *theorem* image_insert
- \+ *theorem* image_eq_empty
- \+ *theorem* card_def
- \+/\- *theorem* card_empty
- \+ *theorem* card_eq_zero
- \+ *theorem* card_pos
- \+/\- *theorem* card_insert_of_not_mem
- \+/\- *theorem* card_insert_le
- \+/\- *theorem* card_erase_of_mem
- \+/\- *theorem* card_range
- \- *theorem* mem_of_mem_list
- \- *theorem* mem_list_of_mem
- \- *theorem* mem_to_finset_of_mem
- \- *theorem* mem_of_subset_of_mem
- \- *theorem* eq_empty_of_subset_empty
- \- *theorem* subset_empty_iff
- \- *theorem* forall_of_forall_insert
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* erase_subset_of_subset_insert
- \- *theorem* subset_insert_of_erase_subset
- \- *theorem* mem_sdiff_iff
- \- *theorem* eq_empty_of_card_eq_zero
- \+/\- *def* erase
- \+ *def* filter
- \+/\- *def* range
- \+/\- *def* to_finset
- \+ *def* fintype.of_multiset
- \+ *def* fintype.of_list
- \+ *def* univ
- \+ *def* image
- \+/\- *def* card
- \- *def* nodup_list
- \- *def* to_nodup_list_of_nodup
- \- *def* to_nodup_list
- \- *def* {u}
- \- *def* to_finset_of_nodup
- \- *def* mem

Modified data/finset/fold.lean
- \- *lemma* fold_to_finset_of_nodup
- \- *lemma* fold_empty
- \- *lemma* fold_insert
- \- *lemma* fold_singleton
- \- *lemma* fold_image
- \- *lemma* fold_congr
- \- *lemma* fold_op_distrib
- \- *lemma* fold_hom
- \- *lemma* fold_union_inter
- \- *lemma* fold_insert_idem
- \- *lemma* bind_empty
- \- *lemma* bind_insert
- \- *lemma* mem_bind_iff
- \- *lemma* image_bind
- \- *lemma* bind_image
- \- *lemma* mem_product_iff
- \- *lemma* mem_sigma_iff
- \- *lemma* sigma_mono
- \+ *theorem* fold_empty
- \+ *theorem* fold_insert
- \+ *theorem* fold_singleton
- \+ *theorem* fold_image
- \+ *theorem* fold_congr
- \+ *theorem* fold_op_distrib
- \+ *theorem* fold_hom
- \+ *theorem* fold_union_inter
- \+ *theorem* fold_insert_idem
- \+ *theorem* bind_empty
- \+ *theorem* bind_insert
- \+ *theorem* mem_bind
- \+ *theorem* image_bind
- \+ *theorem* bind_image
- \+ *theorem* bind_to_finset
- \+ *theorem* product_val
- \+ *theorem* mem_product
- \+ *theorem* product_eq_bind
- \+ *theorem* mem_sigma
- \+ *theorem* sigma_mono
- \+/\- *def* fold

Modified data/list/basic.lean
- \+ *theorem* map_sublist_map
- \+ *theorem* range_concat

Modified data/multiset/basic.lean
- \+ *theorem* subset_zero
- \+ *theorem* card_eq_zero
- \+ *theorem* card_pos
- \+ *theorem* singleton_le
- \+ *theorem* range_zero
- \+ *theorem* range_succ
- \+ *theorem* map_congr
- \+ *theorem* map_le_map
- \+ *theorem* map_subset_map
- \+ *theorem* mem_join
- \+ *theorem* mem_bind
- \+ *theorem* product_singleton
- \+ *theorem* mem_product
- \+/\- *theorem* union_add_distrib
- \+/\- *theorem* add_union_distrib
- \+ *theorem* cons_union_distrib
- \+/\- *theorem* inter_add_distrib
- \+/\- *theorem* add_inter_distrib
- \+ *theorem* cons_inter_distrib
- \+ *theorem* nodup_inter_left
- \+ *theorem* nodup_inter_right
- \+ *theorem* nodup_union
- \+ *theorem* mem_sub_of_nodup
- \+ *theorem* erase_dup_subset'
- \+ *theorem* subset_erase_dup'
- \+/\- *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_ext
- \+ *theorem* erase_dup_map_erase_dup_eq
- \+ *theorem* erase_dup_cons
- \+/\- *theorem* nodup_ndinsert
- \+ *theorem* fold_eq_foldr
- \+ *theorem* coe_fold_r
- \+ *theorem* coe_fold_l
- \+ *theorem* fold_eq_foldl
- \+ *theorem* fold_zero
- \+ *theorem* fold_cons_left
- \+ *theorem* fold_cons_right
- \+ *theorem* fold_cons'_right
- \+ *theorem* fold_cons'_left
- \+ *theorem* fold_add
- \+ *theorem* fold_singleton
- \+ *theorem* fold_distrib
- \+ *theorem* fold_hom
- \+ *theorem* fold_union_inter
- \+ *theorem* fold_erase_dup_idem
- \- *theorem* subset_zero_iff
- \- *theorem* nodup_inter_of_nodup
- \+ *def* fold

Modified data/nat/basic.lean
- \+/\- *theorem* sub_le_right_iff_le_add

Modified data/set/countable.lean


Modified order/filter.lean




## [2017-11-22 05:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/df546eb)
feat(data/set/basic): add coercion from set to type
#### Estimated changes
Modified data/set/basic.lean
- \+ *theorem* set_coe_eq_subtype
- \+ *theorem* set_coe.forall
- \+ *theorem* set_coe.exists



## [2017-11-22 05:26:27-05:00](https://github.com/leanprover-community/mathlib/commit/d548725)
feat(tactic/rcases): support 'rfl' in rcases patterns for subst
Using the special keyword `rfl` in an rcases pattern, as in `rcases h with ⟨a, rfl⟩ | b`, will now perform `subst` on the indicated argument, when it is an equality.
#### Estimated changes
Modified data/hash_map.lean


Modified data/list/perm.lean


Modified data/list/sort.lean


Modified data/multiset/basic.lean


Modified tactic/interactive.lean


Modified tactic/rcases.lean




## [2017-11-20 20:36:26-05:00](https://github.com/leanprover-community/mathlib/commit/b9dcc64)
fix(algebra/group): workaround for [#1871](https://github.com/leanprover-community/mathlib/pull/1871)
Currently, user attributes are not stored in `olean` files, which leads to segfault issues when referencing them using `user_attribute.get_param`. To work around this, we duplicate the stored data in an extra `def`, which *is* stored in the `olean` file.
#### Estimated changes
Modified algebra/group.lean




## [2017-11-20 01:30:51-05:00](https://github.com/leanprover-community/mathlib/commit/40d2b50)
fix(algebra/order): update to lean
The new `not_lt_of_lt` in core is not substitutable for this one because it is in the new algebraic hierarchy and mathlib is still on the old one. But this isn't used anywhere, so I'll just remove it instead of renaming.
#### Estimated changes
Modified algebra/order.lean
- \- *lemma* not_lt_of_lt



## [2017-11-20 01:09:21-05:00](https://github.com/leanprover-community/mathlib/commit/f467c81)
feat(data/multiset): disjoint, nodup, finset ops
#### Estimated changes
Modified data/list/basic.lean
- \+/\- *theorem* sublist_suffix_of_union
- \+/\- *theorem* erase_dup_append
- \- *theorem* disjoint_append_of_disjoint_left
- \+/\- *def* disjoint

Modified data/multiset/basic.lean
- \+/\- *lemma* mem_coe
- \- *lemma* sdiff_union_of_subset
- \- *lemma* sdiff_inter_self
- \- *lemma* sdiff_subset_sdiff
- \- *lemma* image_empty
- \- *lemma* mem_image_iff
- \- *lemma* erase_dup_map_erase_dup_eq
- \- *lemma* image_to_multiset
- \- *lemma* image_to_multiset_of_nodup
- \- *lemma* image_id
- \- *lemma* image_image
- \- *lemma* image_subset_image
- \- *lemma* image_filter
- \- *lemma* image_union
- \- *lemma* image_inter
- \- *lemma* image_singleton
- \- *lemma* image_insert
- \- *lemma* image_eq_empty_iff
- \- *lemma* ne_empty_of_card_eq_succ
- \+/\- *theorem* coe_nil_eq_zero
- \+/\- *theorem* insert_eq_cons
- \+/\- *theorem* cons_coe
- \+/\- *theorem* singleton_coe
- \+/\- *theorem* cons_inj_left
- \+/\- *theorem* cons_inj_right
- \+/\- *theorem* cons_swap
- \+/\- *theorem* mem_cons
- \+/\- *theorem* mem_cons_self
- \+/\- *theorem* exists_cons_of_mem
- \+/\- *theorem* not_mem_zero
- \+/\- *theorem* eq_zero_of_forall_not_mem
- \+/\- *theorem* exists_mem_of_ne_zero
- \+ *theorem* coe_subset
- \+/\- *theorem* subset.refl
- \+/\- *theorem* subset.trans
- \+/\- *theorem* subset_iff
- \+/\- *theorem* mem_of_subset
- \+/\- *theorem* zero_subset
- \+ *theorem* cons_subset
- \+/\- *theorem* subset_of_le
- \+/\- *theorem* mem_of_le
- \+/\- *theorem* coe_le
- \+/\- *theorem* le_induction_on
- \+/\- *theorem* zero_le
- \+ *theorem* le_zero
- \+/\- *theorem* coe_card
- \+/\- *theorem* card_zero
- \+/\- *theorem* card_cons
- \+/\- *theorem* card_le_of_le
- \+/\- *theorem* eq_of_le_of_card_le
- \+/\- *theorem* card_lt_of_lt
- \+/\- *theorem* card_pos_iff_exists_mem
- \+ *theorem* mem_add
- \+/\- *theorem* card_range
- \+/\- *theorem* range_subset
- \+/\- *theorem* mem_range
- \+/\- *theorem* not_mem_range_self
- \+ *theorem* cons_erase
- \+ *theorem* sub_le_self
- \+ *theorem* union_def
- \+/\- *theorem* mem_union
- \+/\- *theorem* mem_inter
- \+ *theorem* le_inter_iff
- \+ *theorem* union_le_iff
- \+ *theorem* union_le_add
- \+ *theorem* coe_disjoint
- \+ *theorem* disjoint.symm
- \+ *theorem* disjoint_comm
- \+ *theorem* disjoint_left
- \+ *theorem* disjoint_right
- \+ *theorem* disjoint_iff_ne
- \+ *theorem* disjoint_of_subset_left
- \+ *theorem* disjoint_of_subset_right
- \+ *theorem* disjoint_of_le_left
- \+ *theorem* disjoint_of_le_right
- \+ *theorem* zero_disjoint
- \+ *theorem* singleton_disjoint
- \+ *theorem* disjoint_singleton
- \+ *theorem* disjoint_add_left
- \+ *theorem* disjoint_add_right
- \+ *theorem* disjoint_cons_left
- \+ *theorem* disjoint_cons_right
- \+ *theorem* inter_eq_zero_iff_disjoint
- \+ *theorem* coe_nodup
- \+ *theorem* forall_mem_ne
- \+ *theorem* nodup_zero
- \+ *theorem* nodup_cons
- \+ *theorem* nodup_cons_of_nodup
- \+ *theorem* nodup_singleton
- \+ *theorem* nodup_of_nodup_cons
- \+ *theorem* not_mem_of_nodup_cons
- \+ *theorem* nodup_of_le
- \+ *theorem* not_nodup_pair
- \+ *theorem* nodup_iff_le
- \+ *theorem* nodup_iff_count_le_one
- \+ *theorem* count_eq_one_of_mem
- \+ *theorem* nodup_add
- \+ *theorem* disjoint_of_nodup_add
- \+ *theorem* nodup_add_of_nodup
- \+ *theorem* nodup_of_nodup_map
- \+ *theorem* nodup_map_on
- \+ *theorem* nodup_map
- \+ *theorem* nodup_filter
- \+ *theorem* nodup_erase_eq_filter
- \+ *theorem* nodup_erase_of_nodup
- \+ *theorem* mem_erase_iff_of_nodup
- \+ *theorem* mem_erase_of_nodup
- \+ *theorem* nodup_product
- \+ *theorem* nodup_range
- \+ *theorem* nodup_inter_of_nodup
- \+ *theorem* nodup_ext
- \+ *theorem* le_iff_subset
- \+ *theorem* range_le
- \+ *theorem* coe_erase_dup
- \+ *theorem* erase_dup_zero
- \+ *theorem* mem_erase_dup
- \+ *theorem* erase_dup_cons_of_mem
- \+ *theorem* erase_dup_cons_of_not_mem
- \+ *theorem* erase_dup_le
- \+ *theorem* erase_dup_subset
- \+ *theorem* subset_erase_dup
- \+ *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_eq_self
- \+ *theorem* le_erase_dup
- \+ *theorem* coe_ndinsert
- \+ *theorem* ndinsert_zero
- \+ *theorem* ndinsert_of_mem
- \+ *theorem* ndinsert_of_not_mem
- \+ *theorem* mem_ndinsert
- \+ *theorem* le_ndinsert_self
- \+ *theorem* mem_ndinsert_self
- \+ *theorem* mem_ndinsert_of_mem
- \+ *theorem* length_ndinsert_of_mem
- \+ *theorem* length_ndinsert_of_not_mem
- \+ *theorem* nodup_ndinsert
- \+ *theorem* ndinsert_le
- \+ *theorem* coe_ndunion
- \+ *theorem* zero_ndunion
- \+ *theorem* cons_ndunion
- \+ *theorem* mem_ndunion
- \+ *theorem* le_ndunion_right
- \+ *theorem* ndunion_le_add
- \+ *theorem* ndunion_le
- \+ *theorem* subset_ndunion_left
- \+ *theorem* le_ndunion_left
- \+ *theorem* ndunion_le_union
- \+ *theorem* nodup_ndunion
- \+ *theorem* ndunion_eq_union
- \+ *theorem* erase_dup_add
- \+ *theorem* coe_ndinter
- \+ *theorem* zero_ndinter
- \+ *theorem* cons_ndinter_of_mem
- \+ *theorem* ndinter_cons_of_not_mem
- \+ *theorem* mem_ndinter
- \+ *theorem* nodup_ndinter
- \+ *theorem* le_ndinter
- \+ *theorem* ndinter_le_left
- \+ *theorem* ndinter_subset_right
- \+ *theorem* ndinter_le_right
- \+ *theorem* inter_le_ndinter
- \+ *theorem* ndinter_eq_inter
- \+ *theorem* ndinter_eq_zero_iff_disjoint
- \- *theorem* eq_zero_of_le_zero
- \- *theorem* eq_cons_erase
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* mem_or_mem_of_mem_union
- \- *theorem* union_subset
- \- *theorem* subset_union_left
- \- *theorem* subset_union_right
- \- *theorem* union_assoc
- \- *theorem* union_idempotent
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* union_self
- \- *theorem* union_empty
- \- *theorem* empty_union
- \- *theorem* insert_eq
- \- *theorem* insert_union
- \- *theorem* union_insert
- \- *theorem* mem_of_mem_inter_left
- \- *theorem* mem_of_mem_inter_right
- \- *theorem* mem_inter_of_mem
- \- *theorem* inter_subset_left
- \- *theorem* inter_subset_right
- \- *theorem* subset_inter
- \- *theorem* inter_comm
- \- *theorem* inter_assoc
- \- *theorem* inter_left_comm
- \- *theorem* inter_right_comm
- \- *theorem* inter_self
- \- *theorem* inter_empty
- \- *theorem* empty_inter
- \- *theorem* insert_inter_of_mem
- \- *theorem* inter_insert_of_mem
- \- *theorem* insert_inter_of_not_mem
- \- *theorem* inter_insert_of_not_mem
- \- *theorem* singleton_inter_of_mem
- \- *theorem* singleton_inter_of_not_mem
- \- *theorem* inter_singleton_of_mem
- \- *theorem* inter_singleton_of_not_mem
- \- *theorem* inter_distrib_left
- \- *theorem* inter_distrib_right
- \- *theorem* union_distrib_left
- \- *theorem* union_distrib_right
- \- *theorem* mem_erase
- \- *theorem* not_mem_erase
- \- *theorem* erase_empty
- \- *theorem* ne_of_mem_erase
- \- *theorem* mem_of_mem_erase
- \- *theorem* mem_erase_of_ne_of_mem
- \- *theorem* erase_insert
- \- *theorem* insert_erase
- \- *theorem* erase_subset_erase
- \- *theorem* erase_subset
- \- *theorem* erase_eq_of_not_mem
- \- *theorem* erase_insert_subset
- \- *theorem* erase_subset_of_subset_insert
- \- *theorem* insert_erase_subset
- \- *theorem* subset_insert_of_erase_subset
- \- *theorem* subset_insert_iff
- \- *theorem* mem_filter
- \- *theorem* filter_subset
- \- *theorem* filter_union
- \- *theorem* filter_filter
- \- *theorem* filter_false
- \- *theorem* filter_union_filter_neg_eq
- \- *theorem* filter_inter_filter_neg_eq
- \- *theorem* mem_sdiff_iff
- \- *theorem* range_zero
- \- *theorem* range_succ
- \- *theorem* exists_nat_subset_range
- \- *theorem* exists_mem_empty_iff
- \- *theorem* exists_mem_insert
- \- *theorem* forall_mem_empty_iff
- \- *theorem* forall_mem_insert
- \- *theorem* card_empty
- \- *theorem* card_insert_of_not_mem
- \- *theorem* card_insert_le
- \- *theorem* eq_empty_of_card_eq_zero
- \- *theorem* card_erase_of_mem
- \+/\- *def* cons
- \+/\- *def* mem
- \+/\- *def* card
- \+/\- *def* range
- \+ *def* disjoint
- \+/\- *def* nodup
- \+ *def* erase_dup
- \+/\- *def* ndinsert
- \+ *def* ndunion
- \+ *def* ndinter
- \- *def* erase



## [2017-11-19 21:14:37-05:00](https://github.com/leanprover-community/mathlib/commit/76a5fea)
fix(*): finish converting structure notation to {, ..s} style
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/finset/basic.lean


Modified data/multiset/basic.lean


Modified data/num/lemmas.lean


Modified data/pfun.lean


Modified data/rat.lean


Modified data/seq/computation.lean


Modified data/set/lattice.lean


Modified order/basic.lean


Modified order/boolean_algebra.lean


Modified order/bounded_lattice.lean


Modified order/complete_boolean_algebra.lean


Modified order/complete_lattice.lean


Modified order/filter.lean


Modified order/lattice.lean


Modified tactic/converter/binders.lean


Modified tactic/converter/old_conv.lean


Modified tactic/finish.lean




## [2017-11-19 19:49:02-05:00](https://github.com/leanprover-community/mathlib/commit/5d65b0a)
fix(algebra/ring): update to lean
#### Estimated changes
Modified algebra/module.lean


Modified algebra/ring.lean




## [2017-11-19 05:53:48-05:00](https://github.com/leanprover-community/mathlib/commit/8067812)
feat(data/multiset): filter, count, distrib lattice
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* length_pos_iff_exists_mem
- \+/\- *theorem* map_const
- \+ *theorem* eq_of_sublist_of_length_le
- \+ *theorem* countp_pos
- \+ *theorem* count_le_count_cons
- \+/\- *theorem* count_pos
- \+ *theorem* diff_append
- \- *theorem* exists_mem_of_countp_pos
- \- *theorem* countp_pos_of_mem
- \- *theorem* count_cons_ge_count
- \- *theorem* mem_of_count_pos
- \- *theorem* count_pos_of_mem

Modified data/list/perm.lean


Modified data/multiset/basic.lean
- \+ *lemma* card_repeat
- \+/\- *theorem* eq_of_le_of_card_le
- \+ *theorem* card_pos_iff_exists_mem
- \+/\- *theorem* eq_zero_of_le_zero
- \+ *theorem* not_mem_zero
- \+ *theorem* zero_subset
- \+ *theorem* eq_zero_of_forall_not_mem
- \+ *theorem* eq_zero_of_subset_zero
- \+ *theorem* subset_zero_iff
- \+ *theorem* exists_mem_of_ne_zero
- \+/\- *theorem* singleton_coe
- \+/\- *theorem* card_add
- \+ *theorem* eq_of_mem_repeat
- \+ *theorem* eq_repeat'
- \+ *theorem* eq_repeat_of_mem
- \+ *theorem* eq_repeat
- \+ *theorem* repeat_subset_singleton
- \+ *theorem* repeat_le_coe
- \+ *theorem* map_const
- \+ *theorem* eq_of_mem_map_const
- \+ *theorem* sub_add'
- \+ *theorem* card_sub
- \+ *theorem* sup_eq_union
- \+ *theorem* inf_eq_inter
- \+ *theorem* union_add_distrib
- \+ *theorem* add_union_distrib
- \+ *theorem* inter_add_distrib
- \+ *theorem* add_inter_distrib
- \+ *theorem* union_add_inter
- \+ *theorem* sub_add_inter
- \+ *theorem* sub_inter
- \+ *theorem* coe_filter
- \+ *theorem* filter_zero
- \+ *theorem* filter_cons_of_pos
- \+ *theorem* filter_cons_of_neg
- \+ *theorem* filter_add
- \+ *theorem* filter_le
- \+ *theorem* filter_subset
- \+ *theorem* mem_filter
- \+ *theorem* of_mem_filter
- \+ *theorem* mem_of_mem_filter
- \+ *theorem* mem_filter_of_mem
- \+ *theorem* filter_eq_self
- \+ *theorem* filter_eq_nil
- \+ *theorem* filter_le_filter
- \+ *theorem* le_filter
- \+ *theorem* filter_sub
- \+ *theorem* filter_union
- \+ *theorem* filter_inter
- \+ *theorem* coe_countp
- \+ *theorem* countp_zero
- \+ *theorem* countp_cons_of_pos
- \+ *theorem* countp_cons_of_neg
- \+ *theorem* countp_eq_card_filter
- \+ *theorem* countp_add
- \+ *theorem* countp_pos
- \+ *theorem* countp_sub
- \+ *theorem* countp_pos_of_mem
- \+ *theorem* countp_le_of_le
- \+ *theorem* coe_count
- \+ *theorem* count_zero
- \+ *theorem* count_cons_self
- \+ *theorem* count_cons_of_ne
- \+ *theorem* count_le_of_le
- \+ *theorem* count_le_count_cons
- \+ *theorem* count_singleton
- \+ *theorem* count_add
- \+ *theorem* count_pos
- \+ *theorem* count_eq_zero_of_not_mem
- \+ *theorem* count_eq_zero
- \+ *theorem* count_repeat
- \+ *theorem* count_erase_self
- \+ *theorem* count_erase_of_ne
- \+ *theorem* count_sub
- \+ *theorem* count_union
- \+ *theorem* count_inter
- \+ *theorem* le_count_iff_repeat_le
- \+ *theorem* ext
- \+ *theorem* le_iff_count
- \- *theorem* not_mem_empty
- \- *theorem* empty_subset
- \- *theorem* eq_empty_of_forall_not_mem
- \- *theorem* eq_empty_of_subset_empty
- \- *theorem* subset_empty_iff
- \- *theorem* exists_mem_of_ne_empty
- \+ *def* repeat
- \+ *def* filter
- \+ *def* countp
- \+ *def* count

Modified data/nat/basic.lean
- \+ *theorem* pred_sub
- \+ *theorem* sub_add_eq_max
- \+ *theorem* sub_add_min
- \+ *theorem* sub_min



## [2017-11-19 00:41:14-05:00](https://github.com/leanprover-community/mathlib/commit/f9de183)
feat(data/multiset): working on multisets, fix rcases bug
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* max_min_distrib_left
- \+ *lemma* max_min_distrib_right
- \+ *lemma* min_max_distrib_left
- \+ *lemma* min_max_distrib_right

Modified analysis/topology/uniform_space.lean


Modified data/list/basic.lean
- \+ *theorem* sum_const_nat
- \+ *theorem* length_join
- \+ *theorem* length_bind
- \+ *theorem* permutations_aux_nil
- \+ *theorem* permutations_aux_cons
- \+ *theorem* mem_erase_of_ne
- \+ *theorem* nil_bag_inter
- \+ *theorem* bag_inter_nil
- \+ *theorem* cons_bag_inter_of_pos
- \+ *theorem* cons_bag_inter_of_neg
- \+ *theorem* mem_bag_inter
- \+ *theorem* bag_inter_sublist_left
- \+ *theorem* nth_range'
- \+ *theorem* nth_range
- \- *theorem* mem_erase_of_ne_of_mem
- \+/\- *def* permutations_aux2
- \+ *def* permutations_aux.rec
- \+/\- *def* permutations_aux
- \- *def* permutations_aux.F
- \- *def* permutations_aux.eqn_1
- \- *def* permutations_aux.eqn_2

Modified data/list/perm.lean
- \+ *theorem* perm_nil
- \+/\- *theorem* perm_diff_right
- \+ *theorem* perm_bag_inter_left
- \+ *theorem* perm_bag_inter_right
- \+ *theorem* permutations_aux2_fst
- \+ *theorem* permutations_aux2_snd_nil
- \+ *theorem* permutations_aux2_snd_cons
- \+ *theorem* permutations_aux2_append
- \+ *theorem* mem_permutations_aux2
- \+ *theorem* mem_permutations_aux2'
- \+ *theorem* length_permutations_aux2
- \+ *theorem* foldr_permutations_aux2
- \+ *theorem* mem_foldr_permutations_aux2
- \+ *theorem* length_foldr_permutations_aux2
- \+ *theorem* length_foldr_permutations_aux2'
- \+ *theorem* perm_of_mem_permutations_aux
- \+ *theorem* perm_of_mem_permutations
- \+ *theorem* length_permutations_aux
- \+ *theorem* length_permutations
- \+ *theorem* mem_permutations_of_perm_lemma
- \+ *theorem* mem_permutations_aux_of_perm
- \+ *theorem* mem_permutations

Modified data/multiset/basic.lean
- \+/\- *theorem* coe_eq_coe
- \+ *theorem* mem_erase_of_ne
- \+ *theorem* coe_map
- \+ *theorem* map_zero
- \+ *theorem* map_cons
- \+ *theorem* map_add
- \+ *theorem* map_map
- \+ *theorem* foldl_zero
- \+ *theorem* foldl_cons
- \+ *theorem* foldl_add
- \+ *theorem* foldr_zero
- \+ *theorem* foldr_cons
- \+ *theorem* foldr_add
- \+/\- *theorem* coe_foldr
- \+/\- *theorem* coe_foldl
- \+ *theorem* prod_eq_foldr
- \+ *theorem* prod_eq_foldl
- \+ *theorem* coe_prod
- \+ *theorem* prod_zero
- \+ *theorem* prod_cons
- \+ *theorem* prod_add
- \+ *theorem* join_zero
- \+ *theorem* join_cons
- \+ *theorem* join_add
- \+ *theorem* coe_bind
- \+ *theorem* zero_bind
- \+ *theorem* cons_bind
- \+ *theorem* add_bind
- \+ *theorem* coe_product
- \+ *theorem* zero_product
- \+ *theorem* cons_product
- \+ *theorem* add_product
- \+ *theorem* product_add
- \+/\- *theorem* le_union_left
- \+/\- *theorem* le_union_right
- \+ *theorem* inter_zero
- \+ *theorem* zero_inter
- \+ *theorem* cons_inter_of_pos
- \+ *theorem* cons_inter_of_neg
- \+ *theorem* inter_le_left
- \+ *theorem* inter_le_right
- \+ *theorem* le_inter
- \+/\- *theorem* union_comm
- \+ *theorem* inter_comm
- \- *theorem* mem_erase_of_ne_of_mem
- \+ *def* bind
- \+ *def* product
- \+ *def* inter
- \- *def* prod_eq_foldr
- \- *def* prod_eq_foldl
- \- *def* sum

Modified data/quot.lean
- \- *lemma* quot_mk_image_univ_eq
- \+ *theorem* quotient.eq

Modified data/set/basic.lean
- \+ *lemma* quot_mk_image_univ_eq

Modified order/boolean_algebra.lean


Modified order/lattice.lean
- \+ *theorem* sup_le_sup_left
- \+ *theorem* sup_le_sup_right

Modified tactic/rcases.lean


Modified theories/set_theory.lean




## [2017-11-18 23:18:32-05:00](https://github.com/leanprover-community/mathlib/commit/d579a56)
fix(*): update to lean
#### Estimated changes
Modified algebra/module.lean


Modified algebra/ordered_group.lean


Modified algebra/ordered_ring.lean


Modified algebra/ring.lean


Modified analysis/ennreal.lean


Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified analysis/topology/topological_structures.lean


Modified order/filter.lean




## [2017-11-15 13:52:33-05:00](https://github.com/leanprover-community/mathlib/commit/6e9d2d5)
fix(data/num): update to lean
#### Estimated changes
Modified data/num/basic.lean


Modified data/num/lemmas.lean




## [2017-11-10 11:32:15+01:00](https://github.com/leanprover-community/mathlib/commit/afddab6)
chore(algebra/module): hide ring parameters, vector_space is no a proper class, remove dual, change variables to implicits
the ring type is often unnecessary it can be computed from the module instance. Also a lot of parameters to lemmas should be implicits as they can be computed from assumptions or the expteced type..
@kckennylau: I removed `dual` as it does not make sense to take about all possible *module structures* possible on the function space `linear_map α β α`. I guess `dual` should be just `linear_map α β α`.
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* smul_smul
- \+/\- *lemma* neg
- \+/\- *lemma* sub
- \+/\- *lemma* mem_ker
- \+/\- *lemma* mul_app
- \+/\- *theorem* ker_of_map_eq_map
- \+/\- *def* ker
- \+/\- *def* im
- \+/\- *def* subspace
- \- *def* dual
- \- *def* vector_space



## [2017-11-10 05:26:42-05:00](https://github.com/leanprover-community/mathlib/commit/0f8a5c8)
refactor(algebra/group): Use a user attr for to_additive
Parts of this commit are redundant pending leanprover/lean[#1857](https://github.com/leanprover-community/mathlib/pull/1857) .
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_empty
- \+/\- *lemma* prod_to_finset_of_nodup
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* prod_const_one
- \+/\- *lemma* prod_image
- \+/\- *lemma* prod_congr
- \+/\- *lemma* prod_inv_distrib
- \- *lemma* prod_eq_of_perm
- \- *lemma* prod_reverse
- \- *theorem* prod_nil
- \- *theorem* prod_cons
- \- *theorem* prod_append
- \- *theorem* prod_join
- \- *theorem* prod_repeat

Modified algebra/group.lean
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj

Modified algebra/group_power.lean
- \+ *theorem* list.prod_repeat

Modified data/finset/fold.lean
- \- *lemma* map_congr
- \- *lemma* foldl_assoc
- \- *lemma* foldl_op_eq_op_foldr_assoc
- \- *lemma* foldl_assoc_comm_cons
- \- *lemma* fold_op_eq_of_perm

Modified data/list/basic.lean
- \+ *lemma* map_congr
- \+ *lemma* foldl_assoc
- \+ *lemma* foldl_op_eq_op_foldr_assoc
- \+ *lemma* foldl_assoc_comm_cons
- \+ *theorem* prod_nil
- \+ *theorem* prod_cons
- \+ *theorem* prod_append
- \+ *theorem* prod_join
- \- *def* sum

Modified data/list/perm.lean
- \+ *lemma* fold_op_eq_of_perm
- \+ *lemma* prod_eq_of_perm
- \+ *lemma* prod_reverse

Modified data/nat/basic.lean
- \+/\- *theorem* size_one



## [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/04dd132)
feat(algebra/big_operators): exists_ne_(one|zero)_of_(prod|sum)_ne_(one|zero)
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* exists_ne_one_of_prod_ne_one



## [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/5923cd0)
feat(data/set/finite): finite_of_finite_image
#### Estimated changes
Modified data/set/finite.lean
- \+ *theorem* finite_of_finite_image

Modified logic/function.lean
- \+ *lemma* inv_fun_comp



## [2017-11-07 19:26:04-05:00](https://github.com/leanprover-community/mathlib/commit/d95bff0)
refactor(data/hash_map): improve hash_map proof
Decrease dependence on implementation details of `array`
#### Estimated changes
Modified data/array/lemmas.lean
- \+/\- *theorem* rev_list_reverse
- \+/\- *theorem* to_list_reverse
- \+/\- *theorem* rev_list_length
- \+/\- *theorem* to_list_length
- \+ *theorem* to_list_nth_le'
- \+ *theorem* write_to_list
- \+/\- *theorem* mem_to_list_enum

Modified data/hash_map.lean
- \+ *theorem* valid.idx_enum
- \+ *theorem* valid.idx_enum_1
- \+/\- *theorem* mk_as_list
- \+ *theorem* mk_valid
- \+/\- *theorem* valid.find_aux_iff
- \- *theorem* foldl_eq_lem
- \- *theorem* valid_aux.unfold_cons
- \- *theorem* valid_aux.nodup
- \- *theorem* valid_aux.eq
- \- *theorem* valid.nodup
- \- *theorem* valid.nodupd
- \- *theorem* valid.eq
- \- *theorem* valid.eq'
- \- *theorem* valid.as_list_length
- \- *theorem* valid.mk
- \+/\- *def* as_list
- \- *def* valid

Modified data/list/basic.lean
- \+ *theorem* join_append
- \+ *theorem* modify_nth_tail_length
- \+ *theorem* modify_nth_length
- \+ *theorem* update_nth_length
- \+/\- *theorem* nth_update_nth_of_lt
- \+ *theorem* drop_eq_nth_le_cons
- \+ *theorem* modify_nth_eq_take_cons_drop
- \+ *theorem* update_nth_eq_take_cons_drop

Modified tactic/interactive.lean




## [2017-11-07 06:09:41-05:00](https://github.com/leanprover-community/mathlib/commit/4ae6a57)
fix(data/array): update to lean
#### Estimated changes
Modified data/array/lemmas.lean
- \+/\- *lemma* push_back_rev_list_core
- \- *lemma* read_write
- \- *lemma* read_write_eq
- \- *lemma* read_write_ne
- \+ *theorem* rev_list_foldr_aux
- \+ *theorem* rev_list_foldr
- \+ *theorem* mem.def
- \+/\- *theorem* rev_list_reverse_core
- \+/\- *theorem* rev_list_reverse
- \+/\- *theorem* to_list_reverse
- \+/\- *theorem* rev_list_length_aux
- \+/\- *theorem* rev_list_length
- \+/\- *theorem* to_list_length
- \+ *theorem* to_list_nth_le_core
- \+ *theorem* to_list_nth_le
- \+/\- *theorem* to_list_nth
- \+ *theorem* to_list_foldl
- \+ *theorem* mem_rev_list_core
- \+ *theorem* mem_rev_list
- \+ *theorem* mem_to_list
- \+/\- *theorem* to_list_to_array
- \+/\- *theorem* push_back_rev_list
- \+/\- *theorem* push_back_to_list
- \+ *theorem* read_foreach_aux
- \+ *theorem* read_foreach
- \+ *theorem* read_map
- \+ *theorem* read_map₂
- \+ *theorem* mem_to_list_enum
- \- *theorem* to_list_nth_core
- \- *theorem* mem_iff_rev_list_mem_core
- \- *theorem* mem_iff_rev_list_mem
- \- *theorem* mem_iff_list_mem
- \- *def* read_foreach_aux
- \- *def* read_foreach
- \- *def* read_map
- \- *def* read_map₂

Modified data/hash_map.lean
- \+ *theorem* valid.nodupd

Modified data/list/basic.lean
- \+/\- *theorem* eq_nil_of_map_eq_nil
- \+ *theorem* map_join
- \+ *theorem* nth_le_of_mem
- \+/\- *theorem* nth_le_nth
- \+/\- *theorem* nth_ge_len
- \+ *theorem* nth_eq_some
- \+ *theorem* nth_of_mem
- \+ *theorem* nth_le_mem
- \+ *theorem* nth_mem
- \+ *theorem* mem_iff_nth_le
- \+ *theorem* mem_iff_nth
- \+/\- *theorem* ext
- \+/\- *theorem* nth_le_reverse_aux1
- \+/\- *theorem* nth_le_reverse_aux2
- \+ *theorem* remove_nth_eq_nth_tail
- \+ *theorem* update_nth_eq_modify_nth
- \+ *theorem* modify_nth_eq_update_nth
- \+ *theorem* nth_modify_nth
- \+ *theorem* nth_modify_nth_eq
- \+ *theorem* nth_modify_nth_ne
- \+ *theorem* nth_update_nth_eq
- \+ *theorem* nth_update_nth_of_lt
- \+ *theorem* nth_update_nth_ne
- \+ *theorem* modify_nth_tail_eq_take_drop
- \+ *theorem* modify_nth_eq_take_drop
- \+/\- *theorem* foldl_append
- \+ *theorem* foldl_join
- \+ *theorem* foldr_join
- \+ *theorem* infix_of_mem_join
- \+ *theorem* length_enum_from
- \+ *theorem* length_enum
- \+ *theorem* enum_from_nth
- \+ *theorem* enum_nth
- \+ *theorem* enum_from_map_snd
- \+ *theorem* enum_map_snd
- \+ *theorem* pairwise.imp_of_mem
- \+ *theorem* pairwise.iff_of_mem
- \+ *theorem* pairwise.and_mem
- \+ *theorem* pairwise.imp_mem
- \+ *theorem* enum_from_map_fst
- \+ *theorem* enum_map_fst
- \- *theorem* pairwise.iff_mem
- \+/\- *def* to_array
- \+ *def* modify_nth_tail
- \+ *def* modify_head
- \+ *def* modify_nth



## [2017-11-06 11:35:36+01:00](https://github.com/leanprover-community/mathlib/commit/2bc7fd4)
feat(data/cardinal): theory for cardinal arithmetic
#### Estimated changes
Created data/cardinal.lean
- \+ *lemma* equiv.of_bijective
- \+ *lemma* schroeder_bernstein
- \+ *lemma* antisymm
- \+ *lemma* option.eq_of_le_some
- \+ *lemma* option.le_Sup
- \+ *lemma* option.Sup_le
- \+ *lemma* option.mem_of_Sup_eq_some
- \+ *lemma* exists_injective_or_surjective
- \+ *lemma* total
- \+ *lemma* power_zero
- \+ *lemma* one_power
- \+ *lemma* zero_power
- \+ *lemma* mul_power
- \+ *lemma* power_sum
- \+ *lemma* power_mul
- \+ *lemma* add_mono
- \+ *lemma* mul_mono
- \+ *lemma* power_mono_left
- \+ *lemma* power_mono_right
- \+ *def* option.strict_partial_order
- \+ *def* option.Sup
- \+ *def* pfun
- \+ *def* pfun.partial_order
- \+ *def* prod_congr
- \+ *def* sum_congr
- \+ *def* arrow_congr_left
- \+ *def* arrow_congr_right
- \+ *def* cardinal
- \+ *def* ω

Modified data/equiv.lean
- \+ *lemma* empty_of_not_nonempty
- \+ *lemma* arrow_empty_unit

Modified data/set/lattice.lean
- \+ *lemma* image_congr



## [2017-11-06 03:28:38-05:00](https://github.com/leanprover-community/mathlib/commit/d62cefd)
refactor(algebra/module): clean up PR commit
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* smul_smul
- \+ *lemma* neg
- \+/\- *lemma* sub
- \+/\- *lemma* add_val
- \+/\- *lemma* zero_val
- \+/\- *lemma* neg_val
- \+/\- *lemma* smul_val
- \+/\- *lemma* map_add_app
- \+/\- *lemma* map_smul_app
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* mem_ker
- \+/\- *lemma* mem_im
- \+/\- *lemma* add_app
- \+/\- *lemma* zero_app
- \+/\- *lemma* neg_app
- \+/\- *lemma* smul_app
- \+ *lemma* one_app
- \+ *lemma* mul_app
- \- *lemma* eq_zero_of_add_self_eq
- \- *lemma* id_app
- \- *lemma* comp_app
- \- *lemma* comp_id
- \- *lemma* id_comp
- \+/\- *theorem* smul_left_distrib
- \+/\- *theorem* smul_right_distrib
- \+/\- *theorem* mul_smul
- \+/\- *theorem* one_smul
- \+/\- *theorem* zero_smul
- \+/\- *theorem* smul_zero
- \+/\- *theorem* neg_smul
- \+ *theorem* neg_one_smul
- \+/\- *theorem* smul_neg
- \+/\- *theorem* smul_sub_left_distrib
- \+/\- *theorem* sub_smul_right_distrib
- \+/\- *theorem* ext
- \+/\- *theorem* ker_of_map_eq_map
- \+/\- *theorem* inj_of_trivial_ker
- \+/\- *theorem* sub_ker
- \- *theorem* add_im
- \- *theorem* zero_im
- \- *theorem* neg_im
- \- *theorem* smul_im
- \- *theorem* comp_assoc
- \- *theorem* comp_add
- \- *theorem* add_comp
- \+/\- *def* ker
- \+/\- *def* im
- \+/\- *def* dual
- \+/\- *def* endomorphism_ring
- \+/\- *def* general_linear_group
- \+ *def* vector_space
- \+ *def* subspace
- \- *def* id

Modified algebra/ring.lean


Deleted algebra/vector_space.lean
- \- *def* dual
- \- *def* general_linear_group



## [2017-11-06 01:31:01-05:00](https://github.com/leanprover-community/mathlib/commit/5cb7fb0)
feat(algebra/vector_space): modules and vector spaces, linear spaces
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* smul_smul
- \+ *lemma* eq_zero_of_add_self_eq
- \+ *lemma* add_val
- \+ *lemma* zero_val
- \+ *lemma* neg_val
- \+ *lemma* smul_val
- \+ *lemma* sub
- \+ *lemma* map_add_app
- \+ *lemma* map_smul_app
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* mem_ker
- \+ *lemma* mem_im
- \+ *lemma* add_app
- \+ *lemma* zero_app
- \+ *lemma* neg_app
- \+ *lemma* smul_app
- \+ *lemma* id_app
- \+ *lemma* comp_app
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *theorem* ext
- \+ *theorem* ker_of_map_eq_map
- \+ *theorem* inj_of_trivial_ker
- \+ *theorem* sub_ker
- \+ *theorem* add_im
- \+ *theorem* zero_im
- \+ *theorem* neg_im
- \+ *theorem* smul_im
- \+ *theorem* comp_assoc
- \+ *theorem* comp_add
- \+ *theorem* add_comp
- \+ *def* ker
- \+ *def* im
- \+ *def* dual
- \+ *def* id
- \+ *def* endomorphism_ring
- \+ *def* general_linear_group
- \- *def* ring.to_module

Modified algebra/ring.lean


Created algebra/vector_space.lean
- \+ *def* dual
- \+ *def* general_linear_group



## [2017-11-06 01:26:58-05:00](https://github.com/leanprover-community/mathlib/commit/0947f96)
feat(data/multiset): working on multiset.union
#### Estimated changes
Modified algebra/group.lean


Modified data/int/basic.lean
- \+ *theorem* mul_sign

Modified data/list/basic.lean
- \+ *theorem* sublist_or_mem_of_sublist
- \+ *theorem* erase_sublist_erase

Modified data/multiset/basic.lean
- \+ *theorem* insert_eq_cons
- \+ *theorem* le_cons_of_not_mem
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_zero
- \+ *theorem* cons_add
- \+/\- *theorem* add_cons
- \+/\- *theorem* eq_cons_erase
- \+ *theorem* le_cons_erase
- \+ *theorem* erase_le_erase
- \+ *theorem* erase_le_iff_le_cons
- \+/\- *theorem* add_sub_of_le
- \+/\- *theorem* sub_add_cancel
- \+ *theorem* add_sub_cancel_left
- \+ *theorem* add_sub_cancel
- \+ *theorem* sub_le_sub_right
- \+ *theorem* sub_le_sub_left
- \+ *theorem* sub_le_iff_le_add
- \+ *theorem* le_sub_add
- \+ *theorem* le_union_left
- \+ *theorem* le_union_right
- \+ *theorem* eq_union_left
- \+ *theorem* union_le_union_right
- \+ *theorem* union_le
- \+ *theorem* union_comm
- \+ *theorem* eq_union_right
- \+ *theorem* union_le_union_left
- \+ *def* union
- \+ *def* nodup
- \+ *def* ndinsert



## [2017-11-05 17:42:46-05:00](https://github.com/leanprover-community/mathlib/commit/2aa6c87)
feat(tactic/norm_num): add support for inv and locations in norm_num
#### Estimated changes
Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-05 01:30:21-04:00](https://github.com/leanprover-community/mathlib/commit/d743fdf)
feat(data/sigma): duplicate sigma basics for psigma
#### Estimated changes
Modified data/sigma/basic.lean
- \+ *lemma* sigma.mk_eq_mk_iff
- \+ *lemma* psigma.mk_eq_mk_iff
- \- *lemma* mk_eq_mk_iff
- \+ *def* sigma.map
- \+ *def* psigma.map
- \- *def* map



## [2017-11-05 00:29:59-05:00](https://github.com/leanprover-community/mathlib/commit/8e99f98)
fix(algebra/field): update to lean
#### Estimated changes
Modified algebra/field.lean
- \- *lemma* inv_ne_zero
- \- *lemma* division_ring.inv_inv
- \- *lemma* division_ring.one_div_div

Modified algebra/ring.lean




## [2017-11-02 17:13:43-04:00](https://github.com/leanprover-community/mathlib/commit/2da9bef)
feat(data/nat/cast,...): add char_zero typeclass for cast_inj
As pointed out by @kbuzzard, the complex numbers are an important example of an unordered characteristic zero field for which we will want cast_inj to be available.
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_ne_zero

Modified data/nat/cast.lean
- \+ *theorem* char_zero_of_inj_zero
- \+ *theorem* add_group.char_zero_of_inj_zero
- \+ *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero

Modified data/rat.lean
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1



## [2017-11-02 02:32:37-04:00](https://github.com/leanprover-community/mathlib/commit/2883c1b)
feat(data/num/lemmas): finish znum isomorphism proof
#### Estimated changes
Modified data/num/lemmas.lean




## [2017-11-02 00:06:37-04:00](https://github.com/leanprover-community/mathlib/commit/efb37f8)
fix(theories/set_theory): workaround for noncomputability bug in lean
#### Estimated changes
Modified theories/set_theory.lean




## [2017-11-01 22:19:53-04:00](https://github.com/leanprover-community/mathlib/commit/0c0c007)
test(tests/norm_num): more tests from [#16](https://github.com/leanprover-community/mathlib/pull/16)
#### Estimated changes
Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-01 22:14:14-04:00](https://github.com/leanprover-community/mathlib/commit/7339f59)
fix(tactic/norm_num): bugfix
#### Estimated changes
Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-01 21:23:52-04:00](https://github.com/leanprover-community/mathlib/commit/5a262df)
fix(tactic/norm_num): fix performance bug in norm_num
#### Estimated changes
Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-01 04:36:53-04:00](https://github.com/leanprover-community/mathlib/commit/6eedc0e)
feat(tactic/norm_num): rewrite norm_num to use simp instead of reflection
#### Estimated changes
Modified tactic/interactive.lean


Modified tactic/norm_num.lean
- \+/\- *lemma* pow_bit0_helper
- \+/\- *lemma* pow_bit1_helper
- \+ *lemma* lt_add_of_pos_helper
- \- *lemma* pow_bit0
- \- *lemma* pow_bit1
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
- \+ *theorem* bit0_zero
- \+ *theorem* bit1_zero
- \- *def* add1
- \- *def* add_n
- \- *def* pos_le
- \- *def* num_le
- \- *def* znum_le
- \- *def* znum.to_pos
- \- *def* znum.to_neg

Modified tests/norm_num.lean




## [2017-11-01 04:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/0663945)
feat(data/num,data/multiset): more properties of binary numbers, begin multisets
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* inv_ne_zero
- \+ *lemma* division_ring.inv_inv
- \+ *lemma* division_ring.inv_div
- \+ *lemma* division_ring.one_div_div

Modified algebra/group_power.lean
- \+ *theorem* has_pow_nat_eq_pow_nat
- \+ *theorem* pow_bit0
- \+ *theorem* pow_bit1

Modified algebra/ordered_group.lean
- \+ *lemma* bit0_pos

Modified algebra/ordered_ring.lean
- \+ *lemma* bit1_pos
- \+ *lemma* bit1_pos'

Modified data/int/basic.lean
- \+ *theorem* cast_coe_nat'

Created data/multiset/basic.lean
- \+ *lemma* mem_coe
- \+ *lemma* sdiff_union_of_subset
- \+ *lemma* sdiff_inter_self
- \+ *lemma* sdiff_subset_sdiff
- \+ *lemma* image_empty
- \+ *lemma* mem_image_iff
- \+ *lemma* erase_dup_map_erase_dup_eq
- \+ *lemma* image_to_multiset
- \+ *lemma* image_to_multiset_of_nodup
- \+ *lemma* image_id
- \+ *lemma* image_image
- \+ *lemma* image_subset_image
- \+ *lemma* image_filter
- \+ *lemma* image_union
- \+ *lemma* image_inter
- \+ *lemma* image_singleton
- \+ *lemma* image_insert
- \+ *lemma* image_eq_empty_iff
- \+ *lemma* ne_empty_of_card_eq_succ
- \+ *theorem* quot_mk_to_coe
- \+ *theorem* quot_mk_to_coe'
- \+ *theorem* coe_eq_coe
- \+ *theorem* subset.refl
- \+ *theorem* subset.trans
- \+ *theorem* subset_iff
- \+ *theorem* mem_of_subset
- \+ *theorem* subset_of_le
- \+ *theorem* mem_of_le
- \+ *theorem* coe_le
- \+ *theorem* le_induction_on
- \+ *theorem* coe_card
- \+ *theorem* card_le_of_le
- \+ *theorem* eq_of_le_of_card_le
- \+ *theorem* card_lt_of_lt
- \+ *theorem* coe_nil_eq_zero
- \+ *theorem* card_zero
- \+ *theorem* zero_le
- \+ *theorem* eq_zero_of_le_zero
- \+ *theorem* not_mem_empty
- \+ *theorem* empty_subset
- \+ *theorem* eq_empty_of_forall_not_mem
- \+ *theorem* eq_empty_of_subset_empty
- \+ *theorem* subset_empty_iff
- \+ *theorem* exists_mem_of_ne_empty
- \+ *theorem* cons_coe
- \+ *theorem* singleton_coe
- \+ *theorem* cons_inj_left
- \+ *theorem* cons_inj_right
- \+ *theorem* mem_cons
- \+ *theorem* mem_cons_self
- \+ *theorem* exists_cons_of_mem
- \+ *theorem* lt_cons_self
- \+ *theorem* le_cons_self
- \+ *theorem* cons_le_cons_iff
- \+ *theorem* cons_le_cons
- \+ *theorem* lt_iff_cons_le
- \+ *theorem* cons_swap
- \+ *theorem* card_cons
- \+ *theorem* coe_add
- \+ *theorem* singleton_add
- \+ *theorem* add_cons
- \+ *theorem* le_add_right
- \+ *theorem* le_add_left
- \+ *theorem* card_add
- \+ *theorem* le_iff_exists_add
- \+ *theorem* coe_erase
- \+ *theorem* erase_zero
- \+ *theorem* erase_cons_head
- \+ *theorem* erase_cons_tail
- \+ *theorem* erase_of_not_mem
- \+ *theorem* eq_cons_erase
- \+ *theorem* card_erase_of_mem
- \+ *theorem* erase_add_left_pos
- \+ *theorem* erase_add_right_pos
- \+ *theorem* erase_add_right_neg
- \+ *theorem* erase_add_left_neg
- \+ *theorem* erase_le
- \+ *theorem* erase_subset
- \+ *theorem* mem_erase_of_ne_of_mem
- \+ *theorem* mem_of_mem_erase
- \+ *theorem* erase_comm
- \+ *theorem* coe_reverse
- \+ *theorem* mem_map
- \+ *theorem* mem_map_of_mem
- \+ *theorem* mem_map_of_inj
- \+ *theorem* coe_foldr
- \+ *theorem* coe_foldl
- \+ *theorem* coe_foldr_swap
- \+ *theorem* foldr_swap
- \+ *theorem* foldl_swap
- \+ *theorem* coe_join
- \+ *theorem* coe_sub
- \+ *theorem* sub_eq_fold_erase
- \+ *theorem* sub_zero
- \+ *theorem* sub_cons
- \+ *theorem* add_sub_of_le
- \+ *theorem* sub_add_cancel
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton_self
- \+ *theorem* singleton_inj
- \+ *theorem* singleton_ne_zero
- \+ *theorem* mem_union
- \+ *theorem* mem_union_left
- \+ *theorem* mem_union_right
- \+ *theorem* mem_or_mem_of_mem_union
- \+ *theorem* union_subset
- \+ *theorem* subset_union_left
- \+ *theorem* subset_union_right
- \+ *theorem* union_assoc
- \+ *theorem* union_idempotent
- \+ *theorem* union_left_comm
- \+ *theorem* union_right_comm
- \+ *theorem* union_self
- \+ *theorem* union_empty
- \+ *theorem* empty_union
- \+ *theorem* insert_eq
- \+ *theorem* insert_union
- \+ *theorem* union_insert
- \+ *theorem* mem_inter
- \+ *theorem* mem_of_mem_inter_left
- \+ *theorem* mem_of_mem_inter_right
- \+ *theorem* mem_inter_of_mem
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* inter_comm
- \+ *theorem* inter_assoc
- \+ *theorem* inter_left_comm
- \+ *theorem* inter_right_comm
- \+ *theorem* inter_self
- \+ *theorem* inter_empty
- \+ *theorem* empty_inter
- \+ *theorem* insert_inter_of_mem
- \+ *theorem* inter_insert_of_mem
- \+ *theorem* insert_inter_of_not_mem
- \+ *theorem* inter_insert_of_not_mem
- \+ *theorem* singleton_inter_of_mem
- \+ *theorem* singleton_inter_of_not_mem
- \+ *theorem* inter_singleton_of_mem
- \+ *theorem* inter_singleton_of_not_mem
- \+ *theorem* inter_distrib_left
- \+ *theorem* inter_distrib_right
- \+ *theorem* union_distrib_left
- \+ *theorem* union_distrib_right
- \+ *theorem* mem_erase
- \+ *theorem* not_mem_erase
- \+ *theorem* erase_empty
- \+ *theorem* ne_of_mem_erase
- \+ *theorem* erase_insert
- \+ *theorem* insert_erase
- \+ *theorem* erase_subset_erase
- \+ *theorem* erase_eq_of_not_mem
- \+ *theorem* erase_insert_subset
- \+ *theorem* erase_subset_of_subset_insert
- \+ *theorem* insert_erase_subset
- \+ *theorem* subset_insert_of_erase_subset
- \+ *theorem* subset_insert_iff
- \+ *theorem* mem_filter
- \+ *theorem* filter_subset
- \+ *theorem* filter_union
- \+ *theorem* filter_filter
- \+ *theorem* filter_false
- \+ *theorem* filter_union_filter_neg_eq
- \+ *theorem* filter_inter_filter_neg_eq
- \+ *theorem* mem_sdiff_iff
- \+ *theorem* mem_range
- \+ *theorem* range_zero
- \+ *theorem* range_succ
- \+ *theorem* not_mem_range_self
- \+ *theorem* range_subset
- \+ *theorem* exists_nat_subset_range
- \+ *theorem* exists_mem_empty_iff
- \+ *theorem* exists_mem_insert
- \+ *theorem* forall_mem_empty_iff
- \+ *theorem* forall_mem_insert
- \+ *theorem* card_empty
- \+ *theorem* card_insert_of_not_mem
- \+ *theorem* card_insert_le
- \+ *theorem* eq_empty_of_card_eq_zero
- \+ *theorem* card_range
- \+ *def* {u}
- \+ *def* mem
- \+ *def* card
- \+ *def* cons
- \+ *def* erase
- \+ *def* map
- \+ *def* foldl
- \+ *def* foldr
- \+ *def* prod
- \+ *def* prod_eq_foldr
- \+ *def* prod_eq_foldl
- \+ *def* sum
- \+ *def* join
- \+ *def* range

Modified data/nat/basic.lean
- \+ *theorem* pred_eq_ppred
- \+ *theorem* sub_eq_psub
- \+ *theorem* ppred_eq_some
- \+ *theorem* ppred_eq_none
- \+ *theorem* psub_eq_some
- \+ *theorem* psub_eq_none
- \+ *theorem* ppred_eq_pred
- \+ *theorem* psub_eq_sub
- \+ *theorem* psub_add
- \+ *theorem* size_one
- \+ *def* ppred
- \+ *def* psub

Modified data/nat/cast.lean
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1

Modified data/num/basic.lean


Modified data/num/lemmas.lean


Modified data/option.lean
- \+ *lemma* none_bind
- \+ *lemma* some_bind
- \+/\- *lemma* bind_some
- \- *lemma* bind_none

Modified data/rat.lean
- \+ *theorem* cast_inv_of_ne_zero
- \+ *theorem* cast_div_of_ne_zero
- \+ *theorem* cast_inv
- \+ *theorem* cast_div

Modified data/seq/seq.lean


