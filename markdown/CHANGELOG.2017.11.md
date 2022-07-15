## [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/f57e59f)
feat(data/analysis): calculations with filters / topologies + misc
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.exists_ne_one_of_prod_ne_one
- \+/\- *lemma* finset.prod_bind
- \+ *theorem* finset.prod_eq_fold
- \+/\- *lemma* finset.prod_image
- \+/\- *lemma* finset.prod_insert
- \+/\- *lemma* finset.prod_sdiff
- \+/\- *lemma* finset.prod_sigma
- \+/\- *lemma* finset.prod_singleton
- \+/\- *lemma* finset.prod_union
- \+/\- *lemma* finset.prod_union_inter

Modified algebra/ordered_group.lean
- \+/\- *lemma* zero_le

Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_iff_mem_nhds
- \+ *lemma* mem_interior_iff_mem_nhds
- \+/\- *lemma* topological_space.mem_nhds_of_is_topological_basis

Added data/analysis/filter.lean
- \+ *theorem* cfilter.coe_mk
- \+ *theorem* cfilter.mem_to_filter_sets
- \+ *def* cfilter.of_equiv
- \+ *theorem* cfilter.of_equiv_val
- \+ *def* cfilter.to_filter
- \+ *theorem* filter.realizer.bot_F
- \+ *theorem* filter.realizer.bot_σ
- \+ *theorem* filter.realizer.le_iff
- \+ *theorem* filter.realizer.map_F
- \+ *theorem* filter.realizer.map_σ
- \+ *theorem* filter.realizer.mem_sets
- \+ *theorem* filter.realizer.ne_bot_iff
- \+ *def* filter.realizer.of_eq
- \+ *def* filter.realizer.of_equiv
- \+ *theorem* filter.realizer.of_equiv_F
- \+ *theorem* filter.realizer.of_equiv_σ
- \+ *def* filter.realizer.of_filter
- \+ *theorem* filter.realizer.principal_F
- \+ *theorem* filter.realizer.principal_σ
- \+ *theorem* filter.realizer.tendsto_iff
- \+ *theorem* filter.realizer.top_F
- \+ *theorem* filter.realizer.top_σ

Added data/analysis/topology.lean
- \+ *def* compact.realizer
- \+ *theorem* ctop.coe_mk
- \+ *theorem* ctop.mem_nhds_to_topsp
- \+ *def* ctop.of_equiv
- \+ *theorem* ctop.of_equiv_val
- \+ *theorem* ctop.realizer.ext'
- \+ *theorem* ctop.realizer.ext
- \+ *theorem* ctop.realizer.is_closed_iff
- \+ *theorem* ctop.realizer.is_open_iff
- \+ *theorem* ctop.realizer.mem_interior_iff
- \+ *theorem* ctop.realizer.nhds_F
- \+ *theorem* ctop.realizer.nhds_σ
- \+ *def* ctop.realizer.of_equiv
- \+ *theorem* ctop.realizer.of_equiv_F
- \+ *theorem* ctop.realizer.of_equiv_σ
- \+ *theorem* ctop.realizer.tendsto_nhds_iff
- \+ *theorem* ctop.to_topsp_is_topological_basis
- \+ *theorem* locally_finite.realizer.to_locally_finite
- \+ *theorem* locally_finite_iff_exists_realizer

Modified data/equiv.lean
- \+/\- *theorem* equiv.apply_eq_iff_eq
- \+/\- *theorem* equiv.apply_inverse_apply
- \+/\- *theorem* equiv.inverse_apply_apply

Modified data/finset.lean
- \+/\- *theorem* finset.fold_image
- \+/\- *theorem* finset.fold_insert
- \+/\- *theorem* finset.fold_insert_idem
- \+/\- *theorem* finset.fold_singleton
- \+/\- *theorem* finset.fold_union_inter
- \+/\- *theorem* finset.image_singleton
- \+ *theorem* finset.insert_empty_eq_singleton
- \- *theorem* finset.insert_singelton_self_eq
- \+ *theorem* finset.insert_singleton_self_eq
- \+ *theorem* finset.inter_eq_empty_iff_disjoint
- \+/\- *theorem* finset.inter_singleton_of_mem
- \+/\- *theorem* finset.inter_singleton_of_not_mem
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_self
- \+ *def* finset.singleton
- \+ *theorem* finset.singleton_eq_singleton
- \+/\- *theorem* finset.singleton_inj
- \+/\- *theorem* finset.singleton_inter_of_mem
- \+/\- *theorem* finset.singleton_inter_of_not_mem
- \+/\- *theorem* finset.singleton_ne_empty
- \+/\- *theorem* finset.singleton_val

Modified data/fintype.lean
- \+ *def* fintype.card
- \+ *def* fintype.equiv_fin
- \+ *theorem* fintype.exists_equiv_fin

Modified data/list/basic.lean
- \+ *theorem* list.nodup_iff_nth_le_inj
- \+ *theorem* list.pairwise_iff_nth_le

Modified data/multiset.lean


Modified data/nat/prime.lean
- \+ *def* nat.factors

Modified data/quot.lean
- \+ *theorem* nonempty_of_trunc

Modified data/set/basic.lean
- \+ *theorem* set.eq_univ_iff_forall
- \+/\- *theorem* set.eq_univ_of_forall
- \+/\- *theorem* set.inter_subset_left
- \+/\- *theorem* set.inter_subset_right
- \+/\- *lemma* set.range_id
- \+ *lemma* set.range_iff_surjective
- \- *lemma* set.range_of_surjective
- \+/\- *theorem* set.subset_empty_iff
- \+ *theorem* set.subset_eq_empty
- \+ *theorem* set.subset_inter_iff
- \+ *theorem* set.subset_ne_empty

Modified data/set/finite.lean
- \+ *theorem* set.finite_mem_finset

Modified logic/basic.lean
- \+ *theorem* iff_iff_eq
- \+ *theorem* iff_of_eq

Modified order/basic.lean
- \+/\- *def* monotone

Modified order/filter.lean
- \+ *def* filter.bind
- \+/\- *lemma* filter.bind_def
- \+/\- *lemma* filter.bind_mono2
- \+/\- *lemma* filter.bind_mono
- \+/\- *lemma* filter.bind_sup
- \- *lemma* filter.fmap_principal
- \+ *lemma* filter.map_def
- \+/\- *lemma* filter.mem_bind_sets
- \+/\- *lemma* filter.principal_bind



## [2017-11-30 22:10:19-05:00](https://github.com/leanprover-community/mathlib/commit/b207991)
refactor(data/multiset): move multiset, finset, ordered_monoid
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/default.lean


Modified algebra/ordered_group.lean
- \+ *lemma* add_eq_zero_iff
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \+ *lemma* add_le_add'
- \+ *lemma* add_le_add_left'
- \+ *lemma* add_le_add_right'
- \+ *lemma* add_le_of_le_of_nonpos'
- \+ *lemma* add_le_of_nonpos_of_le'
- \+ *lemma* add_lt_of_lt_of_neg'
- \+ *lemma* add_lt_of_lt_of_nonpos'
- \+ *lemma* add_lt_of_neg_of_lt'
- \+ *lemma* add_lt_of_nonpos_of_lt'
- \+ *lemma* add_neg'
- \+ *lemma* add_neg_of_neg_of_nonpos'
- \+ *lemma* add_neg_of_nonpos_of_neg'
- \+ *lemma* add_nonneg'
- \+ *lemma* add_nonpos'
- \+ *lemma* add_pos'
- \+ *lemma* add_pos_of_nonneg_of_pos'
- \+ *lemma* add_pos_of_pos_of_nonneg'
- \+ *lemma* le_add_of_le_of_nonneg'
- \+ *lemma* le_add_of_nonneg_left'
- \+ *lemma* le_add_of_nonneg_of_le'
- \+ *lemma* le_add_of_nonneg_right'
- \+ *lemma* le_iff_exists_add
- \+ *lemma* lt_add_of_lt_of_nonneg'
- \+ *lemma* lt_add_of_lt_of_pos'
- \+ *lemma* lt_add_of_nonneg_of_lt'
- \+ *lemma* lt_add_of_pos_of_lt'
- \+ *lemma* lt_of_add_lt_add_left'
- \+ *lemma* lt_of_add_lt_add_right'
- \+ *lemma* zero_le

Deleted algebra/ordered_monoid.lean
- \- *lemma* add_eq_zero_iff
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \- *lemma* add_le_add'
- \- *lemma* add_le_add_left'
- \- *lemma* add_le_add_right'
- \- *lemma* add_le_of_le_of_nonpos'
- \- *lemma* add_le_of_nonpos_of_le'
- \- *lemma* add_lt_of_lt_of_neg'
- \- *lemma* add_lt_of_lt_of_nonpos'
- \- *lemma* add_lt_of_neg_of_lt'
- \- *lemma* add_lt_of_nonpos_of_lt'
- \- *lemma* add_neg'
- \- *lemma* add_neg_of_neg_of_nonpos'
- \- *lemma* add_neg_of_nonpos_of_neg'
- \- *lemma* add_nonneg'
- \- *lemma* add_nonpos'
- \- *lemma* add_pos'
- \- *lemma* add_pos_of_nonneg_of_pos'
- \- *lemma* add_pos_of_pos_of_nonneg'
- \- *lemma* le_add_of_le_of_nonneg'
- \- *lemma* le_add_of_nonneg_left'
- \- *lemma* le_add_of_nonneg_of_le'
- \- *lemma* le_add_of_nonneg_right'
- \- *lemma* le_iff_exists_add
- \- *lemma* lt_add_of_lt_of_nonneg'
- \- *lemma* lt_add_of_lt_of_pos'
- \- *lemma* lt_add_of_nonneg_of_lt'
- \- *lemma* lt_add_of_pos_of_lt'
- \- *lemma* lt_of_add_lt_add_left'
- \- *lemma* lt_of_add_lt_add_right'
- \- *lemma* zero_le

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
- \+ *theorem* finset.mem_univ_val

Modified data/list/basic.lean
- \+/\- *theorem* list.nodup_filter_map

Modified data/set/basic.lean
- \+ *theorem* set.mem_def

Modified data/set/countable.lean
- \+/\- *lemma* set.countable.to_encodable
- \+/\- *lemma* set.countable_encodable'
- \+/\- *lemma* set.countable_finite

Modified data/set/finite.lean
- \+ *theorem* set.finite.induction_on
- \+ *theorem* set.finite.mem_to_finset
- \+ *def* set.finite
- \+ *theorem* set.finite_Union
- \+ *theorem* set.finite_empty
- \+/\- *theorem* set.finite_image
- \+/\- *theorem* set.finite_insert
- \+/\- *lemma* set.finite_le_nat
- \+/\- *lemma* set.finite_prod
- \+/\- *theorem* set.finite_sUnion
- \+/\- *theorem* set.finite_singleton
- \+/\- *theorem* set.finite_subset
- \+/\- *theorem* set.finite_union
- \+ *def* set.fintype_insert'
- \+ *def* set.fintype_of_finset
- \+ *def* set.fintype_of_fintype_image
- \+ *def* set.fintype_subset
- \+ *theorem* set.mem_to_finset
- \+ *theorem* set.mem_to_finset_val
- \+ *def* set.to_finset

Modified data/set/lattice.lean
- \+ *lemma* set.sUnion_eq_Union'

Modified logic/basic.lean


Modified logic/function.lean
- \+ *theorem* function.injective_of_partial_inv
- \+ *theorem* function.injective_of_partial_inv_right
- \+ *def* function.is_partial_inv
- \- *theorem* function.partial_inv_eq
- \- *theorem* function.partial_inv_eq_of_eq
- \+ *theorem* function.partial_inv_of_injective

Modified order/filter.lean


Modified tests/finish3.lean




## [2017-11-24 05:19:35-05:00](https://github.com/leanprover-community/mathlib/commit/e576429)
feat(data/multiset): filter_map
#### Estimated changes
Modified data/multiset/basic.lean
- \+ *theorem* multiset.coe_filter_map
- \+ *theorem* multiset.filter_filter_map
- \+ *def* multiset.filter_map
- \+ *theorem* multiset.filter_map_cons_none
- \+ *theorem* multiset.filter_map_cons_some
- \+ *theorem* multiset.filter_map_eq_filter
- \+ *theorem* multiset.filter_map_eq_map
- \+ *theorem* multiset.filter_map_filter
- \+ *theorem* multiset.filter_map_filter_map
- \+ *theorem* multiset.filter_map_le_filter_map
- \+ *theorem* multiset.filter_map_map
- \+ *theorem* multiset.filter_map_some
- \+ *theorem* multiset.filter_map_zero
- \+ *theorem* multiset.map_filter_map
- \+ *theorem* multiset.map_filter_map_of_inv
- \+ *theorem* multiset.mem_filter_map
- \+ *theorem* multiset.nodup_filter_map



## [2017-11-24 05:18:50-05:00](https://github.com/leanprover-community/mathlib/commit/bade51a)
feat(data/quot): add trunc type (like nonempty in Type)
It is named after the propositional truncation operator in HoTT, although of course the behavior is a bit different in a proof irrelevant setting.
#### Estimated changes
Modified data/quot.lean
- \+ *theorem* forall_quotient_iff
- \- *lemma* forall_quotient_iff
- \+ *theorem* quot.out_eq
- \+ *theorem* quotient.mk_out
- \+ *theorem* quotient.out_eq
- \+ *theorem* trunc.exists_rep
- \+ *theorem* trunc.ind
- \+ *def* trunc.lift
- \+ *def* trunc.mk
- \+ *theorem* trunc.out_eq
- \+ *def* {u}



## [2017-11-23 23:33:09-05:00](https://github.com/leanprover-community/mathlib/commit/16d40d7)
feat(data/finset): fintype, multiset.sort, list.pmap
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_bind
- \+/\- *lemma* finset.prod_product

Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified data/encodable.lean


Modified data/equiv.lean
- \+ *theorem* equiv.apply_eq_iff_eq
- \- *lemma* equiv.apply_eq_iff_eq
- \+ *theorem* equiv.apply_eq_iff_eq_inverse_apply
- \- *lemma* equiv.apply_eq_iff_eq_inverse_apply
- \+ *theorem* equiv.apply_inverse_apply
- \- *lemma* equiv.apply_inverse_apply
- \+ *def* equiv.arrow_empty_unit
- \- *lemma* equiv.arrow_empty_unit
- \+ *theorem* equiv.coe_fn_mk
- \- *lemma* equiv.coe_fn_mk
- \+ *theorem* equiv.coe_fn_symm_mk
- \- *lemma* equiv.coe_fn_symm_mk
- \+ *theorem* equiv.comp_apply
- \- *lemma* equiv.comp_apply
- \+ *def* equiv.empty_of_not_nonempty
- \- *lemma* equiv.empty_of_not_nonempty
- \- *lemma* equiv.eq_iff_eq_of_injective
- \+ *theorem* equiv.eq_of_to_fun_eq
- \- *lemma* equiv.eq_of_to_fun_eq
- \+ *theorem* equiv.id_apply
- \- *lemma* equiv.id_apply
- \+ *theorem* equiv.inverse_apply_apply
- \- *lemma* equiv.inverse_apply_apply
- \+ *def* equiv.sum_equiv_sigma_bool
- \+ *theorem* equiv.swap_apply_def
- \- *lemma* equiv.swap_apply_def
- \+ *theorem* equiv.swap_apply_left
- \- *lemma* equiv.swap_apply_left
- \+ *theorem* equiv.swap_apply_of_ne_of_ne
- \- *lemma* equiv.swap_apply_of_ne_of_ne
- \+ *theorem* equiv.swap_apply_right
- \- *lemma* equiv.swap_apply_right
- \+ *theorem* equiv.swap_comm
- \- *lemma* equiv.swap_comm
- \+ *theorem* equiv.swap_comp_apply
- \- *lemma* equiv.swap_comp_apply
- \+ *theorem* equiv.swap_core_comm
- \- *lemma* equiv.swap_core_comm
- \+ *theorem* equiv.swap_core_self
- \- *lemma* equiv.swap_core_self
- \+ *theorem* equiv.swap_core_swap_core
- \- *lemma* equiv.swap_core_swap_core
- \+ *theorem* equiv.swap_self
- \- *lemma* equiv.swap_self
- \+ *theorem* equiv.swap_swap
- \- *lemma* equiv.swap_swap
- \+ *theorem* function.left_inverse.f_g_eq_id
- \- *lemma* function.left_inverse.f_g_eq_id
- \+ *theorem* function.right_inverse.g_f_eq_id
- \- *lemma* function.right_inverse.g_f_eq_id
- \+ *theorem* subtype.map_comp
- \- *lemma* subtype.map_comp
- \+ *theorem* subtype.map_id
- \- *lemma* subtype.map_id

Modified data/finset/basic.lean
- \+ *def* finset.attach
- \+ *theorem* finset.attach_val
- \+ *theorem* finset.bind_empty
- \+ *theorem* finset.bind_image
- \+ *theorem* finset.bind_insert
- \+ *theorem* finset.bind_to_finset
- \+ *theorem* finset.bind_val
- \+ *def* finset.fold
- \+ *theorem* finset.fold_congr
- \+ *theorem* finset.fold_empty
- \+ *theorem* finset.fold_hom
- \+ *theorem* finset.fold_image
- \+ *theorem* finset.fold_insert
- \+ *theorem* finset.fold_insert_idem
- \+ *theorem* finset.fold_op_distrib
- \+ *theorem* finset.fold_singleton
- \+ *theorem* finset.fold_union_inter
- \+ *theorem* finset.image_bind
- \+ *theorem* finset.mem_attach
- \+ *theorem* finset.mem_bind
- \+ *theorem* finset.mem_mk
- \+ *theorem* finset.mem_product
- \+ *theorem* finset.mem_sigma
- \- *theorem* finset.mem_univ
- \+ *theorem* finset.product_eq_bind
- \+ *theorem* finset.product_val
- \+ *theorem* finset.sigma_eq_bind
- \+ *theorem* finset.sigma_mono
- \+ *def* finset.sort
- \+ *theorem* finset.sort_eq
- \+ *theorem* finset.sort_nodup
- \+ *theorem* finset.sort_sorted
- \+ *theorem* finset.sort_to_finset
- \- *theorem* finset.subset_univ
- \- *def* finset.univ
- \- *def* fintype.of_list
- \- *def* fintype.of_multiset

Modified data/finset/default.lean


Added data/finset/fintype.lean
- \+ *theorem* finset.mem_univ
- \+ *theorem* finset.subset_univ
- \+ *def* finset.univ
- \+ *def* fintype.of_bijective
- \+ *def* fintype.of_equiv
- \+ *def* fintype.of_list
- \+ *def* fintype.of_multiset
- \+ *def* fintype.of_surjective

Deleted data/finset/fold.lean
- \- *theorem* finset.bind_empty
- \- *theorem* finset.bind_image
- \- *theorem* finset.bind_insert
- \- *theorem* finset.bind_to_finset
- \- *def* finset.fold
- \- *theorem* finset.fold_congr
- \- *theorem* finset.fold_empty
- \- *theorem* finset.fold_hom
- \- *theorem* finset.fold_image
- \- *theorem* finset.fold_insert
- \- *theorem* finset.fold_insert_idem
- \- *theorem* finset.fold_op_distrib
- \- *theorem* finset.fold_singleton
- \- *theorem* finset.fold_union_inter
- \- *theorem* finset.image_bind
- \- *theorem* finset.mem_bind
- \- *theorem* finset.mem_product
- \- *theorem* finset.mem_sigma
- \- *theorem* finset.product_eq_bind
- \- *theorem* finset.product_val
- \- *theorem* finset.sigma_mono

Modified data/list/basic.lean
- \+ *def* list.attach
- \+ *theorem* list.attach_map_val
- \+ *theorem* list.length_sigma
- \+ *theorem* list.map_pmap
- \+ *theorem* list.mem_attach
- \+ *theorem* list.mem_pmap
- \+ *theorem* list.mem_sigma
- \+ *theorem* list.nil_sigma
- \+ *theorem* list.nodup_attach
- \+ *theorem* list.nodup_pmap
- \+ *theorem* list.nodup_sigma
- \+ *def* list.pmap
- \+ *theorem* list.pmap_congr
- \+ *theorem* list.pmap_eq_map
- \+ *theorem* list.pmap_eq_map_attach
- \+ *def* list.sigma
- \+ *theorem* list.sigma_cons
- \+ *theorem* list.sigma_nil

Modified data/list/perm.lean
- \+ *theorem* list.perm_pmap

Modified data/list/sort.lean
- \+/\- *def* list.split

Modified data/multiset/basic.lean
- \+ *theorem* multiset.add_sigma
- \+ *def* multiset.attach
- \+ *theorem* multiset.attach_map_val
- \+ *theorem* multiset.coe_attach
- \+ *theorem* multiset.coe_pmap
- \+ *theorem* multiset.coe_sigma
- \+ *theorem* multiset.coe_sort
- \+ *theorem* multiset.cons_sigma
- \+ *theorem* multiset.count_smul
- \+ *theorem* multiset.le_smul_erase_dup
- \+ *theorem* multiset.map_pmap
- \+ *theorem* multiset.mem_attach
- \+ *theorem* multiset.mem_pmap
- \+ *theorem* multiset.mem_sigma
- \+ *theorem* multiset.nodup_attach
- \+ *theorem* multiset.nodup_pmap
- \+ *theorem* multiset.nodup_sigma
- \+ *def* multiset.pmap
- \+ *theorem* multiset.pmap_congr
- \+ *theorem* multiset.pmap_eq_map
- \+ *theorem* multiset.pmap_eq_map_attach
- \+ *theorem* multiset.prod_repeat
- \+ *theorem* multiset.sigma_add
- \+ *theorem* multiset.sigma_singleton
- \+ *def* multiset.sort
- \+ *theorem* multiset.sort_eq
- \+ *theorem* multiset.sort_sorted
- \+ *theorem* multiset.zero_sigma

Modified logic/basic.lean
- \+ *theorem* and_iff_left_of_imp
- \- *lemma* and_iff_left_of_imp
- \+ *theorem* and_iff_right_of_imp
- \- *lemma* and_iff_right_of_imp
- \+ *theorem* classical.cases
- \- *lemma* classical.cases
- \+ *theorem* classical.or_not
- \- *lemma* classical.or_not
- \+ *theorem* false_neq_true
- \- *lemma* false_neq_true
- \+/\- *theorem* forall_2_true_iff
- \+/\- *theorem* forall_3_true_iff
- \+/\- *theorem* forall_true_iff'
- \+ *theorem* heq_iff_eq
- \- *lemma* heq_iff_eq

Modified logic/function.lean
- \+ *def* function.injective.decidable_eq
- \+/\- *theorem* function.injective.eq_iff



## [2017-11-23 22:09:45-05:00](https://github.com/leanprover-community/mathlib/commit/c03c16d)
feat(algebra/group_power): remove overloaded ^ notation, add smul
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* division_ring.inv_comm_of_comm
- \- *lemma* inv_comm_of_comm

Modified algebra/group.lean
- \+ *theorem* inv_comm_of_comm

Modified algebra/group_power.lean
- \+ *theorem* add_monoid.add_smul
- \+ *theorem* add_monoid.neg_smul
- \+ *theorem* add_monoid.smul_mul
- \+ *theorem* add_monoid.smul_one
- \+ *theorem* add_monoid.zero_smul
- \- *theorem* has_pow_nat_eq_pow_nat
- \+ *theorem* list.sum_repeat
- \+/\- *def* monoid.pow
- \+ *theorem* nat.pow_eq_pow
- \- *theorem* nat.pow_eq_pow_nat
- \- *def* pow_int
- \+/\- *theorem* pow_inv_comm
- \- *def* pow_nat
- \+/\- *theorem* pow_one
- \+/\- *theorem* pow_zero
- \+ *theorem* smul_bit1
- \+ *theorem* smul_succ'
- \+ *theorem* smul_succ

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified data/rat.lean


Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-23 06:50:37-05:00](https://github.com/leanprover-community/mathlib/commit/33aa50b)
feat(tactic/generalize_proofs): generalize proofs tactic
Borrowed from leanprover/lean[#1704](https://github.com/leanprover-community/mathlib/pull/1704)
#### Estimated changes
Added tactic/generalize_proofs.lean


Modified tactic/interactive.lean




## [2017-11-22 05:33:59-05:00](https://github.com/leanprover-community/mathlib/commit/902b94d)
refactor(data/finset): redefine finsets as subtype of multisets
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* finset.prod_to_finset_of_nodup

Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_structures.lean


Modified data/encodable.lean


Modified data/finset/basic.lean
- \+/\- *def* finset.card
- \+ *theorem* finset.card_def
- \+ *theorem* finset.card_eq_zero
- \+/\- *theorem* finset.card_erase_of_mem
- \+/\- *theorem* finset.card_insert_le
- \+/\- *theorem* finset.card_insert_of_not_mem
- \+ *theorem* finset.card_pos
- \+/\- *theorem* finset.card_range
- \+/\- *theorem* finset.empty_inter
- \+/\- *theorem* finset.empty_subset
- \+/\- *theorem* finset.empty_union
- \+ *theorem* finset.empty_val
- \- *theorem* finset.eq_empty_of_card_eq_zero
- \+/\- *theorem* finset.eq_empty_of_forall_not_mem
- \- *theorem* finset.eq_empty_of_subset_empty
- \+ *theorem* finset.eq_of_veq
- \+/\- *def* finset.erase
- \+ *theorem* finset.erase_dup_eq_self
- \- *lemma* finset.erase_dup_map_erase_dup_eq
- \+/\- *theorem* finset.erase_empty
- \+/\- *theorem* finset.erase_eq_of_not_mem
- \+/\- *theorem* finset.erase_insert
- \+/\- *theorem* finset.erase_insert_subset
- \+/\- *theorem* finset.erase_subset
- \+/\- *theorem* finset.erase_subset_erase
- \- *theorem* finset.erase_subset_of_subset_insert
- \+ *theorem* finset.erase_val
- \+/\- *theorem* finset.exists_mem_of_ne_empty
- \+/\- *theorem* finset.exists_nat_subset_range
- \+/\- *theorem* finset.ext
- \+ *def* finset.filter
- \+ *theorem* finset.filter_and
- \+/\- *theorem* finset.filter_false
- \+/\- *theorem* finset.filter_filter
- \+/\- *theorem* finset.filter_inter_filter_neg_eq
- \+ *theorem* finset.filter_not
- \+ *theorem* finset.filter_or
- \+/\- *theorem* finset.filter_subset
- \+/\- *theorem* finset.filter_union
- \+/\- *theorem* finset.filter_union_filter_neg_eq
- \+ *theorem* finset.filter_val
- \- *theorem* finset.forall_of_forall_insert
- \+ *theorem* finset.has_insert_eq_insert
- \+ *def* finset.image
- \+ *theorem* finset.image_empty
- \- *lemma* finset.image_empty
- \+ *theorem* finset.image_eq_empty
- \- *lemma* finset.image_eq_empty_iff
- \+ *theorem* finset.image_filter
- \- *lemma* finset.image_filter
- \+ *theorem* finset.image_id
- \- *lemma* finset.image_id
- \+ *theorem* finset.image_image
- \- *lemma* finset.image_image
- \+ *theorem* finset.image_insert
- \- *lemma* finset.image_insert
- \+ *theorem* finset.image_inter
- \- *lemma* finset.image_inter
- \+ *theorem* finset.image_singleton
- \- *lemma* finset.image_singleton
- \+ *theorem* finset.image_subset_image
- \- *lemma* finset.image_subset_image
- \+ *theorem* finset.image_to_finset
- \- *lemma* finset.image_to_finset
- \- *lemma* finset.image_to_finset_of_nodup
- \+ *theorem* finset.image_union
- \- *lemma* finset.image_union
- \+ *theorem* finset.image_val
- \+ *theorem* finset.image_val_of_inj_on
- \+/\- *theorem* finset.insert.comm
- \+ *theorem* finset.insert_def
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.insert_eq_of_mem
- \+/\- *theorem* finset.insert_erase
- \+/\- *theorem* finset.insert_erase_subset
- \+/\- *theorem* finset.insert_idem
- \+/\- *theorem* finset.insert_ne_empty
- \+/\- *theorem* finset.insert_singelton_self_eq
- \+ *theorem* finset.insert_subset
- \+/\- *theorem* finset.insert_subset_insert
- \+/\- *theorem* finset.insert_union
- \+ *theorem* finset.insert_val'
- \+ *theorem* finset.insert_val
- \+/\- *theorem* finset.inter_assoc
- \+/\- *theorem* finset.inter_comm
- \+/\- *theorem* finset.inter_empty
- \+/\- *theorem* finset.inter_left_comm
- \+/\- *theorem* finset.inter_right_comm
- \+ *theorem* finset.inter_sdiff_self
- \+/\- *theorem* finset.inter_self
- \+/\- *theorem* finset.inter_subset_left
- \+/\- *theorem* finset.inter_subset_right
- \+ *theorem* finset.inter_val
- \+ *theorem* finset.inter_val_nd
- \- *def* finset.mem
- \+ *theorem* finset.mem_def
- \+/\- *theorem* finset.mem_erase
- \+/\- *theorem* finset.mem_erase_of_ne_of_mem
- \+/\- *theorem* finset.mem_filter
- \+ *theorem* finset.mem_image
- \- *lemma* finset.mem_image_iff
- \+ *theorem* finset.mem_image_of_mem
- \+/\- *theorem* finset.mem_insert
- \+/\- *theorem* finset.mem_insert_of_mem
- \+/\- *theorem* finset.mem_insert_self
- \+/\- *theorem* finset.mem_inter
- \- *theorem* finset.mem_list_of_mem
- \+/\- *theorem* finset.mem_of_mem_erase
- \+/\- *theorem* finset.mem_of_mem_insert_of_ne
- \+/\- *theorem* finset.mem_of_mem_inter_left
- \+/\- *theorem* finset.mem_of_mem_inter_right
- \- *theorem* finset.mem_of_mem_list
- \+ *theorem* finset.mem_of_subset
- \- *theorem* finset.mem_of_subset_of_mem
- \- *theorem* finset.mem_or_mem_of_mem_union
- \+/\- *theorem* finset.mem_range
- \+ *theorem* finset.mem_sdiff
- \- *theorem* finset.mem_sdiff_iff
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_self
- \- *theorem* finset.mem_to_finset
- \- *theorem* finset.mem_to_finset_of_mem
- \- *lemma* finset.mem_to_finset_of_nodup_eq
- \+/\- *theorem* finset.mem_union
- \+/\- *theorem* finset.mem_union_left
- \+/\- *theorem* finset.mem_union_right
- \+ *theorem* finset.mem_univ
- \- *lemma* finset.ne_empty_of_card_eq_succ
- \+ *theorem* finset.ne_empty_of_mem
- \+/\- *theorem* finset.ne_of_mem_erase
- \+/\- *theorem* finset.not_mem_empty
- \+/\- *theorem* finset.not_mem_erase
- \+/\- *theorem* finset.not_mem_range_self
- \+/\- *def* finset.range
- \+/\- *theorem* finset.range_subset
- \+/\- *theorem* finset.range_succ
- \+ *theorem* finset.range_val
- \+ *theorem* finset.sdiff_eq_filter
- \+ *theorem* finset.sdiff_inter_self
- \- *lemma* finset.sdiff_inter_self
- \+ *theorem* finset.sdiff_subset_sdiff
- \- *lemma* finset.sdiff_subset_sdiff
- \+ *theorem* finset.sdiff_union_of_subset
- \- *lemma* finset.sdiff_union_of_subset
- \+/\- *theorem* finset.singleton_inj
- \+/\- *theorem* finset.singleton_ne_empty
- \+ *theorem* finset.singleton_val
- \+/\- *theorem* finset.subset.refl
- \+/\- *theorem* finset.subset.trans
- \+ *theorem* finset.subset_def
- \+ *theorem* finset.subset_empty
- \- *theorem* finset.subset_empty_iff
- \+/\- *theorem* finset.subset_iff
- \+/\- *theorem* finset.subset_insert
- \+/\- *theorem* finset.subset_insert_iff
- \- *theorem* finset.subset_insert_of_erase_subset
- \+/\- *theorem* finset.subset_union_left
- \+/\- *theorem* finset.subset_union_right
- \+ *theorem* finset.subset_univ
- \- *def* finset.to_finset
- \- *lemma* finset.to_finset_eq_of_nodup
- \- *def* finset.to_finset_of_nodup
- \+/\- *theorem* finset.union_assoc
- \+/\- *theorem* finset.union_comm
- \+/\- *theorem* finset.union_empty
- \+/\- *theorem* finset.union_idempotent
- \+/\- *theorem* finset.union_insert
- \+/\- *theorem* finset.union_left_comm
- \+/\- *theorem* finset.union_right_comm
- \+ *theorem* finset.union_sdiff_of_subset
- \+/\- *theorem* finset.union_self
- \+/\- *theorem* finset.union_subset
- \+ *theorem* finset.union_val
- \+ *theorem* finset.union_val_nd
- \+ *def* finset.univ
- \+ *theorem* finset.val_eq_zero
- \+ *theorem* finset.val_inj
- \+ *theorem* finset.val_le_iff
- \+ *def* fintype.of_list
- \+ *def* fintype.of_multiset
- \+ *theorem* list.mem_to_finset
- \+ *def* list.to_finset
- \+ *theorem* list.to_finset_eq
- \+ *theorem* list.to_finset_val
- \+ *theorem* multiset.mem_to_finset
- \+ *def* multiset.to_finset
- \+ *theorem* multiset.to_finset_eq
- \+ *theorem* multiset.to_finset_val
- \- *def* nodup_list
- \- *def* to_nodup_list
- \- *def* to_nodup_list_of_nodup
- \- *def* {u}

Modified data/finset/fold.lean
- \+ *theorem* finset.bind_empty
- \- *lemma* finset.bind_empty
- \+ *theorem* finset.bind_image
- \- *lemma* finset.bind_image
- \+ *theorem* finset.bind_insert
- \- *lemma* finset.bind_insert
- \+ *theorem* finset.bind_to_finset
- \+/\- *def* finset.fold
- \+ *theorem* finset.fold_congr
- \- *lemma* finset.fold_congr
- \+ *theorem* finset.fold_empty
- \- *lemma* finset.fold_empty
- \+ *theorem* finset.fold_hom
- \- *lemma* finset.fold_hom
- \+ *theorem* finset.fold_image
- \- *lemma* finset.fold_image
- \+ *theorem* finset.fold_insert
- \- *lemma* finset.fold_insert
- \+ *theorem* finset.fold_insert_idem
- \- *lemma* finset.fold_insert_idem
- \+ *theorem* finset.fold_op_distrib
- \- *lemma* finset.fold_op_distrib
- \+ *theorem* finset.fold_singleton
- \- *lemma* finset.fold_singleton
- \- *lemma* finset.fold_to_finset_of_nodup
- \+ *theorem* finset.fold_union_inter
- \- *lemma* finset.fold_union_inter
- \+ *theorem* finset.image_bind
- \- *lemma* finset.image_bind
- \+ *theorem* finset.mem_bind
- \- *lemma* finset.mem_bind_iff
- \+ *theorem* finset.mem_product
- \- *lemma* finset.mem_product_iff
- \+ *theorem* finset.mem_sigma
- \- *lemma* finset.mem_sigma_iff
- \+ *theorem* finset.product_eq_bind
- \+ *theorem* finset.product_val
- \+ *theorem* finset.sigma_mono
- \- *lemma* finset.sigma_mono

Modified data/list/basic.lean
- \+ *theorem* list.map_sublist_map
- \+ *theorem* list.range_concat

Modified data/multiset/basic.lean
- \+/\- *theorem* multiset.add_inter_distrib
- \+/\- *theorem* multiset.add_union_distrib
- \+ *theorem* multiset.card_eq_zero
- \+ *theorem* multiset.card_pos
- \+ *theorem* multiset.coe_fold_l
- \+ *theorem* multiset.coe_fold_r
- \+ *theorem* multiset.cons_inter_distrib
- \+ *theorem* multiset.cons_union_distrib
- \+ *theorem* multiset.erase_dup_cons
- \+ *theorem* multiset.erase_dup_ext
- \+ *theorem* multiset.erase_dup_map_erase_dup_eq
- \+ *theorem* multiset.erase_dup_subset'
- \+ *def* multiset.fold
- \+ *theorem* multiset.fold_add
- \+ *theorem* multiset.fold_cons'_left
- \+ *theorem* multiset.fold_cons'_right
- \+ *theorem* multiset.fold_cons_left
- \+ *theorem* multiset.fold_cons_right
- \+ *theorem* multiset.fold_distrib
- \+ *theorem* multiset.fold_eq_foldl
- \+ *theorem* multiset.fold_eq_foldr
- \+ *theorem* multiset.fold_erase_dup_idem
- \+ *theorem* multiset.fold_hom
- \+ *theorem* multiset.fold_singleton
- \+ *theorem* multiset.fold_union_inter
- \+ *theorem* multiset.fold_zero
- \+/\- *theorem* multiset.inter_add_distrib
- \+ *theorem* multiset.map_congr
- \+ *theorem* multiset.map_le_map
- \+ *theorem* multiset.map_subset_map
- \+ *theorem* multiset.mem_bind
- \+ *theorem* multiset.mem_join
- \+ *theorem* multiset.mem_product
- \+ *theorem* multiset.mem_sub_of_nodup
- \+/\- *theorem* multiset.nodup_erase_dup
- \+ *theorem* multiset.nodup_inter_left
- \- *theorem* multiset.nodup_inter_of_nodup
- \+ *theorem* multiset.nodup_inter_right
- \+/\- *theorem* multiset.nodup_ndinsert
- \+ *theorem* multiset.nodup_union
- \+ *theorem* multiset.product_singleton
- \+ *theorem* multiset.range_succ
- \+ *theorem* multiset.range_zero
- \+ *theorem* multiset.singleton_le
- \+ *theorem* multiset.subset_erase_dup'
- \+ *theorem* multiset.subset_zero
- \- *theorem* multiset.subset_zero_iff
- \+/\- *theorem* multiset.union_add_distrib

Modified data/nat/basic.lean
- \+/\- *theorem* nat.sub_le_right_iff_le_add

Modified data/set/countable.lean


Modified order/filter.lean




## [2017-11-22 05:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/df546eb)
feat(data/set/basic): add coercion from set to type
#### Estimated changes
Modified data/set/basic.lean
- \+ *theorem* set.set_coe.exists
- \+ *theorem* set.set_coe.forall
- \+ *theorem* set.set_coe_eq_subtype



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
- \+/\- *def* list.disjoint
- \- *theorem* list.disjoint_append_of_disjoint_left
- \+/\- *theorem* list.erase_dup_append
- \+/\- *theorem* list.sublist_suffix_of_union

Modified data/multiset/basic.lean
- \+/\- *def* multiset.card
- \+/\- *theorem* multiset.card_cons
- \- *theorem* multiset.card_empty
- \+/\- *theorem* multiset.card_erase_of_mem
- \- *theorem* multiset.card_insert_le
- \- *theorem* multiset.card_insert_of_not_mem
- \+/\- *theorem* multiset.card_range
- \+ *theorem* multiset.coe_disjoint
- \+ *theorem* multiset.coe_erase_dup
- \+ *theorem* multiset.coe_ndinsert
- \+ *theorem* multiset.coe_ndinter
- \+ *theorem* multiset.coe_ndunion
- \+ *theorem* multiset.coe_nodup
- \+ *theorem* multiset.coe_subset
- \+ *theorem* multiset.cons_erase
- \+ *theorem* multiset.cons_ndinter_of_mem
- \+ *theorem* multiset.cons_ndunion
- \+ *theorem* multiset.cons_subset
- \+ *theorem* multiset.count_eq_one_of_mem
- \+ *theorem* multiset.disjoint.symm
- \+ *def* multiset.disjoint
- \+ *theorem* multiset.disjoint_add_left
- \+ *theorem* multiset.disjoint_add_right
- \+ *theorem* multiset.disjoint_comm
- \+ *theorem* multiset.disjoint_cons_left
- \+ *theorem* multiset.disjoint_cons_right
- \+ *theorem* multiset.disjoint_iff_ne
- \+ *theorem* multiset.disjoint_left
- \+ *theorem* multiset.disjoint_of_le_left
- \+ *theorem* multiset.disjoint_of_le_right
- \+ *theorem* multiset.disjoint_of_nodup_add
- \+ *theorem* multiset.disjoint_of_subset_left
- \+ *theorem* multiset.disjoint_of_subset_right
- \+ *theorem* multiset.disjoint_right
- \+ *theorem* multiset.disjoint_singleton
- \- *theorem* multiset.empty_inter
- \- *theorem* multiset.eq_cons_erase
- \- *theorem* multiset.eq_empty_of_card_eq_zero
- \- *theorem* multiset.eq_zero_of_le_zero
- \+/\- *def* multiset.erase
- \+ *def* multiset.erase_dup
- \+ *theorem* multiset.erase_dup_add
- \+ *theorem* multiset.erase_dup_cons_of_mem
- \+ *theorem* multiset.erase_dup_cons_of_not_mem
- \+ *theorem* multiset.erase_dup_eq_self
- \+ *theorem* multiset.erase_dup_le
- \- *lemma* multiset.erase_dup_map_erase_dup_eq
- \+ *theorem* multiset.erase_dup_subset
- \+ *theorem* multiset.erase_dup_zero
- \- *theorem* multiset.erase_empty
- \- *theorem* multiset.erase_eq_of_not_mem
- \- *theorem* multiset.erase_insert
- \- *theorem* multiset.erase_insert_subset
- \+/\- *theorem* multiset.erase_subset
- \- *theorem* multiset.erase_subset_erase
- \- *theorem* multiset.erase_subset_of_subset_insert
- \- *theorem* multiset.exists_mem_empty_iff
- \- *theorem* multiset.exists_mem_insert
- \- *theorem* multiset.exists_nat_subset_range
- \- *theorem* multiset.filter_false
- \- *theorem* multiset.filter_filter
- \- *theorem* multiset.filter_inter_filter_neg_eq
- \+/\- *theorem* multiset.filter_subset
- \+/\- *theorem* multiset.filter_union
- \- *theorem* multiset.filter_union_filter_neg_eq
- \- *theorem* multiset.forall_mem_empty_iff
- \- *theorem* multiset.forall_mem_insert
- \+ *theorem* multiset.forall_mem_ne
- \- *lemma* multiset.image_empty
- \- *lemma* multiset.image_eq_empty_iff
- \- *lemma* multiset.image_filter
- \- *lemma* multiset.image_id
- \- *lemma* multiset.image_image
- \- *lemma* multiset.image_insert
- \- *lemma* multiset.image_inter
- \- *lemma* multiset.image_singleton
- \- *lemma* multiset.image_subset_image
- \- *lemma* multiset.image_to_multiset
- \- *lemma* multiset.image_to_multiset_of_nodup
- \- *lemma* multiset.image_union
- \- *theorem* multiset.insert_erase
- \- *theorem* multiset.insert_erase_subset
- \- *theorem* multiset.insert_inter_of_mem
- \- *theorem* multiset.insert_inter_of_not_mem
- \- *theorem* multiset.inter_assoc
- \+/\- *theorem* multiset.inter_comm
- \- *theorem* multiset.inter_distrib_left
- \- *theorem* multiset.inter_distrib_right
- \- *theorem* multiset.inter_empty
- \+ *theorem* multiset.inter_eq_zero_iff_disjoint
- \- *theorem* multiset.inter_insert_of_mem
- \- *theorem* multiset.inter_insert_of_not_mem
- \+ *theorem* multiset.inter_le_ndinter
- \- *theorem* multiset.inter_left_comm
- \- *theorem* multiset.inter_right_comm
- \- *theorem* multiset.inter_self
- \- *theorem* multiset.inter_singleton_of_mem
- \- *theorem* multiset.inter_singleton_of_not_mem
- \- *theorem* multiset.inter_subset_left
- \- *theorem* multiset.inter_subset_right
- \+ *theorem* multiset.le_erase_dup
- \+ *theorem* multiset.le_iff_subset
- \+ *theorem* multiset.le_inter_iff
- \+ *theorem* multiset.le_ndinsert_self
- \+ *theorem* multiset.le_ndinter
- \+ *theorem* multiset.le_ndunion_left
- \+ *theorem* multiset.le_ndunion_right
- \+ *theorem* multiset.le_zero
- \+ *theorem* multiset.length_ndinsert_of_mem
- \+ *theorem* multiset.length_ndinsert_of_not_mem
- \+ *theorem* multiset.mem_add
- \- *theorem* multiset.mem_erase
- \+ *theorem* multiset.mem_erase_dup
- \+ *theorem* multiset.mem_erase_iff_of_nodup
- \- *theorem* multiset.mem_erase_of_ne_of_mem
- \+ *theorem* multiset.mem_erase_of_nodup
- \+/\- *theorem* multiset.mem_filter
- \- *lemma* multiset.mem_image_iff
- \+/\- *theorem* multiset.mem_inter
- \- *theorem* multiset.mem_inter_of_mem
- \+ *theorem* multiset.mem_ndinsert
- \+ *theorem* multiset.mem_ndinsert_of_mem
- \+ *theorem* multiset.mem_ndinsert_self
- \+ *theorem* multiset.mem_ndinter
- \+ *theorem* multiset.mem_ndunion
- \+/\- *theorem* multiset.mem_of_le
- \+/\- *theorem* multiset.mem_of_mem_erase
- \- *theorem* multiset.mem_of_mem_inter_left
- \- *theorem* multiset.mem_of_mem_inter_right
- \+/\- *theorem* multiset.mem_of_subset
- \+/\- *theorem* multiset.mem_range
- \- *theorem* multiset.mem_sdiff_iff
- \+ *theorem* multiset.mem_union
- \+ *theorem* multiset.ndinsert_le
- \+ *theorem* multiset.ndinsert_of_mem
- \+ *theorem* multiset.ndinsert_of_not_mem
- \+ *theorem* multiset.ndinsert_zero
- \+ *def* multiset.ndinter
- \+ *theorem* multiset.ndinter_cons_of_not_mem
- \+ *theorem* multiset.ndinter_eq_inter
- \+ *theorem* multiset.ndinter_eq_zero_iff_disjoint
- \+ *theorem* multiset.ndinter_le_left
- \+ *theorem* multiset.ndinter_le_right
- \+ *theorem* multiset.ndinter_subset_right
- \+ *def* multiset.ndunion
- \+ *theorem* multiset.ndunion_eq_union
- \+ *theorem* multiset.ndunion_le
- \+ *theorem* multiset.ndunion_le_add
- \+ *theorem* multiset.ndunion_le_union
- \- *lemma* multiset.ne_empty_of_card_eq_succ
- \- *theorem* multiset.ne_of_mem_erase
- \+ *theorem* multiset.nodup_add
- \+ *theorem* multiset.nodup_add_of_nodup
- \+ *theorem* multiset.nodup_cons
- \+ *theorem* multiset.nodup_cons_of_nodup
- \+ *theorem* multiset.nodup_erase_dup
- \+ *theorem* multiset.nodup_erase_eq_filter
- \+ *theorem* multiset.nodup_erase_of_nodup
- \+ *theorem* multiset.nodup_ext
- \+ *theorem* multiset.nodup_filter
- \+ *theorem* multiset.nodup_iff_count_le_one
- \+ *theorem* multiset.nodup_iff_le
- \+ *theorem* multiset.nodup_inter_of_nodup
- \+ *theorem* multiset.nodup_map
- \+ *theorem* multiset.nodup_map_on
- \+ *theorem* multiset.nodup_ndinsert
- \+ *theorem* multiset.nodup_ndinter
- \+ *theorem* multiset.nodup_ndunion
- \+ *theorem* multiset.nodup_of_le
- \+ *theorem* multiset.nodup_of_nodup_cons
- \+ *theorem* multiset.nodup_of_nodup_map
- \+ *theorem* multiset.nodup_product
- \+ *theorem* multiset.nodup_range
- \+ *theorem* multiset.nodup_singleton
- \+ *theorem* multiset.nodup_zero
- \- *theorem* multiset.not_mem_erase
- \+ *theorem* multiset.not_mem_of_nodup_cons
- \+/\- *theorem* multiset.not_mem_range_self
- \+ *theorem* multiset.not_nodup_pair
- \+/\- *def* multiset.range
- \+ *theorem* multiset.range_le
- \+/\- *theorem* multiset.range_subset
- \- *theorem* multiset.range_succ
- \- *theorem* multiset.range_zero
- \- *lemma* multiset.sdiff_inter_self
- \- *lemma* multiset.sdiff_subset_sdiff
- \- *lemma* multiset.sdiff_union_of_subset
- \+ *theorem* multiset.singleton_disjoint
- \- *theorem* multiset.singleton_inter_of_mem
- \- *theorem* multiset.singleton_inter_of_not_mem
- \+ *theorem* multiset.sub_le_self
- \+/\- *theorem* multiset.subset.refl
- \+/\- *theorem* multiset.subset.trans
- \+ *theorem* multiset.subset_erase_dup
- \+/\- *theorem* multiset.subset_iff
- \- *theorem* multiset.subset_insert_iff
- \- *theorem* multiset.subset_insert_of_erase_subset
- \- *theorem* multiset.subset_inter
- \+ *theorem* multiset.subset_ndunion_left
- \+/\- *theorem* multiset.subset_of_le
- \+ *theorem* multiset.union_def
- \- *theorem* multiset.union_distrib_left
- \- *theorem* multiset.union_distrib_right
- \+ *theorem* multiset.union_le_add
- \+ *theorem* multiset.union_le_iff
- \+ *theorem* multiset.zero_disjoint
- \+ *theorem* multiset.zero_ndinter
- \+ *theorem* multiset.zero_ndunion
- \+/\- *theorem* multiset.zero_subset



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
- \- *theorem* list.count_cons_ge_count
- \+ *theorem* list.count_le_count_cons
- \+/\- *theorem* list.count_pos
- \- *theorem* list.count_pos_of_mem
- \+ *theorem* list.countp_pos
- \- *theorem* list.countp_pos_of_mem
- \+ *theorem* list.diff_append
- \+ *theorem* list.eq_of_sublist_of_length_le
- \- *theorem* list.exists_mem_of_countp_pos
- \+ *theorem* list.length_pos_iff_exists_mem
- \+/\- *theorem* list.map_const
- \- *theorem* list.mem_of_count_pos

Modified data/list/perm.lean


Modified data/multiset/basic.lean
- \+ *theorem* multiset.add_inter_distrib
- \+ *theorem* multiset.add_union_distrib
- \+/\- *theorem* multiset.card_add
- \+ *theorem* multiset.card_pos_iff_exists_mem
- \+ *lemma* multiset.card_repeat
- \+ *theorem* multiset.card_sub
- \+ *theorem* multiset.coe_count
- \+ *theorem* multiset.coe_countp
- \+ *theorem* multiset.coe_filter
- \+ *def* multiset.count
- \+ *theorem* multiset.count_add
- \+ *theorem* multiset.count_cons_of_ne
- \+ *theorem* multiset.count_cons_self
- \+ *theorem* multiset.count_eq_zero
- \+ *theorem* multiset.count_eq_zero_of_not_mem
- \+ *theorem* multiset.count_erase_of_ne
- \+ *theorem* multiset.count_erase_self
- \+ *theorem* multiset.count_inter
- \+ *theorem* multiset.count_le_count_cons
- \+ *theorem* multiset.count_le_of_le
- \+ *theorem* multiset.count_pos
- \+ *theorem* multiset.count_repeat
- \+ *theorem* multiset.count_singleton
- \+ *theorem* multiset.count_sub
- \+ *theorem* multiset.count_union
- \+ *theorem* multiset.count_zero
- \+ *def* multiset.countp
- \+ *theorem* multiset.countp_add
- \+ *theorem* multiset.countp_cons_of_neg
- \+ *theorem* multiset.countp_cons_of_pos
- \+ *theorem* multiset.countp_eq_card_filter
- \+ *theorem* multiset.countp_le_of_le
- \+ *theorem* multiset.countp_pos
- \+ *theorem* multiset.countp_pos_of_mem
- \+ *theorem* multiset.countp_sub
- \+ *theorem* multiset.countp_zero
- \- *theorem* multiset.empty_subset
- \- *theorem* multiset.eq_empty_of_forall_not_mem
- \- *theorem* multiset.eq_empty_of_subset_empty
- \+/\- *theorem* multiset.eq_of_le_of_card_le
- \+ *theorem* multiset.eq_of_mem_map_const
- \+ *theorem* multiset.eq_of_mem_repeat
- \+ *theorem* multiset.eq_repeat'
- \+ *theorem* multiset.eq_repeat
- \+ *theorem* multiset.eq_repeat_of_mem
- \+ *theorem* multiset.eq_zero_of_forall_not_mem
- \+/\- *theorem* multiset.eq_zero_of_le_zero
- \+ *theorem* multiset.eq_zero_of_subset_zero
- \- *theorem* multiset.exists_mem_of_ne_empty
- \+ *theorem* multiset.exists_mem_of_ne_zero
- \+ *theorem* multiset.ext
- \+ *def* multiset.filter
- \+ *theorem* multiset.filter_add
- \+ *theorem* multiset.filter_cons_of_neg
- \+ *theorem* multiset.filter_cons_of_pos
- \+ *theorem* multiset.filter_eq_nil
- \+ *theorem* multiset.filter_eq_self
- \+ *theorem* multiset.filter_inter
- \+ *theorem* multiset.filter_le
- \+ *theorem* multiset.filter_le_filter
- \+ *theorem* multiset.filter_sub
- \+/\- *theorem* multiset.filter_subset
- \+/\- *theorem* multiset.filter_union
- \+ *theorem* multiset.filter_zero
- \+ *theorem* multiset.inf_eq_inter
- \+ *theorem* multiset.inter_add_distrib
- \+ *theorem* multiset.le_count_iff_repeat_le
- \+ *theorem* multiset.le_filter
- \+ *theorem* multiset.le_iff_count
- \+ *theorem* multiset.map_const
- \+/\- *theorem* multiset.mem_filter
- \+ *theorem* multiset.mem_filter_of_mem
- \+ *theorem* multiset.mem_of_mem_filter
- \- *theorem* multiset.not_mem_empty
- \+ *theorem* multiset.not_mem_zero
- \+ *theorem* multiset.of_mem_filter
- \+ *def* multiset.repeat
- \+ *theorem* multiset.repeat_le_coe
- \+ *theorem* multiset.repeat_subset_singleton
- \+/\- *theorem* multiset.singleton_coe
- \+ *theorem* multiset.sub_add'
- \+ *theorem* multiset.sub_add_inter
- \+ *theorem* multiset.sub_inter
- \- *theorem* multiset.subset_empty_iff
- \+ *theorem* multiset.subset_zero_iff
- \+ *theorem* multiset.sup_eq_union
- \+ *theorem* multiset.union_add_distrib
- \+ *theorem* multiset.union_add_inter
- \+ *theorem* multiset.zero_subset

Modified data/nat/basic.lean
- \+ *theorem* nat.pred_sub
- \+ *theorem* nat.sub_add_eq_max
- \+ *theorem* nat.sub_add_min
- \+ *theorem* nat.sub_min



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
- \+ *theorem* list.bag_inter_nil
- \+ *theorem* list.bag_inter_sublist_left
- \+ *theorem* list.cons_bag_inter_of_neg
- \+ *theorem* list.cons_bag_inter_of_pos
- \+ *theorem* list.length_bind
- \+ *theorem* list.length_join
- \+ *theorem* list.mem_bag_inter
- \+ *theorem* list.mem_erase_of_ne
- \- *theorem* list.mem_erase_of_ne_of_mem
- \+ *theorem* list.nil_bag_inter
- \+ *theorem* list.nth_range'
- \+ *theorem* list.nth_range
- \- *def* list.permutations_aux.F
- \- *def* list.permutations_aux.eqn_1
- \- *def* list.permutations_aux.eqn_2
- \+ *def* list.permutations_aux.rec
- \+/\- *def* list.permutations_aux2
- \+/\- *def* list.permutations_aux
- \+ *theorem* list.permutations_aux_cons
- \+ *theorem* list.permutations_aux_nil
- \+ *theorem* list.sum_const_nat

Modified data/list/perm.lean
- \+ *theorem* list.foldr_permutations_aux2
- \+ *theorem* list.length_foldr_permutations_aux2'
- \+ *theorem* list.length_foldr_permutations_aux2
- \+ *theorem* list.length_permutations
- \+ *theorem* list.length_permutations_aux2
- \+ *theorem* list.length_permutations_aux
- \+ *theorem* list.mem_foldr_permutations_aux2
- \+ *theorem* list.mem_permutations
- \+ *theorem* list.mem_permutations_aux2'
- \+ *theorem* list.mem_permutations_aux2
- \+ *theorem* list.mem_permutations_aux_of_perm
- \+ *theorem* list.mem_permutations_of_perm_lemma
- \+ *theorem* list.perm_bag_inter_left
- \+ *theorem* list.perm_bag_inter_right
- \+/\- *theorem* list.perm_diff_right
- \+ *theorem* list.perm_nil
- \+ *theorem* list.perm_of_mem_permutations
- \+ *theorem* list.perm_of_mem_permutations_aux
- \+ *theorem* list.permutations_aux2_append
- \+ *theorem* list.permutations_aux2_fst
- \+ *theorem* list.permutations_aux2_snd_cons
- \+ *theorem* list.permutations_aux2_snd_nil

Modified data/multiset/basic.lean
- \+ *theorem* multiset.add_bind
- \+ *theorem* multiset.add_product
- \+ *def* multiset.bind
- \+ *theorem* multiset.coe_bind
- \+/\- *theorem* multiset.coe_eq_coe
- \+/\- *theorem* multiset.coe_foldl
- \+/\- *theorem* multiset.coe_foldr
- \+ *theorem* multiset.coe_map
- \+ *theorem* multiset.coe_prod
- \+ *theorem* multiset.coe_product
- \+ *theorem* multiset.cons_bind
- \+ *theorem* multiset.cons_inter_of_neg
- \+ *theorem* multiset.cons_inter_of_pos
- \+ *theorem* multiset.cons_product
- \+ *theorem* multiset.foldl_add
- \+ *theorem* multiset.foldl_cons
- \+ *theorem* multiset.foldl_zero
- \+ *theorem* multiset.foldr_add
- \+ *theorem* multiset.foldr_cons
- \+ *theorem* multiset.foldr_zero
- \+ *def* multiset.inter
- \+/\- *theorem* multiset.inter_comm
- \+ *theorem* multiset.inter_le_left
- \+ *theorem* multiset.inter_le_right
- \+ *theorem* multiset.inter_zero
- \+ *theorem* multiset.join_add
- \+ *theorem* multiset.join_cons
- \+ *theorem* multiset.join_zero
- \+ *theorem* multiset.le_inter
- \+/\- *theorem* multiset.le_union_left
- \+/\- *theorem* multiset.le_union_right
- \+ *theorem* multiset.map_add
- \+ *theorem* multiset.map_cons
- \+ *theorem* multiset.map_map
- \+ *theorem* multiset.map_zero
- \+ *theorem* multiset.mem_erase_of_ne
- \+/\- *theorem* multiset.mem_erase_of_ne_of_mem
- \+ *theorem* multiset.prod_add
- \+ *theorem* multiset.prod_cons
- \+ *theorem* multiset.prod_eq_foldl
- \- *def* multiset.prod_eq_foldl
- \+ *theorem* multiset.prod_eq_foldr
- \- *def* multiset.prod_eq_foldr
- \+ *theorem* multiset.prod_zero
- \+ *def* multiset.product
- \+ *theorem* multiset.product_add
- \- *def* multiset.sum
- \+/\- *theorem* multiset.union_comm
- \+ *theorem* multiset.zero_bind
- \+ *theorem* multiset.zero_inter
- \+ *theorem* multiset.zero_product

Modified data/quot.lean
- \- *lemma* quot_mk_image_univ_eq
- \+ *theorem* quotient.eq

Modified data/set/basic.lean
- \+ *lemma* set.quot_mk_image_univ_eq

Modified order/boolean_algebra.lean


Modified order/lattice.lean
- \+ *theorem* lattice.sup_le_sup_left
- \+ *theorem* lattice.sup_le_sup_right

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
- \+/\- *def* linear_map.im
- \+/\- *def* linear_map.ker
- \+/\- *theorem* linear_map.ker_of_map_eq_map
- \+/\- *lemma* linear_map.mem_ker
- \- *def* module.dual
- \+/\- *lemma* module.mul_app
- \+/\- *lemma* smul_smul
- \+/\- *lemma* submodule.neg
- \+/\- *lemma* submodule.sub
- \+/\- *def* subspace
- \- *def* vector_space



## [2017-11-10 05:26:42-05:00](https://github.com/leanprover-community/mathlib/commit/0f8a5c8)
refactor(algebra/group): Use a user attr for to_additive
Parts of this commit are redundant pending leanprover/lean[#1857](https://github.com/leanprover-community/mathlib/pull/1857) .
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_congr
- \+/\- *lemma* finset.prod_const_one
- \+/\- *lemma* finset.prod_empty
- \+/\- *lemma* finset.prod_image
- \+/\- *lemma* finset.prod_insert
- \+/\- *lemma* finset.prod_inv_distrib
- \+/\- *lemma* finset.prod_singleton
- \+/\- *lemma* finset.prod_to_finset_of_nodup
- \- *theorem* list.prod_append
- \- *theorem* list.prod_cons
- \- *lemma* list.prod_eq_of_perm
- \- *theorem* list.prod_join
- \- *theorem* list.prod_nil
- \- *theorem* list.prod_repeat
- \- *lemma* list.prod_reverse

Modified algebra/group.lean
- \+/\- *theorem* inv_eq_one
- \+/\- *theorem* inv_inj'
- \+/\- *theorem* inv_ne_one
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_self_iff_eq_one

Modified algebra/group_power.lean
- \+ *theorem* list.prod_repeat

Modified data/finset/fold.lean
- \- *lemma* list.fold_op_eq_of_perm
- \- *lemma* list.foldl_assoc
- \- *lemma* list.foldl_assoc_comm_cons
- \- *lemma* list.foldl_op_eq_op_foldr_assoc
- \- *lemma* list.map_congr

Modified data/list/basic.lean
- \+ *lemma* list.foldl_assoc
- \+ *lemma* list.foldl_assoc_comm_cons
- \+ *lemma* list.foldl_op_eq_op_foldr_assoc
- \+ *lemma* list.map_congr
- \+ *theorem* list.prod_append
- \+ *theorem* list.prod_cons
- \+ *theorem* list.prod_join
- \+ *theorem* list.prod_nil
- \- *def* list.sum

Modified data/list/perm.lean
- \+ *lemma* list.fold_op_eq_of_perm
- \+ *lemma* list.prod_eq_of_perm
- \+ *lemma* list.prod_reverse

Modified data/nat/basic.lean
- \+/\- *theorem* nat.size_one



## [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/04dd132)
feat(algebra/big_operators): exists_ne_(one|zero)_of_(prod|sum)_ne_(one|zero)
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.exists_ne_one_of_prod_ne_one



## [2017-11-09 12:33:00+01:00](https://github.com/leanprover-community/mathlib/commit/5923cd0)
feat(data/set/finite): finite_of_finite_image
#### Estimated changes
Modified data/set/finite.lean
- \+ *theorem* set.finite_of_finite_image

Modified logic/function.lean
- \+ *lemma* function.inv_fun_comp



## [2017-11-07 19:26:04-05:00](https://github.com/leanprover-community/mathlib/commit/d95bff0)
refactor(data/hash_map): improve hash_map proof
Decrease dependence on implementation details of `array`
#### Estimated changes
Modified data/array/lemmas.lean
- \+/\- *theorem* array.rev_list_length
- \+/\- *theorem* array.rev_list_reverse
- \+/\- *theorem* array.to_list_length
- \+ *theorem* array.to_list_nth_le'
- \+/\- *theorem* array.to_list_reverse
- \+ *theorem* array.write_to_list

Modified data/hash_map.lean
- \+/\- *def* bucket_array.as_list
- \- *theorem* bucket_array.foldl_eq_lem
- \+ *theorem* hash_map.mk_valid
- \- *theorem* hash_map.valid.as_list_length
- \- *theorem* hash_map.valid.eq'
- \- *theorem* hash_map.valid.eq
- \+/\- *theorem* hash_map.valid.find_aux_iff
- \+ *theorem* hash_map.valid.idx_enum
- \+ *theorem* hash_map.valid.idx_enum_1
- \- *theorem* hash_map.valid.mk
- \+/\- *theorem* hash_map.valid.modify
- \- *theorem* hash_map.valid.nodup
- \- *theorem* hash_map.valid.nodupd
- \- *def* hash_map.valid
- \- *theorem* hash_map.valid_aux.eq
- \- *theorem* hash_map.valid_aux.nodup
- \- *theorem* hash_map.valid_aux.unfold_cons

Modified data/list/basic.lean
- \+ *theorem* list.drop_eq_nth_le_cons
- \+ *theorem* list.join_append
- \+ *theorem* list.modify_nth_eq_take_cons_drop
- \+ *theorem* list.modify_nth_length
- \+ *theorem* list.modify_nth_tail_length
- \+/\- *theorem* list.nth_update_nth_of_lt
- \+ *theorem* list.update_nth_eq_take_cons_drop
- \+ *theorem* list.update_nth_length

Modified tactic/interactive.lean




## [2017-11-07 06:09:41-05:00](https://github.com/leanprover-community/mathlib/commit/4ae6a57)
fix(data/array): update to lean
#### Estimated changes
Modified data/array/lemmas.lean
- \+ *theorem* array.mem.def
- \- *theorem* array.mem_iff_list_mem
- \- *theorem* array.mem_iff_rev_list_mem
- \- *theorem* array.mem_iff_rev_list_mem_core
- \+ *theorem* array.mem_rev_list
- \+ *theorem* array.mem_rev_list_core
- \+ *theorem* array.mem_to_list
- \+ *theorem* array.mem_to_list_enum
- \+/\- *theorem* array.push_back_rev_list
- \+/\- *lemma* array.push_back_rev_list_core
- \+/\- *theorem* array.push_back_to_list
- \+ *theorem* array.read_foreach
- \- *def* array.read_foreach
- \+ *theorem* array.read_foreach_aux
- \- *def* array.read_foreach_aux
- \+ *theorem* array.read_map
- \- *def* array.read_map
- \+ *theorem* array.read_map₂
- \- *def* array.read_map₂
- \- *lemma* array.read_write
- \- *lemma* array.read_write_eq
- \- *lemma* array.read_write_ne
- \+ *theorem* array.rev_list_foldr
- \+ *theorem* array.rev_list_foldr_aux
- \+/\- *theorem* array.rev_list_length
- \+/\- *theorem* array.rev_list_length_aux
- \+/\- *theorem* array.rev_list_reverse
- \+/\- *theorem* array.rev_list_reverse_core
- \+ *theorem* array.to_list_foldl
- \+/\- *theorem* array.to_list_length
- \+/\- *theorem* array.to_list_nth
- \- *theorem* array.to_list_nth_core
- \+ *theorem* array.to_list_nth_le
- \+ *theorem* array.to_list_nth_le_core
- \+/\- *theorem* array.to_list_reverse
- \+/\- *theorem* array.to_list_to_array

Modified data/hash_map.lean
- \+ *theorem* hash_map.valid.nodupd

Modified data/list/basic.lean
- \+ *theorem* list.enum_from_map_fst
- \+ *theorem* list.enum_from_map_snd
- \+ *theorem* list.enum_from_nth
- \+ *theorem* list.enum_map_fst
- \+ *theorem* list.enum_map_snd
- \+ *theorem* list.enum_nth
- \+/\- *theorem* list.eq_nil_of_map_eq_nil
- \+/\- *theorem* list.ext
- \+/\- *theorem* list.foldl_append
- \+ *theorem* list.foldl_join
- \+ *theorem* list.foldr_join
- \+ *theorem* list.infix_of_mem_join
- \+ *theorem* list.length_enum
- \+ *theorem* list.length_enum_from
- \+ *theorem* list.map_join
- \+ *theorem* list.mem_iff_nth
- \+ *theorem* list.mem_iff_nth_le
- \+ *def* list.modify_head
- \+ *def* list.modify_nth
- \+ *theorem* list.modify_nth_eq_take_drop
- \+ *theorem* list.modify_nth_eq_update_nth
- \+ *def* list.modify_nth_tail
- \+ *theorem* list.modify_nth_tail_eq_take_drop
- \+ *theorem* list.nth_eq_some
- \+/\- *theorem* list.nth_ge_len
- \+ *theorem* list.nth_le_mem
- \+/\- *theorem* list.nth_le_nth
- \+ *theorem* list.nth_le_of_mem
- \+/\- *theorem* list.nth_le_reverse_aux1
- \+/\- *theorem* list.nth_le_reverse_aux2
- \+ *theorem* list.nth_mem
- \+ *theorem* list.nth_modify_nth
- \+ *theorem* list.nth_modify_nth_eq
- \+ *theorem* list.nth_modify_nth_ne
- \+ *theorem* list.nth_of_mem
- \+ *theorem* list.nth_update_nth_eq
- \+ *theorem* list.nth_update_nth_ne
- \+ *theorem* list.nth_update_nth_of_lt
- \+ *theorem* list.pairwise.and_mem
- \- *theorem* list.pairwise.iff_mem
- \+ *theorem* list.pairwise.iff_of_mem
- \+ *theorem* list.pairwise.imp_mem
- \+ *theorem* list.pairwise.imp_of_mem
- \+ *theorem* list.remove_nth_eq_nth_tail
- \+/\- *def* list.to_array
- \+ *theorem* list.update_nth_eq_modify_nth



## [2017-11-06 11:35:36+01:00](https://github.com/leanprover-community/mathlib/commit/2bc7fd4)
feat(data/cardinal): theory for cardinal arithmetic
#### Estimated changes
Added data/cardinal.lean
- \+ *lemma* cardinal.add_mono
- \+ *lemma* cardinal.mul_mono
- \+ *lemma* cardinal.mul_power
- \+ *lemma* cardinal.one_power
- \+ *lemma* cardinal.power_mono_left
- \+ *lemma* cardinal.power_mono_right
- \+ *lemma* cardinal.power_mul
- \+ *lemma* cardinal.power_sum
- \+ *lemma* cardinal.power_zero
- \+ *lemma* cardinal.zero_power
- \+ *def* cardinal.ω
- \+ *def* cardinal
- \+ *lemma* embedding.antisymm
- \+ *def* embedding.arrow_congr_left
- \+ *def* embedding.arrow_congr_right
- \+ *lemma* embedding.exists_injective_or_surjective
- \+ *def* embedding.option.Sup
- \+ *lemma* embedding.option.Sup_le
- \+ *lemma* embedding.option.eq_of_le_some
- \+ *lemma* embedding.option.le_Sup
- \+ *lemma* embedding.option.mem_of_Sup_eq_some
- \+ *def* embedding.option.strict_partial_order
- \+ *def* embedding.pfun.partial_order
- \+ *def* embedding.pfun
- \+ *def* embedding.prod_congr
- \+ *lemma* embedding.schroeder_bernstein
- \+ *def* embedding.sum_congr
- \+ *lemma* embedding.total
- \+ *lemma* equiv.of_bijective

Modified data/equiv.lean
- \+ *lemma* equiv.arrow_empty_unit
- \+ *lemma* equiv.empty_of_not_nonempty

Modified data/set/lattice.lean
- \+ *lemma* image_congr



## [2017-11-06 03:28:38-05:00](https://github.com/leanprover-community/mathlib/commit/d62cefd)
refactor(algebra/module): clean up PR commit
#### Estimated changes
Modified algebra/module.lean
- \- *lemma* eq_zero_of_add_self_eq
- \+/\- *lemma* linear_map.add_app
- \+/\- *theorem* linear_map.ext
- \- *theorem* linear_map.im.add_im
- \- *lemma* linear_map.im.mem_im
- \- *theorem* linear_map.im.neg_im
- \- *theorem* linear_map.im.smul_im
- \- *theorem* linear_map.im.zero_im
- \+/\- *def* linear_map.im
- \+ *theorem* linear_map.inj_of_trivial_ker
- \- *theorem* linear_map.ker.inj_of_trivial_ker
- \- *theorem* linear_map.ker.ker_of_map_eq_map
- \- *lemma* linear_map.ker.mem_ker
- \- *theorem* linear_map.ker.sub_ker
- \+/\- *def* linear_map.ker
- \+ *theorem* linear_map.ker_of_map_eq_map
- \+/\- *lemma* linear_map.map_add_app
- \+/\- *lemma* linear_map.map_neg
- \+/\- *lemma* linear_map.map_smul_app
- \+/\- *lemma* linear_map.map_sub
- \+ *lemma* linear_map.mem_im
- \+ *lemma* linear_map.mem_ker
- \+/\- *lemma* linear_map.neg_app
- \+/\- *lemma* linear_map.smul_app
- \+ *theorem* linear_map.sub_ker
- \+/\- *lemma* linear_map.zero_app
- \- *theorem* module.add_comp
- \- *theorem* module.comp_add
- \- *lemma* module.comp_app
- \- *theorem* module.comp_assoc
- \- *lemma* module.comp_id
- \+/\- *def* module.dual
- \+/\- *def* module.endomorphism_ring
- \+/\- *def* module.general_linear_group
- \- *def* module.id
- \- *lemma* module.id_app
- \- *lemma* module.id_comp
- \+ *lemma* module.mul_app
- \+ *lemma* module.one_app
- \+/\- *theorem* mul_smul
- \+ *theorem* neg_one_smul
- \+/\- *theorem* neg_smul
- \+/\- *theorem* one_smul
- \+/\- *theorem* smul_left_distrib
- \+/\- *theorem* smul_neg
- \+/\- *theorem* smul_right_distrib
- \+/\- *lemma* smul_smul
- \+/\- *theorem* smul_sub_left_distrib
- \+/\- *theorem* smul_zero
- \+/\- *theorem* sub_smul_right_distrib
- \+/\- *lemma* submodule.add_val
- \+ *lemma* submodule.neg
- \+/\- *lemma* submodule.neg_val
- \+/\- *lemma* submodule.smul_val
- \+/\- *lemma* submodule.sub
- \+/\- *lemma* submodule.zero_val
- \+ *def* subspace
- \+ *def* vector_space
- \+/\- *theorem* zero_smul

Modified algebra/ring.lean
- \+ *theorem* units.ext
- \- *def* units.ext
- \+ *lemma* units.inv_coe
- \+/\- *lemma* units.inv_mul
- \- *lemma* units.inv_val'
- \+ *lemma* units.mul_coe
- \- *lemma* units.mul_four
- \+ *lemma* units.mul_inv
- \- *lemma* units.mul_val
- \+ *lemma* units.one_coe
- \- *lemma* units.one_val
- \+ *lemma* units.val_coe

Deleted algebra/vector_space.lean
- \- *def* vector_space.dual
- \- *def* vector_space.general_linear_group



## [2017-11-06 01:31:01-05:00](https://github.com/leanprover-community/mathlib/commit/5cb7fb0)
feat(algebra/vector_space): modules and vector spaces, linear spaces
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* eq_zero_of_add_self_eq
- \+ *lemma* linear_map.add_app
- \+ *theorem* linear_map.ext
- \+ *theorem* linear_map.im.add_im
- \+ *lemma* linear_map.im.mem_im
- \+ *theorem* linear_map.im.neg_im
- \+ *theorem* linear_map.im.smul_im
- \+ *theorem* linear_map.im.zero_im
- \+ *def* linear_map.im
- \+ *theorem* linear_map.ker.inj_of_trivial_ker
- \+ *theorem* linear_map.ker.ker_of_map_eq_map
- \+ *lemma* linear_map.ker.mem_ker
- \+ *theorem* linear_map.ker.sub_ker
- \+ *def* linear_map.ker
- \+ *lemma* linear_map.map_add_app
- \+ *lemma* linear_map.map_neg
- \+ *lemma* linear_map.map_smul_app
- \+ *lemma* linear_map.map_sub
- \+ *lemma* linear_map.map_zero
- \+ *lemma* linear_map.neg_app
- \+ *lemma* linear_map.smul_app
- \+ *lemma* linear_map.zero_app
- \+ *theorem* module.add_comp
- \+ *theorem* module.comp_add
- \+ *lemma* module.comp_app
- \+ *theorem* module.comp_assoc
- \+ *lemma* module.comp_id
- \+ *def* module.dual
- \+ *def* module.endomorphism_ring
- \+ *def* module.general_linear_group
- \+ *def* module.id
- \+ *lemma* module.id_app
- \+ *lemma* module.id_comp
- \- *def* ring.to_module
- \+ *lemma* smul_smul
- \+ *lemma* submodule.add_val
- \+ *lemma* submodule.neg_val
- \+ *lemma* submodule.smul_val
- \+ *lemma* submodule.sub
- \+ *lemma* submodule.zero_val

Modified algebra/ring.lean
- \+ *def* units.ext
- \+ *lemma* units.inv_mul
- \+ *lemma* units.inv_val'
- \+ *lemma* units.mul_four
- \+ *lemma* units.mul_val
- \+ *lemma* units.one_val

Added algebra/vector_space.lean
- \+ *def* vector_space.dual
- \+ *def* vector_space.general_linear_group



## [2017-11-06 01:26:58-05:00](https://github.com/leanprover-community/mathlib/commit/0947f96)
feat(data/multiset): working on multiset.union
#### Estimated changes
Modified algebra/group.lean


Modified data/int/basic.lean
- \+ *theorem* int.mul_sign

Modified data/list/basic.lean
- \+ *theorem* list.erase_sublist_erase
- \+ *theorem* list.sublist_or_mem_of_sublist

Modified data/multiset/basic.lean
- \+/\- *theorem* multiset.add_cons
- \+ *theorem* multiset.add_sub_cancel
- \+ *theorem* multiset.add_sub_cancel_left
- \+/\- *theorem* multiset.add_sub_of_le
- \+ *theorem* multiset.cons_add
- \+/\- *theorem* multiset.eq_cons_erase
- \+ *theorem* multiset.eq_union_left
- \+ *theorem* multiset.eq_union_right
- \+ *theorem* multiset.erase_le_erase
- \+ *theorem* multiset.erase_le_iff_le_cons
- \+ *theorem* multiset.insert_eq_cons
- \+ *theorem* multiset.le_cons_erase
- \+ *theorem* multiset.le_cons_of_not_mem
- \+ *theorem* multiset.le_sub_add
- \+ *theorem* multiset.le_union_left
- \+ *theorem* multiset.le_union_right
- \+/\- *theorem* multiset.mem_singleton
- \+/\- *theorem* multiset.mem_singleton_self
- \+ *def* multiset.ndinsert
- \+ *def* multiset.nodup
- \+/\- *theorem* multiset.singleton_inj
- \+/\- *theorem* multiset.singleton_ne_zero
- \+/\- *theorem* multiset.sub_add_cancel
- \+ *theorem* multiset.sub_le_iff_le_add
- \+ *theorem* multiset.sub_le_sub_left
- \+ *theorem* multiset.sub_le_sub_right
- \+ *def* multiset.union
- \+ *theorem* multiset.union_comm
- \+ *theorem* multiset.union_le
- \+ *theorem* multiset.union_le_union_left
- \+ *theorem* multiset.union_le_union_right



## [2017-11-05 17:42:46-05:00](https://github.com/leanprover-community/mathlib/commit/2aa6c87)
feat(tactic/norm_num): add support for inv and locations in norm_num
#### Estimated changes
Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2017-11-05 01:30:21-04:00](https://github.com/leanprover-community/mathlib/commit/d743fdf)
feat(data/sigma): duplicate sigma basics for psigma
#### Estimated changes
Modified data/sigma/basic.lean
- \+ *def* psigma.map
- \+ *lemma* psigma.mk_eq_mk_iff
- \+/\- *def* sigma.map
- \+/\- *lemma* sigma.mk_eq_mk_iff



## [2017-11-05 00:29:59-05:00](https://github.com/leanprover-community/mathlib/commit/8e99f98)
fix(algebra/field): update to lean
#### Estimated changes
Modified algebra/field.lean
- \- *lemma* division_ring.inv_inv
- \- *lemma* division_ring.one_div_div
- \- *lemma* inv_ne_zero

Modified algebra/ring.lean
- \+ *lemma* mul_neg_one
- \- *theorem* mul_neg_one_eq_neg
- \+ *lemma* neg_one_mul



## [2017-11-02 17:13:43-04:00](https://github.com/leanprover-community/mathlib/commit/2da9bef)
feat(data/nat/cast,...): add char_zero typeclass for cast_inj
As pointed out by @kbuzzard, the complex numbers are an important example of an unordered characteristic zero field for which we will want cast_inj to be available.
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* int.cast_eq_zero
- \+/\- *theorem* int.cast_inj
- \+/\- *theorem* int.cast_ne_zero

Modified data/nat/cast.lean
- \+ *theorem* add_group.char_zero_of_inj_zero
- \+ *theorem* char_zero_of_inj_zero
- \+/\- *theorem* nat.cast_eq_zero
- \+/\- *theorem* nat.cast_inj
- \+/\- *theorem* nat.cast_ne_zero
- \+ *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero

Modified data/rat.lean
- \+/\- *theorem* rat.cast_add
- \+/\- *theorem* rat.cast_bit0
- \+/\- *theorem* rat.cast_bit1
- \+/\- *theorem* rat.cast_div
- \+/\- *theorem* rat.cast_eq_zero
- \+/\- *theorem* rat.cast_inj
- \+/\- *theorem* rat.cast_inv
- \+/\- *theorem* rat.cast_mk
- \+/\- *theorem* rat.cast_mul
- \+/\- *theorem* rat.cast_ne_zero
- \+/\- *theorem* rat.cast_sub



## [2017-11-02 02:32:37-04:00](https://github.com/leanprover-community/mathlib/commit/2883c1b)
feat(data/num/lemmas): finish znum isomorphism proof
#### Estimated changes
Modified data/num/lemmas.lean
- \+ *theorem* num.cast_add
- \+/\- *theorem* num.cast_inj
- \+/\- *theorem* num.cast_le
- \+/\- *theorem* num.cast_lt
- \+/\- *theorem* num.cast_mul
- \+/\- *theorem* pos_num.cast_inj
- \+/\- *theorem* pos_num.cast_le
- \+/\- *theorem* pos_num.cast_lt
- \+/\- *theorem* pos_num.cast_mul
- \- *theorem* znum.add_of_nat
- \+/\- *theorem* znum.cast_add
- \+ *theorem* znum.cast_inj
- \+ *theorem* znum.cast_le
- \+ *theorem* znum.cast_lt
- \+ *theorem* znum.cast_mul
- \+ *theorem* znum.cast_succ
- \+ *theorem* znum.cmp_to_int
- \+ *theorem* znum.le_to_int
- \+ *theorem* znum.lt_to_int
- \+ *theorem* znum.mul_to_int
- \+ *theorem* znum.to_int_inj
- \+ *theorem* znum.to_of_int



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
- \- *lemma* norm_num.bit0_le_one
- \- *lemma* norm_num.bit0_le_zero
- \+ *theorem* norm_num.bit0_zero
- \- *lemma* norm_num.bit1_le_bit0
- \- *lemma* norm_num.bit1_le_one
- \- *lemma* norm_num.bit1_le_zero
- \+ *theorem* norm_num.bit1_zero
- \+ *lemma* norm_num.lt_add_of_pos_helper
- \- *lemma* norm_num.one_le_bit0
- \- *lemma* norm_num.one_le_bit1
- \- *lemma* norm_num.one_le_one
- \- *lemma* norm_num.pow_bit0
- \+/\- *lemma* norm_num.pow_bit0_helper
- \- *lemma* norm_num.pow_bit1
- \+/\- *lemma* norm_num.pow_bit1_helper
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

Modified tests/norm_num.lean




## [2017-11-01 04:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/0663945)
feat(data/num,data/multiset): more properties of binary numbers, begin multisets
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* division_ring.inv_div
- \+ *lemma* division_ring.inv_inv
- \+ *lemma* division_ring.one_div_div
- \+ *lemma* inv_ne_zero

Modified algebra/group_power.lean
- \+ *theorem* has_pow_nat_eq_pow_nat
- \+ *theorem* pow_bit0
- \+ *theorem* pow_bit1

Modified algebra/ordered_group.lean
- \+ *lemma* bit0_pos

Modified algebra/ordered_ring.lean
- \+ *lemma* bit1_pos'
- \+ *lemma* bit1_pos

Modified data/int/basic.lean
- \+ *theorem* int.cast_coe_nat'

Added data/multiset/basic.lean
- \+ *theorem* multiset.add_cons
- \+ *theorem* multiset.add_sub_of_le
- \+ *def* multiset.card
- \+ *theorem* multiset.card_add
- \+ *theorem* multiset.card_cons
- \+ *theorem* multiset.card_empty
- \+ *theorem* multiset.card_erase_of_mem
- \+ *theorem* multiset.card_insert_le
- \+ *theorem* multiset.card_insert_of_not_mem
- \+ *theorem* multiset.card_le_of_le
- \+ *theorem* multiset.card_lt_of_lt
- \+ *theorem* multiset.card_range
- \+ *theorem* multiset.card_zero
- \+ *theorem* multiset.coe_add
- \+ *theorem* multiset.coe_card
- \+ *theorem* multiset.coe_eq_coe
- \+ *theorem* multiset.coe_erase
- \+ *theorem* multiset.coe_foldl
- \+ *theorem* multiset.coe_foldr
- \+ *theorem* multiset.coe_foldr_swap
- \+ *theorem* multiset.coe_join
- \+ *theorem* multiset.coe_le
- \+ *theorem* multiset.coe_nil_eq_zero
- \+ *theorem* multiset.coe_reverse
- \+ *theorem* multiset.coe_sub
- \+ *def* multiset.cons
- \+ *theorem* multiset.cons_coe
- \+ *theorem* multiset.cons_inj_left
- \+ *theorem* multiset.cons_inj_right
- \+ *theorem* multiset.cons_le_cons
- \+ *theorem* multiset.cons_le_cons_iff
- \+ *theorem* multiset.cons_swap
- \+ *theorem* multiset.empty_inter
- \+ *theorem* multiset.empty_subset
- \+ *theorem* multiset.eq_cons_erase
- \+ *theorem* multiset.eq_empty_of_card_eq_zero
- \+ *theorem* multiset.eq_empty_of_forall_not_mem
- \+ *theorem* multiset.eq_empty_of_subset_empty
- \+ *theorem* multiset.eq_of_le_of_card_le
- \+ *theorem* multiset.eq_zero_of_le_zero
- \+ *def* multiset.erase
- \+ *theorem* multiset.erase_add_left_neg
- \+ *theorem* multiset.erase_add_left_pos
- \+ *theorem* multiset.erase_add_right_neg
- \+ *theorem* multiset.erase_add_right_pos
- \+ *theorem* multiset.erase_comm
- \+ *theorem* multiset.erase_cons_head
- \+ *theorem* multiset.erase_cons_tail
- \+ *lemma* multiset.erase_dup_map_erase_dup_eq
- \+ *theorem* multiset.erase_empty
- \+ *theorem* multiset.erase_eq_of_not_mem
- \+ *theorem* multiset.erase_insert
- \+ *theorem* multiset.erase_insert_subset
- \+ *theorem* multiset.erase_le
- \+ *theorem* multiset.erase_of_not_mem
- \+ *theorem* multiset.erase_subset
- \+ *theorem* multiset.erase_subset_erase
- \+ *theorem* multiset.erase_subset_of_subset_insert
- \+ *theorem* multiset.erase_zero
- \+ *theorem* multiset.exists_cons_of_mem
- \+ *theorem* multiset.exists_mem_empty_iff
- \+ *theorem* multiset.exists_mem_insert
- \+ *theorem* multiset.exists_mem_of_ne_empty
- \+ *theorem* multiset.exists_nat_subset_range
- \+ *theorem* multiset.filter_false
- \+ *theorem* multiset.filter_filter
- \+ *theorem* multiset.filter_inter_filter_neg_eq
- \+ *theorem* multiset.filter_subset
- \+ *theorem* multiset.filter_union
- \+ *theorem* multiset.filter_union_filter_neg_eq
- \+ *def* multiset.foldl
- \+ *theorem* multiset.foldl_swap
- \+ *def* multiset.foldr
- \+ *theorem* multiset.foldr_swap
- \+ *theorem* multiset.forall_mem_empty_iff
- \+ *theorem* multiset.forall_mem_insert
- \+ *lemma* multiset.image_empty
- \+ *lemma* multiset.image_eq_empty_iff
- \+ *lemma* multiset.image_filter
- \+ *lemma* multiset.image_id
- \+ *lemma* multiset.image_image
- \+ *lemma* multiset.image_insert
- \+ *lemma* multiset.image_inter
- \+ *lemma* multiset.image_singleton
- \+ *lemma* multiset.image_subset_image
- \+ *lemma* multiset.image_to_multiset
- \+ *lemma* multiset.image_to_multiset_of_nodup
- \+ *lemma* multiset.image_union
- \+ *theorem* multiset.insert_erase
- \+ *theorem* multiset.insert_erase_subset
- \+ *theorem* multiset.insert_inter_of_mem
- \+ *theorem* multiset.insert_inter_of_not_mem
- \+ *theorem* multiset.inter_assoc
- \+ *theorem* multiset.inter_comm
- \+ *theorem* multiset.inter_distrib_left
- \+ *theorem* multiset.inter_distrib_right
- \+ *theorem* multiset.inter_empty
- \+ *theorem* multiset.inter_insert_of_mem
- \+ *theorem* multiset.inter_insert_of_not_mem
- \+ *theorem* multiset.inter_left_comm
- \+ *theorem* multiset.inter_right_comm
- \+ *theorem* multiset.inter_self
- \+ *theorem* multiset.inter_singleton_of_mem
- \+ *theorem* multiset.inter_singleton_of_not_mem
- \+ *theorem* multiset.inter_subset_left
- \+ *theorem* multiset.inter_subset_right
- \+ *def* multiset.join
- \+ *theorem* multiset.le_add_left
- \+ *theorem* multiset.le_add_right
- \+ *theorem* multiset.le_cons_self
- \+ *theorem* multiset.le_iff_exists_add
- \+ *theorem* multiset.le_induction_on
- \+ *theorem* multiset.lt_cons_self
- \+ *theorem* multiset.lt_iff_cons_le
- \+ *def* multiset.map
- \+ *def* multiset.mem
- \+ *lemma* multiset.mem_coe
- \+ *theorem* multiset.mem_cons
- \+ *theorem* multiset.mem_cons_self
- \+ *theorem* multiset.mem_erase
- \+ *theorem* multiset.mem_erase_of_ne_of_mem
- \+ *theorem* multiset.mem_filter
- \+ *lemma* multiset.mem_image_iff
- \+ *theorem* multiset.mem_inter
- \+ *theorem* multiset.mem_inter_of_mem
- \+ *theorem* multiset.mem_map
- \+ *theorem* multiset.mem_map_of_inj
- \+ *theorem* multiset.mem_map_of_mem
- \+ *theorem* multiset.mem_of_le
- \+ *theorem* multiset.mem_of_mem_erase
- \+ *theorem* multiset.mem_of_mem_inter_left
- \+ *theorem* multiset.mem_of_mem_inter_right
- \+ *theorem* multiset.mem_of_subset
- \+ *theorem* multiset.mem_range
- \+ *theorem* multiset.mem_sdiff_iff
- \+ *theorem* multiset.mem_singleton
- \+ *theorem* multiset.mem_singleton_self
- \+ *lemma* multiset.ne_empty_of_card_eq_succ
- \+ *theorem* multiset.ne_of_mem_erase
- \+ *theorem* multiset.not_mem_empty
- \+ *theorem* multiset.not_mem_erase
- \+ *theorem* multiset.not_mem_range_self
- \+ *def* multiset.prod
- \+ *def* multiset.prod_eq_foldl
- \+ *def* multiset.prod_eq_foldr
- \+ *theorem* multiset.quot_mk_to_coe'
- \+ *theorem* multiset.quot_mk_to_coe
- \+ *def* multiset.range
- \+ *theorem* multiset.range_subset
- \+ *theorem* multiset.range_succ
- \+ *theorem* multiset.range_zero
- \+ *lemma* multiset.sdiff_inter_self
- \+ *lemma* multiset.sdiff_subset_sdiff
- \+ *lemma* multiset.sdiff_union_of_subset
- \+ *theorem* multiset.singleton_add
- \+ *theorem* multiset.singleton_coe
- \+ *theorem* multiset.singleton_inj
- \+ *theorem* multiset.singleton_inter_of_mem
- \+ *theorem* multiset.singleton_inter_of_not_mem
- \+ *theorem* multiset.singleton_ne_zero
- \+ *theorem* multiset.sub_add_cancel
- \+ *theorem* multiset.sub_cons
- \+ *theorem* multiset.sub_eq_fold_erase
- \+ *theorem* multiset.sub_zero
- \+ *theorem* multiset.subset.refl
- \+ *theorem* multiset.subset.trans
- \+ *theorem* multiset.subset_empty_iff
- \+ *theorem* multiset.subset_iff
- \+ *theorem* multiset.subset_insert_iff
- \+ *theorem* multiset.subset_insert_of_erase_subset
- \+ *theorem* multiset.subset_inter
- \+ *theorem* multiset.subset_of_le
- \+ *def* multiset.sum
- \+ *theorem* multiset.union_distrib_left
- \+ *theorem* multiset.union_distrib_right
- \+ *theorem* multiset.zero_le
- \+ *def* {u}

Modified data/nat/basic.lean
- \+ *def* nat.ppred
- \+ *theorem* nat.ppred_eq_none
- \+ *theorem* nat.ppred_eq_pred
- \+ *theorem* nat.ppred_eq_some
- \+ *theorem* nat.pred_eq_ppred
- \+ *def* nat.psub
- \+ *theorem* nat.psub_add
- \+ *theorem* nat.psub_eq_none
- \+ *theorem* nat.psub_eq_some
- \+ *theorem* nat.psub_eq_sub
- \+ *theorem* nat.size_one
- \+ *theorem* nat.sub_eq_psub

Modified data/nat/cast.lean
- \+/\- *theorem* nat.cast_bit0
- \+/\- *theorem* nat.cast_bit1

Modified data/num/basic.lean
- \- *def* num.of_nat
- \+ *def* num.of_znum'
- \+ *def* num.of_znum
- \+ *def* num.ppred
- \+ *def* num.psub
- \+ *def* num.sub'
- \+ *def* num.to_znum_neg
- \+ *def* pos_num.of_znum'
- \+ *def* pos_num.of_znum
- \+/\- *def* pos_num.pred'
- \+/\- *def* pos_num.pred
- \- *def* pos_num.psub
- \+ *def* pos_num.sub'

Modified data/num/lemmas.lean
- \+/\- *theorem* num.add_of_nat
- \+ *theorem* num.add_one
- \+ *theorem* num.add_to_nat
- \+ *theorem* num.add_to_znum
- \+ *theorem* num.bit0_of_bit0
- \+ *theorem* num.bit1_of_bit1
- \- *theorem* num.cast_add
- \- *theorem* num.cast_cmp'
- \- *theorem* num.cast_cmp
- \+/\- *theorem* num.cast_one
- \+ *theorem* num.cast_sub'
- \+/\- *theorem* num.cast_succ'
- \+ *theorem* num.cast_to_int
- \+ *theorem* num.cast_to_nat
- \+ *theorem* num.cast_to_znum
- \+ *theorem* num.cast_to_znum_neg
- \+/\- *theorem* num.cast_zero
- \+ *theorem* num.cmp_to_nat
- \+ *theorem* num.le_to_nat
- \+ *theorem* num.lt_to_nat
- \+ *theorem* num.mul_to_nat
- \+/\- *theorem* num.of_nat_inj
- \+ *theorem* num.of_nat_to_znum
- \+ *theorem* num.of_nat_to_znum_neg
- \+ *theorem* num.ppred_to_nat
- \+ *theorem* num.succ'_to_nat
- \+ *theorem* num.succ_to_nat
- \+/\- *theorem* num.to_nat_inj
- \+ *theorem* num.zneg_to_znum
- \+ *theorem* num.zneg_to_znum_neg
- \+ *theorem* pos_num.add_to_nat
- \+/\- *theorem* pos_num.cast_add
- \- *theorem* pos_num.cast_add_comm
- \- *theorem* pos_num.cast_add_comm_lemma_1
- \- *theorem* pos_num.cast_add_comm_lemma_2
- \- *theorem* pos_num.cast_add_one_comm
- \+ *theorem* pos_num.cast_bit0
- \+ *theorem* pos_num.cast_bit1
- \- *theorem* pos_num.cast_cmp'
- \- *theorem* pos_num.cast_cmp
- \+/\- *theorem* pos_num.cast_mul
- \+/\- *theorem* pos_num.cast_one
- \+ *theorem* pos_num.cast_sub'
- \+/\- *theorem* pos_num.cast_succ
- \+ *theorem* pos_num.cast_to_int
- \+ *theorem* pos_num.cast_to_nat
- \+ *theorem* pos_num.cast_to_num
- \+ *theorem* pos_num.cast_to_znum
- \+ *theorem* pos_num.cmp_to_nat
- \+ *theorem* pos_num.cmp_to_nat_lemma
- \+ *theorem* pos_num.le_to_nat
- \+ *theorem* pos_num.lt_to_nat
- \+ *theorem* pos_num.mul_to_nat
- \+/\- *theorem* pos_num.of_to_nat
- \- *theorem* pos_num.one_add
- \+/\- *theorem* pos_num.one_le_cast
- \+ *theorem* pos_num.one_sub'
- \+ *theorem* pos_num.pred'_succ'
- \+/\- *theorem* pos_num.pred'_to_nat
- \+ *theorem* pos_num.size_to_nat
- \+ *theorem* pos_num.sub'_one
- \+ *theorem* pos_num.succ'_pred'
- \+ *theorem* pos_num.succ_to_nat
- \+/\- *theorem* pos_num.to_nat_inj
- \+ *theorem* pos_num.to_nat_pos
- \+ *theorem* znum.add_of_nat
- \+ *theorem* znum.add_one
- \+ *theorem* znum.add_zero
- \+ *theorem* znum.bit0_of_bit0
- \+ *theorem* znum.bit1_of_bit1
- \+ *theorem* znum.cast_add
- \+ *theorem* znum.cast_bit0
- \+ *theorem* znum.cast_bit1
- \+ *theorem* znum.cast_bitm1
- \+ *theorem* znum.cast_neg
- \+/\- *theorem* znum.cast_one
- \+ *theorem* znum.cast_pos
- \+ *theorem* znum.cast_to_int
- \+/\- *theorem* znum.cast_zero
- \+ *theorem* znum.cast_zneg
- \+ *theorem* znum.neg_of_int
- \+ *theorem* znum.neg_zero
- \+ *theorem* znum.of_to_int
- \+ *theorem* znum.zero_add
- \+ *theorem* znum.zneg_bit1
- \+ *theorem* znum.zneg_bitm1
- \+ *theorem* znum.zneg_neg
- \+ *theorem* znum.zneg_pos
- \+ *theorem* znum.zneg_pred
- \+ *theorem* znum.zneg_succ
- \+ *theorem* znum.zneg_zneg

Modified data/option.lean
- \- *lemma* option.bind_none
- \+/\- *lemma* option.bind_some
- \+ *lemma* option.none_bind
- \+ *lemma* option.some_bind

Modified data/rat.lean
- \+ *theorem* rat.cast_div
- \+ *theorem* rat.cast_div_of_ne_zero
- \+ *theorem* rat.cast_inv
- \+ *theorem* rat.cast_inv_of_ne_zero

Modified data/seq/seq.lean


