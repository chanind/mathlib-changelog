## [2018-09-29 09:32:55-04:00](https://github.com/leanprover-community/mathlib/commit/b5d8fbe)
fix(data/nat/prime): fix build, add simp attr
#### Estimated changes
Modified data/nat/basic.lean


Modified data/nat/prime.lean




## [2018-09-29 07:48:43-04:00](https://github.com/leanprover-community/mathlib/commit/6997caf)
feat(data/nat/basic): remove superfluous assumptions
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* nat.lt_pred_iff
- \- *lemma* nat.lt_pred_of_succ_lt
- \+ *lemma* nat.pred_le_iff
- \+/\- *theorem* nat.sub_le_left_iff_le_add
- \+/\- *theorem* nat.sub_le_right_iff_le_add



## [2018-09-24 21:31:25+02:00](https://github.com/leanprover-community/mathlib/commit/6434658)
feat(analysis/topology): locally compact spaces and the compact-open topology
#### Estimated changes
Added analysis/topology/compact_open.lean
- \+ *def* coev
- \+ *def* compact_open
- \+ *def* compact_open_gen
- \+ *lemma* continuous_coev
- \+ *lemma* continuous_ev
- \+ *lemma* continuous_induced
- \+ *def* continuous_map.induced
- \+ *def* ev
- \+ *lemma* image_coev
- \+ *lemma* locally_compact_of_compact
- \+ *lemma* locally_compact_of_compact_nhds

Modified analysis/topology/topological_space.lean
- \+ *lemma* compact_diff
- \+ *lemma* compact_inter



## [2018-09-24 15:33:35+02:00](https://github.com/leanprover-community/mathlib/commit/68acd76)
feat(group_theory/perm): perm.fintype and card_perm (closed [#366](https://github.com/leanprover-community/mathlib/pull/366))
#### Estimated changes
Modified data/fintype.lean
- \+ *lemma* card_perms_of_finset
- \+ *lemma* fintype.card_equiv
- \+ *lemma* fintype.card_perm
- \+ *def* fintype_perm
- \+ *lemma* length_perms_of_list
- \+ *lemma* mem_of_mem_perms_of_list
- \+ *lemma* mem_perms_of_finset_iff
- \+ *lemma* mem_perms_of_list_iff
- \+ *lemma* mem_perms_of_list_of_mem
- \+ *lemma* nodup_perms_of_list
- \+ *def* perms_of_finset
- \+ *def* perms_of_list

Modified group_theory/perm.lean




## [2018-09-24 08:48:09+02:00](https://github.com/leanprover-community/mathlib/commit/cbfe372)
fix(category_theory/functor): make obj_eq_coe a rfl-lemma
This is needed to, for example, let `dsimp` turn `𝟙 (F.obj X)` into `𝟙 (F X)`.
#### Estimated changes
Modified category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.obj_eq_coe



## [2018-09-23 19:54:43-04:00](https://github.com/leanprover-community/mathlib/commit/ce43eae)
fix(topological_structures): fix imports
#### Estimated changes
Modified analysis/topology/topological_structures.lean




## [2018-09-23 18:55:03-04:00](https://github.com/leanprover-community/mathlib/commit/8c76cac)
fix(*): tweaks to 7944cc
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified linear_algebra/submodule.lean
- \+ *def* quotient_module.le_order_embedding
- \+ *def* quotient_module.lt_order_embedding
- \- *def* submodule.submodule_lt_equiv

Modified order/basic.lean


Modified order/order_iso.lean
- \+ *def* order_embedding.lt_embedding_of_le_embedding



## [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/e7c7552)
feat(analysis/topology/continuity): compactness and embeddings
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* compact_iff_compact_image_of_embedding
- \+ *lemma* compact_iff_compact_in_subtype
- \+ *lemma* compact_iff_compact_univ
- \+ *lemma* embedding.continuous
- \+ *lemma* quotient_map.continuous



## [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/ab20b5f)
style(analysis/topology/continuity): minor reorganizations
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* closure_subtype
- \+/\- *lemma* embedding.tendsto_nhds_iff



## [2018-09-21 17:57:07+02:00](https://github.com/leanprover-community/mathlib/commit/ca7f118)
fix(docs/tactics.md): missing backquote, formatting
I think I never previewed when I updated the `linarith` doc before, sorry.
#### Estimated changes
Modified docs/tactics.md




## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/9a7a611)
feat(analysis/topology, order/filter): theorems for the applicative structure on filter; add list topology
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_list
- \+/\- *lemma* quotient_dense_of_dense
- \+ *lemma* topological_space.nhds_mk_of_nhds

Modified order/filter.lean
- \+ *lemma* filter.comap_Sup
- \+ *lemma* filter.comap_supr
- \+ *lemma* filter.le_map
- \+ *lemma* filter.le_seq
- \+ *lemma* filter.map_pure
- \+ *lemma* filter.mem_map_sets_iff
- \+ *lemma* filter.mem_seq_sets_def
- \+ *lemma* filter.mem_seq_sets_iff
- \+ *lemma* filter.mem_traverse_sets
- \+ *lemma* filter.mem_traverse_sets_iff
- \+ *lemma* filter.prod_map_seq_comm
- \+ *lemma* filter.pure_seq_eq_map
- \+ *lemma* filter.seq_assoc
- \+ *lemma* filter.seq_mem_seq_sets
- \+/\- *lemma* filter.seq_mono
- \+ *lemma* filter.seq_pure
- \+ *lemma* filter.sequence_mono
- \+ *lemma* filter.singleton_mem_pure_sets
- \+ *lemma* filter.{l}



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/568a15f)
refactor(category/traversable): proofs about list instance for traverse, simplify multiset.traverse
#### Estimated changes
Modified category/traversable/instances.lean
- \+ *lemma* list.mem_traverse
- \+ *lemma* list.traverse_append
- \+ *lemma* list.traverse_cons
- \+ *lemma* list.traverse_nil
- \- *lemma* traverse_append

Modified data/list/basic.lean
- \+ *lemma* list.forall₂.flip
- \+ *lemma* list.forall₂.mp
- \+ *lemma* list.forall₂_and_left
- \- *lemma* list.forall₂_flip

Modified data/list/perm.lean


Modified data/multiset.lean
- \- *lemma* multiset.coe_append_eq_add_coe
- \- *lemma* multiset.coe_list_cons_eq_cons_coe
- \- *lemma* multiset.coe_traverse_cons
- \- *lemma* multiset.coe_traverse_cons_swap
- \+/\- *def* multiset.traverse



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/618aac9)
feat(data/set): add set.seq (use it for the appliative.seq instance for set)
#### Estimated changes
Modified data/set/lattice.lean
- \+ *lemma* set.image_seq
- \+/\- *lemma* set.mem_seq_iff
- \+ *lemma* set.prod_eq_seq
- \+ *lemma* set.prod_image_seq_comm
- \+ *lemma* set.pure_def
- \+ *def* set.seq
- \+ *lemma* set.seq_def
- \+ *lemma* set.seq_eq_set_seq
- \+ *lemma* set.seq_mono
- \+ *lemma* set.seq_seq
- \+ *lemma* set.seq_singleton
- \+ *lemma* set.seq_subset
- \+ *lemma* set.singleton_seq



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/a62ec36)
refactor(order/filter): remove monad instance on filters; add applicative instance inducing the expected products
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified order/filter.lean
- \- *lemma* filter.mem_return_sets
- \+ *def* filter.seq



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/f53c776)
feat(analysis/topology): pi-spaces: topolopgy generation, prove second countability
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* is_open_set_pi
- \+ *lemma* pi_eq_generate_from
- \+ *lemma* pi_generate_from_eq
- \+ *lemma* pi_generate_from_eq_fintype

Modified analysis/topology/topological_space.lean
- \+ *lemma* generate_from_mono



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/da7bbd7)
feat(data/set): add set.pi
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* equiv.pi_equiv_subtype_sigma

Modified data/equiv/list.lean
- \+ *def* encodable.fintype_arrow
- \+ *def* encodable.fintype_pi

Modified data/finset.lean
- \+ *lemma* finset.set_of_mem

Modified data/fintype.lean
- \+ *lemma* finset.coe_univ

Modified data/set/basic.lean
- \+ *def* set.pi
- \+ *lemma* set.pi_empty_index
- \+ *lemma* set.pi_if
- \+ *lemma* set.pi_insert_index
- \+ *lemma* set.pi_singleton_index
- \+ *lemma* set.sep_set_of
- \+ *lemma* set.sep_univ
- \+ *lemma* set.set_of_mem

Modified data/set/countable.lean
- \+ *lemma* set.countable_pi

Modified data/set/lattice.lean
- \+ *lemma* set.pi_def

Modified logic/basic.lean
- \+ *lemma* rec_heq_of_heq



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/7944cc5)
fix(*): fix some problems introduced with 98152392bcd4b3f783602d030a5ab6a9e47e0088 and 9aec1d18d3c4cbad400d7ddcdd63b94d647b0a01
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/normed_space.lean


Modified analysis/topology/topological_space.lean


Modified linear_algebra/submodule.lean


Modified order/order_iso.lean
- \+/\- *theorem* order_iso.coe_coe_fn

Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* initial_seg.coe_coe_fn
- \+/\- *theorem* principal_seg.coe_coe_fn'
- \+/\- *theorem* principal_seg.coe_coe_fn



## [2018-09-21 00:09:04-04:00](https://github.com/leanprover-community/mathlib/commit/2485d8e)
fix(*): fix build
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified linear_algebra/basic.lean


Modified linear_algebra/submodule.lean


Modified logic/function.lean
- \+/\- *theorem* function.inv_fun_on_eq'

Modified order/basic.lean
- \+/\- *def* order.preimage



## [2018-09-20 19:46:48-04:00](https://github.com/leanprover-community/mathlib/commit/a4108eb)
fix(algebra/pi_instances): bugfix
#### Estimated changes
Modified algebra/pi_instances.lean


Modified linear_algebra/prod_module.lean
- \- *lemma* is_basis_inl_union_inr
- \- *lemma* is_linear_map_prod_fst
- \- *lemma* is_linear_map_prod_inl
- \- *lemma* is_linear_map_prod_inr
- \- *lemma* is_linear_map_prod_mk
- \- *lemma* is_linear_map_prod_snd
- \- *lemma* linear_independent_inl_union_inr
- \+ *lemma* prod.is_basis_inl_union_inr
- \+ *lemma* prod.is_linear_map_prod_fst
- \+ *lemma* prod.is_linear_map_prod_inl
- \+ *lemma* prod.is_linear_map_prod_inr
- \+ *lemma* prod.is_linear_map_prod_mk
- \+ *lemma* prod.is_linear_map_prod_snd
- \+ *lemma* prod.linear_independent_inl_union_inr
- \+ *lemma* prod.span_inl_union_inr
- \+ *lemma* prod.span_prod
- \- *lemma* span_inl_union_inr
- \- *lemma* span_prod



## [2018-09-20 19:21:02-04:00](https://github.com/leanprover-community/mathlib/commit/9aec1d1)
refactor(algebra/pi_instances): move prod instances to pi_instances file
#### Estimated changes
Modified algebra/group.lean


Modified algebra/pi_instances.lean
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
- \+ *lemma* prod.snd_inl
- \+ *lemma* prod.snd_inr
- \+ *lemma* prod.snd_inv
- \+ *lemma* prod.snd_mul
- \+ *lemma* prod.snd_one
- \+ *lemma* prod.snd_prod

Modified linear_algebra/prod_module.lean
- \+ *lemma* is_basis_inl_union_inr
- \+ *lemma* is_linear_map_prod_fst
- \+ *lemma* is_linear_map_prod_inl
- \+ *lemma* is_linear_map_prod_inr
- \+ *lemma* is_linear_map_prod_mk
- \+ *lemma* is_linear_map_prod_snd
- \+ *lemma* linear_independent_inl_union_inr
- \- *lemma* prod.fst_inl
- \- *lemma* prod.fst_inr
- \- *lemma* prod.fst_inv
- \- *lemma* prod.fst_mul
- \- *lemma* prod.fst_one
- \- *lemma* prod.fst_prod
- \- *lemma* prod.injective_inl
- \- *lemma* prod.injective_inr
- \- *def* prod.inl
- \- *lemma* prod.inl_eq_inl
- \- *lemma* prod.inl_eq_inr
- \- *def* prod.inr
- \- *lemma* prod.inr_eq_inl
- \- *lemma* prod.inr_eq_inr
- \- *lemma* prod.is_basis_inl_union_inr
- \- *lemma* prod.is_linear_map_prod_fst
- \- *lemma* prod.is_linear_map_prod_inl
- \- *lemma* prod.is_linear_map_prod_inr
- \- *lemma* prod.is_linear_map_prod_mk
- \- *lemma* prod.is_linear_map_prod_snd
- \- *lemma* prod.linear_independent_inl_union_inr
- \- *lemma* prod.snd_inl
- \- *lemma* prod.snd_inr
- \- *lemma* prod.snd_inv
- \- *lemma* prod.snd_mul
- \- *lemma* prod.snd_one
- \- *lemma* prod.snd_prod
- \- *lemma* prod.span_inl_union_inr
- \- *lemma* prod.span_prod
- \+ *lemma* span_inl_union_inr
- \+ *lemma* span_prod



## [2018-09-20 17:49:40-04:00](https://github.com/leanprover-community/mathlib/commit/3ba4e82)
feat(data/set/finite): finite_subset_Union, disjoint_mono
#### Estimated changes
Modified data/set/finite.lean
- \+ *theorem* set.finite_range
- \+ *lemma* set.finite_subset_Union

Modified data/set/lattice.lean
- \+ *theorem* disjoint_mono
- \+ *theorem* disjoint_mono_left
- \+ *theorem* disjoint_mono_right



## [2018-09-20 17:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/bd26b06)
refactor(linear_algebra/basic): move some lemmas to the right place
#### Estimated changes
Modified algebra/ring.lean
- \+ *lemma* zero_ne_one_or_forall_eq_0

Modified data/seq/computation.lean


Modified data/set/basic.lean
- \+ *lemma* set.diff_self

Modified linear_algebra/basic.lean
- \- *lemma* set.diff_self
- \- *lemma* zero_ne_one_or_forall_eq_0



## [2018-09-20 17:46:38-04:00](https://github.com/leanprover-community/mathlib/commit/1758092)
feat(data/subtype): subtype.coe_ext
#### Estimated changes
Modified data/subtype.lean
- \+ *lemma* subtype.coe_ext



## [2018-09-20 17:45:33-04:00](https://github.com/leanprover-community/mathlib/commit/9815239)
feat(logic/basic): more coe_trans instances
#### Estimated changes
Modified logic/basic.lean
- \+ *theorem* coe_fn_coe_base
- \+ *theorem* coe_fn_coe_trans
- \+ *theorem* coe_sort_coe_base
- \+ *theorem* coe_sort_coe_trans



## [2018-09-20 17:44:42-04:00](https://github.com/leanprover-community/mathlib/commit/0d6bae7)
refactor(order/filter): move directed to order.basic, swap definition
directed means containing upper bounds, not lower bounds
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *theorem* directed.finset_le

Modified order/basic.lean
- \+ *def* directed
- \+ *theorem* directed_comp
- \+ *theorem* directed_mono
- \+ *def* directed_on
- \+ *theorem* directed_on_iff_directed
- \+ *theorem* is_antisymm.swap
- \+ *theorem* is_asymm.swap
- \+/\- *theorem* is_irrefl.swap
- \+ *theorem* is_linear_order.swap
- \+ *theorem* is_partial_order.swap
- \+ *theorem* is_preorder.swap
- \+ *theorem* is_refl.swap
- \+ *theorem* is_total.swap
- \+ *theorem* is_total_preorder.swap
- \+ *def* order.preimage

Modified order/filter.lean
- \- *def* directed
- \+/\- *theorem* directed_of_chain
- \- *def* directed_on
- \+/\- *lemma* directed_on_Union
- \+/\- *lemma* filter.infi_sets_eq'
- \+/\- *lemma* filter.infi_sets_eq
- \+/\- *lemma* filter.map_infi_eq

Modified order/order_iso.lean
- \- *def* order.preimage



## [2018-09-20 17:41:18-04:00](https://github.com/leanprover-community/mathlib/commit/e054277)
feat(order/bounded_lattice): eq_top_mono
#### Estimated changes
Modified order/bounded_lattice.lean
- \+ *theorem* lattice.eq_bot_mono
- \+ *theorem* lattice.eq_top_mono



## [2018-09-20 17:40:57-04:00](https://github.com/leanprover-community/mathlib/commit/84024be)
feat(order/zorn): more zorn's lemma variants
#### Estimated changes
Modified order/zorn.lean
- \+ *theorem* zorn.chain.directed_on
- \+ *theorem* zorn.zorn_subset



## [2018-09-20 16:00:07+02:00](https://github.com/leanprover-community/mathlib/commit/1da8cc5)
feat(analysis/topology/uniform_structure): uniform_space.comap extra
lemmas
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_continuous_iff
- \+ *lemma* uniform_space.comap_comap_comp
- \+ *lemma* uniform_space_comap_id



## [2018-09-20 10:45:52+02:00](https://github.com/leanprover-community/mathlib/commit/d0f1b21)
feat(data/prod): add id_prod
#### Estimated changes
Modified data/prod.lean
- \+ *lemma* prod.id_prod



## [2018-09-19 11:24:25+02:00](https://github.com/leanprover-community/mathlib/commit/318ec36)
feat(group_theory/perm): sign_cycle and sign_bij ([#347](https://github.com/leanprover-community/mathlib/pull/347))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* int.units_pow_eq_pow_mod_two
- \+ *lemma* int.units_pow_two

Modified data/equiv/basic.lean
- \+/\- *theorem* equiv.swap_apply_left
- \+/\- *theorem* equiv.swap_apply_right
- \+/\- *theorem* equiv.swap_swap

Modified group_theory/perm.lean
- \+ *lemma* equiv.perm.card_support_swap
- \+ *lemma* equiv.perm.eq_inv_iff_eq
- \+ *lemma* equiv.perm.eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+ *lemma* equiv.perm.exists_int_pow_eq_of_is_cycle
- \+ *lemma* equiv.perm.inv_eq_iff_eq
- \+ *def* equiv.perm.is_cycle
- \+ *lemma* equiv.perm.is_cycle_inv
- \+ *lemma* equiv.perm.is_cycle_swap
- \+ *lemma* equiv.perm.is_cycle_swap_mul
- \+ *lemma* equiv.perm.is_cycle_swap_mul_aux₁
- \+ *lemma* equiv.perm.is_cycle_swap_mul_aux₂
- \+ *lemma* equiv.perm.is_swap_of_subtype
- \+ *lemma* equiv.perm.mem_iff_of_subtype_apply_mem
- \+ *lemma* equiv.perm.mem_support
- \+ *lemma* equiv.perm.mul_swap_eq_swap_mul
- \+ *def* equiv.perm.of_subtype
- \+ *lemma* equiv.perm.of_subtype_apply_of_not_mem
- \+ *lemma* equiv.perm.of_subtype_subtype_perm
- \+ *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self_int
- \+ *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self_nat
- \+ *lemma* equiv.perm.sign_aux3_symm_trans_trans
- \+ *lemma* equiv.perm.sign_bij
- \+ *lemma* equiv.perm.sign_cycle
- \+ *lemma* equiv.perm.sign_eq_sign_of_equiv
- \+ *lemma* equiv.perm.sign_inv
- \+ *lemma* equiv.perm.sign_mul
- \+ *lemma* equiv.perm.sign_of_subtype
- \+ *lemma* equiv.perm.sign_one
- \+ *lemma* equiv.perm.sign_prod_list_swap
- \+ *lemma* equiv.perm.sign_subtype_perm
- \+ *lemma* equiv.perm.sign_symm_trans_trans
- \+ *def* equiv.perm.subtype_perm
- \+ *lemma* equiv.perm.subtype_perm_of_subtype
- \+ *def* equiv.perm.support
- \+ *lemma* equiv.perm.support_swap
- \+ *lemma* equiv.perm.support_swap_mul_cycle
- \+ *lemma* equiv.perm.swap_mul_eq_mul_swap



## [2018-09-19 11:19:01+02:00](https://github.com/leanprover-community/mathlib/commit/ad9309f)
feat(data/polynomial): C_inj and dvd_iff_is_root ([#359](https://github.com/leanprover-community/mathlib/pull/359))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.C_inj
- \+ *lemma* polynomial.dvd_iff_is_root



## [2018-09-18 23:07:02-04:00](https://github.com/leanprover-community/mathlib/commit/ae0da3d)
feat(algebra/group_power): zero_pow et al
written by Chris Hughes
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* zero_pow

Modified data/fintype.lean
- \+ *lemma* fintype.injective_iff_bijective
- \+ *lemma* fintype.surjective_iff_bijective



## [2018-09-18 18:27:23-04:00](https://github.com/leanprover-community/mathlib/commit/61d0c65)
refactor(ring_theory/matrix): use pi instances
#### Estimated changes
Modified algebra/pi_instances.lean


Modified ring_theory/matrix.lean
- \+/\- *theorem* matrix.add_val
- \+/\- *theorem* matrix.neg_val
- \+/\- *theorem* matrix.zero_val



## [2018-09-18 17:03:51-04:00](https://github.com/leanprover-community/mathlib/commit/5260ab8)
feat(ring_theory/matrix): diagonal matrices
Joint work with Johan Commelin
#### Estimated changes
Modified ring_theory/matrix.lean
- \+ *def* matrix.diagonal
- \+ *theorem* matrix.diagonal_add
- \+ *theorem* matrix.diagonal_mul
- \+ *theorem* matrix.diagonal_mul_diagonal'
- \+ *theorem* matrix.diagonal_mul_diagonal
- \+ *theorem* matrix.diagonal_neg
- \+ *theorem* matrix.diagonal_one
- \+ *theorem* matrix.diagonal_val_eq
- \+ *theorem* matrix.diagonal_val_ne'
- \+ *theorem* matrix.diagonal_val_ne
- \+ *theorem* matrix.diagonal_zero
- \+ *theorem* matrix.mul_diagonal
- \+ *theorem* matrix.mul_eq_mul
- \+/\- *theorem* matrix.mul_val'
- \+/\- *theorem* matrix.mul_val
- \+/\- *theorem* matrix.one_val_eq
- \+/\- *theorem* matrix.one_val_ne'
- \+/\- *theorem* matrix.one_val_ne



## [2018-09-18 13:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/a72807f)
feat(ring_theory/matrix): (finally!) adding matrices ([#334](https://github.com/leanprover-community/mathlib/pull/334))
Joint work by: Ellen Arlt, Blair Shi, Sean Leather, Scott Morrison, Johan Commelin, Kenny Lau, Johannes Hölzl, Mario Carneiro
#### Estimated changes
Added ring_theory/matrix.lean
- \+ *theorem* matrix.add_mul
- \+ *theorem* matrix.add_val
- \+ *theorem* matrix.ext
- \+ *theorem* matrix.ext_iff
- \+ *theorem* matrix.mul_add
- \+ *theorem* matrix.mul_val'
- \+ *theorem* matrix.mul_val
- \+ *theorem* matrix.mul_zero
- \+ *theorem* matrix.neg_val
- \+ *theorem* matrix.one_val
- \+ *theorem* matrix.one_val_eq
- \+ *theorem* matrix.one_val_ne'
- \+ *theorem* matrix.one_val_ne
- \+ *theorem* matrix.zero_mul
- \+ *theorem* matrix.zero_val
- \+ *def* matrix



## [2018-09-18 15:20:04+02:00](https://github.com/leanprover-community/mathlib/commit/7dedf3c)
feat(analysis/topology): injective_separated_pure_cauchy
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* Cauchy.injective_separated_pure_cauchy

Modified docs/extras/well_founded_recursion.md




## [2018-09-17 14:40:15-04:00](https://github.com/leanprover-community/mathlib/commit/2e204f2)
feat(category/functor): make `sum` `functor` instance more universe polymorphic
#### Estimated changes
Modified category/functor.lean




## [2018-09-17 14:39:36-04:00](https://github.com/leanprover-community/mathlib/commit/9d28f8b)
feat(tactic/ext): remove lambda abstractions when inferring a type's name
#### Estimated changes
Modified tactic/ext.lean




## [2018-09-17 13:25:46+02:00](https://github.com/leanprover-community/mathlib/commit/62c69b7)
feat(tactic/linarith): option to prove arbitrary goals by exfalso, enabled by default
#### Estimated changes
Modified docs/tactics.md


Modified tactic/linarith.lean


Modified tests/linarith.lean




## [2018-09-17 11:58:19+02:00](https://github.com/leanprover-community/mathlib/commit/e9af59d)
feat(algebra/order_functions): add simp rules for min/max_eq_left/right (closes [#306](https://github.com/leanprover-community/mathlib/pull/306))
#### Estimated changes
Modified algebra/field_power.lean
- \+/\- *def* fpow
- \+/\- *lemma* fpow_add
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* pow_le_max_of_min_le

Modified algebra/order_functions.lean
- \+/\- *lemma* min_add
- \+/\- *lemma* min_sub

Modified analysis/measure_theory/lebesgue_measure.lean


Modified computability/partrec_code.lean


Modified data/list/basic.lean




## [2018-09-17 09:15:23+02:00](https://github.com/leanprover-community/mathlib/commit/cf260ca)
feat(category_theory/*): some lemmas about universes
#### Estimated changes
Modified category_theory/category.lean


Modified category_theory/functor.lean
- \+ *def* category_theory.functor.ulift_down
- \+ *def* category_theory.functor.ulift_up

Modified category_theory/natural_isomorphism.lean
- \+ *def* category_theory.functor.ulift_down_up
- \+ *def* category_theory.functor.ulift_up_down



## [2018-09-15 17:30:09+02:00](https://github.com/leanprover-community/mathlib/commit/04c4abf)
fix(algebra/group): fix bit0_zero to use (0 : alpha) not (0 : nat)
#### Estimated changes
Modified algebra/group.lean
- \+/\- *lemma* bit0_zero
- \+/\- *lemma* bit1_zero



## [2018-09-15 17:29:12+02:00](https://github.com/leanprover-community/mathlib/commit/39bab47)
feat(linear_algebra): dimension theorem ([#345](https://github.com/leanprover-community/mathlib/pull/345))
* dimension theorem
* more theorems about dimension
* cardinal stuff
* fix error
* move A/S x S = A to quotient_module.lean
* remove pempty_equiv_empty
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* equiv.arrow_punit_equiv_punit
- \- *def* equiv.arrow_unit_equiv_unit
- \+ *def* equiv.bool_equiv_punit_sum_punit
- \- *def* equiv.bool_equiv_unit_sum_unit
- \+ *def* equiv.empty_arrow_equiv_punit
- \- *def* equiv.empty_arrow_equiv_unit
- \+ *def* equiv.empty_equiv_pempty
- \+ *def* equiv.equiv_sigma_subtype
- \+ *def* equiv.false_arrow_equiv_punit
- \- *def* equiv.false_arrow_equiv_unit
- \+ *def* equiv.nat_equiv_nat_sum_punit
- \- *def* equiv.nat_equiv_nat_sum_unit
- \+ *def* equiv.nat_sum_punit_equiv_nat
- \- *def* equiv.nat_sum_unit_equiv_nat
- \+ *def* equiv.option_equiv_sum_punit
- \- *def* equiv.option_equiv_sum_unit
- \+ *def* equiv.pempty_arrow_equiv_punit
- \- *def* equiv.pempty_arrow_equiv_unit
- \+ *def* equiv.pempty_of_not_nonempty
- \+ *def* equiv.prod_punit
- \+ *theorem* equiv.prod_punit_apply
- \- *def* equiv.prod_unit
- \- *theorem* equiv.prod_unit_apply
- \+ *def* equiv.punit_arrow_equiv
- \+ *def* equiv.punit_prod
- \+ *theorem* equiv.punit_prod_apply
- \+ *def* equiv.true_equiv_punit
- \- *def* equiv.unit_arrow_equiv
- \- *def* equiv.unit_prod
- \- *theorem* equiv.unit_prod_apply

Modified data/equiv/encodable.lean


Modified data/fintype.lean
- \+ *theorem* fintype.card_punit
- \+ *theorem* fintype.univ_punit

Modified linear_algebra/basic.lean
- \+ *lemma* is_basis.linear_equiv

Modified linear_algebra/dimension.lean
- \+ *theorem* vector_space.basis_le_span
- \+ *theorem* vector_space.dim_eq_of_linear_equiv
- \+ *theorem* vector_space.dim_im_add_dim_ker
- \+ *theorem* vector_space.dim_prod
- \+ *theorem* vector_space.dim_quotient
- \+ *theorem* vector_space.mk_basis
- \+ *theorem* vector_space.mk_eq_mk_of_basis

Modified linear_algebra/quotient_module.lean
- \+ *theorem* quotient_module.quotient_prod_linear_equiv

Modified set_theory/cardinal.lean
- \+ *lemma* cardinal.finset_card
- \+ *theorem* cardinal.mk_Prop
- \+ *theorem* cardinal.mk_Union_le_sum_mk
- \+ *theorem* cardinal.mk_bool
- \+ *theorem* cardinal.mk_empty'
- \+ *theorem* cardinal.mk_empty
- \+ *theorem* cardinal.mk_eq_of_injective
- \+ *theorem* cardinal.mk_list_eq_sum_pow
- \+ *theorem* cardinal.mk_option
- \+ *theorem* cardinal.mk_pempty
- \+ *theorem* cardinal.mk_plift_false
- \+ *theorem* cardinal.mk_plift_true
- \+ *theorem* cardinal.mk_punit
- \+ *theorem* cardinal.mk_singleton
- \+ *theorem* cardinal.mk_union_add_mk_inter
- \+ *theorem* cardinal.mk_union_of_disjiont
- \+ *theorem* cardinal.mk_unit

Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean
- \+ *theorem* cardinal.mk_list_eq_mk
- \+ *theorem* cardinal.pow_le



## [2018-09-14 14:57:58+02:00](https://github.com/leanprover-community/mathlib/commit/52bc8b6)
fix(analysis/normed_space): Add instance showing that normed field is a normed space over itself
#### Estimated changes
Modified analysis/normed_space.lean




## [2018-09-14 14:51:33+02:00](https://github.com/leanprover-community/mathlib/commit/9daf78b)
feat(tactic/linarith): basic support for nat ([#343](https://github.com/leanprover-community/mathlib/pull/343))
* feat(tactic/linarith): basic support for nats
* fix(tactic/linarith): typo
#### Estimated changes
Modified tactic/linarith.lean
- \+ *lemma* linarith.int.coe_nat_bit0
- \+ *lemma* linarith.int.coe_nat_bit1
- \+ *lemma* linarith.nat_eq_subst
- \+ *lemma* linarith.nat_le_subst
- \+ *lemma* linarith.nat_lt_subst

Modified tests/linarith.lean




## [2018-09-14 14:47:42+02:00](https://github.com/leanprover-community/mathlib/commit/21233b7)
fix(category_theory/*): several minor fixes, preparatory to presheaves ([#342](https://github.com/leanprover-community/mathlib/pull/342))
* fix(category_theory/*): several minor fixes, preparatory to PR’ing the category of presheaves
In category.lean, better proofs in `instance [preorder α] : small_category α := …`.
In natural_isomorphism.lean, some rfl lemmas, natural isomorphisms describing functor composition, and formatting
In examples/topological_spaces.lean, deciding to reverse the arrows in `open_set X` (the category of open sets, with restrictions), to reduce using opposites later, as well as describing the functoriality of `open_set`.
* additional simp lemmas
#### Estimated changes
Modified category_theory/category.lean
- \+ *lemma* category_theory.concrete_category_comp
- \+ *lemma* category_theory.concrete_category_id

Modified category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.open_set.map
- \+ *def* category_theory.examples.open_set.map_id
- \+ *lemma* category_theory.examples.open_set.map_id_obj
- \+ *def* category_theory.examples.open_set.map_iso
- \+ *def* category_theory.examples.open_set.map_iso_id
- \+/\- *def* category_theory.examples.open_set.nbhd
- \+/\- *def* category_theory.examples.open_set.nbhds
- \+/\- *structure* category_theory.examples.open_set

Modified category_theory/natural_isomorphism.lean
- \+ *def* category_theory.functor.assoc
- \+ *def* category_theory.functor.comp_id
- \+ *def* category_theory.functor.id_comp
- \+ *lemma* category_theory.nat_iso.mk_app'
- \+ *lemma* category_theory.nat_iso.mk_app
- \+/\- *lemma* category_theory.nat_iso.naturality_1
- \+/\- *lemma* category_theory.nat_iso.naturality_2
- \+ *def* category_theory.nat_iso.of_components.app
- \+ *def* category_theory.nat_iso.of_components.hom_app
- \+ *def* category_theory.nat_iso.of_components.inv_app
- \+/\- *def* category_theory.nat_iso.of_components



## [2018-09-13 13:42:52-04:00](https://github.com/leanprover-community/mathlib/commit/a770ee5)
fix(data/padics/padic_rationals): fix proof
#### Estimated changes
Modified data/padics/padic_rationals.lean
- \+/\- *lemma* padic.cast_eq_of_rat
- \+/\- *theorem* padic.complete
- \+/\- *lemma* padic.exi_rat_seq_conv
- \+/\- *def* padic.mk
- \+/\- *theorem* padic.rat_dense
- \+/\- *theorem* padic_norm_e.nonarchimedean
- \+/\- *lemma* padic_norm_e.sub_rev
- \+/\- *lemma* padic_norm_e.zero_def
- \+/\- *def* padic_norm_e
- \+/\- *theorem* padic_seq.norm_equiv
- \+/\- *lemma* padic_seq.norm_nonzero_of_not_equiv_zero
- \+/\- *lemma* padic_seq.stationary



## [2018-09-13 12:28:42-04:00](https://github.com/leanprover-community/mathlib/commit/46502df)
feat(algebra/ordered_ring): mul_self_pos
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_one
- \+ *lemma* mul_self_pos



## [2018-09-13 12:07:41-04:00](https://github.com/leanprover-community/mathlib/commit/bebe170)
feat(data/int/order): delete int.order and prove all commented out lemmas ([#348](https://github.com/leanprover-community/mathlib/pull/348))
#### Estimated changes
Modified algebra/archimedean.lean


Modified data/int/basic.lean
- \+ *lemma* int.coe_nat_succ_pos
- \+ *lemma* int.units_inv_eq_self

Deleted data/int/order.lean
- \- *lemma* int.le_of_of_nat_le_of_nat
- \- *lemma* int.of_nat_le_of_nat_of_le



## [2018-09-11 13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/1206356)
fix(doc/tactics): fix typo in documentation of `ext`
#### Estimated changes
Modified docs/tactics.md




## [2018-09-11 10:40:33+02:00](https://github.com/leanprover-community/mathlib/commit/36a82cb)
feat(tactic/ext): use `rcases` patterns to intro `ext` variables
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/ext.lean


Modified tactic/interactive.lean


Modified tactic/pi_instances.lean


Modified tactic/rcases.lean


Modified tests/tactics.lean




## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/ffc6bc0)
feat(tactic/ext): add support for propext
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/ext.lean




## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/c25ca3b)
feat(tactic/ext): address reviewers' comments
#### Estimated changes
Modified core/data/list.lean


Modified docs/tactics.md


Modified tactic/ext.lean




## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4e3b89c)
feat(tactic/ext): make the attribute incremental
#### Estimated changes
Modified category_theory/isomorphism.lean


Added core/data/list.lean
- \+ *def* list.partition_map

Added core/default.lean


Modified data/list/basic.lean
- \+/\- *theorem* list.erase_diff_erase_sublist_of_sublist
- \+/\- *theorem* list.index_of_eq_length

Modified data/sum.lean
- \+ *def* sum.map

Modified docs/tactics.md


Modified tactic/ext.lean
- \+ *def* ext_param_type

Modified tactic/pi_instances.lean




## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/6557f51)
feat(tactic/ext): add indexing of extensionality lemmas
#### Estimated changes
Modified category_theory/isomorphism.lean
- \+/\- *def* category_theory.inv
- \+/\- *def* category_theory.is_iso.hom_inv_id
- \+/\- *def* category_theory.is_iso.inv_hom_id
- \+/\- *lemma* category_theory.iso.hom_inv_id
- \+/\- *lemma* category_theory.iso.inv_hom_id
- \+/\- *def* category_theory.iso.refl
- \+/\- *def* category_theory.iso.symm
- \+/\- *def* category_theory.iso.trans

Modified tactic/basic.lean


Modified tactic/ext.lean




## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/4efdbdb)
feat(tactic/ext): match extensionality lemma more exactly
#### Estimated changes
Modified tactic/basic.lean


Modified tests/tactics.lean




## [2018-09-11 10:07:19+02:00](https://github.com/leanprover-community/mathlib/commit/ba7bd74)
feat(category_theory): Yoneda, basic facts about natural isomorphisms, and an extensionality lemma using Yoneda lemma ([#326](https://github.com/leanprover-community/mathlib/pull/326))
* feat(category_theory/yoneda_lemma)
* feat(category_theory/natural_isomorphisms): basic facts about natural isomorphisms, and an extensionality lemma using Yoneda
#### Estimated changes
Added category_theory/natural_isomorphism.lean
- \+ *def* category_theory.nat_iso.app
- \+ *lemma* category_theory.nat_iso.comp_app
- \+ *lemma* category_theory.nat_iso.hom_eq_coe
- \+ *lemma* category_theory.nat_iso.inv_eq_symm_coe
- \+ *lemma* category_theory.nat_iso.naturality_1
- \+ *lemma* category_theory.nat_iso.naturality_2
- \+ *def* category_theory.nat_iso.of_components

Modified category_theory/types.lean
- \+ *lemma* category_theory.types.iso_mk_coe

Added category_theory/yoneda.lean
- \+ *def* category_theory.yoneda.ext
- \+ *lemma* category_theory.yoneda.map_app
- \+ *lemma* category_theory.yoneda.naturality
- \+ *lemma* category_theory.yoneda.obj_map
- \+ *lemma* category_theory.yoneda.obj_map_id
- \+ *lemma* category_theory.yoneda.obj_obj
- \+ *def* category_theory.yoneda
- \+ *def* category_theory.yoneda_evaluation
- \+ *lemma* category_theory.yoneda_evaluation_map_down
- \+ *def* category_theory.yoneda_lemma
- \+ *def* category_theory.yoneda_pairing
- \+ *lemma* category_theory.yoneda_pairing_map



## [2018-09-10 20:50:08-04:00](https://github.com/leanprover-community/mathlib/commit/40a365a)
feat(tactic/replacer): add support for parameters in replacer
#### Estimated changes
Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/replacer.lean


Modified tests/replacer.lean




## [2018-09-10 22:46:23+02:00](https://github.com/leanprover-community/mathlib/commit/a7995c9)
fix(set_theory/cofinality): fix type of omega_is_regular
#### Estimated changes
Modified set_theory/cofinality.lean
- \+/\- *theorem* cardinal.omega_is_regular



## [2018-09-10 22:44:42+02:00](https://github.com/leanprover-community/mathlib/commit/0e06944)
feat(data/equiv/basic): quot_equiv_of_quot(')
quot_equiv_of_quot matches matches the existing subtype_equiv_of_subtype,
but quot_equiv_of_quot' is useful in practice and this definition is careful
to use eq.rec only in proofs.
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* equiv.quot_equiv_of_quot'
- \+ *def* equiv.quot_equiv_of_quot



## [2018-09-10 22:40:31+02:00](https://github.com/leanprover-community/mathlib/commit/61f4827)
fix(logic/basic): remove unnecessary hypothesis from proof_irrel_heq
#### Estimated changes
Modified logic/basic.lean
- \+/\- *theorem* proof_irrel_heq



## [2018-09-10 13:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/b33764d)
feat(algebra/module): semimodules
#### Estimated changes
Modified algebra/module.lean
- \+ *theorem* add_smul'
- \+ *theorem* mul_smul'
- \+/\- *theorem* mul_smul
- \+ *theorem* one_smul'
- \+ *theorem* smul_add'
- \+ *lemma* smul_eq_mul'
- \+ *lemma* smul_smul'
- \+ *theorem* smul_zero'
- \+ *theorem* zero_smul'

Modified analysis/measure_theory/outer_measure.lean
- \- *theorem* measure_theory.outer_measure.add_smul
- \- *theorem* measure_theory.outer_measure.mul_smul
- \- *theorem* measure_theory.outer_measure.one_smul
- \- *def* measure_theory.outer_measure.smul
- \- *theorem* measure_theory.outer_measure.smul_add
- \- *theorem* measure_theory.outer_measure.smul_zero
- \- *theorem* measure_theory.outer_measure.zero_smul

Modified tactic/abel.lean




## [2018-09-10 03:23:58-04:00](https://github.com/leanprover-community/mathlib/commit/56c4919)
feat(tactic/abel): decision procedure for comm groups
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* gsmul_add
- \+ *theorem* gsmul_zero
- \+ *theorem* mul_gpow
- \+/\- *theorem* one_gpow

Added tactic/abel.lean
- \+ *theorem* tactic.abel.const_add_term
- \+ *theorem* tactic.abel.const_add_termg
- \+ *inductive* tactic.abel.normalize_mode
- \+ *def* tactic.abel.smul
- \+ *def* tactic.abel.smulg
- \+ *lemma* tactic.abel.subst_into_smul
- \+ *lemma* tactic.abel.subst_into_smulg
- \+ *def* tactic.abel.term
- \+ *theorem* tactic.abel.term_add_const
- \+ *theorem* tactic.abel.term_add_constg
- \+ *theorem* tactic.abel.term_add_term
- \+ *theorem* tactic.abel.term_add_termg
- \+ *theorem* tactic.abel.term_atom
- \+ *theorem* tactic.abel.term_atomg
- \+ *theorem* tactic.abel.term_neg
- \+ *theorem* tactic.abel.term_smul
- \+ *theorem* tactic.abel.term_smulg
- \+ *def* tactic.abel.termg
- \+ *theorem* tactic.abel.unfold_gsmul
- \+ *theorem* tactic.abel.unfold_smul
- \+ *theorem* tactic.abel.unfold_smulg
- \+ *lemma* tactic.abel.unfold_sub
- \+ *theorem* tactic.abel.zero_smul
- \+ *theorem* tactic.abel.zero_smulg
- \+ *theorem* tactic.abel.zero_term
- \+ *theorem* tactic.abel.zero_termg

Modified tactic/norm_num.lean
- \+ *lemma* norm_num.subst_into_neg

Modified tactic/ring.lean
- \- *def* horner
- \+/\- *theorem* tactic.ring.add_neg_eq_sub
- \+ *def* tactic.ring.horner
- \- *lemma* tactic.ring.subst_into_neg

Modified tactic/ring2.lean




## [2018-09-09 23:23:59-04:00](https://github.com/leanprover-community/mathlib/commit/f10e7ad)
refactor(tactic/ring): remove unnecessary rat from horner_expr
#### Estimated changes
Modified tactic/ring.lean




## [2018-09-09 23:23:53-04:00](https://github.com/leanprover-community/mathlib/commit/eab064e)
refactor(tactic/ring): use horner_expr instead of destruct on expr
#### Estimated changes
Modified tactic/ring.lean




## [2018-09-09 23:23:45-04:00](https://github.com/leanprover-community/mathlib/commit/484afdf)
test(tests/ring): add test file for ring
#### Estimated changes
Renamed tests/linarith_tests.lean to tests/linarith.lean


Added tests/ring.lean




## [2018-09-09 20:45:05-04:00](https://github.com/leanprover-community/mathlib/commit/181905e)
refactor(tactic/linarith): refactoring
#### Estimated changes
Modified data/prod.lean


Modified meta/rb_map.lean


Modified tactic/linarith.lean
- \+/\- *lemma* linarith.add_subst
- \- *def* linarith.alist_lt
- \+/\- *def* linarith.ineq.is_lt
- \+/\- *def* linarith.ineq.to_string
- \+/\- *lemma* linarith.mul_subst
- \- *def* linarith.reduce_pair_option
- \+/\- *lemma* linarith.sub_subst



## [2018-09-09 18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/4be1ef1)
fix
#### Estimated changes
Modified ring_theory/ideals.lean




## [2018-09-09 18:34:27+02:00](https://github.com/leanprover-community/mathlib/commit/5b7edec)
feat(category_theory): redesign of concrete categories
Also exercising it further with `def forget_to_Mon : CommRing ⥤ Mon := …`
#### Estimated changes
Modified algebra/group.lean


Modified algebra/ring.lean


Modified category_theory/category.lean
- \+ *structure* category_theory.bundled
- \+/\- *structure* category_theory.concrete_category
- \+ *def* category_theory.mk_ob

Modified category_theory/embedding.lean
- \+ *lemma* category_theory.functor.image_preimage
- \+ *def* category_theory.functor.injectivity
- \+ *def* category_theory.functor.preimage
- \- *lemma* category_theory.image_preimage
- \- *def* category_theory.preimage
- \+/\- *lemma* category_theory.preimage_iso_coe
- \+/\- *lemma* category_theory.preimage_iso_symm_coe

Modified category_theory/examples/measurable_space.lean
- \+/\- *def* category_theory.examples.Meas

Added category_theory/examples/monoids.lean
- \+ *def* category_theory.examples.CommMon.forget_to_Mon
- \+ *def* category_theory.examples.CommMon
- \+ *def* category_theory.examples.Mon
- \+ *def* category_theory.examples.is_comm_monoid_hom

Modified category_theory/examples/rings.lean
- \+ *def* category_theory.examples.CommRing.forget_to_CommMon
- \+ *def* category_theory.examples.CommRing
- \+ *def* category_theory.examples.Ring
- \- *lemma* category_theory.examples.comm_ring_hom.map_add
- \- *lemma* category_theory.examples.comm_ring_hom.map_mul
- \- *lemma* category_theory.examples.comm_ring_hom.map_one
- \- *def* category_theory.examples.{u}

Modified category_theory/examples/topological_spaces.lean
- \+/\- *def* category_theory.examples.Top

Modified category_theory/functor.lean
- \+ *def* category_theory.bundled.map

Modified category_theory/types.lean
- \+/\- *def* category_theory.forget



## [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/aaa113a)
fix(tactic/linarith): improve earlier fix
#### Estimated changes
Modified tactic/linarith.lean


Modified tests/linarith_tests.lean




## [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/fa747b0)
fix(tactic/linarith): proper handling of 0 coefficients in input
#### Estimated changes
Modified tactic/linarith.lean




## [2018-09-09 18:32:02+02:00](https://github.com/leanprover-community/mathlib/commit/675c235)
fix(tactic/linarith): make more use of equality hypotheses
#### Estimated changes
Modified tactic/linarith.lean


Modified tests/linarith_tests.lean




## [2018-09-09 15:01:18+02:00](https://github.com/leanprover-community/mathlib/commit/53cc7ce)
refactor(data/polynomial): generalize leading_coeff_X_pow ([#329](https://github.com/leanprover-community/mathlib/pull/329))
Generalize `leading_coeff_X_pow` to `comm_semiring`
#### Estimated changes
Modified data/polynomial.lean




## [2018-09-08 19:25:06-04:00](https://github.com/leanprover-community/mathlib/commit/fc1fd3d)
feat(set_theory/cofinality): sum_lt_of_is_regular
#### Estimated changes
Modified set_theory/cardinal.lean
- \+/\- *theorem* cardinal.sup_le

Modified set_theory/cofinality.lean
- \+ *theorem* cardinal.sum_lt_of_is_regular
- \+ *theorem* cardinal.sup_lt_of_is_regular

Modified set_theory/ordinal.lean
- \+ *theorem* cardinal.add_lt_of_lt
- \+ *theorem* cardinal.mul_lt_of_lt
- \+ *theorem* ordinal.sup_ord



## [2018-09-08 20:54:21+02:00](https://github.com/leanprover-community/mathlib/commit/73abe2e)
fix(category_theory/products): fix types of inl/inr/fst/snd ([#320](https://github.com/leanprover-community/mathlib/pull/320))
#### Estimated changes
Modified category_theory/products.lean
- \+/\- *def* category_theory.prod.fst
- \+/\- *def* category_theory.prod.inl
- \+/\- *def* category_theory.prod.inr
- \+/\- *def* category_theory.prod.snd



## [2018-09-08 20:17:26+02:00](https://github.com/leanprover-community/mathlib/commit/5613d2e)
feat(tactic): add support for quotients to rcases
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* continuous_multiset_sum
- \+/\- *lemma* tendsto_multiset_sum

Modified data/equiv/encodable.lean


Modified data/multiset.lean
- \+/\- *theorem* multiset.cons_inj_right

Modified data/quot.lean
- \+/\- *lemma* quotient.exact'

Modified docs/tactics.md


Modified group_theory/free_group.lean
- \+/\- *def* free_group.to_word.inj
- \+/\- *def* free_group.to_word.mk

Modified ring_theory/associated.lean
- \+/\- *theorem* associates.mul_zero
- \+/\- *theorem* associates.zero_mul

Modified ring_theory/unique_factorization_domain.lean


Modified set_theory/cardinal.lean
- \+/\- *theorem* cardinal.add_le_add
- \+/\- *theorem* cardinal.cantor
- \+/\- *theorem* cardinal.mul_le_mul
- \+/\- *theorem* cardinal.power_le_power_left
- \+/\- *theorem* cardinal.zero_le

Modified tactic/interactive.lean


Modified tactic/rcases.lean




## [2018-09-08 11:44:06+02:00](https://github.com/leanprover-community/mathlib/commit/1b9b139)
refactor(linear_algebra/prod_module): move prod.ring ([#322](https://github.com/leanprover-community/mathlib/pull/322))
#### Estimated changes
Modified analysis/normed_space.lean


Modified linear_algebra/prod_module.lean




## [2018-09-07 17:43:56+02:00](https://github.com/leanprover-community/mathlib/commit/5aa65d6)
order(filter): rename `vmap` to `comap`
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *lemma* nhds_comap_dist
- \- *lemma* nhds_vmap_dist

Modified analysis/nnreal.lean


Modified analysis/real.lean


Modified analysis/topology/continuity.lean
- \+ *lemma* dense_embedding.comap_nhds_neq_bot
- \+ *lemma* dense_embedding.tendsto_comap_nhds_nhds
- \- *lemma* dense_embedding.tendsto_vmap_nhds_nhds
- \- *lemma* dense_embedding.vmap_nhds_neq_bot
- \+ *lemma* nhds_induced_eq_comap
- \- *lemma* nhds_induced_eq_vmap
- \+ *lemma* nhds_subtype_eq_comap
- \- *lemma* nhds_subtype_eq_vmap

Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* filter.map_neg

Modified analysis/topology/uniform_space.lean
- \+ *lemma* cauchy_comap
- \- *lemma* cauchy_vmap
- \+ *lemma* comap_quotient_eq_uniformity
- \+ *lemma* comap_quotient_le_uniformity
- \+/\- *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* nhds_eq_comap_uniformity
- \- *lemma* nhds_eq_vmap_uniformity
- \+/\- *lemma* separated_of_uniform_continuous
- \+ *theorem* to_topological_space_comap
- \- *theorem* to_topological_space_vmap
- \+/\- *lemma* uniform_continuous.prod_mk
- \+ *lemma* uniform_continuous_comap'
- \+ *lemma* uniform_continuous_comap
- \- *lemma* uniform_continuous_vmap'
- \- *lemma* uniform_continuous_vmap
- \+ *def* uniform_space.comap
- \- *def* uniform_space.vmap
- \- *lemma* vmap_quotient_eq_uniformity
- \- *lemma* vmap_quotient_le_uniformity

Modified data/analysis/filter.lean


Modified order/filter.lean
- \+ *def* filter.comap
- \+ *lemma* filter.comap_bot
- \+ *lemma* filter.comap_comap_comp
- \+ *theorem* filter.comap_eq_lift'
- \+ *lemma* filter.comap_eq_of_inverse
- \+ *lemma* filter.comap_id
- \+ *lemma* filter.comap_inf
- \+ *lemma* filter.comap_infi
- \+ *theorem* filter.comap_lift'_eq2
- \+ *theorem* filter.comap_lift'_eq
- \+ *theorem* filter.comap_lift_eq2
- \+ *lemma* filter.comap_lift_eq
- \+ *lemma* filter.comap_map
- \+ *lemma* filter.comap_mono
- \+ *lemma* filter.comap_neq_bot
- \+ *lemma* filter.comap_neq_bot_of_surj
- \+ *theorem* filter.comap_principal
- \+ *lemma* filter.comap_sup
- \+ *lemma* filter.comap_top
- \+ *lemma* filter.gc_map_comap
- \- *lemma* filter.gc_map_vmap
- \+ *lemma* filter.le_comap_map
- \+ *lemma* filter.le_map_comap'
- \+ *lemma* filter.le_map_comap
- \- *lemma* filter.le_map_vmap'
- \- *lemma* filter.le_map_vmap
- \- *lemma* filter.le_vmap_map
- \+/\- *lemma* filter.map_bot
- \+ *lemma* filter.map_comap_le
- \+ *lemma* filter.map_eq_comap_of_inverse
- \- *lemma* filter.map_eq_vmap_of_inverse
- \+ *lemma* filter.map_le_iff_le_comap
- \- *lemma* filter.map_le_iff_le_vmap
- \+/\- *lemma* filter.map_mono
- \+/\- *lemma* filter.map_sup
- \+ *lemma* filter.map_swap_eq_comap_swap
- \- *lemma* filter.map_swap_eq_vmap_swap
- \- *lemma* filter.map_vmap_le
- \+ *theorem* filter.mem_comap_sets
- \- *theorem* filter.mem_vmap_sets
- \+ *lemma* filter.monotone_comap
- \- *lemma* filter.monotone_vmap
- \+ *theorem* filter.preimage_mem_comap
- \- *theorem* filter.preimage_mem_vmap
- \+ *lemma* filter.prod_comap_comap_eq
- \+/\- *lemma* filter.prod_comm'
- \- *lemma* filter.prod_vmap_vmap_eq
- \+ *lemma* filter.sInter_comap_sets
- \- *lemma* filter.sInter_vmap_sets
- \+ *lemma* filter.tendsto_comap''
- \+ *lemma* filter.tendsto_comap
- \+ *lemma* filter.tendsto_comap_iff
- \+ *lemma* filter.tendsto_iff_comap
- \- *lemma* filter.tendsto_iff_vmap
- \- *lemma* filter.tendsto_vmap''
- \- *lemma* filter.tendsto_vmap
- \- *lemma* filter.tendsto_vmap_iff
- \- *def* filter.vmap
- \- *lemma* filter.vmap_bot
- \- *theorem* filter.vmap_eq_lift'
- \- *lemma* filter.vmap_eq_of_inverse
- \- *lemma* filter.vmap_id
- \- *lemma* filter.vmap_inf
- \- *lemma* filter.vmap_infi
- \- *theorem* filter.vmap_lift'_eq2
- \- *theorem* filter.vmap_lift'_eq
- \- *theorem* filter.vmap_lift_eq2
- \- *lemma* filter.vmap_lift_eq
- \- *lemma* filter.vmap_map
- \- *lemma* filter.vmap_mono
- \- *lemma* filter.vmap_neq_bot
- \- *lemma* filter.vmap_neq_bot_of_surj
- \- *theorem* filter.vmap_principal
- \- *lemma* filter.vmap_sup
- \- *lemma* filter.vmap_top
- \- *lemma* filter.vmap_vmap_comp



## [2018-09-07 17:32:23+02:00](https://github.com/leanprover-community/mathlib/commit/2524dba)
fix(algebra/big_operators): change name of `sum_attach` to `finset.sum_attach`
#### Estimated changes
Modified algebra/big_operators.lean




## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/8f89324)
style(linear_algebra/submodule): changed import order; added product construction
#### Estimated changes
Modified linear_algebra/submodule.lean
- \+ *lemma* submodule.coe_prod
- \+ *def* submodule.prod



## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/085c012)
refactor(linear_algebra, ring_theory): rework submodules; move them to linear_algebra
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.image_eq_image
- \+ *lemma* set.image_subset_image_iff
- \+ *lemma* set.injective_image
- \+ *lemma* set.preimage_eq_preimage
- \- *theorem* set.set_coe.exists
- \- *theorem* set.set_coe.forall
- \- *theorem* set.set_coe_cast
- \+/\- *theorem* set.set_coe_eq_subtype
- \+ *lemma* set.surjective_preimage
- \+ *theorem* set_coe.exists
- \+ *theorem* set_coe.ext
- \+ *theorem* set_coe.ext_iff
- \+ *theorem* set_coe.forall
- \+ *theorem* set_coe_cast
- \+ *lemma* subtype.mem

Modified linear_algebra/linear_map_module.lean
- \- *lemma* classical.some_spec2

Modified linear_algebra/quotient_module.lean
- \+ *lemma* quotient_module.coe_eq_zero

Added linear_algebra/submodule.lean
- \+ *theorem* submodule.Union_set_of_directed
- \+ *theorem* submodule.bot_set
- \+ *lemma* submodule.coe_comap
- \+ *lemma* submodule.coe_map
- \+ *def* submodule.comap
- \+ *lemma* submodule.comap_comp
- \+ *lemma* submodule.comap_id
- \+ *lemma* submodule.comap_map_eq
- \+ *def* submodule.comap_quotient.order_iso
- \+ *def* submodule.comap_quotient
- \+ *theorem* submodule.ext
- \+ *lemma* submodule.injective_comap
- \+ *lemma* submodule.injective_map
- \+ *def* submodule.lt_order_embedding
- \+ *def* submodule.map
- \+ *lemma* submodule.map_comp
- \+ *lemma* submodule.map_id
- \+ *def* submodule.map_subtype.le_order_embedding
- \+ *def* submodule.map_subtype.order_iso
- \+ *def* submodule.map_subtype
- \+ *lemma* submodule.map_subtype_embedding_eq
- \+ *lemma* submodule.map_subtype_subset
- \+ *theorem* submodule.mem_coe
- \+ *theorem* submodule.sInter_set
- \+ *def* submodule.span
- \+ *theorem* submodule.span_empty
- \+ *theorem* submodule.span_subset_iff
- \+ *theorem* submodule.span_union
- \+ *def* submodule.submodule_lt_equiv
- \+ *lemma* submodule.subset_comap_quotient
- \+ *theorem* submodule.top_set
- \+ *structure* {u

Modified linear_algebra/subtype_module.lean
- \- *lemma* add_val
- \- *lemma* is_linear_map_subtype_mk
- \- *lemma* is_linear_map_subtype_val
- \+ *lemma* is_submodule.coe_add
- \+ *lemma* is_submodule.coe_neg
- \+ *lemma* is_submodule.coe_smul
- \+ *lemma* is_submodule.coe_zero
- \+ *lemma* is_submodule.is_linear_map_coe
- \- *lemma* is_submodule.is_linear_map_inclusion
- \+ *lemma* is_submodule.is_linear_map_subtype_mk
- \+ *lemma* is_submodule.is_linear_map_subtype_val
- \+ *lemma* is_submodule.sub_val
- \- *lemma* neg_val
- \- *lemma* smul_val
- \- *lemma* sub_val
- \- *lemma* zero_val

Modified logic/basic.lean
- \+ *lemma* classical.some_spec2

Modified order/basic.lean
- \+ *def* linear_order.lift
- \+ *def* partial_order.lift
- \+ *def* preorder.lift

Deleted ring_theory/correspondence_theorem.lean


Modified ring_theory/noetherian.lean
- \- *def* submodule.univ

Deleted ring_theory/submodule.lean
- \- *theorem* submodule.Union_set_of_directed
- \- *theorem* submodule.bot_set
- \- *lemma* submodule.embedding_eq
- \- *theorem* submodule.eq
- \- *theorem* submodule.ext
- \- *theorem* submodule.mem_coe
- \- *def* submodule.pullback_injective_of_surjective
- \- *def* submodule.pushforward_injective_of_injective
- \- *theorem* submodule.sInter_set
- \- *def* submodule.span
- \- *theorem* submodule.span_empty
- \- *theorem* submodule.span_subset_iff
- \- *theorem* submodule.span_union
- \- *theorem* submodule.top_set
- \- *structure* {u

Modified set_theory/ordinal.lean




## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/4421f46)
feat(ring_theory): submodules and quotients of Noetherian modules are Noetherian
#### Estimated changes
Modified algebra/order.lean
- \+ *lemma* le_iff_le_of_strict_mono

Modified data/set/basic.lean
- \+ *theorem* set.singleton_union
- \+/\- *theorem* set.union_singleton

Modified data/set/finite.lean
- \+ *theorem* set.finite.exists_finset_coe

Modified linear_algebra/basic.lean


Modified linear_algebra/quotient_module.lean
- \+ *lemma* quotient_module.quotient.exists_rep

Modified linear_algebra/subtype_module.lean
- \+ *lemma* is_submodule.is_linear_map_inclusion

Modified order/conditionally_complete_lattice.lean


Modified order/order_iso.lean


Added ring_theory/correspondence_theorem.lean


Added ring_theory/noetherian.lean
- \+ *def* is_fg
- \+ *def* is_noetherian
- \+ *theorem* is_noetherian_iff_well_founded
- \+ *theorem* is_noetherian_of_quotient_of_noetherian
- \+ *theorem* is_noetherian_of_submodule_of_noetherian
- \+ *def* is_noetherian_ring
- \+ *def* submodule.fg
- \+ *theorem* submodule.fg_def
- \+ *def* submodule.univ

Added ring_theory/submodule.lean
- \+ *theorem* submodule.Union_set_of_directed
- \+ *theorem* submodule.bot_set
- \+ *lemma* submodule.embedding_eq
- \+ *theorem* submodule.eq
- \+ *theorem* submodule.ext
- \+ *theorem* submodule.mem_coe
- \+ *def* submodule.pullback_injective_of_surjective
- \+ *def* submodule.pushforward_injective_of_injective
- \+ *theorem* submodule.sInter_set
- \+ *def* submodule.span
- \+ *theorem* submodule.span_empty
- \+ *theorem* submodule.span_subset_iff
- \+ *theorem* submodule.span_union
- \+ *theorem* submodule.top_set
- \+ *structure* {u



## [2018-09-07 17:27:38+02:00](https://github.com/leanprover-community/mathlib/commit/dce0e64)
fix(algebra/big_operators): change name of `sum_eq_single` to `finset.sum_eq_single` ([#321](https://github.com/leanprover-community/mathlib/pull/321))
#### Estimated changes
Modified algebra/big_operators.lean


Modified data/polynomial.lean




## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/4085ca1)
feat(category_theory): add measurable space example
#### Estimated changes
Added category_theory/examples/measurable_space.lean
- \+ *def* category_theory.examples.Borel
- \+ *def* category_theory.examples.Meas



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/c2a4cf9)
feat(category_theory): lift morphism map proof to concrete categories
#### Estimated changes
Modified category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.Top
- \+ *def* category_theory.examples.open_set.nbhd
- \+ *def* category_theory.examples.open_set.nbhds
- \+ *structure* category_theory.examples.open_set
- \- *def* category_theory.examples.topological_spaces.Top
- \- *def* category_theory.examples.topological_spaces.nbhd
- \- *def* category_theory.examples.topological_spaces.nbhds
- \- *structure* category_theory.examples.topological_spaces.open_set

Modified category_theory/functor.lean
- \+ *def* category_theory.concrete_functor



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/93e9043)
style(category_theory): concrete categories as type class
#### Estimated changes
Modified category_theory/category.lean
- \+ *structure* category_theory.concrete_category
- \- *def* category_theory.concrete_category

Modified category_theory/examples/rings.lean
- \- *def* category_theory.examples.CommRing
- \- *def* category_theory.examples.comm_ring_hom.comp
- \- *lemma* category_theory.examples.comm_ring_hom.comp_map
- \- *lemma* category_theory.examples.comm_ring_hom.ext
- \- *def* category_theory.examples.comm_ring_hom.id
- \- *lemma* category_theory.examples.comm_ring_hom.id_map
- \+/\- *lemma* category_theory.examples.comm_ring_hom.map_add
- \+/\- *lemma* category_theory.examples.comm_ring_hom.map_mul
- \+/\- *lemma* category_theory.examples.comm_ring_hom.map_one
- \- *structure* category_theory.examples.comm_ring_hom
- \+ *def* category_theory.examples.is_comm_ring_hom
- \+ *def* category_theory.examples.{u}

Modified category_theory/examples/topological_spaces.lean
- \+/\- *def* category_theory.examples.topological_spaces.Top
- \- *lemma* category_theory.examples.topological_spaces.continuous_map.ext
- \- *structure* category_theory.examples.topological_spaces.continuous_map
- \+/\- *structure* category_theory.examples.topological_spaces.open_set

Modified category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.comp_map
- \+/\- *lemma* category_theory.functor.map_comp
- \+/\- *lemma* category_theory.functor.map_id
- \+/\- *lemma* category_theory.functor.mk_map
- \+/\- *lemma* category_theory.functor.mk_obj

Modified category_theory/types.lean
- \+ *def* category_theory.forget
- \+/\- *lemma* category_theory.functor_to_types.map_id
- \+/\- *lemma* category_theory.functor_to_types.naturality
- \+/\- *lemma* category_theory.types_hom
- \+ *def* category_theory.ulift_functor



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/5c48489)
feat(category_theory): construction for a concrete category
#### Estimated changes
Modified category_theory/category.lean
- \+/\- *lemma* category_theory.cancel_epi
- \+/\- *lemma* category_theory.cancel_mono
- \+ *def* category_theory.concrete_category



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/840a733)
removing unnecessary class
#### Estimated changes
Modified analysis/topology/topological_structures.lean




## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/d91428c)
feat(category_theory): the category of topological spaces, and of neighbourhoods of a point. also the category of commutative rings
#### Estimated changes
Modified analysis/topology/topological_structures.lean


Added category_theory/examples/rings.lean
- \+ *def* category_theory.examples.CommRing
- \+ *def* category_theory.examples.comm_ring_hom.comp
- \+ *lemma* category_theory.examples.comm_ring_hom.comp_map
- \+ *lemma* category_theory.examples.comm_ring_hom.ext
- \+ *def* category_theory.examples.comm_ring_hom.id
- \+ *lemma* category_theory.examples.comm_ring_hom.id_map
- \+ *lemma* category_theory.examples.comm_ring_hom.map_add
- \+ *lemma* category_theory.examples.comm_ring_hom.map_mul
- \+ *lemma* category_theory.examples.comm_ring_hom.map_one
- \+ *structure* category_theory.examples.comm_ring_hom

Added category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.topological_spaces.Top
- \+ *lemma* category_theory.examples.topological_spaces.continuous_map.ext
- \+ *structure* category_theory.examples.topological_spaces.continuous_map
- \+ *def* category_theory.examples.topological_spaces.nbhd
- \+ *def* category_theory.examples.topological_spaces.nbhds
- \+ *structure* category_theory.examples.topological_spaces.open_set



## [2018-09-07 09:20:27+02:00](https://github.com/leanprover-community/mathlib/commit/e95111d)
fix(tactic/tidy): fix interactive tidy ignoring cfg
#### Estimated changes
Modified tactic/tidy.lean




## [2018-09-06 15:59:41-04:00](https://github.com/leanprover-community/mathlib/commit/77e104c)
fix(tests/tactics): remove test
I don't think this test demonstrates reasonable/expected behavior of `wlog`, and it is not maintained by the modification, so I've removed it.
#### Estimated changes
Modified tests/tactics.lean




## [2018-09-06 15:39:55-04:00](https://github.com/leanprover-community/mathlib/commit/ea61c21)
fix(tactic/wlog): fix segfault
#### Estimated changes
Modified tactic/wlog.lean




## [2018-09-06 20:28:13+02:00](https://github.com/leanprover-community/mathlib/commit/3842244)
fix(linear_algebra/subtype): simplify lifted operations by using projections instead of match
#### Estimated changes
Modified linear_algebra/subtype_module.lean
- \+/\- *lemma* add_val
- \+/\- *lemma* neg_val
- \+/\- *lemma* smul_val



## [2018-09-06 01:04:28+02:00](https://github.com/leanprover-community/mathlib/commit/f262a07)
fix(linear_algebra/quotient_module): ring parameter for base ring of quotient module needs to be implicit, otherwise type class search loops
#### Estimated changes
Modified linear_algebra/quotient_module.lean




## [2018-09-05 23:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/e24f54e)
fix(linear_algebra/prod): field is implicit parameter of the module / vector space product instances
#### Estimated changes
Modified linear_algebra/prod_module.lean




## [2018-09-05 21:44:40+02:00](https://github.com/leanprover-community/mathlib/commit/016f538)
fix(algebra/module): add out_param to base field of vector spaces
#### Estimated changes
Modified algebra/module.lean




## [2018-09-05 14:33:30+02:00](https://github.com/leanprover-community/mathlib/commit/3a3249e)
feat(data/finsupp): multiset_map_sum/_sum_sum/_index
#### Estimated changes
Modified data/finsupp.lean
- \+/\- *lemma* finsupp.map_domain_finset_sum
- \+ *lemma* finsupp.multiset_map_sum
- \+ *lemma* finsupp.multiset_sum_sum
- \+ *lemma* finsupp.multiset_sum_sum_index
- \+/\- *lemma* finsupp.prod_finset_sum_index
- \+/\- *lemma* finsupp.prod_single



## [2018-09-05 14:19:36+02:00](https://github.com/leanprover-community/mathlib/commit/92b9a00)
feat(data/finsupp): to_/of_multiset, curry/uncurry
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.mem_subtype

Modified data/finsupp.lean
- \- *lemma* finset.mem_subtype
- \+ *lemma* finsupp.count_to_multiset
- \+ *def* finsupp.equiv_multiset
- \+ *def* finsupp.finsupp_prod_equiv
- \+/\- *lemma* finsupp.map_domain_finset_sum
- \+ *lemma* finsupp.mem_support_finset_sum
- \+ *lemma* finsupp.mem_support_multiset_sum
- \+ *lemma* finsupp.mem_support_single
- \+ *def* finsupp.of_multiset
- \+ *lemma* finsupp.of_multiset_apply
- \+/\- *lemma* finsupp.prod_add_index
- \+/\- *lemma* finsupp.prod_finset_sum_index
- \+/\- *lemma* finsupp.prod_map_domain_index
- \+/\- *lemma* finsupp.prod_sum_index
- \+ *lemma* finsupp.single_finset_sum
- \+ *lemma* finsupp.single_multiset_sum
- \+ *lemma* finsupp.single_sum
- \+/\- *lemma* finsupp.sum_add
- \+ *lemma* finsupp.sum_curry_index
- \+/\- *lemma* finsupp.sum_neg
- \+/\- *lemma* finsupp.sum_sub_index
- \+/\- *lemma* finsupp.sum_zero
- \+ *def* finsupp.to_multiset
- \+/\- *structure* finsupp



## [2018-09-05 14:05:50+02:00](https://github.com/leanprover-community/mathlib/commit/e105c9e)
feat(data/multiset): add prod_map_add
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* multiset.prod_map_add



## [2018-09-05 14:04:54+02:00](https://github.com/leanprover-community/mathlib/commit/abd6ab5)
refactor(data/prod): add map_fst, map_snd
#### Estimated changes
Modified data/prod.lean
- \+ *lemma* prod.map_fst
- \+ *lemma* prod.map_snd



## [2018-09-05 13:15:42+02:00](https://github.com/leanprover-community/mathlib/commit/ac4f7b1)
Revert "doc(docs/elan.md): Clarify instructions for leanpkg build"
This reverts commit 89e8cfee313b8bffe70362949577bd575cd09ea5.
#### Estimated changes
Modified docs/elan.md




## [2018-09-05 11:54:07+02:00](https://github.com/leanprover-community/mathlib/commit/9ea38e1)
feat(data/finset): option.to_finset
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* option.mem_to_finset
- \+ *def* option.to_finset
- \+ *theorem* option.to_finset_none
- \+ *theorem* option.to_finset_some



## [2018-09-05 11:53:36+02:00](https://github.com/leanprover-community/mathlib/commit/2997ce6)
feat(logic/embedding): embedding into option
#### Estimated changes
Modified data/option.lean
- \+ *theorem* option.injective_some

Modified logic/embedding.lean




## [2018-09-05 11:52:47+02:00](https://github.com/leanprover-community/mathlib/commit/a2acc61)
doc(docs/howto-contribute.md): fix broken links
#### Estimated changes
Modified docs/howto-contribute.md




## [2018-09-05 11:51:46+02:00](https://github.com/leanprover-community/mathlib/commit/89e8cfe)
doc(docs/elan.md): Clarify instructions for leanpkg build
#### Estimated changes
Modified docs/elan.md




## [2018-09-05 11:51:18+02:00](https://github.com/leanprover-community/mathlib/commit/97cd01b)
refactor(linear_algebra/quotient_module): avoid using type class inference for setoids ([#310](https://github.com/leanprover-community/mathlib/pull/310))
Continuation of [#212](https://github.com/leanprover-community/mathlib/pull/212) . Avoid using type class inference for quotient modules, and introduce a version of `quotient.mk` specifically for quotient modules, whose output type is `quotient β s` rather than `quotient (quotient_rel s)`, which should help type class inference.
#### Estimated changes
Modified linear_algebra/linear_map_module.lean


Modified linear_algebra/quotient_module.lean
- \- *lemma* is_submodule.is_linear_map_quotient_lift
- \- *lemma* is_submodule.is_linear_map_quotient_mk
- \- *lemma* is_submodule.quotient.injective_lift
- \- *def* is_submodule.quotient.lift
- \- *lemma* is_submodule.quotient.lift_mk
- \- *def* is_submodule.quotient
- \- *lemma* is_submodule.quotient_rel_eq
- \+ *lemma* quotient_module.coe_add
- \+ *lemma* quotient_module.coe_smul
- \+ *lemma* quotient_module.coe_zero
- \+ *lemma* quotient_module.is_linear_map_quotient_lift
- \+ *lemma* quotient_module.is_linear_map_quotient_mk
- \+ *def* quotient_module.mk
- \+ *lemma* quotient_module.quotient.injective_lift
- \+ *def* quotient_module.quotient.lift
- \+ *lemma* quotient_module.quotient.lift_mk
- \+ *def* quotient_module.quotient

Modified ring_theory/ideals.lean




## [2018-09-05 11:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/681c98f)
feat(category_theory): full subcategories, preorders, Aut, and End
#### Estimated changes
Modified category_theory/category.lean
- \+ *def* category_theory.End

Added category_theory/full_subcategory.lean
- \+ *def* category_theory.full_subcategory_embedding

Modified category_theory/isomorphism.lean
- \+ *def* category_theory.Aut



## [2018-09-05 09:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/600d3cf)
cleanup(data/polynomial): shorten some proofs
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* finsupp.support_add_eq

Modified data/polynomial.lean
- \+ *lemma* polynomial.apply_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* polynomial.degree_le_degree
- \+ *lemma* polynomial.degree_le_nat_degree
- \+ *lemma* polynomial.le_nat_degree_of_ne_zero



## [2018-09-04 19:56:23+02:00](https://github.com/leanprover-community/mathlib/commit/76de588)
feat(data/polynomial): prove degree_derivative_eq
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_eq_single

Modified data/polynomial.lean
- \+ *lemma* polynomial.degree_derivative_eq
- \+ *lemma* polynomial.derivative_apply
- \+ *lemma* polynomial.mem_support_derivative
- \+ *lemma* polynomial.nat_degree_zero



## [2018-09-04 10:43:33+02:00](https://github.com/leanprover-community/mathlib/commit/eb20fd0)
feat(data/polynomial): derivative on polynomials
#### Estimated changes
Modified data/polynomial.lean
- \+ *def* polynomial.derivative
- \+ *lemma* polynomial.derivative_C
- \+ *lemma* polynomial.derivative_X
- \+ *lemma* polynomial.derivative_add
- \+ *lemma* polynomial.derivative_monomial
- \+ *lemma* polynomial.derivative_mul
- \+ *lemma* polynomial.derivative_one
- \+ *lemma* polynomial.derivative_sum
- \+ *lemma* polynomial.derivative_zero
- \+ *lemma* polynomial.sum_C_mul_X_eq



## [2018-09-04 02:25:20-04:00](https://github.com/leanprover-community/mathlib/commit/fd43fe0)
fix(data/polynomial): fix proofs
#### Estimated changes
Modified data/polynomial.lean
- \+/\- *lemma* polynomial.map_C
- \+/\- *lemma* polynomial.map_X



## [2018-09-04 01:53:38-04:00](https://github.com/leanprover-community/mathlib/commit/7a4125b)
feat(algebra/field): field homs
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* is_field_hom.map_div'
- \+ *lemma* is_field_hom.map_div
- \+ *lemma* is_field_hom.map_eq_zero
- \+ *lemma* is_field_hom.map_inv'
- \+ *lemma* is_field_hom.map_inv
- \+ *lemma* is_field_hom.map_ne_zero
- \+ *def* is_field_hom



## [2018-09-04 01:49:52-04:00](https://github.com/leanprover-community/mathlib/commit/2dd78b8)
feat(data/polynomial): add eval2 for univariate polys
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* int.coe_nat_pow
- \+ *theorem* is_semiring_hom.map_pow

Modified data/polynomial.lean
- \+/\- *def* polynomial.eval
- \+/\- *lemma* polynomial.eval_C
- \+/\- *lemma* polynomial.eval_X
- \+/\- *lemma* polynomial.eval_add
- \+/\- *lemma* polynomial.eval_mul
- \+/\- *lemma* polynomial.eval_one
- \+/\- *lemma* polynomial.eval_pow
- \+/\- *lemma* polynomial.eval_zero
- \+ *def* polynomial.eval₂
- \+ *lemma* polynomial.eval₂_C
- \+ *lemma* polynomial.eval₂_X
- \+ *lemma* polynomial.eval₂_add
- \+ *lemma* polynomial.eval₂_mul
- \+ *lemma* polynomial.eval₂_one
- \+ *lemma* polynomial.eval₂_pow
- \+ *lemma* polynomial.eval₂_zero
- \+ *def* polynomial.map
- \+ *lemma* polynomial.map_C
- \+ *lemma* polynomial.map_X
- \+ *lemma* polynomial.map_add
- \+ *lemma* polynomial.map_mul
- \+ *lemma* polynomial.map_one
- \+ *lemma* polynomial.map_pow
- \+ *lemma* polynomial.map_zero

Modified linear_algebra/multivariate_polynomial.lean




## [2018-09-04 00:35:50-04:00](https://github.com/leanprover-community/mathlib/commit/b8ea49b)
fix(ring_theory/ufd): fix simpa uses
#### Estimated changes
Modified ring_theory/unique_factorization_domain.lean




## [2018-09-03 18:31:34-04:00](https://github.com/leanprover-community/mathlib/commit/4de119e)
fix(*): fix simpa uses
#### Estimated changes
Modified data/padics/padic_norm.lean


Modified data/zmod.lean




## [2018-09-03 16:58:55-04:00](https://github.com/leanprover-community/mathlib/commit/2021a1b)
perf(tactic/ring): don't do any implicit unfolds
#### Estimated changes
Modified tactic/ring.lean
- \+ *lemma* tactic.ring.unfold_div
- \+ *lemma* tactic.ring.unfold_sub



## [2018-09-03 16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/1edb79a)
refactor(ring_theory/associated): rename associated_elements
#### Estimated changes
Renamed ring_theory/associated_elements.lean to ring_theory/associated.lean
- \+/\- *def* irreducible
- \+ *theorem* irreducible_or_factor
- \+ *theorem* is_unit_iff_dvd_one
- \+ *theorem* is_unit_iff_forall_dvd
- \+ *theorem* is_unit_of_dvd_unit
- \+ *theorem* of_irreducible_mul

Modified ring_theory/unique_factorization_domain.lean




## [2018-09-03 16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/956398c)
refactor(tactic/interactive): improve error reporting for simpa
also make simpa fail on no goals or when applied where simp will work
#### Estimated changes
Modified algebra/gcd_domain.lean


Modified analysis/metric_space.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean


Modified data/int/gcd.lean


Modified data/padics/padic_norm.lean


Modified data/rat.lean
- \+/\- *lemma* rat.denom_neg_eq_denom
- \+/\- *lemma* rat.num_denom_mk
- \+/\- *lemma* rat.num_zero

Modified data/real/nnreal.lean


Modified set_theory/ordinal.lean


Modified tactic/interactive.lean




## [2018-09-03 12:33:54+02:00](https://github.com/leanprover-community/mathlib/commit/36dd78e)
feat(category_theory): full and faithful functors, switching products
also the evaluation functor, and replace the ↝ arrow with ⥤, by request
#### Estimated changes
Modified category_theory/category.lean


Added category_theory/embedding.lean
- \+ *lemma* category_theory.image_preimage
- \+ *def* category_theory.preimage
- \+ *def* category_theory.preimage_iso
- \+ *lemma* category_theory.preimage_iso_coe
- \+ *lemma* category_theory.preimage_iso_symm_coe

Modified category_theory/functor.lean
- \+/\- *def* category_theory.functor.comp
- \+/\- *lemma* category_theory.functor.comp_map
- \+/\- *lemma* category_theory.functor.comp_obj
- \+/\- *def* category_theory.functor.map
- \+/\- *lemma* category_theory.functor.map_comp
- \+/\- *lemma* category_theory.functor.map_id
- \+/\- *lemma* category_theory.functor.obj_eq_coe

Modified category_theory/functor_category.lean
- \+/\- *lemma* category_theory.functor.category.comp_app
- \+/\- *lemma* category_theory.functor.category.id_app
- \+/\- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+/\- *lemma* category_theory.functor.category.nat_trans.naturality_app

Modified category_theory/isomorphism.lean
- \+/\- *lemma* category_theory.functor.eq_to_iso
- \+/\- *def* category_theory.functor.on_iso
- \+/\- *lemma* category_theory.functor.on_iso_hom
- \+/\- *lemma* category_theory.functor.on_iso_inv

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.app_eq_coe
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+/\- *def* category_theory.nat_trans.hcomp
- \+/\- *lemma* category_theory.nat_trans.hcomp_app
- \+/\- *lemma* category_theory.nat_trans.id_app
- \+/\- *lemma* category_theory.nat_trans.mk_app
- \+/\- *lemma* category_theory.nat_trans.naturality
- \+/\- *structure* category_theory.nat_trans

Modified category_theory/opposites.lean
- \+/\- *lemma* category_theory.functor.opposite_map
- \+/\- *lemma* category_theory.functor.opposite_obj

Modified category_theory/products.lean
- \+ *def* category_theory.evaluation
- \+/\- *def* category_theory.functor.prod
- \+/\- *lemma* category_theory.functor.prod_map
- \+/\- *lemma* category_theory.functor.prod_obj
- \+/\- *def* category_theory.nat_trans.prod
- \+/\- *lemma* category_theory.nat_trans.prod_app
- \+/\- *def* category_theory.prod.fst
- \+/\- *def* category_theory.prod.inl
- \+/\- *def* category_theory.prod.inr
- \+/\- *def* category_theory.prod.snd
- \+ *def* category_theory.prod.swap
- \+ *def* category_theory.prod.symmetry

Modified category_theory/types.lean


Modified docs/theories/category_theory.md




## [2018-09-03 12:32:04+02:00](https://github.com/leanprover-community/mathlib/commit/6ddc3fc)
feat(data/finset): max_of_ne_empty, min_of_ne_empty
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.max_of_ne_empty
- \+ *theorem* finset.min_of_ne_empty



## [2018-09-03 01:27:28+02:00](https://github.com/leanprover-community/mathlib/commit/7ee7614)
feat(category_theory/isomorphisms): introduce isomorphisms ([#278](https://github.com/leanprover-community/mathlib/pull/278))
* refactor(category_theory): renaming `ulift` to `ulift_functor` to avoid name clashes
* feat(category_theory): introduce isomorphisms
* doc(category_theory): rewrite
* Resolving issues raised by Johannes
* moving heterogenous_identity.lean into isomorphism.lean
* remove unnecessary `obviously` replacement
* refactor(category_theory): using tidy in the category theory library
#### Estimated changes
Modified category_theory/category.lean
- \+ *lemma* category_theory.cancel_epi
- \+ *lemma* category_theory.cancel_mono

Modified category_theory/functor.lean
- \+ *lemma* category_theory.functor.obj_eq_coe

Modified category_theory/functor_category.lean


Added category_theory/isomorphism.lean
- \+ *def* category_theory.eq_to_iso
- \+ *lemma* category_theory.eq_to_iso_refl
- \+ *lemma* category_theory.eq_to_iso_trans
- \+ *lemma* category_theory.functor.eq_to_iso
- \+ *def* category_theory.functor.on_iso
- \+ *lemma* category_theory.functor.on_iso_hom
- \+ *lemma* category_theory.functor.on_iso_inv
- \+ *def* category_theory.inv
- \+ *def* category_theory.is_iso.hom_inv_id
- \+ *def* category_theory.is_iso.inv_hom_id
- \+ *lemma* category_theory.iso.ext
- \+ *lemma* category_theory.iso.hom_eq_coe
- \+ *lemma* category_theory.iso.hom_inv_id
- \+ *lemma* category_theory.iso.inv_eq_coe
- \+ *lemma* category_theory.iso.inv_hom_id
- \+ *def* category_theory.iso.refl
- \+ *lemma* category_theory.iso.refl_coe
- \+ *lemma* category_theory.iso.refl_symm
- \+ *lemma* category_theory.iso.refl_symm_coe
- \+ *def* category_theory.iso.symm
- \+ *def* category_theory.iso.trans
- \+ *lemma* category_theory.iso.trans_coe
- \+ *lemma* category_theory.iso.trans_symm
- \+ *lemma* category_theory.iso.trans_symm_coe
- \+ *structure* category_theory.iso

Modified category_theory/natural_transformation.lean
- \+ *lemma* category_theory.nat_trans.app_eq_coe
- \+/\- *lemma* category_theory.nat_trans.vcomp_assoc

Modified category_theory/opposites.lean


Modified category_theory/products.lean


Modified category_theory/types.lean


Modified docs/theories.md


Renamed docs/theories/categories.md to docs/theories/category_theory.md




## [2018-09-03 00:10:15+02:00](https://github.com/leanprover-community/mathlib/commit/0df6f77)
style(linear_algebra/tensor_product): rename of -> tmul and ⊗ₛ -> ⊗ₜ; some cleanup in free_abelian_group
#### Estimated changes
Modified group_theory/free_abelian_group.lean
- \- *def* free_abelian_group.UMP
- \- *theorem* free_abelian_group.coe_def
- \+ *def* free_abelian_group.to_add_comm_group.UMP
- \- *lemma* free_abelian_group.to_add_comm_group.add
- \- *lemma* free_abelian_group.to_add_comm_group.coe
- \- *theorem* free_abelian_group.to_add_comm_group.ext
- \- *def* free_abelian_group.to_add_comm_group.is_add_group_hom
- \- *lemma* free_abelian_group.to_add_comm_group.neg
- \- *lemma* free_abelian_group.to_add_comm_group.of
- \- *lemma* free_abelian_group.to_add_comm_group.sub
- \- *theorem* free_abelian_group.to_add_comm_group.unique
- \- *lemma* free_abelian_group.to_add_comm_group.zero
- \+/\- *def* free_abelian_group.to_add_comm_group

Modified linear_algebra/tensor_product.lean
- \- *lemma* tensor_product.add_of
- \+ *lemma* tensor_product.add_tmul
- \+/\- *theorem* tensor_product.bilinear
- \- *lemma* tensor_product.of.add_left
- \- *lemma* tensor_product.of.add_right
- \- *lemma* tensor_product.of.smul
- \- *def* tensor_product.of
- \- *lemma* tensor_product.of_add
- \- *lemma* tensor_product.of_smul
- \- *lemma* tensor_product.smul_of
- \+ *lemma* tensor_product.smul_tmul
- \+ *lemma* tensor_product.tmul.add_left
- \+ *lemma* tensor_product.tmul.add_right
- \+ *lemma* tensor_product.tmul.smul
- \+ *def* tensor_product.tmul
- \+ *lemma* tensor_product.tmul_add
- \+ *lemma* tensor_product.tmul_smul
- \- *lemma* tensor_product.to_module.of
- \+ *lemma* tensor_product.to_module.tmul



## [2018-09-02 23:49:36+02:00](https://github.com/leanprover-community/mathlib/commit/40ef7a2)
doc(ring_theory/unique_factorization_domain): add document strings
#### Estimated changes
Modified ring_theory/unique_factorization_domain.lean




## [2018-09-02 16:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/b3afef5)
perf(tactic/ring): fix long-running mk_app invocations
#### Estimated changes
Modified tactic/ring.lean




## [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/dd0c0ae)
feat(ring_theory): add unique factorization domain
#### Estimated changes
Added ring_theory/unique_factorization_domain.lean
- \+ *theorem* associates.eq_of_factors_eq_factors
- \+ *theorem* associates.eq_of_prod_eq_prod
- \+ *theorem* associates.factor_set.coe_add
- \+ *def* associates.factor_set.prod
- \+ *lemma* associates.factor_set.sup_add_inf_eq_add
- \+ *def* associates.factors'
- \+ *theorem* associates.factors'_cong
- \+ *def* associates.factors
- \+ *theorem* associates.factors_0
- \+ *theorem* associates.factors_le
- \+ *theorem* associates.factors_mk
- \+ *theorem* associates.factors_mono
- \+ *theorem* associates.factors_mul
- \+ *theorem* associates.factors_prod
- \+ *theorem* associates.map_subtype_val_factors'
- \+ *theorem* associates.prod_add
- \+ *theorem* associates.prod_coe
- \+ *theorem* associates.prod_factors
- \+ *theorem* associates.prod_le
- \+ *theorem* associates.prod_le_prod_iff_le
- \+ *theorem* associates.prod_mono
- \+ *theorem* associates.prod_top
- \+ *lemma* associates.sup_mul_inf
- \+ *theorem* associates.unique'
- \+ *def* associates.{u}
- \+ *def* unique_factorization_domain.to_gcd_domain



## [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/5f8fafc)
feat(ring_theory): add associated elements
#### Estimated changes
Modified algebra/ring.lean
- \+/\- *theorem* mul_eq_zero
- \+ *theorem* zero_eq_mul

Modified data/multiset.lean
- \+ *theorem* multiset.exists_multiset_eq_map_quot_mk
- \+ *theorem* multiset.induction_on_multiset_quot
- \+ *theorem* multiset.injective_map
- \+ *theorem* multiset.map_eq_map
- \+ *theorem* multiset.map_mk_eq_map_mk_of_rel

Modified data/nat/basic.lean


Modified order/bounded_lattice.lean
- \+ *lemma* with_top.coe_inf
- \+ *lemma* with_top.coe_sup

Added ring_theory/associated_elements.lean
- \+ *theorem* associated.associated_of_dvd_dvd
- \+ *theorem* associated.associated_one_iff_is_unit
- \+ *theorem* associated.associated_one_of_associated_mul_one
- \+ *theorem* associated.associated_one_of_mul_eq_one
- \+ *theorem* associated.associated_zero_iff_eq_zero
- \+ *theorem* associated.unit_associated_one
- \+ *def* associated
- \+ *theorem* associates.coe_unit_eq_one
- \+ *theorem* associates.dvd_of_mk_le_mk
- \+ *lemma* associates.dvd_out_iff
- \+ *theorem* associates.forall_associated
- \+ *theorem* associates.irreducible_mk_iff
- \+ *theorem* associates.is_unit_iff_eq_one
- \+ *theorem* associates.is_unit_mk
- \+ *theorem* associates.le_mul_left
- \+ *theorem* associates.le_mul_right
- \+ *theorem* associates.mk_eq_mk_iff_associated
- \+ *theorem* associates.mk_eq_zero_iff_eq_zero
- \+ *theorem* associates.mk_le_mk_iff_dvd_iff
- \+ *theorem* associates.mk_le_mk_of_dvd
- \+ *theorem* associates.mk_mul_mk
- \+ *theorem* associates.mk_zero_eq
- \+ *theorem* associates.mul_eq_one_iff
- \+ *theorem* associates.mul_eq_zero_iff
- \+ *theorem* associates.mul_mono
- \+ *theorem* associates.mul_zero
- \+ *lemma* associates.norm_unit_out
- \+ *theorem* associates.one_eq_mk_one
- \+ *theorem* associates.one_le
- \+ *lemma* associates.out_dvd_iff
- \+ *lemma* associates.out_mk
- \+ *lemma* associates.out_mul
- \+ *lemma* associates.out_one
- \+ *lemma* associates.out_top
- \+ *theorem* associates.prod_eq_one_iff
- \+ *theorem* associates.prod_eq_zero_iff
- \+ *theorem* associates.prod_le_prod
- \+ *theorem* associates.prod_mk
- \+ *theorem* associates.quot_mk_eq_mk
- \+ *theorem* associates.quotient_mk_eq_mk
- \+ *theorem* associates.rel_associated_iff_map_eq_map
- \+ *theorem* associates.zero_mul
- \+ *theorem* associates.zero_ne_one
- \+ *def* associates
- \+ *def* associates_int_equiv_nat
- \+ *def* irreducible
- \+ *theorem* irreducible_iff_nat_prime
- \+ *def* is_unit
- \+ *theorem* is_unit_mul_units
- \+ *theorem* is_unit_nat
- \+ *theorem* is_unit_one
- \+ *theorem* not_irreducible_one
- \+ *theorem* not_irreducible_zero
- \+ *theorem* not_is_unit_zero
- \+ *theorem* units.is_unit_of_mul_one

Modified ring_theory/localization.lean




## [2018-09-02 20:07:13+02:00](https://github.com/leanprover-community/mathlib/commit/059f937)
feat(tactic): add linear arithmetic tactic ([#301](https://github.com/leanprover-community/mathlib/pull/301))
* feat(data/list, tactic): small helper functions
* feat(meta/rb_map): extra operations on native rb_maps
* feat(tactic/linarith): add tactic for solving linear arithmetic goals
* doc(tactic/linarith): add documentation and tests
* chore(tactic/linarith): add copyright
* feat(tactic/linarith): allow products of coefficients
* feat(tactic/linarith): cut off search early if contradiction is found
* feat(tests/linarith_tests): add test
* doc(doc/tactics): update doc
* feat(tactic/linarith): add config options
* feat(tactic/linarith): support equality goals
* chore(tactic/linarith): move non-tactic code out of tactic monad
* feat(tactic/linarith): support rational coefficients
* doc(tactic/linarith): update doc
* feat(tactic/linarith): fix obvious inefficiency in canceling denoms
* feat(tactic/linarith): efficiency improvements
* fix(tactic/linarith): remove unnecessary import and dead code
* fix(data/list/basic, meta/rb_map): shorter proofs
#### Estimated changes
Modified data/list/basic.lean
- \+/\- *theorem* list.index_of_eq_length
- \+ *def* list.reduce_option

Modified docs/tactics.md


Added meta/rb_map.lean


Modified tactic/basic.lean


Added tactic/linarith.lean
- \+ *lemma* linarith.add_subst
- \+ *def* linarith.alist_lt
- \+ *lemma* linarith.div_subst
- \+ *lemma* linarith.eq_of_eq_of_eq
- \+ *lemma* linarith.eq_of_not_lt_of_not_gt
- \+ *def* linarith.ineq.is_lt
- \+ *def* linarith.ineq.max
- \+ *def* linarith.ineq.to_string
- \+ *inductive* linarith.ineq
- \+ *lemma* linarith.le_of_eq_of_le
- \+ *lemma* linarith.le_of_le_of_eq
- \+ *lemma* linarith.lt_of_eq_of_lt
- \+ *lemma* linarith.lt_of_lt_of_eq
- \+ *lemma* linarith.mul_eq
- \+ *lemma* linarith.mul_neg
- \+ *lemma* linarith.mul_nonpos
- \+ *lemma* linarith.mul_subst
- \+ *lemma* linarith.neg_subst
- \+ *def* linarith.reduce_pair_option
- \+ *lemma* linarith.sub_into_lt
- \+ *lemma* linarith.sub_subst
- \+ *def* linarith.tree.repr
- \+ *inductive* linarith.{u}

Added tests/linarith_tests.lean




## [2018-09-02 19:58:41+02:00](https://github.com/leanprover-community/mathlib/commit/8c19da7)
feat(data/polynomial): has_repr for polynomials ([#302](https://github.com/leanprover-community/mathlib/pull/302))
Not sure if I should change this so that it will always return a string that will not cause any problems if copied and pasted into a lemma. It does this for rationals and integers, although for rationals, it returns something equal to the polynomial you would like, but probably not the polynomial you actually want, i.e. `(2 / 3 : polynomial ℚ)` more or less gives you `(C 2 / C 3)`, rather than `C (2 / 3)`. These expressions are def eq, but not in any reasonable amount of time as soon as the size gets slightly larger.
#### Estimated changes
Modified data/polynomial.lean




## [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/2594f48)
style(linear_algebra/tensor_product): renaming and changing some proofs
#### Estimated changes
Modified group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.to_add_comm_group.coe
- \+ *lemma* free_abelian_group.to_add_comm_group.sub

Modified linear_algebra/tensor_product.lean
- \+/\- *theorem* is_bilinear_map.comm
- \+/\- *theorem* is_bilinear_map.comp
- \+ *theorem* is_bilinear_map.linear_left
- \- *theorem* is_bilinear_map.linear_pair
- \+ *theorem* is_bilinear_map.linear_right
- \+ *theorem* is_bilinear_map.neg_left
- \- *theorem* is_bilinear_map.neg_pair
- \+ *theorem* is_bilinear_map.neg_right
- \- *theorem* is_bilinear_map.pair_linear
- \- *theorem* is_bilinear_map.pair_neg
- \- *theorem* is_bilinear_map.pair_zero
- \+ *theorem* is_bilinear_map.zero_left
- \- *theorem* is_bilinear_map.zero_pair
- \+ *theorem* is_bilinear_map.zero_right
- \+/\- *structure* is_bilinear_map
- \+/\- *lemma* tensor_product.add_of
- \+ *lemma* tensor_product.of.add_left
- \+ *lemma* tensor_product.of.add_right
- \+ *lemma* tensor_product.of.smul
- \+/\- *lemma* tensor_product.of_add
- \+/\- *lemma* tensor_product.of_smul
- \+ *lemma* tensor_product.smul.is_add_group_hom
- \- *def* tensor_product.smul.is_add_group_hom
- \+/\- *lemma* tensor_product.smul_of
- \+/\- *def* tensor_product



## [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/4b5ad0e)
feat(linear_algebra,group_theory): add tensor product and supporting material
#### Estimated changes
Modified algebra/group.lean


Modified algebra/ring.lean


Added group_theory/abelianization.lean
- \+ *def* abelianization.of
- \+ *def* abelianization.to_comm_group.is_group_hom
- \+ *lemma* abelianization.to_comm_group.of
- \+ *theorem* abelianization.to_comm_group.unique
- \+ *def* abelianization.to_comm_group
- \+ *def* abelianization
- \+ *def* commutator

Modified group_theory/coset.lean
- \+ *lemma* quotient_group.induction_on'
- \+ *lemma* quotient_group.induction_on

Added group_theory/free_abelian_group.lean
- \+ *def* free_abelian_group.UMP
- \+ *theorem* free_abelian_group.coe_def
- \+ *def* free_abelian_group.of
- \+ *lemma* free_abelian_group.to_add_comm_group.add
- \+ *theorem* free_abelian_group.to_add_comm_group.ext
- \+ *def* free_abelian_group.to_add_comm_group.is_add_group_hom
- \+ *lemma* free_abelian_group.to_add_comm_group.neg
- \+ *lemma* free_abelian_group.to_add_comm_group.of
- \+ *theorem* free_abelian_group.to_add_comm_group.unique
- \+ *lemma* free_abelian_group.to_add_comm_group.zero
- \+ *def* free_abelian_group.to_add_comm_group
- \+ *def* free_abelian_group

Modified group_theory/quotient_group.lean


Modified group_theory/subgroup.lean


Added linear_algebra/tensor_product.lean
- \+ *theorem* is_bilinear_map.comm
- \+ *theorem* is_bilinear_map.comp
- \+ *theorem* is_bilinear_map.linear_pair
- \+ *theorem* is_bilinear_map.neg_pair
- \+ *theorem* is_bilinear_map.pair_linear
- \+ *theorem* is_bilinear_map.pair_neg
- \+ *theorem* is_bilinear_map.pair_zero
- \+ *theorem* is_bilinear_map.zero_pair
- \+ *structure* is_bilinear_map
- \+ *lemma* tensor_product.add_of
- \+ *theorem* tensor_product.bilinear
- \+ *def* tensor_product.of
- \+ *lemma* tensor_product.of_add
- \+ *lemma* tensor_product.of_smul
- \+ *def* tensor_product.relators
- \+ *def* tensor_product.smul.aux
- \+ *def* tensor_product.smul.is_add_group_hom
- \+ *def* tensor_product.smul
- \+ *lemma* tensor_product.smul_of
- \+ *lemma* tensor_product.to_module.add
- \+ *def* tensor_product.to_module.equiv
- \+ *theorem* tensor_product.to_module.ext
- \+ *def* tensor_product.to_module.linear
- \+ *lemma* tensor_product.to_module.of
- \+ *lemma* tensor_product.to_module.smul
- \+ *theorem* tensor_product.to_module.unique
- \+ *def* tensor_product.to_module
- \+ *def* tensor_product



## [2018-09-02 13:36:43-04:00](https://github.com/leanprover-community/mathlib/commit/dd6b035)
feat(data/option): add simp lemmas for orelse
#### Estimated changes
Modified data/option.lean
- \+ *theorem* option.none_orelse'
- \+ *theorem* option.none_orelse
- \+/\- *theorem* option.orelse_none'
- \+/\- *theorem* option.orelse_none
- \- *theorem* option.orelse_some'
- \- *theorem* option.orelse_some
- \+ *theorem* option.some_orelse'
- \+ *theorem* option.some_orelse



## [2018-09-02 17:21:22](https://github.com/leanprover-community/mathlib/commit/3de3cfb)
feat(tactic/subtype_instance): generating subtype instances
#### Estimated changes
Modified data/list/basic.lean
- \+ *def* list.map_head
- \+ *def* list.map_last

Modified data/string.lean
- \+ *def* string.map_tokens

Added field_theory/subfield.lean


Modified group_theory/subgroup.lean


Modified group_theory/submonoid.lean


Added ring_theory/subring.lean


Added tactic/algebra.lean


Modified tactic/basic.lean


Added tactic/subtype_instance.lean
- \+ *def* tactic.mk_mem_name



## [2018-09-01 13:10:14+02:00](https://github.com/leanprover-community/mathlib/commit/b7b05fb)
style(ring_theory): rename PID to principal_ideal_domain
#### Estimated changes
Renamed ring_theory/PID.lean to ring_theory/principal_ideal_domain.lean


